//! EMUlator module.
#![allow(clippy::doc_markdown)] // ^^

use crate::Addr;
use crate::{CpuRegisters, PpuState};
use crate::{FullInstruction, AddressingMode};
use crate::mapping::{MapLookup, MapLookupError, Mapper};

use nesfile::File as NesFile;

/// Delay the execution so many cycles.
fn delay_cycles(cycles: u8) {
    let _ = cycles;
    // TODO: implement this
}

/// A fault that can occur during operation.
/// This does not correspond to anything on the NES,
/// it's a type for errors in the emulator.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Fault {
    /// Program attempted to access unmapped memory
    UnmappedMemory(Addr),
    /// The mapper gave an address that was invalid
    InvalidMapperAddress(Addr),
    /// The stack page ($0100-$01FF) was underflowed by the stack pointer
    StackUnderflow,
    /// Something went wrong inside nesmulator
    InternalError(InternalErrorFault),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InternalErrorFault {
    kind: InternalFaultKind,
}

impl InternalErrorFault {
    /// Could this error potentially be ignored?
    /// 
    /// Some internal errors are `log!`ed and are otherwise ignored.
    /// Weird behavior in games may happen if these faults are ignored.
    pub fn is_ignorable(&self) -> bool {
        #[allow(clippy::match_same_arms)]
        match self.kind {
            InternalFaultKind::InvalidAddressingMode(_) => true,
            InternalFaultKind::InvalidOperandType => true,
        }
    }
}

/// What actually went wrong?
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum InternalFaultKind {
    /// An invalid addressing mode was detected, with that mode in the error
    InvalidAddressingMode(AddressingMode),
    /// An invalid operand type was detected
    InvalidOperandType,
}

/// The full state of the emulator.
#[derive(Debug, Clone, Hash)]
pub struct State {
    pub file: Box<NesFile>,
    pub cpu_regs: CpuRegisters,
    pub ppu_regs: PpuState,
    pub internal_ram: Box<[u8; 2 * 1024]>,
    pub prg_ram: Box<[u8]>,
    pub chr_ram: Box<[u8]>,
    pub mapper: Mapper,
}

impl State {
    pub fn read_byte(&self, addr: Addr) -> Result<u8, Fault> {
        let addr_usz: usize = addr.into_num().into();
        match addr.into_num() {
            0x0000..0x0800 => Ok(self.internal_ram[addr_usz]),
            0x0800..0x2000 => Ok(self.internal_ram[addr_usz % 0x0800]),
            0x2000..0x2008 => todo!("Access PPU registers"),
            0x2008..0x4000 => todo!("Access mirrors of PPU registers"),
            0x4000..0x4018 => todo!("Access APU & I/O registers"),
            0x4018..0x4020 => Err(Fault::UnmappedMemory(addr)),
            0x4020..=0xFFFF => {
                let res = self.mapper.lookup_addr(addr);
                let lookup = res.map_err(|e| match e {
                    MapLookupError::AddressNotMapped => Fault::UnmappedMemory(addr),
                })?;
                let res: Option<&u8> = match lookup {
                    MapLookup::PrgRom(loc) => self.file.prg_rom.get(usize::from(loc)),
                    MapLookup::PrgRam(loc) => self.prg_ram.get(usize::from(loc)),
                    MapLookup::ChrRom(loc) => self.file.chr_rom.get(usize::from(loc)),
                    MapLookup::ChrRam(loc) => self.chr_ram.get(usize::from(loc)),
                };
                match res {
                    Some(&byte) => Ok(byte),
                    None => Err(Fault::InvalidMapperAddress(addr)),
                }
            },
        }
    }

    pub fn write_byte(&mut self, byte: u8, addr: Addr) -> Result<(), Fault> {
        let addr_usz: usize = addr.into_num().into();
        match addr.into_num() {
            0x0000..0x0800 => self.internal_ram[addr_usz] = byte,
            0x0800..0x2000 => self.internal_ram[addr_usz % 0x0800] = byte,
            0x2000..0x2008 => todo!("Write PPU registers"),
            0x2008..0x4000 => todo!("Write PPU register mirrors"),
            0x4000..0x4018 => todo!("Write APU & I/O registers"),
            0x4018..0x4020 => return Err(Fault::UnmappedMemory(addr)),
            0x4020..=0xFFFF => {
                let lookup = self.mapper.lookup_addr(addr)
                    .map_err(|e| match e {
                        MapLookupError::AddressNotMapped => Fault::UnmappedMemory(addr),
                    })?;
                let (slice, pos) = match lookup {
                    MapLookup::PrgRom(loc) => (&mut self.file.prg_rom, loc),
                    MapLookup::PrgRam(loc) => (&mut self.prg_ram, loc),
                    MapLookup::ChrRom(loc) => (&mut self.file.chr_rom, loc),
                    MapLookup::ChrRam(loc) => (&mut self.chr_ram, loc),
                };
                match slice.get_mut(usize::from(pos)) {
                    Some(place) => *place = byte,
                    None => return Err(Fault::InvalidMapperAddress(addr)),
                }
            },
        }
        Ok(())
    }

    pub fn read_le_u16(&self, addr: Addr) -> Result<u16, Fault> {
        let first = self.read_byte(addr)?;
        let last = self.read_byte(addr.offset(1u8))?;
        Ok(u16::from_le_bytes([first, last]))
    }

    /// # Faults
    /// [`StackUnderflow`](Fault::StackUnderflow)
    fn push_byte(&mut self, byte: u8) -> Result<(), Fault> {
        let stack_pointer = self.cpu_regs.sp;
        let new_sp = stack_pointer.checked_sub(1).ok_or(Fault::StackUnderflow)?;
        self.cpu_regs.sp = new_sp;
        self.internal_ram[usize::from(self.cpu_regs.sp_as_address().into_num())] = byte;
        Ok(())
    }
    
    /// # Faults
    /// [`StackUnderflow`](Fault::StackUnderflow)
    fn pop_byte(&mut self) -> Result<u8, Fault> {
        let stack_pointer = self.cpu_regs.sp;
        let new_sp = stack_pointer.checked_add(1).ok_or(Fault::StackUnderflow)?;
        self.cpu_regs.sp = new_sp;
        Ok(self.internal_ram[usize::from(
            self.cpu_regs.sp_as_address().into_num()
        )])
    }

    /// Reads the interrupt vector from `0xFFFE-FFFF`.
    fn interrupt_vector(&self) -> Result<Addr, Fault> {
        const INTERRUPT_ADDRESS: Addr = Addr::from_num(0xFFFE);
        self.read_le_u16(INTERRUPT_ADDRESS).map(Addr::from_num)
    }

    pub fn exec_instruction(&mut self, inst: FullInstruction) -> Result<(), Fault> {
        exec_instruction::exec_instruction(self, inst)
    }
}

mod exec_instruction;
