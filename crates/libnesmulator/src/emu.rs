//! EMUlator module.
#![allow(clippy::doc_markdown)] // ^^

use crate::Addr;
use crate::{CpuRegisters, PpuState};
use crate::FullInstruction;
use crate::mapping::Mapper;

use nesfile::File as NesFile;

/// A fault that can occur during operation.
/// This does not correspond to anything on the NES,
/// it's a type for errors in the emulator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Fault {
    pub addr: Addr,
    pub typ: FaultType,
}

/// What caused this fault?
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FaultType {
    /// Program attempted to access unmapped memory
    UnmappedMemory,
}

/// The full state of the emulator.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct State {
    pub file: Box<NesFile>,
    pub cpu_regs: CpuRegisters,
    pub ppu_regs: PpuState,
    pub internal_ram: Box<[u8; 2 * 1024]>,
    pub mapper: Mapper,
}

impl State {
    pub(crate) fn read_byte(&self, addr: Addr) -> Result<u8, Fault> {
        let addr_usz: usize = addr.into_num().into();
        match addr.into_num() {
            0x0000..0x0800 => Ok(self.internal_ram[addr_usz]),
            0x0800..0x2000 => Ok(self.internal_ram[addr_usz % 0x0800]),
            0x2000..0x2008 => todo!("Access PPU registers"),
            0x2008..0x4000 => todo!("Access mirrors of PPU registers"),
            0x4000..0x4018 => todo!("Access APU & I/O registers"),
            0x4018..0x4020 => Err(Fault {
                addr,
                typ: FaultType::UnmappedMemory,
            }),
            0x4020..=0xFFFF => {
                todo!("Read from the mapper");
            },
        }
    }

    pub(crate) fn write_byte(&mut self, byte: u8, addr: Addr) -> Result<(), Fault> {
        let addr_usz: usize = addr.into_num().into();
        match addr.into_num() {
            0x0000..0x0800 => self.internal_ram[addr_usz] = byte,
            0x0800..0x2000 => self.internal_ram[addr_usz % 0x0800] = byte,
            0x2000..0x2008 => todo!("Write PPU registers"),
            0x2008..0x4000 => todo!("Write PPU register mirrors"),
            0x4000..0x4018 => todo!("Write APU & I/O registers"),
            0x4018..0x4020 => return Err(Fault {
                addr,
                typ: FaultType::UnmappedMemory,
            }),
            0x4020..=0xFFFF => todo!("read from mapper"),
        }
        Ok(())
    }

    pub fn exec_instruction(&mut self, inst: FullInstruction) {
        todo!("execute instructions")
    }
}
