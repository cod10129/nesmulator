//! EMUlator module.
#![allow(clippy::doc_markdown)] // ^^

use crate::Addr;
use crate::{CpuRegisters, PpuState};
use crate::{Instruction, InstructionWithMode, FullInstruction, AddressingMode, Operand};
use crate::mapping::Mapper;

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
            0x4018..0x4020 => Err(Fault::UnmappedMemory(addr)),
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
            0x4018..0x4020 => return Err(Fault::UnmappedMemory(addr)),
            0x4020..=0xFFFF => todo!("read from mapper"),
        }
        Ok(())
    }

    fn read_le_u16(&self, addr: Addr) -> Result<u16, Fault> {
        let first = self.read_byte(addr)?;
        let last = self.read_byte(Addr::from(addr.into_num() + 1))?;
        Ok(u16::from_le_bytes([first, last]))
    }

    /// # Faults
    /// `StackUnderflow`
    fn push_byte(&mut self, byte: u8) -> Result<(), Fault> {
        let stack_pointer = self.cpu_regs.sp;
        let new_sp = stack_pointer.checked_sub(1).ok_or(Fault::StackUnderflow)?;
        self.cpu_regs.sp = new_sp;
        self.write_byte(byte, self.cpu_regs.sp_as_address())?;
        Ok(())
    }

    pub fn exec_instruction(&mut self, inst: FullInstruction) -> Result<(), Fault> {
        exec_instruction(self, inst)
    }
}

#[allow(clippy::single_match_else)]
#[allow(clippy::too_many_lines)]
fn exec_instruction(state: &mut State, inst: FullInstruction) -> Result<(), Fault> {
    let FullInstruction {
        instruction: InstructionWithMode {
            instruction_type: instruction,
            addressing_mode,
        },
        operand,
    } = inst;

    macro_rules! bad {
        (Addressing for $inst:tt) => {{
            ::log::error!(
                "{} instruction encountered with invalid addressing mode {:?}. \
                This instruction is being ignored, which could cause big problems.",
                stringify!($inst), addressing_mode,
            );
            return Err(Fault::InternalError(InternalErrorFault {
                kind: InternalFaultKind::InvalidAddressingMode(addressing_mode),
            }));
        }};
        (Operand expected $variant:tt) => {{
            // This is either type `Operand` or type `fn(u8/16) -> Operand`
            let _assert_is_variant = crate::Operand::$variant;
            ::log::error!(
                "Incorrect operand for mode {:?}: {:?} (expected {:?}). \
                This error is being ignored to continue operation. \
                NESmulator will likely fail soon.",
                addressing_mode, operand, stringify!($variant),
            );
            return Err(Fault::InternalError(InternalErrorFault {
                kind: InternalFaultKind::InvalidOperandType,
            }));
        }}
    }

    match instruction {
        Instruction::NoOp => match addressing_mode {
            AddressingMode::Implied => { delay_cycles(2) },
            _ => bad!(Addressing for NOP),
        },
        Instruction::Jump => match addressing_mode {
            AddressingMode::Absolute => {
                let Operand::TwoBytes(addr) = operand else {
                    bad!(Operand expected TwoBytes);
                };
                state.cpu_regs.pc = Addr::from(addr);
                delay_cycles(3);
            },
            AddressingMode::Indirect => {
                let Operand::TwoBytes(addr) = operand else {
                    bad!(Operand expected TwoBytes);
                };
                let jump_target = state.read_le_u16(addr.into())?;
                state.cpu_regs.pc = Addr::from(jump_target);
                delay_cycles(5);
            }
            _ => bad!(Addressing for JMP),
        },
        Instruction::PushAccumulator => match addressing_mode {
            AddressingMode::Implied => {
                let Operand::None = operand else {
                    bad!(Operand expected None);
                };
                state.push_byte(state.cpu_regs.a)?;
                delay_cycles(3);
            },
            _ => bad!(Addressing for PHA),
        },
        Instruction::PushFlags => match addressing_mode {
            AddressingMode::Implied => {
                let Operand::None = operand else {
                    bad!(Operand expected None);
                };
                state.push_byte(state.cpu_regs.flags.value_to_push(false))?;
                delay_cycles(3);
            },
            _ => bad!(Addressing for PHP),
        },
        Instruction::TransferRegisterXToStack => match addressing_mode {
            AddressingMode::Implied => {
                let Operand::None = operand else {
                    bad!(Operand expected None);
                };
                state.cpu_regs.sp = state.cpu_regs.x;
                delay_cycles(2);
            },
            _ => bad!(Addressing for TXS),
        },
        Instruction::StoreRegisterX => match addressing_mode {
            AddressingMode::Absolute => {
                let Operand::TwoBytes(addr) = operand else {
                    bad!(Operand expected TwoBytes);
                };
                state.write_byte(state.cpu_regs.x, addr.into())?;
                delay_cycles(4);
            }
            AddressingMode::ZeroPage => {
                let Operand::OneByte(zpaddr) = operand else {
                    bad!(Operand expected OneByte);
                };
                state.write_byte(state.cpu_regs.x, Addr::from_u8(zpaddr))?;
                delay_cycles(3);
            },
            AddressingMode::ZeroPageIndexedY => {
                let Operand::OneByte(base) = operand else {
                    bad!(Operand expected OneByte);
                };
                let addr = base.wrapping_add(state.cpu_regs.y);
                state.write_byte(state.cpu_regs.x, Addr::from_u8(addr))?;
                delay_cycles(4);
            },
            _ => bad!(Addressing for STX),
        },
        // 48 more
        _ => todo!()
    }
    Ok(())
}
