//! EMUlator module.
#![allow(clippy::doc_markdown)] // ^^

use bitvec::prelude as bv;

use crate::Addr;
use crate::{CpuRegisters, CpuFlags, PpuState};
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
        let last = self.read_byte(addr.offset(1))?;
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

    pub fn exec_instruction(&mut self, inst: FullInstruction) -> Result<(), Fault> {
        exec_instruction(self, inst)
    }
}

/// This function **DOES** take care of pushing the program counter
/// forward to point to after the currently executed instruction.
/// 
/// On branch instructions:
/// 
/// This API allows executing any instruction at any time, regardless of the
/// program counter location.
/// 
/// Branch instructions are relative to the PC value after the instruction is executed.
/// This function will assume the PC currently points to the branch instruction,
/// using `PC + inst.size()` to determine the immediately after branch value
/// of the program counter, which is neccessary to accurately compute cycle costs.
#[allow(clippy::single_match_else)]
#[allow(clippy::too_many_lines)]
fn exec_instruction(state: &mut State, inst: FullInstruction) -> Result<(), Fault> {
    use std::ops::Not;

    let FullInstruction {
        instruction: InstructionWithMode {
            instruction_type: instruction,
            addressing_mode,
        },
        operand,
    } = inst;

    let mut should_push_pc = true;

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
    
    macro_rules! extract {
        (Operand::None) => {{
            let Operand::None = operand else {
                bad!(Operand expected None);
            };
        }};
        (Operand::$variant:ident($name:ident)) => {
            let $crate::Operand::$variant($name) = operand else {
                bad!(Operand expected $variant);
            };
        };
        (Implied None for $inst:ident) => {{
            let AddressingMode::Implied = addressing_mode else {
                bad!(Addressing for $inst);
            };
            extract!(Operand::None);
        }};
    }

    macro_rules! branch {
        ($inst:ident: flags.$m1:ident()$(.$m2:ident())?) => {{
            let AddressingMode::Relative = addressing_mode else {
                bad!(Addressing for $inst);
            };
            extract!(Operand::OneByte(offset));
            branch_common(
                &mut state.cpu_regs.pc,
                i8::from_le_bytes(u8::to_le_bytes(offset)),
                state.cpu_regs.flags.$m1()$(.$m2())?
            );
            should_push_pc = false;
        }};
    }

    match instruction {
        Instruction::NoOp => {
            extract!(Implied None for NOP);
            delay_cycles(2);
        },
        Instruction::Jump => match addressing_mode {
            AddressingMode::Absolute => {
                extract!(Operand::TwoBytes(addr));
                state.cpu_regs.pc = addr.into();
                should_push_pc = false;
                delay_cycles(3);
            },
            AddressingMode::Indirect => {
                extract!(Operand::TwoBytes(addr));
                let jump_target = state.read_le_u16(addr.into())?;
                state.cpu_regs.pc = Addr::from(jump_target);
                should_push_pc = false;
                delay_cycles(5);
            }
            _ => bad!(Addressing for JMP),
        },
        Instruction::PushAccumulator => {
            extract!(Implied None for PHA);
            state.push_byte(state.cpu_regs.a)?;
            delay_cycles(3);
        },
        Instruction::PushFlags => {
            extract!(Implied None for PHP);
            state.push_byte(state.cpu_regs.flags.value_to_push(false))?;
            delay_cycles(3);
        },
        Instruction::TransferRegisterXToStack => {
            extract!(Implied None for TXS);
            state.cpu_regs.sp = state.cpu_regs.x;
            delay_cycles(2);
        },
        Instruction::StoreRegisterX => match addressing_mode {
            AddressingMode::Absolute => {
                extract!(Operand::TwoBytes(addr));
                state.write_byte(state.cpu_regs.x, addr.into())?;
                delay_cycles(4);
            }
            AddressingMode::ZeroPage => {
                extract!(Operand::OneByte(zpaddr));
                state.write_byte(state.cpu_regs.x, Addr::from_u8(zpaddr))?;
                delay_cycles(3);
            },
            AddressingMode::ZeroPageIndexedY => {
                extract!(Operand::OneByte(base));
                let addr = base.wrapping_add(state.cpu_regs.y);
                state.write_byte(state.cpu_regs.x, Addr::from_u8(addr))?;
                delay_cycles(4);
            },
            _ => bad!(Addressing for STX),
        },
        Instruction::StoreRegisterY => match addressing_mode {
            AddressingMode::Absolute => {
                extract!(Operand::TwoBytes(addr));
                state.write_byte(state.cpu_regs.y, addr.into())?;
                delay_cycles(4);
            }
            AddressingMode::ZeroPage => {
                extract!(Operand::OneByte(zpaddr));
                state.write_byte(state.cpu_regs.y, Addr::from_u8(zpaddr))?;
                delay_cycles(3);
            },
            AddressingMode::ZeroPageIndexedX => {
                extract!(Operand::OneByte(base));
                let addr = base.wrapping_add(state.cpu_regs.x);
                state.write_byte(state.cpu_regs.y, Addr::from_u8(addr))?;
                delay_cycles(4);
            },
            _ => bad!(Addressing for STY),
        },
        Instruction::StoreAccumulator => {
            let (addr, cycles) = match addressing_mode {
                AddressingMode::Absolute => {
                    extract!(Operand::TwoBytes(addr));
                    (Addr::from(addr), 4)
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand::TwoBytes(base));
                    (Addr::from(base).offset(state.cpu_regs.x.into()), 5)
                },
                AddressingMode::AbsoluteIndexedY => {
                    extract!(Operand::TwoBytes(base));
                    (Addr::from(base).offset(state.cpu_regs.y.into()), 5)
                },
                AddressingMode::ZeroPage => {
                    extract!(Operand::OneByte(zpaddr));
                    (Addr::from_u8(zpaddr), 3)
                },
                AddressingMode::ZeroPageIndexedX => {
                    extract!(Operand::OneByte(base));
                    (Addr::from_u8(base.wrapping_add(state.cpu_regs.x)), 4)
                },
                AddressingMode::IndexedIndirect => {
                    extract!(Operand::OneByte(base));
                    let addr_location = Addr::from_u8(
                        base.wrapping_add(state.cpu_regs.x)
                    );
                    (state.read_le_u16(addr_location)?.into(), 6)
                },
                AddressingMode::IndirectIndexed => {
                    extract!(Operand::OneByte(base_addr));
                    let base = state.read_le_u16(Addr::from_u8(base_addr))?;
                    let addr = base.checked_add(state.cpu_regs.y.into()).unwrap();
                    (Addr::from(addr), 6)
                },
                _ => bad!(Addressing for STA),
            };
            state.write_byte(state.cpu_regs.a, addr)?;
            delay_cycles(cycles);
        },
        Instruction::TransferRegisterXToAcc => {
            extract!(Implied None for TXA);
            state.cpu_regs.a = state.cpu_regs.x;
            state.cpu_regs.flags.set_nz(state.cpu_regs.a);
            delay_cycles(2);
        },
        Instruction::TransferRegisterYToAcc => {
            extract!(Implied None for TYA);
            state.cpu_regs.a = state.cpu_regs.y;
            state.cpu_regs.flags.set_nz(state.cpu_regs.a);
            delay_cycles(2);
        },
        Instruction::TransferAccToRegisterX => {
            extract!(Implied None for TAX);
            state.cpu_regs.x = state.cpu_regs.a;
            state.cpu_regs.flags.set_nz(state.cpu_regs.x);
            delay_cycles(2);
        },
        Instruction::TransferAccToRegisterY => {
            extract!(Implied None for TAY);
            state.cpu_regs.y = state.cpu_regs.a;
            state.cpu_regs.flags.set_nz(state.cpu_regs.y);
            delay_cycles(2);
        },
        Instruction::TransferStackToRegisterX => {
            extract!(Implied None for TSX);
            state.cpu_regs.x = state.cpu_regs.sp;
            state.cpu_regs.flags.set_nz(state.cpu_regs.x);
            delay_cycles(2);
        },
        Instruction::SetCarryFlag => {
            extract!(Implied None for SEC);
            state.cpu_regs.flags.set_carry(true);
            delay_cycles(2);
        },
        Instruction::SetInterruptDisable => {
            extract!(Implied None for SEI);
            state.cpu_regs.flags.set_interrupt_disable(true);
            delay_cycles(2);
        },
        Instruction::ClearCarryFlag => {
            extract!(Implied None for CLC);
            state.cpu_regs.flags.set_carry(false);
            delay_cycles(2);
        },
        Instruction::ClearInterruptDisable => {
            extract!(Implied None for CLI);
            state.cpu_regs.flags.set_interrupt_disable(false);
            delay_cycles(2);
        },
        Instruction::ClearOverflowFlag => {
            extract!(Implied None for CLV);
            state.cpu_regs.flags.set_overflow(false);
            delay_cycles(2);
        },
        Instruction::IncrementMemory => {
            let (addr, cycles) = match addressing_mode {
                AddressingMode::Absolute => {
                    extract!(Operand::TwoBytes(addr));
                    (addr.into(), 6)
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand::TwoBytes(base));
                    (base.wrapping_add(state.cpu_regs.x.into()).into(), 7)
                },
                AddressingMode::ZeroPage => {
                    extract!(Operand::OneByte(zpaddr));
                    (Addr::from_u8(zpaddr), 5)
                },
                AddressingMode::ZeroPageIndexedX => {
                    extract!(Operand::OneByte(zpbase));
                    (Addr::from_u8(zpbase.wrapping_add(state.cpu_regs.x)), 6)
                },
                _ => bad!(Addressing for INC),
            };
            let orig = state.read_byte(addr)?;
            let new = orig.wrapping_add(1);
            state.cpu_regs.flags.set_nz(new);
            state.write_byte(new, addr)?;
            delay_cycles(cycles);
        },
        Instruction::IncrementRegisterX => {
            extract!(Implied None for INX);
            let incremented = state.cpu_regs.x.wrapping_add(1);
            state.cpu_regs.x = incremented;
            state.cpu_regs.flags.set_nz(incremented);
            delay_cycles(2);
        },
        Instruction::IncrementRegisterY => {
            extract!(Implied None for INY);
            let incremented = state.cpu_regs.y.wrapping_add(1);
            state.cpu_regs.y = incremented;
            state.cpu_regs.flags.set_nz(incremented);
            delay_cycles(2);
        },
        Instruction::DecrementMemory => {
            let (addr, cycles) = match addressing_mode {
                AddressingMode::Absolute => {
                    extract!(Operand::TwoBytes(addr));
                    (addr.into(), 6)
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand::TwoBytes(base));
                    (base.wrapping_add(state.cpu_regs.x.into()).into(), 7)
                },
                AddressingMode::ZeroPage => {
                    extract!(Operand::OneByte(zpaddr));
                    (Addr::from_u8(zpaddr), 5)
                },
                AddressingMode::ZeroPageIndexedX => {
                    extract!(Operand::OneByte(zpbase));
                    (Addr::from_u8(zpbase.wrapping_add(state.cpu_regs.x)), 6)
                },
                _ => bad!(Addressing for DEC),
            };
            let decremented = state.read_byte(addr)?.wrapping_sub(1);
            state.cpu_regs.flags.set_nz(decremented);
            state.write_byte(decremented, addr)?;
            delay_cycles(cycles);
        },
        Instruction::DecrementRegisterX => {
            extract!(Implied None for DEX);
            state.cpu_regs.x = state.cpu_regs.x.wrapping_sub(1);
            state.cpu_regs.flags.set_nz(state.cpu_regs.x);
            delay_cycles(2);
        },
        Instruction::DecrementRegisterY => {
            extract!(Implied None for DEY);
            state.cpu_regs.y = state.cpu_regs.y.wrapping_sub(1);
            state.cpu_regs.flags.set_nz(state.cpu_regs.y);
            delay_cycles(2);
        },
        Instruction::LoadAccumulator => {
            let (data, cycles) = match addressing_mode {
                AddressingMode::Immediate => {
                    extract!(Operand::OneByte(val));
                    (val, 2)
                },
                AddressingMode::Absolute => {
                    extract!(Operand::TwoBytes(addr));
                    (state.read_byte(addr.into())?, 4)
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand::TwoBytes(base));
                    let base = Addr::from(base);
                    let addr = base.offset(state.cpu_regs.x.into());
                    let increment = on_different_pages(base, addr);
                    (state.read_byte(addr)?, 4 + u8::from(increment))
                },
                AddressingMode::AbsoluteIndexedY => {
                    extract!(Operand::TwoBytes(base));
                    let base = Addr::from(base);
                    let addr = base.offset(state.cpu_regs.y.into());
                    let increment = on_different_pages(base, addr);
                    (state.read_byte(addr)?, 4 + u8::from(increment))
                },
                AddressingMode::ZeroPage => {
                    extract!(Operand::OneByte(zpaddr));
                    let addr = Addr::from_u8(zpaddr);
                    (state.read_byte(addr)?, 3)
                },
                AddressingMode::ZeroPageIndexedX => {
                    extract!(Operand::OneByte(zpbase));
                    let addr = Addr::from_u8(zpbase.wrapping_add(state.cpu_regs.x));
                    (state.read_byte(addr)?, 4)
                },
                AddressingMode::IndexedIndirect => {
                    extract!(Operand::OneByte(base));
                    let addrloc = Addr::from_u8(base.wrapping_add(state.cpu_regs.x));
                    let addr = state.read_le_u16(addrloc)?.into();
                    (state.read_byte(addr)?, 6)
                },
                AddressingMode::IndirectIndexed => {
                    extract!(Operand::OneByte(baseloc));
                    let base = state.read_le_u16(Addr::from_u8(baseloc))?;
                    let addr = base.checked_add(state.cpu_regs.y.into()).unwrap();
                    let cycles = 5 +
                        u8::from(on_different_pages(base.into(), addr.into()));
                    (state.read_byte(addr.into())?, cycles)
                },
                _ => bad!(Addressing for LDA),
            };
            state.cpu_regs.a = data;
            state.cpu_regs.flags.set_nz(data);
            delay_cycles(cycles);
        },
        Instruction::LoadRegisterX => {
            let (addr, cycles) = match addressing_mode {
                AddressingMode::Immediate => (None, 2),
                AddressingMode::Absolute => {
                    extract!(Operand::TwoBytes(addr));
                    (Some(Addr::from(addr)), 4)
                },
                AddressingMode::AbsoluteIndexedY => {
                    extract!(Operand::TwoBytes(base));
                    let base = Addr::from(base);
                    let addr = base.offset(state.cpu_regs.y.into());
                    let increment = on_different_pages(base, addr);
                    (Some(addr), (4 + u8::from(increment)))
                },
                AddressingMode::ZeroPage => {
                    extract!(Operand::OneByte(zpaddr));
                    (Some(Addr::from_u8(zpaddr)), 3)
                },
                AddressingMode::ZeroPageIndexedY => {
                    extract!(Operand::OneByte(zpbase));
                    let addr = zpbase.wrapping_add(state.cpu_regs.y);
                    (Some(Addr::from_u8(addr)), 4)
                },
                _ => bad!(Addressing for LDX),
            };
            let value = match addr {
                Some(addr) => state.read_byte(addr)?,
                None => {
                    extract!(Operand::OneByte(immediate));
                    immediate
                },
            };
            state.cpu_regs.x = value;
            state.cpu_regs.flags.set_nz(value);
            delay_cycles(cycles);
        },
        Instruction::LoadRegisterY => {
            let (addr, cycles) = match addressing_mode {
                AddressingMode::Immediate => (None, 2),
                AddressingMode::Absolute => {
                    extract!(Operand::TwoBytes(addr));
                    (Some(addr.into()), 4)
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand::TwoBytes(base));
                    let base = Addr::from(base);
                    let addr = base.offset(state.cpu_regs.x.into());
                    let increment = on_different_pages(base, addr);
                    (Some(addr), 4 + u8::from(increment))
                },
                AddressingMode::ZeroPage => {
                    extract!(Operand::OneByte(zpaddr));
                    (Some(Addr::from_u8(zpaddr)), 3)
                },
                AddressingMode::ZeroPageIndexedX => {
                    extract!(Operand::OneByte(zpbase));
                    let addr = zpbase.wrapping_add(state.cpu_regs.x);
                    (Some(Addr::from_u8(addr)), 4)
                },
                _ => bad!(Addressing for LDY),
            };
            let value = match addr {
                Some(addr) => state.read_byte(addr)?,
                None => {
                    extract!(Operand::OneByte(immediate));
                    immediate
                },
            };
            state.cpu_regs.x = value;
            state.cpu_regs.flags.set_nz(value);
            delay_cycles(cycles);
        },
        Instruction::BranchOnCarryClear    => branch!(BCC: flags.get_carry().not()),
        Instruction::BranchOnCarrySet      => branch!(BCS: flags.get_carry()),
        Instruction::BranchOnEqual         => branch!(BEQ: flags.get_zero()),
        Instruction::BranchOnNotEqual      => branch!(BNE: flags.get_zero().not()),
        Instruction::BranchOnMinus         => branch!(BMI: flags.get_negative()),
        Instruction::BranchOnPlus          => branch!(BPL: flags.get_negative().not()),
        Instruction::BranchOnOverflowClear => branch!(BVC: flags.get_overflow().not()),
        Instruction::BranchOnOverflowSet   => branch!(BVS: flags.get_overflow()),
        Instruction::PullAccumulator => {
            extract!(Implied None for PLA);
            state.cpu_regs.a = state.pop_byte()?;
            state.cpu_regs.flags.set_nz(state.cpu_regs.a);
            delay_cycles(4);
        },
        Instruction::PullFlags => {
            extract!(Implied None for PLP);
            let flags = CpuFlags::from_pulled_value(state.pop_byte()?);
            state.cpu_regs.flags = flags;
            delay_cycles(4);
        },
        Instruction::RotateLeft => {
            fn rol_calc(input: u8, flags: &mut CpuFlags) -> u8 {
                let mut bits = bv::BitArray::<u8, bv::Lsb0>::new(input);
                let carry_out = bits[7];
                // ABCDEFGH -> BCDEFGH0
                bits.copy_within(0..7, 1);
                bits.set(0, flags.get_carry());
                flags.set_carry(carry_out);
                let out = bits.into_inner();
                flags.set_nz(out);
                out
            }
            match addressing_mode {
                AddressingMode::Accumulator => {
                    extract!(Operand::None);
                    state.cpu_regs.a = rol_calc(state.cpu_regs.a, &mut state.cpu_regs.flags);
                    delay_cycles(2);
                },
                AddressingMode::Absolute => {
                    extract!(Operand::TwoBytes(addr));
                    let addr = Addr::from(addr);
                    let input = state.read_byte(addr)?;
                    let out = rol_calc(input, &mut state.cpu_regs.flags);
                    state.write_byte(out, addr)?;
                    delay_cycles(6);
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand::TwoBytes(addr));
                    let addr = Addr::from(addr.wrapping_add(state.cpu_regs.x.into()));
                    let input = state.read_byte(addr)?;
                    let out = rol_calc(input, &mut state.cpu_regs.flags);
                    state.write_byte(out, addr)?;
                    delay_cycles(7);
                },
                AddressingMode::ZeroPage => {
                    extract!(Operand::OneByte(zpaddr));
                    let addr = Addr::from_u8(zpaddr);
                    let input = state.read_byte(addr)?;
                    let out = rol_calc(input, &mut state.cpu_regs.flags);
                    state.write_byte(out, addr)?;
                    delay_cycles(5);
                },
                AddressingMode::ZeroPageIndexedX => {
                    extract!(Operand::OneByte(zpbase));
                    let addr = Addr::from_u8(zpbase.wrapping_add(state.cpu_regs.x));
                    let input = state.read_byte(addr)?;
                    let out = rol_calc(input, &mut state.cpu_regs.flags);
                    state.write_byte(out, addr)?;
                    delay_cycles(6);
                },
                _ => bad!(Addressing for ROL),
            }
        },
        // 16 more
        _ => todo!()
    }

    if should_push_pc {
        let new = state.cpu_regs.pc
            .into_num()
            .checked_add(1 + u16::from(operand.size_bytes()))
            .expect("execution should not overflow the address space");
        state.cpu_regs.pc = Addr::from(new);
    }

    Ok(())
}

/// Common code for all branch instructions.
/// The new program count will include incrementing past the branch
/// if the condition is false and the branch is not taken.
fn branch_common(current_pc: &mut Addr, offset: i8, take_branch: bool) {
    let current = *current_pc;
    let target_address = current.offset(offset.into());
    let following_address = current.offset(2);
    let page_increment = on_different_pages(following_address, target_address);
    *current_pc = if take_branch {
        target_address
    } else {
        following_address
    };
    let cycles = match take_branch {
        false => 2,
        true => 3 + u8::from(page_increment),
    };
    delay_cycles(cycles);
}

fn on_different_pages(lhs: Addr, rhs: Addr) -> bool {
    const PAGE_SIZE: u16 = 256; // u8::MAX
    (lhs.into_num() / PAGE_SIZE) != (rhs.into_num() / PAGE_SIZE)
}

#[cfg(test)]
mod tests {
    #[test]
    fn different_pages() {
        use super::on_different_pages;

        assert!(on_different_pages(0xBEFF.into(), 0xBC00.into()));
        assert!(!on_different_pages(0x1200.into(), 0x12FF.into()));
    }
}
