use crate::{
    Addr,
    AddressingMode,
    FullInstruction, InstructionWithMode, Instruction,
    Operand,
    CpuFlags, CpuRegisters,
};
use super::{State, Fault, delay_cycles};

use bitvec::prelude as bv;

type Lsb0BitArray<T> = bv::BitArray<T, bv::Lsb0>;

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
// This function shouldn't really be a thousand lines but it is
// Sorry, Clippy. (and any future maintainers of this code)
pub(super) fn exec_instruction(state: &mut State, inst: FullInstruction) -> Result<(), Fault> {
    use std::ops::Not as _;

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
            return Err(Fault::InternalError(super::InternalErrorFault {
                kind: super::InternalFaultKind::InvalidAddressingMode(addressing_mode),
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
            return Err(Fault::InternalError(super::InternalErrorFault {
                kind: super::InternalFaultKind::InvalidOperandType,
            }));
        }}
    }
    
    macro_rules! extract {
        (Operand::None) => {{
            let Operand::None = operand else {
                bad!(Operand expected None);
            };
        }};
        (Operand($addr:ident)) => {
            extract!(Operand::TwoBytes(_tmp_addr_value));
            // This has to use the user's token to keep the span
            extract!(@@internal assert_addr $addr);
            let $addr = $crate::Addr::from_num(_tmp_addr_value);
        };
        (Operand(addr $name:ident)) => {
            extract!(Operand::TwoBytes(_tmp_addr_value));
            let $name = $crate::Addr::from_num(_tmp_addr_value);
        };
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
        (@@internal assert_addr addr) => {};
        (@@internal assert_addr $not_addr:ident) => {
            compile_error!("expected Operand(addr). To use an arbitrary name \
            use extract!(Operand(addr <$name>))");
        };
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

    macro_rules! zpcalc {
        (offset $offset:tt) => {{
            extract!(Operand::OneByte(zpaddr));
            $crate::Addr::from_u8(u8::wrapping_add(
                zpaddr,
                zpcalc!(@@internal pick-offset $offset),
            ))
        }};
        (@@internal pick-offset X) => {{ state.cpu_regs.x }};
        (@@internal pick-offset Y) => {{ state.cpu_regs.y }};
        (@@internal pick-offset 0) => {{ 0u8 }};
    }

    match instruction {
        Instruction::NoOp => {
            extract!(Implied None for NOP);
            delay_cycles(2);
        },
        Instruction::Jump => match addressing_mode {
            AddressingMode::Absolute => {
                extract!(Operand(addr));
                state.cpu_regs.pc = addr;
                should_push_pc = false;
                delay_cycles(3);
            },
            AddressingMode::Indirect => {
                extract!(Operand(addr));
                let jump_target = state.read_le_u16(addr)?;
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
                extract!(Operand(addr));
                state.write_byte(state.cpu_regs.x, addr)?;
                delay_cycles(4);
            }
            AddressingMode::ZeroPage => {
                state.write_byte(state.cpu_regs.x, zpcalc!(offset 0))?;
                delay_cycles(3);
            },
            AddressingMode::ZeroPageIndexedY => {
                state.write_byte(state.cpu_regs.x, zpcalc!(offset Y))?;
                delay_cycles(4);
            },
            _ => bad!(Addressing for STX),
        },
        Instruction::StoreRegisterY => match addressing_mode {
            AddressingMode::Absolute => {
                extract!(Operand(addr));
                state.write_byte(state.cpu_regs.y, addr)?;
                delay_cycles(4);
            }
            AddressingMode::ZeroPage => {
                state.write_byte(state.cpu_regs.y, zpcalc!(offset 0))?;
                delay_cycles(3);
            },
            AddressingMode::ZeroPageIndexedX => {
                state.write_byte(state.cpu_regs.y, zpcalc!(offset X))?;
                delay_cycles(4);
            },
            _ => bad!(Addressing for STY),
        },
        Instruction::StoreAccumulator => {
            let (addr, cycles) = match addressing_mode {
                AddressingMode::Absolute => {
                    extract!(Operand(addr));
                    (addr, 4)
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand(addr base));
                    (base.offset(state.cpu_regs.x), 5)
                },
                AddressingMode::AbsoluteIndexedY => {
                    extract!(Operand(addr base));
                    (base.offset(state.cpu_regs.y), 5)
                },
                AddressingMode::ZeroPage => (zpcalc!(offset 0), 3),
                AddressingMode::ZeroPageIndexedX => (zpcalc!(offset X), 4),
                AddressingMode::IndexedIndirect => {
                    let addr_location = zpcalc!(offset X);
                    let addr = state.read_le_u16(addr_location)?;
                    (addr.into(), 6)
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
                    extract!(Operand(addr));
                    (addr, 6)
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand(addr base));
                    (base.offset(state.cpu_regs.x), 7)
                },
                AddressingMode::ZeroPage => (zpcalc!(offset 0), 5),
                AddressingMode::ZeroPageIndexedX => (zpcalc!(offset X), 6),
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
                    extract!(Operand(addr));
                    (addr, 6)
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand(addr base));
                    (base.offset(state.cpu_regs.x), 7)
                },
                AddressingMode::ZeroPage => (zpcalc!(offset 0), 5),
                AddressingMode::ZeroPageIndexedX => (zpcalc!(offset X), 6),
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
                    extract!(Operand(addr));
                    (state.read_byte(addr)?, 4)
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.x);
                    let increment = on_different_pages(base, addr);
                    (state.read_byte(addr)?, 4 + u8::from(increment))
                },
                AddressingMode::AbsoluteIndexedY => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.y);
                    let increment = on_different_pages(base, addr);
                    (state.read_byte(addr)?, 4 + u8::from(increment))
                },
                AddressingMode::ZeroPage => {
                    (state.read_byte(zpcalc!(offset 0))?, 3)
                },
                AddressingMode::ZeroPageIndexedX => {
                    (state.read_byte(zpcalc!(offset X))?, 4)
                },
                AddressingMode::IndexedIndirect => {
                    let addrloc = zpcalc!(offset X);
                    let addr = state.read_le_u16(addrloc)?.into();
                    (state.read_byte(addr)?, 6)
                },
                AddressingMode::IndirectIndexed => {
                    extract!(Operand::OneByte(baseloc));
                    let base = state.read_le_u16(Addr::from_u8(baseloc))?;
                    let addr = base.checked_add(state.cpu_regs.y.into()).unwrap();
                    let increment = on_different_pages(base.into(), addr.into());
                    let cycles = 5 + u8::from(increment);
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
                    extract!(Operand(addr));
                    (Some(addr), 4)
                },
                AddressingMode::AbsoluteIndexedY => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.y);
                    let increment = on_different_pages(base, addr);
                    (Some(addr), (4 + u8::from(increment)))
                },
                AddressingMode::ZeroPage         => (Some(zpcalc!(offset 0)), 3),
                AddressingMode::ZeroPageIndexedY => (Some(zpcalc!(offset Y)), 4),
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
                    extract!(Operand(addr));
                    (Some(addr), 4)
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.x);
                    let increment = on_different_pages(base, addr);
                    (Some(addr), 4 + u8::from(increment))
                },
                AddressingMode::ZeroPage         => (Some(zpcalc!(offset 0)), 3),
                AddressingMode::ZeroPageIndexedX => (Some(zpcalc!(offset X)), 4),
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
                let mut bits = Lsb0BitArray::new(input);
                let carry_out = bits[7];
                // ABCDEFGH -> BCDEFGH0
                bits.copy_within(0..8, 1);
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
                    extract!(Operand(addr));
                    let input = state.read_byte(addr)?;
                    let out = rol_calc(input, &mut state.cpu_regs.flags);
                    state.write_byte(out, addr)?;
                    delay_cycles(6);
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.x);
                    let input = state.read_byte(addr)?;
                    let out = rol_calc(input, &mut state.cpu_regs.flags);
                    state.write_byte(out, addr)?;
                    delay_cycles(7);
                },
                AddressingMode::ZeroPage => {
                    let addr = zpcalc!(offset 0);
                    let input = state.read_byte(addr)?;
                    let out = rol_calc(input, &mut state.cpu_regs.flags);
                    state.write_byte(out, addr)?;
                    delay_cycles(5);
                },
                AddressingMode::ZeroPageIndexedX => {
                    let addr = zpcalc!(offset X);
                    let input = state.read_byte(addr)?;
                    let out = rol_calc(input, &mut state.cpu_regs.flags);
                    state.write_byte(out, addr)?;
                    delay_cycles(6);
                },
                _ => bad!(Addressing for ROL),
            }
        },
        Instruction::AndMemory => {
            let (val, cycles) = match addressing_mode {
                AddressingMode::Immediate => {
                    extract!(Operand::OneByte(immediate));
                    (immediate, 2)
                },
                AddressingMode::Absolute => {
                    extract!(Operand(addr));
                    (state.read_byte(addr)?, 4)
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.x);
                    let increment = u8::from(on_different_pages(base, addr));
                    (state.read_byte(addr)?, 4 + increment)
                },
                AddressingMode::AbsoluteIndexedY => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.y);
                    let increment = u8::from(on_different_pages(base, addr));
                    (state.read_byte(addr)?, 4 + increment)
                },
                AddressingMode::ZeroPage => {
                    (state.read_byte(zpcalc!(offset 0))?, 3)
                },
                AddressingMode::ZeroPageIndexedX => {
                    (state.read_byte(zpcalc!(offset X))?, 4)
                },
                AddressingMode::IndexedIndirect => {
                    let addr_ptr = zpcalc!(offset X);
                    let addr = Addr::from(state.read_le_u16(addr_ptr)?);
                    (state.read_byte(addr)?, 6)
                },
                AddressingMode::IndirectIndexed => {
                    extract!(Operand::OneByte(baseloc));
                    let base = Addr::from(state.read_le_u16(Addr::from_u8(baseloc))?);
                    let addr = base.offset(state.cpu_regs.y);
                    let increment = u8::from(on_different_pages(base, addr));
                    (state.read_byte(addr)?, 5 + increment)
                },
                _ => bad!(Addressing for AND),
            };
            state.cpu_regs.a &= val;
            state.cpu_regs.flags.set_nz(state.cpu_regs.a);
            delay_cycles(cycles);
        },
        Instruction::OrMemory => {
            let (value, cycles) = match addressing_mode {
                AddressingMode::Immediate => {
                    extract!(Operand::OneByte(immediate));
                    (immediate, 2)
                },
                AddressingMode::Absolute => {
                    extract!(Operand(addr));
                    (state.read_byte(addr)?, 4)
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.x);
                    let increment = u8::from(on_different_pages(base, addr));
                    (state.read_byte(addr)?, 4 + increment)
                },
                AddressingMode::AbsoluteIndexedY => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.y);
                    let increment = u8::from(on_different_pages(base, addr));
                    (state.read_byte(addr)?, 4 + increment)
                },
                AddressingMode::ZeroPage => {
                    (state.read_byte(zpcalc!(offset 0))?, 3)
                },
                AddressingMode::ZeroPageIndexedX => {
                    (state.read_byte(zpcalc!(offset X))?, 4)
                },
                AddressingMode::IndexedIndirect => {
                    let addr_ptr = zpcalc!(offset X);
                    let addr = Addr::from(state.read_le_u16(addr_ptr)?);
                    (state.read_byte(addr)?, 6)
                },
                AddressingMode::IndirectIndexed => {
                    extract!(Operand::OneByte(addr_ptr));
                    let addr_ptr = Addr::from_u8(addr_ptr);
                    let base = Addr::from(state.read_le_u16(addr_ptr)?);
                    let addr = base.offset(state.cpu_regs.y);
                    let increment = u8::from(on_different_pages(base, addr));
                    (state.read_byte(addr)?, 5 + increment)
                },
                _ => bad!(Addressing for ORA),
            };
            state.cpu_regs.a |= value;
            state.cpu_regs.flags.set_nz(state.cpu_regs.a);
            delay_cycles(cycles);
        },
        Instruction::ExclusiveOr => {
            fn xor(input: u8, regs: &mut CpuRegisters) {
                regs.a ^= input;
                regs.flags.set_nz(regs.a);
            }
            match addressing_mode {
                AddressingMode::Immediate => {
                    extract!(Operand::OneByte(immediate));
                    xor(immediate, &mut state.cpu_regs);
                    delay_cycles(2);
                },
                AddressingMode::Absolute => {
                    extract!(Operand(addr));
                    xor(state.read_byte(addr)?, &mut state.cpu_regs);
                    delay_cycles(4);
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.x);
                    xor(state.read_byte(addr)?, &mut state.cpu_regs);
                    let increment = u8::from(on_different_pages(base, addr));
                    delay_cycles(4 + increment);
                },
                AddressingMode::AbsoluteIndexedY => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.y);
                    xor(state.read_byte(addr)?, &mut state.cpu_regs);
                    let increment = u8::from(on_different_pages(base, addr));
                    delay_cycles(4 + increment);
                },
                AddressingMode::ZeroPage => {
                    xor(state.read_byte(zpcalc!(offset 0))?, &mut state.cpu_regs);
                    delay_cycles(3);
                },
                AddressingMode::ZeroPageIndexedX => {
                    xor(state.read_byte(zpcalc!(offset X))?, &mut state.cpu_regs);
                    delay_cycles(4);
                },
                AddressingMode::IndexedIndirect => {
                    let addr_ptr = zpcalc!(offset X);
                    let addr = Addr::from(state.read_le_u16(addr_ptr)?);
                    xor(state.read_byte(addr)?, &mut state.cpu_regs);
                    delay_cycles(6);
                },
                AddressingMode::IndirectIndexed => {
                    extract!(Operand::OneByte(base_ptr));
                    let base = Addr::from(
                        state.read_le_u16(Addr::from_u8(base_ptr))?
                    );
                    let addr = base.offset(state.cpu_regs.y);
                    xor(state.read_byte(addr)?, &mut state.cpu_regs);
                    let increment = u8::from(on_different_pages(base, addr));
                    delay_cycles(5 + increment);
                },
                _ => bad!(Addressing for EOR),
            };
        },
        Instruction::TestBits => {
            let (addr, cycles) = match addressing_mode {
                AddressingMode::Absolute => {
                    extract!(Operand(addr));
                    (addr, 4)
                },
                AddressingMode::ZeroPage => (zpcalc!(offset 0), 3),
                _ => bad!(Addressing for BIT),
            };
            let value = state.read_byte(addr)?;
            let and_result = value & state.cpu_regs.a;
            let value = Lsb0BitArray::new(value);
            state.cpu_regs.flags.set_negative(value[7]);
            state.cpu_regs.flags.set_overflow(value[6]);
            state.cpu_regs.flags.set_zero(and_result == 0);
            delay_cycles(cycles);
        },
        Instruction::JumpToSubroutine => {
            let AddressingMode::Absolute = addressing_mode else {
                bad!(Addressing for JSR);
            };
            extract!(Operand(addr target_addr));
            let to_push = state.cpu_regs.pc.offset(2u8);
            let [low, high] = to_push.into_num().to_le_bytes();
            state.push_byte(high)?;
            state.push_byte(low)?;
            state.cpu_regs.pc = target_addr;
            should_push_pc = false;
            delay_cycles(6);
        },
        Instruction::ReturnFromSubroutine => {
            extract!(Implied None for RTS);
            let low = state.pop_byte()?;
            let high = state.pop_byte()?;
            let pc = Addr::from_num(u16::from_le_bytes([low, high]));
            state.cpu_regs.pc = pc.offset(1u8);
            should_push_pc = false;
            delay_cycles(6);
        },
        Instruction::Break => {
            extract!(Implied None for BRK);
            let pc_to_push = state.cpu_regs.pc.offset(2u8);
            let [low, high] = pc_to_push.into_num().to_le_bytes();
            state.push_byte(high)?;
            state.push_byte(low)?;
            state.cpu_regs.pc = state.interrupt_vector()?;
            should_push_pc = false;
            delay_cycles(7);
        },
        Instruction::ReturnFromInterrupt => {
            extract!(Implied None for RTI);
            let flags = state.pop_byte()?;
            state.cpu_regs.flags = CpuFlags::from_pulled_value(flags);
            let pc_low = state.pop_byte()?;
            let pc_high = state.pop_byte()?;
            let new_pc = Addr::from_num(u16::from_le_bytes([pc_high, pc_low]));
            state.cpu_regs.pc = new_pc;
            should_push_pc = false;
            delay_cycles(6);
        },
        Instruction::ArithmeticShiftLeft => {
            fn asl_impl(input: u8, flags: &mut CpuFlags) -> u8 {
                let mut value = Lsb0BitArray::new(input);
                let carry_out = value[7];
                value.copy_within(0..8, 1);
                value.set(0, false);
                let output = value.into_inner();
                flags.set_nz(output);
                flags.set_carry(carry_out);
                output
            }
            let (addr, cycles) = match addressing_mode {
                AddressingMode::Accumulator => {
                    (None, 2)
                },
                AddressingMode::Absolute => {
                    extract!(Operand(addr));
                    (Some(addr), 6)
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand(addr base));
                    (Some(base.offset(state.cpu_regs.x)), 7)
                },
                AddressingMode::ZeroPage         => (Some(zpcalc!(offset 0)), 5),
                AddressingMode::ZeroPageIndexedX => (Some(zpcalc!(offset X)), 6),
                _ => bad!(Addressing for ASL),
            };
            match addr {
                // Accumulator
                None => {
                    let val = asl_impl(state.cpu_regs.a, &mut state.cpu_regs.flags);
                    state.cpu_regs.a = val;
                },
                Some(addr) => {
                    let input = state.read_byte(addr)?;
                    let out = asl_impl(input, &mut state.cpu_regs.flags);
                    state.write_byte(out, addr)?;
                },
            }
            delay_cycles(cycles);
        },
        Instruction::CompareAccumulator => {
            let (addr, cycles) = match addressing_mode {
                AddressingMode::Immediate => (None, 2),
                AddressingMode::Absolute => {
                    extract!(Operand(addr));
                    (Some(addr), 4)
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.x);
                    let increment = u8::from(on_different_pages(base, addr));
                    (Some(addr), 4 + increment)
                },
                AddressingMode::AbsoluteIndexedY => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.y);
                    let increment = u8::from(on_different_pages(base, addr));
                    (Some(addr), 4 + increment)
                },
                AddressingMode::ZeroPage         => (Some(zpcalc!(offset 0)), 3),
                AddressingMode::ZeroPageIndexedX => (Some(zpcalc!(offset X)), 4),
                AddressingMode::IndexedIndirect => {
                    let addr_ptr = zpcalc!(offset X);
                    let addr = Addr::from(state.read_le_u16(addr_ptr)?);
                    (Some(addr), 6)
                },
                AddressingMode::IndirectIndexed => {
                    extract!(Operand::OneByte(base_ptr));
                    let base = Addr::from(state.read_le_u16(Addr::from_u8(base_ptr))?);
                    let addr = base.offset(state.cpu_regs.y);
                    let increment = u8::from(on_different_pages(base, addr));
                    (Some(addr), 5 + increment)
                },
                _ => bad!(Addressing for CMP),
            };
            match addr {
                None => {
                    extract!(Operand::OneByte(immediate));
                    cmp_impl(
                        immediate, &mut state.cpu_regs.flags,
                        state.cpu_regs.a
                    );
                },
                Some(addr) => cmp_impl(
                    state.read_byte(addr)?,
                    &mut state.cpu_regs.flags,
                    state.cpu_regs.a,
                ),
            }
            delay_cycles(cycles);
        },
        Instruction::CompareXRegister => {
            let (value, cycles) = match addressing_mode {
                AddressingMode::Immediate => {
                    extract!(Operand::OneByte(immediate));
                    (immediate, 2)
                },
                AddressingMode::Absolute => {
                    extract!(Operand(addr));
                    (state.read_byte(addr)?, 4)
                },
                AddressingMode::ZeroPage => {
                    let addr = zpcalc!(offset 0);
                    (state.read_byte(addr)?, 3)
                },
                _ => bad!(Addressing for CPX),
            };
            cmp_impl(value, &mut state.cpu_regs.flags, state.cpu_regs.x);
            delay_cycles(cycles);
        },
        Instruction::CompareYRegister => {
            let (value, cycles) = match addressing_mode {
                AddressingMode::Immediate => {
                    extract!(Operand::OneByte(immediate));
                    (immediate, 2)
                },
                AddressingMode::Absolute => {
                    extract!(Operand(addr));
                    (state.read_byte(addr)?, 4)
                },
                AddressingMode::ZeroPage => {
                    let addr = zpcalc!(offset 0);
                    (state.read_byte(addr)?, 3)
                },
                _ => bad!(Addressing for CPY),
            };
            cmp_impl(value, &mut state.cpu_regs.flags, state.cpu_regs.y);
            delay_cycles(cycles);
        },
        Instruction::LogicalShiftRight => {
            fn lsr_impl(input: u8, flags: &mut CpuFlags) -> u8 {
                let input = Lsb0BitArray::new(input);
                flags.set_carry(input[0]);
                let output = {
                    let mut input = input;
                    input.copy_within(1..8, 0);
                    input.set(7, false);
                    input
                };
                output.into_inner()
            }
            let (addr, cycles) = match addressing_mode {
                AddressingMode::Accumulator => (None, 2),
                AddressingMode::Absolute => {
                    extract!(Operand(addr));
                    (Some(addr), 6)
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.x);
                    (Some(addr), 7)
                },
                AddressingMode::ZeroPage         => (Some(zpcalc!(offset 0)), 5),
                AddressingMode::ZeroPageIndexedX => (Some(zpcalc!(offset X)), 6),
                _ => bad!(Addressing for LSR),
            };
            match addr {
                None => {
                    let output = lsr_impl(state.cpu_regs.a, &mut state.cpu_regs.flags);
                    state.cpu_regs.a = output;
                },
                Some(addr) => {
                    let input = state.read_byte(addr)?;
                    let output = lsr_impl(input, &mut state.cpu_regs.flags);
                    state.cpu_regs.a = output;
                },
            }
            delay_cycles(cycles);
        },
        Instruction::RotateRight => {
            fn ror_impl(input: u8, flags: &mut CpuFlags) -> u8 {
                flags.set_negative(flags.get_carry());
                let input = Lsb0BitArray::new(input);
                let output_carry = input[0];
                let output = {
                    let mut input = input;
                    input.copy_within(1..8, 0);
                    input.set(7, flags.get_carry());
                    input.into_inner()
                };
                flags.set_carry(output_carry);
                flags.set_zero(output == 0);
                output
            }
            let (addr, cycles) = match addressing_mode {
                AddressingMode::Accumulator => (None, 2),
                AddressingMode::Absolute => {
                    extract!(Operand(addr));
                    (Some(addr), 6)
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.x);
                    (Some(addr), 7)
                },
                AddressingMode::ZeroPage         => (Some(zpcalc!(offset 0)), 5),
                AddressingMode::ZeroPageIndexedX => (Some(zpcalc!(offset X)), 6),
                _ => bad!(Addressing for ROR),
            };
            match addr {
                // Accumulator
                None => {
                    let output = ror_impl(state.cpu_regs.a, &mut state.cpu_regs.flags);
                    state.cpu_regs.a = output;
                },
                Some(addr) => {
                    let input = state.read_byte(addr)?;
                    let out = ror_impl(input, &mut state.cpu_regs.flags);
                    state.write_byte(out, addr)?;
                },
            }
            delay_cycles(cycles);
        },
        Instruction::AddWithCarry => {
            let (addr, cycles) = match addressing_mode {
                AddressingMode::Immediate => (None, 2),
                AddressingMode::Absolute => {
                    extract!(Operand(addr));
                    (Some(addr), 4)
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.x);
                    let increment = u8::from(on_different_pages(base, addr));
                    (Some(addr), 4 + increment)
                },
                AddressingMode::AbsoluteIndexedY => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.y);
                    let increment = u8::from(on_different_pages(base, addr));
                    (Some(addr), 4 + increment)
                },
                AddressingMode::ZeroPage => {
                    let addr = zpcalc!(offset 0);
                    (Some(addr), 3)
                },
                AddressingMode::ZeroPageIndexedX => {
                    let addr = zpcalc!(offset X);
                    (Some(addr), 4)
                },
                AddressingMode::IndexedIndirect => {
                    let addr_ptr = zpcalc!(offset X);
                    let addr = Addr::from(state.read_le_u16(addr_ptr)?);
                    (Some(addr), 6)
                },
                AddressingMode::IndirectIndexed => {
                    let addr_ptr = zpcalc!(offset 0);
                    let base = Addr::from(state.read_le_u16(addr_ptr)?);
                    let addr = base.offset(state.cpu_regs.y);
                    let increment = u8::from(on_different_pages(base, addr));
                    (Some(addr), 5 + increment)
                },
                _ => bad!(Addressing for ADC),
            };
            let input = match addr {
                None => {
                    extract!(Operand::OneByte(immediate));
                    immediate
                },
                Some(addr) => state.read_byte(addr)?,
            };
            let orig_sign_bit = Lsb0BitArray::new(input)[7];
            let (result, carry) = overflowing_add_with_carry(
                state.cpu_regs.a, input,
                state.cpu_regs.flags.get_carry(),
            );
            let new_sign_bit = Lsb0BitArray::new(result)[7];
            state.cpu_regs.flags.set_overflow(orig_sign_bit != new_sign_bit);
            state.cpu_regs.flags.set_carry(carry);
            state.cpu_regs.flags.set_nz(result);
            state.cpu_regs.a = result;
            delay_cycles(cycles);
        },
        Instruction::SubtractWithCarry => {
            let (addr, cycles) = match addressing_mode {
                AddressingMode::Immediate => (None, 2),
                AddressingMode::Absolute => {
                    extract!(Operand(addr));
                    (Some(addr), 4)
                },
                AddressingMode::AbsoluteIndexedX => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.x);
                    let increment = u8::from(on_different_pages(base, addr));
                    (Some(addr), 4 + increment)
                },
                AddressingMode::AbsoluteIndexedY => {
                    extract!(Operand(addr base));
                    let addr = base.offset(state.cpu_regs.y);
                    let increment = u8::from(on_different_pages(base, addr));
                    (Some(addr), 4 + increment)
                },
                AddressingMode::ZeroPage         => (Some(zpcalc!(offset 0)), 3),
                AddressingMode::ZeroPageIndexedX => (Some(zpcalc!(offset X)), 4),
                AddressingMode::IndexedIndirect => {
                    let addr_ptr = zpcalc!(offset X);
                    let addr = Addr::from(state.read_le_u16(addr_ptr)?);
                    (Some(addr), 6)
                },
                AddressingMode::IndirectIndexed => {
                    let base_ptr = zpcalc!(offset 0);
                    let base = Addr::from(state.read_le_u16(base_ptr)?);
                    let addr = base.offset(state.cpu_regs.y);
                    let increment = u8::from(on_different_pages(base, addr));
                    (Some(addr), 5 + increment)
                },
                _ => bad!(Addressing for SBC),
            };
            let input = match addr {
                None => {
                    extract!(Operand::OneByte(immediate));
                    immediate
                },
                Some(addr) => state.read_byte(addr)?,
            };
            // Honestly not entirely sure about this code
            // https://www.pagetable.com/c64ref/6502/?tab=2#SBC
            let old_sign = Lsb0BitArray::new(input)[7];
            let (result, carry) = overflowing_sub_with_carry(
                state.cpu_regs.a, input,
                state.cpu_regs.flags.get_carry(),
            );
            let new_sign = Lsb0BitArray::new(result)[7];
            state.cpu_regs.flags.set_overflow(old_sign != new_sign);
            state.cpu_regs.flags.set_carry(carry);
            state.cpu_regs.flags.set_nz(result);
            state.cpu_regs.a = result;
            delay_cycles(cycles);
        },
        // 0 more!!
        // _ => todo!()
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
    let target_address = current.offset(offset);
    let following_address = current.offset(2u8);
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

/// Compares the input from memory to the `register`.
/// Sets the flags accordingly.
fn cmp_impl(input: u8, flags: &mut CpuFlags, register: u8) {
    let result = register.wrapping_sub(input);
    flags.set_nz(result);
    flags.set_carry(input <= register);
}

/// (Unstable) [`u8::carrying_add`].
fn overflowing_add_with_carry(lhs: u8, rhs: u8, carry: bool) -> (u8, bool) {
    let (res1, c1) = lhs.overflowing_add(rhs);
    let (final_sum, c2) = res1.overflowing_add(u8::from(carry));
    (final_sum, c1 || c2)
}

/// (Unstable) [`u8::borrowing_sub`].
fn overflowing_sub_with_carry(lhs: u8, rhs: u8, carry: bool) -> (u8, bool) {
    let (r1, c1) = lhs.overflowing_sub(rhs);
    let (r2, c2) = r1.overflowing_sub(u8::from(carry));
    (r2, c1 || c2)
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

    #[test]
    fn carrying_add() {
        use super::overflowing_add_with_carry as oawc;
        assert_eq!(oawc(10, 2, true), (13, false));
        assert_eq!(oawc(255, 2, false), (1, true));
        assert_eq!(oawc(100, 155, true), (0, true));
    }

    #[test]
    fn borrowing_sub() {
        use super::overflowing_sub_with_carry as oswc;
        assert_eq!(oswc(7, 5, true), (1, false));
        assert_eq!(oswc(255, 255, true), (255, true));
        assert_eq!(oswc(100, 106, false), (250, true));
    }
}
