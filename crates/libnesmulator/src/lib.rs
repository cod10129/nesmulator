//! The NES emulator library.
//! It's a fully functional emulator, with UI provided by the binary crates.

use std::fmt;

type ParseResult<'a, O> = nom::IResult<&'a [u8], O, nom::error::VerboseError<&'a [u8]>>;

mod registers;
pub use registers::{
    CpuRegisters, CpuFlags,
    PpuState,
    PpuRegisters,
        PpuCtrl, SpriteSize, VramIncrement,
        PpuMask,
        PpuStatus,
        PpuScroll,
};

pub mod mapping;

/// An address on the NES 6502.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Addr {
    inner: u16,
}

impl Addr {
    pub const NULL: Self = Self { inner: 0 };
    pub fn from_num(n: u16) -> Self { n.into() }
    pub fn into_num(self) -> u16 { self.inner }
}

impl From<u16> for Addr {
    fn from(addr: u16) -> Self {
        Self { inner: addr }
    }
}

impl From<Addr> for u16 {
    fn from(addr: Addr) -> Self {
        addr.inner
    }
}

impl fmt::Debug for Addr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "${:04X}", self.inner)
    }
}

/// An addressing mode on the 6502 chip.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AddressingMode {
    /// The target is the accumulator (register A).
    Accumulator,
    /// The instruction data is one byte directly after the opcode.
    Immediate,
    /// The target(s) of the instruction are implied by what instruction it is.
    Implied,
    /// This addressing mode is only used for the branch instructions.
    /// If the branch is taken, the program counter is incremented by the operand,
    /// which is an `i8` placed directly after the opcode.
    Relative,
    /// The memory location is specified explicitly, a **little-endian** u16 after
    /// the opcode.
    Absolute,
    /// Zero-Page addressing is absolute addressing, but with an implied 0x00.
    /// e.g. `LDA $35` will put $0035 into register A.
    ZeroPage,
    /// This addressing mode is only used by the `JMP` instruction.
    /// The opcode is followed by a `u16` address. This pointer is followed,
    /// and the PC is set to whatever address is read from that pointer.
    Indirect,
    /// The target address is the sum of the absolute operand `u16` and value of X.
    AbsoluteIndexedX,
    /// The target address is the sum of the absolute operand `u16` and value of Y.
    AbsoluteIndexedY,
    /// Like `AbsoluteIndexedX`, but with a `u8` that's an address in the zero page.
    /// **THE ADDRESS CALCULATION WRAPS THE ZERO PAGE.**
    ZeroPageIndexedX,
    /// Like `AbsoluteIndexedY`, but with a `u8` that's an address in the zero page.
    /// **THE ADDRESS CALCULATION WRAPS THE ZERO PAGE.**
    ZeroPageIndexedY,
    /// Not to be confused with `IndirectIndexed`.
    /// 
    /// This mode is only used with the X register. The operand is a zero page `u8` index.
    /// This value is (wrapping the 0 page) added with the value in X,
    /// and that pointer is dereferenced (reading a `u16` address) to get the target.
    IndexedIndirect,
    /// Not to be confused with `IndexedIndirect`.
    /// 
    /// This mode is only used with the Y register. The operand is a zero page `u8` index.
    /// The address stored at the zero page location is fetched, and Y is added
    /// to *that* address to get the final target.
    IndirectIndexed,
}

impl AddressingMode {
    /// The size of the operand, either 0, 1, or 2.
    pub fn operand_size(self) -> u8 {
        use AddressingMode::*;
        match self {
            Implied | Accumulator => 0,
            Immediate | Relative | ZeroPage
                | ZeroPageIndexedX | ZeroPageIndexedY
                | IndexedIndirect | IndirectIndexed => 1,
            Absolute | Indirect | AbsoluteIndexedX | AbsoluteIndexedY => 2,
        }
    }
}

/// One of the ~46~ 44 instructions on the 6502.
/// As this is the NES, the clear and set decimal mode instructions are disabled,
/// as decimal mode does not exist on the NES.
/// 
/// <https://www.pagetable.com/c64ref/6502/?tab=2>
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Instruction {
    /// `ADC`. Flags: `NViZC`.
    AddWithCarry,
    /// `AND`. Flags: `NviZc`.
    AndMemory,
    /// `ASL`. Flags: `NviZC`.
    ArithmeticShiftLeft,
    /// `BIT`. Flags: `NViZc`.
    TestBits,
    /// `BPL`. Flags: `nvizc`.
    BranchOnPlus,
    /// `BMI`. Flags: `nvizc`.
    BranchOnMinus,
    /// `BVC`. Flags: `nvizc`.
    BranchOnOverflowClear,
    /// `BVS`. Flags: `nvizc`.
    BranchOnOverflowSet,
    /// `BCC`. Flags: `nvizc`.
    BranchOnCarryClear,
    /// `BCS`. Flags: `nvizc`.
    BranchOnCarrySet,
    /// `BNE`. Flags: `nvizc`.
    BranchOnNotEqual,
    /// `BEQ`. Flags: `nvizc`.
    BranchOnEqual,
    /// `BRK`. Flags: `nvizcB`.
    Break,
    /// `CLC`. Flags: `nvizC`.
    ClearCarryFlag,
    /// `CLI`. Flags: `nvIzc`.
    ClearInterruptDisable,
    /// `CLV`. Flags: `nVizc`.
    ClearOverflowFlag,
    /// `CMP`. Flags: `NviZC`.
    CompareAccumulator,
    /// `CPX`. Flags: `NviZC`.
    CompareXRegister,
    /// `CPY`. Flags: `NviZC`.
    CompareYRegister,
    /// `DEC`. Flags: `NviZc`.
    DecrementMemory,
    /// `DEX`. Flags: `NviZc`.
    DecrementRegisterX,
    /// `DEY`. Flags: `NviZc`.
    DecrementRegisterY,
    /// `EOR`. Flags: `NviZc`.
    ExclusiveOr,
    /// `INC`. Flags: `NviZc`.
    IncrementMemory,
    /// `INX`. Flags: `NviZc`.
    IncrementRegisterX,
    /// `INY`. Flags: `NviZc`.
    IncrementRegisterY,
    /// `JMP`. Flags: `nvizc`.
    Jump,
    /// `JSR`. Flags: `nvizc`.
    JumpToSubroutine,
    /// `LDA`. Flags: `NviZc`.
    LoadAccumulator,
    /// `LDX`. Flags: `NviZc`.
    LoadRegisterX,
    /// `LDY`. Flags: `NviZc`.
    LoadRegisterY,
    /// `LSR`. Flags: `NviZC`.
    LogicalShiftRight,
    /// `NOP`. Flags: `nvizc`.
    NoOp,
    /// `ORA`. Flags: `NviZc`.
    OrMemory,
    /// `PHA`. Flags: `nvizc`.
    PushAccumulator,
    /// `PHP`. Flags: `nvizc`.
    PushFlags,
    /// `PLA`. Flags: `NviZc`.
    PullAccumulator,
    /// `PLP`. Flags: `NVIZCD`.
    PullFlags,
    /// `ROL`. Flags: `NviZC`.
    RotateLeft,
    /// `ROR`. Flags: `NviZC`.
    RotateRight,
    /// `RTI`. Flags: `NVIZCD`.
    ReturnFromInterrupt,
    /// `RTS`. Flags: `nvizc`.
    ReturnFromSubroutine,
    /// `SBC`. Flags: `NViZC`.
    SubtractWithCarry,
    /// `SEC`. Flags: `nvizC`.
    SetCarryFlag,
    /// `SEI`. Flags: `nvIzc`.
    SetInterruptDisable,
    /// `STA`. Flags: `nvizc`.
    StoreAccumulator,
    /// `STX`. Flags: `nvizc`.
    StoreRegisterX,
    /// `STY`. Flags: `nvizc`.
    StoreRegisterY,
    /// `TAX`. Flags: `NviZc`.
    TransferAccToRegisterX,
    /// `TAY`. Flags: `NviZc`.
    TransferAccToRegisterY,
    /// `TSX`. Flags: `NviZc`.
    TransferStackToRegisterX,
    /// `TXS`. Flags: `nvizc`.
    TransferRegisterXToStack,
    /// `TXA`. Flags: `NviZc`.
    TransferRegisterXToAcc,
    /// `TYA`. Flags: `NviZc`.
    TransferRegisterYToAcc,
}

/// An instruction with its addressing mode.
/// Each combination in this struct has its own opcode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InstructionWithMode {
    pub instruction_type: Instruction,
    pub addressing_mode: AddressingMode,
}

// Declare this to pull in one `impl InstructionWithMode`.
mod all_opcodes;

/// A full instruction with a type, addressing mode, and operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FullInstruction {
    pub instruction: InstructionWithMode,
    pub operand: Operand,
}

impl FullInstruction {
    /// Parses the `FullInstruction` from byte data.
    /// 
    /// ```
    /// use libnesmulator::{
    ///     FullInstruction, InstructionWithMode, Instruction,
    ///     AddressingMode, Operand
    /// };
    /// let (i, instruction) = FullInstruction::parse(b"\xC9\x42").unwrap();
    /// assert_eq!(instruction, FullInstruction {
    ///     instruction: InstructionWithMode {
    ///         instruction_type: Instruction::CompareAccumulator,
    ///         addressing_mode: AddressingMode::Immediate,
    ///     },
    ///     operand: Operand::OneByte(0x42),
    /// });
    /// ```
    pub fn parse(i: &[u8]) -> ParseResult<'_, FullInstruction> {
        use nom::{
            combinator::{map, map_res},
            error::context,
            number::complete::u8,
        };
        let (i, inst_with_mode) = context(
            "InstructionWithMode",
            map_res(u8, InstructionWithMode::parse),
        )(i)?;
        let operand_size = inst_with_mode.addressing_mode.operand_size();
        let (i, operand) = match operand_size {
            0 => (i, Operand::None),
            1 => context("Operand", map(u8, Operand::OneByte))(i)?,
            2 => context("Operand", map(
                nom::number::complete::le_u16,
                Operand::TwoBytes,
            ))(i)?,
            3..=u8::MAX => unreachable!(),
        };
        Ok((i, FullInstruction {
            instruction: inst_with_mode,
            operand
        }))
    }
}

/// An operand to an instruction, either 0, 1, or 2 bytes.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operand {
    None,
    OneByte(u8),
    TwoBytes(u16),
}

impl fmt::Debug for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::None => write!(f, "None"),
            Operand::OneByte(b) => write!(f, "${b:02X}"),
            Operand::TwoBytes(b) => write!(f, "${b:04X}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn operand_debug() {
        fn format(operand: Operand) -> String {
            format!("{operand:?}")
        }
        assert_eq!(format(Operand::None), "None");
        assert_eq!(format(Operand::OneByte(33)), "$21");
        assert_eq!(format(Operand::TwoBytes(0x0B_8A)), "$0B8A");
    }

    #[test]
    fn full_instruction_parse() {
        let (i, inst) = FullInstruction::parse(b"\xEA").unwrap();
        assert!(i.is_empty());
        assert_eq!(inst, FullInstruction {
            instruction: InstructionWithMode {
                addressing_mode: AddressingMode::Implied,
                instruction_type: Instruction::NoOp,
            },
            operand: Operand::None,
        });

        let (i, inst) = FullInstruction::parse(b"\x4C\xEF\xBE").unwrap();
        assert!(i.is_empty());
        assert_eq!(inst, FullInstruction {
            instruction: InstructionWithMode {
                instruction_type: Instruction::Jump,
                addressing_mode: AddressingMode::Absolute,
            },
            operand: Operand::TwoBytes(0xBEEF),
        });
    }
}
