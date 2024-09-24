//! The NES emulator library.
//! It's a fully functional emulator, with UI provided by the binary crates.

use bitvec::prelude as bv;

/// The state of the CPU registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RegisterState {
    pub a: u8,
    pub x: u8,
    pub y: u8,
    pub flags: CpuFlags,
    pub sp: u8,
    pub pc: u16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CpuFlags {
    /// This is actually just a `u8`, but the `bitvec` APIs are very convenient.
    /// (and by that I mean just being able to [] into a bitvector)
    inner: bv::BitArray<[u8; 1], bv::Lsb0>,
}

impl CpuFlags {
    fn get_carry(self) -> bool { self.inner[0] }
    fn get_zero(self) -> bool { self.inner[1] }
    fn get_interrupt_disable(self) -> bool { self.inner[2] }
    fn get_overflow(self) -> bool { self.inner[6] }
    fn get_negative(self) -> bool { self.inner[7] }
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
