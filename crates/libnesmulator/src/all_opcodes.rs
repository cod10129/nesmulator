use crate::{Instruction, AddressingMode, InstructionWithMode};

impl InstructionWithMode {
    /// Returns an `Err` if the opcode is invalid or unrecognized.
    #[allow(clippy::match_same_arms)]
    #[allow(clippy::too_many_lines)] // It's ONE MATCH.
    pub(crate) fn parse(n: u8) -> Result<Self, ()> {
        use Instruction::*;
        use AddressingMode::*;
        fn c(i: Instruction, am: AddressingMode) -> InstructionWithMode {
            InstructionWithMode {
                instruction_type: i, addressing_mode: am,
            }
        }

        const UNRECOGNIZED: Result<InstructionWithMode, ()> = Err(());

        Ok(match n {
            0x00 => c(Break, Implied),
            0x01 => c(OrMemory, IndexedIndirect),
            0x02 => return UNRECOGNIZED,
            0x03 => return UNRECOGNIZED,
            0x04 => return UNRECOGNIZED,
            0x05 => c(OrMemory, ZeroPage),
            0x06 => c(ArithmeticShiftLeft, ZeroPage),
            0x07 => return UNRECOGNIZED,
            0x08 => c(PushFlags, Implied),
            0x09 => c(OrMemory, Immediate),
            0x0A => c(ArithmeticShiftLeft, Accumulator),
            0x0B => return UNRECOGNIZED,
            0x0C => return UNRECOGNIZED,
            0x0D => c(OrMemory, Absolute),
            0x0E => c(ArithmeticShiftLeft, Absolute),
            0x0F => return UNRECOGNIZED,
            0x10 => c(BranchOnPlus, Relative),
            0x11 => c(OrMemory, IndirectIndexed),
            0x12 => return UNRECOGNIZED,
            0x13 => return UNRECOGNIZED,
            0x14 => return UNRECOGNIZED,
            0x15 => c(OrMemory, ZeroPageIndexedX),
            0x16 => c(ArithmeticShiftLeft, ZeroPageIndexedX),
            0x17 => return UNRECOGNIZED,
            0x18 => c(ClearCarryFlag, Implied),
            0x19 => c(OrMemory, AbsoluteIndexedY),
            0x1A => return UNRECOGNIZED,
            0x1B => return UNRECOGNIZED,
            0x1C => return UNRECOGNIZED,
            0x1D => c(OrMemory, AbsoluteIndexedX),
            0x1E => c(ArithmeticShiftLeft, AbsoluteIndexedX),
            0x1F => return UNRECOGNIZED,
            0x20 => c(JumpToSubroutine, Absolute),
            0x21 => c(AndMemory, IndexedIndirect),
            0x22 => return UNRECOGNIZED,
            0x23 => return UNRECOGNIZED,
            0x24 => c(TestBits, ZeroPage),
            0x25 => c(AndMemory, ZeroPage),
            0x26 => c(RotateLeft, ZeroPage),
            0x27 => return UNRECOGNIZED,
            0x28 => c(PullFlags, Implied),
            0x29 => c(AndMemory, Immediate),
            0x2A => c(RotateLeft, Accumulator),
            0x2B => return UNRECOGNIZED,
            0x2C => c(TestBits, Absolute),
            0x2D => c(AndMemory, Absolute),
            0x2E => c(RotateLeft, Absolute),
            0x2F => return UNRECOGNIZED,
            0x30 => c(BranchOnMinus, Relative),
            0x31 => c(AndMemory, IndirectIndexed),
            0x32 => return UNRECOGNIZED,
            0x33 => return UNRECOGNIZED,
            0x34 => return UNRECOGNIZED,
            0x35 => c(AndMemory, ZeroPageIndexedX),
            0x36 => c(RotateLeft, ZeroPageIndexedX),
            0x37 => return UNRECOGNIZED,
            0x38 => c(SetCarryFlag, Implied),
            0x39 => c(AndMemory, AbsoluteIndexedY),
            0x3A => return UNRECOGNIZED,
            0x3B => return UNRECOGNIZED,
            0x3C => return UNRECOGNIZED,
            0x3D => c(AndMemory, AbsoluteIndexedX),
            0x3E => c(RotateLeft, AbsoluteIndexedX),
            0x3F => return UNRECOGNIZED,
            0x40 => c(ReturnFromInterrupt, Implied),
            0x41 => c(ExclusiveOr, IndexedIndirect),
            0x42 => return UNRECOGNIZED,
            0x43 => return UNRECOGNIZED,
            0x44 => return UNRECOGNIZED,
            0x45 => c(ExclusiveOr, ZeroPage),
            0x46 => c(LogicalShiftRight, ZeroPage),
            0x47 => return UNRECOGNIZED,
            0x48 => c(PushAccumulator, Implied),
            0x49 => c(ExclusiveOr, Immediate),
            0x4A => c(LogicalShiftRight, Accumulator),
            0x4B => return UNRECOGNIZED,
            0x4C => c(Jump, Absolute),
            0x4D => c(ExclusiveOr, Absolute),
            0x4E => c(LogicalShiftRight, Absolute),
            0x4F => return UNRECOGNIZED,
            0x50 => c(BranchOnOverflowClear, Relative),
            0x51 => c(ExclusiveOr, IndirectIndexed),
            0x52 => return UNRECOGNIZED,
            0x53 => return UNRECOGNIZED,
            0x54 => return UNRECOGNIZED,
            0x55 => c(ExclusiveOr, ZeroPageIndexedX),
            0x56 => c(LogicalShiftRight, ZeroPageIndexedX),
            0x57 => return UNRECOGNIZED,
            0x58 => c(ClearInterruptDisable, Implied),
            0x59 => c(ExclusiveOr, AbsoluteIndexedY),
            0x5A => return UNRECOGNIZED,
            0x5B => return UNRECOGNIZED,
            0x5C => return UNRECOGNIZED,
            0x5D => c(ExclusiveOr, AbsoluteIndexedX),
            0x5E => c(LogicalShiftRight, AbsoluteIndexedX),
            0x5F => return UNRECOGNIZED,
            0x60 => c(ReturnFromSubroutine, Implied),
            0x61 => c(AddWithCarry, IndexedIndirect),
            0x62 => return UNRECOGNIZED,
            0x63 => return UNRECOGNIZED,
            0x64 => return UNRECOGNIZED,
            0x65 => c(AddWithCarry, ZeroPage),
            0x66 => c(RotateRight, ZeroPage),
            0x67 => return UNRECOGNIZED,
            0x68 => c(PullAccumulator, Implied),
            0x69 => c(AddWithCarry, Immediate),
            0x6A => c(RotateRight, Accumulator),
            0x6B => return UNRECOGNIZED,
            0x6C => c(Jump, Indirect),
            0x6D => c(AddWithCarry, Absolute),
            0x6E => c(RotateRight, Absolute),
            0x6F => return UNRECOGNIZED,
            0x70 => c(BranchOnOverflowSet, Relative),
            0x71 => c(AddWithCarry, IndirectIndexed),
            0x72 => return UNRECOGNIZED,
            0x73 => return UNRECOGNIZED,
            0x74 => return UNRECOGNIZED,
            0x75 => c(AddWithCarry, ZeroPageIndexedX),
            0x76 => c(RotateRight, ZeroPageIndexedX),
            0x77 => return UNRECOGNIZED,
            0x78 => c(SetInterruptDisable, Implied),
            0x79 => c(AddWithCarry, AbsoluteIndexedY),
            0x7A => return UNRECOGNIZED,
            0x7B => return UNRECOGNIZED,
            0x7C => return UNRECOGNIZED,
            0x7D => c(AddWithCarry, AbsoluteIndexedX),
            0x7E => c(RotateRight, AbsoluteIndexedX),
            0x7F => return UNRECOGNIZED,
            0x80 => return UNRECOGNIZED,
            0x81 => c(StoreAccumulator, IndexedIndirect),
            0x82 => return UNRECOGNIZED,
            0x83 => return UNRECOGNIZED,
            0x84 => c(StoreRegisterY, ZeroPage),
            0x85 => c(StoreAccumulator, ZeroPage),
            0x86 => c(StoreRegisterX, ZeroPage),
            0x87 => return UNRECOGNIZED,
            0x88 => c(DecrementRegisterY, Implied),
            0x89 => return UNRECOGNIZED,
            0x8A => c(TransferRegisterXToAcc, Implied),
            0x8B => return UNRECOGNIZED,
            0x8C => c(StoreRegisterY, Absolute),
            0x8D => c(StoreAccumulator, Absolute),
            0x8E => c(StoreRegisterX, Absolute),
            0x8F => return UNRECOGNIZED,
            0x90 => c(BranchOnCarryClear, Relative),
            0x91 => c(StoreAccumulator, IndirectIndexed),
            0x92 => return UNRECOGNIZED,
            0x93 => return UNRECOGNIZED,
            0x94 => c(StoreRegisterY, ZeroPageIndexedX),
            0x95 => c(StoreAccumulator, ZeroPageIndexedX),
            0x96 => c(StoreRegisterX, ZeroPageIndexedY),
            0x97 => return UNRECOGNIZED,
            0x98 => c(TransferRegisterYToAcc, Implied),
            0x99 => c(StoreAccumulator, AbsoluteIndexedY),
            0x9A => c(TransferRegisterXToStack, Implied),
            0x9B => return UNRECOGNIZED,
            0x9C => return UNRECOGNIZED,
            0x9D => c(StoreAccumulator, AbsoluteIndexedX),
            0x9E => return UNRECOGNIZED,
            0x9F => return UNRECOGNIZED,
            0xA0 => c(LoadRegisterY, Immediate),
            0xA1 => c(LoadAccumulator, IndexedIndirect),
            0xA2 => c(LoadRegisterX, Immediate),
            0xA3 => return UNRECOGNIZED,
            0xA4 => c(LoadRegisterY, ZeroPage),
            0xA5 => c(LoadAccumulator, ZeroPage),
            0xA6 => c(LoadRegisterX, ZeroPage),
            0xA7 => return UNRECOGNIZED,
            0xA8 => c(TransferAccToRegisterY, Implied),
            0xA9 => c(LoadAccumulator, Immediate),
            0xAA => c(TransferAccToRegisterX, Implied),
            0xAB => return UNRECOGNIZED,
            0xAC => c(LoadRegisterY, Absolute),
            0xAD => c(LoadAccumulator, Absolute),
            0xAE => c(LoadRegisterX, Absolute),
            0xAF => return UNRECOGNIZED,
            0xB0 => c(BranchOnCarrySet, Relative),
            0xB1 => c(LoadAccumulator, IndirectIndexed),
            0xB2 => return UNRECOGNIZED,
            0xB3 => return UNRECOGNIZED,
            0xB4 => c(LoadRegisterY, ZeroPageIndexedX),
            0xB5 => c(LoadAccumulator, ZeroPageIndexedX),
            0xB6 => c(LoadRegisterX, ZeroPageIndexedY),
            0xB7 => return UNRECOGNIZED,
            0xB8 => c(ClearOverflowFlag, Implied),
            0xB9 => c(LoadAccumulator, AbsoluteIndexedY),
            0xBA => c(TransferStackToRegisterX, Implied),
            0xBB => return UNRECOGNIZED,
            0xBC => c(LoadRegisterY, AbsoluteIndexedX),
            0xBD => c(LoadAccumulator, AbsoluteIndexedX),
            0xBE => c(LoadRegisterX, AbsoluteIndexedY),
            0xBF => return UNRECOGNIZED,
            0xC0 => c(CompareYRegister, Immediate),
            0xC1 => c(CompareAccumulator, IndexedIndirect),
            0xC2 => return UNRECOGNIZED,
            0xC3 => return UNRECOGNIZED,
            0xC4 => c(CompareYRegister, ZeroPage),
            0xC5 => c(CompareAccumulator, ZeroPage),
            0xC6 => c(DecrementMemory, ZeroPage),
            0xC7 => return UNRECOGNIZED,
            0xC8 => c(IncrementRegisterY, Implied),
            0xC9 => c(CompareAccumulator, Immediate),
            0xCA => c(DecrementRegisterX, Implied),
            0xCB => return UNRECOGNIZED,
            0xCC => c(CompareYRegister, Absolute),
            0xCD => c(CompareAccumulator, Absolute),
            0xCE => c(DecrementMemory, Absolute),
            0xCF => return UNRECOGNIZED,
            0xD0 => c(BranchOnNotEqual, Relative),
            0xD1 => c(CompareAccumulator, IndirectIndexed),
            0xD2 => return UNRECOGNIZED,
            0xD3 => return UNRECOGNIZED,
            0xD4 => return UNRECOGNIZED,
            0xD5 => c(CompareAccumulator, ZeroPageIndexedX),
            0xD6 => c(DecrementMemory, ZeroPageIndexedX),
            0xD7 => return UNRECOGNIZED,
            0xD8 => return UNRECOGNIZED, // Clear decimal mode
            0xD9 => c(CompareAccumulator, AbsoluteIndexedY),
            0xDA => return UNRECOGNIZED,
            0xDB => return UNRECOGNIZED,
            0xDC => return UNRECOGNIZED,
            0xDD => c(CompareAccumulator, AbsoluteIndexedX),
            0xDE => c(DecrementMemory, AbsoluteIndexedX),
            0xDF => return UNRECOGNIZED,
            0xE0 => c(CompareXRegister, Immediate),
            0xE1 => c(SubtractWithCarry, IndexedIndirect),
            0xE2 => return UNRECOGNIZED,
            0xE3 => return UNRECOGNIZED,
            0xE4 => c(CompareXRegister, ZeroPage),
            0xE5 => c(SubtractWithCarry, ZeroPage),
            0xE6 => c(IncrementMemory, ZeroPage),
            0xE7 => return UNRECOGNIZED,
            0xE8 => c(IncrementRegisterX, Implied),
            0xE9 => c(SubtractWithCarry, Immediate),
            0xEA => c(NoOp, Implied),
            0xEB => return UNRECOGNIZED,
            0xEC => c(CompareXRegister, Absolute),
            0xED => c(SubtractWithCarry, Absolute),
            0xEE => c(IncrementMemory, Absolute),
            0xEF => return UNRECOGNIZED,
            0xF0 => c(BranchOnEqual, Relative),
            0xF1 => c(SubtractWithCarry, IndirectIndexed),
            0xF2 => return UNRECOGNIZED,
            0xF3 => return UNRECOGNIZED,
            0xF4 => return UNRECOGNIZED,
            0xF5 => c(SubtractWithCarry, ZeroPageIndexedX),
            0xF6 => c(IncrementMemory, ZeroPageIndexedX),
            0xF7 => return UNRECOGNIZED,
            0xF8 => return UNRECOGNIZED, // Set decimal mode
            0xF9 => c(SubtractWithCarry, AbsoluteIndexedY),
            0xFA => return UNRECOGNIZED,
            0xFB => return UNRECOGNIZED,
            0xFC => return UNRECOGNIZED,
            0xFD => c(SubtractWithCarry, AbsoluteIndexedX),
            0xFE => c(IncrementMemory, AbsoluteIndexedX),
            0xFF => return UNRECOGNIZED,
        })
    }
}

#[cfg(test)]
#[test]
fn no_duplicates() {
    use std::collections::HashSet;
    let mut uniq = HashSet::new();
    let has_unique_elements = (0..=u8::MAX)
        .filter_map(|n| InstructionWithMode::parse(n).ok())
        .all(|inst| {
            let res = uniq.insert(inst);
            if !res {
                eprintln!("Element {inst:#?} already present in set");
            }
            res
        });
    assert!(has_unique_elements);
}
