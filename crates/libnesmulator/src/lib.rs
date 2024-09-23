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
    // Begin Indexed Operations, which add the X and Y registers to addresses
    /// The target address is determined by an absolute operand (`u16`)
    /// and a register (X or Y).
    /// The target is the sum of the absolute operand and register value.
    AbsoluteIndexed,
    /// This is like absolute indexing, but with one `u8` that's an address in the zero page.
    /// **THE TARGET ADDRESS WRAPS THE ZERO PAGE.**
    /// If you have an operand of `$C0` and an X of `$60`, that wraps to the address
    /// `$C0+$60 && $FF` or `$20`.
    ZeroPageIndexed,
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
            Immediate | Relative | ZeroPage | ZeroPageIndexed
                | IndexedIndirect | IndirectIndexed => 1,
            Absolute | Indirect | AbsoluteIndexed => 2,
        }
    }
}
