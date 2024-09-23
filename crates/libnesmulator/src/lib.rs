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
