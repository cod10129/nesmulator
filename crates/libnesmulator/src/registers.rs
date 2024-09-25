// This file/namespace is not publicly exposed
#![allow(clippy::module_name_repetitions)]

use bitvec::prelude as bv;

/// The state of the CPU registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CpuRegisters {
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
    inner: bv::BitArray<u8, bv::Lsb0>,
}

impl CpuFlags {
    pub fn get_carry(self) -> bool { self.inner[0] }
    pub fn get_zero(self) -> bool { self.inner[1] }
    pub fn get_interrupt_disable(self) -> bool { self.inner[2] }
    pub fn get_overflow(self) -> bool { self.inner[6] }
    pub fn get_negative(self) -> bool { self.inner[7] }
}
/*
/// The registers of the Picture Processing Unit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PpuRegisters {
    pub ctrl: PpuCtrl,
    pub mask: PpuMask,
    pub status: PpuStatus,
    pub scroll: PpuScroll,
    pub addr: PpuAddr,
    pub data: PpuData,
    pub oam_addr: u8,
    pub oam_data: u8,
    pub oam_dma: u8,
}

/// The flags to control PPU operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PpuCtrl {
    inner: bv::BitArray<u8, bv::Lsb0>,
}*/
