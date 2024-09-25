// This file/namespace is not publicly exposed
#![allow(clippy::module_name_repetitions)]

use bitvec::prelude as bv;

use crate::Addr;

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

/// The registers of the Picture Processing Unit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PpuRegisters {
    pub ctrl: PpuCtrl,
    pub mask: PpuMask,
    pub status: PpuStatus,
    // pub scroll: PpuScroll,
    // pub addr: PpuAddr,
    // pub data: PpuData,
    pub oam_addr: u8,
    pub oam_data: u8,
    pub oam_dma: u8,
}

/// The flags to control PPU operation.
/// 
/// Access: RW.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PpuCtrl {
    // TODO Currently unmapped in this library:
    // bit 6
    // Note that setting bit 6 can damage a physical NES console
    inner: bv::BitArray<u8, bv::Lsb0>,
}

impl PpuCtrl {
    pub fn should_generate_nmi(self) -> bool { self.inner[7] }
    pub fn sprite_size(self) -> SpriteSize {
        SpriteSize::from_bool(self.inner[5])
    }

    pub fn background_pattern_table_address(self) -> Addr {
        match self.inner[4] {
            false => Addr::from(0x0000),
            true  => Addr::from(0x1000),
        }
    }

    pub fn sprite_pattern_table_address(self) -> Addr {
        match self.inner[3] {
            false => Addr::from(0x0000),
            true  => Addr::from(0x1000),
        }
    }

    pub fn base_nametable_address(self) -> Addr {
        match (self.inner[1], self.inner[0]) {
            (false, false) => Addr::from(0x2000),
            (false, true ) => Addr::from(0x2400),
            (true,  false) => Addr::from(0x2800),
            (true,  true ) => Addr::from(0x2C00),
        }
    }

    pub fn vram_increment(self) -> VramIncrement {
        match self.inner[2] {
            false => VramIncrement::GoingAcross,
            true  => VramIncrement::GoingDown,
        }
    }
}

/// The size of a sprite in [`PpuCtrl`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SpriteSize {
    Pixels8x8,
    Pixels8x16,
}

impl SpriteSize {
    fn from_bool(b: bool) -> SpriteSize {
        match b {
            false => SpriteSize::Pixels8x8,
            true => SpriteSize::Pixels8x16,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VramIncrement {
    GoingAcross,
    GoingDown,
}

impl VramIncrement {
    /// How much does the VRAM address increment by when the CPU touches PPUDATA?
    pub fn increment(self) -> u8 {
        match self {
            Self::GoingAcross => 1,
            Self::GoingDown => 32,
        }
    }
}

/// The `PPUMASK` register on the NES,
/// controlling sprite and background rendering.
/// 
/// Access: RW.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PpuMask {
    inner: bv::BitArray<u8, bv::Lsb0>,
}

impl PpuMask {
    pub fn is_grayscale(self) -> bool { self.inner[0] }
    pub fn show_background_leftmost(self) -> bool { self.inner[1] }
    pub fn show_sprites_leftmost(self) -> bool { self.inner[2] }
    pub fn show_background(self) -> bool { self.inner[3] }
    pub fn show_sprites(self) -> bool { self.inner[4] }
    pub fn emphasize_red_ntsc(self) -> bool { self.inner[5] }
    pub fn emphasize_red_pal(self) -> bool { self.inner[6] }
    pub fn emphasize_green_ntsc(self) -> bool { self.inner[6] }
    pub fn emphasize_green_pal(self) -> bool { self.inner[5] }
    pub fn emphasize_blue_ntsc(self) -> bool { self.inner[7] }
    pub fn emphasize_blue_pal(self) -> bool { self.inner[7] }
}

// TODO:
// Wiki says reads of this clear some address latch?
/// PPU status register, maybe for timing.
/// 
/// Access: R.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PpuStatus {
    // Bits 0-4 are actually unmapped
    // idk what 5 even does??
    inner: bv::BitArray<u8, bv::Lsb0>,
}

impl PpuStatus {
    pub fn sprite0_hit(self) -> bool { self.inner[6] }
    pub fn in_vblank(self) -> bool { self.inner[7] }
}
