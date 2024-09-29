// This file/namespace is not publicly exposed
#![allow(clippy::module_name_repetitions)]

use bitvec::prelude as bv;
use bv::BitArray;

use crate::Addr;

/// The state of the CPU registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CpuRegisters {
    pub a: u8,
    pub x: u8,
    pub y: u8,
    pub flags: CpuFlags,
    pub sp: u8,
    pub pc: Addr,
}

impl CpuRegisters {
    pub(crate) fn sp_as_address(self) -> Addr {
        Addr::from(u16::from(self.sp) + 0x01_00)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CpuFlags {
    /// This is actually just a `u8`, but the `bitvec` APIs are very convenient.
    /// (and by that I mean just being able to [] into a bitvector)
    inner: BitArray<u8, bv::Lsb0>,
}

impl CpuFlags {
    pub fn get_carry(self) -> bool { self.inner[0] }
    pub fn get_zero(self) -> bool { self.inner[1] }
    pub fn get_interrupt_disable(self) -> bool { self.inner[2] }
    pub fn get_overflow(self) -> bool { self.inner[6] }
    pub fn get_negative(self) -> bool { self.inner[7] }

    pub(crate) fn value_to_push(self, set_b: bool) -> u8 {
        let mut arr = self.inner;
        arr.set(4, set_b);
        arr.set(5, true);
        arr.into_inner()
    }

    /// Sets the negative and zero flags accordingly
    /// as if this value is being stored.
    pub(crate) fn set_nz(&mut self, value: u8) {
        self.inner.set(1, value == 0);
        let value = BitArray::<u8, bv::Lsb0>::new(value);
        self.inner.set(7, value[7]);
    }
}

/// The full state of the Picture Processing Unit.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PpuState {
    pub regs: PpuRegisters,
    internal_registers: PpuInternalRegisters,
}

/// The four internal registers of the PPU.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct PpuInternalRegisters {
    v: PpuVramAddress,
    t: PpuVramAddress,
    x: u8,
    /// The "write latch" or "write toggle".
    /// Is this the second write (true)?
    /// 
    /// Toggles on writes to `PPUSCROLL`/`PPUADDR`
    /// Clears on reads of `PPUSTATUS`.
    w: bool,
}

/// A struct containing a PPU VRAM address register.
/// 
/// (During rendering, used for scroll positions).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct PpuVramAddress {
    /// This is conceptually only 15 bits, but there's no `u15`.
    inner: BitArray<[u8; 2], bv::Lsb0>,
}

impl PpuVramAddress {
    fn inner_mut(&mut self) -> &mut bv::BitSlice<u8, bv::Lsb0> {
        &mut self.inner
    }
}

/// The registers of the Picture Processing Unit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PpuRegisters {
    pub ctrl: PpuCtrl,
    pub mask: PpuMask,
    pub status: PpuStatus,
    pub scroll: PpuScroll,
    // pub addr: PpuAddr,
    // pub data: PpuData,
    // pub oam_addr: u8,
    // pub oam_data: u8,
    // pub oam_dma: u8,
}

/// The flags to control PPU operation.
/// 
/// Access: RW.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PpuCtrl {
    // TODO Currently unmapped in this library:
    // bit 6
    // Note that setting bit 6 can damage a physical NES console
    inner: BitArray<u8, bv::Lsb0>,
}

impl PpuCtrl {
    pub fn write(&mut self, state: &mut PpuState, data: u8) {
        let data = BitArray::new(data);
        state.internal_registers.t.inner_mut()
            [10..12]
            .copy_from_bitslice(&data[0..2]);
        self.inner = data;
    }

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
    inner: BitArray<u8, bv::Lsb0>,
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

/// PPU status register, maybe for timing.
/// 
/// Access: R.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PpuStatus {
    // Bits 0-4 are actually unmapped
    // idk what 5 even does??
    inner: BitArray<u8, bv::Lsb0>,
}

impl PpuStatus {
    // This function is called whenever the register is read from.
    fn on_read(state: &mut PpuState) {
        state.internal_registers.w = false;
        state.regs.status.inner.set(7, false);
    }

    pub fn sprite0_hit(self, state: &mut PpuState) -> bool {
        Self::on_read(state);
        self.inner[6]
    }

    pub fn in_vblank(self, state: &mut PpuState) -> bool {
        Self::on_read(state);
        self.inner[7]
    }
}

/// The `PPUSCROLL` register, changing the scroll position.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PpuScroll {
    // This type actually only exists for the sake of the side effects of
    // writing to it, putting data into internal registers `t` and `x`.
    _empty: (),
}

impl PpuScroll {
    pub fn write(self, state: &mut PpuState, byte: u8) {
        let data = BitArray::new(byte);
        #[allow(clippy::bool_comparison)]
        if state.internal_registers.w == false {
            let (t_data, x_data) = data.split_at(3);
            bv::BitSlice::from_element_mut(&mut state.internal_registers.x)
                [0..3]
                .copy_from_bitslice(x_data);
            state.internal_registers.t.inner_mut()
                [0..5]
                .copy_from_bitslice(t_data);
            state.internal_registers.w = true;
        } else {
            let t_reg = state.internal_registers.t.inner_mut();
            t_reg[8..10].copy_from_bitslice(&data[6..8]);
            t_reg[5..8].copy_from_bitslice(&data[3..6]);
            t_reg[12..15].copy_from_bitslice(&data[0..3]);
            state.internal_registers.w = false;
        }
    }
}
