//! A crate for analyzing and parsing `.nes` files in the NES 2.0 format.
//! 
//! <https://www.nesdev.org/wiki/NES_2.0>

use nom::bits::{self, complete::bool as parse_bool};
use nom::bytes::complete::tag;
use nom::combinator::map;
use nom::error::context;
use nom::error::VerboseError;
use nom::number::complete::u8;
use nom::sequence::tuple;

type Input<'a> = &'a [u8];
type BitInput<'a> = (Input<'a>, usize);
type NomError<'a> = VerboseError<Input<'a>>;
type BitsError<'a> = VerboseError<BitInput<'a>>;
type BitParseResult<'a, O> = nom::IResult<BitInput<'a>, O, BitsError<'a>>;
type ParseResult<'a, O> = nom::IResult<Input<'a>, O, NomError<'a>>;

fn take_bits_u8<'a>(count: usize) -> impl Fn(BitInput<'a>) -> BitParseResult<'a, u8> {
    nom::bits::complete::take(count)
}

fn take_bits_u16<'a>(count: usize) -> impl Fn(BitInput<'a>) -> BitParseResult<'a, u16> {
    nom::bits::complete::take(count)
}

/// The NES 2.0 file header.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Header {
    pub is_nes_2: Nes2OrInes,
    /// Not to be confused with `prg_ram_size`.
    pub prg_rom_size: u32,
    /// Not to be confused with `chr_ram_size`.
    pub chr_rom_size: u32,
    pub nametable_layout: NametableLayout,
    pub nametable_is_alternate: bool,
    pub non_volatile_memory_present: bool,
    pub trainer_is_present: bool,
    pub mapper: Mapper,
    pub console_type: ConsoleType,
    /// Not to be confused with `prg_rom_size`.
    /// Fits in `u21`.
    pub prg_ram_size: u32,
    pub prg_nvram_size: u32,
    /// Not to be confused with `chr_rom_size`.
    pub chr_ram_size: u32,
    pub chr_nvram_size: u32,
    pub timing_mode: TimingMode,
    /// 0-3
    pub misc_roms_count: u8,
    /// 0x0-3D
    pub default_expansion_device: u8,
}

impl Header {
    #[allow(clippy::missing_panics_doc)]
    #[allow(clippy::similar_names)]
    #[allow(clippy::too_many_lines)] // This lint exists??
    pub fn parse(i: Input<'_>) -> ParseResult<'_, Header> {
        // All bit parsers need to be kind of reversed
        let (i, (
            _magic,
            prg_rom_size_lsb, chr_rom_size_lsb,
            (
                mapper_number_3_0,
                nametable_is_alternate,
                trainer_is_present,
                non_volatile_memory_present,
                nametable_layout,
            ),
            (
                mapper_number_7_4,
                is_nes_2,
                // This is not ConsoleType because we need byte 13
                // to build all the data for the type.
                console_type,
            ),
            (submapper_number, mapper_number_11_8),
            (prg_rom_size_msb, chr_rom_size_msb),
            (prg_nvram_shift_count, prg_ram_shift_count),
            (chr_nvram_shift_count, chr_ram_shift_count),
            (_, timing_mode),
            (console_type_info_upper, console_type_info_lower),
            (_, misc_roms_count),
            (_, default_expansion_device),
        )) = tuple((
            context("NES<EOF> magic", tag(b"NES\x1A")),
            context("PRG-ROM size LSB", u8),
            context("CHR-ROM size LSB", u8),
            context("Flags 6", bits::bits(tuple::<_, _, BitsError<'_>, _>((
                context("Mapper Num 3..0", take_bits_u16(4)),
                context("Alternate nametable", parse_bool),
                context("Trainer present", parse_bool),
                context("Non-volatile Memory", parse_bool),
                #[allow(clippy::match_bool)]
                context("Wired Nametable Layout", map(parse_bool, |b| match b {
                    false => NametableLayout::MirroredHorizontally,
                    true  => NametableLayout::MirroredVertically,
                })),
            )))),
            context("Flags 7", bits::bits(tuple::<_, _, BitsError<'_>, _>((
                context("Mapper Num 7..4", take_bits_u16(4)),
                context("NES 2.0 Identifier", map(take_bits_u8(2), {
                    |bits| match bits {
                        0b10 => Nes2OrInes::Nes2,
                        0b00 | 0b01 | 0b11 => Nes2OrInes::Ines,
                        0b100..=u8::MAX => unreachable!(),
                    }
                })),
                context("Console Type", take_bits_u8(2)),
            )))),
            context("Rest of Mapper", bits::bits(tuple::<_, _, BitsError<'_>, _>((
                context("Submapper Num", take_bits_u8(4)),
                context("Mapper Num 11..8", take_bits_u16(4)),
            )))),
            context("ROM size MSB", bits::bits(tuple::<_, _, BitsError<'_>, _>((
                context("CHR-ROM size MSB", take_bits_u8(4)),
                context("PRG-ROM size MSB", take_bits_u8(4)),
            )))),
            context("PRG-RAM size", bits::bits(tuple::<_, _, BitsError<'_>, _>((
                context("PRG-NVRAM shift count", take_bits_u8(4)),
                context("PRG-RAM shift count", take_bits_u8(4)),
            )))),
            context("CHR-RAM size", bits::bits(tuple::<_, _, BitsError<'_>, _>((
                context("CHR-NVRAM shift count", take_bits_u8(4)),
                context("CHR-RAM shift count", take_bits_u8(4)),
            )))),
            context("CPU/PPU timing", bits::bits(tuple::<_, _, BitsError<'_>, _>((
                context("Reserved, ignored", take_bits_u8(6)),
                context("Timing Mode", map(take_bits_u8(2), |mode| match mode {
                    0 => TimingMode::RP2C02,
                    1 => TimingMode::RP2C07,
                    2 => TimingMode::MultipleRegion,
                    3 => TimingMode::UA6538,
                    4..=u8::MAX => unreachable!(),
                })),
            )))),
            context("Console Type Information", bits::bits(tuple::<_, _, BitsError<'_>, _>((
                context("Upper bits", take_bits_u8(4)),
                context("Lower bits", take_bits_u8(4)),
            )))),
            context("Misc. ROMs", bits::bits(tuple::<_, _, BitsError<'_>, _>((
                context("Reserved, ignored", take_bits_u8(6)),
                context("Misc. ROMs Count", take_bits_u8(2)),
            )))),
            context("D.E.D", bits::bits(tuple::<_, _, BitsError<'_>, _>((
                context("Reserved, ignored", take_bits_u8(2)),
                context("Default Expansion Device", take_bits_u8(6)),
            )))),
        ))(i)?;
        let console_type = match console_type {
            0 => ConsoleType::NintendoEntertainmentSystem,
            1 => ConsoleType::NintendoVsSystem(VsSystemType {
                ppu_type: VsPpuType::from_bits(console_type_info_lower),
                hardware_type: console_type_info_upper,
            }),
            2 => ConsoleType::NintendoPlaychoice10,
            3 => ConsoleType::ExtendedConsoleType(
                console_type_info_lower,
            ),
            4..=u8::MAX => unreachable!(),
        };
        let mapper = Mapper {
            mapper_number: (
                (mapper_number_11_8 << 8) | (mapper_number_7_4 << 4) | mapper_number_3_0
            ),
            submapper_number,
        };
        let shift_ct_to_ram_size = |shift_count: u8| -> u32 {
            if shift_count == 0 { 0 }
            else { 64 << shift_count }
        };
        let rom_size_combiner = |msb: u8, lsb: u8| -> u32 {
            assert!(msb < 0x10);
            let (msb, lsb): (u32, u32) = (msb.into(), lsb.into());
            if msb == 0xF {
                let (exponent, multiplier) = (msb & 0b1111_1100, msb & 0b11);
                2u32.pow(exponent) * ((multiplier * 2) + 1)
            } else {
                (msb << 8) | lsb
            }
        };
        Ok((i, Header {
            prg_rom_size: rom_size_combiner(prg_rom_size_msb, prg_rom_size_lsb),
            chr_rom_size: rom_size_combiner(chr_rom_size_msb, chr_rom_size_lsb),
            prg_ram_size:   shift_ct_to_ram_size(prg_ram_shift_count),
            prg_nvram_size: shift_ct_to_ram_size(prg_nvram_shift_count),
            chr_ram_size:   shift_ct_to_ram_size(chr_ram_shift_count),
            chr_nvram_size: shift_ct_to_ram_size(chr_nvram_shift_count),
            is_nes_2, nametable_layout, nametable_is_alternate,
            non_volatile_memory_present, trainer_is_present, mapper, console_type,
            timing_mode, misc_roms_count, default_expansion_device,
        }))
    }
}

/// Is this an NES 2.0 ROM or a compatible iNES rom?
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Nes2OrInes {
    Nes2,
    Ines,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NametableLayout {
    MirroredHorizontally = 0,
    MirroredVertically   = 1,
}

/// A mapper and submapper number.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Mapper {
    /// This fits in a `u12`.
    pub mapper_number: u16,
    /// This fits in a `u4`.
    pub submapper_number: u8,
}

/// The type of console
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ConsoleType {
    NintendoEntertainmentSystem = 0,
    NintendoVsSystem(VsSystemType) = 1,
    NintendoPlaychoice10 = 2,
    ExtendedConsoleType(u8) = 3,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VsSystemType {
    pub ppu_type: VsPpuType,
    /// Actually just 0-6
    pub hardware_type: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VsPpuType {
    RP2C03B     = 0x0,
    RP2C03G     = 0x1,
    RP2C04_0001 = 0x2,
    RP2C04_0002 = 0x3,
    RP2C04_0003 = 0x4,
    RP2C04_0004 = 0x5,
    RC2C03B     = 0x6,
    RC2C03C     = 0x7,
    RC2C05_01   = 0x8,
    RC2C05_02   = 0x9,
    RC2C05_03   = 0xA,
    RC2C05_04   = 0xB,
    RC2C05_05   = 0xC,
    Reserved,
}

impl VsPpuType {
    #[allow(clippy::match_same_arms, clippy::manual_range_patterns)]
    fn from_bits(bits: u8) -> Self {
        match bits {
            0x0 => Self::RC2C03B,
            0x1 => Self::RP2C03G,
            0x2 => Self::RP2C04_0001,
            0x3 => Self::RP2C04_0002,
            0x4 => Self::RP2C04_0003,
            0x5 => Self::RP2C04_0004,
            0x6 => Self::RC2C03B,
            0x7 => Self::RC2C03C,
            0x8 => Self::RC2C05_01,
            0x9 => Self::RC2C05_02,
            0xA => Self::RC2C05_03,
            0xB => Self::RC2C05_04,
            0xC => Self::RC2C05_05,
            0xD | 0xE | 0xF => Self::Reserved,
            16..=u8::MAX => unreachable!(),
        }
    }
}

/// The timing mode of the CPU/PPU.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TimingMode {
    /// "NTSC NES"
    RP2C02,
    /// "Licensed PAL NES"
    RP2C07,
    MultipleRegion,
    /// "Dendy"
    UA6538,
}
