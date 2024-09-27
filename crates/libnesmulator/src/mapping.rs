//! A module for NES mappers.

use crate::Addr;
pub use nesfile::Mapper as RawMapper;

/// A mapper (they're all hardcoded into `nesmulator`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Mapper {
    M000,
}

impl Mapper {
    pub fn data(&self) -> MappingData {
        use Mapper::*;
        match self {
            M000 => MappingData { prg_rom_start: Addr::from(0x8000) },
        }
    }
}

/// Some data about a mapping (WIP).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[allow(clippy::module_name_repetitions)]
pub struct MappingData {
    prg_rom_start: Addr,
}
