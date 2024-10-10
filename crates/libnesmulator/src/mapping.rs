//! A module for NES mappers.

use crate::Addr;
pub use nesfile::Mapper as RawMapper;

mod nrom;
pub use nrom::NromMapper;

/// A mapper (they're all hardcoded into `nesmulator`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Mapper {
    /// aka NROM
    M000(NromMapper),
}

impl Mapper {
    pub fn lookup_addr(&self, addr: Addr) -> Result<MapLookup, MapLookupError> {
        match self {
            Mapper::M000(nrom) => nrom.lookup_addr(addr),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MapLookup {
    /// Use this location in the PRG-ROM
    PrgRom(u16),
    /// Use this location in the CHR-ROM
    ChrRom(u16),
    /// Use this location in the PRG-RAM
    PrgRam(u16),
    /// Use this location in the CHR-RAM
    ChrRam(u16),
}

/// An error that can occur while looking up an address
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum MapLookupError {
    /// The given address is not mapped by this mapper.
    AddressNotMapped,
}
