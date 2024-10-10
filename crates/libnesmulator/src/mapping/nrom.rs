use crate::Addr;
use super::{MapLookup, MapLookupError};

#[allow(clippy::module_name_repetitions)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NromMapper {
    /// Do we mirror $8000-BFFF at $C000-FFFF, or use $C000-FFFF to map the other
    /// 16 KB of PRG-ROM?
    mirror_prg_rom: bool,
}

impl NromMapper {
    pub fn lookup_addr(self, addr: Addr) -> Result<MapLookup, MapLookupError> {
        // $6000-7FFF is PRG-RAM (Family Basic only)
        // (Pretend it's all mapped to existing PRG-RAM)
        // $8000-BFFF First 16 KiB of ROM
        // $C000-FFFF Second 16 KiB of ROM or mirror of first 16 KiB
        let addr = addr.into_num();
        Ok(match addr {
            0x0000..=0x5FFF => return Err(MapLookupError::AddressNotMapped),
            0x6000..=0x7FFF => MapLookup::PrgRam(addr - 0x6000),
            0x8000..=0xBFFF => MapLookup::PrgRom(addr - 0x8000),
            0xC000..=0xFFFF => {
                let offset = match self.mirror_prg_rom {
                    false => 0x8000,
                    true => 0xC000,
                };
                MapLookup::PrgRom(addr - offset)
            },
        })
    }
}
