/// ROM geometry selected by a circuit or by the guest's execution environment.
/// Only the supported geometries below can be constructed outside this module.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RomGeometry {
    byte_size_log2: u8,
}

impl RomGeometry {
    pub const fn byte_size(self) -> usize {
        1 << self.byte_size_log2
    }

    pub const fn word_size(self) -> usize {
        self.byte_size() / core::mem::size_of::<u32>()
    }

    pub const fn second_word_bits(self) -> usize {
        self.byte_size_log2 as usize - 16
    }
}

pub const REGULAR_ROM: RomGeometry = RomGeometry { byte_size_log2: 22 };
pub const L1_WRAP_ROM: RomGeometry = RomGeometry { byte_size_log2: 19 };

// Existing circuits retain their 4 MiB ROM regardless of the enclosing guest's layout.
pub const ROM_BYTE_SIZE_LOG2: usize = REGULAR_ROM.byte_size_log2 as usize;
pub const ROM_BYTE_SIZE: usize = REGULAR_ROM.byte_size();
pub const ROM_SECOND_WORD_BITS: usize = REGULAR_ROM.second_word_bits();
pub const ROM_WORD_SIZE: usize = REGULAR_ROM.word_size();
