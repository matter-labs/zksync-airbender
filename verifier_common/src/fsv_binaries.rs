//! Exact registry of full-statement verifier guests under
//! `tools/gkr_verifier/full_statement_verifiers/`.

use crate::prover::common_constants::{RomGeometry, L1_WRAP_ROM, REGULAR_ROM};
use crate::prover::definitions::USE_REDUCED_BLAKE2_ROUNDS;

pub use crate::prover::definitions::{BlakeMode, SecurityLevel, SoundnessMode};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FsvProgram {
    UnrolledBaseLayer,
    UnrolledRecursionLayer,
    UnifiedBaseLayer,
    UnifiedRecursionLayer,
}

impl FsvProgram {
    #[must_use]
    pub const fn reduced_rounds(self) -> bool {
        USE_REDUCED_BLAKE2_ROUNDS
    }
}

/// The statement a guest verifies within its layer.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FsvProfile {
    /// The recursion pipeline's statement.
    Standard,
    /// Unified recursion verifying the merged-mode compression schedule.
    Compression,
    CompressionFinalWrap,
}

impl FsvProfile {
    #[must_use]
    pub const fn rom(self) -> RomGeometry {
        match self {
            Self::CompressionFinalWrap => L1_WRAP_ROM,
            Self::Standard | Self::Compression => REGULAR_ROM,
        }
    }
}

/// Exact identity of a full-statement verifier guest.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct FsvDescriptor {
    pub soundness_mode: SoundnessMode,
    pub program: FsvProgram,
    pub profile: FsvProfile,
    pub blake: BlakeMode,
}

impl FsvDescriptor {
    /// A standard-profile descriptor.
    #[must_use]
    pub const fn new(soundness_mode: SoundnessMode, program: FsvProgram, blake: BlakeMode) -> Self {
        Self {
            soundness_mode,
            program,
            profile: FsvProfile::Standard,
            blake,
        }
    }

    #[must_use]
    pub const fn compression(profile: FsvProfile) -> Self {
        Self {
            soundness_mode: SoundnessMode::PessimisticConjecture,
            program: FsvProgram::UnifiedRecursionLayer,
            profile,
            blake: BlakeMode::BlakeSpecialOpcodes,
        }
    }

    /// Path relative to the FSV root. Panics if this descriptor has no built guest.
    #[must_use]
    pub fn relative_path(&self) -> &'static str {
        FSV_REGISTRY
            .iter()
            .find(|entry| entry.descriptor == *self)
            .unwrap_or_else(|| panic!("no full-statement verifier is built for {self:?}"))
            .relative_path
    }
}

/// A built guest: its descriptor and its path relative to the FSV root.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FsvRegistryEntry {
    pub descriptor: FsvDescriptor,
    pub relative_path: &'static str,
}

const fn entry(
    soundness_mode: SoundnessMode,
    program: FsvProgram,
    profile: FsvProfile,
    blake: BlakeMode,
    relative_path: &'static str,
) -> FsvRegistryEntry {
    FsvRegistryEntry {
        descriptor: FsvDescriptor {
            soundness_mode,
            program,
            profile,
            blake,
        },
        relative_path,
    }
}

/// Every built guest, with ethproofs-soundcalc guests in their mode subdirectory.
pub const FSV_REGISTRY: &[FsvRegistryEntry] = {
    use BlakeMode::{BlakeSpecialOpcodes, Compression};
    use FsvProfile::{CompressionFinalWrap, Standard};
    use FsvProgram::*;
    use SoundnessMode::{EthproofsSoundnessCalc, PessimisticConjecture};
    &[
        entry(
            PessimisticConjecture,
            UnrolledBaseLayer,
            Standard,
            Compression,
            "fsv_unrolled_base_layer_sec_100_blake2_with_compression.elf",
        ),
        entry(
            PessimisticConjecture,
            UnrolledRecursionLayer,
            Standard,
            Compression,
            "fsv_unrolled_recursion_layer_sec_100_blake2_with_compression.elf",
        ),
        entry(
            PessimisticConjecture,
            UnifiedRecursionLayer,
            Standard,
            Compression,
            "fsv_unified_recursion_layer_sec_100_blake2_with_compression.elf",
        ),
        entry(
            PessimisticConjecture,
            UnifiedRecursionLayer,
            Standard,
            BlakeSpecialOpcodes,
            "fsv_unified_recursion_layer_sec_100_special_opcodes_extension.elf",
        ),
        entry(
            PessimisticConjecture,
            UnifiedRecursionLayer,
            FsvProfile::Compression,
            BlakeSpecialOpcodes,
            "fsv_unified_recursion_layer_sec_100_compression_special_opcodes_extension.elf",
        ),
        entry(
            PessimisticConjecture,
            UnifiedRecursionLayer,
            CompressionFinalWrap,
            BlakeSpecialOpcodes,
            "fsv_unified_recursion_layer_sec_100_compression_final_wrap_special_opcodes_extension.elf",
        ),
        entry(
            EthproofsSoundnessCalc,
            UnrolledBaseLayer,
            Standard,
            Compression,
            "ethproofs_soundcalc/fsv_unrolled_base_layer_sec_100_blake2_with_compression.elf",
        ),
        entry(
            EthproofsSoundnessCalc,
            UnrolledRecursionLayer,
            Standard,
            Compression,
            "ethproofs_soundcalc/fsv_unrolled_recursion_layer_sec_100_blake2_with_compression.elf",
        ),
        entry(
            EthproofsSoundnessCalc,
            UnifiedRecursionLayer,
            Standard,
            Compression,
            "ethproofs_soundcalc/fsv_unified_recursion_layer_sec_100_blake2_with_compression.elf",
        ),
        entry(
            EthproofsSoundnessCalc,
            UnifiedRecursionLayer,
            Standard,
            BlakeSpecialOpcodes,
            "ethproofs_soundcalc/fsv_unified_recursion_layer_sec_100_special_opcodes_extension.elf",
        ),
    ]
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tags_roundtrip_through_parse() {
        for mode in BlakeMode::ALL {
            assert_eq!(BlakeMode::parse(mode.tag()), Some(*mode));
        }
        assert_eq!(BlakeMode::parse("nonsense"), None);
    }
}
