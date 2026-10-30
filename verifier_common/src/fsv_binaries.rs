//! The registry of full-statement verifier guest binaries: which guest is built for which
//! (security level, soundness mode, layer, profile, blake mode), and where it lives under the
//! FSV root (`tools/gkr_verifier/full_statement_verifiers/`). Lookups are exact: a descriptor
//! without a row is an error naming the reason, never a fallback to a neighbouring binary.
//! The pinned identity of every row lives in the tracked manifest next to the binaries,
//! checked by `full_statement_verifier::host_utils::load_fsv_exact`.

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
    pub const fn base_name(self) -> &'static str {
        match self {
            Self::UnrolledBaseLayer => "fsv_unrolled_base_layer_sec_100",
            Self::UnrolledRecursionLayer => "fsv_unrolled_recursion_layer_sec_100",
            Self::UnifiedBaseLayer => "fsv_unified_base_layer_sec_100",
            Self::UnifiedRecursionLayer => "fsv_unified_recursion_layer_sec_100",
        }
    }

    /// Manifest token of the layer.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::UnrolledBaseLayer => "unrolled_base_layer",
            Self::UnrolledRecursionLayer => "unrolled_recursion_layer",
            Self::UnifiedBaseLayer => "unified_base_layer",
            Self::UnifiedRecursionLayer => "unified_recursion_layer",
        }
    }

    #[must_use]
    pub const fn reduced_rounds(self) -> bool {
        USE_REDUCED_BLAKE2_ROUNDS
    }

    /// Whether some soundness mode has a standard-profile guest of this layer built with
    /// `blake` (the union of [`FSV_REGISTRY`] over modes). Selecting a guest for one mode goes
    /// through [`FsvDescriptor::registry_entry`].
    #[must_use]
    pub const fn supports(self, blake: BlakeMode) -> bool {
        matches!(
            (self, blake),
            (
                Self::UnrolledBaseLayer | Self::UnrolledRecursionLayer | Self::UnifiedBaseLayer,
                BlakeMode::Compression
            ) | (
                Self::UnifiedRecursionLayer,
                BlakeMode::Compression | BlakeMode::BlakeSpecialOpcodes
            )
        )
    }
}

/// The statement a guest verifies within its layer.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FsvProfile {
    /// The recursion pipeline's statement.
    Standard,
    /// Unified recursion verifying the merged-mode L1 feeder schedule.
    L1Feeder,
}

impl FsvProfile {
    /// Manifest token of the profile.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::Standard => "standard",
            Self::L1Feeder => "l1_feeder",
        }
    }
}

/// Exact identity of a full-statement verifier guest.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct FsvDescriptor {
    pub security: SecurityLevel,
    pub soundness_mode: SoundnessMode,
    pub program: FsvProgram,
    pub profile: FsvProfile,
    pub blake: BlakeMode,
}

impl FsvDescriptor {
    /// A standard-profile descriptor.
    #[must_use]
    pub const fn new(
        security: SecurityLevel,
        soundness_mode: SoundnessMode,
        program: FsvProgram,
        blake: BlakeMode,
    ) -> Self {
        Self {
            security,
            soundness_mode,
            program,
            profile: FsvProfile::Standard,
            blake,
        }
    }

    /// The registry row of this descriptor, or the reason no guest is built for it.
    pub fn registry_entry(&self) -> Result<&'static FsvRegistryEntry, UnsupportedFsvVariant> {
        FSV_REGISTRY
            .iter()
            .find(|entry| entry.descriptor == *self)
            .ok_or(UnsupportedFsvVariant {
                descriptor: *self,
                reason: unsupported_reason(self),
            })
    }

    /// The manifest tokens: security, soundness mode, layer, profile, blake mode.
    #[must_use]
    pub fn tokens(&self) -> [&'static str; 5] {
        [
            self.security.dir_suffix(),
            self.soundness_mode.file_suffix(),
            self.program.tag(),
            self.profile.tag(),
            self.blake.tag(),
        ]
    }
}

impl core::fmt::Display for FsvDescriptor {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let [security, mode, program, profile, blake] = self.tokens();
        write!(f, "{security}/{mode}/{program}/{profile}/{blake}")
    }
}

/// A built guest: its descriptor and its path relative to the FSV root.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FsvRegistryEntry {
    pub descriptor: FsvDescriptor,
    pub relative_path: &'static str,
}

/// A descriptor no guest is built for.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct UnsupportedFsvVariant {
    pub descriptor: FsvDescriptor,
    pub reason: &'static str,
}

impl core::fmt::Display for UnsupportedFsvVariant {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "no full-statement verifier is built for {}: {}",
            self.descriptor, self.reason
        )
    }
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
            security: SecurityLevel::Sec100,
            soundness_mode,
            program,
            profile,
            blake,
        },
        relative_path,
    }
}

/// Every built guest. Pessimistic-conjecture guests keep their historical flat names (the
/// unified base layer is the one unsuffixed file); ethproofs-soundcalc guests live in the
/// `ethproofs_soundcalc/` subdirectory under the same basenames.
pub const FSV_REGISTRY: &[FsvRegistryEntry] = {
    use BlakeMode::{BlakeSpecialOpcodes, Compression};
    use FsvProfile::{L1Feeder, Standard};
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
            UnifiedBaseLayer,
            Standard,
            Compression,
            "fsv_unified_base_layer_sec_100.elf",
        ),
        entry(
            PessimisticConjecture,
            UnifiedRecursionLayer,
            L1Feeder,
            BlakeSpecialOpcodes,
            "fsv_unified_recursion_layer_sec_100_l1_feeder_special_opcodes_extension.elf",
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

fn unsupported_reason(descriptor: &FsvDescriptor) -> &'static str {
    use FsvProgram::*;
    use SoundnessMode::EthproofsSoundnessCalc;
    match (
        descriptor.soundness_mode,
        descriptor.program,
        descriptor.profile,
        descriptor.blake,
    ) {
        (_, _, _, BlakeMode::GFunction | BlakeMode::Software) => {
            "no guest is built with the G-function delegation or software blake"
        }
        (EthproofsSoundnessCalc, _, FsvProfile::L1Feeder, _) => {
            "ethproofs_soundcalc is not implemented for the L1 feeder/wrap/EVM profile \
             (deferred product scope); its schedule exists only in pessimistic_conjecture"
        }
        (_, _, FsvProfile::L1Feeder, _) => {
            "the L1 feeder is built only as the special-opcodes unified recursion verifier"
        }
        (EthproofsSoundnessCalc, UnifiedBaseLayer, _, _) => {
            "the recursion pipeline never selects the unified base layer, so no \
             ethproofs_soundcalc guest is built for it"
        }
        (_, _, _, BlakeMode::BlakeSpecialOpcodes) => {
            "special-opcodes blake is built only for the unified recursion layer"
        }
        _ => "no guest is built for this security level",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const PIPELINE_ROWS: [(FsvProgram, BlakeMode); 4] = [
        (FsvProgram::UnrolledBaseLayer, BlakeMode::Compression),
        (FsvProgram::UnrolledRecursionLayer, BlakeMode::Compression),
        (FsvProgram::UnifiedRecursionLayer, BlakeMode::Compression),
        (
            FsvProgram::UnifiedRecursionLayer,
            BlakeMode::BlakeSpecialOpcodes,
        ),
    ];

    fn programs() -> [FsvProgram; 4] {
        [
            FsvProgram::UnrolledBaseLayer,
            FsvProgram::UnrolledRecursionLayer,
            FsvProgram::UnifiedBaseLayer,
            FsvProgram::UnifiedRecursionLayer,
        ]
    }

    #[test]
    fn tags_roundtrip_through_parse() {
        for mode in BlakeMode::ALL {
            assert_eq!(BlakeMode::parse(mode.tag()), Some(*mode));
        }
        assert_eq!(BlakeMode::parse("nonsense"), None);
    }

    #[test]
    fn registry_rows_and_paths_are_unique() {
        for (i, a) in FSV_REGISTRY.iter().enumerate() {
            for b in &FSV_REGISTRY[i + 1..] {
                assert_ne!(a.descriptor, b.descriptor);
                assert_ne!(a.relative_path, b.relative_path);
            }
        }
        assert_eq!(FSV_REGISTRY.len(), 10);
    }

    #[test]
    fn every_mode_has_the_pipeline_guests() {
        for mode in SoundnessMode::ALL {
            for (program, blake) in PIPELINE_ROWS {
                let descriptor = FsvDescriptor::new(SecurityLevel::Sec100, *mode, program, blake);
                let entry = descriptor.registry_entry().unwrap();
                let file = alloc::format!("{}_{}.elf", program.base_name(), blake.tag());
                let expected = match mode {
                    SoundnessMode::PessimisticConjecture => file,
                    SoundnessMode::EthproofsSoundnessCalc => {
                        alloc::format!("ethproofs_soundcalc/{file}")
                    }
                };
                assert_eq!(entry.relative_path, expected);
            }
        }
    }

    #[test]
    fn supports_is_the_union_of_standard_rows() {
        for program in programs() {
            for blake in BlakeMode::ALL {
                let built = FSV_REGISTRY.iter().any(|entry| {
                    entry.descriptor.program == program
                        && entry.descriptor.profile == FsvProfile::Standard
                        && entry.descriptor.blake == *blake
                });
                assert_eq!(program.supports(*blake), built, "{program:?} {blake:?}");
            }
        }
    }

    #[test]
    fn missing_variants_name_their_reason() {
        let sec = SecurityLevel::Sec100;
        let ethproofs = SoundnessMode::EthproofsSoundnessCalc;
        let pessimistic = SoundnessMode::PessimisticConjecture;

        let unified_base = FsvDescriptor::new(
            sec,
            ethproofs,
            FsvProgram::UnifiedBaseLayer,
            BlakeMode::Compression,
        );
        let err = unified_base.registry_entry().unwrap_err();
        assert!(err.reason.contains("never selects the unified base layer"));

        let feeder = FsvDescriptor {
            profile: FsvProfile::L1Feeder,
            ..FsvDescriptor::new(
                sec,
                ethproofs,
                FsvProgram::UnifiedRecursionLayer,
                BlakeMode::BlakeSpecialOpcodes,
            )
        };
        let err = feeder.registry_entry().unwrap_err();
        assert!(err
            .reason
            .contains("not implemented for the L1 feeder/wrap/EVM profile"));
        assert!(FsvDescriptor {
            soundness_mode: pessimistic,
            ..feeder
        }
        .registry_entry()
        .is_ok());

        let special_unrolled = FsvDescriptor::new(
            sec,
            pessimistic,
            FsvProgram::UnrolledBaseLayer,
            BlakeMode::BlakeSpecialOpcodes,
        );
        let err = special_unrolled.registry_entry().unwrap_err();
        assert!(err.reason.contains("only for the unified recursion layer"));

        for mode in SoundnessMode::ALL {
            for program in programs() {
                for blake in [BlakeMode::GFunction, BlakeMode::Software] {
                    let err = FsvDescriptor::new(sec, *mode, program, blake)
                        .registry_entry()
                        .unwrap_err();
                    assert!(err.reason.contains("G-function delegation or software"));
                }
            }
        }
    }

    #[test]
    fn display_joins_the_manifest_tokens() {
        let entry = &FSV_REGISTRY[6];
        assert_eq!(
            alloc::format!("{}", entry.descriptor),
            "sec_100/ethproofs_soundcalc/unrolled_base_layer/standard/blake2_with_compression"
        );
    }
}
