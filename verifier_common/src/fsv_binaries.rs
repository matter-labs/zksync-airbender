
use crate::prover::definitions::USE_REDUCED_BLAKE2_ROUNDS;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BlakeMode {
    Compression,
    GFunction,
    BlakeSpecialOpcodes,
}

impl BlakeMode {
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::Compression => "blake2_with_compression",
            Self::GFunction => "blake2_g_function",
            Self::BlakeSpecialOpcodes => "special_opcodes_extension",
        }
    }

    #[must_use]
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "blake2_with_compression" | "compression" | "round" => Some(Self::Compression),
            "blake2_g_function" | "g_function" | "g" => Some(Self::GFunction),
            "special_opcodes_extension" | "special_opcodes" | "spec" => {
                Some(Self::BlakeSpecialOpcodes)
            }
            _ => None,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
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
            Self::UnrolledBaseLayer => "fsv_unrolled_base_layer_sec_80",
            Self::UnrolledRecursionLayer => "fsv_unrolled_recursion_layer_sec_80",
            Self::UnifiedBaseLayer => "fsv_unified_base_layer_sec_80",
            Self::UnifiedRecursionLayer => "fsv_unified_recursion_layer_sec_80",
        }
    }

    #[must_use]
    pub const fn reduced_rounds(self) -> bool {
        USE_REDUCED_BLAKE2_ROUNDS
    }

    #[must_use]
    pub const fn supports(self, mode: BlakeMode) -> bool {
        match (self, mode) {
            (Self::UnifiedBaseLayer | Self::UnifiedRecursionLayer, _) => true,
            (_, BlakeMode::BlakeSpecialOpcodes) => false,
            (_, _) => true,
        }
    }

    #[must_use]
    pub fn file_stem(self, mode: BlakeMode) -> alloc::string::String {
        assert!(
            self.supports(mode),
            "{} is not built with blake mode {}",
            self.base_name(),
            mode.tag()
        );
        alloc::format!("{}_{}", self.base_name(), mode.tag())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tags_roundtrip_through_parse() {
        for mode in [
            BlakeMode::Compression,
            BlakeMode::GFunction,
            BlakeMode::BlakeSpecialOpcodes,
        ] {
            assert_eq!(BlakeMode::parse(mode.tag()), Some(mode));
        }
        assert_eq!(BlakeMode::parse("nonsense"), None);
    }

    #[test]
    fn special_opcodes_is_unified_only() {
        assert!(FsvProgram::UnifiedRecursionLayer.supports(BlakeMode::BlakeSpecialOpcodes));
        assert!(!FsvProgram::UnrolledBaseLayer.supports(BlakeMode::BlakeSpecialOpcodes));
        assert!(!FsvProgram::UnrolledRecursionLayer.supports(BlakeMode::BlakeSpecialOpcodes));
        assert!(FsvProgram::UnrolledBaseLayer.supports(BlakeMode::GFunction));
    }

    #[test]
    fn registry_matches_checked_in_binaries() {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../tools/gkr_verifier");
        // Blake-suffixed recursion-pipeline variants.
        for (program, modes) in [
            (
                FsvProgram::UnrolledBaseLayer,
                &[BlakeMode::Compression, BlakeMode::GFunction][..],
            ),
            (
                FsvProgram::UnrolledRecursionLayer,
                &[BlakeMode::Compression, BlakeMode::GFunction][..],
            ),
            (
                FsvProgram::UnifiedRecursionLayer,
                &[
                    BlakeMode::Compression,
                    BlakeMode::GFunction,
                    BlakeMode::BlakeSpecialOpcodes,
                ][..],
            ),
        ] {
            for mode in modes {
                for ext in ["bin", "text"] {
                    let path = dir.join(alloc::format!("{}.{ext}", program.file_stem(*mode)));
                    assert!(path.exists(), "missing fsv binary {}", path.display());
                }
            }
        }
    }
}
