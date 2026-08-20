//! Compatibility view of the measured backward-resource envelope.
//!
//! Production compilation uses the fixed descriptor constants in `backward`.
//! The standalone benchmark also records the measured corpus envelope in its
//! frozen ABI and therefore needs these values as data.

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GpuResourceProfile {
    pub r0: R0ResourceProfile,
    pub continuations: ContinuationResourceProfile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R0ResourceProfile {
    pub source_window_columns: usize,
    pub max_source_windows: usize,
    pub max_immediates: usize,
    pub max_coefficient_recipes: usize,
    pub max_sources: usize,
    pub max_projections: usize,
    pub max_records: usize,
    pub max_program_words: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContinuationResourceProfile {
    pub source_window_columns: usize,
    pub max_source_windows: usize,
    pub max_immediates: usize,
    pub max_coefficient_recipes: usize,
    pub max_sources: usize,
    pub max_projections: usize,
    pub max_records: usize,
    pub max_program_words: usize,
    pub max_fragment_atoms: usize,
    pub max_expansion_factor: usize,
}

impl GpuResourceProfile {
    pub const fn production() -> Self {
        const MAX_COEFFICIENT_RECIPES: usize = 1_138;
        const MAX_SOURCES: usize = 1_062;
        const MAX_PROJECTIONS: usize = 1_731;
        const MAX_R0_RECORDS: usize = 1_791;
        const MAX_CONTINUATION_RECORDS: usize = 2_156;
        const WORDS_PER_RECORD: usize = 4;

        Self {
            r0: R0ResourceProfile {
                source_window_columns: 128,
                max_source_windows: 64,
                max_immediates: 512,
                max_coefficient_recipes: MAX_COEFFICIENT_RECIPES,
                max_sources: MAX_SOURCES,
                max_projections: MAX_PROJECTIONS,
                max_records: MAX_R0_RECORDS,
                max_program_words: WORDS_PER_RECORD * MAX_R0_RECORDS,
            },
            continuations: ContinuationResourceProfile {
                source_window_columns: 128,
                max_source_windows: 64,
                max_immediates: 512,
                max_coefficient_recipes: MAX_COEFFICIENT_RECIPES,
                max_sources: MAX_SOURCES,
                max_projections: MAX_PROJECTIONS,
                max_records: MAX_CONTINUATION_RECORDS,
                max_program_words: WORDS_PER_RECORD * MAX_CONTINUATION_RECORDS,
                max_fragment_atoms: 2,
                max_expansion_factor: 46,
            },
        }
    }
}
