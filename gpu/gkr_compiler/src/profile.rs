#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ForwardResourceProfile {
    pub cache_cells: usize,
}

/// Backward compiler capacities selected for one GPU implementation.
///
/// R0 and continuation are deliberately separate concrete profiles. Their wire
/// formats and compiler pipelines are different even where today's capacities
/// happen to coincide.
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
        Self {
            r0: R0ResourceProfile {
                source_window_columns: SOURCE_WINDOW_COLUMNS,
                max_source_windows: MAX_SOURCE_WINDOWS,
                max_immediates: LEAN_MAX_IMMEDIATES,
                max_coefficient_recipes: in_scope::MAX_COEFFICIENT_RECIPES,
                max_sources: in_scope::MAX_SOURCES,
                max_projections: in_scope::MAX_PROJECTIONS,
                max_records: in_scope::MAX_TERMS,
                max_program_words: LEAN_WORDS_PER_TERM * in_scope::MAX_TERMS,
            },
            continuations: ContinuationResourceProfile {
                source_window_columns: SOURCE_WINDOW_COLUMNS,
                max_source_windows: MAX_SOURCE_WINDOWS,
                max_immediates: LEAN_MAX_IMMEDIATES,
                max_coefficient_recipes: in_scope::MAX_COEFFICIENT_RECIPES,
                max_sources: in_scope::MAX_SOURCES,
                max_projections: in_scope::MAX_PROJECTIONS,
                max_records: in_scope::MAX_RECORDS,
                max_program_words: LEAN_WORDS_PER_TERM * in_scope::MAX_RECORDS,
                max_fragment_atoms: in_scope::MAX_FRAGMENT_ATOMS,
                max_expansion_factor: in_scope::MAX_EXPANSION_FACTOR,
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResourceProfileError {
    Zero {
        field: &'static str,
    },
    ExceedsWire {
        field: &'static str,
        value: usize,
        maximum: usize,
    },
    Inconsistent {
        field: &'static str,
        required: usize,
        actual: usize,
    },
}

impl ResourceProfileError {
    pub const fn field(&self) -> &'static str {
        match self {
            Self::Zero { field }
            | Self::ExceedsWire { field, .. }
            | Self::Inconsistent { field, .. } => field,
        }
    }
}

impl core::fmt::Display for ResourceProfileError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Zero { field } => write!(formatter, "{field} must be nonzero"),
            Self::ExceedsWire {
                field,
                value,
                maximum,
            } => write!(
                formatter,
                "{field}={value} exceeds the wire maximum {maximum}"
            ),
            Self::Inconsistent {
                field,
                required,
                actual,
            } => write!(
                formatter,
                "{field}={actual} is smaller than the required {required}"
            ),
        }
    }
}

impl std::error::Error for ResourceProfileError {}

const WIRE_SOURCE_WINDOW_COLUMNS: usize = 128;
const WIRE_SOURCE_WINDOWS: usize = 64;
const WIRE_COEFFICIENT_ENCODINGS: usize = 1 << 13;
const RESERVED_COEFFICIENT_ENCODINGS: usize = 2;
const WIRE_IMMEDIATE_ENCODINGS: usize = 1 << 13;
const RESERVED_IMMEDIATE_ENCODINGS: usize = 2;
const WORDS_PER_RECORD: usize = 4;
const KERNEL_ARGUMENT_WORDS: usize = 32_764 / 2;

fn validate_common(
    source_window_columns: usize,
    max_source_windows: usize,
    max_immediates: usize,
    max_coefficient_recipes: usize,
    max_sources: usize,
    max_projections: usize,
    max_records: usize,
    max_program_words: usize,
) -> Result<(), ResourceProfileError> {
    let nonzero = [
        ("source_window_columns", source_window_columns),
        ("max_source_windows", max_source_windows),
        ("max_immediates", max_immediates),
        ("max_coefficient_recipes", max_coefficient_recipes),
        ("max_sources", max_sources),
        ("max_projections", max_projections),
        ("max_records", max_records),
        ("max_program_words", max_program_words),
    ];
    if let Some((field, _)) = nonzero.into_iter().find(|(_, value)| *value == 0) {
        return Err(ResourceProfileError::Zero { field });
    }

    for (field, value, maximum) in [
        (
            "source_window_columns",
            source_window_columns,
            WIRE_SOURCE_WINDOW_COLUMNS,
        ),
        (
            "max_source_windows",
            max_source_windows,
            WIRE_SOURCE_WINDOWS,
        ),
        (
            "max_immediates",
            max_immediates + RESERVED_IMMEDIATE_ENCODINGS,
            WIRE_IMMEDIATE_ENCODINGS,
        ),
        (
            "max_coefficient_recipes",
            max_coefficient_recipes + RESERVED_COEFFICIENT_ENCODINGS,
            WIRE_COEFFICIENT_ENCODINGS,
        ),
        (
            "max_program_words",
            max_program_words,
            KERNEL_ARGUMENT_WORDS,
        ),
    ] {
        if value > maximum {
            return Err(ResourceProfileError::ExceedsWire {
                field,
                value,
                maximum,
            });
        }
    }

    let required = max_records.saturating_mul(WORDS_PER_RECORD);
    if max_program_words < required {
        return Err(ResourceProfileError::Inconsistent {
            field: "max_program_words",
            required,
            actual: max_program_words,
        });
    }
    Ok(())
}

pub fn validate_r0_profile(profile: &R0ResourceProfile) -> Result<(), ResourceProfileError> {
    validate_common(
        profile.source_window_columns,
        profile.max_source_windows,
        profile.max_immediates,
        profile.max_coefficient_recipes,
        profile.max_sources,
        profile.max_projections,
        profile.max_records,
        profile.max_program_words,
    )
}

pub fn validate_continuation_profile(
    profile: &ContinuationResourceProfile,
) -> Result<(), ResourceProfileError> {
    validate_common(
        profile.source_window_columns,
        profile.max_source_windows,
        profile.max_immediates,
        profile.max_coefficient_recipes,
        profile.max_sources,
        profile.max_projections,
        profile.max_records,
        profile.max_program_words,
    )?;
    for (field, value) in [
        ("max_fragment_atoms", profile.max_fragment_atoms),
        ("max_expansion_factor", profile.max_expansion_factor),
    ] {
        if value == 0 {
            return Err(ResourceProfileError::Zero { field });
        }
    }
    Ok(())
}
use crate::backward::common::lean::LEAN_WORDS_PER_TERM;
use crate::backward::common::limits::{
    LEAN_MAX_IMMEDIATES, MAX_SOURCE_WINDOWS, SOURCE_WINDOW_COLUMNS, in_scope,
};
