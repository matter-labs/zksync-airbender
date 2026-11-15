use crate::{
    backward::kernels::{make_eq_sizes, GKR_BACKWARD_MAX_TRACE_LEN_LOG2},
    upstream::GKRAddress,
};

pub(crate) const DR_WINDOW_COORDINATES: usize = 3;
pub(crate) const DR_WINDOW_ROWS_PER_TILE: usize = 32;
pub(crate) const DR_WINDOW_TENSOR_CELLS: usize = 27;
pub(crate) const DR_WINDOW_MIN_FOLDING_STEPS: usize = 4;
pub(crate) const DR_WINDOW_MAX_FOLDING_STEPS: usize = GKR_BACKWARD_MAX_TRACE_LEN_LOG2;
pub(crate) const DR_WINDOW_BLOCK_THREADS: u32 = 288;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum DrWindowBindError {
    Cuda(era_cudart_sys::CudaError),
    UnsupportedFoldingSteps {
        folding_steps: usize,
    },
    ScratchCapacity {
        required: usize,
        capacity: usize,
    },
    EqBuildOffset {
        expected: usize,
        observed: usize,
    },
    EqSizeMismatch,
    InvalidContinuationBoundary {
        folding_steps: usize,
        start_round: usize,
    },
    InvalidTailEntry {
        entry_round: usize,
    },
    MissingPublicationIndex {
        dense_slot: usize,
        input_operand: usize,
    },
    PublicationIndexOverflow {
        publication_index: usize,
        canonical_source_count: usize,
    },
    ArenaGeometryOverflow {
        log2_stride: u32,
        poly_count: usize,
    },
    ArenaCapacity {
        required: usize,
        capacity: usize,
    },
    MissingSource {
        address: GKRAddress,
        logical_layer: usize,
    },
    StrideMismatch {
        backing: usize,
        expected_log2_stride: u32,
        observed_log2_stride: u32,
    },
    FinalPublicationStrideMismatch {
        owner_log2_stride: u32,
        planned_log2_stride: u32,
    },
    BaseSlotOverflow {
        required: usize,
        capacity: usize,
    },
    PolyIndexOverflow {
        poly_index: usize,
        capacity: usize,
    },
    NullContinuationPointer {
        pointer: &'static str,
    },
    NullContinuationTableBase {
        slot: usize,
        input_operand: usize,
        table_slot: usize,
        destination: bool,
    },
    ContinuationEqAliasedPointers {
        first: &'static str,
        second: &'static str,
    },
    ContinuationEqLowMismatch,
}

impl From<era_cudart_sys::CudaError> for DrWindowBindError {
    fn from(error: era_cudart_sys::CudaError) -> Self {
        Self::Cuda(error)
    }
}

impl core::fmt::Display for DrWindowBindError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for DrWindowBindError {}

pub(crate) fn dr_window_row_tiles(folding_steps: usize) -> usize {
    let log_rows = folding_steps - DR_WINDOW_COORDINATES;
    (1usize << log_rows)
        .div_ceil(DR_WINDOW_ROWS_PER_TILE)
        .max(1)
}

pub(crate) fn dr_window_log_rows(folding_steps: usize) -> u32 {
    assert!(folding_steps >= DR_WINDOW_COORDINATES);
    (folding_steps - DR_WINDOW_COORDINATES) as u32
}

pub(crate) fn dr_window_partials_len(folding_steps: usize) -> usize {
    DR_WINDOW_TENSOR_CELLS * (dr_window_row_tiles(folding_steps) + 1)
}

pub(crate) fn validate_dr_window_folding_steps(
    folding_steps: usize,
) -> Result<(), DrWindowBindError> {
    if !(DR_WINDOW_MIN_FOLDING_STEPS..=DR_WINDOW_MAX_FOLDING_STEPS).contains(&folding_steps) {
        return Err(DrWindowBindError::UnsupportedFoldingSteps { folding_steps });
    }
    Ok(())
}

pub(crate) fn validate_dr_r0_eq_contract(
    folding_steps: usize,
    build_offset: usize,
    eq_sizes: crate::backward::GkrEqSizes,
) -> Result<(), DrWindowBindError> {
    if build_offset != DR_WINDOW_COORDINATES {
        return Err(DrWindowBindError::EqBuildOffset {
            expected: DR_WINDOW_COORDINATES,
            observed: build_offset,
        });
    }
    if eq_sizes != make_eq_sizes(folding_steps - DR_WINDOW_COORDINATES) {
        return Err(DrWindowBindError::EqSizeMismatch);
    }
    Ok(())
}
