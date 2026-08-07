use std::collections::{BTreeMap, VecDeque};
use std::ffi::c_void;
use std::ptr::null_mut;

use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart_sys::{cudaGetSymbolAddress, cuda_struct_and_stub};

use super::super::super::GpuGKRStorage;
use super::encoding::GpuGKRDimensionReducingRound0BatchCompact;
use super::launchers::GkrEqSizes;
use super::shared::{
    ClaimBufferLayout, DeviceClaimPointAndBatching, GKR_BACKWARD_MAX_TRACE_LEN_LOG2,
};
use crate::upstream::{DimensionReducingInputOutput, GKRAddress, GKRInputs, OutputType};
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub(crate) enum GpuGKRDimensionReducingKernelKind {
    Pairwise = 0,
    Lookup = 1,
}

impl GpuGKRDimensionReducingKernelKind {
    pub(crate) const fn as_u32(self) -> u32 {
        self as u32
    }

    pub(crate) const fn challenge_count(self) -> usize {
        match self {
            Self::Pairwise => 1,
            Self::Lookup => 2,
        }
    }
}

// Dim-reducing layers are keyed by OutputType: 2 pairwise records for
// PermutationProduct, up to 3 lookup records, plus (unified circuit)
// 2 pairwise records for InitsAndTeardownsProduct = 7 records / 10 challenges.
// MUST stay in lockstep with the native mirror in
// native/gkr/support/descriptors.cuh (GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER /
// GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN).
pub(crate) const GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER: usize = 7;
pub(crate) const GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN: usize = 10;
/// Dim-reducing next-layer state stores `(folding_steps - 1)` per-round
/// challenges plus 3 transcript-squeezed values:
/// `[folding_challenges, r_before_last, r_last, next_batching]`.
pub(crate) const MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN: usize =
    GKR_BACKWARD_MAX_TRACE_LEN_LOG2 + 2;

cuda_struct_and_stub! {
    static ab_gkr_dim_reducing_batch_challenge_table:
        [E4; GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN];
}
cuda_struct_and_stub! {
    static ab_gkr_dim_reducing_layer_claim_point: [E4; MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN];
}

pub(crate) fn get_dim_reducing_layer_claim_point_device_ptr() -> *mut E4 {
    let mut ptr: *mut c_void = null_mut();
    // SAFETY: ab_gkr_dim_reducing_layer_claim_point is a valid
    // __constant__ symbol defined in backward/dim_reducing.cu.
    unsafe {
        cudaGetSymbolAddress(
            &mut ptr,
            &ab_gkr_dim_reducing_layer_claim_point as *const _ as *const c_void,
        )
    }
    .wrap()
    .expect("cudaGetSymbolAddress failed for ab_gkr_dim_reducing_layer_claim_point");
    ptr.cast()
}

fn get_dim_reducing_batch_challenge_table_device_ptr() -> *mut E4 {
    let mut ptr: *mut c_void = null_mut();
    // SAFETY: ab_gkr_dim_reducing_batch_challenge_table is a valid
    // __constant__ symbol defined in backward/dim_reducing.cu.
    unsafe {
        cudaGetSymbolAddress(
            &mut ptr,
            &ab_gkr_dim_reducing_batch_challenge_table as *const _ as *const c_void,
        )
    }
    .wrap()
    .expect("cudaGetSymbolAddress failed for ab_gkr_dim_reducing_batch_challenge_table");
    ptr as *mut E4
}

pub(crate) fn schedule_dim_reducing_batch_challenge_table_prelude(
    batch_challenge_base: *const E4,
    context: &ProverContext,
) -> CudaResult<()> {
    let table_ptr = get_dim_reducing_batch_challenge_table_device_ptr();
    // SAFETY: the symbol storage contains exactly
    // GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN E4 elements.
    let table = unsafe {
        DeviceSlice::from_raw_parts_mut(table_ptr, GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN)
    };
    // SAFETY: the caller passes a device-resident scalar that remains valid
    // until this stream-ordered prelude and all following kernels are scheduled.
    let base = unsafe { DeviceVariable::from_raw_parts(batch_challenge_base) };
    gpu_ops::powers::get_powers_by_ref::<E4>(base, 0, table, context.get_exec_stream())
}

pub(crate) struct GpuGKRDimensionReducingRoundScratch {
    pub(crate) eq_low_group: DeviceAllocation<E4>,
    pub(crate) accumulator: DeviceAllocation<E4>,
    /// Per-block partials buffer for the fused tail (stage-1 dual-reduce
    /// output, stage-2 mega-finalize input).
    pub(crate) partials: DeviceAllocation<E4>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct GpuGKRDimensionReducingKernelPlan {
    pub(crate) kind: GpuGKRDimensionReducingKernelKind,
    pub(crate) inputs: GKRInputs,
    pub(crate) batch_challenge_offset: usize,
}

#[doc(hidden)]
pub(crate) struct GpuGKRDimensionReducingSumcheckLayerPlan {
    pub layer_idx: usize,
    pub(crate) trace_len_after_reduction: usize,
    pub(crate) folding_steps: usize,
    pub(crate) kernel_plans: Vec<GpuGKRDimensionReducingKernelPlan>,
    pub(crate) folding_addresses: Vec<GKRAddress>,
    pub(crate) round0_batch_template_compact: GpuGKRDimensionReducingRound0BatchCompact<E4>,
    pub(crate) round_scratch: GpuGKRDimensionReducingRoundScratch,
    /// Strict 3-slot eq-sizes descriptor. Initialised at layer start from
    /// `make_eq_sizes(folding_steps - 1)`, mutated in place by
    /// `fold_eq_values_for_next_round` between sumcheck rounds, and passed by
    /// value into the dim-reducing consumer kernel arg structs.
    pub(crate) eq_sizes: GkrEqSizes,
}

// SAFETY: descriptor raw pointers are only forwarded to stream-ordered kernels.
unsafe impl Send for GpuGKRDimensionReducingSumcheckLayerPlan {}
unsafe impl Sync for GpuGKRDimensionReducingSumcheckLayerPlan {}

pub struct GpuGKRDimensionReducingBackwardState {
    #[allow(dead_code)] // Keeps queued forward ranges alive until the stream consumes them.
    pub(crate) forward_tracing_ranges: Vec<Range>,
    pub(crate) storage: GpuGKRStorage<BF, E4>,
    pub(crate) pending_layers:
        VecDeque<(usize, BTreeMap<OutputType, DimensionReducingInputOutput>)>,
    pub(crate) next_trace_len_after_reduction: usize,
}

#[doc(hidden)]
pub(crate) struct GpuGKRDimensionReducingScheduledLayerExecution {
    #[allow(dead_code)] // Keeps queued NVTX host callbacks alive until the stream consumes them.
    pub(crate) tracing_ranges: Vec<Range>,
    /// Device-resident Fiat-Shamir seed passed in by the caller, consumed by
    /// this layer's per-round + end-of-layer transcript work, and returned
    /// via `.take()` for the next backward layer scheduler to reuse. `None`
    /// after the orchestrator has pulled it out.
    pub device_seed: Option<DeviceAllocation<u32>>,
    /// Device-resident `[claim_point || batching_challenge]` buffer for the
    /// NEXT backward layer. Populated on-device from this layer's folding
    /// challenges + end-of-layer squeezed challenges. Taken by the orchestrator
    /// via `.take()`.
    pub device_claim_point_for_next_layer: Option<DeviceClaimPointAndBatching>,
    /// Device-resident `current_claims` buffer for the NEXT backward layer.
    /// This layer's `device_new_claims` becomes the next layer's input to
    /// `build_combined_claim`.
    pub device_claims_for_next_layer: Option<DeviceAllocation<E4>>,
    /// Explicit address order of `device_claims_for_next_layer`.
    pub claim_layout_for_next_layer: Option<ClaimBufferLayout>,
}
