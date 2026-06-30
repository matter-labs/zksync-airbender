use std::collections::{BTreeMap, VecDeque};
use std::ffi::c_void;
use std::ptr::null_mut;

use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart_sys::cudaGetSymbolAddress;

use super::super::super::{
    GpuGKRStorage, GpuSumcheckRound1PreparedStorage, GpuSumcheckRound2PreparedStorage,
    GpuSumcheckRound3AndBeyondPreparedStorage,
};
use super::encoding::{
    GpuGKRDimensionReducingContinuationBatchCompact, GpuGKRDimensionReducingRound0BatchCompact,
};
use super::launchers::GkrEqSizes;
use super::shared::{
    ClaimBufferLayout, DeviceClaimPointAndBatching, ScheduledDimensionReducingFinalReadback,
    GKR_BACKWARD_MAX_TRACE_LEN_LOG2,
};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::prover::ProverContext;
use crate::upstream::{
    DimensionReducingInputOutput, Field, FieldExtension, GKRInputs, OutputType, Seed,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DimensionReducingKernelBlueprint<E> {
    pub(crate) kind: GpuGKRDimensionReducingKernelKind,
    pub(crate) inputs: GKRInputs,
    pub(crate) batch_challenge_offset: usize,
    pub(crate) batch_challenge_count: usize,
    pub(crate) batch_challenges: Vec<E>,
}

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
}

// Dim-reducing layers are keyed by OutputType: 2 pairwise records for
// PermutationProduct, up to 3 lookup records, plus (unified circuit, PR #305)
// 2 pairwise records for InitsAndTeardownsProduct = 7 records / 10 challenges.
// MUST stay in lockstep with the native mirror in
// native/prover/gkr/support/descriptors.cuh (GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER /
// GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN).
pub(crate) const GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER: usize = 7;
pub(crate) const GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN: usize = 10;
/// Dim-reducing next-layer state stores `(folding_steps - 1)` per-round
/// challenges plus 3 transcript-squeezed values:
/// `[folding_challenges, r_before_last, r_last, next_batching]`.
pub(crate) const MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN: usize =
    GKR_BACKWARD_MAX_TRACE_LEN_LOG2 + 2;

extern "C" {
    static ab_gkr_dim_reducing_batch_challenge_table:
        [E4; GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN];
    static ab_gkr_dim_reducing_layer_claim_point: [E4; MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN];
}

pub(crate) fn get_dim_reducing_layer_claim_point_device_ptr() -> *mut E4 {
    use std::sync::OnceLock;

    static PTR: OnceLock<usize> = OnceLock::new();
    let ptr = *PTR.get_or_init(|| {
        let mut p: *mut c_void = null_mut();
        // SAFETY: ab_gkr_dim_reducing_layer_claim_point is a valid
        // __constant__ symbol defined in backward/dim_reducing.cu.
        unsafe {
            cudaGetSymbolAddress(
                &mut p,
                &ab_gkr_dim_reducing_layer_claim_point as *const _ as *const c_void,
            )
        }
        .wrap()
        .expect("cudaGetSymbolAddress failed for ab_gkr_dim_reducing_layer_claim_point");
        p as usize
    });
    ptr as *mut E4
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
    crate::ops::powers::get_powers_by_ref::<E4>(base, 0, false, table, context.get_exec_stream())
}

#[derive(Clone, Debug)]
pub(crate) struct GpuGKRDimensionReducingRound3Prepared<E> {
    pub(crate) step: usize,
    pub(crate) prepared: GpuSumcheckRound3AndBeyondPreparedStorage<E>,
}

#[allow(dead_code)]
pub(crate) struct GpuGKRDimensionReducingRoundScratch<E> {
    pub(crate) claim_point: DeviceAllocation<E>,
    pub(crate) eq_low_group: DeviceAllocation<E>,
    pub(crate) accumulator: DeviceAllocation<E>,
    pub(crate) reduction_output: DeviceAllocation<E>,
    pub(crate) reduction_temp_storage: DeviceAllocation<u8>,
    /// Per-block partials buffer for the fused tail (stage-1 dual-reduce
    /// output, stage-2 mega-finalize input).
    pub(crate) partials: DeviceAllocation<E>,
}

#[derive(Clone, Debug)]
pub(crate) struct GpuGKRDimensionReducingKernelPlan<B, E> {
    #[allow(dead_code)]
    pub(crate) kind: GpuGKRDimensionReducingKernelKind,
    pub(crate) inputs: GKRInputs,
    pub(crate) batch_challenge_offset: usize,
    #[allow(dead_code)]
    pub(crate) batch_challenge_count: usize,
    #[allow(dead_code)]
    pub(crate) batch_challenges: Vec<E>,
    pub(crate) round1_prepared: GpuSumcheckRound1PreparedStorage<B, E>,
    pub(crate) round2_prepared: Option<GpuSumcheckRound2PreparedStorage<B, E>>,
    pub(crate) round3_and_beyond_prepared: Vec<GpuGKRDimensionReducingRound3Prepared<E>>,
}

pub(crate) struct GpuGKRDimensionReducingSumcheckLayerPlan<B, E> {
    pub(crate) layer_idx: usize,
    #[allow(dead_code)]
    pub(crate) trace_len_after_reduction: usize,
    pub(crate) folding_steps: usize,
    #[allow(dead_code)]
    pub(crate) batch_challenge_base: Option<E>,
    pub(crate) kernel_plans: Vec<GpuGKRDimensionReducingKernelPlan<B, E>>,
    pub(crate) round0_batch_template_compact: GpuGKRDimensionReducingRound0BatchCompact<E>,
    pub(crate) round1_batch_template_compact: GpuGKRDimensionReducingContinuationBatchCompact<E>,
    /// Single descriptor reused for every continuation step >= 2. The kernel
    /// derives per-step folding-buffer offsets from `step + acc_size`.
    pub(crate) continuation_batch_template_compact:
        GpuGKRDimensionReducingContinuationBatchCompact<E>,
    pub(crate) round_scratch: GpuGKRDimensionReducingRoundScratch<E>,
    /// When set, `batch_challenge_base_ptr()` returns this raw pointer instead
    /// of `round_scratch.claim_point.as_ptr().add(folding_steps)`. The
    /// workflow_state path uses this to point at the orchestrator-owned
    /// `device_claim_point_in[folding_steps]` so the per-layer
    /// `round_scratch.claim_point` D2D is no longer needed.
    pub(crate) batch_challenge_base_override_ptr: Option<*const E>,
    /// Strict 3-slot eq-sizes descriptor. Initialised at layer start from
    /// `make_eq_sizes(folding_steps - 1)`, mutated in place by
    /// `fold_eq_values_for_next_round` between sumcheck rounds, and passed by
    /// value into the dim-reducing consumer kernel arg structs.
    pub(crate) eq_sizes: GkrEqSizes,
}

// SAFETY: `batch_challenge_base_override_ptr` only stores a raw pointer into a
// device allocation that the caller keeps alive for the full duration of any
// scheduled stream op consuming this layer plan. The pointer is never
// dereferenced from Rust — it is only forwarded to kernel arguments.
unsafe impl<B, E> Send for GpuGKRDimensionReducingSumcheckLayerPlan<B, E>
where
    B: Send,
    E: Send,
{
}
unsafe impl<B, E> Sync for GpuGKRDimensionReducingSumcheckLayerPlan<B, E>
where
    B: Sync,
    E: Sync,
{
}

pub(crate) struct GpuGKRDimensionReducingBackwardState<B, E> {
    #[allow(dead_code)] // Keeps queued forward ranges alive until the stream consumes them.
    pub(crate) forward_tracing_ranges: Vec<Range>,
    pub(crate) storage: GpuGKRStorage<B, E>,
    pub(crate) pending_layers:
        VecDeque<(usize, BTreeMap<OutputType, DimensionReducingInputOutput>)>,
    pub(crate) next_trace_len_after_reduction: usize,
}

pub(crate) struct ScheduledDimensionReducingLayerExecutionState<E: FieldExtension<BF> + Field> {
    pub(crate) seed: Seed,
    pub(crate) folding_challenges: Vec<E>,
}

pub(crate) struct GpuGKRDimensionReducingScheduledLayerExecution<B, E: FieldExtension<BF> + Field> {
    #[allow(dead_code)] // Keeps queued NVTX host callbacks alive until the stream consumes them.
    pub(crate) tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    // Keeps layer-start callbacks alive until the stream consumes them.
    pub(crate) start_callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(crate) final_readback: ScheduledDimensionReducingFinalReadback,
    #[allow(dead_code)]
    // keepalive: shared state is referenced by stream-scheduled callbacks via shared_state_handle.
    pub(crate) shared_state: Box<ScheduledDimensionReducingLayerExecutionState<E>>,
    /// Device-resident Fiat-Shamir seed passed in by the caller, consumed by
    /// this layer's per-round + end-of-layer transcript work, and returned
    /// via `.take()` for the next backward layer scheduler to reuse. `None`
    /// after the orchestrator has pulled it out. Replaces the per-layer entry
    /// H2D that used to mirror `workflow_state.seed` into a fresh device slot.
    pub(crate) device_seed: Option<DeviceAllocation<u32>>,
    /// Device-resident `[claim_point || batching_challenge]` buffer for the
    /// NEXT backward layer. Populated on-device from this layer's folding
    /// challenges + end-of-layer squeezed challenges. Taken by the orchestrator
    /// via `.take()`. Replaces the per-layer entry H2D that used to copy
    /// `workflow_state.current_claim_point` + `current_batching_challenge`
    /// from host.
    pub(crate) device_claim_point_for_next_layer: Option<DeviceClaimPointAndBatching<E>>,
    /// Device-resident `current_claims` buffer for the NEXT backward layer.
    /// This layer's `device_new_claims` becomes the next layer's input to
    /// `build_combined_claim`.
    pub(crate) device_claims_for_next_layer: Option<DeviceAllocation<E>>,
    /// Explicit address order of `device_claims_for_next_layer`.
    pub(crate) claim_layout_for_next_layer: Option<ClaimBufferLayout>,
    #[allow(dead_code)]
    pub(crate) _phantom: std::marker::PhantomData<B>,
}

#[cfg(test)]
mod cap_tests {
    use super::{
        GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN, GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER,
    };

    // Lockstep guard: these two values are mirrored verbatim into
    // native/prover/gkr/support/descriptors.cuh:52-53. If you change one
    // side you MUST change the other; this test fails loudly to force it.
    #[test]
    fn gkr_dim_reducing_caps_lockstep() {
        assert_eq!(GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER, 7);
        assert_eq!(GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN, 10);
    }
}
