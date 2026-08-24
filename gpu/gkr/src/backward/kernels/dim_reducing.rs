use std::collections::{BTreeMap, VecDeque};
use std::ffi::c_void;
use std::ptr::null_mut;

use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart_sys::{cudaGetSymbolAddress, cuda_struct_and_stub};

use super::super::super::GpuGKRStorage;
use super::encoding::GpuGKRDimensionReducingBatch;
use super::launchers::GkrEqSizes;
use super::shared::{
    ClaimBufferLayout, DeviceClaimPointAndBatching, GKR_BACKWARD_MAX_TRACE_LEN_LOG2,
};
use crate::upstream::{DimensionReducingInputOutput, GKRAddress, OutputType};
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;

// Dim-reducing layers carry one slot per OutputType, in OutputType discriminant
// order, each with 2 inputs / 2 outputs / 2 batch challenges. MUST stay in
// lockstep with the native mirror in native/gkr/support/descriptors.cuh.
pub(crate) const GKR_DIM_REDUCING_SLOTS: usize = 5;
pub(crate) const GKR_DIM_REDUCING_INPUTS_PER_SLOT: usize = 2;
pub(crate) const GKR_DIM_REDUCING_OUTPUTS_PER_SLOT: usize = 2;
pub(crate) const GKR_DIM_REDUCING_IO_PER_SLOT: usize =
    GKR_DIM_REDUCING_INPUTS_PER_SLOT + GKR_DIM_REDUCING_OUTPUTS_PER_SLOT;
pub(crate) const GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN: usize =
    GKR_DIM_REDUCING_SLOTS * GKR_DIM_REDUCING_OUTPUTS_PER_SLOT;

/// Wire slot index for an output type. The device derives each slot's kind from
/// this index at compile time, and exponents are packed densely in this order,
/// which must stay the `OutputType` `Ord` order the generated verifier walks.
pub(crate) const fn dim_reducing_slot_index(output_type: OutputType) -> usize {
    match output_type {
        OutputType::PermutationProduct => 0,
        OutputType::Lookup16Bits => 1,
        OutputType::LookupTimestamps => 2,
        OutputType::GenericLookup => 3,
        OutputType::InitsAndTeardownsProduct => 4,
    }
}

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

/// Host-side plan for one enabled slot: its 2 input and 2 output addresses, and
/// the batch-challenge table index carried by each output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct GpuGKRDimensionReducingSlotPlan {
    pub(crate) inputs: [GKRAddress; GKR_DIM_REDUCING_INPUTS_PER_SLOT],
    pub(crate) outputs: [GKRAddress; GKR_DIM_REDUCING_OUTPUTS_PER_SLOT],
    pub(crate) batch_exp: [u16; GKR_DIM_REDUCING_OUTPUTS_PER_SLOT],
}

/// The fixed slot table for one dim-reducing layer. `None` means the circuit
/// does not use that output type.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct GpuGKRDimensionReducingLayerSlots {
    pub(crate) slots: [Option<GpuGKRDimensionReducingSlotPlan>; GKR_DIM_REDUCING_SLOTS],
}

impl GpuGKRDimensionReducingLayerSlots {
    pub(crate) fn enabled_mask(&self) -> u32 {
        self.slots
            .iter()
            .enumerate()
            .filter(|(_, slot)| slot.is_some())
            .fold(0u32, |mask, (idx, _)| mask | (1u32 << idx))
    }

    /// Enabled slots in wire order, paired with their slot index.
    pub(crate) fn iter_enabled(
        &self,
    ) -> impl Iterator<Item = (usize, &GpuGKRDimensionReducingSlotPlan)> {
        self.slots
            .iter()
            .enumerate()
            .filter_map(|(idx, slot)| slot.as_ref().map(|slot| (idx, slot)))
    }

    /// Every input address read by this layer, in wire order.
    pub(crate) fn input_addresses(&self) -> impl Iterator<Item = GKRAddress> + '_ {
        self.iter_enabled()
            .flat_map(|(_, slot)| slot.inputs.iter().copied())
    }
}

#[doc(hidden)]
pub(crate) struct GpuGKRDimensionReducingSumcheckLayerPlan {
    pub layer_idx: usize,
    pub(crate) trace_len_after_reduction: usize,
    pub(crate) folding_steps: usize,
    pub(crate) layer_slots: GpuGKRDimensionReducingLayerSlots,
    pub(crate) folding_addresses: Vec<GKRAddress>,
    pub(crate) round0_batch_template_compact: GpuGKRDimensionReducingBatch<E4>,
    /// Preparation-only owner for the future complete DR window chain. The
    /// Task 6 scheduler deliberately leaves this hook untouched and executes
    /// the accepted legacy per-round layer.
    #[allow(dead_code)]
    pub(crate) dr_window: Option<crate::backward::window_dr::DrWindowLayerCompositionHook>,
    pub(crate) round_scratch: GpuGKRDimensionReducingRoundScratch,
    /// Strict 3-slot eq-sizes descriptor. Initialised at layer start from
    /// `make_eq_sizes(folding_steps - 1)`, updated between sumcheck rounds,
    /// and passed by value into the dim-reducing consumer kernel arguments.
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
