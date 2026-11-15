use std::{
    collections::{BTreeMap, VecDeque},
    ffi::c_void,
    ptr::null_mut,
};

use era_cudart::{
    result::{CudaResult, CudaResultWrap},
    slice::{DeviceSlice, DeviceVariable},
};
use era_cudart_sys::{cudaGetSymbolAddress, cuda_struct_and_stub};
use gpu_core::primitives::{
    context::DeviceAllocation,
    device_tracing::Range,
    field::{BF, E4},
};
use gpu_prover_context::ProverContext;

use crate::{
    baby_bear::backward::kernels::shared::DeviceClaimPointAndBatching,
    backward::kernels::{dim_reducing::*, shared::ClaimBufferLayout},
    upstream::{DimensionReducingInputOutput, GKRAddress, OutputType},
    GpuGKRStorage,
};

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

#[doc(hidden)]
pub(crate) struct GpuGKRDimensionReducingSumcheckLayerPlan {
    pub layer_idx: usize,
    pub(crate) folding_steps: usize,
    pub(crate) layer_slots: GpuGKRDimensionReducingLayerSlots,
    pub(crate) folding_addresses: Vec<GKRAddress>,
    pub(crate) dr_window_program: std::sync::Arc<crate::DrWindowLayerProgram>,
    pub(crate) dr_window:
        Option<crate::baby_bear::backward::window_dr::DrWindowLayerPreparationHook>,
    pub(crate) dr_tail_capacity:
        crate::baby_bear::backward::dr_tail::capacity::DrTailCapacityDecision,
    pub(crate) direct_tail_inputs:
        Option<crate::baby_bear::backward::window_dr::DrWindowRawInputKeepalive>,
    pub(crate) _partials: Option<DeviceAllocation<E4>>,
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
