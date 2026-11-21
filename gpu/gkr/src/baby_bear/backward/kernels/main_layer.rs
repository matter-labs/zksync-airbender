use std::collections::VecDeque;

use gpu_core::primitives::{
    context::DeviceAllocation,
    device_tracing::Range,
    field::{BF, E4},
};

use crate::{
    baby_bear::backward::kernels::shared::DeviceClaimPointAndBatching,
    backward::kernels::{launchers::GkrEqSizes, shared::ClaimBufferLayout},
    upstream::GKRAddress,
    GpuGKRStorage,
};

pub(crate) struct GpuGKRMainLayerRoundScratch {
    pub(crate) eq_low_group: DeviceAllocation<E4>,
    pub(crate) partials: DeviceAllocation<E4>,
}

/// The windowed rounds 0-2 and the bank fill that precedes them.
pub(crate) struct WindowedR0Launch {
    pub(crate) bank: crate::baby_bear::backward::window::bank::WindowCoefficientBank,
    pub(crate) window: crate::baby_bear::backward::window::r0::Launch,
}

#[doc(hidden)]
pub(crate) struct GpuGKRMainLayerSumcheckLayerPlan {
    pub layer_idx: usize,
    pub(crate) folding_steps: usize,
    pub(crate) claim_terms: Vec<(usize, GKRAddress)>,
    pub(crate) folding_evaluation_sources: Vec<crate::upstream::GKRAddress>,
    pub(crate) canonical_final_addresses: Vec<(usize, crate::upstream::GKRAddress)>,
    pub(crate) round_scratch: GpuGKRMainLayerRoundScratch,
    pub(crate) windowed_r0: WindowedR0Launch,
    pub(crate) main_continuation_bank:
        crate::baby_bear::backward::window::bank::MainContinuationCoefficientBank,
    pub(crate) main_execution_plan:
        crate::backward::main_layer::execution_plan::MainLayerExecutionPlan,
    pub(crate) main_continuation:
        crate::baby_bear::backward::main_continuation::MainContinuationWindowSequence,
    pub(crate) main_tail_program: crate::baby_bear::backward::main_tail::MainTailProgram,
    pub(crate) main_tail_launched: Option<crate::baby_bear::backward::main_tail::MainTailLaunched>,
    pub(crate) eq_sizes: GkrEqSizes,
}

// SAFETY: descriptor raw pointers are only forwarded to stream-ordered kernels.
unsafe impl Send for GpuGKRMainLayerSumcheckLayerPlan {}
unsafe impl Sync for GpuGKRMainLayerSumcheckLayerPlan {}

#[doc(hidden)]
pub(crate) struct GpuGKRMainLayerBackwardState {
    #[allow(dead_code)] // Keeps queued forward ranges alive through backward scheduling.
    pub(crate) forward_tracing_ranges: Vec<Range>,
    pub(crate) storage: GpuGKRStorage<BF, E4>,
    pub(crate) pending_layers: VecDeque<usize>,
    pub(crate) trace_len: usize,
    pub(crate) inits_and_teardowns_top_bits: Vec<u32>,
    pub(crate) programs: std::sync::Arc<crate::baby_bear::GkrPrograms>,
}

#[doc(hidden)]
pub(crate) struct GpuGKRMainLayerScheduledLayerExecution {
    #[allow(dead_code)] // Keeps queued NVTX host callbacks alive until the stream consumes them.
    pub(crate) tracing_ranges: Vec<Range>,
    /// Device-resident Fiat-Shamir seed (see dim-reducing twin). Taken by the
    /// orchestrator to thread into the next backward layer.
    pub(crate) device_seed: Option<DeviceAllocation<u32>>,
    /// Device-resident `[claim_point || batching_challenge]` for the NEXT
    /// backward layer (see dim-reducing twin). Taken by the orchestrator.
    pub(crate) device_claim_point_for_next_layer: Option<DeviceClaimPointAndBatching>,
    /// Device-resident `current_claims` buffer for the NEXT backward layer.
    pub(crate) device_claims_for_next_layer: Option<DeviceAllocation<E4>>,
    /// Explicit address order of `device_claims_for_next_layer`.
    pub(crate) claim_layout_for_next_layer: Option<ClaimBufferLayout>,
}
