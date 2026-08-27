use std::collections::VecDeque;

use super::super::super::GpuGKRStorage;
use super::launchers::GkrEqSizes;
use super::shared::{ClaimBufferLayout, DeviceClaimPointAndBatching};
use crate::upstream::GKRAddress;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};

pub(crate) struct GpuGKRMainLayerRoundScratch {
    pub(crate) eq_low_group: DeviceAllocation<E4>,
    pub(crate) partials: DeviceAllocation<E4>,
}

/// The windowed rounds 0-2 and the bank fill that precedes them.
pub(crate) struct WindowedR0Launch {
    pub(crate) bank: super::super::window::bank::WindowCoefficientBank,
    pub(crate) window: super::super::window::binding::WindowLaunch,
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
    pub(crate) main_continuation_bank: super::super::window::bank::MainContinuationCoefficientBank,
    pub(crate) main_execution_plan:
        super::super::main_layer::execution_plan::MainLayerExecutionPlan,
    pub(crate) main_continuation: super::super::main_continuation::MainContinuationWindowSequence,
    pub(crate) main_tail_program: super::super::main_tail::MainTailProgram,
    pub(crate) main_tail_launched: Option<super::super::main_tail::MainTailLaunched>,
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
    pub(crate) programs: std::sync::Arc<crate::GkrPrograms>,
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
