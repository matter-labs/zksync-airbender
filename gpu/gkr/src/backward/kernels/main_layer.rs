use std::collections::VecDeque;

use super::super::super::GpuGKRStorage;
use super::launchers::GkrEqSizes;
use super::shared::{ClaimBufferLayout, DeviceClaimPointAndBatching};
use crate::upstream::GKRAddress;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::static_host::StaticPinnedBox;

pub(crate) struct GpuGKRMainLayerRoundScratch {
    pub(crate) eq_low_group: DeviceAllocation<E4>,
    pub(crate) partials: DeviceAllocation<E4>,
}

/// The windowed arm's rounds 0-2: the window producer plus the bank fill that
/// must precede it and the tail arm that consumes its partial tensor.
pub(crate) struct WindowedR0Launch {
    pub(crate) bank: super::super::vm::production_bind::BwdVmWindowBank,
    pub(crate) window: super::super::window::binding::WindowLaunch,
    pub(crate) tail_arm: crate::WindowTailArm,
}

/// How a prepared layer plays main-layer rounds 0-2. Selected once per proof by
/// [`crate::backward_execution_strategy`], bound once per layer.
pub(crate) enum MainLayerR0Binding {
    PerRound(super::super::vm::production_bind::BwdVmRound0Launch),
    Windowed(WindowedR0Launch),
}

#[doc(hidden)]
pub(crate) struct GpuGKRMainLayerSumcheckLayerPlan {
    pub layer_idx: usize,
    pub(crate) folding_steps: usize,
    pub(crate) claim_terms: Vec<(usize, GKRAddress)>,
    pub(crate) folding_evaluation_sources: Vec<crate::upstream::GKRAddress>,
    pub(crate) canonical_final_addresses: Vec<(usize, crate::upstream::GKRAddress)>,
    pub(crate) round_scratch: GpuGKRMainLayerRoundScratch,
    pub(crate) bwd_vm_r0: MainLayerR0Binding,
    pub(crate) bwd_vm_ext: super::super::vm::production_bind::BwdVmExtLaunch,
    pub(crate) main_execution_plan:
        super::super::main_layer::execution_plan::MainLayerExecutionPlan,
    pub(crate) main_continuation: super::super::main_continuation::MainContinuationWindowSequence,
    pub(crate) main_tail_program: Option<super::super::main_tail::MainTailProgram>,
    pub(crate) main_tail_launched: Option<super::super::main_tail::MainTailLaunched>,
    pub(crate) main_chain_selected: bool,
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
    pub(crate) strategy: crate::BackwardExecutionStrategy,
    pub(crate) window_tail: crate::WindowTailArm,
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
    /// Coefficient-blob host staging, moved out of the layer plan so it outlives
    /// the async H2D copies that read it.
    #[allow(dead_code)]
    pub(crate) coeff_bank_staging: Vec<StaticPinnedBox<u8>>,
    /// Pointer-free final continuation Eq boundary. The isolated Task 6 arm
    /// adopts the publication into legacy; Blue may consume this witness when
    /// replacing that remainder with main-mega.
    #[allow(dead_code)]
    pub(crate) main_continuation_eq_boundary:
        Option<super::super::main_layer::execution_plan::MainEqBoundaryWitness>,
    /// Test-only ownership keeps the terminal recurrence state live for the
    /// full-layer option-off/option-on byte comparison.
    #[cfg(test)]
    pub(crate) device_final_claim_for_test: Option<DeviceAllocation<E4>>,
    #[cfg(test)]
    pub(crate) device_final_eq_prefactor_for_test: Option<DeviceAllocation<E4>>,
}
