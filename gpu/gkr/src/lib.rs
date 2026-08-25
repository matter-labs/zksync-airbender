#![allow(incomplete_features)]
#![cfg_attr(test, feature(allocator_api))]
#![feature(generic_const_exprs)]
#![warn(clippy::manual_div_ceil)]
#![warn(clippy::needless_pass_by_value)]
// Required by the stream-scheduled callback accessors.
#![allow(clippy::mut_from_ref)]
// The scheduling/launcher functions here take one argument per distinct
// device buffer / layout / stream input; splitting them into config structs
// would obscure the pipeline wiring for a cosmetic win (same precedent as
// gpu_hash's / gpu_ntt's / gpu_execution_prover's / gpu_trace's crate-level
// allow).
#![allow(clippy::too_many_arguments)]
// `no_cuda` gates out every GPU test body, leaving their helpers and imports dead
// by construction. That mode only ever compiles, so this is not a real finding.
#![cfg_attr(no_cuda, allow(dead_code, unused_imports))]
pub mod backward;
pub mod base_layer_claims;
pub mod forward;
pub mod gkr_ops;
#[path = "backward/main_layer/execution_plan.rs"]
pub(crate) mod main_layer_execution_plan;
mod programs;
pub mod proof_layout;
pub mod setup;
pub mod stage1;
pub(crate) mod storage;
pub(crate) mod storage_types;
pub(crate) mod support;
pub(crate) mod upstream;

pub use backward::window::tail::WindowTailArm;
pub use backward::{
    preflight_dr_tail_resources, DrTailCapacityDecision, DrTailCapacityRejection,
    DrTailKernelResources, DrTailLayerPlan, DrTailProofPlan, DrTailResourceError,
    DrTailScheduleError,
};
pub(crate) use forward::kernels::ForwardKernels;
pub(crate) use gpu_gkr_model::address_audit as gkr_address_audit;
pub(crate) use gpu_gkr_model::storage_layout;
pub(crate) use gpu_gkr_model::transform;
pub use programs::{
    DrWindowLayerProgram, DrWindowLoweringRejection, DrWindowProgramBundle, GkrPrograms,
    MainContinuationWindowLoweringRejection, MainContinuationWindowProgramBundle,
    WindowLoweringRejection, WindowProgramBundle,
};
pub(crate) use storage_types::*;
// Keep the public path `gpu_gkr::gkr_initial_inner_products` (apex proof).
pub use support::initial_inner_products as gkr_initial_inner_products;

#[cfg(test)]
gpu_core::force_serial_libtest!();
#[cfg(test)]
pub(crate) mod test_utils;

use crate::upstream::SumcheckScheduleClass;

/// Caller-selected backward-phase behaviour, threaded from the apex `prove()`
/// down to layer preparation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GkrBackwardOptions {
    /// Select the complete DR-tail megakernel chain after resource preflight.
    pub dr_tail_megakernel: bool,
    /// Request the window-3 sectioned executor for main-layer rounds 0-2. The
    /// request is honoured only for a windowed sumcheck schedule; see
    /// [`backward_execution_strategy`]. Clearing it is the escape hatch back to
    /// the per-round arm.
    pub windowed_r0: bool,
    /// Request width-3 main-layer continuation windows after the landed R0
    /// window. The library default stays off for diagnostic compatibility;
    /// the production worker enables the accepted complete chain.
    pub windowed_main_continuations: bool,
    /// Prepare the dimension-reducing windowed-R0 bundle and per-layer launch
    /// objects consumed by the complete DR-tail production chain.
    pub windowed_dr: bool,
    /// Request the width-3 dimension-reducing continuation producers after
    /// windowed R0. Preflight accepts them only as part of the complete chain
    /// with the recursive-tail consumer.
    pub windowed_dr_continuations: bool,
    pub window_tail: WindowTailArm,
}

impl Default for GkrBackwardOptions {
    fn default() -> Self {
        Self {
            dr_tail_megakernel: false,
            windowed_r0: true,
            windowed_main_continuations: false,
            windowed_dr: false,
            windowed_dr_continuations: false,
            window_tail: WindowTailArm::Split,
        }
    }
}

/// The main-layer arm one proof runs. Resolved once per proof, never per layer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BackwardExecutionStrategy {
    PerRound,
    WindowedR0,
}

/// The three inseparable stages of the complete windowed DR chain.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DrWindowChainStages {
    windowed_r0: bool,
    continuations: bool,
    recursive_tail: bool,
}

impl DrWindowChainStages {
    pub const fn new(windowed_r0: bool, continuations: bool, recursive_tail: bool) -> Self {
        Self {
            windowed_r0,
            continuations,
            recursive_tail,
        }
    }

    pub const fn windowed_r0(self) -> bool {
        self.windowed_r0
    }

    pub const fn continuations(self) -> bool {
        self.continuations
    }

    pub const fn recursive_tail(self) -> bool {
        self.recursive_tail
    }

    pub const fn any_stage(self) -> bool {
        self.windowed_r0 || self.continuations || self.recursive_tail
    }

    const fn complete(self) -> bool {
        self.windowed_r0 && self.continuations && self.recursive_tail
    }
}

/// A pure DR continuation/whole-layer preflight rejection.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DrWindowContinuationPreflightError {
    RequiresWindowedSchedule,
    BundleNotReady,
    IncompleteChain {
        windowed_r0: bool,
        continuations: bool,
        recursive_tail: bool,
    },
    MixedLegacyAndWindowed {
        windowed_r0: bool,
        continuations: bool,
        recursive_tail: bool,
    },
    UnsupportedFoldingSteps {
        folding_steps: usize,
    },
    InvalidContinuationBoundary {
        folding_steps: usize,
        start_round: usize,
    },
    InvalidContinuationSuffix {
        folding_steps: usize,
        start_round: usize,
        expected_suffix_count: usize,
        observed_suffix_count: usize,
    },
    SharedMemoryCapacity {
        required_bytes: usize,
        capacity_bytes: usize,
    },
    DeviceResourceUnavailable,
}

/// Already-observed geometry/resource values consumed by the pure capability
/// validator. Purple supplies the real device query later; this type performs
/// no CUDA call and cannot make Red's incomplete chain runnable.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DrWindowContinuationCapabilityProbe {
    folding_steps: usize,
    start_round: usize,
    suffix_count: usize,
    required_shared_memory_bytes: usize,
    shared_memory_capacity_bytes: usize,
    device_resources_available: bool,
}

impl DrWindowContinuationCapabilityProbe {
    pub const fn new(
        folding_steps: usize,
        start_round: usize,
        suffix_count: usize,
        required_shared_memory_bytes: usize,
        shared_memory_capacity_bytes: usize,
        device_resources_available: bool,
    ) -> Self {
        Self {
            folding_steps,
            start_round,
            suffix_count,
            required_shared_memory_bytes,
            shared_memory_capacity_bytes,
            device_resources_available,
        }
    }
}

/// Validate production whole-layer selection without exposing a legacy path.
/// `Ok(false)` is the default-off state and `Ok(true)` selects only the
/// complete new chain.
#[doc(hidden)]
pub fn select_dr_window_complete_chain(
    strategy: BackwardExecutionStrategy,
    stages: DrWindowChainStages,
) -> Result<bool, DrWindowContinuationPreflightError> {
    if !stages.any_stage() {
        return Ok(false);
    }
    if strategy != BackwardExecutionStrategy::WindowedR0 {
        return Err(DrWindowContinuationPreflightError::RequiresWindowedSchedule);
    }
    if !stages.complete() {
        return Err(DrWindowContinuationPreflightError::IncompleteChain {
            windowed_r0: stages.windowed_r0,
            continuations: stages.continuations,
            recursive_tail: stages.recursive_tail,
        });
    }
    Ok(true)
}

/// Validate one continuation coordinate and already-observed capacity record.
/// This is deliberately allocation- and CUDA-free so every failure remains a
/// pre-transfer decision.
#[doc(hidden)]
pub fn validate_dr_window_continuation_capability(
    probe: DrWindowContinuationCapabilityProbe,
) -> Result<(), DrWindowContinuationPreflightError> {
    if backward::window_dr::validate_dr_window_folding_steps(probe.folding_steps).is_err() {
        return Err(
            DrWindowContinuationPreflightError::UnsupportedFoldingSteps {
                folding_steps: probe.folding_steps,
            },
        );
    }
    let geometry = backward::window_dr::dr_window_continuation_pass_geometry(
        probe.folding_steps,
        probe.start_round,
    )
    .map_err(
        |_| DrWindowContinuationPreflightError::InvalidContinuationBoundary {
            folding_steps: probe.folding_steps,
            start_round: probe.start_round,
        },
    )?;
    if probe.suffix_count != geometry.challenge_count {
        return Err(
            DrWindowContinuationPreflightError::InvalidContinuationSuffix {
                folding_steps: probe.folding_steps,
                start_round: probe.start_round,
                expected_suffix_count: geometry.challenge_count,
                observed_suffix_count: probe.suffix_count,
            },
        );
    }
    if probe.required_shared_memory_bytes > probe.shared_memory_capacity_bytes {
        return Err(DrWindowContinuationPreflightError::SharedMemoryCapacity {
            required_bytes: probe.required_shared_memory_bytes,
            capacity_bytes: probe.shared_memory_capacity_bytes,
        });
    }
    if !probe.device_resources_available {
        return Err(DrWindowContinuationPreflightError::DeviceResourceUnavailable);
    }
    Ok(())
}

/// A checked main-layer continuation plan could not represent or satisfy the
/// requested geometry. Exposed for the apex preflight without exposing the
/// crate-internal plan representation.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MainTailRoundBudgetKind {
    AtLeast,
    AtMost,
}

#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MainLayerExecutionPlanError {
    ZeroTailRoundBudget,
    FoldingStepsBeforeWindowedR0 {
        folding_steps: usize,
    },
    TailBudgetCannotBeSatisfied {
        folding_steps: usize,
        tail_round_budget: MainTailRoundBudgetKind,
        budget_rounds: u8,
    },
    ArithmeticOverflow,
    PlanDoesNotFitRuntimeFields {
        window_count: usize,
        tail_start_round: usize,
    },
}

/// Returns the continuation window count selected by the legacy-tail policy.
/// This narrow query is the only plan detail the apex preflight consumes.
#[doc(hidden)]
pub fn main_continuation_window_count(
    options: GkrBackwardOptions,
    strategy: BackwardExecutionStrategy,
    folding_steps: usize,
) -> Result<u8, MainLayerExecutionPlanError> {
    main_layer_execution_plan::try_derive_main_layer_execution_plan(
        options,
        strategy,
        folding_steps,
        main_layer_execution_plan::MainTailRoundBudget::AtLeast {
            min_tail_rounds: main_layer_execution_plan::LEGACY_MAIN_TAIL_MIN_ROUNDS,
        },
    )
    .map(|plan| plan.window_count())
}

/// The selector: the windowed arm runs iff it was requested AND the prover
/// config's same-size schedule validated as [`SumcheckScheduleClass::Windowed`]
/// for the layer width. `validated_class` is `None` when the schedule failed
/// validation, which is a mismatch like any other non-windowed class.
pub fn backward_execution_strategy(
    options: GkrBackwardOptions,
    validated_class: Option<SumcheckScheduleClass>,
) -> BackwardExecutionStrategy {
    if options.windowed_r0 && validated_class == Some(SumcheckScheduleClass::Windowed) {
        BackwardExecutionStrategy::WindowedR0
    } else {
        BackwardExecutionStrategy::PerRound
    }
}

#[cfg(test)]
mod cpu_windowed_selector_tests {
    use super::*;

    fn windowed_request() -> GkrBackwardOptions {
        GkrBackwardOptions::default()
    }

    #[test]
    fn cpu_windowed_selector_takes_the_window_only_for_a_windowed_schedule() {
        assert_eq!(
            backward_execution_strategy(windowed_request(), Some(SumcheckScheduleClass::Windowed)),
            BackwardExecutionStrategy::WindowedR0
        );
        for class in [SumcheckScheduleClass::Naive, SumcheckScheduleClass::Uniskip] {
            assert_eq!(
                backward_execution_strategy(windowed_request(), Some(class)),
                BackwardExecutionStrategy::PerRound,
                "{class:?} must not take the windowed arm"
            );
        }
        assert_eq!(
            backward_execution_strategy(windowed_request(), None),
            BackwardExecutionStrategy::PerRound
        );
    }

    #[test]
    fn cpu_windowed_selector_defaults_to_the_windowed_arm() {
        let options = GkrBackwardOptions::default();
        assert!(options.windowed_r0);
        assert!(!options.windowed_main_continuations);
        assert!(!options.windowed_dr);
        assert!(!options.windowed_dr_continuations);
        assert_eq!(options.window_tail, WindowTailArm::Split);
        assert_eq!(
            backward_execution_strategy(options, Some(SumcheckScheduleClass::Windowed)),
            BackwardExecutionStrategy::WindowedR0
        );
    }

    #[test]
    fn cpu_dr_window_preparation_option_is_not_a_backward_execution_selector() {
        let enabled = GkrBackwardOptions {
            windowed_dr: true,
            windowed_dr_continuations: false,
            ..GkrBackwardOptions::default()
        };
        let disabled = GkrBackwardOptions {
            windowed_dr: false,
            ..enabled
        };
        let continuations = GkrBackwardOptions {
            windowed_dr_continuations: true,
            ..enabled
        };
        for class in [
            Some(SumcheckScheduleClass::Windowed),
            Some(SumcheckScheduleClass::Naive),
            Some(SumcheckScheduleClass::Uniskip),
            None,
        ] {
            assert_eq!(
                backward_execution_strategy(enabled, class),
                backward_execution_strategy(disabled, class),
                "DR preparation must not select a production execution arm"
            );
            assert_eq!(
                backward_execution_strategy(continuations, class),
                backward_execution_strategy(disabled, class),
                "DR continuations must not add a backward-strategy arm"
            );
        }
    }

    #[test]
    fn cpu_windowed_selector_honours_the_per_round_escape_hatch() {
        let options = GkrBackwardOptions {
            windowed_r0: false,
            windowed_dr_continuations: false,
            ..GkrBackwardOptions::default()
        };
        for class in [
            Some(SumcheckScheduleClass::Windowed),
            Some(SumcheckScheduleClass::Naive),
            Some(SumcheckScheduleClass::Uniskip),
            None,
        ] {
            assert_eq!(
                backward_execution_strategy(options, class),
                BackwardExecutionStrategy::PerRound,
                "{class:?} must stay per-round without the request"
            );
        }
    }
}
