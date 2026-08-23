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
mod programs;
pub mod proof_layout;
pub mod setup;
pub mod stage1;
pub(crate) mod storage;
pub(crate) mod storage_types;
pub(crate) mod support;
pub(crate) mod upstream;

pub use backward::window::tail::WindowTailArm;
pub(crate) use forward::kernels::ForwardKernels;
pub(crate) use gpu_gkr_model::address_audit as gkr_address_audit;
pub(crate) use gpu_gkr_model::storage_layout;
pub(crate) use gpu_gkr_model::transform;
pub use programs::{
    DrWindowLayerProgram, DrWindowLoweringRejection, DrWindowProgramBundle, GkrPrograms,
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
    /// Request the window-3 sectioned executor for main-layer rounds 0-2. The
    /// request is honoured only for a windowed sumcheck schedule; see
    /// [`backward_execution_strategy`]. Clearing it is the escape hatch back to
    /// the per-round arm.
    pub windowed_r0: bool,
    pub window_tail: WindowTailArm,
}

impl Default for GkrBackwardOptions {
    fn default() -> Self {
        Self {
            windowed_r0: true,
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
        assert_eq!(options.window_tail, WindowTailArm::Split);
        assert_eq!(
            backward_execution_strategy(options, Some(SumcheckScheduleClass::Windowed)),
            BackwardExecutionStrategy::WindowedR0
        );
    }

    #[test]
    fn cpu_windowed_selector_honours_the_per_round_escape_hatch() {
        let options = GkrBackwardOptions {
            windowed_r0: false,
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
