mod abi;
#[cfg(not(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
)))]
#[allow(dead_code)] // Task 6 schedules the launch-ready Task 5 surface.
mod binding;
#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
#[path = "binding.rs"]
mod binding_impl;
#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
mod binding {
    use std::cell::Cell;

    use era_cudart::result::CudaResult;
    use gpu_prover_context::ProverContext;

    pub(crate) use super::binding_impl::{
        bind_first_main_continuation_window, bind_later_main_continuation_window,
        MainContinuationWindowBindError, MainContinuationWindowLaunchBinding,
        MainContinuationWindowLaunched, MainContinuationWindowRuntimeScratch,
    };

    thread_local! {
        static ACTIVE_TASK8_LAUNCH_COUNT: Cell<Option<usize>> = const { Cell::new(None) };
    }

    /// Scoped counter around one production main-layer schedule. The actual
    /// enqueue wrapper below is the only increment site.
    pub(crate) struct Task8MainContinuationLaunchCounterGuard {
        active: bool,
    }

    impl Task8MainContinuationLaunchCounterGuard {
        pub(crate) fn install() -> Self {
            ACTIVE_TASK8_LAUNCH_COUNT.with(|counter| {
                assert!(
                    counter.replace(Some(0)).is_none(),
                    "Task 8 continuation launch counter cannot be nested"
                );
            });
            Self { active: true }
        }

        pub(crate) fn finish(mut self) -> usize {
            let launches = ACTIVE_TASK8_LAUNCH_COUNT.with(|counter| {
                counter
                    .replace(None)
                    .expect("Task 8 continuation launch counter was not active")
            });
            self.active = false;
            launches
        }
    }

    impl Drop for Task8MainContinuationLaunchCounterGuard {
        fn drop(&mut self) {
            if self.active {
                ACTIVE_TASK8_LAUNCH_COUNT.with(|counter| {
                    assert!(
                        counter.replace(None).is_some(),
                        "Task 8 continuation launch counter was cleared early"
                    );
                });
            }
        }
    }

    pub(crate) fn launch_main_continuation_window(
        launch: super::binding_impl::MainContinuationWindowLaunch<'_>,
        context: &ProverContext,
    ) -> CudaResult<MainContinuationWindowLaunched> {
        let launched = super::binding_impl::launch_main_continuation_window(launch, context)?;
        ACTIVE_TASK8_LAUNCH_COUNT.with(|counter| {
            if let Some(launches) = counter.get() {
                counter.set(Some(
                    launches
                        .checked_add(1)
                        .expect("Task 8 continuation launch count overflow"),
                ));
            }
        });
        Ok(launched)
    }
}
#[allow(dead_code)] // Task 6 dispatches the generated bank through `binding`.
mod generated_registry;
mod publication;
mod reference;
mod sequence;

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
mod differential_tests;

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
pub(crate) use binding::Task8MainContinuationLaunchCounterGuard;
#[allow(unused_imports)] // Task 6 consumes this staged production seam.
pub(crate) use binding::{
    bind_first_main_continuation_window, bind_later_main_continuation_window,
    launch_main_continuation_window, MainContinuationWindowBindError,
    MainContinuationWindowLaunched, MainContinuationWindowRuntimeScratch,
};

pub(crate) use publication::{
    preserve_owned_on_validation_error, repoint_final_evaluations_from_raw,
    validate_adoption_state, validate_canonical_publication, ContinuationPublicationError,
    ContinuationPublishedLevel, ContinuationPublishedShape,
};
#[doc(hidden)]
pub use reference::{continuation_window_tensor_reference, ContinuationWindowReferenceError};
pub(crate) use sequence::MainContinuationWindowSequence;

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
pub(crate) use differential_tests::schedule_prepared_main_continuation_differential;

#[cfg(all(
    any(test, feature = "task8_continuation_differential_test"),
    not(no_cuda)
))]
#[doc(hidden)]
pub use crate::backward::stage_snapshots::{
    MainContinuationDifferentialHandle, MainContinuationDifferentialReport,
    MainContinuationExecutionCounts, MainContinuationExecutionCountsHandle,
};

#[cfg(test)]
mod cpu_tests;

#[cfg(all(test, not(no_cuda)))]
mod tests;
