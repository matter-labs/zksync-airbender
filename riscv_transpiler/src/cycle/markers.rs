//! Cycle markers record anonymous cycle snapshots together with cumulative
//! delegation counts for one profiled execution scope.
//!
//! This module is meant for profiling of the RISC-V program runs.

use std::cell::RefCell;
use std::collections::HashMap;

use crate::vm::{Counters, ExecutionObserver, State};
use common_constants::{
    internal_features::TRANSPILER_MARKER_CSR, TimestampScalar, INITIAL_TIMESTAMP, TIMESTAMP_STEP,
};

/// An execution observer which collects the cycle markers and delegation counts
/// for the profiled execution scope.
///
/// This intended use is to specify it as a generic parameter for `Vm` and call
/// from within `CycleMarkerHooks::with(...)` scope to collect the cycle marker
/// data for the profiled execution run.
pub struct CycleMarkerHooks;

impl CycleMarkerHooks {
    /// Collect cycle markers and delegation counts that happen while `f` runs.
    ///
    /// This method enables the cycle marker data collection for the duration of `f`,
    /// so it is expected that `with` will only be used for a single profiled execution
    /// run at a time.
    pub fn with<T>(f: impl FnOnce() -> T) -> (T, CycleMarker) {
        let guard = ActiveCycleMarkerGuard::install();
        let result = f();
        let marker = guard.take();

        (result, marker)
    }
}

impl<C: Counters> ExecutionObserver<C> for CycleMarkerHooks {
    fn on_marker(state: &State<C>) {
        let cycles = {
            debug_assert!(state.timestamp >= INITIAL_TIMESTAMP);
            debug_assert_eq!(state.timestamp % TIMESTAMP_STEP, 0);
            (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP
        };
        with_active_cycle_marker_mut(|collector| {
            collector.set_cycle_counter(cycles);
            collector.add_marker();
        });
    }

    fn on_delegation(_state: &State<C>, id: u32, by: u64) {
        debug_assert_ne!(id, TRANSPILER_MARKER_CSR);
        with_active_cycle_marker_mut(|collector| collector.add_delegation_count(id, by));
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Mark {
    pub cycles: u64,
    pub delegations: HashMap<u32, u64>,
}

impl Mark {
    pub fn diff(&self, before: &Self) -> Self {
        let cycles = self.cycles - before.cycles;
        let mut delegations = HashMap::new();
        for (id, current_count) in self.delegations.iter() {
            match before.delegations.get(id) {
                Some(previous_count) => {
                    let diff = current_count - previous_count;
                    if diff != 0 {
                        delegations.insert(*id, diff);
                    }
                }
                None => {
                    delegations.insert(*id, *current_count);
                }
            }
        }

        Self {
            cycles,
            delegations,
        }
    }
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct CycleMarker {
    cycle_counter: u64,
    pub markers: Vec<Mark>,
    pub delegation_counter: HashMap<u32, u64>,
}

impl CycleMarker {
    fn new() -> Self {
        Self::default()
    }

    #[inline(always)]
    fn add_marker(&mut self) {
        // Marker instructions are profiling boundaries, not profiled work. Normalize
        // the raw VM cycle counter so `Mark::diff` reports only non-marker cycles.
        let cycles = self.cycle_counter - self.markers.len() as u64;
        self.markers.push(Mark {
            cycles,
            delegations: self.delegation_counter.clone(),
        });
    }

    #[inline(always)]
    fn set_cycle_counter(&mut self, cycles: u64) {
        self.cycle_counter = cycles;
    }

    #[inline(always)]
    fn add_delegation_count(&mut self, id: u32, by: u64) {
        self.delegation_counter
            .entry(id)
            .and_modify(|count| *count += by)
            .or_insert(by);
    }
}

std::thread_local! {
  static ACTIVE_CYCLE_MARKER: RefCell<Option<CycleMarker>> = const { RefCell::new(None) };
}

fn with_active_cycle_marker_mut<T>(f: impl FnOnce(&mut CycleMarker) -> T) -> T {
    ACTIVE_CYCLE_MARKER.with(|collector| {
        let mut collector = collector.borrow_mut();
        let collector = collector.as_mut().unwrap_or_else(|| {
            panic!("CycleMarkerHooks was used outside CycleMarkerHooks::with(...)")
        });

        f(collector)
    })
}

/// This guard ensures that the thread-local storage remains in a consistent state
/// even if `CycleMarkerHooks::with(...)` panics.
struct ActiveCycleMarkerGuard;

impl ActiveCycleMarkerGuard {
    fn install() -> Self {
        ACTIVE_CYCLE_MARKER.with(|collector| {
            let mut collector = collector.borrow_mut();
            assert!(
                collector.is_none(),
                "CycleMarkerHooks::with(...) does not support nested collection scopes",
            );
            *collector = Some(CycleMarker::new());
        });

        Self
    }

    fn take(self) -> CycleMarker {
        ACTIVE_CYCLE_MARKER.with(|collector| {
            collector.borrow_mut().take().expect(
                "CycleMarkerHooks::with(...) collector unexpectedly disappeared before the scope finished",
            )
        })
    }
}

impl Drop for ActiveCycleMarkerGuard {
    fn drop(&mut self) {
        ACTIVE_CYCLE_MARKER.with(|collector| {
            *collector.borrow_mut() = None;
        });
    }
}
