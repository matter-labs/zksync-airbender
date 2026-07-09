//! fwd-VM GKR eval-ISA A/B bench harness.
//!
//! Compiled ONLY under `cfg(all(test, feature = "bench"))` (a feature-gated
//! non-test module could not see dev-dependencies). The legacy v1 bench
//! interpreter (`InterpDesc3`, launchers, LDC `__constant__` upload,
//! `native/bench/gkr_fwd_vm.cu`) is gone (Task 12) — `tests::fwd_vm_ab_report`
//! now drives the production v2 fwd-VM kernels (`super::vm`) directly. This
//! parent holds only the shared fixture, the timing primitive (`harness`),
//! and the compile chain (`fwd_vm/compile.rs`).

pub(crate) mod fixture;
pub(crate) mod fwd_vm;
pub(crate) mod harness;

/// LDC feasibility threshold (u16 lanes) used only by the host-only size
/// probe (`fwd_vm::tests::fwd_vm_circuits_compile_and_size_probe`) to report
/// whether a compiled layer's program would have fit a 28KB `__constant__`
/// array — a historical reference point from the deleted v1 bench kernel, not
/// tied to any live native symbol.
pub(crate) const BENCH_INTERP_PROGRAM_LDC_LANES: usize = 14336;
