//! fwd-VM GKR eval-ISA bench harness.
//!
//! Compiled ONLY under `cfg(all(test, feature = "bench"))`. Both gates are
//! required: plain `cargo test -p circuit_prover` must not reference
//! `ab_gkr_bench_*` symbols (the bench `.cu` is only compiled into
//! `circuit_prover_native` under `-DAB_GKR_BENCH=ON`, so a plain `cfg(test)`
//! extern would fail to link), and a feature-gated non-test module could not
//! see dev-dependencies.
//!
//! The interpreter kernels, launchers, ABI (`InterpDesc3`), lowering, and gates
//! live in `fwd_vm/`; this parent holds only the shared fixture, the timing
//! primitive (`harness`), and the LDC program-upload plumbing.

pub(crate) mod fixture;
pub(crate) mod fwd_vm;
pub(crate) mod harness;

use era_cudart::result::CudaResult;
use era_cudart_sys::cuda_struct_and_stub;

pub(crate) const BENCH_INTERP_THREADS_PER_BLOCK: u32 = 128;

/// LDC program capacity in u16 lanes (28KB of the 64KB `__constant__` budget;
/// must match `ab_gkr_bench_program` in `native/bench/gkr_fwd_vm.cu`).
pub(crate) const BENCH_INTERP_PROGRAM_LDC_LANES: usize = 14336;

/// The default static dynamic-smem cap CUDA grants a kernel without opting in.
/// The committed fwd-VM configs (128 threads, budget <= 16 cells) stay under it.
pub(super) const BENCH_INTERP_DEFAULT_SMEM_CAP: usize = 48 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum InterpResidency {
    Ldg,
    Ldc,
}

cuda_struct_and_stub! { static ab_gkr_bench_program: [u16; BENCH_INTERP_PROGRAM_LDC_LANES]; }

/// Host-side fit check + `__constant__` upload for the LDC variant. Returns
/// false (no upload) when the program exceeds the 28KB constant array.
/// Synchronous H2D — bench/test harness code only.
pub(crate) fn upload_bench_program_to_constant(lanes: &[u16]) -> CudaResult<bool> {
    if lanes.len() > BENCH_INTERP_PROGRAM_LDC_LANES {
        return Ok(false);
    }
    let mut padded = Box::new([0u16; BENCH_INTERP_PROGRAM_LDC_LANES]);
    padded[..lanes.len()].copy_from_slice(lanes);
    // SAFETY: ab_gkr_bench_program is a valid __constant__ u16[14336] symbol
    // defined in native/bench/gkr_fwd_vm.cu (always present when this module
    // compiles: feature `bench` <=> -DAB_GKR_BENCH=ON).
    unsafe { crate::primitives::utils::memcpy_to_symbol(&ab_gkr_bench_program, &*padded)? };
    Ok(true)
}
