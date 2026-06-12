//! Stage-3 GKR eval-ISA bench harness
//! (spec: .agents/specs/2026-06-12-gkr-eval-isa-stage3-cuda-bench-design.md).
//!
//! Compiled ONLY under `cfg(all(test, feature = "bench"))`. Both gates are
//! required: plain `cargo test -p circuit_prover` must not reference
//! `ab_gkr_bench_*` symbols (the bench `.cu` is only compiled into
//! `circuit_prover_native` under `-DAB_GKR_BENCH=ON`, so a plain `cfg(test)`
//! extern would fail to link), and a feature-gated non-test module could not
//! see dev-dependencies.

mod lower;
mod tests;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::cuda_struct_and_stub;

use crate::primitives::field::BF;
use crate::prover::ProverContext;

pub(crate) const BENCH_INTERP_THREADS_PER_BLOCK: u32 = 128;

/// LDC program capacity in u16 lanes (28KB of the 64KB `__constant__` budget;
/// must match `ab_gkr_bench_program` in `native/bench/gkr_fwd_interp.cu`).
pub(crate) const BENCH_INTERP_PROGRAM_LDC_LANES: usize = 14336;

/// Mirror of `interp_desc` in `native/bench/gkr_fwd_interp.cu` — keep the
/// two in sync field-for-field. Task 4 extends BOTH sides with the payload
/// buffer pointer + offset table.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct InterpDesc {
    /// Lane stream in global memory; ignored by the LDC variant (may be null
    /// there after `upload_bench_program_to_constant`).
    pub program_ldg: *const u16,
    /// Total lane count — the kernel asserts decode consumes exactly this.
    pub program_lanes: u32,
    pub n_instr: u32,
    /// ONE pointer table: bf source columns at `[0, n_sources_bf)`, then e4
    /// source columns (Source operand banks are separate id spaces; the
    /// kernel indexes e4 ids at `n_sources_bf + id`).
    pub sources: *const *const u8,
    pub n_sources_bf: u32,
    /// Per ORIGINAL output slot j; null = slot never written by the program.
    pub outputs: *const *mut u8,
    /// Bitset, 1 bit per output slot: buffer element width (1 = e4, 0 = bf).
    pub output_e4: *const u32,
    /// Montgomery-form bf constant table (see `lower::LoweredProgram::consts`).
    pub consts: *const BF,
    /// Per-thread bf cell-file size; dynamic smem = budget_cells * 4 * blockDim.
    pub budget_cells: u32,
    pub count: u32,
    /// Debug counter: incremented once per (NativeK instruction, active thread).
    pub native_skip: *mut u32,
    /// Debug flag: `INTERP_ERR_*` bits atomicOr'd by the kernel; 0 = clean.
    pub error_flag: *mut u32,
}

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrBenchFwdInterp,
    desc: InterpDesc,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_bench_fwd_interp_ldg_kernel(desc: InterpDesc)
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_bench_fwd_interp_ldc_kernel(desc: InterpDesc)
);

cuda_struct_and_stub! { static ab_gkr_bench_program: [u16; BENCH_INTERP_PROGRAM_LDC_LANES]; }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum InterpResidency {
    Ldg,
    Ldc,
}

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
    // defined in native/bench/gkr_fwd_interp.cu (always present when this
    // module compiles: feature `bench` <=> -DAB_GKR_BENCH=ON).
    unsafe { crate::primitives::utils::memcpy_to_symbol(&ab_gkr_bench_program, &*padded)? };
    Ok(true)
}

pub(crate) fn launch_bench_fwd_interp(
    desc: &InterpDesc,
    residency: InterpResidency,
    context: &ProverContext,
) -> CudaResult<()> {
    let grid_dim = desc.count.max(1).div_ceil(BENCH_INTERP_THREADS_PER_BLOCK);
    let dynamic_smem_bytes =
        desc.budget_cells as usize * 4 * BENCH_INTERP_THREADS_PER_BLOCK as usize;
    let config = CudaLaunchConfig::builder()
        .grid_dim(grid_dim)
        .block_dim(BENCH_INTERP_THREADS_PER_BLOCK)
        .dynamic_smem_bytes(dynamic_smem_bytes)
        .stream(context.get_exec_stream())
        .build();
    let kernel = match residency {
        InterpResidency::Ldg => ab_gkr_bench_fwd_interp_ldg_kernel,
        InterpResidency::Ldc => ab_gkr_bench_fwd_interp_ldc_kernel,
    };
    let args = GkrBenchFwdInterpArguments::new(*desc);
    GkrBenchFwdInterpFunction(kernel).launch(&config, &args)
}

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrBenchFwdInterpSmoke,
    src: *const BF,
    dst: *mut BF,
    count: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_bench_fwd_interp_smoke_kernel(
        src: *const BF,
        dst: *mut BF,
        count: u32,
    )
);

pub(crate) fn launch_bench_fwd_interp_smoke(
    src: *const BF,
    dst: *mut BF,
    count: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let grid_dim = count.max(1).div_ceil(BENCH_INTERP_THREADS_PER_BLOCK);
    let config = CudaLaunchConfig::basic(
        grid_dim,
        BENCH_INTERP_THREADS_PER_BLOCK,
        context.get_exec_stream(),
    );
    let args = GkrBenchFwdInterpSmokeArguments::new(src, dst, count);
    GkrBenchFwdInterpSmokeFunction(ab_gkr_bench_fwd_interp_smoke_kernel).launch(&config, &args)
}
