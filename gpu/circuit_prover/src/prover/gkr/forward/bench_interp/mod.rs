//! Stage-3 GKR eval-ISA bench harness
//! (spec: .agents/specs/2026-06-12-gkr-eval-isa-stage3-cuda-bench-design.md).
//!
//! Compiled ONLY under `cfg(all(test, feature = "bench"))`. Both gates are
//! required: plain `cargo test -p circuit_prover` must not reference
//! `ab_gkr_bench_*` symbols (the bench `.cu` is only compiled into
//! `circuit_prover_native` under `-DAB_GKR_BENCH=ON`, so a plain `cfg(test)`
//! extern would fail to link), and a feature-gated non-test module could not
//! see dev-dependencies.

mod fixture;
pub(crate) mod harness;
mod lower;
mod report;
mod tests;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::{cudaFuncSetAttribute, cuda_struct_and_stub, CudaFuncAttribute};

use crate::primitives::field::BF;
use crate::prover::ProverContext;

pub(crate) const BENCH_INTERP_THREADS_PER_BLOCK: u32 = 128;

/// Block size for the launch-config-fairness 256-thread variant (spec §9).
pub(crate) const BENCH_INTERP_THREADS_PER_BLOCK_256: u32 = 256;

/// LDC program capacity in u16 lanes (28KB of the 64KB `__constant__` budget;
/// must match `ab_gkr_bench_program` in `native/bench/gkr_fwd_interp.cu`).
pub(crate) const BENCH_INTERP_PROGRAM_LDC_LANES: usize = 14336;

/// Mirror of `interp_desc` in `native/bench/gkr_fwd_interp.cu` — keep the
/// two in sync field-for-field.
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
    pub native_fired: *mut u32,
    /// Debug flag: `INTERP_ERR_*` bits atomicOr'd by the kernel; 0 = clean.
    pub error_flag: *mut u32,
    /// Final cell-file dump for parity tests; null in timing runs. Layout
    /// `[c * count + gid]`, `budget_cells x count` bf elements.
    pub debug_cells: *mut BF,
    /// NativeK payload table: one 16B-aligned byte buffer of variable-size
    /// tagged records (writer: `lower::lower_payloads`; reader + full ABI
    /// comment: `fire_payload` in the `.cu`). Always LDG-resident.
    pub payloads: *const u8,
    /// Per-payload-index byte offset into `payloads`.
    pub payload_offsets: *const u32,
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

cuda_kernel_declaration!(pub(crate)
    ab_gkr_bench_fwd_interp_ldg256_kernel(desc: InterpDesc)
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_bench_fwd_interp_ldc256_kernel(desc: InterpDesc)
);

cuda_struct_and_stub! { static ab_gkr_bench_program: [u16; BENCH_INTERP_PROGRAM_LDC_LANES]; }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum InterpResidency {
    Ldg,
    Ldc,
}

/// Block-size selector for the launch-config-fairness report (spec §9).
/// `T128` is flat's matched config (128 threads, the kernel's `__launch_bounds__`
/// min-blocks 4); `T256` is the interpreter's alternate config (256/2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BenchThreads {
    T128,
    T256,
}

impl BenchThreads {
    pub(crate) fn threads_per_block(self) -> u32 {
        match self {
            BenchThreads::T128 => BENCH_INTERP_THREADS_PER_BLOCK,
            BenchThreads::T256 => BENCH_INTERP_THREADS_PER_BLOCK_256,
        }
    }

    /// The kernel symbol for this (threads, residency) combination.
    fn kernel(self, residency: InterpResidency) -> unsafe extern "C" fn(InterpDesc) {
        match (self, residency) {
            (BenchThreads::T128, InterpResidency::Ldg) => ab_gkr_bench_fwd_interp_ldg_kernel,
            (BenchThreads::T128, InterpResidency::Ldc) => ab_gkr_bench_fwd_interp_ldc_kernel,
            (BenchThreads::T256, InterpResidency::Ldg) => ab_gkr_bench_fwd_interp_ldg256_kernel,
            (BenchThreads::T256, InterpResidency::Ldc) => ab_gkr_bench_fwd_interp_ldc256_kernel,
        }
    }
}

/// Per-thread dynamic-smem the interpreter cell-file needs:
/// `budget_cells * sizeof(BF) * threads_per_block`. Matches the `.cu`'s
/// `extern __shared__ bf cells[]` sizing (`smem = budget_cells * 4 *
/// blockDim.x`).
pub(crate) fn bench_interp_dynamic_smem_bytes(budget_cells: u32, threads_per_block: u32) -> usize {
    budget_cells as usize * std::mem::size_of::<BF>() * threads_per_block as usize
}

/// The default static dynamic-smem cap CUDA grants a kernel without opting in.
/// A 256-thread block at >12 cells (>48 KB) exceeds it, so the launcher opts in
/// via `cudaFuncSetAttribute(MaxDynamicSharedMemorySize)` (NTT precedent,
/// `gpu/ntt/src/ntt/dit.rs`).
pub(super) const BENCH_INTERP_DEFAULT_SMEM_CAP: usize = 48 * 1024;

/// Opt a kernel into a dynamic-smem allocation above the 48 KB default cap, then
/// (best-effort) bias its carveout toward shared memory so the request can be
/// granted. Returns the attribute-set result; a failure here (e.g.
/// `cudaErrorInvalidValue` for a request beyond `MaxSharedMemoryPerBlockOptin`)
/// surfaces to the caller rather than silently launching with the default cap.
fn opt_in_large_smem(
    kernel: unsafe extern "C" fn(InterpDesc),
    smem_bytes: usize,
) -> CudaResult<()> {
    let ptr = kernel as *const std::ffi::c_void;
    // SAFETY: `kernel` is a valid `__global__` function pointer; the attribute
    // value is the byte count the launch will request as dynamic smem.
    unsafe {
        cudaFuncSetAttribute(
            ptr,
            CudaFuncAttribute::MaxDynamicSharedMemorySize,
            smem_bytes as i32,
        )
    }
    .wrap()?;
    // Bias the SM's L1/smem split toward shared memory (100%) so a large request
    // is satisfiable. Best-effort: ignore failure (some arches reject 100%).
    crate::primitives::utils::set_shared_carveout(ptr, 100);
    Ok(())
}

/// Static blocks-per-SM the (threads, residency, budget) config achieves under
/// its padded dynamic-smem footprint — the launch-config fairness occupancy
/// number (spec §9). Opts the kernel into a large-smem cap first when the
/// footprint exceeds the 48 KB default (otherwise the occupancy query reflects
/// the un-opted-in kernel and a >48 KB request would later fail to launch).
pub(crate) fn bench_interp_blocks_per_sm(
    threads: BenchThreads,
    residency: InterpResidency,
    budget_cells: u32,
) -> CudaResult<i32> {
    let tpb = threads.threads_per_block();
    let smem = bench_interp_dynamic_smem_bytes(budget_cells, tpb);
    let kernel = threads.kernel(residency);
    if smem > BENCH_INTERP_DEFAULT_SMEM_CAP {
        opt_in_large_smem(kernel, smem)?;
    }
    era_cudart::occupancy::max_active_blocks_per_multiprocessor(
        &GkrBenchFwdInterpFunction(kernel),
        tpb as i32,
        smem,
    )
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
    threads: BenchThreads,
    context: &ProverContext,
) -> CudaResult<()> {
    let tpb = threads.threads_per_block();
    let grid_dim = desc.count.max(1).div_ceil(tpb);
    let dynamic_smem_bytes = bench_interp_dynamic_smem_bytes(desc.budget_cells, tpb);
    let kernel = threads.kernel(residency);
    // >48 KB dynamic smem (256 threads x >12 cells) needs the opt-in before the
    // launch will accept the request; idempotent for the small-budget case.
    if dynamic_smem_bytes > BENCH_INTERP_DEFAULT_SMEM_CAP {
        opt_in_large_smem(kernel, dynamic_smem_bytes)?;
    }
    let config = CudaLaunchConfig::builder()
        .grid_dim(grid_dim)
        .block_dim(tpb)
        .dynamic_smem_bytes(dynamic_smem_bytes)
        .stream(context.get_exec_stream())
        .build();
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
