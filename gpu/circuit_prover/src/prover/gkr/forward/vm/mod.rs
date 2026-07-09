//! fwd-VM v2: the production forward-VM interpreter path.
//!
//! Task 7 defined the descriptor ABI ([`desc`]), Task 8 the CUDA kernels
//! (`native/prover/gkr/forward/fwd_vm.cu`: `ab_gkr_fwd_vm_s4_kernel` release +
//! `ab_gkr_fwd_vm_validate_kernel`), Task 9 (this module level) the production
//! lowering ([`lower`]), the `__constant__` challenge-bank binding/upload, and
//! the kernel launch wrappers. Task 10 wires the launchers against the flat
//! oracle.

// Consumed by Task 10; the launchers/lowering have no production caller yet.
#[allow(dead_code)]
pub(crate) mod desc;
#[allow(dead_code)]
pub(crate) mod lower;
#[cfg(test)]
mod tests;
// GPU parity gate (Task 10). Bench-gated ONLY because its harness (the
// bench_interp CircuitFixture + compile chain) is; the kernels it launches
// are production symbols.
// `pub(crate)`: the fwd-VM A/B bench (`bench_interp::fwd_vm::tests::
// fwd_vm_ab_report`) reuses its parity gate + resolver/header plumbing.
#[cfg(all(test, feature = "bench"))]
pub(crate) mod gpu_tests;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::cuda_struct_and_stub;

use self::desc::{FwdVmDesc, CONST_CHALLENGE_CAP};
use self::lower::FwdVmLayerSetup;
use crate::primitives::field::E4;
use crate::prover::ProverContext;
use crate::upstream::Field;

/// Both fwd-VM v2 kernels are compiled for exactly 128 threads/block
/// (`__launch_bounds__(128, ...)`; the release body hard-codes 128 in its
/// smem index math).
pub(crate) const FWD_VM_THREADS_PER_BLOCK: u32 = 128;

/// The release instantiation's compile-time cell budget in bf LANES:
/// `ab_gkr_fwd_vm_s4_kernel` = 4 ext-cell buckets = 16 bf lanes (the committed
/// b16 corpus budget).
pub(crate) const FWD_VM_S4_BUDGET_LANES: u32 = 16;

// --- __constant__ challenge bank (Task 8 kernel-side symbol) -----------------
// Runtime-produced `LdcSub::ConstChallenge` values — the one legitimately
// runtime-late descriptor input. Defined in fwd_vm.cu at global namespace:
// `__device__ __constant__ e4 ab_gkr_fwd_vm_const_challenge[8]`.
cuda_struct_and_stub! { static ab_gkr_fwd_vm_const_challenge: [E4; CONST_CHALLENGE_CAP]; }

/// Upload a layer's `ConstChallenge` bank into the kernel's `__constant__`
/// symbol, STREAM-ORDERED on `exec_stream` (GPU scheduling contract: all
/// uploads and all launches that read the mutable symbol are serialized on
/// `exec_stream`; the bank is per-proof-instance state). The unused tail of
/// the 8-slot bank is zero-padded; `FwdVmDesc::n_const_challenge` carries the
/// used length for the VALIDATE kernel's bounds check.
///
/// The pageable stack-local source is safe with the async copy: CUDA stages
/// pageable host sources before returning (see
/// `gpu_core::primitives::utils::memcpy_to_symbol_async`).
#[allow(dead_code)] // consumed by Task 10
pub(crate) fn upload_const_challenges(values: &[E4], context: &ProverContext) -> CudaResult<()> {
    assert!(
        values.len() <= CONST_CHALLENGE_CAP,
        "const-challenge bank {} exceeds CONST_CHALLENGE_CAP {CONST_CHALLENGE_CAP}",
        values.len()
    );
    let padded: [E4; CONST_CHALLENGE_CAP] =
        core::array::from_fn(|i| values.get(i).copied().unwrap_or(Field::ZERO));
    // SAFETY: `ab_gkr_fwd_vm_const_challenge` is the kernel-side
    // `__constant__ e4[CONST_CHALLENGE_CAP]` symbol; `[E4; CONST_CHALLENGE_CAP]`
    // is layout-identical (16-B aligned, 16 B per element).
    unsafe {
        crate::primitives::utils::memcpy_to_symbol_async(
            &ab_gkr_fwd_vm_const_challenge,
            &padded,
            context.get_exec_stream(),
        )
    }
}

// --- kernel declarations + launch wrappers ------------------------------------

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrFwdVmRelease,
    desc: FwdVmDesc,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_fwd_vm_s4_kernel(desc: FwdVmDesc)
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrFwdVmValidate,
    desc: FwdVmDesc,
    error_flag: *mut u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_fwd_vm_validate_kernel(desc: FwdVmDesc, error_flag: *mut u32)
);

/// Launch the RELEASE fwd-VM interpreter (`ab_gkr_fwd_vm_s4_kernel`,
/// row-per-thread over `desc.count` rows, static smem — zero dynamic bytes).
/// `budget_lanes` is the layer's compiled cell budget (`CompiledLayer::
/// budget`); the s4 instantiation supports exactly [`FWD_VM_S4_BUDGET_LANES`].
/// Enqueues on `exec_stream`; the caller keeps `setup` alive until every
/// launch scheduled with it has been enqueued (it owns any `program_ldg`
/// fallback the by-value descriptor points into).
#[allow(dead_code)]
pub(crate) fn launch_fwd_vm_s4(
    setup: &FwdVmLayerSetup,
    budget_lanes: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(
        budget_lanes, FWD_VM_S4_BUDGET_LANES,
        "ab_gkr_fwd_vm_s4_kernel is instantiated for a {FWD_VM_S4_BUDGET_LANES}-lane cell \
         budget; layer compiled at {budget_lanes}"
    );
    let grid_dim = setup.desc.count.max(1).div_ceil(FWD_VM_THREADS_PER_BLOCK);
    let config = CudaLaunchConfig::builder()
        .grid_dim(grid_dim)
        .block_dim(FWD_VM_THREADS_PER_BLOCK)
        .stream(context.get_exec_stream())
        .build();
    let args = GkrFwdVmReleaseArguments::new(setup.desc);
    GkrFwdVmReleaseFunction(ab_gkr_fwd_vm_s4_kernel).launch(&config, &args)
}

/// Static blocks-per-SM of the release s4 kernel at its committed launch shape
/// (128 threads, zero dynamic smem — the compile-time `__shared__` cell file is
/// already accounted for by ptxas). Bench/report metadata.
#[allow(dead_code)]
pub(crate) fn fwd_vm_s4_blocks_per_sm() -> CudaResult<i32> {
    era_cudart::occupancy::max_active_blocks_per_multiprocessor(
        &GkrFwdVmReleaseFunction(ab_gkr_fwd_vm_s4_kernel),
        FWD_VM_THREADS_PER_BLOCK as i32,
        0,
    )
}

/// Launch the VALIDATE fwd-VM instantiation (test/parity harness only):
/// dynamic smem sized from `budget_lanes` (the kernel recovers the budget from
/// `%dynamic_smem_size` for its fail-closed cell-bounds checks) and an
/// `error_flag` device word the kernel atomicOr's `FWDVM_ERR_*` bits into.
/// Enqueues on `exec_stream`.
#[allow(dead_code)]
pub(crate) fn launch_fwd_vm_validate(
    setup: &FwdVmLayerSetup,
    budget_lanes: u32,
    error_flag: *mut u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let smem_bytes =
        budget_lanes as usize * core::mem::size_of::<u32>() * FWD_VM_THREADS_PER_BLOCK as usize;
    let grid_dim = setup.desc.count.max(1).div_ceil(FWD_VM_THREADS_PER_BLOCK);
    let config = CudaLaunchConfig::builder()
        .grid_dim(grid_dim)
        .block_dim(FWD_VM_THREADS_PER_BLOCK)
        .dynamic_smem_bytes(smem_bytes)
        .stream(context.get_exec_stream())
        .build();
    let args = GkrFwdVmValidateArguments::new(setup.desc, error_flag);
    GkrFwdVmValidateFunction(ab_gkr_fwd_vm_validate_kernel).launch(&config, &args)
}
