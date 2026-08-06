//! fwd-VM v2: the production forward-VM interpreter path.
//!
//! Task 7 defined the descriptor ABI ([`desc`]), Task 8 the CUDA kernels
//! (`native/prover/gkr/forward/fwd_vm.cu`: `ab_gkr_fwd_vm_s4_kernel` release +
//! `ab_gkr_fwd_vm_validate_kernel`), Task 9 (this module level) the production
//! lowering ([`lower`]), the `__constant__` derived-E4 bank binding/upload, and
//! the kernel launch wrappers. Task 10 wires the launchers against the flat
//! oracle.

pub(crate) mod desc;
pub(crate) mod lower;
mod output;
pub(crate) mod production_bind;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::cuda_struct_and_stub;

use self::desc::{FwdVmDesc, CONST_DERIVED_E4_CAP};
use self::lower::FwdVmLayerSetup;
use crate::upstream::Field;
use gpu_core::primitives::field::E4;
use gpu_prover_context::ProverContext;

/// Both fwd-VM v2 kernels are compiled for exactly 128 threads/block
/// (`__launch_bounds__(128, ...)`; the release body hard-codes 128 in its
/// smem index math).
pub(crate) const FWD_VM_THREADS_PER_BLOCK: u32 = 128;

/// The release instantiation's compile-time E4-bucket budget.
pub(crate) const FWD_VM_S4_BUDGET_BUCKETS: u32 = 4;

// --- __constant__ derived-E4 bank (Task 8 kernel-side symbol) ----------------
// Runtime-produced `LdcSub::ConstDerivedE4` values — the one legitimately
// runtime-late descriptor input. Defined in fwd_vm.cu at global namespace:
// `__device__ __constant__ e4 ab_gkr_fwd_vm_const_derived_e4[8]`.
cuda_struct_and_stub! { static ab_gkr_fwd_vm_const_derived_e4: [E4; CONST_DERIVED_E4_CAP]; }

/// Upload a layer's `ConstDerivedE4` bank into the kernel's `__constant__`
/// symbol, STREAM-ORDERED on `exec_stream` (GPU scheduling contract: all
/// uploads and all launches that read the mutable symbol are serialized on
/// `exec_stream`; the bank is per-proof-instance state). For a layer with a
/// decoder desc, `values` must also carry the decoder fill value at
/// `FwdVmDesc::fill_bank_idx` (appended after the real `ConstDerivedE4`
/// entries — see `lower::lower_layer_desc`'s fill contract). The unused tail
/// of the 8-slot bank is zero-padded; `FwdVmDesc::n_const_derived_e4` carries
/// the used length for the VALIDATE kernel's bounds check.
///
/// The pageable stack-local source is safe with the async copy: CUDA stages
/// pageable host sources before returning (see
/// `gpu_core::primitives::utils::memcpy_to_symbol_async`).
#[allow(dead_code)] // consumed by Task 10
pub(crate) fn upload_const_derived_e4(values: &[E4], context: &ProverContext) -> CudaResult<()> {
    assert!(
        values.len() <= CONST_DERIVED_E4_CAP,
        "const-derived-e4 bank {} exceeds CONST_DERIVED_E4_CAP {CONST_DERIVED_E4_CAP}",
        values.len()
    );
    let padded: [E4; CONST_DERIVED_E4_CAP] =
        core::array::from_fn(|i| values.get(i).copied().unwrap_or(Field::ZERO));
    // SAFETY: `ab_gkr_fwd_vm_const_derived_e4` is the kernel-side
    // `__constant__ e4[CONST_DERIVED_E4_CAP]` symbol; `[E4; CONST_DERIVED_E4_CAP]`
    // is layout-identical (16-B aligned, 16 B per element).
    unsafe {
        gpu_core::primitives::utils::memcpy_to_symbol_async(
            &ab_gkr_fwd_vm_const_derived_e4,
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
/// `budget_buckets` is the circuit's retained E4-bucket budget; the s4
/// instantiation supports exactly [`FWD_VM_S4_BUDGET_BUCKETS`].
/// Enqueues on `exec_stream`; the caller keeps `setup` alive until every
/// launch scheduled with it has been enqueued (it owns any `program_ldg`
/// fallback the by-value descriptor points into).
#[allow(dead_code)]
pub(crate) fn launch_fwd_vm_s4(
    setup: &FwdVmLayerSetup,
    budget_buckets: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(
        budget_buckets, FWD_VM_S4_BUDGET_BUCKETS,
        "ab_gkr_fwd_vm_s4_kernel is instantiated for a {FWD_VM_S4_BUDGET_BUCKETS}-bucket \
         budget; circuit compiled at {budget_buckets}"
    );
    let grid_dim = setup.desc.count.max(1).div_ceil(FWD_VM_THREADS_PER_BLOCK);
    let config = CudaLaunchConfig::builder()
        .grid_dim(grid_dim)
        .block_dim(FWD_VM_THREADS_PER_BLOCK)
        .stream(context.get_exec_stream())
        .build();
    let args = GkrFwdVmReleaseArguments::new(setup.desc);
    #[cfg(test)]
    S4_LAUNCHES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    GkrFwdVmReleaseFunction(ab_gkr_fwd_vm_s4_kernel).launch(&config, &args)
}

/// Release-kernel launch count, for gates that must prove the VM actually ran.
/// An exact count, not `> 0`: one launch does not prove that every selected
/// layer ran, and a proof can match for reasons other than the VM working.
#[cfg(test)]
static S4_LAUNCHES: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// Zero the launch counter and return a handle that reads it back.
#[cfg(test)]
pub(crate) fn count_fwd_vm_s4_launches() -> FwdVmLaunchCounter {
    S4_LAUNCHES.store(0, std::sync::atomic::Ordering::Relaxed);
    FwdVmLaunchCounter
}

#[cfg(test)]
pub(crate) struct FwdVmLaunchCounter;

#[cfg(test)]
impl FwdVmLaunchCounter {
    pub(crate) fn launches(&self) -> usize {
        S4_LAUNCHES.load(std::sync::atomic::Ordering::Relaxed)
    }
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
