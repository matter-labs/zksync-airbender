//! GPU launch glue for the GKR eval-ISA **v2** forward interpreter
//! (`native/bench/gkr_fwd_interp_v2.cu`). Mirrors the v1 `mod.rs` glue but for
//! the typed-lane v2 ABI (no NativeK payload table). Compiled only under
//! `cfg(all(test, feature = "bench"))`.

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::{cudaFuncSetAttribute, CudaFuncAttribute};

use super::{
    bench_interp_dynamic_smem_bytes, BenchThreads, InterpResidency, BENCH_INTERP_DEFAULT_SMEM_CAP,
};
use crate::primitives::field::{BF, E4};
use crate::prover::ProverContext;

/// Host mirror of `interp_desc2` in `native/bench/gkr_fwd_interp_v2.cu`. The C
/// struct is pointers + `u32` only (challenges ride a device `e4[8]` via
/// `challenge_scalars`, so there are no inline 16-byte fields to align-match).
/// Keep field order identical to the `.cu`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct InterpDesc2 {
    /// Lane stream in global memory; ignored by the LDC variant (may be null).
    pub program_ldg: *const u16,
    pub program_lanes: u32,
    pub n_instr: u32,

    /// Matrix-slot columns: `columns[col_base[slot] + col]` = device base of
    /// that column (bf 4B / e4 16B by `slot_is_e4`). Null entry for a referenced
    /// (slot,col) is a hard kernel error.
    pub columns: *const *const u8,
    pub col_base: *const u32,
    pub slot_is_e4: u32,
    pub n_matrix_slots: u32,

    pub consts: *const BF,            // LdcSub::Const, Montgomery
    pub const_challenge: *const E4,   // LdcSub::ConstChallenge; [k] = alpha^k
    pub n_const_challenge: u32,
    pub arg_challenge: *const E4,     // LdcSub::ArgChallenge raw bank
    pub n_arg_challenge: u32,
    /// e4[8]: [0] gamma, [1+role] perm_challenges (role 0..5), [7] perm_additive.
    pub challenge_scalars: *const E4,

    pub n_descs: u32,
    pub desc_kind: *const u8,
    pub desc_n: *const *const u8,
    pub desc_mapping: *const *const u32,
    pub desc_n_len: *const u32,
    pub desc_mask: *const *const BF,
    pub desc_fill_alpha: *const u32,
    pub desc_table_id: *const u32,

    /// Materialize outputs: `out_columns[out_base[slot] + col]`; null = the
    /// (slot,col) is never materialized.
    pub out_columns: *const *mut u8,
    pub out_base: *const u32,
    pub out_is_e4: u32,

    pub budget_cells: u32,
    pub count: u32,
    pub error_flag: *mut u32,
}

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrBenchFwdInterpV2,
    desc: InterpDesc2,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_bench_fwd_interp_v2_ldg_kernel(desc: InterpDesc2)
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_bench_fwd_interp_v2_ldc_kernel(desc: InterpDesc2)
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_bench_fwd_interp_v2_ldg256_kernel(desc: InterpDesc2)
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_bench_fwd_interp_v2_ldc256_kernel(desc: InterpDesc2)
);

// Static-shared-memory cell-budget sweep family (LDG, 128 threads). One symbol
// per compiled budget; `v2_static_kernel(n)` maps a budget to its symbol.
macro_rules! decl_static_v2 {
    ($($n:literal => $sym:ident),* $(,)?) => {
        $( cuda_kernel_declaration!(pub(crate) $sym(desc: InterpDesc2)); )*
        /// Static-smem kernel for cell budget `budget` (16..=64 step 4), or None.
        pub(crate) fn v2_static_kernel(budget: u32) -> Option<unsafe extern "C" fn(InterpDesc2)> {
            Some(match budget {
                $( $n => $sym, )*
                _ => return None,
            })
        }
    };
}
decl_static_v2!(
    16 => ab_gkr_bench_fwd_interp_v2_ldg_s16_kernel,
    20 => ab_gkr_bench_fwd_interp_v2_ldg_s20_kernel,
    24 => ab_gkr_bench_fwd_interp_v2_ldg_s24_kernel,
    28 => ab_gkr_bench_fwd_interp_v2_ldg_s28_kernel,
    32 => ab_gkr_bench_fwd_interp_v2_ldg_s32_kernel,
    36 => ab_gkr_bench_fwd_interp_v2_ldg_s36_kernel,
    40 => ab_gkr_bench_fwd_interp_v2_ldg_s40_kernel,
    44 => ab_gkr_bench_fwd_interp_v2_ldg_s44_kernel,
    48 => ab_gkr_bench_fwd_interp_v2_ldg_s48_kernel,
    52 => ab_gkr_bench_fwd_interp_v2_ldg_s52_kernel,
    56 => ab_gkr_bench_fwd_interp_v2_ldg_s56_kernel,
    60 => ab_gkr_bench_fwd_interp_v2_ldg_s60_kernel,
    64 => ab_gkr_bench_fwd_interp_v2_ldg_s64_kernel,
);

fn v2_kernel(
    threads: BenchThreads,
    residency: InterpResidency,
) -> unsafe extern "C" fn(InterpDesc2) {
    match (threads, residency) {
        (BenchThreads::T128, InterpResidency::Ldg) => ab_gkr_bench_fwd_interp_v2_ldg_kernel,
        (BenchThreads::T128, InterpResidency::Ldc) => ab_gkr_bench_fwd_interp_v2_ldc_kernel,
        (BenchThreads::T256, InterpResidency::Ldg) => ab_gkr_bench_fwd_interp_v2_ldg256_kernel,
        (BenchThreads::T256, InterpResidency::Ldc) => ab_gkr_bench_fwd_interp_v2_ldc256_kernel,
    }
}

/// Opt a v2 kernel into a >48 KB dynamic-smem allocation and bias its carveout
/// toward shared memory (same as the v1 `opt_in_large_smem`, replicated here
/// because that one is private to `mod.rs`).
fn v2_opt_in_large_smem(
    kernel: unsafe extern "C" fn(InterpDesc2),
    smem_bytes: usize,
) -> CudaResult<()> {
    let ptr = kernel as *const std::ffi::c_void;
    // SAFETY: `kernel` is a valid __global__ function pointer; the value is the
    // dynamic-smem byte count the launch will request.
    unsafe {
        cudaFuncSetAttribute(ptr, CudaFuncAttribute::MaxDynamicSharedMemorySize, smem_bytes as i32)
    }
    .wrap()?;
    crate::primitives::utils::set_shared_carveout(ptr, 100);
    Ok(())
}

/// Launch the v2 interpreter. Grid covers `desc.count` rows at `threads` per
/// block; dynamic smem = `budget_cells * 4 * threads` (the per-thread bf cell
/// file). Enqueues on `exec_stream`.
pub(crate) fn launch_bench_fwd_interp_v2(
    desc: &InterpDesc2,
    residency: InterpResidency,
    threads: BenchThreads,
    context: &ProverContext,
) -> CudaResult<()> {
    let tpb = threads.threads_per_block();
    let grid_dim = desc.count.max(1).div_ceil(tpb);
    let smem = bench_interp_dynamic_smem_bytes(desc.budget_cells, tpb);
    let kernel = v2_kernel(threads, residency);
    if smem > BENCH_INTERP_DEFAULT_SMEM_CAP {
        v2_opt_in_large_smem(kernel, smem)?;
    }
    let config = CudaLaunchConfig::builder()
        .grid_dim(grid_dim)
        .block_dim(tpb)
        .dynamic_smem_bytes(smem)
        .stream(context.get_exec_stream())
        .build();
    let args = GkrBenchFwdInterpV2Arguments::new(*desc);
    GkrBenchFwdInterpV2Function(kernel).launch(&config, &args)
}

/// Launch the static-shared-memory v2 interpreter for cell budget `budget_cap`
/// (one of the compiled sweep budgets, 16..=64 step 4). The cell file is a
/// compile-time `__shared__` array sized `budget_cap*128` bf, so NO dynamic smem
/// is requested — the footprint is visible to ptxas (occupancy + launch bounds).
/// LDG residency, 128 threads. Requires `desc.budget_cells <= budget_cap`.
pub(crate) fn launch_bench_fwd_interp_v2_static(
    desc: &InterpDesc2,
    budget_cap: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(
        desc.budget_cells <= budget_cap,
        "static kernel budget {budget_cap} < realized cells {}",
        desc.budget_cells
    );
    let kernel = v2_static_kernel(budget_cap)
        .unwrap_or_else(|| panic!("no static v2 kernel compiled for budget {budget_cap}"));
    let tpb = 128u32;
    let grid_dim = desc.count.max(1).div_ceil(tpb);
    let config = CudaLaunchConfig::builder()
        .grid_dim(grid_dim)
        .block_dim(tpb)
        .dynamic_smem_bytes(0)
        .stream(context.get_exec_stream())
        .build();
    let args = GkrBenchFwdInterpV2Arguments::new(*desc);
    GkrBenchFwdInterpV2Function(kernel).launch(&config, &args)
}
