use std::ffi::c_void;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::cudaGetSymbolAddress;

use super::super::super::{
    GpuExtensionFieldPolyContinuingLaunchDescriptor, GpuExtensionFieldPolyInitialSource,
};
use super::encoding::{
    GpuGKRDimensionReducingContinuationBatchCompact, GpuGKRDimensionReducingRound0BatchCompact,
};
use crate::primitives::context::ProverContext;
use crate::primitives::field::{BF, E4};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use crate::upstream::Field;

pub(crate) const GKR_DIM_REDUCING_THREADS_PER_BLOCK: u32 = WARP_SIZE * 4;
pub(crate) const GKR_TRACE_HOLDER_PARTIALS_THREADS_PER_BLOCK: u32 = 512;
pub(crate) const GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK: usize = 4;
pub(crate) const GKR_EQ_GROUP_SIZE: usize = 8;
pub(crate) const GKR_EQ_GROUP_TABLE_LEN: usize = 1 << GKR_EQ_GROUP_SIZE;
// Number of warp-uniform high slabs in the strict 3-slot eq layout.
// Mirrors `GKR_EQ_HIGH_SLOTS` in
// `gpu_prover/native/prover/gkr/support/descriptors.cuh`.
pub(crate) const GKR_EQ_HIGH_SLOTS: usize = 2;

/// Rust-side mirror of the CUDA `gkr_eq_sizes` struct in
/// `gpu_prover/native/prover/gkr/support/descriptors.cuh`. Holds per-slot bit
/// widths for the strict 3-slot eq layout `[high[0], high[1], low]`. Field
/// types and layout MUST match the CUDA side (`unsigned high[2]; unsigned low`).
#[repr(C)]
#[derive(Copy, Clone, Debug, Default)]
pub(crate) struct GkrEqSizes {
    pub(crate) high: [u32; GKR_EQ_HIGH_SLOTS],
    pub(crate) low: u32,
}

const _: () = assert!(std::mem::size_of::<GkrEqSizes>() == 12);

impl GkrEqSizes {
    /// Zero-initialised descriptor; used as the `Default` impl for the compact
    /// batch structs before the scheduler fills in the real sizes from
    /// [`make_eq_sizes`].
    pub(crate) const fn zeroed() -> Self {
        Self {
            high: [0; GKR_EQ_HIGH_SLOTS],
            low: 0,
        }
    }
}

/// Builds the strict 3-slot eq-sizes descriptor for a fresh factored-eq
/// build. Mirrors the build kernel's natural grouping: top groups go to
/// `high[0..]` (size 8 each until the last group), the last group goes to
/// `low`. For small `challenge_count`, unused high slots have size 0 and
/// the inline-eq reads slot[0] (the build kernel writes `E::ONE()` there
/// as a sentinel).
pub(crate) fn make_eq_sizes(challenge_count: usize) -> GkrEqSizes {
    let g_count = eq_group_count(challenge_count);
    let mut high = [0u32; GKR_EQ_HIGH_SLOTS];
    let mut low: u32 = 0;
    let mut consumed = 0usize;
    let mut high_idx = 0usize;
    for g in 0..g_count {
        let remaining = challenge_count - consumed;
        let g_size = remaining.min(GKR_EQ_GROUP_SIZE) as u32;
        if g + 1 == g_count {
            low = g_size;
        } else {
            assert!(high_idx < GKR_EQ_HIGH_SLOTS);
            high[high_idx] = g_size;
            high_idx += 1;
        }
        consumed += g_size as usize;
    }
    GkrEqSizes { high, low }
}

extern "C" {
    static ab_gkr_eq_high: [[E4; GKR_EQ_GROUP_TABLE_LEN]; GKR_EQ_HIGH_SLOTS];
}

/// Returns the device pointer to the `__constant__` `ab_gkr_eq_high`
/// symbol — a single contiguous block of
/// `GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN` E4 elements. Used by the
/// build / fold launchers (which need a writable device pointer through
/// `cudaGetSymbolAddress`) and by consumer kernels via the inline-eq
/// helper.
pub(crate) fn get_eq_high_constant_device_ptr() -> *mut E4 {
    let mut ptr: *mut c_void = std::ptr::null_mut();
    unsafe { cudaGetSymbolAddress(&mut ptr, &ab_gkr_eq_high as *const _ as *const c_void) }
        .wrap()
        .expect("cudaGetSymbolAddress failed for ab_gkr_eq_high");
    ptr as *mut E4
}

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingPairwiseRound0<T>,
    inputs: *const GpuExtensionFieldPolyInitialSource<T>,
    outputs: *const GpuExtensionFieldPolyInitialSource<T>,
    batch_challenges: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingLookupRound0<T>,
    inputs: *const GpuExtensionFieldPolyInitialSource<T>,
    outputs: *const GpuExtensionFieldPolyInitialSource<T>,
    batch_challenges: *const T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingPairwiseContinuation<T>,
    inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<T>,
    folding_challenge: *const T,
    batch_challenges: *const T,
    explicit_form: bool,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingLookupContinuation<T>,
    inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<T>,
    folding_challenge: *const T,
    batch_challenges: *const T,
    explicit_form: bool,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingBuildEqGroupTablesFromPairs<T>,
    eq_pair_values: *const T,
    challenge_count: u32,
    eq_group_tables: *mut T,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingBuildEqGroupTablesFromPoint<T>,
    claim_point: *const T,
    challenge_offset: u32,
    challenge_count: u32,
    eq_group_tables: *mut T,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingBuildEqHighLowFromPoint<T>,
    claim_point: *const T,
    challenge_offset: u32,
    challenge_count: u32,
    high_slab: *mut T,
    low_buffer: *mut T,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingBuildEqValuesFromGroupTables<T>,
    eq_group_tables: *const T,
    challenge_count: u32,
    eq_values: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingFoldEqValues<T>,
    eq_values: *mut T,
    half_len: u32,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingFoldEqHighGroup<T>,
    high_slab_group_base: *mut T,
    new_g_len: u32,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingTraceHolderBlockPartials<T>,
    raw_values: *const BF,
    eq_values: *const T,
    block_partials: *mut T,
    trace_len: u32,
    column_start: u32,
    chunk_cols: u32,
    blocks_count: u32,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingRound0BatchedCompact<T>,
    batch: GpuGKRDimensionReducingRound0BatchCompact<T>,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingRound1BatchedCompact<T>,
    batch: GpuGKRDimensionReducingContinuationBatchCompact<T>,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuDimensionReducingContinuationBatchedCompact<T>,
    batch: GpuGKRDimensionReducingContinuationBatchCompact<T>,
    acc_size: u32,
    step: u32,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKREqInlineMaterializeForTest<T>,
    eq_low: *const T,
    sizes: GkrEqSizes,
    eq_values: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_pairwise_round0_e4_kernel(
        inputs: *const GpuExtensionFieldPolyInitialSource<E4>,
        outputs: *const GpuExtensionFieldPolyInitialSource<E4>,
        batch_challenges: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_lookup_round0_e4_kernel(
        inputs: *const GpuExtensionFieldPolyInitialSource<E4>,
        outputs: *const GpuExtensionFieldPolyInitialSource<E4>,
        batch_challenges: *const E4,
        contributions: *mut E4,
        acc_size: u32,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_pairwise_continuation_e4_kernel(
        inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>,
        folding_challenge: *const E4,
        batch_challenges: *const E4,
        explicit_form: bool,
        contributions: *mut E4,
        acc_size: u32,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_lookup_continuation_e4_kernel(
        inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>,
        folding_challenge: *const E4,
        batch_challenges: *const E4,
        explicit_form: bool,
        contributions: *mut E4,
        acc_size: u32,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_build_eq_group_tables_from_pairs_e4_kernel(
        eq_pair_values: *const E4,
        challenge_count: u32,
        eq_group_tables: *mut E4,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_build_eq_group_tables_from_point_e4_kernel(
        claim_point: *const E4,
        challenge_offset: u32,
        challenge_count: u32,
        eq_group_tables: *mut E4,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_build_eq_high_low_from_point_e4_kernel(
        claim_point: *const E4,
        challenge_offset: u32,
        challenge_count: u32,
        high_slab: *mut E4,
        low_buffer: *mut E4,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_build_eq_values_from_group_tables_e4_kernel(
        eq_group_tables: *const E4,
        challenge_count: u32,
        eq_values: *mut E4,
        acc_size: u32,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_fold_eq_values_e4_kernel(
        eq_values: *mut E4,
        half_len: u32,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_fold_eq_high_group_in_place_e4_kernel(
        high_slab_group_base: *mut E4,
        new_g_len: u32,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_trace_holder_block_partials_e4_kernel(
        raw_values: *const BF,
        eq_values: *const E4,
        block_partials: *mut E4,
        trace_len: u32,
        column_start: u32,
        chunk_cols: u32,
        blocks_count: u32,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_round0_batched_compact_e4_kernel(
        batch: GpuGKRDimensionReducingRound0BatchCompact<E4>,
        acc_size: u32,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_round1_batched_compact_e4_kernel(
        batch: GpuGKRDimensionReducingContinuationBatchCompact<E4>,
        acc_size: u32,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_dim_reducing_continuation_batched_compact_e4_kernel(
        batch: GpuGKRDimensionReducingContinuationBatchCompact<E4>,
        acc_size: u32,
        step: u32,
    )
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_eq_inline_materialize_for_test_e4_kernel(
        eq_low: *const E4,
        sizes: GkrEqSizes,
        eq_values: *mut E4,
        acc_size: u32,
    )
);

/// Dispatches the fused per-round backward-sumcheck state update kernel for
/// `E4`. The wrapper is preserved so the call site in `backward.rs` can stay
/// generic over `<E: GpuKernels>` once E6 ships; today only `E4` is supported.
#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_backward_sumcheck_round_update_e4(
    reduction_output: &DeviceSlice<E4>,
    prev_claim_coord: &DeviceSlice<E4>,
    seed: &mut DeviceSlice<u32>,
    claim: &mut DeviceSlice<E4>,
    eq_prefactor: &mut DeviceSlice<E4>,
    coeffs_out: &mut DeviceSlice<E4>,
    challenge_out: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    crate::ops::blake2s::backward_sumcheck_round_update(
        reduction_output,
        prev_claim_coord,
        seed,
        claim,
        eq_prefactor,
        coeffs_out,
        challenge_out,
        stream,
    )
}

pub(crate) fn gkr_dim_reducing_launch_config(
    count: u32,
    context: &ProverContext,
) -> CudaLaunchConfig<'_> {
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(GKR_DIM_REDUCING_THREADS_PER_BLOCK, count.max(1));
    CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream())
}

pub(crate) fn gkr_trace_holder_partials_launch_config(
    blocks_count: u32,
    context: &ProverContext,
) -> CudaLaunchConfig<'_> {
    CudaLaunchConfig::basic(
        blocks_count,
        GKR_TRACE_HOLDER_PARTIALS_THREADS_PER_BLOCK,
        context.get_exec_stream(),
    )
}

pub(crate) fn launch_dim_reducing_round0_batched_compact<
    E: crate::prover::gkr::GpuKernels + Field,
>(
    batch: &GpuGKRDimensionReducingRound0BatchCompact<E>,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingRound0BatchedCompactArguments::new(*batch, acc_size as u32);
    GpuDimensionReducingRound0BatchedCompactFunction(E::ROUND0_BATCHED_COMPACT)
        .launch(&config, &args)
}

pub(crate) fn launch_dim_reducing_round1_batched_compact<
    E: crate::prover::gkr::GpuKernels + Field,
>(
    batch: &GpuGKRDimensionReducingContinuationBatchCompact<E>,
    _folding_challenge: *const E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingRound1BatchedCompactArguments::new(*batch, acc_size as u32);
    GpuDimensionReducingRound1BatchedCompactFunction(E::ROUND1_BATCHED_COMPACT)
        .launch(&config, &args)
}

pub(crate) fn launch_dim_reducing_continuation_batched_compact<
    E: crate::prover::gkr::GpuKernels + Field,
>(
    batch: &GpuGKRDimensionReducingContinuationBatchCompact<E>,
    _folding_challenge: *const E,
    acc_size: usize,
    step: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingContinuationBatchedCompactArguments::new(
        *batch,
        acc_size as u32,
        step as u32,
    );
    GpuDimensionReducingContinuationBatchedCompactFunction(E::CONTINUATION_BATCHED_COMPACT)
        .launch(&config, &args)
}

pub(crate) fn launch_build_eq_values_from_point<E: crate::prover::gkr::GpuKernels>(
    claim_point: *const E,
    challenge_offset: usize,
    challenge_count: usize,
    eq_group_tables: *mut E,
    eq_values: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(challenge_offset <= u32::MAX as usize);
    assert!(challenge_count <= u32::MAX as usize);
    assert!(acc_size <= u32::MAX as usize);
    let group_count = eq_group_count(challenge_count);
    if group_count > 0 {
        let config = CudaLaunchConfig::basic(
            group_count as u32,
            GKR_EQ_GROUP_TABLE_LEN as u32,
            context.get_exec_stream(),
        );
        let args = GpuDimensionReducingBuildEqGroupTablesFromPointArguments::new(
            claim_point,
            challenge_offset as u32,
            challenge_count as u32,
            eq_group_tables,
        );
        GpuDimensionReducingBuildEqGroupTablesFromPointFunction(
            E::BUILD_EQ_GROUP_TABLES_FROM_POINT,
        )
        .launch(&config, &args)?;
    }

    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingBuildEqValuesFromGroupTablesArguments::new(
        eq_group_tables,
        challenge_count as u32,
        eq_values,
        acc_size as u32,
    );
    GpuDimensionReducingBuildEqValuesFromGroupTablesFunction(E::BUILD_EQ_VALUES_FROM_GROUP_TABLES)
        .launch(&config, &args)
}

/// Builds the factored eq representation directly from a claim point:
/// high groups 0..(G-2) land in `high_slab` (the `__constant__`
/// `ab_gkr_eq_high` symbol, accessed via the device pointer from
/// [`get_eq_high_constant_device_ptr`]), and the last (low) group lands in
/// `low_buffer`. Used by the backward GKR sumcheck factored-eq path; WHIR
/// continues to use [`launch_build_eq_values_from_point`] for the
/// materialized eq path.
///
/// The grid is sized `max(groups_count, GKR_EQ_HIGH_SLOTS)` so that thread 0
/// of every block initializes its high slot's `[0]` entry to `E::ONE()` —
/// degenerate slots (small `challenge_count`) need this sentinel because
/// the inline-eq read is unconditional.
pub(crate) fn launch_build_eq_high_and_low_groups_from_point<E: crate::prover::gkr::GpuKernels>(
    claim_point: *const E,
    challenge_offset: usize,
    challenge_count: usize,
    high_slab: *mut E,
    low_buffer: *mut E,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(challenge_offset <= u32::MAX as usize);
    assert!(challenge_count <= u32::MAX as usize);
    let group_count = eq_group_count(challenge_count);
    let block_count = group_count.max(GKR_EQ_HIGH_SLOTS);
    if block_count == 0 {
        return Ok(());
    }
    let config = CudaLaunchConfig::basic(
        block_count as u32,
        GKR_EQ_GROUP_TABLE_LEN as u32,
        context.get_exec_stream(),
    );
    let args = GpuDimensionReducingBuildEqHighLowFromPointArguments::new(
        claim_point,
        challenge_offset as u32,
        challenge_count as u32,
        high_slab,
        low_buffer,
    );
    GpuDimensionReducingBuildEqHighLowFromPointFunction(E::BUILD_EQ_HIGH_LOW_FROM_POINT)
        .launch(&config, &args)
}

/// Test-only launcher that materializes a dense `eq_values[0..acc_size]`
/// buffer by calling the inline-eq device helper for each `gid`. Used by
/// parity tests to compare the factored representation against the CPU
/// ground truth. The high slabs are read from the `ab_gkr_eq_high`
/// `__constant__` symbol — the caller must have populated it via the
/// build path before calling this launcher.
#[cfg(test)]
pub(crate) fn launch_materialize_eq_from_factored_for_test<E: crate::prover::gkr::GpuKernels>(
    eq_low: *const E,
    sizes: &GkrEqSizes,
    eq_values: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(acc_size <= u32::MAX as usize);
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args =
        GpuGKREqInlineMaterializeForTestArguments::new(eq_low, *sizes, eq_values, acc_size as u32);
    GpuGKREqInlineMaterializeForTestFunction(E::EQ_INLINE_MATERIALIZE_FOR_TEST)
        .launch(&config, &args)
}

pub(crate) fn round0_eq_pair_values_len(folding_steps: usize) -> usize {
    2 * folding_steps.saturating_sub(1)
}

pub(crate) fn eq_group_count(challenge_count: usize) -> usize {
    challenge_count.div_ceil(GKR_EQ_GROUP_SIZE)
}

pub(crate) fn eq_group_tables_len(challenge_count: usize) -> usize {
    eq_group_count(challenge_count) * GKR_EQ_GROUP_TABLE_LEN
}

pub(crate) fn round0_eq_group_tables_len(folding_steps: usize) -> usize {
    eq_group_tables_len(folding_steps.saturating_sub(1))
}

#[cfg(test)]
pub(crate) fn launch_fold_eq_values_in_place<E: crate::prover::gkr::GpuKernels>(
    eq_values: *mut E,
    half_len: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(half_len <= u32::MAX as usize);
    let config = gkr_dim_reducing_launch_config(half_len as u32, context);
    let args = GpuDimensionReducingFoldEqValuesArguments::new(eq_values, half_len as u32);
    GpuDimensionReducingFoldEqValuesFunction(E::FOLD_EQ_VALUES).launch(&config, &args)
}

/// Halves the slot whose base pointer is supplied, in place. After the call
/// the top half is summed into the bottom half. `g_size_before` is the slot's
/// bit-count BEFORE the fold (must be >= 1); after the call its size is
/// `g_size_before - 1`. When `g_size_before == 1` the result is the eq
/// identity sum (`E::ONE()`) sitting at index 0.
pub(crate) fn launch_fold_eq_slot_in_place<E: crate::prover::gkr::GpuKernels>(
    slot_base: *mut E,
    g_size_before: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(g_size_before >= 1);
    assert!(g_size_before <= GKR_EQ_GROUP_SIZE);
    let new_g_len = 1u32 << (g_size_before - 1);
    // One block, up to GKR_EQ_GROUP_TABLE_LEN / 2 = 128 threads. The largest
    // fold has 128 active threads, well under occupancy limits.
    let config = CudaLaunchConfig::basic(1, new_g_len, context.get_exec_stream());
    let args = GpuDimensionReducingFoldEqHighGroupArguments::new(slot_base, new_g_len);
    GpuDimensionReducingFoldEqHighGroupFunction(E::FOLD_EQ_HIGH_GROUP_IN_PLACE)
        .launch(&config, &args)
}

/// Halves the high slab slot `slot` (0..GKR_EQ_HIGH_SLOTS) of the
/// `ab_gkr_eq_high` `__constant__` symbol in place. Looks up the symbol's
/// device address via `cudaGetSymbolAddress` and offsets to the slot base.
pub(crate) fn launch_fold_eq_high_in_constant<E: crate::prover::gkr::GpuKernels>(
    slot: usize,
    g_size_before: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(slot < GKR_EQ_HIGH_SLOTS);
    let base = get_eq_high_constant_device_ptr();
    let slot_offset = slot * GKR_EQ_GROUP_TABLE_LEN;
    // SAFETY: ab_gkr_eq_high has GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN
    // elements; `slot < GKR_EQ_HIGH_SLOTS` keeps the offset in bounds.
    let slot_base = unsafe { (base as *mut E).add(slot_offset) };
    launch_fold_eq_slot_in_place::<E>(slot_base, g_size_before, context)
}

/// Folds the factored eq representation by one bit. With the strict 3-slot
/// layout, we fold `high[0]` first, then `high[1]`, then `low`. High slabs
/// live in the `ab_gkr_eq_high` `__constant__` symbol — the launcher writes
/// through the device pointer obtained from `cudaGetSymbolAddress`. The low
/// slab lives in global memory; the caller passes its pointer.
pub(crate) fn fold_factored_eq_one_round<E: crate::prover::gkr::GpuKernels>(
    eq_sizes: &mut GkrEqSizes,
    eq_low: *mut E,
    context: &ProverContext,
) -> CudaResult<()> {
    if eq_sizes.high[0] > 0 {
        let g_size_before = eq_sizes.high[0] as usize;
        launch_fold_eq_high_in_constant::<E>(0, g_size_before, context)?;
        eq_sizes.high[0] -= 1;
    } else if eq_sizes.high[1] > 0 {
        let g_size_before = eq_sizes.high[1] as usize;
        launch_fold_eq_high_in_constant::<E>(1, g_size_before, context)?;
        eq_sizes.high[1] -= 1;
    } else {
        let g_size_before = eq_sizes.low as usize;
        debug_assert!(g_size_before >= 1);
        launch_fold_eq_slot_in_place::<E>(eq_low, g_size_before, context)?;
        eq_sizes.low -= 1;
    }
    Ok(())
}

pub(crate) fn launch_trace_holder_block_partials<E: crate::prover::gkr::GpuKernels>(
    raw_values: *const BF,
    eq_values: *const E,
    block_partials: *mut E,
    trace_len: usize,
    column_start: usize,
    chunk_cols: usize,
    blocks_count: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(trace_len <= u32::MAX as usize);
    assert!(column_start <= u32::MAX as usize);
    assert!(chunk_cols <= u32::MAX as usize);
    assert!(blocks_count <= u32::MAX as usize);
    let config = gkr_trace_holder_partials_launch_config(blocks_count as u32, context);
    let args = GpuDimensionReducingTraceHolderBlockPartialsArguments::new(
        raw_values,
        eq_values,
        block_partials,
        trace_len as u32,
        column_start as u32,
        chunk_cols as u32,
        blocks_count as u32,
    );

    GpuDimensionReducingTraceHolderBlockPartialsFunction(E::TRACE_HOLDER_BLOCK_PARTIALS)
        .launch(&config, &args)
}

#[cfg(test)]
pub(crate) fn launch_pairwise_round0<E: crate::prover::gkr::GpuKernels>(
    descriptors: &crate::prover::gkr::GpuSumcheckRound0ScheduledLaunchDescriptors<impl Sized, E>,
    batch_challenges: *const E,
    contributions: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let inputs = descriptors.device.extension_field_inputs.as_ptr();
    let outputs = descriptors.device.extension_field_outputs.as_ptr();
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingPairwiseRound0Arguments::new(
        inputs,
        outputs,
        batch_challenges,
        contributions,
        acc_size as u32,
    );

    GpuDimensionReducingPairwiseRound0Function(E::PAIRWISE_ROUND0).launch(&config, &args)
}

#[cfg(test)]
pub(crate) fn launch_lookup_round0<E: crate::prover::gkr::GpuKernels>(
    descriptors: &crate::prover::gkr::GpuSumcheckRound0ScheduledLaunchDescriptors<impl Sized, E>,
    batch_challenges: *const E,
    contributions: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let inputs = descriptors.device.extension_field_inputs.as_ptr();
    let outputs = descriptors.device.extension_field_outputs.as_ptr();
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingLookupRound0Arguments::new(
        inputs,
        outputs,
        batch_challenges,
        contributions,
        acc_size as u32,
    );

    GpuDimensionReducingLookupRound0Function(E::LOOKUP_ROUND0).launch(&config, &args)
}

#[cfg(test)]
pub(crate) fn launch_pairwise_continuation<E: crate::prover::gkr::GpuKernels>(
    descriptors: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<E>,
    folding_challenge: *const E,
    batch_challenges: *const E,
    explicit_form: bool,
    contributions: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingPairwiseContinuationArguments::new(
        descriptors,
        folding_challenge,
        batch_challenges,
        explicit_form,
        contributions,
        acc_size as u32,
    );

    GpuDimensionReducingPairwiseContinuationFunction(E::PAIRWISE_CONTINUATION)
        .launch(&config, &args)
}

#[cfg(test)]
pub(crate) fn launch_lookup_continuation<E: crate::prover::gkr::GpuKernels>(
    descriptors: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<E>,
    folding_challenge: *const E,
    batch_challenges: *const E,
    explicit_form: bool,
    contributions: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingLookupContinuationArguments::new(
        descriptors,
        folding_challenge,
        batch_challenges,
        explicit_form,
        contributions,
        acc_size as u32,
    );

    GpuDimensionReducingLookupContinuationFunction(E::LOOKUP_CONTINUATION).launch(&config, &args)
}

#[cfg(test)]
pub(crate) fn launch_build_round0_eq_values_from_pairs<E: crate::prover::gkr::GpuKernels>(
    eq_pair_values: *const E,
    challenge_count: usize,
    eq_group_tables: *mut E,
    eq_values: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(challenge_count <= u32::MAX as usize);
    assert!(acc_size <= u32::MAX as usize);
    let group_count = eq_group_count(challenge_count);
    if group_count > 0 {
        let config = CudaLaunchConfig::basic(
            group_count as u32,
            GKR_EQ_GROUP_TABLE_LEN as u32,
            context.get_exec_stream(),
        );
        let args = GpuDimensionReducingBuildEqGroupTablesFromPairsArguments::new(
            eq_pair_values,
            challenge_count as u32,
            eq_group_tables,
        );
        GpuDimensionReducingBuildEqGroupTablesFromPairsFunction(
            E::BUILD_EQ_GROUP_TABLES_FROM_PAIRS,
        )
        .launch(&config, &args)?;
    }

    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingBuildEqValuesFromGroupTablesArguments::new(
        eq_group_tables,
        challenge_count as u32,
        eq_values,
        acc_size as u32,
    );
    GpuDimensionReducingBuildEqValuesFromGroupTablesFunction(E::BUILD_EQ_VALUES_FROM_GROUP_TABLES)
        .launch(&config, &args)
}
