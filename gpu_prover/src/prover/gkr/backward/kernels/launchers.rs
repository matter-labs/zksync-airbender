use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

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
// Maximum number of "high" (warp-uniform) eq groups consumed inline by per-
// round backward kernels. Mirrors `GKR_EQ_MAX_HIGH_GROUPS` in
// `gpu_prover/native/prover/gkr/support/descriptors.cuh`.
pub(crate) const GKR_EQ_MAX_HIGH_GROUPS: usize = 2;

/// Rust-side mirror of the CUDA `gkr_eq_layout_compact` struct in
/// `gpu_prover/native/prover/gkr/support/descriptors.cuh`. The 8-byte layout
/// and field order/types/padding MUST match the CUDA side exactly; the size
/// is guarded both there (via `static_assert(sizeof(...) == 8)`) and here
/// (via the `const _: ()` size assertion below).
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub(crate) struct GkrEqLayoutCompact {
    pub(crate) num_high_groups: u8,
    pub(crate) high_group_base_idx: u8,
    pub(crate) high_group_sizes: [u8; GKR_EQ_MAX_HIGH_GROUPS],
    pub(crate) low_group_size: u8,
    pub(crate) padding: [u8; 3],
}

const _: () = assert!(std::mem::size_of::<GkrEqLayoutCompact>() == 8);

impl GkrEqLayoutCompact {
    /// Zero-initialised descriptor; used as the `Default` impl for the compact
    /// batch structs before the scheduler fills in the real layout from
    /// [`make_eq_layout_compact`].
    pub(crate) const fn zeroed() -> Self {
        Self {
            num_high_groups: 0,
            high_group_base_idx: 0,
            high_group_sizes: [0; GKR_EQ_MAX_HIGH_GROUPS],
            low_group_size: 0,
            padding: [0; 3],
        }
    }
}

/// Builds the compact eq layout descriptor for a fresh factored-eq build
/// (groups 0..G-2 are the high groups stored in the high slab; group G-1 is
/// the low group stored in the low buffer). `high_group_base_idx` is the slab
/// slot treated as "group 0" by inline-eq consumers — always `0` for an
/// initial build, but kept here so the fold path can advance it without
/// rebuilding this descriptor.
pub(crate) fn make_eq_layout_compact(
    challenge_count: usize,
    high_group_base_idx: u8,
) -> GkrEqLayoutCompact {
    let g_count = eq_group_count(challenge_count);
    let mut high_group_sizes = [0u8; GKR_EQ_MAX_HIGH_GROUPS];
    let mut num_high_groups: u8 = 0;
    let mut low_group_size: u8 = 0;
    let mut consumed = 0usize;
    for g in 0..g_count {
        let remaining = challenge_count - consumed;
        let g_size = remaining.min(GKR_EQ_GROUP_SIZE) as u8;
        if g + 1 == g_count {
            low_group_size = g_size;
        } else {
            assert!((num_high_groups as usize) < GKR_EQ_MAX_HIGH_GROUPS);
            high_group_sizes[num_high_groups as usize] = g_size;
            num_high_groups += 1;
        }
        consumed += g_size as usize;
    }
    GkrEqLayoutCompact {
        num_high_groups,
        high_group_base_idx,
        high_group_sizes,
        low_group_size,
        padding: [0; 3],
    }
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
    high_slab: *const T,
    low_buffer: *const T,
    layout: GkrEqLayoutCompact,
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
        high_slab: *const E4,
        low_buffer: *const E4,
        layout: GkrEqLayoutCompact,
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
/// high groups 0..(G-2) land in `high_slab` (stride `GKR_EQ_GROUP_TABLE_LEN`),
/// the last (low) group lands in `low_buffer`. Used by the backward GKR
/// sumcheck factored-eq path; WHIR continues to use
/// [`launch_build_eq_values_from_point`] for the materialized eq path.
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
    if group_count == 0 {
        // challenge_count == 0; nothing to build. The consumer reads the
        // low-group's slot 0 as E::ONE — the caller is responsible for
        // ensuring either the buffer is initialized to ONE or never read.
        return Ok(());
    }
    let config = CudaLaunchConfig::basic(
        group_count as u32,
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
/// ground truth.
#[cfg(test)]
pub(crate) fn launch_materialize_eq_from_factored_for_test<E: crate::prover::gkr::GpuKernels>(
    high_slab: *const E,
    low_buffer: *const E,
    layout: &GkrEqLayoutCompact,
    eq_values: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(acc_size <= u32::MAX as usize);
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuGKREqInlineMaterializeForTestArguments::new(
        high_slab,
        low_buffer,
        *layout,
        eq_values,
        acc_size as u32,
    );
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

/// Halves the high-group slot at `high_group_base_idx` in the factored-eq
/// high slab in place. After the call the top half of the slot is summed into
/// the bottom half; the high slab logically loses one bit at that slot.
/// `g_size_before` is the slot's bit-count BEFORE the fold (must be >= 1);
/// after the call its size is `g_size_before - 1`. When `g_size_before == 1`
/// the slot becomes a single E::ONE-effective entry — callers typically bump
/// `high_group_base_idx` and decrement `num_high_groups` at that point.
pub(crate) fn launch_fold_eq_high_group_in_place<E: crate::prover::gkr::GpuKernels>(
    high_slab: *mut E,
    high_group_base_idx: usize,
    g_size_before: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(g_size_before >= 1);
    assert!(g_size_before <= GKR_EQ_GROUP_SIZE);
    let new_g_len = 1u32 << (g_size_before - 1);
    let slab_offset = high_group_base_idx
        .checked_mul(GKR_EQ_GROUP_TABLE_LEN)
        .expect("slab offset overflow");
    // SAFETY: the caller guarantees `high_slab` points at a slab with at least
    // `(high_group_base_idx + 1) * GKR_EQ_GROUP_TABLE_LEN` elements.
    let group_base = unsafe { high_slab.add(slab_offset) };
    // One block, up to GKR_EQ_GROUP_TABLE_LEN / 2 = 128 threads. Single block
    // is fine: the largest fold has 128 active threads, well under occupancy
    // limits, and a single-block launch keeps the kernel pointer-driven and
    // layer-kind agnostic.
    let config = CudaLaunchConfig::basic(1, new_g_len, context.get_exec_stream());
    let args = GpuDimensionReducingFoldEqHighGroupArguments::new(group_base, new_g_len);
    GpuDimensionReducingFoldEqHighGroupFunction(E::FOLD_EQ_HIGH_GROUP_IN_PLACE)
        .launch(&config, &args)
}

/// Folds the factored eq representation by one bit. The "active topmost" bit
/// lives in `eq_layout.high_group_sizes[0]` while `num_high_groups > 0` (slab
/// slot offset by `high_group_base_idx`), and in `low_group_size` once all
/// high groups are exhausted. The fold kernel is the same generic halving
/// (`low + high` in place) for both, so we reuse
/// `launch_fold_eq_high_group_in_place` for the low buffer with
/// `base_idx = 0`. Metadata-only transitions (compacting a fully-consumed high
/// group) require no kernel launch.
pub(crate) fn fold_factored_eq_one_round<E: crate::prover::gkr::GpuKernels>(
    eq_layout: &mut GkrEqLayoutCompact,
    eq_high_groups: *mut E,
    eq_low_group: *mut E,
    context: &ProverContext,
) -> CudaResult<()> {
    if eq_layout.num_high_groups > 0 {
        let active_slab_slot = eq_layout.high_group_base_idx as usize;
        let g_size_before = eq_layout.high_group_sizes[0] as usize;
        debug_assert!(g_size_before >= 1);
        launch_fold_eq_high_group_in_place::<E>(
            eq_high_groups,
            active_slab_slot,
            g_size_before,
            context,
        )?;
        eq_layout.high_group_sizes[0] -= 1;
        if eq_layout.high_group_sizes[0] == 0 {
            // Compact: shift sizes left by one, zero the now-vacated tail
            // slot, advance the slab base index, and shrink num_high_groups.
            for i in 0..(GKR_EQ_MAX_HIGH_GROUPS - 1) {
                eq_layout.high_group_sizes[i] = eq_layout.high_group_sizes[i + 1];
            }
            eq_layout.high_group_sizes[GKR_EQ_MAX_HIGH_GROUPS - 1] = 0;
            eq_layout.high_group_base_idx += 1;
            eq_layout.num_high_groups -= 1;
        }
    } else {
        let g_size_before = eq_layout.low_group_size as usize;
        debug_assert!(g_size_before >= 1);
        launch_fold_eq_high_group_in_place::<E>(eq_low_group, 0, g_size_before, context)?;
        eq_layout.low_group_size -= 1;
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
