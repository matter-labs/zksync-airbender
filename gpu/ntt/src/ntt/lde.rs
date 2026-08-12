#![allow(non_snake_case)]

use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use super::dispatch::dispatch_strategy;
use super::dit::monomials_to_evals_dit;
use super::forward::{
    monomials_to_evals_2_pass_compact_initial, monomials_to_evals_3_pass,
    monomials_to_evals_compact_1_pass, monomials_to_evals_smem_packed, monomials_to_evals_subwarp,
};
use super::kernels::*;
use super::shared;

use crate::ntt_twiddles::OMEGA_LOG_ORDER;
use gpu_core::primitives::context::DeviceProperties;
use gpu_core::primitives::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, DeviceMatrixMut,
};
use gpu_core::primitives::field::BaseField;

type BF = BaseField;

// Computes grid dimensions for high-degree LDE kernels, targeting fractional occupancy.
// num_cols_per_coset and cosets_in_tile are not required to be powers of 2.
// The resulting grid prioritizes monomial reuse, because monomials are unique gmem data.
// However, the grid is not guaranteed to yield good occupancy or load balancing
// by itself. It's meant to work with an external multistream ping-ping approach,
// where 2 grids in flight compensate for each other's tail effects.
fn get_lde_grid_dims_for_occupancy_hint(
    n: usize,
    cosets_in_tile: usize,
    num_cols_per_coset: usize,
    func: &impl KernelFunction,
    block_dim_x: usize,
    vals_per_block: usize,
    occupancy_hint_numerator: usize,
    occupancy_hint_denominator: usize,
    device_properties: &DeviceProperties,
) -> CudaResult<Dim3> {
    assert!(n >= vals_per_block);
    assert_eq!(n % vals_per_block, 0);

    let max_blocks_per_sm = era_cudart::occupancy::max_active_blocks_per_multiprocessor(
        func,
        block_dim_x as i32,
        0, // dynamic_smem_size
    )?;
    let max_blocks_per_sm = max_blocks_per_sm as usize;

    let full_occupancy = max_blocks_per_sm * device_properties.sm_count;
    let target_blocks =
        (full_occupancy * occupancy_hint_numerator).div_ceil(occupancy_hint_denominator);

    let grid_dim_x = n / vals_per_block;

    // First, if laying out blocks across n gives enough occupancy, we're done.
    if grid_dim_x >= target_blocks {
        let grid: Dim3 = (grid_dim_x as u32, 1, 1).into();
        return Ok(grid);
    }

    // Second, see if we can achieve target occupancy by parallelizing over columns
    // within each coset. Expose the parallelism via blockDim.y.
    if grid_dim_x * num_cols_per_coset >= target_blocks {
        let grid_dim_y = target_blocks.div_ceil(grid_dim_x);
        debug_assert!(grid_dim_x * grid_dim_y >= target_blocks);
        let grid = (grid_dim_x as u32, grid_dim_y as u32, 1).into();
        return Ok(grid);
    }
    // Max out parallelism over columns within each coset (prioritize monomial reuse)
    let grid_dim_y = num_cols_per_coset;

    // As a last resort, split the coset tile. Expose the parallelism via blockDim.z.
    let xy_blocks = grid_dim_x * grid_dim_y;
    let grid_dim_z = target_blocks.div_ceil(xy_blocks);
    debug_assert!(xy_blocks * grid_dim_z >= target_blocks);
    // Technically, grid_dim_z can be > cosets_in_tile without affecting correctness.
    // The grid would just include a bunch of spurious no-op blocks.
    // But it would indicate a weird, non-performant geometry we don't expect in production.
    // Demoted to debug_assert!: an aggressive occupancy hint can legitimately
    // push grid_dim_z past cosets_in_tile (seen while authoring the host-oracle
    // tests), and since correctness is unaffected this must not abort a release
    // launch.
    debug_assert!(grid_dim_z <= cosets_in_tile);
    let grid = (grid_dim_x as u32, grid_dim_y as u32, grid_dim_z as u32).into();
    Ok(grid)
}

fn get_lde_config_for_log_n(log_n: usize) -> (usize, usize) {
    let (block_dim_x, vals_per_block) = match log_n {
        18 => (512, 1024),
        17 => (256, 512),
        16 => (128, 256),
        15 => (64, 128),
        14 => (128, 256),
        _ => unimplemented!(),
    };
    (block_dim_x, vals_per_block)
}

/// Fast-path arm of [`lde_with_coset_range`] for `log_n` in `(13, 18]`
/// (`MAX_LOG_N_FOR_SINGLE_KERNEL_LDE < log_n <= 18`). Single caller.
pub(crate) fn lde_intermediate_range(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs: &mut DeviceSlice<BF>,
    log_n: usize,
    log_lde_factor: usize,
    cosets_in_tile: usize,
    coset_index_base: usize,
    num_cols_per_coset_stride: usize,
    occupancy_hint_numerator: usize,
    occupancy_hint_denominator: usize,
    device_properties: &DeviceProperties,
    stream: &CudaStream,
) -> CudaResult<()> {
    let trace_len = 1 << log_n;
    assert_eq!(inputs_matrix.rows(), trace_len);
    assert_eq!(inputs_matrix.cols(), num_cols_per_coset_stride);
    assert!(outputs.len() >= trace_len * num_cols_per_coset_stride * cosets_in_tile);
    let coset_factor_shift = (OMEGA_LOG_ORDER as usize - log_n - log_lde_factor) as u32;
    let mut outputs_matrix = DeviceMatrixMut::new(outputs, trace_len);
    let inputs_matrix = inputs_matrix.as_ptr_and_stride();
    let outputs_matrix_const = outputs_matrix.as_ptr_and_stride();
    let outputs_matrix_mut = outputs_matrix.as_mut_ptr_and_stride();
    let log_k = log_n - 8;
    let (block_dim_x, vals_per_block) = get_lde_config_for_log_n(log_n);
    let first_pass_function = match log_n {
        18 => LdeIntermediateFunction(ab_lde_first_10_stages_kernel),
        17 => LdeIntermediateFunction(ab_lde_first_9_stages_kernel),
        16 => LdeIntermediateFunction(ab_lde_first_8_stages_kernel),
        15 => LdeIntermediateFunction(ab_lde_first_7_stages_kernel),
        14 => LdeIntermediateFunction(ab_lde_first_6_stages_kernel),
        _ => unimplemented!(),
    };
    let grid_dim: Dim3 = get_lde_grid_dims_for_occupancy_hint(
        trace_len,
        cosets_in_tile,
        num_cols_per_coset_stride,
        &first_pass_function,
        block_dim_x,
        vals_per_block,
        occupancy_hint_numerator,
        occupancy_hint_denominator,
        device_properties,
    )?;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim_x as u32, stream);
    let args = LdeIntermediateArguments::new(
        inputs_matrix,
        outputs_matrix_mut,
        log_n as u32,
        shared::checked_u32(coset_index_base, "coset_index_base"),
        coset_factor_shift,
        shared::checked_u32(num_cols_per_coset_stride, "num_cols_per_coset_stride"),
        shared::checked_u32(cosets_in_tile, "cosets_in_tile"),
    );
    first_pass_function.launch(&config, &args)?;
    // Pass 2: noninitial_8 with start_stage = log_k.
    assert!(
        cosets_in_tile.is_power_of_two(),
        "cosets_in_tile must be a power of 2 (got {cosets_in_tile})"
    );
    let log_cosets_in_tile = cosets_in_tile.trailing_zeros();
    let threads_pass2 = 512;
    let bf_vals_per_block_pass2 = 1 << 13;
    let start_stage = log_k;
    let num_block_exchg_regions = trace_len >> (start_stage + 8);
    let block_exchg_region_size = 1 << (start_stage + 8);
    let blocks_per_exchg_region = block_exchg_region_size / bf_vals_per_block_pass2;
    debug_assert_eq!(
        blocks_per_exchg_region * num_block_exchg_regions,
        trace_len / bf_vals_per_block_pass2
    );
    let cols_in_chunk = num_cols_per_coset_stride;
    let grid_dim_pass2: Dim3 = (blocks_per_exchg_region as u32
        * num_block_exchg_regions as u32
        * cosets_in_tile as u32
        * cols_in_chunk as u32)
        .into();
    let config_pass2 = CudaLaunchConfig::basic(grid_dim_pass2, threads_pass2 as u32, stream);
    let args_pass2 = StridedTilesStagesArguments::new(
        outputs_matrix_const,
        outputs_matrix_mut,
        log_n as i32,
        start_stage as i32,
        shared::checked_i32(cols_in_chunk, "num_cols_per_coset_stride"),
        log_cosets_in_tile as i32,
    );
    StridedTilesStagesFunction(ab_monomials_to_evals_noninitial_8_stages_kernel)
        .launch(&config_pass2, &args_pass2)
}

/// Forward NTT from bitreversed monomials to natural-order evaluations across
/// the full multi-coset LDE.
///
/// Runs the forward NTT across the full power-of-two LDE: all
/// `num_cosets = 1 << log_lde_factor` cosets, starting at coset 0. Use
/// [`lde_with_coset_range`] to process a caller-selected power-of-two
/// coset subrange.
///
/// For the compact 1-pass range (`log_n <= 12`) all cosets are batched into one
/// launch via `gridDim.x`. For larger `log_n` (2-pass-compact-initial, 3-pass
/// forward) cosets are batched up to the L2-pressure cap from the strategy.
///
/// Output layout: coset-major outer, column-major inner. Coset k's columns
/// occupy `outputs[(k * num_cols_per_coset_stride + col) * trace_len ..]` for
/// col in `[0, inputs_matrix.cols())`. When `num_cols_per_coset_stride ==
/// inputs_matrix.cols()` (the typical case) cosets sit back-to-back; setting
/// it larger leaves gaps between cosets (used by the base-trace LDE caller
/// to write directly into a `[coset][col][trace_len]` trace-holder backing
/// where col here is a per-column NTT inside an outer column loop).
pub fn bitreversed_monomials_to_natural_evals_multi_coset(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs: &mut DeviceSlice<BF>,
    log_n: usize,
    log_lde_factor: usize,
    num_cols_per_coset_stride: usize,
    transposed_monomials: bool,
    ntt_ctx: &crate::ntt_twiddles::DeviceContext,
    d_table_scratch: Option<&mut DeviceSlice<BF>>,
    stream: &CudaStream,
    device_properties: &DeviceProperties,
) -> CudaResult<()> {
    let num_cosets = 1usize << log_lde_factor;
    dispatch_forward_multi_coset(
        inputs_matrix,
        outputs,
        log_n,
        log_lde_factor,
        num_cosets,
        0,
        num_cols_per_coset_stride,
        transposed_monomials,
        ntt_ctx,
        d_table_scratch,
        stream,
        device_properties,
    )
}

pub const MAX_LOG_N_FOR_SINGLE_KERNEL_LDE: usize = 13;

/// Multi-coset forward NTT over a caller-selected coset range.
///
/// `log_lde_factor` still describes the full LDE domain and therefore the
/// coset-factor shift. `num_cosets` is the number of local cosets written to
/// `outputs`, while `coset_index_base` is the global coset index used for the
/// first local coset's coset factor. Both caller-controlled values must be
/// powers of two, and the selected range must fit within the full LDE coset
/// domain.
pub fn lde_with_coset_range(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs: &mut DeviceSlice<BF>,
    log_n: usize,
    log_lde_factor: usize,
    num_cosets: usize,
    coset_index_base: usize,
    num_cols_per_coset_stride: usize,
    occupancy_hint_numerator: usize,
    occupancy_hint_denominator: usize,
    ntt_ctx: &crate::ntt_twiddles::DeviceContext,
    d_table_scratch: Option<&mut DeviceSlice<BF>>,
    stream: &CudaStream,
    device_properties: &DeviceProperties,
) -> CudaResult<()> {
    assert!(
        log_n + log_lde_factor <= OMEGA_LOG_ORDER as usize,
        "log_n ({log_n}) + log_lde_factor ({log_lde_factor}) > OMEGA_LOG_ORDER ({OMEGA_LOG_ORDER})",
    );
    assert!(
        num_cosets.is_power_of_two(),
        "num_cosets must be a power of 2 (got {num_cosets})"
    );
    let full_num_cosets = 1usize << log_lde_factor;
    let coset_index_end = coset_index_base
        .checked_add(num_cosets)
        .expect("coset_index_base + num_cosets overflow");
    assert!(
        coset_index_end <= full_num_cosets,
        "coset range [{coset_index_base}, {coset_index_end}) exceeds full LDE coset count {full_num_cosets}",
    );
    // TODO: extend to smaller sizes when chunking-friendly kernels are done
    if (log_n <= 18) && (log_n > MAX_LOG_N_FOR_SINGLE_KERNEL_LDE) {
        let result = lde_intermediate_range(
            inputs_matrix,
            outputs,
            log_n,
            log_lde_factor,
            num_cosets,
            coset_index_base,
            num_cols_per_coset_stride,
            occupancy_hint_numerator,
            occupancy_hint_denominator,
            device_properties,
            stream,
        );
        return result;
    }
    dispatch_forward_multi_coset(
        inputs_matrix,
        outputs,
        log_n,
        log_lde_factor,
        num_cosets,
        coset_index_base,
        num_cols_per_coset_stride,
        /*transposed_monomials=*/ false,
        ntt_ctx,
        d_table_scratch,
        stream,
        device_properties,
    )
}

/// Shared core behind both [`bitreversed_monomials_to_natural_evals_multi_coset`]
/// and [`lde_with_coset_range`]'s fallback arm: selects the forward NTT
/// strategy for `log_n` and dispatches to the matching pass-shape kernel(s).
fn dispatch_forward_multi_coset(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs: &mut DeviceSlice<BF>,
    log_n: usize,
    log_lde_factor: usize,
    num_cosets: usize,
    coset_index_base: usize,
    num_cols_per_coset_stride: usize,
    transposed_monomials: bool,
    ntt_ctx: &crate::ntt_twiddles::DeviceContext,
    d_table_scratch: Option<&mut DeviceSlice<BF>>,
    stream: &CudaStream,
    device_properties: &DeviceProperties,
) -> CudaResult<()> {
    assert!(
        log_n + log_lde_factor <= OMEGA_LOG_ORDER as usize,
        "log_n ({log_n}) + log_lde_factor ({log_lde_factor}) > OMEGA_LOG_ORDER ({OMEGA_LOG_ORDER})",
    );
    assert!(
        num_cosets.is_power_of_two(),
        "num_cosets must be a power of 2 (got {num_cosets})"
    );
    let full_num_cosets = 1usize << log_lde_factor;
    let coset_index_end = coset_index_base
        .checked_add(num_cosets)
        .expect("coset_index_base + num_cosets overflow");
    assert!(
        coset_index_end <= full_num_cosets,
        "coset range [{coset_index_base}, {coset_index_end}) exceeds full LDE coset count {full_num_cosets}",
    );
    let trace_len = 1usize << log_n;
    let num_cols = inputs_matrix.cols();
    assert!(
        num_cols_per_coset_stride >= num_cols,
        "num_cols_per_coset_stride ({num_cols_per_coset_stride}) must be >= inputs_matrix.cols() ({num_cols})",
    );
    // Highest col accessed: (num_cosets - 1) * stride + num_cols - 1; rows
    // run to trace_len. Outputs must cover this range.
    let max_col_offset_exclusive = (num_cosets - 1) * num_cols_per_coset_stride + num_cols;
    assert!(
        outputs.len() >= max_col_offset_exclusive * trace_len,
        "outputs slice has {} BFs but needs at least {} for ({}, {}, {}) cosets x stride x trace_len",
        outputs.len(),
        max_col_offset_exclusive * trace_len,
        num_cosets,
        num_cols_per_coset_stride,
        trace_len,
    );
    let strategy = super::select_ntt_strategy(
        super::NttDirection::Forward,
        log_n,
        num_cols,
        num_cosets,
        device_properties,
    )
    .unwrap_or_else(|e| unreachable!("forward strategy unavailable: {e:?}"));
    debug_assert!(!strategy.passes.is_empty());
    let coset_factor_shift = (OMEGA_LOG_ORDER as usize - log_n - log_lde_factor) as u32;
    // Compact 1-pass (log_n in [4, 12]) and 2-pass-compact-initial (log_n in
    // [13, 20]) kernel families now consume cosets_per_launch directly. Other
    // ranges fall back to a per-coset loop.
    let mut d_table_scratch = d_table_scratch;
    if strategy.passes.len() == 1 {
        let mut outputs_matrix = DeviceMatrixMut::new(outputs, trace_len);
        return match strategy.passes[0].kernel {
            super::NttKernelKind::MonomialsToEvalsDit { log_vpt, .. } => monomials_to_evals_dit(
                inputs_matrix,
                &mut outputs_matrix,
                log_n,
                log_vpt,
                coset_index_base,
                coset_factor_shift,
                num_cosets,
                num_cols_per_coset_stride,
                transposed_monomials,
                ntt_ctx,
                d_table_scratch.as_deref_mut().expect(
                    "DIT range requires a d_table_scratch (len >= N); caller must \
                     provide one for log_n in [2,13]",
                ),
                stream,
                device_properties,
            ),
            super::NttKernelKind::MonomialsToEvalsSubwarp {
                log_instances_per_block,
                ..
            } => {
                // Precondition guard restored after the dead-param removal: this
                // kernel only ever runs at log_n < 21, so transposed monomials
                // (log_n >= 21) are unreachable by construction — panic loudly if
                // a future strategy/caller change ever routes one here.
                assert!(
                    !transposed_monomials,
                    "subwarp forward NTT kernel does not support transposed monomials",
                );
                monomials_to_evals_subwarp(
                    inputs_matrix,
                    &mut outputs_matrix,
                    log_n,
                    coset_index_base,
                    coset_factor_shift,
                    num_cosets,
                    num_cols_per_coset_stride,
                    log_instances_per_block,
                    stream,
                )
            }
            super::NttKernelKind::MonomialsToEvalsSmemPacked {
                log_instances_per_block,
                ..
            } => {
                assert!(
                    !transposed_monomials,
                    "smem-packed forward NTT kernel does not support transposed monomials",
                );
                monomials_to_evals_smem_packed(
                    inputs_matrix,
                    &mut outputs_matrix,
                    log_n,
                    coset_index_base,
                    coset_factor_shift,
                    num_cosets,
                    num_cols_per_coset_stride,
                    log_instances_per_block,
                    stream,
                )
            }
            _ => {
                assert!(
                    !transposed_monomials,
                    "compact 1-pass forward NTT kernel does not support transposed monomials",
                );
                monomials_to_evals_compact_1_pass(
                    inputs_matrix,
                    &mut outputs_matrix,
                    log_n,
                    coset_index_base,
                    coset_factor_shift,
                    num_cosets,
                    num_cols_per_coset_stride,
                    strategy.columns_per_launch,
                    stream,
                )
            }
        };
    }
    if strategy.passes.len() == 2
        && matches!(
            strategy.passes[0].kernel,
            super::NttKernelKind::MonomialsToEvalsFirstCompact { .. }
        )
    {
        // Precondition guard restored after the dead-param removal: the 2-pass
        // compact-initial kernel only ever runs at log_n < 21, so transposed
        // monomials (log_n >= 21) are unreachable by construction — panic loudly
        // if a future strategy/caller change ever routes one here.
        assert!(
            !transposed_monomials,
            "2-pass compact-initial forward NTT kernel does not support transposed monomials",
        );
        let mut outputs_matrix = DeviceMatrixMut::new(outputs, trace_len);
        return monomials_to_evals_2_pass_compact_initial(
            inputs_matrix,
            &mut outputs_matrix,
            log_n,
            coset_index_base,
            coset_factor_shift,
            num_cosets,
            num_cols_per_coset_stride,
            strategy.cosets_per_launch,
            strategy.columns_per_launch,
            stream,
        );
    }
    if strategy.passes.len() == 3 {
        let mut outputs_matrix = DeviceMatrixMut::new(outputs, trace_len);
        return monomials_to_evals_3_pass(
            inputs_matrix,
            &mut outputs_matrix,
            log_n,
            coset_index_base,
            coset_factor_shift,
            num_cosets,
            num_cols_per_coset_stride,
            strategy.cosets_per_launch,
            strategy.columns_per_launch,
            transposed_monomials,
            stream,
        );
    }
    // Fallback for any pass shape not handled above: loop per coset using the
    // existing single-coset dispatch. Honors num_cols_per_coset_stride by
    // offsetting each coset's slab by stride * trace_len BFs.
    for coset_offset in 0..num_cosets {
        let global_coset = coset_index_base + coset_offset;
        let chunk_start = coset_offset * num_cols_per_coset_stride * trace_len;
        let chunk_end = chunk_start + num_cols * trace_len;
        let chunk = &mut outputs[chunk_start..chunk_end];
        let mut outputs_matrix = DeviceMatrixMut::new(chunk, trace_len);
        dispatch_strategy(
            inputs_matrix,
            &mut outputs_matrix,
            log_n,
            log_lde_factor,
            global_coset,
            transposed_monomials,
            ntt_ctx,
            // DIT is always single-pass and handled above; this fallback is for
            // 2/3-pass-compact shapes that ignore the scratch. Reborrow anyway
            // so the Option survives the loop.
            d_table_scratch.as_deref_mut(),
            stream,
            &strategy,
            device_properties,
        )?;
    }
    Ok(())
}
