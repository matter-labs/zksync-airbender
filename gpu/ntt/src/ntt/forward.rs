#![allow(non_snake_case)]

use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart_sys::{cudaFuncSetAttribute, CudaFuncAttribute};

use super::kernels::*;
use gpu_core::primitives::device_structures::{
    DeviceMatrixChunk, DeviceMatrixChunkImpl, DeviceMatrixChunkMut, DeviceMatrixChunkMutImpl,
};
use gpu_core::primitives::field::BaseField;
use gpu_core::primitives::utils::GetChunksCount;

use std::mem::size_of;

type BF = BaseField;

pub fn monomials_to_evals_3_pass(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    coset_index_base: usize,
    coset_factor_shift: u32,
    num_cosets: usize,
    num_cols_per_coset: usize,
    cosets_per_launch: usize,
    columns_per_launch: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    // Multi-coset flat-blockIdx.x layout: initial pass packs
    //   gridDim.x = blocks_per_ntt * cosets_in_tile * cols_in_chunk
    // (kernel decomposes coset and computes coset_factor_power inline). Two
    // noninitial_8 passes use the same packing. With cosets_per_launch = 1
    // (log_cosets_in_tile = 0) the layout collapses to the original
    // single-coset path. cosets_per_launch is sized by the strategy to keep
    // pass-1 output resident in L2 across the three passes.
    let n = 1 << log_n;
    assert_eq!(inputs_matrix.rows(), n);
    assert_eq!(outputs_matrix.rows(), n);
    assert_eq!(inputs_matrix.slice().as_ptr() as usize % 16, 0);
    assert_eq!(outputs_matrix.slice().as_ptr() as usize % 16, 0);
    assert_eq!((inputs_matrix.stride() * size_of::<BF>()) % 16, 0);
    assert_eq!((outputs_matrix.stride() * size_of::<BF>()) % 16, 0);
    assert_eq!((inputs_matrix.offset() * size_of::<BF>()) % 16, 0);
    assert_eq!((outputs_matrix.offset() * size_of::<BF>()) % 16, 0);
    assert!(columns_per_launch >= 1);
    assert!(cosets_per_launch >= 1 && cosets_per_launch <= num_cosets);
    assert!(num_cosets.is_power_of_two());
    assert!(cosets_per_launch.is_power_of_two());
    let num_ntts = inputs_matrix.cols();
    assert!(
        num_cols_per_coset >= num_ntts,
        "num_cols_per_coset ({num_cols_per_coset}) < num_ntts ({num_ntts})",
    );
    let max_col_offset_exclusive = (num_cosets - 1) * num_cols_per_coset + num_ntts;
    assert!(
        outputs_matrix.cols() >= max_col_offset_exclusive,
        "outputs_matrix.cols() = {} < {}",
        outputs_matrix.cols(),
        max_col_offset_exclusive,
    );
    let log_cosets_in_tile = cosets_per_launch.trailing_zeros() as i32;
    let initial_function = match log_n {
        21 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_initial_5_stages_kernel),
        22 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_initial_6_stages_kernel),
        23 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_initial_7_stages_kernel),
        24 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_initial_8_stages_kernel),
        _ => unreachable!(
            "NTT 3-pass monomials->evals kernels are only generated for log_n in 21..=24"
        ),
    };
    let inputs_slice = inputs_matrix.slice();
    let input_stride = inputs_matrix.stride();
    let input_offset = inputs_matrix.offset();
    let output_stride = outputs_matrix.stride();
    let output_offset = outputs_matrix.offset();
    let outputs_slice_const = unsafe {
        DeviceSlice::from_raw_parts(
            outputs_matrix.slice().as_ptr(),
            outputs_matrix.slice().len(),
        )
    };
    let outputs_slice_mut = outputs_matrix.slice_mut();
    // Loop order: col-tile OUTER, coset-tile INNER. This keeps the col-tile's
    // monomial source resident in L2 across the coset launches (each coset
    // launch re-reads the same monomials -- with the 50% L2 working-set budget
    // from `select_ntt_strategy`, the other 50% of L2 holds the monomials for
    // the duration of the col-tile's coset sweep).
    let mut col_start = 0usize;
    while col_start < num_ntts {
        let cols_in_chunk = (num_ntts - col_start).min(columns_per_launch);
        let input_range = col_start * input_stride..(col_start + cols_in_chunk) * input_stride;
        let input_slice = &inputs_slice[input_range];
        let input_matrix = DeviceMatrixChunk::new(input_slice, input_stride, input_offset, n);
        let input_matrix = input_matrix.as_ptr_and_stride();
        let mut coset_tile_start = 0usize;
        while coset_tile_start < num_cosets {
            let cosets_in_tile = (num_cosets - coset_tile_start).min(cosets_per_launch);
            debug_assert!(cosets_in_tile.is_power_of_two());
            let tile_coset_base = coset_index_base + coset_tile_start;
            // Slice the multi-coset output buffer to start at the tile's first
            // virtual column (coset_tile_start * num_cols_per_coset + col_start).
            // The kernel's add_col(coset_in_tile * num_cols_per_coset +
            // col_within_tile) navigates from this slice base.
            let tile_base_in_cols = coset_tile_start * num_cols_per_coset + col_start;
            let output_byte_start = tile_base_in_cols * output_stride;
            let output_slice_const = &outputs_slice_const[output_byte_start..];
            let output_slice_mut = &mut outputs_slice_mut[output_byte_start..];
            let output_matrix_const =
                DeviceMatrixChunk::new(output_slice_const, output_stride, output_offset, n);
            let mut output_matrix_mut =
                DeviceMatrixChunkMut::new(output_slice_mut, output_stride, output_offset, n);
            let output_matrix_const = output_matrix_const.as_ptr_and_stride();
            let output_matrix_mut = output_matrix_mut.as_mut_ptr_and_stride();
            let threads = 256;
            let bf_vals_per_block = 1 << 13; // 8192
            let blocks = n.get_chunks_count(bf_vals_per_block);
            // Initial pass: gridDim.x = blocks * cosets_in_tile * cols_in_chunk.
            let grid_dim_initial: Dim3 =
                (blocks as u32 * cosets_in_tile as u32 * cols_in_chunk as u32).into();
            let config = CudaLaunchConfig::basic(grid_dim_initial, threads as u32, stream);
            let args_initial = MonomialsToEvalsCompactArguments::new(
                input_matrix,
                output_matrix_mut,
                transposed_monomials,
                log_n as i32,
                tile_coset_base as i32,
                coset_factor_shift as i32,
                num_cols_per_coset as i32,
                log_cosets_in_tile,
            );
            initial_function.launch(&config, &args_initial)?;
            // Two noninitial_8 passes with start_stage = log_n - 16, log_n - 8.
            let threads = 512;
            let mut start_stage = log_n - 16;
            for _ in 0..2 {
                let num_block_exchg_regions = n >> (start_stage + 8);
                let block_exchg_region_size = 1 << (start_stage + 8);
                let blocks_per_exchg_region = block_exchg_region_size / bf_vals_per_block;
                assert_eq!(
                    blocks_per_exchg_region * num_block_exchg_regions,
                    n / bf_vals_per_block
                );
                let grid_dim: Dim3 = (blocks_per_exchg_region as u32
                    * num_block_exchg_regions as u32
                    * cosets_in_tile as u32
                    * cols_in_chunk as u32)
                    .into();
                let config = CudaLaunchConfig::basic(grid_dim, threads as u32, stream);
                let args = StridedTilesStagesArguments::new(
                    output_matrix_const,
                    output_matrix_mut,
                    log_n as i32,
                    start_stage as i32,
                    num_cols_per_coset as i32,
                    log_cosets_in_tile,
                );
                StridedTilesStagesFunction(ab_monomials_to_evals_noninitial_8_stages_kernel)
                    .launch(&config, &args)?;
                start_stage += 8;
            }
            coset_tile_start += cosets_in_tile;
        }
        col_start += cols_in_chunk;
    }
    Ok(())
}

pub fn monomials_to_evals_compact_1_pass(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    coset_index_base: usize,
    coset_factor_shift: u32,
    num_cosets: usize,
    num_cols_per_coset: usize,
    columns_per_launch: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    // One block per (column, coset) NTT, all `log_n` butterfly stages run
    // inside the block out of shared memory. Coset shift is fused into the
    // bitreversed load. Shared memory is `extern __shared__ bf smem[]` and is
    // sized per LOG_N at launch time.
    //
    // Multi-coset flat-blockIdx.x layout: `gridDim.x = cosets_per_launch *
    // cols_in_chunk` (blocks_per_ntt = 1 for compact 1-pass). The kernel
    // decomposes blockIdx.x into (coset_in_tile, col), advances the output
    // pointer to `(coset_in_tile * num_cols + col) * trace_len`, and computes
    // `coset_factor_power = (coset_index_base + coset_in_tile) <<
    // coset_factor_shift` inline. With `num_cosets = 1` and `coset_index_base =
    // coset_index`, this collapses to the original single-coset behavior.
    //
    // Output buffer layout when `num_cosets > 1`: coset-major outer,
    // column-major inner, i.e. coset k spans rows
    // `[k * num_cols * trace_len, (k + 1) * num_cols * trace_len)`. The output
    // matrix passed in covers all `num_cosets * num_cols` virtual columns.
    assert!(
        (4..=12).contains(&log_n),
        "compact 1-pass NTT only supports log_n in [4, 12]"
    );
    assert!(
        !transposed_monomials,
        "compact 1-pass NTT does not support transposed monomials"
    );
    assert!(columns_per_launch >= 1);
    assert!(
        num_cosets.is_power_of_two(),
        "num_cosets must be a power of 2 (got {num_cosets})"
    );
    let n = 1 << log_n;
    assert_eq!(inputs_matrix.rows(), n);
    assert_eq!(outputs_matrix.rows(), n);
    let num_ntts = inputs_matrix.cols();
    assert!(
        num_cols_per_coset >= num_ntts,
        "num_cols_per_coset ({num_cols_per_coset}) < num_ntts ({num_ntts})",
    );
    let max_col_offset_exclusive = (num_cosets - 1) * num_cols_per_coset + num_ntts;
    assert!(
        outputs_matrix.cols() >= max_col_offset_exclusive,
        "outputs_matrix.cols() = {} < {} (num_cosets={}, stride={}, num_ntts={})",
        outputs_matrix.cols(),
        max_col_offset_exclusive,
        num_cosets,
        num_cols_per_coset,
        num_ntts,
    );
    let inputs_slice = inputs_matrix.slice();
    let input_stride = inputs_matrix.stride();
    let input_offset = inputs_matrix.offset();
    let output_stride = outputs_matrix.stride();
    let output_offset = outputs_matrix.offset();
    let outputs_slice_mut = outputs_matrix.slice_mut();
    let log_cosets_in_tile = num_cosets.trailing_zeros() as i32;
    let threads = 256u32;
    let smem_bytes = n * size_of::<BF>();
    let function = match log_n {
        4 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_all_4_stages_kernel),
        5 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_all_5_stages_kernel),
        6 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_all_6_stages_kernel),
        7 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_all_7_stages_kernel),
        8 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_all_8_stages_kernel),
        9 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_all_9_stages_kernel),
        10 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_all_10_stages_kernel),
        11 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_all_11_stages_kernel),
        12 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_all_12_stages_kernel),
        _ => unreachable!("compact 1-pass monomials->evals kernels only exist for log_n in 4..=12"),
    };
    // For LOG_N <= 12 the per-block smem (<= 16 KB) is under the default cap
    // and the `cudaFuncSetAttribute` call is a no-op; we apply it
    // unconditionally to keep the launch path uniform.
    let func_ptr = function.as_ptr();
    unsafe {
        cudaFuncSetAttribute(
            func_ptr,
            CudaFuncAttribute::MaxDynamicSharedMemorySize,
            smem_bytes as i32,
        )
        .wrap()?;
    }
    let mut col_start = 0usize;
    while col_start < num_ntts {
        let cols_in_chunk = (num_ntts - col_start).min(columns_per_launch);
        let input_range = col_start * input_stride..(col_start + cols_in_chunk) * input_stride;
        let input_slice = &inputs_slice[input_range];
        let input_matrix = DeviceMatrixChunk::new(input_slice, input_stride, input_offset, n);
        // Slice the multi-coset output buffer to start at col_start for the
        // first coset slot. The kernel's add_col(coset * num_ntts + col)
        // advances from there; both axes are bounded by num_cosets /
        // cols_in_chunk.
        let output_byte_start = col_start * output_stride;
        let output_slice_mut = &mut outputs_slice_mut[output_byte_start..];
        let mut output_matrix_mut =
            DeviceMatrixChunkMut::new(output_slice_mut, output_stride, output_offset, n);
        let input_matrix = input_matrix.as_ptr_and_stride();
        let output_matrix_mut = output_matrix_mut.as_mut_ptr_and_stride();
        // Flat-blockIdx.x layout: gridDim.x = num_cosets * cols_in_chunk
        // (blocks_per_ntt = 1 for compact 1-pass).
        let grid_dim: Dim3 = ((num_cosets * cols_in_chunk) as u32).into();
        let mut config = CudaLaunchConfig::basic(grid_dim, threads, stream);
        config.dynamic_smem_bytes = smem_bytes;
        let args = MonomialsToEvalsCompactArguments::new(
            input_matrix,
            output_matrix_mut,
            false,
            log_n as i32,
            coset_index_base as i32,
            coset_factor_shift as i32,
            num_cols_per_coset as i32,
            log_cosets_in_tile,
        );
        function.launch(&config, &args)?;
        col_start += cols_in_chunk;
    }
    Ok(())
}

pub fn monomials_to_evals_subwarp(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    coset_index_base: usize,
    coset_factor_shift: u32,
    num_cosets: usize,
    num_cols_per_coset: usize,
    log_instances_per_block: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    // Sub-warp register-resident kernel for log_n in {4, 5}: each thread holds
    // one element value in a register, butterflies swap partners via
    // `__shfl_xor_sync`. Block threads = N << log_ipb; for the supported pairs
    // this evaluates to 256.
    assert!(
        (1..=5).contains(&log_n),
        "subwarp NTT only supports log_n in [1, 5]"
    );
    assert!(
        !transposed_monomials,
        "subwarp NTT does not support transposed monomials"
    );
    assert!(
        num_cosets.is_power_of_two(),
        "num_cosets must be a power of 2 (got {num_cosets})"
    );
    let n = 1 << log_n;
    assert_eq!(inputs_matrix.rows(), n);
    assert_eq!(outputs_matrix.rows(), n);
    let num_ntts = inputs_matrix.cols();
    assert!(
        num_cols_per_coset >= num_ntts,
        "num_cols_per_coset ({num_cols_per_coset}) < num_ntts ({num_ntts})",
    );
    assert!(
        num_ntts.is_power_of_two(),
        "subwarp NTT requires num_ntts to be a power of 2 (got {num_ntts})"
    );
    let instances_per_block = 1usize << log_instances_per_block;
    let workload = num_cosets
        .checked_mul(num_ntts)
        .expect("num_cosets * num_ntts overflow");
    assert!(
        workload % instances_per_block == 0,
        "workload ({workload}) not divisible by instances_per_block ({instances_per_block})",
    );
    let max_col_offset_exclusive = (num_cosets - 1) * num_cols_per_coset + num_ntts;
    assert!(
        outputs_matrix.cols() >= max_col_offset_exclusive,
        "outputs_matrix.cols() = {} < {} (num_cosets={}, stride={}, num_ntts={})",
        outputs_matrix.cols(),
        max_col_offset_exclusive,
        num_cosets,
        num_cols_per_coset,
        num_ntts,
    );
    let log_cosets_in_tile = num_cosets.trailing_zeros() as i32;
    let threads_per_block = (n << log_instances_per_block) as u32;
    debug_assert!(
        threads_per_block <= 256,
        "subwarp threads_per_block ({threads_per_block}) > 256",
    );
    let function = match (log_n, log_instances_per_block) {
        (1, 7) => {
            MonomialsToEvalsCompactFunction(ab_monomials_to_evals_subwarp_1_stages_ipb7_kernel)
        }
        (2, 6) => {
            MonomialsToEvalsCompactFunction(ab_monomials_to_evals_subwarp_2_stages_ipb6_kernel)
        }
        (3, 5) => {
            MonomialsToEvalsCompactFunction(ab_monomials_to_evals_subwarp_3_stages_ipb5_kernel)
        }
        (4, 4) => {
            MonomialsToEvalsCompactFunction(ab_monomials_to_evals_subwarp_4_stages_ipb4_kernel)
        }
        (5, 3) => {
            MonomialsToEvalsCompactFunction(ab_monomials_to_evals_subwarp_5_stages_ipb3_kernel)
        }
        (1, 0) => {
            MonomialsToEvalsCompactFunction(ab_monomials_to_evals_subwarp_1_stages_ipb0_kernel)
        }
        (2, 0) => {
            MonomialsToEvalsCompactFunction(ab_monomials_to_evals_subwarp_2_stages_ipb0_kernel)
        }
        (3, 0) => {
            MonomialsToEvalsCompactFunction(ab_monomials_to_evals_subwarp_3_stages_ipb0_kernel)
        }
        _ => unreachable!(
            "subwarp kernels exist only for (log_n, log_ipb) in {{(1,7),(2,6),(3,5),(4,4),(5,3),(1,0),(2,0),(3,0)}}, got ({log_n}, {log_instances_per_block})"
        ),
    };
    let input_stride = inputs_matrix.stride();
    let input_offset = inputs_matrix.offset();
    let output_stride = outputs_matrix.stride();
    let output_offset = outputs_matrix.offset();
    let inputs_slice = inputs_matrix.slice();
    let outputs_slice_mut = outputs_matrix.slice_mut();
    let input_slice = &inputs_slice[..num_ntts * input_stride];
    let input_matrix = DeviceMatrixChunk::new(input_slice, input_stride, input_offset, n);
    let output_slice_mut = &mut outputs_slice_mut[..];
    let mut output_matrix_mut =
        DeviceMatrixChunkMut::new(output_slice_mut, output_stride, output_offset, n);
    let input_matrix = input_matrix.as_ptr_and_stride();
    let output_matrix_mut = output_matrix_mut.as_mut_ptr_and_stride();
    // gridDim.x = (num_cosets * num_ntts) >> log_instances_per_block.
    let grid_dim: Dim3 = ((workload >> log_instances_per_block) as u32).into();
    let config = CudaLaunchConfig::basic(grid_dim, threads_per_block, stream);
    let args = MonomialsToEvalsCompactArguments::new(
        input_matrix,
        output_matrix_mut,
        false,
        log_n as i32,
        coset_index_base as i32,
        coset_factor_shift as i32,
        num_cols_per_coset as i32,
        log_cosets_in_tile,
    );
    function.launch(&config, &args)?;
    Ok(())
}

pub fn monomials_to_evals_smem_packed(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    coset_index_base: usize,
    coset_factor_shift: u32,
    num_cosets: usize,
    num_cols_per_coset: usize,
    log_instances_per_block: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    // Smem-packed multi-NTT-per-block kernel for log_n in [6, 8]: each block
    // holds `1 << log_instances_per_block` independent NTT instances. Block
    // threads = HALF_N << log_ipb = (1 << (log_n - 1 + log_ipb)); for the
    // supported (log_n, log_ipb) pairs this evaluates to 256.
    //
    // Block flat index: `(blockIdx.x << log_ipb) | local_instance`, decomposed
    // into (coset_in_tile, col) the same way the compact 1-pass kernel does --
    // coset_in_tile in the low `log_cosets_in_tile` bits, col above. Caller
    // must guarantee `num_cosets * num_ntts` is a multiple of (1 << log_ipb);
    // the strategy enforces this by only selecting smem-packed when the
    // workload is a power-of-two >= IPB.
    assert!(
        (6..=8).contains(&log_n),
        "smem-packed NTT only supports log_n in [6, 8]"
    );
    assert!(
        !transposed_monomials,
        "smem-packed NTT does not support transposed monomials"
    );
    assert!(
        num_cosets.is_power_of_two(),
        "num_cosets must be a power of 2 (got {num_cosets})"
    );
    let n = 1 << log_n;
    assert_eq!(inputs_matrix.rows(), n);
    assert_eq!(outputs_matrix.rows(), n);
    let num_ntts = inputs_matrix.cols();
    assert!(
        num_cols_per_coset >= num_ntts,
        "num_cols_per_coset ({num_cols_per_coset}) < num_ntts ({num_ntts})",
    );
    assert!(
        num_ntts.is_power_of_two(),
        "smem-packed NTT requires num_ntts to be a power of 2 (got {num_ntts})"
    );
    let instances_per_block = 1usize << log_instances_per_block;
    let workload = num_cosets
        .checked_mul(num_ntts)
        .expect("num_cosets * num_ntts overflow");
    assert!(
        workload % instances_per_block == 0,
        "workload ({workload}) not divisible by instances_per_block ({instances_per_block})",
    );
    let max_col_offset_exclusive = (num_cosets - 1) * num_cols_per_coset + num_ntts;
    assert!(
        outputs_matrix.cols() >= max_col_offset_exclusive,
        "outputs_matrix.cols() = {} < {} (num_cosets={}, stride={}, num_ntts={})",
        outputs_matrix.cols(),
        max_col_offset_exclusive,
        num_cosets,
        num_cols_per_coset,
        num_ntts,
    );
    let log_cosets_in_tile = num_cosets.trailing_zeros() as i32;
    let half_n = 1usize << (log_n - 1);
    let threads_per_block = (half_n << log_instances_per_block) as u32;
    debug_assert!(
        threads_per_block <= 256,
        "smem-packed threads_per_block ({threads_per_block}) > 256",
    );
    let smem_bytes = (n << log_instances_per_block) * size_of::<BF>();
    let function = match (log_n, log_instances_per_block) {
        (6, 3) => {
            MonomialsToEvalsCompactFunction(ab_monomials_to_evals_smem_packed_6_stages_ipb3_kernel)
        }
        (7, 2) => {
            MonomialsToEvalsCompactFunction(ab_monomials_to_evals_smem_packed_7_stages_ipb2_kernel)
        }
        (8, 1) => {
            MonomialsToEvalsCompactFunction(ab_monomials_to_evals_smem_packed_8_stages_ipb1_kernel)
        }
        _ => unreachable!(
            "smem-packed kernels exist only for (log_n, log_ipb) in {{(6,3), (7,2), (8,1)}}, got ({log_n}, {log_instances_per_block})"
        ),
    };
    let func_ptr = function.as_ptr();
    // smem is <= 8 KB for all supported (log_n, log_ipb); the unconditional
    // setattr keeps the launch path uniform with the compact 1-pass kernel.
    unsafe {
        cudaFuncSetAttribute(
            func_ptr,
            CudaFuncAttribute::MaxDynamicSharedMemorySize,
            smem_bytes as i32,
        )
        .wrap()?;
    }
    let input_stride = inputs_matrix.stride();
    let input_offset = inputs_matrix.offset();
    let output_stride = outputs_matrix.stride();
    let output_offset = outputs_matrix.offset();
    let inputs_slice = inputs_matrix.slice();
    let outputs_slice_mut = outputs_matrix.slice_mut();
    let input_slice = &inputs_slice[..num_ntts * input_stride];
    let input_matrix = DeviceMatrixChunk::new(input_slice, input_stride, input_offset, n);
    let output_slice_mut = &mut outputs_slice_mut[..];
    let mut output_matrix_mut =
        DeviceMatrixChunkMut::new(output_slice_mut, output_stride, output_offset, n);
    let input_matrix = input_matrix.as_ptr_and_stride();
    let output_matrix_mut = output_matrix_mut.as_mut_ptr_and_stride();
    // gridDim.x = (num_cosets * num_ntts) >> log_instances_per_block.
    let grid_dim: Dim3 = ((workload >> log_instances_per_block) as u32).into();
    let mut config = CudaLaunchConfig::basic(grid_dim, threads_per_block, stream);
    config.dynamic_smem_bytes = smem_bytes;
    let args = MonomialsToEvalsCompactArguments::new(
        input_matrix,
        output_matrix_mut,
        false,
        log_n as i32,
        coset_index_base as i32,
        coset_factor_shift as i32,
        num_cols_per_coset as i32,
        log_cosets_in_tile,
    );
    function.launch(&config, &args)?;
    Ok(())
}

pub fn monomials_to_evals_2_pass_compact_initial(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    coset_index_base: usize,
    coset_factor_shift: u32,
    num_cosets: usize,
    num_cols_per_coset: usize,
    cosets_per_launch: usize,
    columns_per_launch: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    // Pass 1: compact "first K stages" kernel, K = log_n - 8, one block per
    // chunk of 2^K consecutive bitreversed inputs. Pass 2: noninitial_8
    // starting at start_stage = K. Covers log_n in [13, 20].
    //
    // Multi-coset flat-blockIdx.x: both passes pack
    //   gridDim.x = blocks_per_ntt * cosets_in_tile * cols_in_chunk
    // where blocks_per_ntt = n / 2^K (pass 1) or
    // blocks_per_exchg_region * num_exchg_regions (pass 2). The kernels
    // decompose blockIdx.x into (intra_blocks, coset_in_tile, col), advance
    // `gmem_*.add_col(coset_in_tile * num_cols_per_coset + col)` and (for
    // pass 1) compute `coset_factor_power = (coset_index_base + coset_in_tile)
    // << coset_factor_shift` inline. With `num_cosets = 1` and
    // `cosets_per_launch = 1` (log_cosets_in_tile = 0) the layout collapses
    // to the original single-coset path.
    assert!(
        (13..=20).contains(&log_n),
        "2-pass compact-initial NTT only supports log_n in [13, 20]"
    );
    assert!(
        !transposed_monomials,
        "2-pass compact-initial NTT does not support transposed monomials"
    );
    assert!(columns_per_launch >= 1);
    assert!(cosets_per_launch >= 1 && cosets_per_launch <= num_cosets);
    assert!(num_cosets.is_power_of_two());
    assert!(cosets_per_launch.is_power_of_two());
    let n = 1 << log_n;
    assert_eq!(inputs_matrix.rows(), n);
    assert_eq!(outputs_matrix.rows(), n);
    assert_eq!(inputs_matrix.slice().as_ptr() as usize % 16, 0);
    assert_eq!(outputs_matrix.slice().as_ptr() as usize % 16, 0);
    assert_eq!((inputs_matrix.stride() * size_of::<BF>()) % 16, 0);
    assert_eq!((outputs_matrix.stride() * size_of::<BF>()) % 16, 0);
    assert_eq!((inputs_matrix.offset() * size_of::<BF>()) % 16, 0);
    assert_eq!((outputs_matrix.offset() * size_of::<BF>()) % 16, 0);
    let log_k = log_n - 8;
    let k_vals = 1usize << log_k;
    let smem_bytes_pass1 = k_vals * size_of::<BF>();
    let threads_pass1 = 256u32;
    let blocks_pass1 = (n / k_vals) as u32;
    let pass1_function = match log_k {
        5 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_first_5_stages_compact_kernel),
        6 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_first_6_stages_compact_kernel),
        7 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_first_7_stages_compact_kernel),
        8 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_first_8_stages_compact_kernel),
        9 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_first_9_stages_compact_kernel),
        10 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_first_10_stages_compact_kernel),
        11 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_first_11_stages_compact_kernel),
        12 => MonomialsToEvalsCompactFunction(ab_monomials_to_evals_first_12_stages_compact_kernel),
        _ => unreachable!("log_k = log_n - 8 in [5, 12] for the 2-pass compact range"),
    };
    let num_ntts = inputs_matrix.cols();
    assert!(
        num_cols_per_coset >= num_ntts,
        "num_cols_per_coset ({num_cols_per_coset}) < num_ntts ({num_ntts})",
    );
    let max_col_offset_exclusive = (num_cosets - 1) * num_cols_per_coset + num_ntts;
    assert!(
        outputs_matrix.cols() >= max_col_offset_exclusive,
        "outputs_matrix.cols() = {} < {}",
        outputs_matrix.cols(),
        max_col_offset_exclusive,
    );
    let log_cosets_in_tile = cosets_per_launch.trailing_zeros() as i32;
    let inputs_slice = inputs_matrix.slice();
    let input_stride = inputs_matrix.stride();
    let input_offset = inputs_matrix.offset();
    let output_stride = outputs_matrix.stride();
    let output_offset = outputs_matrix.offset();
    let outputs_slice_const = unsafe {
        DeviceSlice::from_raw_parts(
            outputs_matrix.slice().as_ptr(),
            outputs_matrix.slice().len(),
        )
    };
    let outputs_slice_mut = outputs_matrix.slice_mut();
    // Loop order: col-tile OUTER, coset-tile INNER. Keeps the col-tile's
    // monomial source resident in L2 across the coset sweep -- with the 50%
    // L2 working-set budget from `select_ntt_strategy`, the other 50% holds
    // the monomials for all coset launches of one col-tile.
    let mut col_start = 0usize;
    while col_start < num_ntts {
        let cols_in_chunk = (num_ntts - col_start).min(columns_per_launch);
        let input_range = col_start * input_stride..(col_start + cols_in_chunk) * input_stride;
        let input_slice = &inputs_slice[input_range];
        let input_matrix = DeviceMatrixChunk::new(input_slice, input_stride, input_offset, n);
        let input_matrix = input_matrix.as_ptr_and_stride();
        let mut coset_tile_start = 0usize;
        while coset_tile_start < num_cosets {
            let cosets_in_tile = (num_cosets - coset_tile_start).min(cosets_per_launch);
            debug_assert!(cosets_in_tile.is_power_of_two());
            let tile_coset_base = coset_index_base + coset_tile_start;
            // Slice the multi-coset output buffer to start at the tile's first
            // virtual column (coset_tile_start * num_cols_per_coset + col_start).
            // The kernel's add_col(coset_in_tile * num_cols_per_coset +
            // col_within_tile) navigates from this slice base.
            let tile_base_in_cols = coset_tile_start * num_cols_per_coset + col_start;
            let output_byte_start = tile_base_in_cols * output_stride;
            let output_slice_const = &outputs_slice_const[output_byte_start..];
            let output_slice_mut = &mut outputs_slice_mut[output_byte_start..];
            let output_matrix_const =
                DeviceMatrixChunk::new(output_slice_const, output_stride, output_offset, n);
            let mut output_matrix_mut =
                DeviceMatrixChunkMut::new(output_slice_mut, output_stride, output_offset, n);
            let output_matrix_const = output_matrix_const.as_ptr_and_stride();
            let output_matrix_mut = output_matrix_mut.as_mut_ptr_and_stride();
            // Pass 1: gridDim.x = blocks_pass1 * cosets_in_tile * cols_in_chunk.
            let grid_dim_pass1: Dim3 =
                (blocks_pass1 * cosets_in_tile as u32 * cols_in_chunk as u32).into();
            let mut config = CudaLaunchConfig::basic(grid_dim_pass1, threads_pass1, stream);
            config.dynamic_smem_bytes = smem_bytes_pass1;
            let args = MonomialsToEvalsCompactArguments::new(
                input_matrix,
                output_matrix_mut,
                false,
                log_n as i32,
                tile_coset_base as i32,
                coset_factor_shift as i32,
                num_cols_per_coset as i32,
                log_cosets_in_tile,
            );
            pass1_function.launch(&config, &args)?;
            // Pass 2: noninitial_8 with start_stage = log_k.
            let threads_pass2 = 512;
            let bf_vals_per_block_pass2 = 1 << 13;
            let start_stage = log_k;
            let num_block_exchg_regions = n >> (start_stage + 8);
            let block_exchg_region_size = 1 << (start_stage + 8);
            let blocks_per_exchg_region = block_exchg_region_size / bf_vals_per_block_pass2;
            assert_eq!(
                blocks_per_exchg_region * num_block_exchg_regions,
                n / bf_vals_per_block_pass2
            );
            let grid_dim_pass2: Dim3 = (blocks_per_exchg_region as u32
                * num_block_exchg_regions as u32
                * cosets_in_tile as u32
                * cols_in_chunk as u32)
                .into();
            let config_pass2 =
                CudaLaunchConfig::basic(grid_dim_pass2, threads_pass2 as u32, stream);
            let args_pass2 = StridedTilesStagesArguments::new(
                output_matrix_const,
                output_matrix_mut,
                log_n as i32,
                start_stage as i32,
                num_cols_per_coset as i32,
                log_cosets_in_tile,
            );
            StridedTilesStagesFunction(ab_monomials_to_evals_noninitial_8_stages_kernel)
                .launch(&config_pass2, &args_pass2)?;
            coset_tile_start += cosets_in_tile;
        }
        col_start += cols_in_chunk;
    }
    Ok(())
}

pub fn monomials_to_evals_2_pass(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    coset_factor_power: usize,
    columns_per_launch: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    // Legacy 2-pass forward NTT for log_n in [23, 24] when the column footprint
    // exceeds L2. Both passes use the flat-blockIdx.x layout: gridDim.x =
    // blocks_per_ntt * cols_in_chunk (kernels decompose internally).
    let n = 1 << log_n;
    assert_eq!(inputs_matrix.rows(), n);
    assert_eq!(outputs_matrix.rows(), n);
    // __pipeline_memcpy_asyncs in the kernel require 16 byte alignment
    assert_eq!(inputs_matrix.slice().as_ptr() as usize % 16, 0);
    assert_eq!(outputs_matrix.slice().as_ptr() as usize % 16, 0);
    assert_eq!((inputs_matrix.stride() * size_of::<BF>()) % 16, 0);
    assert_eq!((outputs_matrix.stride() * size_of::<BF>()) % 16, 0);
    assert_eq!((inputs_matrix.offset() * size_of::<BF>()) % 16, 0);
    assert_eq!((outputs_matrix.offset() * size_of::<BF>()) % 16, 0);
    assert!(columns_per_launch >= 1);
    let num_ntts = outputs_matrix.cols();
    let inputs_slice = inputs_matrix.slice();
    let input_stride = inputs_matrix.stride();
    let input_offset = inputs_matrix.offset();
    let output_stride = outputs_matrix.stride();
    let output_offset = outputs_matrix.offset();
    let outputs_slice_const = unsafe {
        DeviceSlice::from_raw_parts(
            outputs_matrix.slice().as_ptr(),
            outputs_matrix.slice().len(),
        )
    };
    let outputs_slice_mut = outputs_matrix.slice_mut();
    let mut col_start = 0usize;
    while col_start < num_ntts {
        let cols_in_chunk = (num_ntts - col_start).min(columns_per_launch);
        let input_range = col_start * input_stride..(col_start + cols_in_chunk) * input_stride;
        let output_range = col_start * output_stride..(col_start + cols_in_chunk) * output_stride;
        let input_slice = &inputs_slice[input_range];
        let output_slice_const = &outputs_slice_const[output_range.clone()];
        let output_slice_mut = &mut outputs_slice_mut[output_range];
        let input_matrix = DeviceMatrixChunk::new(input_slice, input_stride, input_offset, n);
        let output_matrix_const =
            DeviceMatrixChunk::new(output_slice_const, output_stride, output_offset, n);
        let mut output_matrix_mut =
            DeviceMatrixChunkMut::new(output_slice_mut, output_stride, output_offset, n);
        let input_matrix = input_matrix.as_ptr_and_stride();
        let output_matrix_const = output_matrix_const.as_ptr_and_stride();
        let output_matrix_mut = output_matrix_mut.as_mut_ptr_and_stride();
        let bf_vals_per_block = 1 << 14; // 16384
        let smem_twiddles_per_block = 1 << 13; // 8192
        let smem_bytes = (bf_vals_per_block + smem_twiddles_per_block) * size_of::<BF>();
        let threads = 512;
        let blocks = n.get_chunks_count(bf_vals_per_block);
        // Flat-blockIdx.x: gridDim.x = blocks * cols_in_chunk.
        let grid_dim_pass1: Dim3 = (blocks as u32 * cols_in_chunk as u32).into();
        let mut config = CudaLaunchConfig::basic(grid_dim_pass1, threads as u32, stream);
        config.dynamic_smem_bytes = smem_bytes;
        let args = MonomialsToEvalsInitialArguments::new(
            input_matrix,
            output_matrix_mut,
            transposed_monomials,
            log_n as i32,
            coset_factor_power as i32,
        );
        let function =
            MonomialsToEvalsInitialFunction(ab_monomials_to_evals_first_14_stages_kernel);
        let func_ptr = function.as_ptr();
        unsafe {
            cudaFuncSetAttribute(
                func_ptr,
                CudaFuncAttribute::MaxDynamicSharedMemorySize,
                smem_bytes as i32,
            )
            .wrap()?;
        }
        function.launch(&config, &args)?;
        let bf_vals_per_block = 1 << 14; // 16384
        let smem_bytes = bf_vals_per_block * size_of::<BF>();
        let threads = 512;
        let blocks = n.get_chunks_count(bf_vals_per_block);
        // Flat-blockIdx.x: gridDim.x = blocks * cols_in_chunk.
        let grid_dim_pass2: Dim3 = (blocks as u32 * cols_in_chunk as u32).into();
        let mut config = CudaLaunchConfig::basic(grid_dim_pass2, threads as u32, stream);
        config.dynamic_smem_bytes = smem_bytes;
        let args = StridedTilesStagesArguments::new(
            output_matrix_const,
            output_matrix_mut,
            log_n as i32,
            0,
            0,
            0,
        );
        let function = match log_n {
            23 => StridedTilesStagesFunction(ab_monomials_to_evals_last_9_stages_kernel),
            24 => StridedTilesStagesFunction(ab_monomials_to_evals_last_10_stages_kernel),
            _ => unreachable!(
                "NTT 2-pass final-stage kernels are only generated for final_stages in {{9, 10}} (log_n in {{23, 24}})"
            ),
        };
        let func_ptr = function.as_ptr();
        unsafe {
            cudaFuncSetAttribute(
                func_ptr,
                CudaFuncAttribute::MaxDynamicSharedMemorySize,
                smem_bytes as i32,
            )
            .wrap()?;
        }
        function.launch(&config, &args)?;
        col_start += cols_in_chunk;
    }
    Ok(())
}
