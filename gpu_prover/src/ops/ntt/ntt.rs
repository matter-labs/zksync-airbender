#![allow(non_snake_case)]

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart_sys::{cudaFuncSetAttribute, CudaFuncAttribute};

use super::{natural_evals_to_bitreversed_coeffs, MIN_LOG_N_FOR_MULTISTAGE_KERNELS};

use crate::primitives::context::DeviceProperties;
use crate::primitives::device_structures::{
    DeviceMatrixChunk, DeviceMatrixChunkImpl, DeviceMatrixChunkMut, DeviceMatrixChunkMutImpl,
    DeviceMatrixMut, MutPtrAndStride, PtrAndStride,
};
use crate::primitives::field::BaseField;
use crate::primitives::ntt_twiddles::OMEGA_LOG_ORDER;
use crate::primitives::utils::GetChunksCount;

use std::mem::size_of;

type BF = BaseField;

cuda_kernel!(
    StridedTilesStages,
    strided_tiles_stages,
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    log_n: i32,
    start_stage: i32,
    num_cols_per_coset: i32,
    log_cosets_in_tile: i32,
);

// 2-pass evals to monomials
strided_tiles_stages!(ab_evals_to_monomials_first_9_stages_kernel);
strided_tiles_stages!(ab_evals_to_monomials_first_10_stages_kernel);

// 3-pass evals to monomials
strided_tiles_stages!(ab_evals_to_monomials_nonfinal_8_stages_kernel);

// 2-pass monomials to evals
strided_tiles_stages!(ab_monomials_to_evals_last_9_stages_kernel);
strided_tiles_stages!(ab_monomials_to_evals_last_10_stages_kernel);

// 3-pass monomials to evals
strided_tiles_stages!(ab_monomials_to_evals_noninitial_8_stages_kernel);

cuda_kernel!(
    EvalsToMonomialsFinal,
    evals_to_monomials_final,
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    transposed_monomials: bool,
    log_n: i32,
    num_cols_per_coset: i32,
    log_cosets_in_tile: i32,
);

// 2-pass evals to monomials
evals_to_monomials_final!(ab_evals_to_monomials_last_14_stages_kernel);

// 3-pass evals to monomials
evals_to_monomials_final!(ab_evals_to_monomials_final_5_stages_kernel);
evals_to_monomials_final!(ab_evals_to_monomials_final_6_stages_kernel);
evals_to_monomials_final!(ab_evals_to_monomials_final_7_stages_kernel);
evals_to_monomials_final!(ab_evals_to_monomials_final_8_stages_kernel);

cuda_kernel!(
    MonomialsToEvalsInitial,
    monomials_to_evals_initial,
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    transposed_monomials: bool,
    log_n: i32,
    coset_factor_power: i32,
);

// 2-pass monomials to evals
monomials_to_evals_initial!(ab_monomials_to_evals_first_14_stages_kernel);

// 3-pass monomials to evals initial kernels are registered below alongside
// the rest of the multi-coset MonomialsToEvalsCompact family.

// Compact 1-pass (all-stages-in-block) monomials to evals for log_n in [4, 12].
// These kernels consume the multi-coset signature: gridDim.x packs
// (col_tile, coset_in_tile, intra_block=0); the kernel decomposes blockIdx.x
// to recover (coset, col) and computes `coset_factor_power` from
// `coset_index_base + coset_in_tile`.
cuda_kernel!(
    MonomialsToEvalsCompact,
    monomials_to_evals_compact,
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    transposed_monomials: bool,
    log_n: i32,
    coset_index_base: i32,
    coset_factor_shift: i32,
    num_cols_per_coset: i32,
    log_cosets_in_tile: i32,
);

monomials_to_evals_compact!(ab_monomials_to_evals_all_4_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_all_5_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_all_6_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_all_7_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_all_8_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_all_9_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_all_10_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_all_11_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_all_12_stages_kernel);

// Smem-packed multi-NTT-per-block 1-pass kernels for log_n in [6, 8]: each
// block holds `1 << LOG_IPB` independent NTT instances so a 256-thread block
// stays fully utilized through the butterfly stages. Same MonomialsToEvalsCompact
// signature as the compact 1-pass kernels (multi-coset args are reused; the
// kernel internally re-decomposes blockIdx.x to (col, coset_in_tile) packed
// IPB-at-a-time).
monomials_to_evals_compact!(ab_monomials_to_evals_smem_packed_6_stages_ipb3_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_smem_packed_7_stages_ipb2_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_smem_packed_8_stages_ipb1_kernel);

// Sub-warp register-resident multi-NTT-per-block 1-pass kernels for log_n in
// [1, 5]: each thread holds one element in a register; the butterfly exchange
// uses `__shfl_xor_sync` instead of smem. Same MonomialsToEvalsCompact signature.
monomials_to_evals_compact!(ab_monomials_to_evals_subwarp_1_stages_ipb7_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_subwarp_2_stages_ipb6_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_subwarp_3_stages_ipb5_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_subwarp_4_stages_ipb4_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_subwarp_5_stages_ipb3_kernel);
// IPB=1 variants for log_n in [1, 3] cover workloads below IPB_max where the
// strategy can't fall back to compact 1-pass (which only exists for log_n >= 4).
monomials_to_evals_compact!(ab_monomials_to_evals_subwarp_1_stages_ipb0_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_subwarp_2_stages_ipb0_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_subwarp_3_stages_ipb0_kernel);

// Streaming multi-coset single-column NTT for log_n in [3, 8]. One block owns
// a contiguous range of cosets, walks them with a register-resident running
// shift update, and stores via a vector store. The v8 variant uses 32-byte
// (vec8) stores (-> STG.E.256 on sm_100+, two STG.E.128 on older arch); the
// v4 variant uses 16-byte (vec4) stores (-> STG.E.128) with half the
// per-thread state and is picked by the dispatcher on sm_<90 where the v8
// store would decompose. Caller loops over columns.
cuda_kernel!(
    MonomialsToEvalsStreaming,
    monomials_to_evals_streaming,
    monomials: *const BF,
    out: *mut BF,
    coset_index_base: i32,
    coset_factor_shift: i32,
    num_cosets: u32,
    coset_stride_bf: u64,
);
monomials_to_evals_streaming!(ab_monomials_to_evals_streaming_v8_3_stages_kernel);
monomials_to_evals_streaming!(ab_monomials_to_evals_streaming_v8_4_stages_kernel);
monomials_to_evals_streaming!(ab_monomials_to_evals_streaming_v8_5_stages_kernel);
monomials_to_evals_streaming!(ab_monomials_to_evals_streaming_v8_6_stages_kernel);
monomials_to_evals_streaming!(ab_monomials_to_evals_streaming_v8_7_stages_kernel);
monomials_to_evals_streaming!(ab_monomials_to_evals_streaming_v8_8_stages_kernel);
monomials_to_evals_streaming!(ab_monomials_to_evals_streaming_v4_2_stages_kernel);
monomials_to_evals_streaming!(ab_monomials_to_evals_streaming_v4_3_stages_kernel);
monomials_to_evals_streaming!(ab_monomials_to_evals_streaming_v4_4_stages_kernel);
monomials_to_evals_streaming!(ab_monomials_to_evals_streaming_v4_5_stages_kernel);
monomials_to_evals_streaming!(ab_monomials_to_evals_streaming_v4_6_stages_kernel);
monomials_to_evals_streaming!(ab_monomials_to_evals_streaming_v4_7_stages_kernel);

// 3-pass monomials to evals: initial kernels share the multi-coset
// MonomialsToEvalsCompact signature so the 3-pass dispatcher can fold the
// coset axis into gridDim.x.
monomials_to_evals_compact!(ab_monomials_to_evals_initial_5_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_initial_6_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_initial_7_stages_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_initial_8_stages_kernel);

// 2-pass first-K-stages compact kernels for log_n in [13, 20]. Pass 1 does the
// first K = log_n - 8 butterfly stages per chunk of 2^K bitreversed inputs;
// pass 2 is the existing noninitial_8 starting at start_stage = K. Multi-coset
// signature shared with the compact 1-pass kernels.
monomials_to_evals_compact!(ab_monomials_to_evals_first_5_stages_compact_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_first_6_stages_compact_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_first_7_stages_compact_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_first_8_stages_compact_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_first_9_stages_compact_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_first_10_stages_compact_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_first_11_stages_compact_kernel);
monomials_to_evals_compact!(ab_monomials_to_evals_first_12_stages_compact_kernel);

pub(crate) fn evals_to_monomials_3_pass(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    columns_per_launch: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    // Column batching mirrors the forward 3-pass: the two nonfinal_8 passes use
    // `grid_dim.z` for column (.x = tiles, .y = exchange regions), the final
    // pass uses `grid_dim.y` for column (.x = blocks).
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
        let threads = 512;
        let bf_vals_per_block = 1 << 13; // 8192
        let mut start_stage = 0;
        for i in 0..2 {
            let num_exchg_regions = 1 << start_stage;
            let exchg_region_size = n >> start_stage;
            let blocks_per_exchg_region = exchg_region_size / bf_vals_per_block;
            assert_eq!(
                blocks_per_exchg_region * num_exchg_regions,
                n / bf_vals_per_block
            );
            // Flat-blockIdx.x: gridDim.x = blocks_per_exchg_region * num_exchg_regions * cols_in_chunk.
            let grid_dim: Dim3 =
                (blocks_per_exchg_region as u32 * num_exchg_regions as u32 * cols_in_chunk as u32)
                    .into();
            let config = CudaLaunchConfig::basic(grid_dim, threads as u32, stream);
            let input = if i == 0 {
                input_matrix
            } else {
                output_matrix_const
            };
            let args = StridedTilesStagesArguments::new(
                input,
                output_matrix_mut,
                log_n as i32,
                start_stage as i32,
                0,
                0,
            );
            StridedTilesStagesFunction(ab_evals_to_monomials_nonfinal_8_stages_kernel)
                .launch(&config, &args)?;
            start_stage += 8;
        }
        let threads = 256;
        let bf_vals_per_block = 1 << 13; // 8192
        let blocks = n.get_chunks_count(bf_vals_per_block);
        // Flat-blockIdx.x: gridDim.x = blocks * cols_in_chunk.
        let grid_dim_final: Dim3 = (blocks as u32 * cols_in_chunk as u32).into();
        let config = CudaLaunchConfig::basic(grid_dim_final, threads as u32, stream);
        let args = EvalsToMonomialsFinalArguments::new(
            output_matrix_const,
            output_matrix_mut,
            transposed_monomials,
            log_n as i32,
            0,
            0,
        );
        match log_n {
            21 => EvalsToMonomialsFinalFunction(ab_evals_to_monomials_final_5_stages_kernel)
                .launch(&config, &args)?,
            22 => EvalsToMonomialsFinalFunction(ab_evals_to_monomials_final_6_stages_kernel)
                .launch(&config, &args)?,
            23 => EvalsToMonomialsFinalFunction(ab_evals_to_monomials_final_7_stages_kernel)
                .launch(&config, &args)?,
            24 => EvalsToMonomialsFinalFunction(ab_evals_to_monomials_final_8_stages_kernel)
                .launch(&config, &args)?,
            _ => unreachable!(
                "NTT 3-pass evals->monomials kernels are only generated for log_n in 21..=24"
            ),
        }
        col_start += cols_in_chunk;
    }
    Ok(())
}

pub(crate) fn evals_to_monomials_2_pass(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    columns_per_launch: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    // Column batching: both passes use `grid_dim.y` for column (.x = blocks).
    // first_9/first_10 already supported grid_dim.y; last_14 picked it up in
    // Phase A.
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
        let smem_bytes = bf_vals_per_block * size_of::<BF>();
        let threads = 512;
        let blocks = n.get_chunks_count(bf_vals_per_block);
        // Flat-blockIdx.x: gridDim.x = blocks * cols_in_chunk.
        let grid_dim: Dim3 = (blocks as u32 * cols_in_chunk as u32).into();
        let mut config = CudaLaunchConfig::basic(grid_dim, threads as u32, stream);
        config.dynamic_smem_bytes = smem_bytes;
        let args = StridedTilesStagesArguments::new(
            input_matrix,
            output_matrix_mut,
            log_n as i32,
            0,
            0,
            0,
        );
        let function = match log_n {
            23 => StridedTilesStagesFunction(ab_evals_to_monomials_first_9_stages_kernel),
            24 => StridedTilesStagesFunction(ab_evals_to_monomials_first_10_stages_kernel),
            _ => unreachable!(
                "NTT 2-pass evals->monomials kernels are only generated for log_n in 23..=24"
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
        let bf_vals_per_block = 1 << 14; // 16384
        let smem_twiddles_per_block = 1 << 13; // 8192
        let smem_bytes = (bf_vals_per_block + smem_twiddles_per_block) * size_of::<BF>();
        let threads = 512;
        let blocks = n.get_chunks_count(bf_vals_per_block);
        // Flat-blockIdx.x: gridDim.x = blocks * cols_in_chunk.
        let grid_dim_last: Dim3 = (blocks as u32 * cols_in_chunk as u32).into();
        let mut config = CudaLaunchConfig::basic(grid_dim_last, threads as u32, stream);
        config.dynamic_smem_bytes = smem_bytes;
        let args = EvalsToMonomialsFinalArguments::new(
            output_matrix_const,
            output_matrix_mut,
            transposed_monomials,
            log_n as i32,
            0,
            0,
        );
        let function = EvalsToMonomialsFinalFunction(ab_evals_to_monomials_last_14_stages_kernel);
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

pub(crate) fn monomials_to_evals_3_pass(
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

pub(crate) fn monomials_to_evals_compact_1_pass(
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

pub(crate) fn monomials_to_evals_subwarp(
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

pub(crate) fn monomials_to_evals_smem_packed(
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

/// Streaming multi-coset single-column NTT for `log_n in [2, 8]`. One block
/// owns a contiguous range of cosets and walks them sequentially with a
/// register-resident running shift update `m' *= D` (where
/// `D[r] = omega^(Delta * bitrev(r))` is loop-invariant). VPT is picked from
/// `log_n` alone:
///   - `log_n in [2, 7]`: VPT=4, 16-byte vec4 store (STG.E.128). Lower
///     register pressure (32 regs/thread, 8 blocks/SM), and on sm_<90 avoids
///     the 256-bit decomposition that wipes out coalescing on Ampere/Ada.
///     A 500-iter Blackwell sweep showed VPT=4 ≥ VPT=8 across this range
///     (tied at DRAM saturation for log_n in [2, 6], ~4% faster at log_n=7).
///   - `log_n == 8`: VPT=8, 32-byte vec8 store. Required because VPT=4 there
///     would need TPC=64 > warp; the last cross-thread `__shfl_xor_sync` can't
///     reach across the warp boundary.
///
/// Callers loop over columns externally — the kernel is one column per launch,
/// the host advances `(monomials_ptr, out_ptr)` per column and uses
/// `coset_stride_bf = num_cols_per_coset_stride * trace_len` to step between
/// adjacent cosets in the output buffer.
pub(crate) fn monomials_to_evals_streaming(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    coset_index_base: usize,
    coset_factor_shift: u32,
    num_cosets: usize,
    num_cols_per_coset: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
    device_props: &DeviceProperties,
) -> CudaResult<()> {
    monomials_to_evals_streaming_impl(
        inputs_matrix,
        outputs_matrix,
        log_n,
        streaming_log_vpt_for(log_n),
        coset_index_base,
        coset_factor_shift,
        num_cosets,
        num_cols_per_coset,
        transposed_monomials,
        stream,
        device_props,
    )
}

/// VPT choice for the streaming kernel given `log_n`. VPT=8 only for
/// `log_n == 8` (cross-warp shuffle constraint); VPT=4 everywhere else.
/// Mirrored by the strategy gate.
pub(crate) fn streaming_log_vpt_for(log_n: usize) -> usize {
    if log_n == 8 {
        3
    } else {
        2
    }
}

#[cfg(test)]
pub(crate) fn monomials_to_evals_streaming_with_log_vpt(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    log_vpt: usize,
    coset_index_base: usize,
    coset_factor_shift: u32,
    num_cosets: usize,
    num_cols_per_coset: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
    device_props: &DeviceProperties,
) -> CudaResult<()> {
    monomials_to_evals_streaming_impl(
        inputs_matrix,
        outputs_matrix,
        log_n,
        log_vpt,
        coset_index_base,
        coset_factor_shift,
        num_cosets,
        num_cols_per_coset,
        transposed_monomials,
        stream,
        device_props,
    )
}

fn monomials_to_evals_streaming_impl(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    log_vpt: usize,
    coset_index_base: usize,
    coset_factor_shift: u32,
    num_cosets: usize,
    num_cols_per_coset: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
    device_props: &DeviceProperties,
) -> CudaResult<()> {
    assert!(
        (2..=8).contains(&log_n),
        "streaming NTT only supports log_n in [2, 8]"
    );
    assert!(
        log_vpt == 2 || log_vpt == 3,
        "log_vpt must be 2 (vec4) or 3 (vec8), got {log_vpt}"
    );
    assert!(
        log_vpt == 3 || log_n <= 7,
        "VPT=4 (log_vpt=2) requires log_n <= 7 (TPC must fit in a warp); got log_n={log_n}"
    );
    assert!(
        log_n >= log_vpt,
        "log_n ({log_n}) must be >= log_vpt ({log_vpt})"
    );
    assert!(
        !transposed_monomials,
        "streaming NTT does not support transposed monomials"
    );
    assert!(
        num_cosets.is_power_of_two(),
        "num_cosets must be a power of 2 (got {num_cosets})"
    );
    let n = 1usize << log_n;
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
    // TPC = 2^(log_n - log_vpt); COSETS_PER_IT = BLK / TPC with BLK = 256.
    let tpc = 1usize << (log_n - log_vpt);
    let cosets_per_it = 256 / tpc;
    assert!(
        num_cosets % cosets_per_it == 0,
        "num_cosets ({num_cosets}) must be divisible by cosets_per_it ({cosets_per_it}) at log_n={log_n}, log_vpt={log_vpt}",
    );
    let total_iters = num_cosets / cosets_per_it;
    // Block budget: a single SM-batch (sm_count blocks) is enough for the
    // streaming loop to amortize setup; in production num_cosets is large so
    // each block runs many iterations regardless. Cap at total_iters to avoid
    // empty trailing blocks.
    let blocks_per_sm_target = 4usize;
    let grid_blocks = (device_props.sm_count * blocks_per_sm_target)
        .min(total_iters)
        .max(1);
    let function = match (log_vpt, log_n) {
        (3, 3) => MonomialsToEvalsStreamingFunction(ab_monomials_to_evals_streaming_v8_3_stages_kernel),
        (3, 4) => MonomialsToEvalsStreamingFunction(ab_monomials_to_evals_streaming_v8_4_stages_kernel),
        (3, 5) => MonomialsToEvalsStreamingFunction(ab_monomials_to_evals_streaming_v8_5_stages_kernel),
        (3, 6) => MonomialsToEvalsStreamingFunction(ab_monomials_to_evals_streaming_v8_6_stages_kernel),
        (3, 7) => MonomialsToEvalsStreamingFunction(ab_monomials_to_evals_streaming_v8_7_stages_kernel),
        (3, 8) => MonomialsToEvalsStreamingFunction(ab_monomials_to_evals_streaming_v8_8_stages_kernel),
        (2, 2) => MonomialsToEvalsStreamingFunction(ab_monomials_to_evals_streaming_v4_2_stages_kernel),
        (2, 3) => MonomialsToEvalsStreamingFunction(ab_monomials_to_evals_streaming_v4_3_stages_kernel),
        (2, 4) => MonomialsToEvalsStreamingFunction(ab_monomials_to_evals_streaming_v4_4_stages_kernel),
        (2, 5) => MonomialsToEvalsStreamingFunction(ab_monomials_to_evals_streaming_v4_5_stages_kernel),
        (2, 6) => MonomialsToEvalsStreamingFunction(ab_monomials_to_evals_streaming_v4_6_stages_kernel),
        (2, 7) => MonomialsToEvalsStreamingFunction(ab_monomials_to_evals_streaming_v4_7_stages_kernel),
        _ => unreachable!("streaming kernels: log_vpt in {{2, 3}} and log_n in [2, 8] (VPT=4 excludes log_n=8, VPT=8 requires log_n >= 3); got log_vpt={log_vpt}, log_n={log_n}"),
    };
    let input_stride = inputs_matrix.stride();
    let input_offset = inputs_matrix.offset();
    let output_stride = outputs_matrix.stride();
    let output_offset = outputs_matrix.offset();
    // Inputs and outputs are column-major: column k starts at offset
    // `k * stride + offset` in BFs. The kernel sees per-column slices; the
    // output's adjacent cosets sit `num_cols_per_coset * output_stride` BFs
    // apart (output_stride == trace_len for the typical caller).
    let coset_stride_bf = (num_cols_per_coset as u64) * (output_stride as u64);
    let inputs_slice = inputs_matrix.slice();
    let outputs_slice_mut = outputs_matrix.slice_mut();
    let grid_dim: Dim3 = (grid_blocks as u32).into();
    let block_dim: Dim3 = 256u32.into();
    for col in 0..num_ntts {
        let mono_start = col * input_stride + input_offset;
        let monomials_ptr = unsafe { inputs_slice.as_ptr().add(mono_start) };
        let out_start = col * output_stride + output_offset;
        let out_ptr = unsafe { outputs_slice_mut.as_mut_ptr().add(out_start) };
        let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
        let args = MonomialsToEvalsStreamingArguments::new(
            monomials_ptr,
            out_ptr,
            coset_index_base as i32,
            coset_factor_shift as i32,
            num_cosets as u32,
            coset_stride_bf,
        );
        function.launch(&config, &args)?;
    }
    Ok(())
}

pub(crate) fn monomials_to_evals_2_pass_compact_initial(
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

pub(crate) fn monomials_to_evals_2_pass(
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
                "NTT 3-pass bitreversed->natural kernels are only generated for log_n in 21..=24"
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

/// Multi-coset variant of `bitreversed_monomials_to_natural_evals`.
///
/// Runs the same forward NTT across `num_cosets` consecutive cosets starting
/// at `coset_index_base`. For the compact 1-pass range (`log_n <= 12`) all
/// cosets are batched into one launch via `gridDim.x`, eliminating the
/// per-coset launch overhead that previously dominated small-`log_n` work. For
/// larger `log_n` (2-pass-compact-initial, 3-pass forward) cosets are batched
/// up to the L2-pressure cap from the strategy.
///
/// Output layout: coset-major outer, column-major inner. Coset k's columns
/// occupy `outputs[(k * num_cols_per_coset_stride + col) * trace_len ..]` for
/// col in `[0, inputs_matrix.cols())`. When `num_cols_per_coset_stride ==
/// inputs_matrix.cols()` (the typical case) cosets sit back-to-back; setting
/// it larger leaves gaps between cosets (used by the base-trace LDE caller
/// to write directly into a `[coset][col][trace_len]` trace-holder backing
/// where col here is a per-column NTT inside an outer column loop).
#[allow(dead_code)]
pub(crate) fn bitreversed_monomials_to_natural_evals_multi_coset(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs: &mut DeviceSlice<BF>,
    log_n: usize,
    log_lde_factor: usize,
    coset_index_base: usize,
    num_cosets: usize,
    num_cols_per_coset_stride: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
    device_properties: &DeviceProperties,
) -> CudaResult<()> {
    assert!(
        log_n + log_lde_factor <= OMEGA_LOG_ORDER as usize,
        "log_n ({log_n}) + log_lde_factor ({log_lde_factor}) > OMEGA_LOG_ORDER ({OMEGA_LOG_ORDER})",
    );
    assert!(num_cosets >= 1);
    assert!(
        num_cosets.is_power_of_two(),
        "num_cosets must be a power of 2 (got {num_cosets})"
    );
    assert!(coset_index_base + num_cosets <= (1usize << log_lde_factor));
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
        false,
        device_properties,
    )
    .unwrap_or_else(|e| unreachable!("forward strategy unavailable: {e:?}"));
    debug_assert!(!strategy.passes.is_empty());
    let coset_factor_shift = (OMEGA_LOG_ORDER as usize - log_n - log_lde_factor) as u32;
    // Compact 1-pass (log_n in [4, 12]) and 2-pass-compact-initial (log_n in
    // [13, 20]) kernel families now consume cosets_per_launch directly. Other
    // ranges fall back to a per-coset loop until B4/B5 flip their kernels.
    if strategy.passes.len() == 1 {
        let mut outputs_matrix = DeviceMatrixMut::new(outputs, trace_len);
        return match strategy.passes[0].kernel {
            super::NttKernelKind::MonomialsToEvalsStreaming { .. } => monomials_to_evals_streaming(
                inputs_matrix,
                &mut outputs_matrix,
                log_n,
                coset_index_base,
                coset_factor_shift,
                num_cosets,
                num_cols_per_coset_stride,
                transposed_monomials,
                stream,
                device_properties,
            ),
            super::NttKernelKind::MonomialsToEvalsSubwarp {
                log_instances_per_block,
                ..
            } => monomials_to_evals_subwarp(
                inputs_matrix,
                &mut outputs_matrix,
                log_n,
                coset_index_base,
                coset_factor_shift,
                num_cosets,
                num_cols_per_coset_stride,
                log_instances_per_block,
                transposed_monomials,
                stream,
            ),
            super::NttKernelKind::MonomialsToEvalsSmemPacked {
                log_instances_per_block,
                ..
            } => monomials_to_evals_smem_packed(
                inputs_matrix,
                &mut outputs_matrix,
                log_n,
                coset_index_base,
                coset_factor_shift,
                num_cosets,
                num_cols_per_coset_stride,
                log_instances_per_block,
                transposed_monomials,
                stream,
            ),
            _ => monomials_to_evals_compact_1_pass(
                inputs_matrix,
                &mut outputs_matrix,
                log_n,
                coset_index_base,
                coset_factor_shift,
                num_cosets,
                num_cols_per_coset_stride,
                strategy.columns_per_launch,
                transposed_monomials,
                stream,
            ),
        };
    }
    if strategy.passes.len() == 2
        && matches!(
            strategy.passes[0].kernel,
            super::NttKernelKind::MonomialsToEvalsFirstCompact { .. }
        )
    {
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
            transposed_monomials,
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
            stream,
            &strategy,
            device_properties,
        )?;
    }
    Ok(())
}

#[allow(dead_code)]
pub(crate) fn bitreversed_monomials_to_natural_evals(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    log_lde_factor: usize,
    coset_index: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
    device_properties: &DeviceProperties,
) -> CudaResult<()> {
    // The LDE domain must fit in BabyBear's 2-adicity. Multi-stage kernels'
    // coset-shift path computes `bitrev(row, log_n) * coset_factor_power`
    // (with `coset_factor_power = coset_index << (OMEGA_LOG_ORDER - log_n -
    // log_lde_factor)`) and looks it up in `ab_ntt_forward_powers`, which
    // decodes exponents in `[0, 2^OMEGA_LOG_ORDER)`. `log_n + log_lde_factor
    // > OMEGA_LOG_ORDER` would also imply a negative shift in
    // `coset_factor_power`, which is undefined.
    assert!(
        log_n + log_lde_factor <= OMEGA_LOG_ORDER as usize,
        "log_n ({log_n}) + log_lde_factor ({log_lde_factor}) > OMEGA_LOG_ORDER ({OMEGA_LOG_ORDER})",
    );
    assert!(coset_index < (1usize << log_lde_factor));
    let cols = inputs_matrix.cols();
    match super::select_ntt_strategy(
        super::NttDirection::Forward,
        log_n,
        cols,
        1,
        false,
        device_properties,
    ) {
        Ok(strategy) => dispatch_strategy(
            inputs_matrix,
            outputs_matrix,
            log_n,
            log_lde_factor,
            coset_index,
            transposed_monomials,
            stream,
            &strategy,
            device_properties,
        ),
        Err(super::NttStrategyError::LogNBelowSupported {
            log_n: bad_log_n,
            min_supported,
        }) => {
            unreachable!(
                "bitreversed_monomials_to_natural_evals called with log_n={bad_log_n} \
                 below MIN_SUPPORTED_LOG_N={min_supported}; log_n=0 is the only \
                 unsupported size (identity NTT = host memcpy, handled by callers)"
            )
        }
    }
}

fn dispatch_strategy(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    log_lde_factor: usize,
    coset_index: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
    strategy: &super::NttStrategy,
    device_properties: &DeviceProperties,
) -> CudaResult<()> {
    let coset_factor_shift = (OMEGA_LOG_ORDER as usize - log_n - log_lde_factor) as u32;
    let coset_factor_power = coset_index << coset_factor_shift;
    // Single-coset dispatch: pass num_cols_per_coset = inputs_matrix.cols()
    // (the contiguous default). The multi-coset entry overrides this when the
    // output buffer is strided.
    let num_cols_per_coset = inputs_matrix.cols();
    debug_assert!(!strategy.passes.is_empty());
    debug_assert_eq!(
        strategy.passes.iter().map(|p| p.stage_count).sum::<usize>(),
        log_n,
    );
    match strategy.passes.len() {
        1 => match strategy.passes[0].kernel {
            super::NttKernelKind::MonomialsToEvalsStreaming { .. } => monomials_to_evals_streaming(
                inputs_matrix,
                outputs_matrix,
                log_n,
                coset_index,
                coset_factor_shift,
                1,
                num_cols_per_coset,
                transposed_monomials,
                stream,
                device_properties,
            ),
            super::NttKernelKind::MonomialsToEvalsSubwarp {
                log_instances_per_block,
                ..
            } => monomials_to_evals_subwarp(
                inputs_matrix,
                outputs_matrix,
                log_n,
                coset_index,
                coset_factor_shift,
                1,
                num_cols_per_coset,
                log_instances_per_block,
                transposed_monomials,
                stream,
            ),
            super::NttKernelKind::MonomialsToEvalsSmemPacked {
                log_instances_per_block,
                ..
            } => monomials_to_evals_smem_packed(
                inputs_matrix,
                outputs_matrix,
                log_n,
                coset_index,
                coset_factor_shift,
                1,
                num_cols_per_coset,
                log_instances_per_block,
                transposed_monomials,
                stream,
            ),
            _ => monomials_to_evals_compact_1_pass(
                inputs_matrix,
                outputs_matrix,
                log_n,
                coset_index,
                coset_factor_shift,
                1,
                num_cols_per_coset,
                strategy.columns_per_launch,
                transposed_monomials,
                stream,
            ),
        },
        2 => match strategy.passes[0].kernel {
            super::NttKernelKind::MonomialsToEvalsFirstCompact { .. } => {
                monomials_to_evals_2_pass_compact_initial(
                    inputs_matrix,
                    outputs_matrix,
                    log_n,
                    coset_index,
                    coset_factor_shift,
                    1,
                    num_cols_per_coset,
                    1,
                    strategy.columns_per_launch,
                    transposed_monomials,
                    stream,
                )
            }
            _ => monomials_to_evals_2_pass(
                inputs_matrix,
                outputs_matrix,
                log_n,
                coset_factor_power,
                strategy.columns_per_launch,
                transposed_monomials,
                stream,
            ),
        },
        3 => monomials_to_evals_3_pass(
            inputs_matrix,
            outputs_matrix,
            log_n,
            coset_index,
            coset_factor_shift,
            1,
            num_cols_per_coset,
            1,
            strategy.columns_per_launch,
            transposed_monomials,
            stream,
        ),
        n => unreachable!("NTT strategy emits 1, 2, or 3 passes, got {n}"),
    }
}

#[allow(dead_code)]
pub(crate) fn natural_evals_to_bitreversed_monomials(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
    device_properties: &DeviceProperties,
) -> CudaResult<()> {
    assert!(log_n <= OMEGA_LOG_ORDER as usize);
    if log_n < MIN_LOG_N_FOR_MULTISTAGE_KERNELS {
        // Fallback (uses 1 stage at a time kernels)
        assert!(
            !transposed_monomials,
            "fallback path does not support transposed monomials",
        );
        let cols = inputs_matrix.cols();
        let rows = inputs_matrix.rows();
        assert_eq!(cols, outputs_matrix.cols());
        assert_eq!(rows, outputs_matrix.rows());
        let inputs_stride = inputs_matrix.stride();
        let outputs_stride = outputs_matrix.stride();
        let inputs_offset = inputs_matrix.offset();
        let outputs_offset = outputs_matrix.offset();
        let inputs_slice = &(inputs_matrix.slice())[inputs_offset..];
        let outputs_slice = &mut (outputs_matrix.slice_mut())[outputs_offset..];
        for col in 0..cols {
            natural_evals_to_bitreversed_coeffs(
                &inputs_slice[col * inputs_stride..col * inputs_stride + rows],
                &mut outputs_slice[col * outputs_stride..col * outputs_stride + rows],
                log_n,
                stream,
            )?;
        }
        return Ok(());
    }
    // Inverse strategy emits a 2-pass plan when a column exceeds L2 (log_n >=
    // 23 on L4-class devices) and a 3-pass plan otherwise; `columns_per_launch`
    // is the L2-aware clamp shared with the forward path.
    let num_cols = outputs_matrix.cols();
    let strategy = super::select_ntt_strategy(
        super::NttDirection::Inverse,
        log_n,
        num_cols,
        1,
        false,
        device_properties,
    )
    .unwrap_or_else(|e| {
        unreachable!(
            "natural_evals_to_bitreversed_monomials called with log_n={log_n} below \
             inverse strategy's MULTIPASS_MIN_LOG_N (multistage fallback above should \
             have caught log_n < {}): {:?}",
            MIN_LOG_N_FOR_MULTISTAGE_KERNELS, e
        )
    });
    debug_assert_eq!(
        strategy.passes.iter().map(|p| p.stage_count).sum::<usize>(),
        log_n,
    );
    match strategy.passes.len() {
        2 => evals_to_monomials_2_pass(
            inputs_matrix,
            outputs_matrix,
            log_n,
            strategy.columns_per_launch,
            transposed_monomials,
            stream,
        )?,
        3 => evals_to_monomials_3_pass(
            inputs_matrix,
            outputs_matrix,
            log_n,
            strategy.columns_per_launch,
            transposed_monomials,
            stream,
        )?,
        n => unreachable!("inverse NTT strategy emits 2 or 3 passes, got {n}"),
    }
    Ok(())
}
