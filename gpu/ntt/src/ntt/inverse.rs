#![allow(non_snake_case)]

use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use super::kernels::*;
use super::shared;
use gpu_core::primitives::device_structures::{
    DeviceMatrixChunk, DeviceMatrixChunkImpl, DeviceMatrixChunkMut, DeviceMatrixChunkMutImpl,
};
use gpu_core::primitives::field::BaseField;
use gpu_core::primitives::utils::GetChunksCount;

use std::mem::size_of;

type BF = BaseField;

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
    shared::assert_ntt_16b_aligned(inputs_matrix, outputs_matrix);
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
    let n = 1 << log_n;
    assert_eq!(inputs_matrix.rows(), n);
    assert_eq!(outputs_matrix.rows(), n);
    shared::assert_ntt_16b_aligned(inputs_matrix, outputs_matrix);
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
        shared::set_max_dynamic_smem(&function, smem_bytes)?;
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
        shared::set_max_dynamic_smem(&function, smem_bytes)?;
        function.launch(&config, &args)?;
        col_start += cols_in_chunk;
    }
    Ok(())
}
