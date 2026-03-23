#![allow(non_snake_case)]

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart_sys::{cudaFuncSetAttribute, CudaFuncAttribute};

use super::{
    bitreversed_coeffs_to_natural_coset, hypercube_evals_natural_to_bitreversed_coeffs,
    MIN_LOG_N_FOR_MULTISTAGE_KERNELS,
};

use crate::device_structures::{
    DeviceMatrixChunk, DeviceMatrixChunkImpl, DeviceMatrixChunkMut, DeviceMatrixChunkMutImpl,
    MutPtrAndStride, PtrAndStride,
};
use crate::field::BaseField;
use crate::primitives::context::DeviceProperties;
use crate::primitives::device_context::OMEGA_LOG_ORDER;
use crate::utils::GetChunksCount;

use std::mem::size_of;

type BF = BaseField;

cuda_kernel!(
    StridedTilesStages,
    strided_tiles_stages,
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    log_n: i32,
    start_stage: i32,
);

// 2-pass evals to monomials
strided_tiles_stages!(ab_hypercube_evals_to_monomials_first_9_stages_kernel);
strided_tiles_stages!(ab_hypercube_evals_to_monomials_first_10_stages_kernel);

// 3-pass evals to monomials
strided_tiles_stages!(ab_hypercube_evals_to_monomials_nonfinal_8_stages_kernel);

cuda_kernel!(
    EvalsToMonomialsFinal,
    hypercube_evals_to_monomials_final,
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    transposed_monomials: bool,
    log_n: i32,
);

// 2-pass evals to monomials
hypercube_evals_to_monomials_final!(ab_hypercube_evals_to_monomials_last_14_stages_kernel);

// 3-pass evals to monomials
hypercube_evals_to_monomials_final!(ab_hypercube_evals_to_monomials_final_5_stages_kernel);
hypercube_evals_to_monomials_final!(ab_hypercube_evals_to_monomials_final_6_stages_kernel);
hypercube_evals_to_monomials_final!(ab_hypercube_evals_to_monomials_final_7_stages_kernel);
hypercube_evals_to_monomials_final!(ab_hypercube_evals_to_monomials_final_8_stages_kernel);

pub(crate) fn hypercube_evals_to_monomials_3_pass(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
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
    let num_ntts = outputs_matrix.cols();
    let inputs_slice = inputs_matrix.slice();
    let stride = outputs_matrix.stride();
    let offset = outputs_matrix.offset();
    let outputs_slice_const = unsafe {
        DeviceSlice::from_raw_parts(
            outputs_matrix.slice().as_ptr(),
            outputs_matrix.slice().len(),
        )
    };
    let outputs_slice_mut = outputs_matrix.slice_mut();
    // Work on 1 column at a time to leverage whatever L2 persistence we can
    for col in 0..num_ntts {
        let range = col * stride..(col + 1) * stride;
        let input_slice = &inputs_slice[range.clone()];
        let output_slice_const = &outputs_slice_const[range.clone()];
        let output_slice_mut = &mut outputs_slice_mut[range.clone()];
        let input_matrix = DeviceMatrixChunk::new(input_slice, stride, offset, n);
        let output_matrix_const = DeviceMatrixChunk::new(output_slice_const, stride, offset, n);
        let mut output_matrix_mut = DeviceMatrixChunkMut::new(output_slice_mut, stride, offset, n);
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
            let mut grid_dim: Dim3 = (blocks_per_exchg_region as u32).into();
            grid_dim.y = num_exchg_regions as u32;
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
            );
            StridedTilesStagesFunction(ab_hypercube_evals_to_monomials_nonfinal_8_stages_kernel)
                .launch(&config, &args)?;
            start_stage += 8;
        }
        let threads = 256;
        let bf_vals_per_block = 1 << 13; // 8192
        let blocks = n.get_chunks_count(bf_vals_per_block);
        let config = CudaLaunchConfig::basic(blocks as u32, threads as u32, stream);
        let args = EvalsToMonomialsFinalArguments::new(
            output_matrix_const,
            output_matrix_mut,
            transposed_monomials,
            log_n as i32,
        );
        match log_n {
            21 => {
                EvalsToMonomialsFinalFunction(ab_hypercube_evals_to_monomials_final_5_stages_kernel)
                    .launch(&config, &args)?
            }
            22 => {
                EvalsToMonomialsFinalFunction(ab_hypercube_evals_to_monomials_final_6_stages_kernel)
                    .launch(&config, &args)?
            }
            23 => {
                EvalsToMonomialsFinalFunction(ab_hypercube_evals_to_monomials_final_7_stages_kernel)
                    .launch(&config, &args)?
            }
            24 => {
                EvalsToMonomialsFinalFunction(ab_hypercube_evals_to_monomials_final_8_stages_kernel)
                    .launch(&config, &args)?
            }
            _ => unimplemented!(),
        }
    }
    Ok(())
}

pub(crate) fn hypercube_evals_to_monomials_2_pass(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
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
    let num_ntts = outputs_matrix.cols();
    let inputs_slice = inputs_matrix.slice();
    let stride = outputs_matrix.stride();
    let offset = outputs_matrix.offset();
    let outputs_slice_const = unsafe {
        DeviceSlice::from_raw_parts(
            outputs_matrix.slice().as_ptr(),
            outputs_matrix.slice().len(),
        )
    };
    let outputs_slice_mut = outputs_matrix.slice_mut();
    // Work on 1 column at a time to leverage whatever L2 persistence we can
    for col in 0..num_ntts {
        let range = col * stride..(col + 1) * stride;
        let input_slice = &inputs_slice[range.clone()];
        let output_slice_const = &outputs_slice_const[range.clone()];
        let output_slice_mut = &mut outputs_slice_mut[range.clone()];
        let input_matrix = DeviceMatrixChunk::new(input_slice, stride, offset, n);
        let output_matrix_const = DeviceMatrixChunk::new(output_slice_const, stride, offset, n);
        let mut output_matrix_mut = DeviceMatrixChunkMut::new(output_slice_mut, stride, offset, n);
        let input_matrix = input_matrix.as_ptr_and_stride();
        let output_matrix_const = output_matrix_const.as_ptr_and_stride();
        let output_matrix_mut = output_matrix_mut.as_mut_ptr_and_stride();
        let bf_vals_per_block = 1 << 14; // 16384
        let smem_bytes = bf_vals_per_block * size_of::<BF>();
        let threads = 512;
        let blocks = n.get_chunks_count(bf_vals_per_block);
        let mut grid_dim: Dim3 = (blocks as u32).into();
        grid_dim.y = 1;
        let mut config = CudaLaunchConfig::basic(grid_dim, threads as u32, stream);
        config.dynamic_smem_bytes = smem_bytes;
        let args =
            StridedTilesStagesArguments::new(input_matrix, output_matrix_mut, log_n as i32, 0);
        let function = match log_n {
            23 => StridedTilesStagesFunction(ab_hypercube_evals_to_monomials_first_9_stages_kernel),
            24 => {
                StridedTilesStagesFunction(ab_hypercube_evals_to_monomials_first_10_stages_kernel)
            }
            _ => unimplemented!(),
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
        let smem_bytes = bf_vals_per_block * size_of::<BF>();
        let threads = 512;
        let blocks = n.get_chunks_count(bf_vals_per_block);
        let mut config = CudaLaunchConfig::basic(blocks as u32, threads as u32, stream);
        config.dynamic_smem_bytes = smem_bytes;
        let args = EvalsToMonomialsFinalArguments::new(
            output_matrix_const,
            output_matrix_mut,
            transposed_monomials,
            log_n as i32,
        );
        let function =
            EvalsToMonomialsFinalFunction(ab_hypercube_evals_to_monomials_last_14_stages_kernel);
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
    }
    Ok(())
}

#[allow(unused)]
pub fn hypercube_natural_evals_to_bitreversed_monomials(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
    device_properties: &DeviceProperties,
) -> CudaResult<()> {
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
            hypercube_evals_natural_to_bitreversed_coeffs(
                &inputs_slice[col * inputs_stride..col * inputs_stride + rows],
                &mut outputs_slice[col * outputs_stride..col * outputs_stride + rows],
                log_n,
                stream,
            )?;
        }
        return Ok(());
    }
    // Quick and dirty heuristic: use 3-pass if one column fits in L2, 2-pass otherwise
    let l2_bytes = device_properties.l2_cache_size_bytes;
    let column_bytes = (1 << log_n) * size_of::<BF>();
    if (column_bytes >= l2_bytes) && (log_n >= 23) {
        hypercube_evals_to_monomials_2_pass(
            inputs_matrix,
            outputs_matrix,
            log_n,
            transposed_monomials,
            stream,
        )?;
    } else {
        hypercube_evals_to_monomials_3_pass(
            inputs_matrix,
            outputs_matrix,
            log_n,
            transposed_monomials,
            stream,
        )?;
    }
    Ok(())
}
