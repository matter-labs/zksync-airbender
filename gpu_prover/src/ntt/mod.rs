#![allow(non_snake_case)]

pub mod utils;

#[cfg(test)]
pub mod tests;

use era_cudart::cuda_kernel;
use era_cudart::error::get_last_error;
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::{CudaStream, CudaStreamWaitEventFlags};

use crate::context::OMEGA_LOG_ORDER;
use crate::device_structures::{
    DeviceMatrixChunk, DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride,
    PtrAndStride,
};
use crate::field::BaseField;
use crate::ntt::utils::{
    COMPLEX_COLS_PER_BLOCK, get_main_to_coset_launch_chain, STAGE_PLANS_B2N, STAGE_PLANS_N2B
};
use crate::utils::GetChunksCount;

use itertools::Itertools;

cuda_kernel!(
    B2NOneStage,
    b2n_one_stage_kernel,
    inputs_matrix: PtrAndStride<BaseField>,
    outputs_matrix: MutPtrAndStride<BaseField>,
    start_stage: u32,
    log_n: u32,
    blocks_per_ntt: u32,
    log_extension_degree: u32,
    coset_idx: u32,
);

b2n_one_stage_kernel!(bitrev_Z_to_natural_coset_evals_1_stage);

// "v" indicates a vectorized layout of BaseField columns,
// For the final output, columns represent distinct base field values.
// For intermediate outputs, each pair of columns represents the c0s and c1s
// of a single column of complex values.
cuda_kernel!(
    B2NMultiStage,
    b2n_multi_stage_kernel,
    inputs_matrix: PtrAndStride<BaseField>,
    outputs_matrix: MutPtrAndStride<BaseField>,
    start_stage: u32,
    stages_this_launch: u32,
    log_n: u32,
    num_Z_cols: u32,
    log_extension_degree: u32,
    coset_idx: u32,
);

b2n_multi_stage_kernel!(bitrev_Z_to_natural_coset_evals_noninitial_7_or_8_stages_block);
b2n_multi_stage_kernel!(bitrev_Z_to_natural_coset_evals_initial_7_stages_warp);
b2n_multi_stage_kernel!(bitrev_Z_to_natural_coset_evals_initial_8_stages_warp);
b2n_multi_stage_kernel!(bitrev_Z_to_natural_coset_evals_initial_9_to_12_stages_block);

#[allow(clippy::too_many_arguments)]
fn bitrev_Z_to_natural_evals(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BaseField> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BaseField> + ?Sized),
    log_n: usize,
    num_bf_cols: usize,
    log_extension_degree: usize,
    coset_idx: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(log_n >= 1);
    assert!(log_n <= OMEGA_LOG_ORDER as usize);
    assert_eq!(num_bf_cols % 2, 0);
    let n = 1 << log_n;
    let num_Z_cols = (num_bf_cols / 2) as u32;
    assert_eq!(inputs_matrix.rows(), n);
    assert_eq!(inputs_matrix.cols(), num_bf_cols);
    assert_eq!(outputs_matrix.rows(), n);
    assert_eq!(outputs_matrix.cols(), num_bf_cols);
    let log_n = log_n as u32;
    let n = n as u32;

    let inputs_matrix = inputs_matrix.as_ptr_and_stride();
    let outputs_matrix_const = outputs_matrix.as_ptr_and_stride();
    let outputs_matrix_mut = outputs_matrix.as_mut_ptr_and_stride();

    // The following bound is overly conservative, since technically the GPU-side
    // 3-layer power caches support powers as fine-grained as CIRCLE_GROUP_LOG_ORDER.
    // Therefore, the assert may fire for some sizes/LDE degrees that could technically work,
    // but are bigger than we expect. Its purpose is to remind us to revisit the logic
    // in such unexpected cases (and relax the bound if the new cases are legitimate).
    assert!(log_n + (log_extension_degree as u32) < OMEGA_LOG_ORDER);

    // The log_n < 16 path isn't performant, and is meant to unblock
    // small proofs for debugging purposes only.
    if log_n < 16 {
        let threads: u32 = 128;
        let n: u32 = 1 << log_n;
        let blocks_per_ntt: u32 = n.get_chunks_count(2 * threads);
        let blocks = blocks_per_ntt * num_Z_cols;
        let config = CudaLaunchConfig::basic(blocks, threads, stream);
        let kernel_function = B2NOneStageFunction(bitrev_Z_to_natural_coset_evals_1_stage);
        let args = B2NOneStageArguments::new(
            inputs_matrix,
            outputs_matrix_mut,
            0,
            log_n,
            blocks_per_ntt,
            log_extension_degree as u32,
            coset_idx as u32,
        );
        kernel_function.launch(&config, &args)?;
        for stage in 1..log_n {
            let args = B2NOneStageArguments::new(
                outputs_matrix_const,
                outputs_matrix_mut,
                stage,
                log_n,
                blocks_per_ntt,
                log_extension_degree as u32,
                coset_idx as u32,
            );
            kernel_function.launch(&config, &args)?;
        }
        return Ok(());
    }

    use crate::ntt::utils::B2N_LAUNCH::*;
    let plan = &STAGE_PLANS_B2N[log_n as usize - 16];
    let mut stage: u32 = 0;
    for &kernel in &plan[..] {
        let start_stage = stage;
        let num_chunks = num_Z_cols.get_chunks_count(COMPLEX_COLS_PER_BLOCK);
        if let Some((kern, stages_this_launch)) = kernel {
            stage += stages_this_launch;
            let (function, grid_dim_x, block_dim_x): (B2NMultiStageSignature, u32, u32) = match kern {
                INITIAL_7_WARP => (
                    bitrev_Z_to_natural_coset_evals_initial_7_stages_warp,
                    n / (4 * 128),
                    128,
                ),
                INITIAL_8_WARP => (
                    bitrev_Z_to_natural_coset_evals_initial_8_stages_warp,
                    n / (4 * 256),
                    128,
                ),
                INITIAL_9_TO_12_BLOCK => (
                    bitrev_Z_to_natural_coset_evals_initial_9_to_12_stages_block,
                    n / 4096,
                    512,
                ),
                NONINITIAL_7_OR_8_BLOCK => (
                    bitrev_Z_to_natural_coset_evals_noninitial_7_or_8_stages_block,
                    n / 4096,
                    512,
                ),
            };
            let inputs = if start_stage == 0 {
                inputs_matrix
            } else {
                outputs_matrix_const
            };
            let config = CudaLaunchConfig::basic((grid_dim_x, num_chunks), block_dim_x, stream);
            let args = B2NMultiStageArguments::new(
                inputs,
                outputs_matrix_mut,
                start_stage,
                stages_this_launch,
                log_n,
                num_Z_cols,
                log_extension_degree as u32,
                coset_idx as u32,
            );
            B2NMultiStageFunction(function).launch(&config, &args)
        } else {
            get_last_error().wrap()
        }?;
    }
    assert_eq!(stage, log_n);
    get_last_error().wrap()
}

#[allow(clippy::too_many_arguments)]
pub fn bitrev_Z_to_natural_trace_coset_evals(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BaseField> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BaseField> + ?Sized),
    log_n: usize,
    num_bf_cols: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    bitrev_Z_to_natural_evals(
        inputs_matrix,
        outputs_matrix,
        log_n,
        num_bf_cols,
        1,
        1,
        stream,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn bitrev_Z_to_natural_composition_main_evals(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BaseField> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BaseField> + ?Sized),
    log_n: usize,
    num_bf_cols: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    bitrev_Z_to_natural_evals(
        inputs_matrix,
        outputs_matrix,
        log_n,
        num_bf_cols,
        1,
        0,
        stream,
    )
}

cuda_kernel!(
    N2BOneStageKernel,
    one_stage_kernel,
    inputs_matrix: PtrAndStride<BaseField>,
    outputs_matrix: MutPtrAndStride<BaseField>,
    start_stage: u32,
    log_n: u32,
    blocks_per_ntt: u32,
    evals_are_coset: bool,
);

one_stage_kernel!(evals_to_Z_one_stage);

cuda_kernel!(
    N2BMultiStage,
    n2b_multi_stage_kernel,
    inputs_matrix: PtrAndStride<BaseField>,
    outputs_matrix: MutPtrAndStride<BaseField>,
    start_stage: u32,
    stages_this_launch: u32,
    log_n: u32,
    num_Z_cols: u32,
);

n2b_multi_stage_kernel!(evals_to_Z_nonfinal_7_or_8_stages_block);
n2b_multi_stage_kernel!(main_domain_evals_to_Z_final_7_stages_warp);
n2b_multi_stage_kernel!(main_domain_evals_to_Z_final_8_stages_warp);
n2b_multi_stage_kernel!(main_domain_evals_to_Z_final_9_to_12_stages_block);
n2b_multi_stage_kernel!(coset_evals_to_Z_final_7_stages_warp);
n2b_multi_stage_kernel!(coset_evals_to_Z_final_8_stages_warp);
n2b_multi_stage_kernel!(coset_evals_to_Z_final_9_to_12_stages_block);

#[allow(clippy::too_many_arguments)]
fn natural_evals_to_bitrev_Z(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BaseField> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BaseField> + ?Sized),
    log_n: usize,
    num_bf_cols: usize,
    evals_are_coset: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(log_n >= 1);
    assert!(log_n <= OMEGA_LOG_ORDER as usize);
    assert_eq!(num_bf_cols % 2, 0);
    let n = 1 << log_n;
    let num_Z_cols = (num_bf_cols / 2) as u32;
    assert_eq!(inputs_matrix.rows(), n);
    assert_eq!(inputs_matrix.cols(), num_bf_cols);
    assert_eq!(outputs_matrix.rows(), n);
    assert_eq!(outputs_matrix.cols(), num_bf_cols);
    let log_n = log_n as u32;
    let n = n as u32;

    let inputs_matrix = inputs_matrix.as_ptr_and_stride();
    let outputs_matrix_const = outputs_matrix.as_ptr_and_stride();
    let outputs_matrix_mut = outputs_matrix.as_mut_ptr_and_stride();

    // The log_n < 16 path isn't performant, and is meant to unblock
    // small proofs for debugging purposes only.
    if log_n < 16 {
        let threads = 128;
        let blocks_per_ntt = (n + 2 * threads - 1) / (2 * threads);
        let blocks = blocks_per_ntt * num_Z_cols;
        let config = CudaLaunchConfig::basic(blocks, threads, stream);
        let kernel_function = N2BOneStageKernelFunction(evals_to_Z_one_stage);
        let args = N2BOneStageKernelArguments::new(
            inputs_matrix,
            outputs_matrix_mut,
            0,
            log_n,
            blocks_per_ntt,
            evals_are_coset,
        );
        kernel_function.launch(&config, &args)?;
        for stage in 1..log_n {
            let args = N2BOneStageKernelArguments::new(
                outputs_matrix_const,
                outputs_matrix_mut,
                stage,
                log_n,
                blocks_per_ntt,
                evals_are_coset,
            );
            kernel_function.launch(&config, &args)?;
        }
        return Ok(());
    }

    use crate::ntt::utils::N2B_LAUNCH::*;
    let plan = &STAGE_PLANS_N2B[log_n as usize - 16];
    let (kern, stages_this_launch) = plan[0].expect("plan must contain at least 1 kernel");
    assert_eq!(kern, NONFINAL_7_OR_8_BLOCK);
    let num_chunks = (num_Z_cols + COMPLEX_COLS_PER_BLOCK - 1) / COMPLEX_COLS_PER_BLOCK;
    let grid_dim_x = n / 4096;
    let block_dim_x = 512;
    let config = CudaLaunchConfig::basic((grid_dim_x, num_chunks), block_dim_x, stream);
    let args = N2BMultiStageArguments::new(
        inputs_matrix,
        outputs_matrix_mut,
        0,
        stages_this_launch,
        log_n,
        num_Z_cols,
    );
    N2BMultiStageFunction(evals_to_Z_nonfinal_7_or_8_stages_block).launch(&config, &args)?;
    let mut stage = stages_this_launch;
    for &kernel in &plan[1..] {
        let start_stage = stage;
        let num_chunks = (num_Z_cols + COMPLEX_COLS_PER_BLOCK - 1) / COMPLEX_COLS_PER_BLOCK;
        if let Some((kern, stages_this_launch)) = kernel {
            stage += stages_this_launch;
            let (function, grid_dim_x, block_dim_x): (N2BMultiStageSignature, u32, u32) =
                match kern {
                    FINAL_7_WARP => (
                        if evals_are_coset {
                            coset_evals_to_Z_final_7_stages_warp
                        } else {
                            main_domain_evals_to_Z_final_7_stages_warp
                        },
                        n / (4 * 128),
                        128,
                    ),
                    FINAL_8_WARP => (
                        if evals_are_coset {
                            coset_evals_to_Z_final_8_stages_warp
                        } else {
                            main_domain_evals_to_Z_final_8_stages_warp
                        },
                        n / (4 * 256),
                        128,
                    ),
                    FINAL_9_TO_12_BLOCK => (
                        if evals_are_coset {
                            coset_evals_to_Z_final_9_to_12_stages_block
                        } else {
                            main_domain_evals_to_Z_final_9_to_12_stages_block
                        },
                        n / 4096,
                        512,
                    ),
                    NONFINAL_7_OR_8_BLOCK => {
                        (evals_to_Z_nonfinal_7_or_8_stages_block, n / 4096, 512)
                    }
                };
            let config = CudaLaunchConfig::basic((grid_dim_x, num_chunks), block_dim_x, stream);
            let args = N2BMultiStageArguments::new(
                outputs_matrix_const,
                outputs_matrix_mut,
                start_stage,
                stages_this_launch,
                log_n,
                num_Z_cols,
            );
            N2BMultiStageFunction(function).launch(&config, &args)
        } else {
            get_last_error().wrap()
        }?;
    }
    assert_eq!(stage, log_n);
    get_last_error().wrap()
}

#[allow(clippy::too_many_arguments)]
pub fn natural_trace_main_evals_to_bitrev_Z(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BaseField> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BaseField> + ?Sized),
    log_n: usize,
    num_bf_cols: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    natural_evals_to_bitrev_Z(
        inputs_matrix,
        outputs_matrix,
        log_n,
        num_bf_cols,
        false,
        stream,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn natural_composition_coset_evals_to_bitrev_Z(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BaseField> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BaseField> + ?Sized),
    log_n: usize,
    num_bf_cols: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    natural_evals_to_bitrev_Z(
        inputs_matrix,
        outputs_matrix,
        log_n,
        num_bf_cols,
        true,
        stream,
    )
}

// The ideal strategy might be:
// If 1 column > L2:
//   first and last kernel unified, middle kernels for all cols chunked and multistreamed
// If 1 column barely fits L2, run experiments to choose between:
//   first and last kernel unified, middle kernels for all cols chunked and multistreamed
//   Work on 1 col at a time end to end. Middle kernels for that col chunked and multistreamed
// If >= 2 cols fit L2:
//   Chunk and multistream by col.
// But if L2 working set can't saturate SMs, the picture becomes more vague...

#[allow(clippy::too_many_arguments)]
pub fn natural_main_evals_to_natural_coset_evals(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BaseField> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BaseField> + ?Sized),
    log_n: usize,
    num_bf_cols: usize,
    exec_stream: &CudaStream,
    aux_stream: &CudaStream,
) -> CudaResult<()> {
    // Sizes < 2^16 are typically for testing only. Fall back to simple path.
    if log_n < 16 {
        let const_outputs_slice = unsafe {
            DeviceSlice::from_raw_parts(
                outputs_matrix.slice().as_ptr(),
                outputs_matrix.slice().len(),
            )
        };
        let const_outputs_matrix = DeviceMatrixChunk::new(
            const_outputs_slice, 
            outputs_matrix.stride(),
            outputs_matrix.offset(),
            outputs_matrix.rows(),
        );
        natural_trace_main_evals_to_bitrev_Z(
            inputs_matrix,
            outputs_matrix,
            log_n as usize,
            num_bf_cols,
            exec_stream,
        )?;
        return bitrev_Z_to_natural_trace_coset_evals(
            &const_outputs_matrix,
            outputs_matrix,
            log_n as usize,
            num_bf_cols,
            exec_stream,
        );
    }

    assert!(log_n >= 1);
    assert!(log_n <= OMEGA_LOG_ORDER as usize);
    assert_eq!(num_bf_cols % 2, 0);
    let n = 1 << log_n;
    let num_Z_cols = (num_bf_cols / 2) as u32;
    assert_eq!(inputs_matrix.rows(), n);
    assert_eq!(inputs_matrix.cols(), num_bf_cols);
    assert_eq!(outputs_matrix.rows(), n);
    assert_eq!(outputs_matrix.cols(), num_bf_cols);
    let log_n = log_n as u32;
    let n = n as u32;

    let inputs_matrix = inputs_matrix.as_ptr_and_stride();
    let outputs_matrix_const = outputs_matrix.as_ptr_and_stride();
    let outputs_matrix_mut = outputs_matrix.as_mut_ptr_and_stride();

    let l2_working_set_e2_elems = 1 << 20;
    let l2_working_set_e2_elems_per_stream = l2_working_set_e2_elems >> 1; 

    let start_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    let end_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;

    use crate::ntt::utils::N2B_LAUNCH::*;
    use crate::ntt::utils::B2N_LAUNCH::*;
    let (n2b_plan, b2n_plan) = get_main_to_coset_launch_chain(log_n as usize);

    // Run first n2b kernel over the entire input.
    let (kern, stages_this_launch) = n2b_plan[0];
    assert_eq!(kern, NONFINAL_7_OR_8_BLOCK);
    let num_chunks = (num_Z_cols + COMPLEX_COLS_PER_BLOCK - 1) / COMPLEX_COLS_PER_BLOCK;
    let grid_dim_x = n / 4096;
    let block_dim_x = 512;
    let config = CudaLaunchConfig::basic((grid_dim_x, num_chunks), block_dim_x, exec_stream);
    let args = N2BMultiStageArguments::new(
        inputs_matrix,
        outputs_matrix_mut,
        0,
        stages_this_launch,
        log_n,
        num_Z_cols,
    );
    N2BMultiStageFunction(evals_to_Z_nonfinal_7_or_8_stages_block).launch(&config, &args)?;

    let mut stage = stages_this_launch;

    start_event.record(exec_stream)?;
    aux_stream.wait_event(&start_event, CudaStreamWaitEventFlags::DEFAULT)?;

    // Run noninitial kernels of n2b and nonfinal kernels of b2n
    // with L2 chunking and multistreaming to reduce tail effect,
    // inspired by GTC S62401 "How To Write A CUDA Program: The Ninja Edition"
    // https://www.nvidia.com/en-us/on-demand/session/gtc24-s62401/
    let stream_refs = [exec_stream, aux_stream];
    let mut stream_selector = 0;
    for row_range in &(0..n).chunks(l2_working_set_e2_elems_per_stream) {
        for col in 0..num_Z_cols {

        }
        
    }

    end_event.record(aux_stream)?;
    exec_stream.wait_event(&end_event, CudaStreamWaitEventFlags::DEFAULT)?;

    // Run final b2n kernel over the entire output.
    let (kern, stages_this_launch) = b2n_plan[b2n_plan.len() - 1];
    assert_eq!(kern, NONINITIAL_7_OR_8_BLOCK);
    let num_chunks = (num_Z_cols + COMPLEX_COLS_PER_BLOCK - 1) / COMPLEX_COLS_PER_BLOCK;
    let grid_dim_x = n / 4096;
    let block_dim_x = 512;
    let config = CudaLaunchConfig::basic((grid_dim_x, num_chunks), block_dim_x, exec_stream);
    let args = B2NMultiStageArguments::new(
        inputs_matrix,
        outputs_matrix_mut,
        0,
        stages_this_launch,
        log_n,
        num_Z_cols,
        1, // log_extension_degree
        1, // coset_index
    );
    B2NMultiStageFunction(bitrev_Z_to_natural_coset_evals_noninitial_7_or_8_stages_block)
        .launch(&config, &args)?;

    Ok(())
}
