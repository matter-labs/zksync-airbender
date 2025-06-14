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
    DeviceMatrixChunk, DeviceMatrixChunkImpl, DeviceMatrixChunkMut, DeviceMatrixChunkMutImpl,
    MutPtrAndStride, PtrAndStride,
};
use crate::field::{BaseField, Ext2Field};
use crate::ntt::utils::{
    get_main_to_coset_launch_chain, COMPLEX_COLS_PER_BLOCK, STAGE_PLANS_B2N, STAGE_PLANS_N2B,
};
use crate::prover::context::DeviceProperties;
use crate::utils::GetChunksCount;

use itertools::Itertools;

type BF = BaseField;
type E2 = Ext2Field;

cuda_kernel!(
    B2NOneStage,
    b2n_one_stage_kernel,
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    start_stage: u32,
    log_n: u32,
    blocks_per_ntt: u32,
    log_extension_degree: u32,
    coset_idx: u32,
);

b2n_one_stage_kernel!(bitrev_Z_to_natural_coset_evals_one_stage);

// "v" indicates a vectorized layout of BF columns,
// For the final output, columns represent distinct base field values.
// For intermediate outputs, each pair of columns represents the c0s and c1s
// of a single column of complex values.
cuda_kernel!(
    B2NMultiStage,
    b2n_multi_stage_kernel,
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    start_stage: u32,
    stages_this_launch: u32,
    log_n: u32,
    num_Z_cols: u32,
    log_extension_degree: u32,
    coset_idx: u32,
    grid_offset: u32,
);

b2n_multi_stage_kernel!(bitrev_Z_to_natural_coset_evals_noninitial_7_or_8_stages_block);
b2n_multi_stage_kernel!(bitrev_Z_to_natural_coset_evals_initial_7_stages_warp);
b2n_multi_stage_kernel!(bitrev_Z_to_natural_coset_evals_initial_8_stages_warp);
b2n_multi_stage_kernel!(bitrev_Z_to_natural_coset_evals_initial_9_to_12_stages_block);

#[allow(clippy::too_many_arguments)]
fn bitrev_Z_to_natural_evals(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
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
    let num_Z_cols = num_bf_cols / 2;
    assert_eq!(inputs_matrix.rows(), n);
    assert_eq!(inputs_matrix.cols(), num_bf_cols);
    assert_eq!(outputs_matrix.rows(), n);
    assert_eq!(outputs_matrix.cols(), num_bf_cols);

    let inputs_matrix = inputs_matrix.as_ptr_and_stride();
    let outputs_matrix_const = outputs_matrix.as_ptr_and_stride();
    let outputs_matrix_mut = outputs_matrix.as_mut_ptr_and_stride();

    // The following bound is overly conservative, since technically the GPU-side
    // 3-layer power caches support powers as fine-grained as CIRCLE_GROUP_LOG_ORDER.
    // Therefore, the assert may fire for some sizes/LDE degrees that could technically work,
    // but are bigger than we expect. Its purpose is to remind us to revisit the logic
    // in such unexpected cases (and relax the bound if the new cases are legitimate).
    assert!(log_n + log_extension_degree < OMEGA_LOG_ORDER as usize);

    // The log_n < 16 path isn't performant, and is meant to unblock
    // small proofs for debugging purposes only.
    if log_n < 16 {
        let threads = 128;
        let n = 1 << log_n;
        let blocks_per_ntt = n.get_chunks_count(2 * threads);
        let blocks = blocks_per_ntt * num_Z_cols;
        let config = CudaLaunchConfig::basic(blocks as u32, threads as u32, stream);
        let kernel_function = B2NOneStageFunction(bitrev_Z_to_natural_coset_evals_one_stage);
        let args = B2NOneStageArguments::new(
            inputs_matrix,
            outputs_matrix_mut,
            0,
            log_n as u32,
            blocks_per_ntt as u32,
            log_extension_degree as u32,
            coset_idx as u32,
        );
        kernel_function.launch(&config, &args)?;
        for stage in 1..log_n {
            let args = B2NOneStageArguments::new(
                outputs_matrix_const,
                outputs_matrix_mut,
                stage as u32,
                log_n as u32,
                blocks_per_ntt as u32,
                log_extension_degree as u32,
                coset_idx as u32,
            );
            kernel_function.launch(&config, &args)?;
        }
        return Ok(());
    }

    use crate::ntt::utils::B2N_LAUNCH::*;
    let plan = &STAGE_PLANS_B2N[log_n - 16];
    let mut stage = 0;
    for &kernel in &plan[..] {
        let start_stage = stage;
        let num_chunks = num_Z_cols.get_chunks_count(COMPLEX_COLS_PER_BLOCK);
        if let Some((kern, stages_this_launch, vals_per_block)) = kernel {
            stage += stages_this_launch;
            let (function, grid_dim_x, block_dim_x): (B2NMultiStageSignature, usize, usize) =
                match kern {
                    INITIAL_7_WARP => (
                        bitrev_Z_to_natural_coset_evals_initial_7_stages_warp,
                        n / vals_per_block,
                        128,
                    ),
                    INITIAL_8_WARP => (
                        bitrev_Z_to_natural_coset_evals_initial_8_stages_warp,
                        n / vals_per_block,
                        128,
                    ),
                    INITIAL_9_TO_12_BLOCK => (
                        bitrev_Z_to_natural_coset_evals_initial_9_to_12_stages_block,
                        n / vals_per_block,
                        512,
                    ),
                    NONINITIAL_7_OR_8_BLOCK => (
                        bitrev_Z_to_natural_coset_evals_noninitial_7_or_8_stages_block,
                        n / vals_per_block,
                        512,
                    ),
                };
            let inputs = if start_stage == 0 {
                inputs_matrix
            } else {
                outputs_matrix_const
            };
            let config = CudaLaunchConfig::basic(
                (grid_dim_x as u32, num_chunks as u32),
                block_dim_x as u32,
                stream,
            );
            let args = B2NMultiStageArguments::new(
                inputs,
                outputs_matrix_mut,
                start_stage as u32,
                stages_this_launch as u32,
                log_n as u32,
                num_Z_cols as u32,
                log_extension_degree as u32,
                coset_idx as u32,
                0,
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
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
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
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
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
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    start_stage: u32,
    log_n: u32,
    blocks_per_ntt: u32,
    evals_are_coset: bool,
);

one_stage_kernel!(evals_to_Z_one_stage);

cuda_kernel!(
    N2BMultiStage,
    n2b_multi_stage_kernel,
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    start_stage: u32,
    stages_this_launch: u32,
    log_n: u32,
    num_Z_cols: u32,
    grid_offset: u32,
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
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    num_bf_cols: usize,
    evals_are_coset: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(log_n >= 1);
    assert!(log_n <= OMEGA_LOG_ORDER as usize);
    assert_eq!(num_bf_cols % 2, 0);
    let n = 1 << log_n;
    let num_Z_cols = num_bf_cols / 2;
    assert_eq!(inputs_matrix.rows(), n);
    assert_eq!(inputs_matrix.cols(), num_bf_cols);
    assert_eq!(outputs_matrix.rows(), n);
    assert_eq!(outputs_matrix.cols(), num_bf_cols);

    let inputs_matrix = inputs_matrix.as_ptr_and_stride();
    let outputs_matrix_const = outputs_matrix.as_ptr_and_stride();
    let outputs_matrix_mut = outputs_matrix.as_mut_ptr_and_stride();

    // The log_n < 16 path isn't performant, and is meant to unblock
    // small proofs for debugging purposes only.
    if log_n < 16 {
        let threads = 128;
        let blocks_per_ntt = (n + 2 * threads - 1) / (2 * threads);
        let blocks = blocks_per_ntt * num_Z_cols;
        let config = CudaLaunchConfig::basic(blocks as u32, threads as u32, stream);
        let kernel_function = N2BOneStageKernelFunction(evals_to_Z_one_stage);
        let args = N2BOneStageKernelArguments::new(
            inputs_matrix,
            outputs_matrix_mut,
            0,
            log_n as u32,
            blocks_per_ntt as u32,
            evals_are_coset,
        );
        kernel_function.launch(&config, &args)?;
        for stage in 1..log_n {
            let args = N2BOneStageKernelArguments::new(
                outputs_matrix_const,
                outputs_matrix_mut,
                stage as u32,
                log_n as u32,
                blocks_per_ntt as u32,
                evals_are_coset,
            );
            kernel_function.launch(&config, &args)?;
        }
        return Ok(());
    }

    use crate::ntt::utils::N2B_LAUNCH::*;
    let plan = &STAGE_PLANS_N2B[log_n - 16];
    let mut stage = 0;
    for &kernel in &plan[..] {
        let start_stage = stage;
        let num_chunks = num_Z_cols.div_ceil(COMPLEX_COLS_PER_BLOCK);
        if let Some((kern, stages_this_launch, vals_per_block)) = kernel {
            stage += stages_this_launch;
            let (function, grid_dim_x, block_dim_x): (N2BMultiStageSignature, usize, usize) =
                match kern {
                    FINAL_7_WARP => (
                        if evals_are_coset {
                            coset_evals_to_Z_final_7_stages_warp
                        } else {
                            main_domain_evals_to_Z_final_7_stages_warp
                        },
                        n / vals_per_block,
                        128,
                    ),
                    FINAL_8_WARP => (
                        if evals_are_coset {
                            coset_evals_to_Z_final_8_stages_warp
                        } else {
                            main_domain_evals_to_Z_final_8_stages_warp
                        },
                        n / vals_per_block,
                        128,
                    ),
                    FINAL_9_TO_12_BLOCK => (
                        if evals_are_coset {
                            coset_evals_to_Z_final_9_to_12_stages_block
                        } else {
                            main_domain_evals_to_Z_final_9_to_12_stages_block
                        },
                        n / vals_per_block,
                        512,
                    ),
                    NONFINAL_7_OR_8_BLOCK => (
                        evals_to_Z_nonfinal_7_or_8_stages_block,
                        n / vals_per_block,
                        512,
                    ),
                };
            let inputs = if start_stage == 0 {
                inputs_matrix
            } else {
                outputs_matrix_const
            };
            let config = CudaLaunchConfig::basic(
                (grid_dim_x as u32, num_chunks as u32),
                block_dim_x as u32,
                stream,
            );
            let args = N2BMultiStageArguments::new(
                inputs,
                outputs_matrix_mut,
                start_stage as u32,
                stages_this_launch as u32,
                log_n as u32,
                num_Z_cols as u32,
                0,
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
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
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
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
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
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    num_bf_cols: usize,
    exec_stream: &CudaStream,
    aux_stream: &CudaStream,
    device_properties: &DeviceProperties,
) -> CudaResult<()> {
    let mut fallback = || -> CudaResult<()> {
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
            log_n,
            num_bf_cols,
            exec_stream,
        )?;
        bitrev_Z_to_natural_trace_coset_evals(
            &const_outputs_matrix,
            outputs_matrix,
            log_n,
            num_bf_cols,
            exec_stream,
        )
    };

    // n < 2^16 is for testing only and uses simple kernels
    if log_n < 16 {
        return fallback();
    }

    // quick-and-dirty heuristic:
    // Use chunked L2 persistence iff we estimate it can saturate the SMs.
    let l2_bytes_with_safety_margin = device_properties.l2_cache_size_bytes >> 1;
    let l2_working_set_e2_elems = l2_bytes_with_safety_margin / std::mem::size_of::<E2>();
    // intent is "prev_power_of_two()" but there's no canned method afaik
    let l2_working_set_e2_elems = l2_working_set_e2_elems.next_power_of_two() >> 1;
    // Big kernels typically use 4096 elems per block, and 2 blocks can fit on each SM
    let working_set_block_count = l2_working_set_e2_elems / 4096;
    let full_wave_block_count = 2 * device_properties.sm_count;
    // Assume the chunking approach can saturate if it can put 1.5 full waves in flight
    let l2_working_set_can_saturate = working_set_block_count >= (full_wave_block_count * 3 / 2);

    if !l2_working_set_can_saturate {
        return fallback();
    }

    assert!(log_n >= 1);
    assert!(log_n <= OMEGA_LOG_ORDER as usize);
    assert_eq!(num_bf_cols % 2, 0);
    let n = 1 << log_n;
    let num_Z_cols = num_bf_cols / 2;
    assert_eq!(inputs_matrix.rows(), n);
    assert_eq!(inputs_matrix.cols(), num_bf_cols);
    assert_eq!(outputs_matrix.rows(), n);
    assert_eq!(outputs_matrix.cols(), num_bf_cols);

    let inputs_matrix_arg = inputs_matrix.as_ptr_and_stride();
    let outputs_matrix_const = outputs_matrix.as_ptr_and_stride();
    let outputs_matrix_mut = outputs_matrix.as_mut_ptr_and_stride();

    let start_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    let end_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;

    use crate::ntt::utils::B2N_LAUNCH::*;
    use crate::ntt::utils::N2B_LAUNCH::*;
    let (n2b_plan, b2n_plan) = get_main_to_coset_launch_chain(log_n);

    // let l2_working_set_e2_elems = 1 << 23;
    // We'd like the L2 to accommodate 2 work packets at once (one per stream)
    let work_packet_elems = l2_working_set_e2_elems >> 1;

    // If the L2 work packet can fit at least 1 full column, we'll include
    // the first n2b and last b2n launches in the persistence chain.
    let work_packet_has_full_cols = work_packet_elems >= n;

    // make sure data chunks that will be assigned to middle kernels are
    // independently contiguous
    let second_kernel_exchg_region_size = 1 << (log_n - n2b_plan[0].1);
    assert!(work_packet_elems >= second_kernel_exchg_region_size);
    let second_to_last_kernel_exchg_region_size = 1 << (log_n - b2n_plan[b2n_plan.len() - 1].1);
    assert!(work_packet_elems >= second_to_last_kernel_exchg_region_size);

    let mut persistence_chain_start_stage = 0;

    if !work_packet_has_full_cols {
        // Run first n2b kernel over the entire input.
        let (kern, stages_first_launch, vals_per_block) = n2b_plan[0];
        assert_eq!(kern, NONFINAL_7_OR_8_BLOCK);
        let grid_dim_x = n / vals_per_block;
        let grid_dim_y = num_Z_cols.div_ceil(COMPLEX_COLS_PER_BLOCK);
        let block_dim_x = 512;
        let config = CudaLaunchConfig::basic(
            (grid_dim_x as u32, grid_dim_y as u32),
            block_dim_x as u32,
            exec_stream,
        );
        let args = N2BMultiStageArguments::new(
            inputs_matrix_arg,
            outputs_matrix_mut,
            0,
            stages_first_launch as u32,
            log_n as u32,
            num_Z_cols as u32,
            0,
        );
        N2BMultiStageFunction(evals_to_Z_nonfinal_7_or_8_stages_block).launch(&config, &args)?;
        persistence_chain_start_stage += stages_first_launch;
    }

    start_event.record(exec_stream)?;
    aux_stream.wait_event(&start_event, CudaStreamWaitEventFlags::DEFAULT)?;

    // Run noninitial kernels of n2b and nonfinal kernels of b2n
    // with L2 chunking and multistreaming to reduce tail effect,
    // inspired by GTC S62401 "How To Write A CUDA Program: The Ninja Edition"
    // https://www.nvidia.com/en-us/on-demand/session/gtc24-s62401/
    // let instant = std::time::Instant::now();
    let rows_per_packet = std::cmp::min(n, work_packet_elems);
    let stream_refs = [exec_stream, aux_stream];
    let chain_start = if work_packet_has_full_cols { 0 } else { 1 };
    let n2b_packet_plan_details: Vec<_> = (&n2b_plan[chain_start..])
        .iter()
        .map(|&(kern, stages_this_launch, vals_per_block)| {
            let (function, grid_dim_x, block_dim_x): (N2BMultiStageSignature, usize, u32) =
                match kern {
                    FINAL_7_WARP => (
                        main_domain_evals_to_Z_final_7_stages_warp,
                        rows_per_packet / vals_per_block,
                        128,
                    ),
                    FINAL_8_WARP => (
                        main_domain_evals_to_Z_final_8_stages_warp,
                        rows_per_packet / vals_per_block,
                        128,
                    ),
                    FINAL_9_TO_12_BLOCK => (
                        main_domain_evals_to_Z_final_9_to_12_stages_block,
                        rows_per_packet / vals_per_block,
                        512,
                    ),
                    NONFINAL_7_OR_8_BLOCK => (
                        evals_to_Z_nonfinal_7_or_8_stages_block,
                        rows_per_packet / vals_per_block,
                        512,
                    ),
                };
            (
                function,
                grid_dim_x,
                block_dim_x,
                stages_this_launch,
                vals_per_block,
            )
        })
        .collect_vec();
    let chain_lim = if work_packet_has_full_cols {
        b2n_plan.len()
    } else {
        b2n_plan.len() - 1
    };
    let b2n_packet_plan_details: Vec<_> = (&b2n_plan[..chain_lim])
        .iter()
        .map(|&(kern, stages_this_launch, vals_per_block)| {
            let (function, grid_dim_x, block_dim_x): (B2NMultiStageSignature, usize, u32) =
                match kern {
                    INITIAL_7_WARP => (
                        bitrev_Z_to_natural_coset_evals_initial_7_stages_warp,
                        rows_per_packet / vals_per_block,
                        128,
                    ),
                    INITIAL_8_WARP => (
                        bitrev_Z_to_natural_coset_evals_initial_8_stages_warp,
                        rows_per_packet / vals_per_block,
                        128,
                    ),
                    INITIAL_9_TO_12_BLOCK => (
                        bitrev_Z_to_natural_coset_evals_initial_9_to_12_stages_block,
                        rows_per_packet / vals_per_block,
                        512,
                    ),
                    NONINITIAL_7_OR_8_BLOCK => (
                        bitrev_Z_to_natural_coset_evals_noninitial_7_or_8_stages_block,
                        rows_per_packet / vals_per_block,
                        512,
                    ),
                };
            (
                function,
                grid_dim_x,
                block_dim_x,
                stages_this_launch,
                vals_per_block,
            )
        })
        .collect();
    let stride = outputs_matrix.stride();
    let offset = outputs_matrix.offset();
    let inputs_slice = inputs_matrix.slice();
    let outputs_slice_const = unsafe {
        DeviceSlice::from_raw_parts(
            outputs_matrix.slice().as_ptr(),
            outputs_matrix.slice().len(),
        )
    };
    let outputs_slice_mut = outputs_matrix.slice_mut();
    let Z_cols_per_packet = std::cmp::max(1, work_packet_elems / n);
    let num_work_packets = if work_packet_has_full_cols {
        assert!(work_packet_elems >= n);
        num_Z_cols.div_ceil(Z_cols_per_packet)
    } else {
        assert!(n > work_packet_elems);
        let work_packets_per_col = n / work_packet_elems;
        work_packets_per_col * num_Z_cols
    };
    let mut start_stage = persistence_chain_start_stage;
    for first_work_packet in (0..num_work_packets).step_by(2) {
        start_stage = persistence_chain_start_stage;
        let mut matrices_both_packets = [None, None];
        for &i in [0, 1].iter() {
            let work_packet = first_work_packet + i;
            if work_packet < num_work_packets {
                if work_packet_has_full_cols {
                    assert!(work_packet * Z_cols_per_packet < num_Z_cols);
                }
                let Z_col = (work_packet * Z_cols_per_packet) % num_Z_cols;
                let Z_cols_this_packet = std::cmp::min(Z_cols_per_packet, num_Z_cols - Z_col);
                let row_packet = work_packet / num_Z_cols;
                let bf_start_col = 2 * Z_col;
                let bf_lim_col = bf_start_col + 2 * Z_cols_this_packet;
                let input_slice = &inputs_slice[bf_start_col * stride..bf_lim_col * stride];
                let output_slice_const =
                    &outputs_slice_const[bf_start_col * stride..bf_lim_col * stride];
                let output_slice_mut =
                    &mut outputs_slice_mut[bf_start_col * stride..bf_lim_col * stride];
                let input_matrix =
                    DeviceMatrixChunk::new(input_slice, stride, offset, rows_per_packet);
                let output_matrix_const =
                    DeviceMatrixChunk::new(output_slice_const, stride, offset, rows_per_packet);
                let mut output_matrix_mut =
                    DeviceMatrixChunkMut::new(output_slice_mut, stride, offset, rows_per_packet);
                matrices_both_packets[i] = Some((
                    input_matrix.as_ptr_and_stride(),
                    output_matrix_const.as_ptr_and_stride(),
                    output_matrix_mut.as_mut_ptr_and_stride(),
                    row_packet,
                    Z_cols_this_packet,
                ));
            }
        }
        // Dispatch chained kernels for two work packets breadth-first (ping-pong)
        for &(function, grid_dim_x, block_dim_x, stages_this_launch, _vals_per_block) in
            n2b_packet_plan_details.iter()
        {
            for (i, matrices) in matrices_both_packets.iter().enumerate() {
                if let Some((
                    input_matrix,
                    output_matrix_const,
                    output_matrix_mut,
                    row_packet,
                    Z_cols_this_packet,
                )) = matrices
                {
                    let grid_dim_y = Z_cols_this_packet.div_ceil(COMPLEX_COLS_PER_BLOCK);
                    let config = CudaLaunchConfig::basic(
                        (grid_dim_x as u32, grid_dim_y as u32),
                        block_dim_x as u32,
                        stream_refs[i],
                    );
                    let input = if start_stage == 0 {
                        *input_matrix
                    } else {
                        *output_matrix_const
                    };
                    let args = N2BMultiStageArguments::new(
                        input,
                        *output_matrix_mut,
                        start_stage as u32,
                        stages_this_launch as u32,
                        log_n as u32,
                        *Z_cols_this_packet as u32,
                        (*row_packet * grid_dim_x) as u32,
                    );
                    N2BMultiStageFunction(function).launch(&config, &args)?;
                }
            }
            start_stage += stages_this_launch;
        }
        start_stage = 0;
        for &(function, grid_dim_x, block_dim_x, stages_this_launch, _vals_per_block) in
            b2n_packet_plan_details.iter()
        {
            for (i, matrices) in matrices_both_packets.iter().enumerate() {
                if let Some((
                    _input_matrix,
                    output_matrix_const,
                    output_matrix_mut,
                    row_packet,
                    Z_cols_this_packet,
                )) = matrices
                {
                    let grid_dim_y = Z_cols_this_packet.div_ceil(COMPLEX_COLS_PER_BLOCK);
                    let config = CudaLaunchConfig::basic(
                        (grid_dim_x as u32, grid_dim_y as u32),
                        block_dim_x as u32,
                        stream_refs[i],
                    );
                    let args = B2NMultiStageArguments::new(
                        *output_matrix_const,
                        *output_matrix_mut,
                        start_stage as u32,
                        stages_this_launch as u32,
                        log_n as u32,
                        *Z_cols_this_packet as u32,
                        1,
                        1,
                        (*row_packet * grid_dim_x) as u32,
                    );
                    B2NMultiStageFunction(function).launch(&config, &args)?;
                }
            }
            start_stage += stages_this_launch;
        }
    }
    // println!("Chunk launch logic took {:?}", instant.elapsed());

    end_event.record(aux_stream)?;
    exec_stream.wait_event(&end_event, CudaStreamWaitEventFlags::DEFAULT)?;

    if !work_packet_has_full_cols {
        // Run final b2n kernel over the entire output.
        let (kern, stages_last_launch, vals_per_block) = b2n_plan[b2n_plan.len() - 1];
        assert_eq!(kern, NONINITIAL_7_OR_8_BLOCK);
        let grid_dim_x = n / vals_per_block;
        let grid_dim_y = num_Z_cols.div_ceil(COMPLEX_COLS_PER_BLOCK);
        let block_dim_x = 512;
        let config = CudaLaunchConfig::basic(
            (grid_dim_x as u32, grid_dim_y as u32),
            block_dim_x as u32,
            exec_stream,
        );
        let args = B2NMultiStageArguments::new(
            outputs_matrix_const,
            outputs_matrix_mut,
            start_stage as u32,
            stages_last_launch as u32,
            log_n as u32,
            num_Z_cols as u32,
            1, // log_extension_degree
            1, // coset_index
            0,
        );
        B2NMultiStageFunction(bitrev_Z_to_natural_coset_evals_noninitial_7_or_8_stages_block)
            .launch(&config, &args)?;
    }

    Ok(())
}
