#![allow(non_snake_case)]

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchAttribute, CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use super::hypercube_evals_to_monomial_coeffs;
use super::shared;
use super::strategy::{TWO_PASS_COMPACT_MAX_LOG_N, TWO_PASS_COMPACT_MIN_LOG_N};

use gpu_core::primitives::context::DeviceProperties;
use gpu_core::primitives::device_structures::{
    DeviceMatrixChunk, DeviceMatrixChunkImpl, DeviceMatrixChunkMut, DeviceMatrixChunkMutImpl,
    MutPtrAndStride, PtrAndStride,
};
use gpu_core::primitives::field::BaseField;
use gpu_core::primitives::utils::GetChunksCount;

use std::mem::size_of;

type BF = BaseField;

const _: () = assert!(TWO_PASS_COMPACT_MIN_LOG_N == 13);
const _: () = assert!(TWO_PASS_COMPACT_MAX_LOG_N == 20);

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
strided_tiles_stages!(ab_hypercube_evals_to_monomials_8_stages_kernel);
strided_tiles_stages!(ab_hypercube_evals_to_monomials_8_stages_1_role_kernel);
strided_tiles_stages!(ab_hypercube_evals_to_monomials_8_stages_pdl_kernel);

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
hypercube_evals_to_monomials_final!(ab_hypercube_evals_to_monomials_final_4_stages_kernel);
hypercube_evals_to_monomials_final!(ab_hypercube_evals_to_monomials_final_5_stages_kernel);
hypercube_evals_to_monomials_final!(ab_hypercube_evals_to_monomials_final_6_stages_kernel);
hypercube_evals_to_monomials_final!(ab_hypercube_evals_to_monomials_final_7_stages_kernel);
hypercube_evals_to_monomials_final!(ab_hypercube_evals_to_monomials_finest_8_stages_kernel);

cuda_kernel!(
    HypercubeLastCompact,
    hypercube_last_compact,
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
);

hypercube_last_compact!(ab_hypercube_evals_to_monomials_last_5_stages_compact_kernel);
hypercube_last_compact!(ab_hypercube_evals_to_monomials_last_6_stages_compact_kernel);
hypercube_last_compact!(ab_hypercube_evals_to_monomials_last_7_stages_compact_kernel);
hypercube_last_compact!(ab_hypercube_evals_to_monomials_last_8_stages_compact_kernel);
hypercube_last_compact!(ab_hypercube_evals_to_monomials_last_9_stages_compact_kernel);
hypercube_last_compact!(ab_hypercube_evals_to_monomials_last_10_stages_compact_kernel);
hypercube_last_compact!(ab_hypercube_evals_to_monomials_last_11_stages_compact_kernel);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum HypercubeDispatch {
    OneStagePerVariable {
        stages: usize,
    },
    TwoPassCompact {
        first_stages: usize,
        last_stages: usize,
    },
    ThreePassCompact {
        first_stages: usize,
        middle_stages: usize,
        last_stages: usize,
    },
    TwoPass,
    ThreePass,
}

impl HypercubeDispatch {
    #[cfg(test)]
    fn kernel_launches_per_column(self) -> usize {
        match self {
            Self::OneStagePerVariable { stages } => stages,
            Self::TwoPassCompact { .. } | Self::TwoPass => 2,
            Self::ThreePassCompact { .. } | Self::ThreePass => 3,
        }
    }
}

fn select_hypercube_dispatch(
    log_n: usize,
    large_ntt_passes: super::NttPassCount,
) -> HypercubeDispatch {
    if log_n < TWO_PASS_COMPACT_MIN_LOG_N {
        HypercubeDispatch::OneStagePerVariable { stages: log_n }
    } else if log_n < TWO_PASS_COMPACT_MAX_LOG_N {
        HypercubeDispatch::TwoPassCompact {
            first_stages: 8,
            last_stages: log_n - 8,
        }
    } else if log_n == TWO_PASS_COMPACT_MAX_LOG_N {
        HypercubeDispatch::ThreePassCompact {
            first_stages: 8,
            middle_stages: 8,
            last_stages: 4,
        }
    } else {
        match large_ntt_passes {
            super::NttPassCount::Two => HypercubeDispatch::TwoPass,
            super::NttPassCount::Three => HypercubeDispatch::ThreePass,
        }
    }
}

#[cfg(test)]
mod cpu_dispatch_tests {
    use super::*;

    #[test]
    fn compact_range_never_uses_one_stage_per_variable() {
        for log_n in TWO_PASS_COMPACT_MIN_LOG_N..=TWO_PASS_COMPACT_MAX_LOG_N {
            for large_ntt_passes in [
                super::super::NttPassCount::Two,
                super::super::NttPassCount::Three,
            ] {
                let dispatch = select_hypercube_dispatch(log_n, large_ntt_passes);
                let expected = if log_n == TWO_PASS_COMPACT_MAX_LOG_N {
                    HypercubeDispatch::ThreePassCompact {
                        first_stages: 8,
                        middle_stages: 8,
                        last_stages: 4,
                    }
                } else {
                    HypercubeDispatch::TwoPassCompact {
                        first_stages: 8,
                        last_stages: log_n - 8,
                    }
                };
                assert_eq!(
                    dispatch, expected,
                    "log_n={log_n}, large_ntt_passes={large_ntt_passes:?}",
                );
                let expected_launches = if log_n == TWO_PASS_COMPACT_MAX_LOG_N {
                    3
                } else {
                    2
                };
                assert_eq!(
                    dispatch.kernel_launches_per_column(),
                    expected_launches,
                    "log_n={log_n}"
                );
                assert!(dispatch.kernel_launches_per_column() < log_n);
            }
        }
    }
}

/// The two hypercube nonfinal passes for one column (pass 1 reads the
/// hypercube evals, pass 2 runs in place on the output).
fn launch_nonfinal_passes(
    input_matrix: PtrAndStride<BF>,
    output_matrix_const: PtrAndStride<BF>,
    output_matrix_mut: MutPtrAndStride<BF>,
    log_n: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    let n = 1usize << log_n;
    let mut start_stage = 0;
    for i in 0..2 {
        let log_bf_vals_per_block = if log_n == 20 && start_stage == 8 {
            12 // 4096: one exchange region and one tile role per thread
        } else {
            13 // 8192: two tile roles per thread
        };
        let bf_vals_per_block = 1usize << log_bf_vals_per_block;
        let num_exchg_regions = 1 << start_stage;
        let exchg_region_size = n >> start_stage;
        let blocks_per_exchg_region = exchg_region_size / bf_vals_per_block;
        assert_eq!(
            blocks_per_exchg_region * num_exchg_regions,
            n / bf_vals_per_block
        );
        let mut grid_dim: Dim3 = (blocks_per_exchg_region as u32).into();
        grid_dim.y = num_exchg_regions as u32;
        let config = CudaLaunchConfig::basic(grid_dim, 256, stream);
        let input = if i == 0 {
            input_matrix
        } else {
            output_matrix_const
        };
        let args =
            StridedTilesStagesArguments::new(input, output_matrix_mut, log_n as i32, start_stage);
        let function = if log_bf_vals_per_block == 12 {
            StridedTilesStagesFunction(ab_hypercube_evals_to_monomials_8_stages_1_role_kernel)
        } else {
            StridedTilesStagesFunction(ab_hypercube_evals_to_monomials_8_stages_kernel)
        };
        function.launch(&config, &args)?;
        start_stage += 8;
    }
    Ok(())
}

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
    shared::assert_ntt_16b_aligned(inputs_matrix, outputs_matrix);
    let num_ntts = outputs_matrix.cols();
    assert_eq!(inputs_matrix.cols(), num_ntts);
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
        launch_nonfinal_passes(
            input_matrix,
            output_matrix_const,
            output_matrix_mut,
            log_n,
            stream,
        )?;
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
            20 => {
                EvalsToMonomialsFinalFunction(ab_hypercube_evals_to_monomials_final_4_stages_kernel)
                    .launch(&config, &args)?
            }
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
            24 => EvalsToMonomialsFinalFunction(
                ab_hypercube_evals_to_monomials_finest_8_stages_kernel,
            )
            .launch(&config, &args)?,
            _ => unreachable!("hypercube 3-pass kernels are only generated for log_n in 20..=24"),
        }
    }
    Ok(())
}

/// [`hypercube_evals_to_monomials_3_pass`] minus the final pass: leaves the
/// PRE-TAIL intermediate in `outputs_matrix` for the fused LDE boundary kernel
/// (which applies the final `log_n - 16` stages inline for the first coset,
/// materializing the monomials in place as it goes).
pub(crate) fn hypercube_evals_to_pre_tail_monomials_3_pass(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    let n = 1 << log_n;
    assert_eq!(inputs_matrix.rows(), n);
    assert_eq!(outputs_matrix.rows(), n);
    shared::assert_ntt_16b_aligned(inputs_matrix, outputs_matrix);
    let num_ntts = outputs_matrix.cols();
    assert_eq!(inputs_matrix.cols(), num_ntts);
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
        launch_nonfinal_passes(
            input_matrix,
            output_matrix_const,
            output_matrix_mut,
            log_n,
            stream,
        )?;
    }
    Ok(())
}

/// Fine->coarse pre-tail for the natural fused LDE boundary kernel: the
/// finest-stage kernel FIRST (reading the hypercube evals out of place),
/// then the middle 8 stages in place — the coarse-8 tail stays for the fused
/// kernel. Valid reorder: the hypercube stages carry no twiddles and commute.
pub(crate) fn hypercube_evals_to_pre_tail_monomials_lsb_3_pass(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    device_properties: &DeviceProperties,
    stream: &CudaStream,
) -> CudaResult<()> {
    hypercube_evals_to_monomials_lsb_fine_first(
        inputs_matrix,
        outputs_matrix,
        log_n,
        false,
        device_properties,
        stream,
    )
}

/// Continue the fine->coarse pre-tail after a preceding cross-column kernel
/// has already written the finest-stage output into `outputs_matrix`.
pub(crate) fn hypercube_evals_to_pre_tail_monomials_lsb_3_pass_after_finest(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    device_properties: &DeviceProperties,
    stream: &CudaStream,
) -> CudaResult<()> {
    hypercube_evals_to_monomials_lsb_fine_first(
        inputs_matrix,
        outputs_matrix,
        log_n,
        true,
        device_properties,
        stream,
    )
}

fn hypercube_evals_to_monomials_lsb_fine_first(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    finest_already_computed: bool,
    device_properties: &DeviceProperties,
    stream: &CudaStream,
) -> CudaResult<()> {
    let n = 1 << log_n;
    assert_eq!(inputs_matrix.rows(), n);
    assert_eq!(outputs_matrix.rows(), n);
    shared::assert_ntt_16b_aligned(inputs_matrix, outputs_matrix);
    let num_ntts = outputs_matrix.cols();
    assert_eq!(inputs_matrix.cols(), num_ntts);
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
        // Finest stages first, out of place from the hypercube evals. A
        // previous column's fused terminal may already have produced this
        // exact slab.
        let threads = 256;
        let bf_vals_per_block = 1 << 13; // 8192
        let blocks = n.get_chunks_count(bf_vals_per_block);
        if !finest_already_computed {
            let config = CudaLaunchConfig::basic(blocks as u32, threads as u32, stream);
            let args = EvalsToMonomialsFinalArguments::new(
                input_matrix,
                output_matrix_mut,
                false,
                log_n as i32,
            );
            match log_n {
                21 => EvalsToMonomialsFinalFunction(
                    ab_hypercube_evals_to_monomials_final_5_stages_kernel,
                )
                .launch(&config, &args)?,
                22 => EvalsToMonomialsFinalFunction(
                    ab_hypercube_evals_to_monomials_final_6_stages_kernel,
                )
                .launch(&config, &args)?,
                23 => EvalsToMonomialsFinalFunction(
                    ab_hypercube_evals_to_monomials_final_7_stages_kernel,
                )
                .launch(&config, &args)?,
                24 => EvalsToMonomialsFinalFunction(
                    ab_hypercube_evals_to_monomials_finest_8_stages_kernel,
                )
                .launch(&config, &args)?,
                _ => {
                    unreachable!("hypercube 3-pass kernels are only generated for log_n in 21..=24")
                }
            }
        }
        // Middle 8 stages in place.
        let start_stage = 8;
        let num_exchg_regions = 1usize << start_stage;
        let exchg_region_size = n >> start_stage;
        let blocks_per_exchg_region = exchg_region_size / bf_vals_per_block;
        assert_eq!(
            blocks_per_exchg_region * num_exchg_regions,
            n / bf_vals_per_block
        );
        let mut grid_dim: Dim3 = (blocks_per_exchg_region as u32).into();
        grid_dim.y = num_exchg_regions as u32;
        let pdl_middle = finest_already_computed
            && matches!(log_n, 22..=24)
            && shared::supports_tma_pdl(device_properties.compute_capability_major);
        let pdl_attributes = [CudaLaunchAttribute::ProgrammaticStreamSerialization(true)];
        let mut config = CudaLaunchConfig::basic(grid_dim, threads as u32, stream);
        if pdl_middle {
            config.attributes = &pdl_attributes;
        }
        let args = StridedTilesStagesArguments::new(
            output_matrix_const,
            output_matrix_mut,
            log_n as i32,
            start_stage as i32,
        );
        let middle = if pdl_middle {
            ab_hypercube_evals_to_monomials_8_stages_pdl_kernel
        } else {
            ab_hypercube_evals_to_monomials_8_stages_kernel
        };
        StridedTilesStagesFunction(middle).launch(&config, &args)?;
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
    shared::assert_ntt_16b_aligned(inputs_matrix, outputs_matrix);
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
            _ => unreachable!("hypercube 2-pass kernels are only generated for log_n in 23..=24"),
        };
        shared::set_max_dynamic_smem(&function, smem_bytes)?;
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
        shared::set_max_dynamic_smem(&function, smem_bytes)?;
        function.launch(&config, &args)?;
    }
    Ok(())
}

/// Two-pass compact-range Mobius transform: the existing whole-domain
/// nonfinal8 pass followed by a twiddle-free consecutive-chunk tail of
/// `log_n - 8` stages. This path is natural-layout only.
pub(crate) fn hypercube_evals_to_monomials_2_pass_compact(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        (TWO_PASS_COMPACT_MIN_LOG_N..TWO_PASS_COMPACT_MAX_LOG_N).contains(&log_n),
        "two-pass compact hypercube path supports log_n in [{TWO_PASS_COMPACT_MIN_LOG_N}, {TWO_PASS_COMPACT_MAX_LOG_N})",
    );
    assert!(
        !transposed_monomials,
        "compact hypercube path does not support transposed monomials",
    );
    let n = 1usize << log_n;
    assert_eq!(inputs_matrix.rows(), n);
    assert_eq!(outputs_matrix.rows(), n);
    assert_eq!(inputs_matrix.stride(), outputs_matrix.stride());
    shared::assert_ntt_16b_aligned(inputs_matrix, outputs_matrix);
    let num_ntts = outputs_matrix.cols();
    assert_eq!(inputs_matrix.cols(), num_ntts);
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
    let log_k = log_n - 8;
    let tail_function = match log_k {
        5 => HypercubeLastCompactFunction(
            ab_hypercube_evals_to_monomials_last_5_stages_compact_kernel,
        ),
        6 => HypercubeLastCompactFunction(
            ab_hypercube_evals_to_monomials_last_6_stages_compact_kernel,
        ),
        7 => HypercubeLastCompactFunction(
            ab_hypercube_evals_to_monomials_last_7_stages_compact_kernel,
        ),
        8 => HypercubeLastCompactFunction(
            ab_hypercube_evals_to_monomials_last_8_stages_compact_kernel,
        ),
        9 => HypercubeLastCompactFunction(
            ab_hypercube_evals_to_monomials_last_9_stages_compact_kernel,
        ),
        10 => HypercubeLastCompactFunction(
            ab_hypercube_evals_to_monomials_last_10_stages_compact_kernel,
        ),
        11 => HypercubeLastCompactFunction(
            ab_hypercube_evals_to_monomials_last_11_stages_compact_kernel,
        ),
        _ => unreachable!("log_k = log_n - 8 is in [5, 11]"),
    };

    // Work on one column at a time to preserve the existing L2 locality.
    for col in 0..num_ntts {
        let range = col * stride..(col + 1) * stride;
        let input_slice = &inputs_slice[range.clone()];
        let output_slice_const = &outputs_slice_const[range.clone()];
        let output_slice_mut = &mut outputs_slice_mut[range];
        let input_matrix =
            DeviceMatrixChunk::new(input_slice, stride, offset, n).as_ptr_and_stride();
        let output_matrix_const =
            DeviceMatrixChunk::new(output_slice_const, stride, offset, n).as_ptr_and_stride();
        let mut output_matrix_mut = DeviceMatrixChunkMut::new(output_slice_mut, stride, offset, n);
        let output_matrix_mut = output_matrix_mut.as_mut_ptr_and_stride();

        // At log_n=13/14 this is intentionally a skinny 1/2-block grid per
        // column; it is still a fixed two-launch path instead of 13/14
        // one-stage launches. Column folding can be added if these sizes
        // become hot enough to justify changing the kernel ABI.
        let first_blocks = n / (1usize << 13);
        let first_config = CudaLaunchConfig::basic(first_blocks as u32, 256, stream);
        let first_args =
            StridedTilesStagesArguments::new(input_matrix, output_matrix_mut, log_n as i32, 0);
        StridedTilesStagesFunction(ab_hypercube_evals_to_monomials_8_stages_kernel)
            .launch(&first_config, &first_args)?;

        let k_vals = 1usize << log_k;
        let tail_blocks = n / k_vals;
        debug_assert_eq!(tail_blocks, 1usize << 8);
        let mut tail_config = CudaLaunchConfig::basic(tail_blocks as u32, 256, stream);
        tail_config.dynamic_smem_bytes = k_vals * size_of::<BF>();
        let tail_args = HypercubeLastCompactArguments::new(output_matrix_const, output_matrix_mut);
        tail_function.launch(&tail_config, &tail_args)?;
    }
    Ok(())
}

/// Multilinear hypercube evaluations -> multilinear monomial coefficients, the
/// multistage form of [`super::hypercube_evals_to_monomial_coeffs`] (which
/// serves the sub-floor fallback below). Being a Mobius transform it preserves
/// its input's labeling; production feeds it natural-order evaluations, so the
/// coefficients come out natural.
pub fn hypercube_evals_to_monomials(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    transposed_monomials: bool,
    stream: &CudaStream,
    device_properties: &DeviceProperties,
) -> CudaResult<()> {
    let dispatch =
        select_hypercube_dispatch(log_n, super::ntt_pass_selection(log_n, device_properties));
    match dispatch {
        HypercubeDispatch::OneStagePerVariable { stages } => {
            debug_assert_eq!(stages, log_n);
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
                hypercube_evals_to_monomial_coeffs(
                    &inputs_slice[col * inputs_stride..col * inputs_stride + rows],
                    &mut outputs_slice[col * outputs_stride..col * outputs_stride + rows],
                    log_n,
                    stream,
                )?;
            }
        }
        HypercubeDispatch::TwoPassCompact {
            first_stages,
            last_stages,
        } => {
            debug_assert_eq!(first_stages, 8);
            debug_assert_eq!(first_stages + last_stages, log_n);
            hypercube_evals_to_monomials_2_pass_compact(
                inputs_matrix,
                outputs_matrix,
                log_n,
                transposed_monomials,
                stream,
            )?
        }
        HypercubeDispatch::ThreePassCompact {
            first_stages,
            middle_stages,
            last_stages,
        } => {
            debug_assert_eq!((first_stages, middle_stages, last_stages), (8, 8, 4));
            debug_assert_eq!(first_stages + middle_stages + last_stages, log_n);
            hypercube_evals_to_monomials_3_pass(
                inputs_matrix,
                outputs_matrix,
                log_n,
                transposed_monomials,
                stream,
            )?
        }
        HypercubeDispatch::TwoPass => hypercube_evals_to_monomials_2_pass(
            inputs_matrix,
            outputs_matrix,
            log_n,
            transposed_monomials,
            stream,
        )?,
        HypercubeDispatch::ThreePass => hypercube_evals_to_monomials_3_pass(
            inputs_matrix,
            outputs_matrix,
            log_n,
            transposed_monomials,
            stream,
        )?,
    }
    Ok(())
}
