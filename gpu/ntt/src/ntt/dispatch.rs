#![allow(non_snake_case)]

use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use super::dit::monomials_to_evals_dit;
use super::forward::{
    monomials_to_evals_2_pass, monomials_to_evals_2_pass_compact_initial,
    monomials_to_evals_3_pass, monomials_to_evals_compact_1_pass, monomials_to_evals_smem_packed,
    monomials_to_evals_subwarp,
};
use super::inverse::{evals_to_monomials_2_pass, evals_to_monomials_3_pass};
use super::{natural_evals_to_bitreversed_coeffs, MIN_LOG_N_FOR_MULTISTAGE_KERNELS};

use crate::ntt_twiddles::OMEGA_LOG_ORDER;
use gpu_core::primitives::context::DeviceProperties;
use gpu_core::primitives::device_structures::{DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl};
use gpu_core::primitives::field::BaseField;

type BF = BaseField;

pub(super) fn dispatch_strategy(
    inputs_matrix: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    outputs_matrix: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: usize,
    log_lde_factor: usize,
    coset_index: usize,
    transposed_monomials: bool,
    ntt_ctx: &crate::ntt_twiddles::DeviceContext,
    d_table_scratch: Option<&mut DeviceSlice<BF>>,
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
    let mut d_table_scratch = d_table_scratch;
    match strategy.passes.len() {
        1 => match strategy.passes[0].kernel {
            super::NttKernelKind::MonomialsToEvalsDit { log_vpt, .. } => monomials_to_evals_dit(
                inputs_matrix,
                outputs_matrix,
                log_n,
                log_vpt,
                coset_index,
                coset_factor_shift,
                1,
                num_cols_per_coset,
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
            } => monomials_to_evals_subwarp(
                inputs_matrix,
                outputs_matrix,
                log_n,
                coset_index,
                coset_factor_shift,
                1,
                num_cols_per_coset,
                log_instances_per_block,
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

pub fn natural_evals_to_bitreversed_monomials(
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
