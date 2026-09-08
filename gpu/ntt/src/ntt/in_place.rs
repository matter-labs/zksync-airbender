//! Transforms that consume and replace a single polynomial representation.

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::context::DeviceProperties;
use gpu_core::primitives::device_structures::{MutPtrAndStride, PtrAndStride};
use gpu_core::primitives::field::BF;

use super::kernels::*;
use super::{select_ntt_strategy, shared, NttDirection, NttKernelKind, OMEGA_LOG_ORDER};

/// Replace natural monomials with bitreversed evaluations of one shifted
/// coset. One mutable slab describes exact aliasing; no aliased Rust slices
/// or auxiliary allocations are constructed.
pub fn monomials_to_coset_in_place(
    values: &mut DeviceSlice<BF>,
    log_n: usize,
    log_lde_factor: usize,
    coset_index: usize,
    properties: &DeviceProperties,
    stream: &CudaStream,
) -> CudaResult<()> {
    monomials_to_coset_in_place_impl(
        values,
        log_n,
        log_lde_factor,
        coset_index,
        properties,
        stream,
        false,
    )
}

fn monomials_to_coset_in_place_impl(
    values: &mut DeviceSlice<BF>,
    log_n: usize,
    log_lde_factor: usize,
    coset_index: usize,
    properties: &DeviceProperties,
    stream: &CudaStream,
    hypercube_final4: bool,
) -> CudaResult<()> {
    assert!((20..=24).contains(&log_n));
    assert!(log_n + log_lde_factor <= OMEGA_LOG_ORDER as usize);
    assert!(coset_index < 1usize << log_lde_factor);
    let n = 1usize << log_n;
    assert_eq!(values.len() % n, 0);
    assert_eq!(values.as_ptr() as usize % 16, 0);
    let columns = values.len() / n;
    if columns == 0 {
        return Ok(());
    }
    let strategy =
        select_ntt_strategy(NttDirection::NaturalToBitrev, log_n, columns, 1, properties)
            .expect("in-place forward requires a natural-to-bitrev strategy");
    let shift = (OMEGA_LOG_ORDER as usize - log_n - log_lde_factor) as i32;
    for first_column in (0..columns).step_by(strategy.columns_per_launch) {
        let count = (columns - first_column).min(strategy.columns_per_launch);
        // SAFETY: the existing forward network already permits exact aliasing
        // for coset zero. A shifted coset changes only load-side scaling; block
        // row ownership and read-before-write barriers are identical.
        let (input, output) = unsafe {
            let ptr = values.as_mut_ptr().add(first_column * n);
            (
                PtrAndStride::new(ptr.cast_const(), n),
                MutPtrAndStride::new(ptr, n),
            )
        };
        let large_two_pass = matches!(
            strategy.passes[0].kernel,
            NttKernelKind::NaturalToBitrevFirst { .. }
        );
        let first = MonomialsToEvalsCompactFunction(if large_two_pass {
            match log_n {
                23 => ab_natural_monomials_to_bitrev_evals_first_9_stages_kernel,
                24 => ab_natural_monomials_to_bitrev_evals_first_10_stages_kernel,
                _ => unreachable!(),
            }
        } else if hypercube_final4 {
            assert_eq!(log_n, 20);
            ab_natural_monomials_to_bitrev_evals_initial_8_stages_from_hypercube_final_4_kernel
        } else {
            ab_natural_monomials_to_bitrev_evals_initial_8_stages_kernel
        });
        let block_values = if large_two_pass { 16384 } else { 8192 };
        let threads = if large_two_pass { 512 } else { 256 };
        let mut config =
            CudaLaunchConfig::basic((n / block_values * count) as u32, threads, stream);
        if large_two_pass {
            config.dynamic_smem_bytes = block_values * size_of::<BF>();
            shared::set_max_dynamic_smem(&first, config.dynamic_smem_bytes)?;
        }
        first.launch(
            &config,
            &MonomialsToEvalsCompactArguments::new(
                input,
                output,
                false,
                log_n as i32,
                coset_index as i32,
                shift,
                count as i32,
                0,
            ),
        )?;
        if strategy.passes.len() == 3 {
            let prefetch = if count == 1 && first_column + 1 < columns {
                // SAFETY: this next column remains within the owned slab;
                // terminal prefetch only reads it, before its initial launch.
                Some(unsafe { values.as_ptr().add((first_column + 1) * n) })
            } else {
                None
            };
            super::forward::launch_natural_to_bitrev_tail(
                input, output, log_n, count, count, 0, prefetch, None, properties, stream,
            )?;
        } else {
            let (last, block_values, shared_values) = if large_two_pass {
                (
                    ab_natural_monomials_to_bitrev_evals_last_14_stages_kernel
                        as NaturalToBitrevFinalSignature,
                    16384,
                    16384 + 8192,
                )
            } else {
                assert_eq!(log_n, 20);
                (
                    ab_natural_monomials_to_bitrev_evals_last_12_stages_compact_kernel
                        as NaturalToBitrevFinalSignature,
                    4096,
                    4096,
                )
            };
            let last = NaturalToBitrevFinalFunction(last);
            let mut config =
                CudaLaunchConfig::basic((n / block_values * count) as u32, threads, stream);
            config.dynamic_smem_bytes = shared_values * size_of::<BF>();
            shared::set_max_dynamic_smem(&last, config.dynamic_smem_bytes)?;
            last.launch(
                &config,
                &NaturalToBitrevFinalArguments::new(input, output, log_n as i32, count as i32, 0),
            )?;
        }
    }
    Ok(())
}

/// Consume raw evaluations into one coset, preserving the fused Mobius/NTT
/// boundary and next-column finest work without retaining any intermediate M.
pub fn hypercube_to_coset_in_place(
    values: &mut DeviceSlice<BF>,
    log_n: usize,
    log_lde_factor: usize,
    coset_index: usize,
    properties: &DeviceProperties,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!((20..=24).contains(&log_n));
    assert!(log_n + log_lde_factor <= OMEGA_LOG_ORDER as usize);
    assert!(coset_index < 1usize << log_lde_factor);
    let n = 1usize << log_n;
    assert_eq!(values.len() % n, 0);
    assert_eq!(values.as_ptr() as usize % 16, 0);
    let columns = values.len() / n;
    let three_pass =
        log_n != 20 && !(log_n >= 23 && n * size_of::<BF>() >= properties.l2_cache_size_bytes);
    if !three_pass {
        if log_n == 20 {
            for column in 0..columns {
                // SAFETY: exact aliasing of the block-owned row sets in the
                // coarse and middle Mobius passes, with their existing barriers.
                let (input, output) = unsafe {
                    let ptr = values.as_mut_ptr().add(column * n);
                    (
                        PtrAndStride::new(ptr.cast_const(), n),
                        MutPtrAndStride::new(ptr, n),
                    )
                };
                super::hypercube::launch_nonfinal_passes(input, input, output, log_n, stream)?;
            }
        } else {
            super::hypercube::transform_hypercube_in_place::<false>(
                values, log_n, properties, stream,
            )?;
        }
        return monomials_to_coset_in_place_impl(
            values,
            log_n,
            log_lde_factor,
            coset_index,
            properties,
            stream,
            log_n == 20,
        );
    }
    let shift = (OMEGA_LOG_ORDER as usize - log_n - log_lde_factor) as i32;
    for column in 0..columns {
        // SAFETY: the first pass and fused boundary read all block-owned rows
        // before overwriting those same rows. The boundary omits M writeback.
        let (input, output) = unsafe {
            let ptr = values.as_mut_ptr().add(column * n);
            (
                PtrAndStride::new(ptr.cast_const(), n),
                MutPtrAndStride::new(ptr, n),
            )
        };
        super::hypercube::launch_pre_tail_lsb_column(
            input,
            input,
            output,
            log_n,
            column != 0,
            properties,
            stream,
        )?;
        let config = CudaLaunchConfig::basic((n / 8192) as u32, 256, stream);
        LdeFusedWritebackFunction(ab_natural_lde_fused_boundary_in_place_kernel).launch(
            &config,
            &LdeFusedWritebackArguments::new(
                output,
                output,
                log_n as i32,
                coset_index as i32,
                shift,
                1,
                0,
            ),
        )?;
        let next = if column + 1 < columns {
            // SAFETY: the next raw column is disjoint from this coset. The
            // terminal's fused finest pass permits exact aliasing within it.
            Some(unsafe {
                let ptr = values.as_mut_ptr().add((column + 1) * n);
                (
                    PtrAndStride::new(ptr.cast_const(), n),
                    MutPtrAndStride::new(ptr, n),
                )
            })
        } else {
            None
        };
        super::forward::launch_natural_to_bitrev_tail(
            input, output, log_n, 1, 1, 0, None, next, properties, stream,
        )?;
    }
    Ok(())
}

/// Restore the raw evaluations required by witness sumchecks after an in-place
/// commitment has inverse-transformed its final coset back into monomials.
pub fn monomials_to_hypercube_in_place(
    values: &mut DeviceSlice<BF>,
    log_n: usize,
    properties: &DeviceProperties,
    stream: &CudaStream,
) -> CudaResult<()> {
    super::hypercube::transform_hypercube_in_place::<true>(values, log_n, properties, stream)
}

/// Replace bitreversed evaluations on `coset_index` with natural monomials.
/// Each column is one polynomial of size 2^log_n. No allocation, copy or
/// bit-reversal pass is needed. All prior readers must be ordered on `stream`.
pub fn coset_to_monomials_in_place(
    values: &mut DeviceSlice<BF>,
    log_n: usize,
    log_lde_factor: usize,
    coset_index: usize,
    properties: &DeviceProperties,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!((20..=24).contains(&log_n));
    assert!(log_n + log_lde_factor <= OMEGA_LOG_ORDER as usize);
    assert!(coset_index < 1usize << log_lde_factor);
    let n = 1usize << log_n;
    assert_eq!(values.len() % n, 0);
    assert_eq!(values.as_ptr() as usize % 16, 0);
    let columns = values.len() / n;
    if columns == 0 {
        return Ok(());
    }
    // This inverse has the bitrev-to-natural DIF address network. The usual
    // Inverse selector describes natural-to-bitrev DIT and cannot be used.
    let strategy = select_ntt_strategy(NttDirection::Forward, log_n, columns, 1, properties)
        .expect("in-place inverse requires bitrev-to-natural pass geometry");
    let factor = (coset_index << (OMEGA_LOG_ORDER as usize - log_n - log_lde_factor)) as u32;
    for first_column in (0..columns).step_by(strategy.columns_per_launch) {
        let count = (columns - first_column).min(strategy.columns_per_launch);
        // SAFETY: both pointer descriptors address the same exclusive slab.
        // Every pass reads its complete block-owned row set before overwriting
        // it, with the existing warp/block barriers. Cosets are never batched
        // here, so no other coset block can race a shared monomial source.
        let (input, output) = unsafe {
            let ptr = values.as_mut_ptr().add(first_column * n);
            (
                PtrAndStride::new(ptr.cast_const(), n),
                MutPtrAndStride::new(ptr, n),
            )
        };
        for pass in &strategy.passes {
            match pass.kernel {
                NttKernelKind::MonomialsToEvalsInitial { stages: 14 } => {
                    let function = MonomialsToEvalsInitialFunction(
                        ab_coset_to_monomials_first_14_stages_kernel,
                    );
                    let mut config =
                        CudaLaunchConfig::basic((n / 16384 * count) as u32, 512, stream);
                    config.dynamic_smem_bytes = (16384 + 8192) * size_of::<BF>();
                    shared::set_max_dynamic_smem(&function, config.dynamic_smem_bytes)?;
                    function.launch(
                        &config,
                        &MonomialsToEvalsInitialArguments::new(
                            input,
                            output,
                            false,
                            log_n as i32,
                            factor as i32,
                        ),
                    )?;
                }
                NttKernelKind::MonomialsToEvalsInitial { stages }
                | NttKernelKind::MonomialsToEvalsFirstCompact { stages } => {
                    let signature = match pass.kernel {
                        NttKernelKind::MonomialsToEvalsFirstCompact { stages: 12 } => {
                            ab_coset_to_monomials_first_12_stages_compact_kernel
                        }
                        NttKernelKind::MonomialsToEvalsInitial { stages: 5 } => {
                            ab_coset_to_monomials_initial_5_stages_kernel
                        }
                        NttKernelKind::MonomialsToEvalsInitial { stages: 6 } => {
                            ab_coset_to_monomials_initial_6_stages_kernel
                        }
                        NttKernelKind::MonomialsToEvalsInitial { stages: 7 } => {
                            ab_coset_to_monomials_initial_7_stages_kernel
                        }
                        NttKernelKind::MonomialsToEvalsInitial { stages: 8 } => {
                            ab_coset_to_monomials_initial_8_stages_kernel
                        }
                        _ => unreachable!("unsupported inverse initial pass: {pass:?}"),
                    };
                    let compact = matches!(
                        pass.kernel,
                        NttKernelKind::MonomialsToEvalsFirstCompact { .. }
                    );
                    let block_values = if compact { 1usize << stages } else { 8192 };
                    let mut config =
                        CudaLaunchConfig::basic((n / block_values * count) as u32, 256, stream);
                    if compact {
                        config.dynamic_smem_bytes = block_values * size_of::<BF>();
                    }
                    MonomialsToEvalsCompactFunction(signature).launch(
                        &config,
                        &MonomialsToEvalsCompactArguments::new(
                            input,
                            output,
                            false,
                            log_n as i32,
                            0,
                            0,
                            count as i32,
                            0,
                        ),
                    )?;
                }
                NttKernelKind::MonomialsToEvalsNonInitial { stages: 8 }
                | NttKernelKind::MonomialsToEvalsLast { .. } => {
                    let (signature, block_values, threads) = match pass.kernel {
                        NttKernelKind::MonomialsToEvalsNonInitial { .. } => (
                            ab_coset_to_monomials_noninitial_8_stages_kernel
                                as CosetToMonomialsStagesSignature,
                            8192,
                            256,
                        ),
                        NttKernelKind::MonomialsToEvalsLast { stages: 9 } => (
                            ab_coset_to_monomials_last_9_stages_kernel
                                as CosetToMonomialsStagesSignature,
                            16384,
                            512,
                        ),
                        NttKernelKind::MonomialsToEvalsLast { stages: 10 } => (
                            ab_coset_to_monomials_last_10_stages_kernel
                                as CosetToMonomialsStagesSignature,
                            16384,
                            512,
                        ),
                        _ => unreachable!("unsupported inverse final pass: {pass:?}"),
                    };
                    let function = CosetToMonomialsStagesFunction(signature);
                    let mut config =
                        CudaLaunchConfig::basic((n / block_values * count) as u32, threads, stream);
                    if block_values == 16384 {
                        config.dynamic_smem_bytes = block_values * size_of::<BF>();
                        shared::set_max_dynamic_smem(&function, config.dynamic_smem_bytes)?;
                    }
                    function.launch(
                        &config,
                        &CosetToMonomialsStagesArguments::new(
                            input,
                            output,
                            log_n as i32,
                            pass.start_stage as i32,
                            count as i32,
                            0,
                            factor,
                        ),
                    )?;
                }
                _ => unreachable!("unsupported in-place inverse plan: {pass:?}"),
            }
        }
    }
    Ok(())
}
