//! Fused LDE generation with retained natural monomials and one coset output.

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::context::DeviceProperties;
use gpu_core::primitives::device_structures::{
    DeviceMatrix, DeviceMatrixMut, MutPtrAndStride, PtrAndStride,
};
use gpu_core::primitives::field::BF;

use super::forward::{
    launch_natural_to_bitrev_tail, natural_monomials_to_bitrev_evals_2_pass,
    natural_monomials_to_bitrev_evals_2_pass_compact,
};
use super::hypercube::{
    launch_hypercube_two_pass_column, launch_nonfinal_passes, launch_pre_tail_lsb_column,
};
use super::kernels::*;
use super::{select_ntt_strategy, NttDirection, NttKernelKind, OMEGA_LOG_ORDER};

/// Launch choices for measuring the retained-monomial schedule. These affect
/// cache traffic, never the representation, output ordering or allocation bound.
#[derive(Clone, Copy, Debug)]
pub struct RetainedLdeOptions {
    pub stream_first_coset_stores: bool,
    pub prefetch_next_monomial_column: bool,
}

impl Default for RetainedLdeOptions {
    fn default() -> Self {
        Self {
            stream_first_coset_stores: false,
            prefetch_next_monomial_column: true,
        }
    }
}

fn check_shape(
    monomials: &DeviceSlice<BF>,
    coset: &DeviceSlice<BF>,
    log_n: usize,
    log_f: usize,
    coset_index: usize,
) {
    assert!((20..=24).contains(&log_n));
    assert!(log_n + log_f <= OMEGA_LOG_ORDER as usize);
    assert!(coset_index < (1usize << log_f));
    assert_eq!(monomials.len(), coset.len());
    assert_eq!(monomials.len() % (1usize << log_n), 0);
    assert_eq!(monomials.as_ptr() as usize % 16, 0);
    assert_eq!(coset.as_ptr() as usize % 16, 0);
}

fn three_pass(log_n: usize, properties: &DeviceProperties) -> bool {
    let strategy = select_ntt_strategy(NttDirection::NaturalToBitrev, log_n, 1, 1, properties)
        .expect("retained LDE requires a natural-to-bitrev strategy");
    matches!(
        strategy.passes.last().unwrap().kernel,
        NttKernelKind::NaturalToBitrevFinal { .. }
    )
}

/// Preserve `raw` while producing true natural monomials and one bitreversed
/// coset. The monomial allocation serves as pre-tail scratch; the boundary
/// completes monomials, writes them back before scaling, and starts the coset.
/// No allocation or bulk copy is performed by this function.
pub fn hypercube_to_retained_monomials_and_coset(
    raw: &DeviceSlice<BF>,
    monomials: &mut DeviceSlice<BF>,
    coset: &mut DeviceSlice<BF>,
    log_n: usize,
    log_f: usize,
    coset_index: usize,
    options: RetainedLdeOptions,
    properties: &DeviceProperties,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(raw.len(), monomials.len());
    assert_eq!(raw.as_ptr() as usize % 16, 0);
    check_shape(monomials, coset, log_n, log_f, coset_index);
    // SAFETY: raw is a separate, equally sized allocation, alive throughout
    // scheduling; all launches use the same stream.
    unsafe {
        initialize(
            raw.as_ptr(),
            monomials,
            coset,
            log_n,
            log_f,
            coset_index,
            options,
            properties,
            stream,
        )
    }
}

/// Consumes the hypercube representation in `raw_to_monomials`, leaving true
/// natural monomials there and one bitreversed coset in separate output storage.
/// All earlier readers of raw values must be ordered before these launches.
/// The single mutable source argument avoids constructing aliased Rust views.
pub fn hypercube_to_retained_monomials_and_coset_in_place(
    raw_to_monomials: &mut DeviceSlice<BF>,
    coset: &mut DeviceSlice<BF>,
    log_n: usize,
    log_f: usize,
    coset_index: usize,
    options: RetainedLdeOptions,
    properties: &DeviceProperties,
    stream: &CudaStream,
) -> CudaResult<()> {
    check_shape(raw_to_monomials, coset, log_n, log_f, coset_index);
    // SAFETY: initialize permits exact source/destination aliasing. Hypercube
    // passes read and rewrite disjoint block-owned row sets, with their existing
    // warp/block barriers before stores. Coset output is a separate allocation.
    unsafe {
        initialize(
            raw_to_monomials.as_ptr(),
            raw_to_monomials,
            coset,
            log_n,
            log_f,
            coset_index,
            options,
            properties,
            stream,
        )
    }
}

unsafe fn initialize(
    raw: *const BF,
    monomials: &mut DeviceSlice<BF>,
    coset: &mut DeviceSlice<BF>,
    log_n: usize,
    log_f: usize,
    coset_index: usize,
    options: RetainedLdeOptions,
    properties: &DeviceProperties,
    stream: &CudaStream,
) -> CudaResult<()> {
    let n = 1usize << log_n;
    let columns = monomials.len() / n;
    let three = three_pass(log_n, properties);
    let shift = (OMEGA_LOG_ORDER as usize - log_n - log_f) as i32;
    for column in 0..columns {
        let offset = column * n;
        let input = PtrAndStride::new(raw.add(offset), n);
        let m_const = PtrAndStride::new(monomials.as_ptr().add(offset), n);
        let m_mut = MutPtrAndStride::new(monomials.as_mut_ptr().add(offset), n);
        let c_const = PtrAndStride::new(coset.as_ptr().add(offset), n);
        let c_mut = MutPtrAndStride::new(coset.as_mut_ptr().add(offset), n);
        if three {
            // The preceding column's terminal already computed this finest
            // pass, including when the next raw column aliases its M output.
            launch_pre_tail_lsb_column(
                input,
                m_const,
                m_mut,
                log_n,
                column != 0,
                properties,
                stream,
            )?;
            let config = CudaLaunchConfig::basic((n / 8192) as u32, 256, stream);
            launch_boundary(
                m_mut,
                c_mut,
                log_n,
                log_f,
                coset_index,
                options.stream_first_coset_stores,
                &config,
            )?;
            let next = (column + 1 < columns).then(|| {
                (
                    PtrAndStride::new(raw.add(offset + n), n),
                    MutPtrAndStride::new(monomials.as_mut_ptr().add(offset + n), n),
                )
            });
            launch_natural_to_bitrev_tail(
                c_const, c_mut, log_n, 1, 1, 0, None, next, properties, stream,
            )?;
        } else if log_n == 20 {
            launch_nonfinal_passes(input, m_const, m_mut, log_n, stream)?;
            let config = CudaLaunchConfig::basic((n / 8192) as u32, 256, stream);
            // Exactly one coset and one column: multiple coset blocks must
            // never concurrently read and write the same monomial source.
            let args =
                LdeFusedWritebackArguments::new(m_mut, c_mut, 20, coset_index as i32, shift, 1, 0);
            LdeFusedWritebackFunction(ab_natural_lde_fused_boundary_writeback_log_n_20_kernel)
                .launch(&config, &args)?;
            let mut config = CudaLaunchConfig::basic((n / 4096) as u32, 256, stream);
            config.dynamic_smem_bytes = 4096 * size_of::<BF>();
            let args = NaturalToBitrevFinalArguments::new(c_const, c_mut, 20, 1, 0);
            NaturalToBitrevFinalFunction(
                ab_natural_monomials_to_bitrev_evals_last_12_stages_compact_kernel,
            )
            .launch(&config, &args)?;
        } else {
            // The original full-LDE schedule is also unfused in this regime.
            launch_hypercube_two_pass_column(input, m_const, m_mut, log_n, false, stream)?;
            generate_column(
                &monomials[offset..offset + n],
                &mut coset[offset..offset + n],
                log_n,
                log_f,
                coset_index,
                None,
                properties,
                stream,
            )?;
        }
    }
    Ok(())
}

fn launch_boundary(
    monomials: MutPtrAndStride<BF>,
    coset: MutPtrAndStride<BF>,
    log_n: usize,
    log_f: usize,
    coset_index: usize,
    stream_stores: bool,
    config: &CudaLaunchConfig,
) -> CudaResult<()> {
    if log_f == 1 && coset_index == 1 {
        let kernel = match (log_n, stream_stores) {
            (21, true) => ab_natural_lde_fused_boundary_writeback_out_cs_log_n_21_c1_kernel,
            (22, true) => ab_natural_lde_fused_boundary_writeback_out_cs_log_n_22_c1_kernel,
            (23, true) => ab_natural_lde_fused_boundary_writeback_out_cs_log_n_23_c1_kernel,
            (24, true) => ab_natural_lde_fused_boundary_writeback_out_cs_log_n_24_c1_kernel,
            (21, false) => ab_natural_lde_fused_boundary_writeback_out_cg_log_n_21_c1_kernel,
            (22, false) => ab_natural_lde_fused_boundary_writeback_out_cg_log_n_22_c1_kernel,
            (23, false) => ab_natural_lde_fused_boundary_writeback_out_cg_log_n_23_c1_kernel,
            (24, false) => ab_natural_lde_fused_boundary_writeback_out_cg_log_n_24_c1_kernel,
            _ => unreachable!(),
        };
        let args = LdeFusedWritebackFixedArguments::new(monomials, coset);
        LdeFusedWritebackFixedFunction(kernel).launch(config, &args)
    } else {
        let args = LdeFusedWritebackArguments::new(
            monomials,
            coset,
            log_n as i32,
            coset_index as i32,
            (OMEGA_LOG_ORDER as usize - log_n - log_f) as i32,
            1,
            0,
        );
        let kernel = if stream_stores {
            ab_natural_lde_fused_boundary_writeback_out_cs_kernel
        } else {
            ab_natural_lde_fused_boundary_writeback_out_cg_kernel
        };
        LdeFusedWritebackFunction(kernel).launch(config, &args)
    }
}

/// Regenerate one coset from retained natural monomials. Callers enqueue all
/// readers of the preceding coset before reusing the output on this stream.
pub fn retained_monomials_to_coset(
    monomials: &DeviceSlice<BF>,
    coset: &mut DeviceSlice<BF>,
    log_n: usize,
    log_f: usize,
    coset_index: usize,
    options: RetainedLdeOptions,
    properties: &DeviceProperties,
    stream: &CudaStream,
) -> CudaResult<()> {
    check_shape(monomials, coset, log_n, log_f, coset_index);
    let n = 1usize << log_n;
    let columns = monomials.len() / n;
    if !three_pass(log_n, properties) && columns != 0 {
        // Compact regeneration has no cross-column finest/prefetch dependency.
        // Use the existing L2-bounded column tiling instead of paying two
        // launches per column. The large two-pass strategy uses its own bound.
        let strategy =
            select_ntt_strategy(NttDirection::NaturalToBitrev, log_n, columns, 1, properties)
                .expect("retained regeneration requires a natural-to-bitrev strategy");
        let input = DeviceMatrix::new(monomials, n);
        let mut output = DeviceMatrixMut::new(coset, n);
        let shift = (OMEGA_LOG_ORDER as usize - log_n - log_f) as u32;
        if log_n == 20 {
            return natural_monomials_to_bitrev_evals_2_pass_compact(
                &input,
                &mut output,
                log_n,
                coset_index,
                shift,
                1,
                columns,
                1,
                strategy.columns_per_launch,
                false,
                stream,
            );
        }
        return natural_monomials_to_bitrev_evals_2_pass(
            &input,
            &mut output,
            log_n,
            coset_index,
            shift,
            1,
            columns,
            1,
            strategy.columns_per_launch,
            false,
            stream,
        );
    }

    for column in 0..columns {
        let offset = column * n;
        let next = (options.prefetch_next_monomial_column && column + 1 < columns)
            .then(|| unsafe { monomials.as_ptr().add(offset + n) });
        generate_column(
            &monomials[offset..offset + n],
            &mut coset[offset..offset + n],
            log_n,
            log_f,
            coset_index,
            next,
            properties,
            stream,
        )?;
    }
    Ok(())
}

fn generate_column(
    monomials: &DeviceSlice<BF>,
    coset: &mut DeviceSlice<BF>,
    log_n: usize,
    log_f: usize,
    coset_index: usize,
    prefetch: Option<*const BF>,
    properties: &DeviceProperties,
    stream: &CudaStream,
) -> CudaResult<()> {
    let n = 1usize << log_n;
    let shift = (OMEGA_LOG_ORDER as usize - log_n - log_f) as u32;
    if three_pass(log_n, properties) {
        let input = PtrAndStride::new(monomials.as_ptr(), n);
        let output_const = PtrAndStride::new(coset.as_ptr(), n);
        let output = MutPtrAndStride::new(coset.as_mut_ptr(), n);
        let config = CudaLaunchConfig::basic((n / 8192) as u32, 256, stream);
        let args = MonomialsToEvalsCompactArguments::new(
            input,
            output,
            false,
            log_n as i32,
            coset_index as i32,
            shift as i32,
            1,
            0,
        );
        MonomialsToEvalsCompactFunction(
            ab_natural_monomials_to_bitrev_evals_initial_8_stages_kernel,
        )
        .launch(&config, &args)?;
        launch_natural_to_bitrev_tail(
            output_const,
            output,
            log_n,
            1,
            1,
            0,
            prefetch,
            None,
            properties,
            stream,
        )
    } else {
        let input = DeviceMatrix::new(monomials, n);
        let mut output = DeviceMatrixMut::new(coset, n);
        if log_n == 20 {
            natural_monomials_to_bitrev_evals_2_pass_compact(
                &input,
                &mut output,
                log_n,
                coset_index,
                shift,
                1,
                1,
                1,
                1,
                false,
                stream,
            )
        } else {
            natural_monomials_to_bitrev_evals_2_pass(
                &input,
                &mut output,
                log_n,
                coset_index,
                shift,
                1,
                1,
                1,
                1,
                false,
                stream,
            )
        }
    }
}
