use era_cudart::execution::{CudaLaunchConfig, KernelArguments, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{
    cuda_kernel, cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function,
};
use era_cudart_sys::{cudaFuncSetAttribute, CudaFuncAttribute};
use gpu_core::primitives::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride, PtrAndStride,
};
use gpu_core::primitives::field::PR;
use std::ops::Range;

use super::context::{DeviceContext, TwiddleDescriptor};
use super::{validate_context_log, validate_disjoint, validate_matrix, validate_slice};

pub(crate) const MAX_COLUMNS_PER_LAUNCH: usize = 65535;

cuda_kernel_signature_arguments_and_function!(
    pub(crate) Dit,
    inputs: PtrAndStride<PR>, outputs: MutPtrAndStride<PR>, descriptor: TwiddleDescriptor,
    log_n: u32, start_stage: u32,
);
macro_rules! dit_kernel {
    ($name:ident) => {
        cuda_kernel_declaration!($name(
            inputs: PtrAndStride<PR>, outputs: MutPtrAndStride<PR>, descriptor: TwiddleDescriptor,
            log_n: u32, start_stage: u32,
        ));
    };
}
dit_kernel!(ab_pr_dit_nonfinal_5_stages_kernel);
dit_kernel!(ab_pr_dit_nonfinal_6_stages_kernel);
dit_kernel!(ab_pr_dit_nonfinal_7_stages_kernel);
dit_kernel!(ab_pr_dit_nonfinal_8_stages_kernel);
dit_kernel!(ab_pr_dit_final_8_stages_kernel);
dit_kernel!(ab_pr_dit_final_10_stages_kernel);
dit_kernel!(ab_pr_dit_final_12_stages_kernel);
dit_kernel!(ab_pr_dit_small_kernel);

cuda_kernel!(Scale, ab_pr_lde_scale_kernel(
    inputs: PtrAndStride<PR>, outputs: MutPtrAndStride<PR>, offset: *const PR, rows: u32,
));
cuda_kernel!(ScaleTable, ab_pr_lde_scale_table_kernel(
    inputs: *const PR, outputs: *mut PR, descriptor: TwiddleDescriptor, log_n: u32,
    log_domain: u32, k0: u32,
));
cuda_kernel!(Naturalize, ab_pr_naturalize_kernel(
    inputs: PtrAndStride<PR>, outputs: MutPtrAndStride<PR>, log_n: u32,
));
cuda_kernel!(NaturalizeNaive, ab_pr_naturalize_naive_kernel(
    values: MutPtrAndStride<PR>, log_n: u32,
));

#[derive(Clone, Copy, Debug)]
pub(crate) enum TransformPass {
    Small,
    Nonfinal(u32),
    Final(u32),
}

pub(crate) trait TransformPolicy {
    type Function: KernelFunction;
    type Arguments: KernelArguments<Signature = <Self::Function as KernelFunction>::Signature>;
    fn function(&self, pass: TransformPass) -> Self::Function;
    fn arguments(
        &self,
        source: PtrAndStride<PR>,
        target: MutPtrAndStride<PR>,
        log_n: u32,
        start_stage: u32,
    ) -> Self::Arguments;
}

pub(crate) struct DitPolicy(pub(crate) TwiddleDescriptor);
impl TransformPolicy for DitPolicy {
    type Function = DitFunction;
    type Arguments = DitArguments;
    fn function(&self, pass: TransformPass) -> DitFunction {
        DitFunction(match pass {
            TransformPass::Small => ab_pr_dit_small_kernel,
            TransformPass::Nonfinal(5) => ab_pr_dit_nonfinal_5_stages_kernel,
            TransformPass::Nonfinal(6) => ab_pr_dit_nonfinal_6_stages_kernel,
            TransformPass::Nonfinal(7) => ab_pr_dit_nonfinal_7_stages_kernel,
            TransformPass::Nonfinal(8) => ab_pr_dit_nonfinal_8_stages_kernel,
            TransformPass::Final(8) => ab_pr_dit_final_8_stages_kernel,
            TransformPass::Final(10) => ab_pr_dit_final_10_stages_kernel,
            TransformPass::Final(12) => ab_pr_dit_final_12_stages_kernel,
            _ => panic!("Proth120 NTT: unsupported transform pass {pass:?}"),
        })
    }
    fn arguments(
        &self,
        source: PtrAndStride<PR>,
        target: MutPtrAndStride<PR>,
        log_n: u32,
        start_stage: u32,
    ) -> DitArguments {
        DitArguments::new(source, target, self.0, log_n, start_stage)
    }
}

pub(crate) fn split_table(log_n: u32) -> &'static [u32] {
    match log_n {
        8 => &[8],
        9 => &[9],
        10 => &[10],
        11 => &[11],
        12 => &[12],
        13 => &[5, 8],
        14 => &[6, 8],
        15 => &[7, 8],
        16 => &[8, 8],
        17 => &[7, 10],
        18 => &[8, 10],
        19 => &[7, 12],
        20 => &[8, 12],
        21 => &[5, 8, 8],
        22 => &[7, 7, 8],
        23 => &[8, 7, 8],
        24 => &[8, 8, 8],
        25 => &[8, 7, 10],
        26 => &[8, 8, 10],
        _ => panic!("Proth120 NTT: log_n {log_n} outside 8..=26"),
    }
}

pub(crate) fn set_max_dynamic_smem(function: &impl KernelFunction, bytes: usize) -> CudaResult<()> {
    assert!(
        bytes <= i32::MAX as usize,
        "Proth120 NTT: dynamic shared memory size exceeds i32::MAX"
    );
    unsafe {
        cudaFuncSetAttribute(
            function.as_ptr(),
            CudaFuncAttribute::MaxDynamicSharedMemorySize,
            bytes as i32,
        )
        .wrap()
    }
}

pub(crate) fn launch_transform<P: TransformPolicy>(
    policy: &P,
    source: PtrAndStride<PR>,
    target: MutPtrAndStride<PR>,
    log_n: u32,
    cols: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    launch_transform_chunked(
        policy,
        source,
        target,
        log_n,
        cols,
        MAX_COLUMNS_PER_LAUNCH,
        stream,
    )
}

fn launch_transform_chunked<P: TransformPolicy>(
    policy: &P,
    source: PtrAndStride<PR>,
    target: MutPtrAndStride<PR>,
    log_n: u32,
    cols: usize,
    columns_per_launch: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        (0..=26).contains(&log_n),
        "Proth120 NTT: transform log_n {log_n} outside 0..=26"
    );
    assert!(
        (1..=MAX_COLUMNS_PER_LAUNCH).contains(&columns_per_launch),
        "Proth120 NTT: invalid columns_per_launch {columns_per_launch}"
    );
    let splits = if log_n <= 12 {
        &[][..]
    } else {
        split_table(log_n)
    };
    let mut start_stage = 0;
    let small_stages = [log_n];
    let passes = if splits.is_empty() {
        &small_stages[..]
    } else {
        splits
    };
    for &stages in passes {
        let is_small = log_n <= 12;
        let is_final = start_stage + stages == log_n;
        let pass = if is_small {
            TransformPass::Small
        } else if is_final {
            TransformPass::Final(stages)
        } else {
            TransformPass::Nonfinal(stages)
        };
        let function = policy.function(pass);
        let dynamic_bytes = if is_final {
            (1usize << stages) * size_of::<PR>()
        } else {
            0
        };
        if is_final && (stages >= 10 || is_small && log_n >= 11) {
            set_max_dynamic_smem(&function, dynamic_bytes)?;
        }
        let output_source = PtrAndStride::new(target.ptr as *const PR, target.stride);
        let input = if start_stage == 0 {
            source
        } else {
            output_source
        };
        for column in (0..cols).step_by(columns_per_launch) {
            let chunk = (cols - column).min(columns_per_launch);
            let input = PtrAndStride::new(
                unsafe {
                    input.ptr.add(
                        column
                            .checked_mul(input.stride)
                            .expect("Proth120 NTT: input column offset overflow"),
                    )
                },
                input.stride,
            );
            let output = MutPtrAndStride::new(
                unsafe {
                    target.ptr.add(
                        column
                            .checked_mul(target.stride)
                            .expect("Proth120 NTT: output column offset overflow"),
                    )
                },
                target.stride,
            );
            let mut config = if is_small {
                CudaLaunchConfig::basic((1, chunk as u32), ((1u32 << log_n) / 4).max(1), stream)
            } else if is_final {
                CudaLaunchConfig::basic(
                    (1u32 << (log_n - stages), chunk as u32),
                    1u32 << (stages - 2),
                    stream,
                )
            } else {
                assert!(
                    log_n - start_stage >= 11,
                    "Proth120 NTT: nonfinal transform region below 2048 rows"
                );
                let y = 1u32 << (log_n - start_stage - 11);
                assert!(y <= 65535, "Proth120 NTT: grid.y exceeds 65535");
                CudaLaunchConfig::basic((1u32 << start_stage, y, chunk as u32), 512, stream)
            };
            config.dynamic_smem_bytes = dynamic_bytes;
            function.launch(
                &config,
                &policy.arguments(input, output, log_n, start_stage),
            )?;
        }
        start_stage += stages;
    }
    Ok(())
}

pub(super) fn naturalize(
    values: MutPtrAndStride<PR>,
    log_n: u32,
    cols: usize,
    columns_per_launch: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    for column in (0..cols).step_by(columns_per_launch) {
        let chunk = (cols - column).min(columns_per_launch);
        let target = MutPtrAndStride::new(
            unsafe {
                values.ptr.add(
                    column
                        .checked_mul(values.stride)
                        .expect("Proth120 NTT: naturalize column offset overflow"),
                )
            },
            values.stride,
        );
        if log_n < 10 {
            let config = CudaLaunchConfig::basic((1u32 << (log_n - 8), chunk as u32), 256, stream);
            NaturalizeNaiveFunction::default()
                .launch(&config, &NaturalizeNaiveArguments::new(target, log_n))?;
        } else {
            let m = 1u32 << (log_n / 2 - 5);
            let config = CudaLaunchConfig::basic(
                (m * (m + 1) / 2, 1u32 << (log_n & 1), chunk as u32),
                (32, 2, 2),
                stream,
            );
            let source = PtrAndStride::new(target.ptr as *const PR, target.stride);
            NaturalizeFunction::default()
                .launch(&config, &NaturalizeArguments::new(source, target, log_n))?;
        }
    }
    Ok(())
}

pub fn lde_coset(
    ctx: &DeviceContext,
    inputs: &(impl DeviceMatrixChunkImpl<PR> + ?Sized),
    outputs: &mut (impl DeviceMatrixChunkMutImpl<PR> + ?Sized),
    offset: &DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    lde_coset_chunked(ctx, inputs, outputs, offset, MAX_COLUMNS_PER_LAUNCH, stream)
}

pub(super) fn lde_coset_chunked(
    ctx: &DeviceContext,
    inputs: &(impl DeviceMatrixChunkImpl<PR> + ?Sized),
    outputs: &mut (impl DeviceMatrixChunkMutImpl<PR> + ?Sized),
    offset: &DeviceSlice<PR>,
    columns_per_launch: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    let (log_n, input_range) = validate_matrix(inputs, 8, 26, "Proth120 LDE input");
    let (_, output_range) = validate_matrix(outputs, 8, 26, "Proth120 LDE output");
    validate_context_log(ctx, log_n);
    assert_eq!(
        inputs.rows(),
        outputs.rows(),
        "Proth120 LDE: input/output rows differ"
    );
    assert_eq!(
        inputs.cols(),
        outputs.cols(),
        "Proth120 LDE: input/output columns differ"
    );
    assert_eq!(offset.len(), 1, "Proth120 LDE: offset length must be 1");
    let offset_range = validate_slice(offset, "Proth120 LDE offset");
    validate_disjoint(
        &input_range,
        &output_range,
        "Proth120 LDE: input/output overlap",
    );
    validate_disjoint(
        &offset_range,
        &output_range,
        "Proth120 LDE: offset/output overlap",
    );
    assert!(
        (1..=MAX_COLUMNS_PER_LAUNCH).contains(&columns_per_launch),
        "Proth120 LDE: invalid columns_per_launch {columns_per_launch}"
    );
    let rows = inputs.rows();
    let source = inputs.as_ptr_and_stride();
    let target = outputs.as_mut_ptr_and_stride();
    for column in (0..inputs.cols()).step_by(columns_per_launch) {
        let cols = (inputs.cols() - column).min(columns_per_launch);
        let input = PtrAndStride::new(
            unsafe {
                source.ptr.add(
                    column
                        .checked_mul(source.stride)
                        .expect("Proth120 LDE: input column offset overflow"),
                )
            },
            source.stride,
        );
        let output = MutPtrAndStride::new(
            unsafe {
                target.ptr.add(
                    column
                        .checked_mul(target.stride)
                        .expect("Proth120 LDE: output column offset overflow"),
                )
            },
            target.stride,
        );
        let config =
            CudaLaunchConfig::basic((rows.div_ceil(8 * 256) as u32, cols as u32), 256, stream);
        ScaleFunction::default().launch(
            &config,
            &ScaleArguments::new(input, output, offset.as_ptr(), rows as u32),
        )?;
    }
    let scaled = PtrAndStride::new(target.ptr as *const PR, target.stride);
    launch_transform_chunked(
        &DitPolicy(ctx.descriptor()),
        scaled,
        target,
        log_n,
        outputs.cols(),
        columns_per_launch,
        stream,
    )?;
    naturalize(target, log_n, outputs.cols(), columns_per_launch, stream)
}

pub fn lde_cosets_batched(
    ctx: &DeviceContext,
    inputs: &DeviceSlice<PR>,
    log_domain: u32,
    coset_range: Range<u32>,
    outputs: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        inputs.len().is_power_of_two(),
        "Proth120 batched LDE: input length must be a power of two"
    );
    let log_n = inputs.len().trailing_zeros();
    assert!(
        (8..=26).contains(&log_n),
        "Proth120 batched LDE: log_n {log_n} outside 8..=26"
    );
    assert!(
        log_n <= log_domain && log_domain <= ctx.log_max_domain(),
        "Proth120 batched LDE: log_domain {log_domain} outside {log_n}..={}",
        ctx.log_max_domain()
    );
    assert!(
        coset_range.start <= coset_range.end,
        "Proth120 batched LDE: reversed coset range"
    );
    assert!(
        coset_range.end <= 1u32 << (log_domain - log_n),
        "Proth120 batched LDE: coset range exceeds logical domain"
    );
    let count = (coset_range.end - coset_range.start) as usize;
    let rows = inputs.len();
    let expected = count
        .checked_mul(rows)
        .expect("Proth120 batched LDE: output length overflow");
    assert_eq!(
        outputs.len(),
        expected,
        "Proth120 batched LDE: output length differs from coset range"
    );
    let input_range = validate_slice(inputs, "Proth120 batched LDE input");
    let output_range = validate_slice(outputs, "Proth120 batched LDE output");
    validate_disjoint(
        &input_range,
        &output_range,
        "Proth120 batched LDE: input/output overlap",
    );
    if count == 0 {
        return Ok(());
    }
    let descriptor = ctx.descriptor();
    for column in (0..count).step_by(MAX_COLUMNS_PER_LAUNCH) {
        let cols = (count - column).min(MAX_COLUMNS_PER_LAUNCH);
        let output = unsafe {
            outputs.as_mut_ptr().add(
                column
                    .checked_mul(rows)
                    .expect("Proth120 batched LDE: column offset overflow"),
            )
        };
        let config = CudaLaunchConfig::basic((rows as u32 / 256, cols as u32), 256, stream);
        ScaleTableFunction::default().launch(
            &config,
            &ScaleTableArguments::new(
                inputs.as_ptr(),
                output,
                descriptor,
                log_n,
                log_domain,
                coset_range.start + column as u32,
            ),
        )?;
    }
    let target = MutPtrAndStride::new(outputs.as_mut_ptr(), rows);
    let source = PtrAndStride::new(target.ptr as *const PR, rows);
    launch_transform(&DitPolicy(descriptor), source, target, log_n, count, stream)?;
    naturalize(target, log_n, count, MAX_COLUMNS_PER_LAUNCH, stream)
}

cuda_kernel_signature_arguments_and_function!(
    ConvertCosetLeaves,
    coset: *mut PR, log_n: u32, descriptor: TwiddleDescriptor, offset: *const PR,
);
cuda_kernel_signature_arguments_and_function!(
    ConvertGatheredLeaves,
    leaves: *mut PR, indices: *const u32, count: u32, log_coset: u32,
    descriptor: TwiddleDescriptor, offset: *const PR,
);

macro_rules! leaf_kernels {
    ($coset:ident, $gathered:ident) => {
        cuda_kernel_declaration!($coset(
            coset: *mut PR, log_n: u32, descriptor: TwiddleDescriptor, offset: *const PR,
        ));
        cuda_kernel_declaration!($gathered(
            leaves: *mut PR, indices: *const u32, count: u32, log_coset: u32,
            descriptor: TwiddleDescriptor, offset: *const PR,
        ));
    };
}
leaf_kernels!(
    ab_pr_convert_coset_leaves_1_kernel,
    ab_pr_convert_gathered_leaves_1_kernel
);
leaf_kernels!(
    ab_pr_convert_coset_leaves_2_kernel,
    ab_pr_convert_gathered_leaves_2_kernel
);
leaf_kernels!(
    ab_pr_convert_coset_leaves_3_kernel,
    ab_pr_convert_gathered_leaves_3_kernel
);
leaf_kernels!(
    ab_pr_convert_coset_leaves_4_kernel,
    ab_pr_convert_gathered_leaves_4_kernel
);

fn validate_leaf_shape(
    ctx: &DeviceContext,
    log_coset: u32,
    log_values: u32,
    offset: &DeviceSlice<PR>,
) {
    assert!(
        (8..=26).contains(&log_coset),
        "Proth120 leaf conversion: log_coset {log_coset} outside 8..=26"
    );
    validate_context_log(ctx, log_coset);
    assert!(
        log_values <= 4 && log_values <= log_coset,
        "Proth120 leaf conversion: log_values_per_leaf {log_values} exceeds min(4, log_coset)"
    );
    assert_eq!(
        offset.len(),
        1,
        "Proth120 leaf conversion: offset length must be one"
    );
}

pub fn convert_coset_leaves(
    ctx: &DeviceContext,
    coset: &mut DeviceSlice<PR>,
    log_values_per_leaf: u32,
    offset: &DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        coset.len().is_power_of_two(),
        "Proth120 leaf conversion: coset length must be a power of two"
    );
    let log_n = coset.len().trailing_zeros();
    validate_leaf_shape(ctx, log_n, log_values_per_leaf, offset);
    let values_range = validate_slice(coset, "Proth120 leaf conversion coset");
    let offset_range = validate_slice(offset, "Proth120 leaf conversion offset");
    validate_disjoint(
        &values_range,
        &offset_range,
        "Proth120 leaf conversion: coset/offset overlap",
    );
    let function = ConvertCosetLeavesFunction(match log_values_per_leaf {
        0 => return Ok(()),
        1 => ab_pr_convert_coset_leaves_1_kernel,
        2 => ab_pr_convert_coset_leaves_2_kernel,
        3 => ab_pr_convert_coset_leaves_3_kernel,
        4 => ab_pr_convert_coset_leaves_4_kernel,
        _ => unreachable!(),
    });
    let leaves = (coset.len() >> log_values_per_leaf) as u32;
    let config = CudaLaunchConfig::basic(leaves.div_ceil(256), 256, stream);
    function.launch(
        &config,
        &ConvertCosetLeavesArguments::new(
            coset.as_mut_ptr(),
            log_n,
            ctx.descriptor(),
            offset.as_ptr(),
        ),
    )
}

pub fn convert_gathered_leaves(
    ctx: &DeviceContext,
    leaves: &mut DeviceSlice<PR>,
    leaf_indices: &DeviceSlice<u32>,
    log_coset: u32,
    log_values_per_leaf: u32,
    offset: &DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    validate_leaf_shape(ctx, log_coset, log_values_per_leaf, offset);
    let expected = leaf_indices
        .len()
        .checked_mul(1usize << log_values_per_leaf)
        .expect("Proth120 gathered leaf conversion: length overflow");
    assert_eq!(leaves.len(), expected, "Proth120 gathered leaf conversion: leaves length must equal indices length << log_values_per_leaf");
    let values_range = validate_slice(leaves, "Proth120 gathered leaf conversion leaves");
    let index_range = validate_slice(leaf_indices, "Proth120 gathered leaf conversion indices");
    let offset_range = validate_slice(offset, "Proth120 gathered leaf conversion offset");
    validate_disjoint(
        &values_range,
        &index_range,
        "Proth120 gathered leaf conversion: leaves/indices overlap",
    );
    validate_disjoint(
        &values_range,
        &offset_range,
        "Proth120 gathered leaf conversion: leaves/offset overlap",
    );
    let count = u32::try_from(leaf_indices.len())
        .expect("Proth120 gathered leaf conversion: query count exceeds u32");
    if count == 0 || log_values_per_leaf == 0 {
        return Ok(());
    }
    let function = ConvertGatheredLeavesFunction(match log_values_per_leaf {
        1 => ab_pr_convert_gathered_leaves_1_kernel,
        2 => ab_pr_convert_gathered_leaves_2_kernel,
        3 => ab_pr_convert_gathered_leaves_3_kernel,
        4 => ab_pr_convert_gathered_leaves_4_kernel,
        _ => unreachable!(),
    });
    let config = CudaLaunchConfig::basic(count.div_ceil(256), 256, stream);
    function.launch(
        &config,
        &ConvertGatheredLeavesArguments::new(
            leaves.as_mut_ptr(),
            leaf_indices.as_ptr(),
            count,
            log_coset,
            ctx.descriptor(),
            offset.as_ptr(),
        ),
    )
}
