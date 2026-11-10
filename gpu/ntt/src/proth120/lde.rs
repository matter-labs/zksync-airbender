use era_cudart::execution::{CudaLaunchConfig, KernelArguments, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::{cudaFuncSetAttribute, CudaFuncAttribute};
use gpu_core::primitives::device_structures::{MutPtrAndStride, PtrAndStride};
use gpu_core::primitives::field::PR;

use super::context::TwiddleDescriptor;

pub(crate) const MAX_COLUMNS_PER_LAUNCH: usize = 65535;

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ChunkMap {
    pub(crate) gate: *const u32,
    pub(crate) strip_base: u32,
    pub(crate) strip_blocks: u32,
    pub(crate) strip_domain_bits: u32,
    pub(crate) reserved: u32,
}

impl ChunkMap {
    pub(crate) const FULL: Self = Self {
        gate: std::ptr::null(),
        strip_base: 0,
        strip_blocks: 1,
        strip_domain_bits: 0,
        reserved: 0,
    };
}

const _: () = assert!(core::mem::size_of::<ChunkMap>() == 24);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) Dit,
    inputs: PtrAndStride<PR>, outputs: MutPtrAndStride<PR>, descriptor: TwiddleDescriptor,
    log_n: u32, start_stage: u32, map: ChunkMap,
);
macro_rules! dit_kernel {
    ($name:ident) => {
        cuda_kernel_declaration!($name(
            inputs: PtrAndStride<PR>, outputs: MutPtrAndStride<PR>, descriptor: TwiddleDescriptor,
            log_n: u32, start_stage: u32, map: ChunkMap,
        ));
    };
}
dit_kernel!(ab_pr_dit_nonfinal_5_stages_narrow_kernel);
dit_kernel!(ab_pr_dit_nonfinal_6_stages_narrow_kernel);
dit_kernel!(ab_pr_dit_nonfinal_7_stages_narrow_kernel);
dit_kernel!(ab_pr_dit_nonfinal_8_stages_kernel);

#[derive(Clone, Copy, Debug)]
pub(crate) enum TransformPass {
    Small,
    Nonfinal(u32),
    NonfinalNarrow(u32),
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
        map: ChunkMap,
    ) -> Self::Arguments;
}

pub(crate) struct DitPolicy(pub(crate) TwiddleDescriptor);
impl TransformPolicy for DitPolicy {
    type Function = DitFunction;
    type Arguments = DitArguments;
    fn function(&self, pass: TransformPass) -> DitFunction {
        DitFunction(match pass {
            TransformPass::NonfinalNarrow(5) => ab_pr_dit_nonfinal_5_stages_narrow_kernel,
            TransformPass::NonfinalNarrow(6) => ab_pr_dit_nonfinal_6_stages_narrow_kernel,
            TransformPass::NonfinalNarrow(7) => ab_pr_dit_nonfinal_7_stages_narrow_kernel,
            TransformPass::Nonfinal(8) => ab_pr_dit_nonfinal_8_stages_kernel,
            _ => panic!("Proth120 NTT: unsupported transform pass {pass:?}"),
        })
    }
    fn arguments(
        &self,
        source: PtrAndStride<PR>,
        target: MutPtrAndStride<PR>,
        log_n: u32,
        start_stage: u32,
        map: ChunkMap,
    ) -> DitArguments {
        DitArguments::new(source, target, self.0, log_n, start_stage, map)
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
                &policy.arguments(input, output, log_n, start_stage, ChunkMap::FULL),
            )?;
        }
        start_stage += stages;
    }
    Ok(())
}
