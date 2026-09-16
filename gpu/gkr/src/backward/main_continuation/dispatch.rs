//! Kernel selection and enqueueing for prepared MAIN continuation windows.
use super::super::abi::MAIN_CONTINUATION_WINDOW_PUBLICATION_THREADS;
use super::super::generated_registry::{
    GkrBwdMainContinuationWindow3Arguments, GkrBwdMainContinuationWindow3Signature,
    MainContinuationWindowKernelEntry, MAIN_CONTINUATION_WINDOW_BLOCK_THREADS,
    MAIN_CONTINUATION_WINDOW_FUSED_MIN_BLOCKS, MAIN_CONTINUATION_WINDOW_FUSED_THREADS,
    MAIN_CONTINUATION_WINDOW_KERNELS, MAIN_CONTINUATION_WINDOW_UNIVERSAL_MASK,
};
use super::*;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use gpu_gkr_compiler::{MainContinuationWindowShape, MAIN_CONTINUATION_WINDOW_SHAPE_DEFINED_BITS};

#[path = "partition.rs"]
mod partition;

era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_operand_1f_b2(desc: MainContinuationWindowLaunchBinding));

const MAIN_CONTINUATION_WINDOW_X01_PROGRAM_WORD_THRESHOLD: usize = 1_024;
const MAIN_CONTINUATION_WINDOW_FUSED_X01_PROGRAM_WORD_UPPER_BOUND: usize = 5_500;
const MAIN_CONTINUATION_WINDOW_FUSION_MIN_WAVES: usize = 2;

fn main_continuation_launch_min_tiles(
    sm_count: usize,
    program_words: usize,
    canonical_input: bool,
) -> usize {
    assert!(sm_count > 0);
    if canonical_input
        && program_words >= MAIN_CONTINUATION_WINDOW_FUSED_X01_PROGRAM_WORD_UPPER_BOUND
    {
        sm_count
    } else {
        MAIN_CONTINUATION_WINDOW_FUSION_MIN_WAVES
            * MAIN_CONTINUATION_WINDOW_FUSED_MIN_BLOCKS as usize
            * sm_count
    }
}

fn main_continuation_use_paired(sm_count: usize, program_words: usize, row_tiles: usize) -> bool {
    assert!(sm_count > 0);
    let four_waves = 4 * MAIN_CONTINUATION_WINDOW_FUSED_MIN_BLOCKS as usize * sm_count;
    (program_words < MAIN_CONTINUATION_WINDOW_X01_PROGRAM_WORD_THRESHOLD
        && row_tiles >= sm_count.div_ceil(2)
        && row_tiles < four_waves)
        || (program_words >= MAIN_CONTINUATION_WINDOW_FUSED_X01_PROGRAM_WORD_UPPER_BOUND
            && row_tiles >= sm_count)
}

#[cfg(test)]
mod cpu_main_continuation_fusion_policy {
    use super::main_continuation_use_paired;

    #[test]
    fn cpu_paired_policy_scales_and_preserves_selector_boundaries() {
        for sm in [72_usize, 128, 188, 189] {
            let lower = sm.div_ceil(2);
            for (words, tiles, expected) in [
                (1023, lower - 1, false),
                (1023, lower, true),
                (1023, 8 * sm - 1, true),
                (1023, 8 * sm, false),
                (1024, 4 * sm, false),
                (5499, 4 * sm, false),
                (5500, sm - 1, false),
                (5500, sm, true),
                (5500, 8 * sm, true),
            ] {
                assert_eq!(
                    main_continuation_use_paired(sm, words, tiles),
                    expected,
                    "SMs={sm}, words={words}, tiles={tiles}"
                );
            }
        }
    }
}

fn resolve_kernel(
    shape: MainContinuationWindowShape,
) -> Result<&'static MainContinuationWindowKernelEntry, MainContinuationWindowBindError> {
    let mask = shape.bits();
    if mask & !MAIN_CONTINUATION_WINDOW_SHAPE_DEFINED_BITS != 0 {
        return Err(MainContinuationWindowBindError::UndefinedShapeBits { bits: mask });
    }
    MAIN_CONTINUATION_WINDOW_KERNELS
        .iter()
        .find(|entry| entry.mask == mask)
        .ok_or(MainContinuationWindowBindError::NoKernelForMask { mask })
}

fn use_x01_specialization(program_words: usize) -> bool {
    program_words >= MAIN_CONTINUATION_WINDOW_X01_PROGRAM_WORD_THRESHOLD
}

fn use_fused_x01_specialization(program_words: usize) -> bool {
    use_x01_specialization(program_words)
        && program_words < MAIN_CONTINUATION_WINDOW_FUSED_X01_PROGRAM_WORD_UPPER_BOUND
}

/// Output ownership returned only after the reader launch has been enqueued.
pub(crate) struct MainContinuationWindowLaunched {
    partition_partials: Option<gpu_core::primitives::context::DeviceAllocation<E4>>,
    published: ContinuationPublishedLevel,
    row_tiles: usize,
    reduced_tensor: *mut E4,
    eq_sizes: GkrEqSizes,
}

impl MainContinuationWindowLaunched {
    pub(crate) fn partials(&self, original: *const E4) -> *const E4 {
        self.partition_partials
            .as_ref()
            .map_or(original, |p| p.as_ptr())
    }
    pub(crate) fn into_published_level(self) -> ContinuationPublishedLevel {
        self.published
    }

    pub(crate) fn row_tiles(&self) -> usize {
        self.row_tiles
    }

    pub(crate) fn reduced_tensor(&self) -> *mut E4 {
        self.reduced_tensor
    }

    /// Exact pass-local Eq shape copied from the enqueued descriptor. The
    /// physical tail advances this host mirror once before boundary checking.
    pub(crate) fn eq_sizes(&self) -> GkrEqSizes {
        self.eq_sizes
    }
}

#[derive(Clone, Copy)]
pub(super) struct MainContinuationWindowEvaluatorKernel(GkrBwdMainContinuationWindow3Signature);

impl KernelFunction for MainContinuationWindowEvaluatorKernel {
    type Signature = GkrBwdMainContinuationWindow3Signature;

    fn as_ptr(&self) -> *const std::os::raw::c_void {
        self.0 as *const std::os::raw::c_void
    }
}

pub(super) enum WindowDispatch {
    Partitioned {
        plan: gpu_gkr_compiler::MainContinuationPartitionPlan,
        kernel: MainContinuationWindowEvaluatorKernel,
    },
    Fused(MainContinuationWindowEvaluatorKernel),
    Split {
        publish: MainContinuationWindowEvaluatorKernel,
        evaluate: Option<MainContinuationWindowEvaluatorKernel>,
    },
}

pub(super) fn select_dispatch(
    program: &MainContinuationWindowProgram,
    binding: &MainContinuationWindowLaunchBinding,
    input_kind: MainContinuationInputKind,
    rows: usize,
    context: &ProverContext,
) -> Result<WindowDispatch, MainContinuationWindowBindError> {
    let kernel = resolve_kernel(program.shape)?;
    let continuation = binding.publication_fold != 0;
    let words = usize::from(binding.program_words);
    let row_tiles = binding.row_tiles as usize;
    let device = context.get_device_properties();
    let paired = main_continuation_use_paired(device.sm_count, words, row_tiles);
    let fused_x01 = use_fused_x01_specialization(words);
    // Partitioned static-selector kernels are compiled only for the full shape.
    if continuation
        && (paired || !fused_x01 || kernel.mask == MAIN_CONTINUATION_WINDOW_UNIVERSAL_MASK)
    {
        if let Some(plan) = partition::select(program, binding, device, rows) {
            let symbol = if fused_x01 {
                MAIN_CONTINUATION_WINDOW_KERNELS
                    .iter()
                    .find(|k| k.mask == MAIN_CONTINUATION_WINDOW_UNIVERSAL_MASK)
                    .expect("universal continuation kernel")
                    .fused_x01_symbol
            } else {
                ab_gkr_main_cont_operand_1f_b2
            };
            return Ok(WindowDispatch::Partitioned {
                plan,
                kernel: MainContinuationWindowEvaluatorKernel(symbol),
            });
        }
    }
    if continuation
        && (paired
            || row_tiles
                >= main_continuation_launch_min_tiles(
                    device.sm_count,
                    words,
                    input_kind == MainContinuationInputKind::Later,
                ))
    {
        return Ok(WindowDispatch::Fused(
            MainContinuationWindowEvaluatorKernel(if paired {
                ab_gkr_main_cont_operand_1f_b2
            } else if fused_x01 {
                kernel.fused_x01_symbol
            } else {
                kernel.fused_symbol
            }),
        ));
    }
    Ok(WindowDispatch::Split {
        publish: MainContinuationWindowEvaluatorKernel(kernel.publication_symbol),
        evaluate: continuation.then(|| {
            MainContinuationWindowEvaluatorKernel(if use_x01_specialization(words) {
                kernel.x01_symbol
            } else {
                kernel.symbol
            })
        }),
    })
}

/// Consuming the preparation keeps its input borrow and output allocation alive
/// until the reader launch is enqueued.
pub(crate) fn launch_main_continuation_window(
    launch: MainContinuationWindowLaunch<'_>,
    context: &ProverContext,
) -> CudaResult<MainContinuationWindowLaunched> {
    let config =
        |blocks, threads| CudaLaunchConfig::basic(blocks, threads, context.get_exec_stream());
    let mut partition_partials = None;
    let mut row_tiles = launch.row_tiles;
    match &launch.dispatch {
        WindowDispatch::Partitioned { plan, kernel } => {
            partition_partials = Some(partition::launch(&launch, plan, *kernel, context)?);
            row_tiles *= plan.parts.len();
        }
        WindowDispatch::Fused(kernel) => kernel.launch(
            &config(
                launch.binding.row_tiles,
                MAIN_CONTINUATION_WINDOW_FUSED_THREADS,
            ),
            &GkrBwdMainContinuationWindow3Arguments::new(*launch.binding),
        )?,
        WindowDispatch::Split { publish, evaluate } => {
            let args = GkrBwdMainContinuationWindow3Arguments::new(*launch.binding);
            publish.launch(
                &config(
                    launch.publication_grid_blocks,
                    MAIN_CONTINUATION_WINDOW_PUBLICATION_THREADS,
                ),
                &args,
            )?;
            if let Some(kernel) = evaluate {
                kernel.launch(
                    &config(launch.grid_blocks, MAIN_CONTINUATION_WINDOW_BLOCK_THREADS),
                    &args,
                )?;
            }
        }
    }
    Ok(MainContinuationWindowLaunched {
        partition_partials,
        published: launch.published,
        row_tiles,
        reduced_tensor: launch.reduced_tensor,
        eq_sizes: launch.binding.eq_sizes,
    })
}
