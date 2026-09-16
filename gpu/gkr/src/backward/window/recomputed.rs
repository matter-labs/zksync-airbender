//! MAIN R0 endpoints are reconstructed from the same input pairs as the leading
//! coefficient. The program, scalar seed and kernel family are selected together.

use era_cudart::{
    cuda_kernel,
    execution::{CudaLaunchConfig, KernelFunction},
    result::CudaResult,
};
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr_compiler::{
    backward::recomputed_r0::{
        compile_recomputed_r0, compile_recomputed_r0_layer, reorder_window_boundaries,
    },
    window::WindowShape,
    window_manifest::WINDOWED_R0_BLOCK_THREADS,
    WindowProgram,
};
use gpu_prover_context::ProverContext;

use super::binding::{
    build_window_binding_capacity, intern_window_addressing, window_row_tiles, WindowBindError,
    WindowLaunchBinding, WindowRuntimeScratch,
};
use super::tail::WINDOW_TAIL_TENSOR_CELLS;
use crate::GpuGKRStorage;

/// Includes the largest grouped input-expression program with room for growth.
const PROGRAM_WORDS: usize = 8192;
type Binding = WindowLaunchBinding<PROGRAM_WORDS>;
const _: () = {
    assert!(size_of::<Binding>() == 19552);
    assert!(std::mem::offset_of!(Binding, program) == 1120);
    assert!(std::mem::offset_of!(Binding, immediates) == 17504);
    assert!(
        size_of::<Binding>() + size_of::<u32>() <= gpu_gkr_compiler::KERNEL_ARGUMENT_CEILING_BYTES
    );
};

cuda_kernel!(Recomputed3, ab_gkr_r0_recomputed_b3(desc: Binding, scalar_seed: u32));
cuda_kernel!(Packed4, ab_gkr_r0_recomputed_packed_b4(desc: Binding, scalar_seed: u32));
cuda_kernel!(Unit4, ab_gkr_r0_recomputed_unit_b4(desc: Binding, scalar_seed: u32));
cuda_kernel!(Tails4, ab_gkr_r0_recomputed_tails_b4(desc: Binding, scalar_seed: u32));

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kernel {
    Recomputed3,
    Packed4,
    Unit4,
    Tails4,
}

impl Kernel {
    fn shape_mask(self) -> u16 {
        match self {
            Self::Recomputed3 | Self::Packed4 => 0x7f7,
            Self::Unit4 => 0x771,
            Self::Tails4 => 0x7ff,
        }
    }
}

/// A single selected lowering owns its coefficient plans and scalar seed.
/// Selection never depends on a circuit name or a materialized output.
#[derive(Clone, Debug)]
pub struct RecomputedWindowProgram {
    pub window: WindowProgram,
    pub scalar_seed: Option<u16>,
    kernel: Kernel,
}

pub(crate) fn compile_programs(
    dag: &gkr_eval_ir::DagCircuit,
) -> Result<Vec<RecomputedWindowProgram>, String> {
    let original = compile_recomputed_r0(dag).map_err(|error| format!("recomputed R0: {error}"))?;
    original
        .into_iter()
        .enumerate()
        .map(|(layer, mut selected)| {
            let sections = selected.window.sections;
            // Empirical work-density weight. Read the original program so grouping
            // and record ordering cannot perturb the launch-bound decision.
            let b4 = u64::from(sections[0]) > 4 * u64::from(sections[3] - sections[0]);
            let kernel = if !b4 {
                Kernel::Recomputed3
            } else if selected.window.shape.bits() & !0x771 == 0 {
                Kernel::Unit4
            } else {
                let grouped = compile_recomputed_r0_layer(dag, layer, true)
                    .map_err(|error| format!("recomputed R0 linear tails: {error}"))?;
                if grouped.window.shape.contains(WindowShape::BF_LINEAR_TAIL) {
                    selected = grouped;
                    Kernel::Tails4
                } else {
                    Kernel::Packed4
                }
            };
            if selected.layer != layer || selected.window.shape.bits() & !kernel.shape_mask() != 0 {
                return Err(format!(
                    "recomputed R0 L{layer}: shape {:#x} is unsupported by {kernel:?}",
                    selected.window.shape.bits()
                ));
            }
            if selected.window.words.len() > PROGRAM_WORDS {
                return Err(format!(
                    "recomputed R0 L{layer}: {} program words exceed {PROGRAM_WORDS}",
                    selected.window.words.len()
                ));
            }
            reorder_window_boundaries(&mut selected.window);
            Ok(RecomputedWindowProgram {
                window: selected.window,
                scalar_seed: selected.scalar_seed,
                kernel,
            })
        })
        .collect()
}

pub(crate) struct Launch {
    binding: Box<Binding>,
    kernel: Kernel,
    scalar_seed: u32,
    pub row_tiles: usize,
    pub reduced_tensor: *mut E4,
}

pub(crate) fn bind<E: Copy>(
    program: &RecomputedWindowProgram,
    storage: &GpuGKRStorage<BF, E>,
    folding_steps: usize,
    scratch: WindowRuntimeScratch,
) -> Result<Launch, WindowBindError> {
    let addressing = intern_window_addressing(storage, &program.window)?;
    let binding =
        build_window_binding_capacity(&program.window, &addressing, folding_steps, scratch)?;
    let row_tiles = window_row_tiles(1usize << folding_steps);
    // SAFETY: the binding capacity check covers both the partial tensor and its reduction.
    let reduced_tensor = unsafe { scratch.partials.add(WINDOW_TAIL_TENSOR_CELLS * row_tiles) };
    Ok(Launch {
        binding,
        kernel: program.kernel,
        scalar_seed: u32::from(program.scalar_seed.unwrap_or(u16::MAX)),
        row_tiles,
        reduced_tensor,
    })
}

pub(crate) fn launch(window: &Launch, context: &ProverContext) -> CudaResult<()> {
    let config = CudaLaunchConfig::basic(
        window.row_tiles as u32,
        WINDOWED_R0_BLOCK_THREADS,
        context.get_exec_stream(),
    );
    match window.kernel {
        Kernel::Recomputed3 => Recomputed3Function::default().launch(
            &config,
            &Recomputed3Arguments::new(*window.binding, window.scalar_seed),
        ),
        Kernel::Packed4 => Packed4Function::default().launch(
            &config,
            &Packed4Arguments::new(*window.binding, window.scalar_seed),
        ),
        Kernel::Unit4 => Unit4Function::default().launch(
            &config,
            &Unit4Arguments::new(*window.binding, window.scalar_seed),
        ),
        Kernel::Tails4 => Tails4Function::default().launch(
            &config,
            &Tails4Arguments::new(*window.binding, window.scalar_seed),
        ),
    }
}

#[cfg(test)]
mod cpu_tests;
