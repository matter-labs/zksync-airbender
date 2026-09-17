//! MAIN R0 endpoints are reconstructed from the same input pairs as the leading
//! coefficient. The program, scalar seed and kernel family are selected together.

use era_cudart::{
    cuda_kernel,
    execution::{CudaLaunchConfig, KernelFunction},
    result::CudaResult,
};
use gpu_core::primitives::field::{BF, E4};
pub(crate) use gpu_gkr_compiler::backward::{
    R0Kernel as Kernel, R0WindowProgram as RecomputedWindowProgram,
};
use gpu_prover_context::ProverContext;

use super::binding::{
    build_window_binding, intern_window_addressing, window_row_tiles, WindowBindError,
    WindowLaunchBinding, WindowRuntimeScratch,
};
use super::tail::WINDOW_TAIL_TENSOR_CELLS;
use crate::GpuGKRStorage;

cuda_kernel!(Recomputed3, ab_gkr_r0_recomputed_b3(desc: WindowLaunchBinding, scalar_seed: u32));
cuda_kernel!(Unit4, ab_gkr_r0_recomputed_unit_b4(desc: WindowLaunchBinding, scalar_seed: u32));
cuda_kernel!(Tails4, ab_gkr_r0_recomputed_tails_b4(desc: WindowLaunchBinding, scalar_seed: u32));

pub(crate) struct Launch {
    binding: Box<WindowLaunchBinding>,
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
    let binding = build_window_binding(&program.window, &addressing, folding_steps, scratch)?;
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
    let config = CudaLaunchConfig::basic(window.row_tiles as u32, 288, context.get_exec_stream());
    match window.kernel {
        Kernel::Recomputed3 => Recomputed3Function::default().launch(
            &config,
            &Recomputed3Arguments::new(*window.binding, window.scalar_seed),
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
