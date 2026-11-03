//! MAIN R0 endpoints are reconstructed from the same input pairs as the leading
//! coefficient. The program, scalar seed and kernel family are selected together.

use era_cudart::{
    cuda_kernel,
    execution::{CudaLaunchConfig, KernelFunction},
    result::CudaResult,
};
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr_compiler::backward::{R0Kernel as Kernel, R0WindowProgram};
use gpu_prover_context::ProverContext;

use super::binding::{
    build_window_binding, intern_window_addressing, window_row_tiles, WindowBindError,
    WindowLaunchBinding, WindowRuntimeScratch,
};
use super::tail::WINDOW_TAIL_TENSOR_CELLS;
use crate::GpuGKRStorage;

cuda_kernel!(General3, ab_gkr_r0_b3(desc: WindowLaunchBinding, scalar_seed: u32));
cuda_kernel!(Unit4, ab_gkr_r0_unit_b4(desc: WindowLaunchBinding, scalar_seed: u32));
cuda_kernel!(Tails4, ab_gkr_r0_tails_b4(desc: WindowLaunchBinding, scalar_seed: u32));

pub(crate) struct Launch {
    bounds: Option<partition::PartitionBounds>,
    binding: Box<WindowLaunchBinding>,
    kernel: Kernel,
    scalar_seed: u32,
    pub row_tiles: usize,
    pub reduction_tiles: usize,
    pub reduced_tensor: *mut E4,
}

pub(crate) fn bind<E: Copy>(
    program: &R0WindowProgram,
    storage: &GpuGKRStorage<BF, E>,
    folding_steps: usize,
    scratch: WindowRuntimeScratch,
    plan: &gpu_gkr_compiler::window::partition::R0PartitionPlan,
) -> Result<Launch, WindowBindError> {
    let (binding, bounds) = partition::bind(program, plan, storage, folding_steps, scratch)?;
    let row_tiles = window_row_tiles(1usize << folding_steps);
    let reduction_tiles =
        partition::reduction_tiles(row_tiles, plan.parts.len()).map_err(|_| {
            WindowBindError::Capacity {
                resource: "partition reduction tiles",
                required: row_tiles.saturating_mul(plan.parts.len()),
                capacity: u32::MAX as usize,
            }
        })?;
    let required = WINDOW_TAIL_TENSOR_CELLS * (reduction_tiles + 1);
    if required > scratch.partials_capacity {
        return Err(WindowBindError::Capacity {
            resource: "partition partials",
            required,
            capacity: scratch.partials_capacity,
        });
    }
    // SAFETY: the binding capacity check covers both the partial tensor and its reduction.
    let reduced_tensor = unsafe {
        scratch
            .partials
            .add(WINDOW_TAIL_TENSOR_CELLS * reduction_tiles)
    };
    Ok(Launch {
        bounds,
        binding,
        kernel: program.kernel,
        scalar_seed: u32::from(program.scalar_seed.unwrap_or(u16::MAX)),
        row_tiles,
        reduction_tiles,
        reduced_tensor,
    })
}

pub(crate) fn launch(window: &Launch, context: &ProverContext) -> CudaResult<()> {
    if let Some(bounds) = window.bounds {
        return partition::launch(window, bounds, context);
    }
    let config = CudaLaunchConfig::basic(window.row_tiles as u32, 288, context.get_exec_stream());
    match window.kernel {
        Kernel::General3 => General3Function::default().launch(
            &config,
            &General3Arguments::new(*window.binding, window.scalar_seed),
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

pub(crate) mod partition;
