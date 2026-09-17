//! Source-disjoint R0 grid partitions. The program owns checked CPU candidates;
//! selection uses device properties and occupancy of the linked entries. No
//! calibration work or synchronization is added to the proof stream.
use super::*;
use crate::backward::window::binding::bind_window_words;
use core::mem::size_of;
use era_cudart::device::{device_get_attribute, get_device};
use era_cudart::occupancy::max_active_blocks_per_multiprocessor;
use era_cudart_sys::{CudaDeviceAttr, CudaError};
use gpu_gkr_compiler::window::partition::{
    policy::{R0PartitionHardware, REQUESTED_PARTS},
    R0PartitionPlan,
};
use gpu_gkr_compiler::WindowProgram;

const MAX_PARTS: usize = REQUESTED_PARTS[REQUESTED_PARTS.len() - 1];

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub(super) struct PartitionBounds {
    pub(super) parts: u32,
    pub(super) ends: [[u32; 4]; MAX_PARTS],
}
const _: () = {
    assert!(MAX_PARTS == 16);
    assert!(size_of::<PartitionBounds>() == 260);
    assert!(std::mem::align_of::<PartitionBounds>() == 4);
    assert!(std::mem::offset_of!(PartitionBounds, ends) == 4);
    assert!(
        size_of::<WindowLaunchBinding>() + 4 + size_of::<PartitionBounds>()
            <= gpu_gkr_compiler::KERNEL_ARGUMENT_CEILING_BYTES
    );
};

cuda_kernel!(Grid3, ab_gkr_r0_partition_b3(desc: WindowLaunchBinding, scalar_seed: u32, bounds: PartitionBounds));
cuda_kernel!(GridUnit4, ab_gkr_r0_partition_unit_b4(desc: WindowLaunchBinding, scalar_seed: u32, bounds: PartitionBounds));
cuda_kernel!(GridTails4, ab_gkr_r0_partition_tails_b4(desc: WindowLaunchBinding, scalar_seed: u32, bounds: PartitionBounds));

fn hardware(kernel: Kernel, context: &ProverContext) -> CudaResult<R0PartitionHardware> {
    let device = get_device()?;
    let properties = context.get_device_properties();
    let attr = |attribute| device_get_attribute(attribute, device).map(f64::from);
    let clock_hz = attr(CudaDeviceAttr::ClockRate)? * 1000.0;
    let memory_clock_hz = attr(CudaDeviceAttr::MemoryClockRate)? * 1000.0;
    let bus_bits = attr(CudaDeviceAttr::GlobalMemoryBusWidth)?;
    let threads = 288;
    let original = match kernel {
        Kernel::General3 => {
            max_active_blocks_per_multiprocessor(&General3Function::default(), threads, 0)
        }

        Kernel::Unit4 => {
            max_active_blocks_per_multiprocessor(&Unit4Function::default(), threads, 0)
        }
        Kernel::Tails4 => {
            max_active_blocks_per_multiprocessor(&Tails4Function::default(), threads, 0)
        }
    }?;
    let grid = match kernel {
        Kernel::General3 => {
            max_active_blocks_per_multiprocessor(&Grid3Function::default(), threads, 0)
        }

        Kernel::Unit4 => {
            max_active_blocks_per_multiprocessor(&GridUnit4Function::default(), threads, 0)
        }
        Kernel::Tails4 => {
            max_active_blocks_per_multiprocessor(&GridTails4Function::default(), threads, 0)
        }
    }?;
    if original <= 0 || grid <= 0 {
        return Err(CudaError::ErrorInvalidConfiguration);
    }
    let hardware = R0PartitionHardware {
        sm_count: properties.sm_count,
        l2_bytes: properties.l2_cache_size_bytes,
        clock_hz,
        memory_bytes_per_second: memory_clock_hz * bus_bits * 2.0 / 8.0,
        // Peak warp-issue estimate for the four scheduler partitions of
        // modern NVIDIA SMs. This is an architecture prior, not a CUDA
        // attribute or a guarantee that a kernel attains the rate.
        issue_slots_per_sm_cycle: 4.0,
        original_blocks_per_sm: original as usize,
        grid_blocks_per_sm: grid as usize,
    };
    Ok(hardware)
}

pub(crate) fn select<'a>(
    program: &'a R0WindowProgram,
    row_tiles: usize,
    context: &ProverContext,
) -> CudaResult<&'a R0PartitionPlan> {
    program
        .partition_candidates
        .select(row_tiles, &hardware(program.kernel, context)?)
        .map_err(|_| CudaError::ErrorInvalidValue)
}

/// Producer tiles and reducer tiles differ by the number of source partitions.
pub(crate) fn reduction_tiles(row_tiles: usize, parts: usize) -> CudaResult<usize> {
    if row_tiles == 0 || !(1..=MAX_PARTS).contains(&parts) {
        return Err(CudaError::ErrorInvalidValue);
    }
    row_tiles
        .checked_mul(parts)
        .filter(|&tiles| tiles <= u32::MAX as usize)
        .ok_or(CudaError::ErrorInvalidValue)
}

pub(crate) fn partials_len(row_tiles: usize, parts: usize) -> CudaResult<usize> {
    reduction_tiles(row_tiles, parts)?
        .checked_add(1)
        .and_then(|tiles| tiles.checked_mul(WINDOW_TAIL_TENSOR_CELLS))
        .ok_or(CudaError::ErrorInvalidValue)
}

/// Bind each checked part with the original addressing and bank, concatenate its
/// records, and retain one descriptor. Metadata and seed belong to the original
/// selected lowering; only the record sequence and section endpoints change.
pub(super) fn bind<E: Copy>(
    program: &R0WindowProgram,
    plan: &R0PartitionPlan,
    storage: &GpuGKRStorage<BF, E>,
    folding_steps: usize,
    scratch: WindowRuntimeScratch,
) -> Result<(Box<WindowLaunchBinding>, Option<PartitionBounds>), WindowBindError> {
    assert!(!plan.parts.is_empty() && plan.parts.len() <= MAX_PARTS);
    let addressing = intern_window_addressing(storage, &program.window)?;
    bind_addressed(&program.window, plan, &addressing, folding_steps, scratch)
}

pub(super) fn bind_addressed(
    program: &WindowProgram,
    plan: &R0PartitionPlan,
    addressing: &super::super::binding::WindowAddressing,
    folding_steps: usize,
    scratch: WindowRuntimeScratch,
) -> Result<(Box<WindowLaunchBinding>, Option<PartitionBounds>), WindowBindError> {
    assert!(!plan.parts.is_empty() && plan.parts.len() <= MAX_PARTS);
    let mut combined = build_window_binding(program, addressing, folding_steps, scratch)?;
    if plan.parts.len() == 1 {
        // Keep the original body and original record order for K1.
        return Ok((combined, None));
    }
    combined.program.fill(0);
    let mut bounds = PartitionBounds {
        parts: plan.parts.len() as u32,
        ..Default::default()
    };
    let mut base = 0usize;
    for (index, part) in plan.parts.iter().enumerate() {
        let count = part.sections[3] as usize;
        bind_window_words(
            part,
            addressing,
            &mut combined.program[4 * base..4 * (base + count)],
        )?;
        for section in 0..4 {
            bounds.ends[index][section] = base as u32 + part.sections[section];
        }
        base += count;
    }
    assert_eq!(base, program.sections[3] as usize);
    Ok((combined, Some(bounds)))
}

pub(super) fn launch(
    window: &Launch,
    bounds: PartitionBounds,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(
        window.reduction_tiles,
        window.row_tiles * bounds.parts as usize
    );
    let config = CudaLaunchConfig::builder()
        .grid_dim((window.row_tiles as u32, bounds.parts))
        .block_dim(288)
        .stream(context.get_exec_stream())
        .build();
    let binding = *window.binding;
    let seed = window.scalar_seed;
    match window.kernel {
        Kernel::General3 => {
            Grid3Function::default().launch(&config, &Grid3Arguments::new(binding, seed, bounds))
        }
        Kernel::Unit4 => GridUnit4Function::default()
            .launch(&config, &GridUnit4Arguments::new(binding, seed, bounds)),
        Kernel::Tails4 => GridTails4Function::default()
            .launch(&config, &GridTails4Arguments::new(binding, seed, bounds)),
    }
}

#[cfg(test)]
mod cpu_tests {
    use super::*;

    #[test]
    fn cpu_partition_scratch_extents() {
        for rows in [1, 4096, 8192, 16384, 65536] {
            for parts in 1..=MAX_PARTS {
                assert_eq!(reduction_tiles(rows, parts).unwrap(), rows * parts);
                assert_eq!(partials_len(rows, parts).unwrap(), 27 * (rows * parts + 1));
            }
        }
        for (rows, parts) in [
            (0, 1),
            (1, 0),
            (1, MAX_PARTS + 1),
            (usize::MAX, 2),
            (u32::MAX as usize, 2),
        ] {
            assert!(reduction_tiles(rows, parts).is_err());
            assert!(partials_len(rows, parts).is_err());
        }
    }
}
