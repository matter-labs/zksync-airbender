//! Production partition selection and first-owner folding. The compiler has
//! already checked atom coverage; this binder supplies runtime pointers/types.
use super::*;
use crate::backward::window::common::BWD_SOURCE_LANE_COLUMN_BITS;
use gpu_core::primitives::context::{DeviceAllocation, DeviceProperties};
use gpu_gkr_compiler::{select_main_continuation_partition, MainContinuationPartitionPlan};

fn source_bytes(desc: &MainContinuationWindowLaunchBinding, source: u16) -> usize {
    let lane = desc.source[usize::from(source)].src;
    match desc.slot[usize::from(lane >> BWD_SOURCE_LANE_COLUMN_BITS)].origin {
        BWD_COEFF_ORIGIN_READ_EXT => 16,
        BWD_COEFF_ORIGIN_READ_BASE => 4,
        BWD_COEFF_ORIGIN_PROCEDURAL => 1,
        _ => unreachable!("the checked binder only produces known source origins"),
    }
}

pub(super) fn select(
    program: &MainContinuationWindowProgram,
    desc: &MainContinuationWindowLaunchBinding,
    device: &DeviceProperties,
    mask: u16,
    rows: usize,
) -> Option<MainContinuationPartitionPlan> {
    if desc.publication_fold != 3 {
        return None;
    }
    let paired = main_continuation_use_paired(
        device.sm_count,
        desc.program_words as usize,
        desc.row_tiles as usize,
    );
    // Preserve the measured universal-body restriction, without another shape
    // family. Other masks keep their existing static-selector implementation.
    if !paired && use_fused_x01_specialization(desc.program_words as usize) && mask != 0x1f {
        return None;
    }
    let e4 = (0..desc.source_count)
        .filter(|&s| source_bytes(desc, s) == 16)
        .count();
    select_main_continuation_partition(
        &program.partitions,
        usize::from(desc.source_count),
        e4,
        rows,
        desc.row_tiles as usize,
        device.sm_count * MAIN_CONTINUATION_WINDOW_FUSED_MIN_BLOCKS as usize,
        device.l2_cache_size_bytes,
    )
    .cloned()
}

pub(super) fn launch(
    launch: &MainContinuationWindowLaunch<'_>,
    plan: &MainContinuationPartitionPlan,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<E4>> {
    let cells = launch.row_tiles * MAIN_CONTINUATION_WINDOW_TENSOR_CELLS;
    let mut partials = context.alloc::<E4>(cells * plan.parts.len(), AllocationPlacement::Top)?;
    enqueue(launch, plan, partials.as_mut_ptr(), context)?;
    // The caller retains this owner through scheduling the ordinary reducer.
    Ok(partials)
}

pub(super) fn enqueue(
    launch: &MainContinuationWindowLaunch<'_>,
    plan: &MainContinuationPartitionPlan,
    partials: *mut E4,
    context: &ProverContext,
) -> CudaResult<()> {
    let cells = launch.row_tiles * MAIN_CONTINUATION_WINDOW_TENSOR_CELLS;
    let universal = MAIN_CONTINUATION_WINDOW_KERNELS
        .iter()
        .find(|k| k.mask == MAIN_CONTINUATION_WINDOW_UNIVERSAL_MASK)
        .expect("universal continuation kernel");
    // Partitioned windows use paired operands beyond the unsplit policy's
    // small-program grid cutoff. Keep the existing static-selector range;
    // partition selection already checks resident coverage.
    let kernel = MainContinuationWindowEvaluatorKernel(
        if use_fused_x01_specialization(launch.binding.program_words as usize) {
            universal.fused_x01_symbol
        } else {
            ab_gkr_main_cont_operand_1f_b2
        },
    );
    let config = CudaLaunchConfig::basic(
        launch.binding.row_tiles,
        MAIN_CONTINUATION_WINDOW_FUSED_THREADS,
        context.get_exec_stream(),
    );
    for (index, part) in plan.parts.iter().enumerate() {
        let mut desc = *launch.binding;
        desc.program.fill(0);
        desc.program[..part.words.len()].copy_from_slice(&part.words);
        desc.program_words = part.words.len() as u16;
        if index != 0 {
            desc.c_init_coeff = BWD_COEFF_NONE;
        }
        // SAFETY: K disjoint banks of exactly `cells` values in this allocation.
        desc.partials = unsafe { partials.add(index * cells) };
        let (offsets, sources) = build_fold_lists(
            part.fold_sources.iter().map(|&source| FoldItem {
                source,
                // Balance all fold traffic, including each E4 publication.
                // Procedural sources generate their inputs without global reads.
                byte_weight: match source_bytes(&launch.binding, source) {
                    1 => core::mem::size_of::<E4>(),
                    input_bytes => {
                        (input_bytes << desc.publication_fold) + core::mem::size_of::<E4>()
                    }
                },
            }),
            usize::from(desc.source_count),
            false,
        )
        .expect("compiler-checked first-owner fold list");
        desc.fold_list_offsets = offsets;
        desc.fold_sources.fill(0);
        desc.fold_sources[..sources.len()].copy_from_slice(&sources);
        kernel.launch(&config, &GkrBwdMainContinuationWindow3Arguments::new(desc))?;
    }
    Ok(())
}
