pub(crate) mod binding;

use core::mem::size_of;

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use gpu_core::primitives::utils::WARP_SIZE;
use gpu_prover_context::ProverContext;

use gpu_gkr_compiler::backward::{R0Kernel, R0WindowProgram};
use gpu_gkr_compiler::window::partition::R0PartitionPlan;

use self::binding::{
    bind_r0_window_pr, PartitionBoundsPr, WindowLaunchBindingPr, WindowRuntimeScratchPr,
    PR_WINDOW_MAX_PARTS,
};
use crate::backward::window::binding::{window_row_tiles, WindowBindError};
use crate::proth120::backward::banks::CoefficientBankViewPr;
use crate::upstream::PR;
use crate::GpuGKRStorage;

pub(crate) const PR_WINDOW_TAIL_TENSOR_CELLS: usize = 27;
pub(crate) const PR_R0_ARGUMENT_BYTES: usize =
    (size_of::<WindowLaunchBindingPr>() + size_of::<u32>()).next_multiple_of(8);
pub(crate) const PR_R0_PARTITION_ARGUMENT_BYTES: usize =
    (size_of::<WindowLaunchBindingPr>() + size_of::<u32>() + size_of::<PartitionBoundsPr>())
        .next_multiple_of(8);
pub(crate) const PR_FOLD_WEIGHTS_ARGUMENT_BYTES: usize =
    (2 * size_of::<*const PR>() + size_of::<u32>()).next_multiple_of(8);
pub(crate) const PR_WINDOW_TAIL_REDUCE_ARGUMENT_BYTES: usize =
    (size_of::<*const PR>() + size_of::<u32>()).next_multiple_of(8) + size_of::<*const PR>();
pub(crate) const PR_WINDOW_TAIL_ARGUMENT_BYTES: usize =
    (8 * size_of::<*const PR>() + size_of::<u32>()).next_multiple_of(8);
const _: () = {
    assert!(PR_R0_ARGUMENT_BYTES == 19_544);
    assert!(PR_R0_PARTITION_ARGUMENT_BYTES == 19_800);
    assert!(PR_FOLD_WEIGHTS_ARGUMENT_BYTES == 24);
    assert!(PR_WINDOW_TAIL_REDUCE_ARGUMENT_BYTES == 24);
    assert!(PR_WINDOW_TAIL_ARGUMENT_BYTES == 72);
};
const PR_WINDOW_TAIL_REDUCE_BLOCK_THREADS: u32 = 256;
const PR_WINDOW_TAIL_BLOCK_THREADS: u32 = 256;

cuda_kernel!(
    PrWindowTailReduce,
    ab_pr_gkr_window_tail_reduce_kernel(partials: *const PR, row_tiles: u32, tensor_out: *mut PR)
);

cuda_kernel!(
    PrWindowTail,
    ab_pr_gkr_window_tail_kernel(
        tensor: *const PR,
        prev_claim_coords: *const PR,
        seed_io: *mut u8,
        claim_io: *mut PR,
        eq_prefactor_io: *mut PR,
        coeffs_out: *mut PR,
        challenges_out: *mut PR,
        active_eq_slot_base: *mut PR,
        active_eq_size_before_fold: u32,
    )
);

cuda_kernel!(
    PrBuildFoldWeights,
    ab_pr_gkr_bwd_build_fold_weights_kernel(fold_weights: *mut PR, claim_point: *const PR, round: u32)
);

pub(crate) struct WindowTailStatePr {
    pub partials: *const PR,
    pub row_tiles: usize,
    pub reduced_tensor: *mut PR,
    pub prev_claim_coords: *const PR,
    pub seed: *mut u8,
    pub claim: *mut PR,
    pub eq_prefactor: *mut PR,
    pub coeffs_out: *mut PR,
    pub challenges_out: *mut PR,
    pub active_eq_slot_base: *mut PR,
    pub active_eq_size_before_fold: u32,
}

pub(crate) fn launch_window_tail_pr(
    state: &WindowTailStatePr,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(state.row_tiles > 0, "Proth120 window tail needs row tiles");
    let row_tiles =
        u32::try_from(state.row_tiles).expect("Proth120 window tail row tiles exceed u32");
    for (name, pointer) in [
        ("partials", state.partials as usize),
        ("reduced tensor", state.reduced_tensor as usize),
        (
            "previous claim coordinates",
            state.prev_claim_coords as usize,
        ),
        ("seed", state.seed as usize),
        ("claim", state.claim as usize),
        ("eq prefactor", state.eq_prefactor as usize),
        ("coefficients", state.coeffs_out as usize),
        ("challenges", state.challenges_out as usize),
        ("active eq slot", state.active_eq_slot_base as usize),
    ] {
        assert!(pointer != 0, "Proth120 window tail {name} pointer is null");
    }
    let stream = context.get_exec_stream();
    let reduce_config = CudaLaunchConfig::basic(
        PR_WINDOW_TAIL_TENSOR_CELLS as u32,
        PR_WINDOW_TAIL_REDUCE_BLOCK_THREADS,
        stream,
    );
    PrWindowTailReduceFunction::default().launch(
        &reduce_config,
        &PrWindowTailReduceArguments::new(state.partials, row_tiles, state.reduced_tensor),
    )?;
    let config = CudaLaunchConfig::basic(1, PR_WINDOW_TAIL_BLOCK_THREADS, stream);
    PrWindowTailFunction::default().launch(
        &config,
        &PrWindowTailArguments::new(
            state.reduced_tensor,
            state.prev_claim_coords,
            state.seed,
            state.claim,
            state.eq_prefactor,
            state.coeffs_out,
            state.challenges_out,
            state.active_eq_slot_base,
            state.active_eq_size_before_fold,
        ),
    )
}

pub(crate) fn launch_build_fold_weights_pr(
    fold_weights: *mut PR,
    point: *const PR,
    round: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(round >= 1, "Proth120 fold weights are continuation-only");
    assert!(
        !fold_weights.is_null() && !point.is_null(),
        "Proth120 fold weights need device pointers"
    );
    let config = CudaLaunchConfig::basic(1, WARP_SIZE, context.get_exec_stream());
    PrBuildFoldWeightsFunction::default().launch(
        &config,
        &PrBuildFoldWeightsArguments::new(fold_weights, point, round),
    )
}

const PR_WINDOW_BLOCK_THREADS: u32 = 288;
const PR_WINDOW_SCALAR_SEED_NONE: u32 = 0xffff;

cuda_kernel!(
    PrR0General,
    ab_pr_gkr_bwd_r0_kernel(desc: WindowLaunchBindingPr, scalar_seed: u32)
);
cuda_kernel!(
    PrR0Unit,
    ab_pr_gkr_bwd_r0_unit_kernel(desc: WindowLaunchBindingPr, scalar_seed: u32)
);
cuda_kernel!(
    PrR0Tails,
    ab_pr_gkr_bwd_r0_tails_kernel(desc: WindowLaunchBindingPr, scalar_seed: u32)
);
cuda_kernel!(
    PrR0PartitionGeneral,
    ab_pr_gkr_bwd_r0_partition_kernel(
        desc: WindowLaunchBindingPr,
        scalar_seed: u32,
        bounds: PartitionBoundsPr
    )
);
cuda_kernel!(
    PrR0PartitionUnit,
    ab_pr_gkr_bwd_r0_partition_unit_kernel(
        desc: WindowLaunchBindingPr,
        scalar_seed: u32,
        bounds: PartitionBoundsPr
    )
);
cuda_kernel!(
    PrR0PartitionTails,
    ab_pr_gkr_bwd_r0_partition_tails_kernel(
        desc: WindowLaunchBindingPr,
        scalar_seed: u32,
        bounds: PartitionBoundsPr
    )
);

pub(crate) struct R0WindowLaunchPr {
    binding: Box<WindowLaunchBindingPr>,
    bounds: Option<PartitionBoundsPr>,
    kernel: R0Kernel,
    shape: u16,
    scalar_seed: u32,
    pub row_tiles: usize,
    pub reduction_tiles: usize,
    pub reduced_tensor: *mut PR,
}

pub(crate) fn r0_partials_len_pr(trace_len: usize, parts: usize) -> usize {
    assert!(
        (1..=PR_WINDOW_MAX_PARTS).contains(&parts),
        "Proth120 R0 partition count {parts} is unsupported"
    );
    PR_WINDOW_TAIL_TENSOR_CELLS * (window_row_tiles(trace_len) * parts + 1)
}

pub(crate) fn bind_r0_pr(
    program: &R0WindowProgram,
    plan: Option<&R0PartitionPlan>,
    storage: &GpuGKRStorage<PR, PR>,
    folding_steps: usize,
    scratch: WindowRuntimeScratchPr,
    bank: CoefficientBankViewPr,
) -> Result<R0WindowLaunchPr, WindowBindError> {
    let (binding, bounds) =
        bind_r0_window_pr(&program.window, plan, storage, folding_steps, scratch, bank)?;
    let row_tiles = window_row_tiles(1usize << folding_steps);
    let parts = bounds.map_or(1, |bounds| bounds.parts as usize);
    let reduction_tiles = row_tiles * parts;
    let required = r0_partials_len_pr(1usize << folding_steps, parts);
    if required > scratch.partials_capacity {
        return Err(WindowBindError::Capacity {
            resource: "partition partials",
            required,
            capacity: scratch.partials_capacity,
        });
    }
    let reduced_tensor = unsafe {
        scratch
            .partials
            .add(PR_WINDOW_TAIL_TENSOR_CELLS * reduction_tiles)
    };
    Ok(R0WindowLaunchPr {
        binding,
        bounds,
        kernel: program.kernel,
        shape: program.window.shape.bits(),
        scalar_seed: program
            .scalar_seed
            .map_or(PR_WINDOW_SCALAR_SEED_NONE, u32::from),
        row_tiles,
        reduction_tiles,
        reduced_tensor,
    })
}

pub(crate) fn launch_r0_pr(window: &R0WindowLaunchPr, context: &ProverContext) -> CudaResult<()> {
    launch_r0_pr_with(window, window.kernel, context)
}

pub(crate) fn launch_r0_pr_with(
    window: &R0WindowLaunchPr,
    kernel: R0Kernel,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(
        window.shape & !kernel.shape_mask(),
        0,
        "Proth120 R0 program shape {:#x} is unsupported by {kernel:?}",
        window.shape
    );
    let row_tiles = u32::try_from(window.row_tiles).expect("Proth120 R0 row tiles exceed u32");
    let stream = context.get_exec_stream();
    let desc = *window.binding;
    let seed = window.scalar_seed;
    let Some(bounds) = window.bounds else {
        let config = CudaLaunchConfig::basic(row_tiles, PR_WINDOW_BLOCK_THREADS, stream);
        return match kernel {
            R0Kernel::General3 => PrR0GeneralFunction::default()
                .launch(&config, &PrR0GeneralArguments::new(desc, seed)),
            R0Kernel::Unit4 => {
                PrR0UnitFunction::default().launch(&config, &PrR0UnitArguments::new(desc, seed))
            }
            R0Kernel::Tails4 => {
                PrR0TailsFunction::default().launch(&config, &PrR0TailsArguments::new(desc, seed))
            }
        };
    };
    assert_eq!(
        window.reduction_tiles,
        window.row_tiles * bounds.parts as usize
    );
    let config = CudaLaunchConfig::builder()
        .grid_dim((row_tiles, bounds.parts))
        .block_dim(PR_WINDOW_BLOCK_THREADS)
        .stream(stream)
        .build();
    match kernel {
        R0Kernel::General3 => PrR0PartitionGeneralFunction::default().launch(
            &config,
            &PrR0PartitionGeneralArguments::new(desc, seed, bounds),
        ),
        R0Kernel::Unit4 => PrR0PartitionUnitFunction::default().launch(
            &config,
            &PrR0PartitionUnitArguments::new(desc, seed, bounds),
        ),
        R0Kernel::Tails4 => PrR0PartitionTailsFunction::default().launch(
            &config,
            &PrR0PartitionTailsArguments::new(desc, seed, bounds),
        ),
    }
}
