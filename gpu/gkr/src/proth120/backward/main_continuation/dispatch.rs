use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use gpu_prover_context::ProverContext;

use super::binding::{MainContinuationLaunchPr, PR_MAIN_CONTINUATION_BLOCK_THREADS};
use super::publication::ContinuationPublishedLevelPr;
use crate::backward::GkrEqSizes;
use crate::proth120::backward::main_continuation_window_manifest::{
    PrGkrBwdMainContinuationWindowArguments, PrGkrBwdMainContinuationWindowSignature,
    PrMainContinuationWindowKernelEntry, PR_MAIN_CONTINUATION_WINDOW_KERNELS,
};
use crate::upstream::PR;

pub(crate) fn resolve_pr_main_continuation_kernel(
    mask: u16,
) -> &'static PrMainContinuationWindowKernelEntry {
    u8::try_from(mask)
        .ok()
        .and_then(|mask| {
            PR_MAIN_CONTINUATION_WINDOW_KERNELS
                .iter()
                .find(|entry| entry.mask == mask)
        })
        .unwrap_or_else(|| panic!("Proth120 main continuation has no kernel for mask {mask:#04x}"))
}

#[derive(Clone, Copy)]
struct MainContinuationKernelPr(PrGkrBwdMainContinuationWindowSignature);

impl KernelFunction for MainContinuationKernelPr {
    type Signature = PrGkrBwdMainContinuationWindowSignature;

    fn as_ptr(&self) -> *const std::os::raw::c_void {
        self.0 as *const std::os::raw::c_void
    }
}

pub(crate) struct MainContinuationLaunchedPr {
    published: ContinuationPublishedLevelPr,
    row_tiles: usize,
    partials: *const PR,
    reduced_tensor: *mut PR,
    eq_sizes: GkrEqSizes,
}

impl MainContinuationLaunchedPr {
    pub(crate) fn row_tiles(&self) -> usize {
        self.row_tiles
    }

    pub(crate) fn partials(&self) -> *const PR {
        self.partials
    }

    pub(crate) fn reduced_tensor(&self) -> *mut PR {
        self.reduced_tensor
    }

    pub(crate) fn eq_sizes(&self) -> GkrEqSizes {
        self.eq_sizes
    }

    pub(crate) fn into_published_level(self) -> ContinuationPublishedLevelPr {
        self.published
    }
}

pub(crate) fn launch_main_continuation_pr(
    launch: MainContinuationLaunchPr<'_>,
    context: &ProverContext,
) -> CudaResult<MainContinuationLaunchedPr> {
    let config = CudaLaunchConfig::basic(
        launch.binding.row_tiles,
        PR_MAIN_CONTINUATION_BLOCK_THREADS,
        context.get_exec_stream(),
    );
    MainContinuationKernelPr(launch.kernel.symbol).launch(
        &config,
        &PrGkrBwdMainContinuationWindowArguments::new(*launch.binding),
    )?;
    Ok(MainContinuationLaunchedPr {
        published: launch.published,
        row_tiles: launch.row_tiles,
        partials: launch.binding.partials.cast_const(),
        reduced_tensor: launch.reduced_tensor,
        eq_sizes: launch.binding.eq_sizes,
    })
}
