use crate::upstream::GKRMemoryLayout;
use crate::witness::memory_unrolled::InitsAndTeardownsLayouts;
use crate::witness::trace_unrolled::{InitsAndTeardownsTraceDevice, InitsAndTeardownsTraceRaw};
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::device_structures::{DeviceMatrixMutImpl, MutPtrAndStride};
use gpu_core::primitives::field::PR;
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use gpu_ops::simple::set_to_zero;

cuda_kernel!(GenerateProth120InitsAndTeardowns,
    ab_pr_generate_inits_and_teardowns_kernel(
        init_and_teardown_layouts: InitsAndTeardownsLayouts,
        trace: InitsAndTeardownsTraceRaw,
        memory: MutPtrAndStride<PR>,
        page_size_log2: u32,
        pages_per_set_log2: u32,
    )
);

pub fn generate_inits_and_teardowns(
    layout: &GKRMemoryLayout,
    trace_len_log2: u32,
    page_size_log2: u32,
    trace: &InitsAndTeardownsTraceDevice,
    memory: &mut impl DeviceMatrixMutImpl<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(memory.cols(), layout.total_width);
    assert_eq!(memory.stride(), 1usize << trace_len_log2);
    assert!(page_size_log2 < trace_len_log2);
    set_to_zero(memory.slice_mut(), stream)?;
    let num_pages = trace.page_indices.len();
    if num_pages == 0 {
        return Ok(());
    }
    let total_words = num_pages
        .checked_shl(page_size_log2)
        .expect("inits-and-teardowns total word count overflows usize");
    assert!(total_words <= u32::MAX as usize);
    let pages_per_set_log2 = trace_len_log2 - page_size_log2;
    let layouts = (&layout.teardown_sets).into();
    let trace_raw: InitsAndTeardownsTraceRaw = trace.into();
    let memory = memory.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 8, total_words as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateProth120InitsAndTeardownsArguments::new(
        layouts,
        trace_raw,
        memory,
        page_size_log2,
        pages_per_set_log2,
    );
    GenerateProth120InitsAndTeardownsFunction::default().launch(&config, &args)
}
