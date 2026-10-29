use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use crate::upstream::PR;

cuda_kernel_signature_arguments_and_function!(
    PrSum32Probe,
    values: *const PR,
    segment_offsets: *const u32,
    segment_count: u32,
    sums: *mut PR,
);
cuda_kernel_declaration!(ab_pr_gkr_sum32_probe_kernel(
    values: *const PR,
    segment_offsets: *const u32,
    segment_count: u32,
    sums: *mut PR,
));

#[doc(hidden)]
pub fn pr_sum32_probe(
    values: &DeviceSlice<PR>,
    segment_offsets: &DeviceSlice<u32>,
    sums: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(
        segment_offsets.len(),
        sums.len() + 1,
        "Proth120 sum32 probe needs one offset per segment boundary"
    );
    let count = u32::try_from(sums.len()).expect("Proth120 sum32 probe segment count exceeds u32");
    let config = CudaLaunchConfig::basic(count.div_ceil(128).max(1), 128, stream);
    PrSum32ProbeFunction(ab_pr_gkr_sum32_probe_kernel).launch(
        &config,
        &PrSum32ProbeArguments::new(
            values.as_ptr(),
            segment_offsets.as_ptr(),
            count,
            sums.as_mut_ptr(),
        ),
    )
}
