use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use super::{assert_no_overlap, checked_bytes, checked_u64, SEED_BYTES};

cuda_kernel!(
    HashBytes,
    ab_keccak256_hash_bytes_kernel(input: *const u8, len: u64, out: *mut u8)
);

#[doc(hidden)]
pub fn hash_bytes(
    input: &DeviceSlice<u8>,
    out: &mut DeviceSlice<u8>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "hash_bytes";
    assert_eq!(
        out.len(),
        SEED_BYTES,
        "keccak256::hash_bytes: out.len() == 32"
    );
    checked_bytes::<u8>(NAME, input.len());
    checked_bytes::<u8>(NAME, out.len());
    let len = checked_u64(NAME, input.len());
    assert_no_overlap(NAME, input, out);
    let args = HashBytesArguments::new(input.as_ptr(), len, out.as_mut_ptr());
    HashBytesFunction::default().launch(&CudaLaunchConfig::basic(1, 1, stream), &args)
}
