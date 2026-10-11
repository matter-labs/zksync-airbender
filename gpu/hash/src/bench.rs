use era_cudart::cuda_kernel;
use era_cudart::device::{device_get_attribute, get_device};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaDeviceAttr::MultiProcessorCount;

use crate::keccak256::Digest;

cuda_kernel!(
    Bench,
    bench,
    bytes: u32,
    count: u64,
    out: *mut Digest
);

bench!(ab_keccak256_bench_unroll_kernel);
bench!(ab_keccak256_bench_loop_kernel);

pub fn bench_hash_count() -> CudaResult<usize> {
    let count = device_get_attribute(MultiProcessorCount, get_device()?)? as usize;
    Ok(count
        .checked_mul(2048 * 4)
        .expect("keccak256::bench_hash_count: count overflow"))
}

pub fn bench_keccak256(
    bytes: u32,
    round_loop: bool,
    out: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        matches!(bytes, 40 | 64 | 256 | 448),
        "keccak256::bench_keccak256: unsupported bytes"
    );
    let count = bench_hash_count()?;
    assert_eq!(
        out.len(),
        count,
        "keccak256::bench_keccak256: out.len() == count"
    );
    let grid =
        u32::try_from(count.div_ceil(128)).expect("keccak256::bench_keccak256: grid overflow");
    let function = if round_loop {
        ab_keccak256_bench_loop_kernel
    } else {
        ab_keccak256_bench_unroll_kernel
    };
    let args = BenchArguments::new(bytes, count as u64, out.as_mut_ptr());
    BenchFunction(function).launch(&CudaLaunchConfig::basic(grid, 128, stream), &args)
}
