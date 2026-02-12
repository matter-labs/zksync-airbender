use crate::field::BaseField;
use era_cudart::cuda_kernel;
use era_cudart::device::{device_get_attribute, get_device};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaDeviceAttr::MultiProcessorCount;
use std::ptr::null_mut;

type BF = BaseField;

cuda_kernel!(Bench, bench, values: *const BF);

bench!(ab_add_bench_kernel);
bench!(ab_mul_bench_kernel);

pub fn add_bench(stream: &CudaStream) -> CudaResult<()> {
    let device_id = get_device()?;
    let mpc = device_get_attribute(MultiProcessorCount, device_id)? as u32;
    let config = CudaLaunchConfig::basic(mpc, 1024, stream);
    let args = BenchArguments::new(null_mut());
    BenchFunction(ab_add_bench_kernel).launch(&config, &args)
}

pub fn mul_bench(stream: &CudaStream) -> CudaResult<()> {
    let device_id = get_device()?;
    let mpc = device_get_attribute(MultiProcessorCount, device_id)? as u32;
    let config = CudaLaunchConfig::basic(mpc, 1024, stream);
    let args = BenchArguments::new(null_mut());
    BenchFunction(ab_mul_bench_kernel).launch(&config, &args)
}
