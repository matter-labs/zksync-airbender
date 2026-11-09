//! Field-arithmetic micro-benchmark helpers.
//!
//! Each `bench_*` launches a compute-bound kernel (defined in
//! `native/bench/field.cu`) that hammers one field op (`add`/`mul` over
//! `bf`/`e2`/`e4`/`e6`) so the Criterion entry in `benches/field.rs` can
//! measure raw arithmetic throughput. Gated behind the `bench` feature; uses a
//! plain `era_cudart` stream and the `gpu_core_bench_native` archive.

use crate::primitives::field::BF;
use era_cudart::cuda_kernel;
use era_cudart::device::{device_get_attribute, get_device};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaDeviceAttr::MultiProcessorCount;
use std::ptr::null_mut;

cuda_kernel!(Bench, bench, values: *const BF, count: u32);

bench!(ab_add_bf_bench_kernel);
bench!(ab_mul_bf_bench_kernel);
bench!(ab_add_e2_bench_kernel);
bench!(ab_mul_e2_bench_kernel);
bench!(ab_add_e4_bench_kernel);
bench!(ab_mul_e4_bench_kernel);
bench!(ab_add_e6_bench_kernel);
bench!(ab_mul_e6_bench_kernel);

fn bench(f: BenchSignature, stream: &CudaStream) -> CudaResult<()> {
    let device_id = get_device()?;
    let mpc = device_get_attribute(MultiProcessorCount, device_id)? as u32;
    let config = CudaLaunchConfig::basic(mpc, 1024, stream);
    let args = BenchArguments::new(null_mut(), 0);
    BenchFunction(f).launch(&config, &args)
}

pub fn bench_add_bf(stream: &CudaStream) -> CudaResult<()> {
    bench(ab_add_bf_bench_kernel, stream)
}

pub fn bench_mul_bf(stream: &CudaStream) -> CudaResult<()> {
    bench(ab_mul_bf_bench_kernel, stream)
}

pub fn bench_add_e2(stream: &CudaStream) -> CudaResult<()> {
    bench(ab_add_e2_bench_kernel, stream)
}

pub fn bench_mul_e2(stream: &CudaStream) -> CudaResult<()> {
    bench(ab_mul_e2_bench_kernel, stream)
}

pub fn bench_add_e4(stream: &CudaStream) -> CudaResult<()> {
    bench(ab_add_e4_bench_kernel, stream)
}

pub fn bench_mul_e4(stream: &CudaStream) -> CudaResult<()> {
    bench(ab_mul_e4_bench_kernel, stream)
}

pub fn bench_add_e6(stream: &CudaStream) -> CudaResult<()> {
    bench(ab_add_e6_bench_kernel, stream)
}

pub fn bench_mul_e6(stream: &CudaStream) -> CudaResult<()> {
    bench(ab_mul_e6_bench_kernel, stream)
}
