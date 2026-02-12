#![feature(custom_test_frameworks)]
#![test_runner(criterion::runner)]

use criterion::{criterion_group, criterion_main, Bencher, Criterion, Throughput};
use era_criterion_cuda::CudaMeasurement;
use era_cudart::device::device_get_attribute;
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaDeviceAttr::MultiProcessorCount;

use gpu_prover::field_bench::*;

fn field(c: &mut Criterion<CudaMeasurement>) {
    let mpc = device_get_attribute(MultiProcessorCount, 0).unwrap() as u64;
    let stream = CudaStream::default();
    let mut group = c.benchmark_group("field");
    group.throughput(Throughput::Elements(mpc * 1024 * 1024 * 64 * 16));
    group.bench_function("add", |b: &mut Bencher<CudaMeasurement>| {
        b.iter(|| {
            add_bench(&stream).unwrap();
            stream.synchronize().unwrap();
        })
    });
    group.bench_function("mul", |b: &mut Bencher<CudaMeasurement>| {
        b.iter(|| {
            mul_bench(&stream).unwrap();
            stream.synchronize().unwrap();
        })
    });
    group.finish();
}

criterion_group!(
    name = bench;
    config = Criterion::default().with_measurement::<CudaMeasurement>(CudaMeasurement{});
    targets = field
);
criterion_main!(bench);
