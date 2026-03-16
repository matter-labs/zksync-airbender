#![feature(custom_test_frameworks)]
#![test_runner(criterion::runner)]

use criterion::{criterion_group, criterion_main, Bencher, Criterion, Throughput};
use era_criterion_cuda::CudaMeasurement;
use era_cudart::device::device_get_attribute;
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaDeviceAttr::MultiProcessorCount;
use gpu_prover::bench::field::*;

fn binary_bf(c: &mut Criterion<CudaMeasurement>) {
    let mpc = device_get_attribute(MultiProcessorCount, 0).unwrap() as u64;
    let stream = CudaStream::default();
    let mut group = c.benchmark_group("field");
    group.throughput(Throughput::Elements(mpc * 1024 * 1024 * 32 * 32));
    group.bench_function("add_bf", |b: &mut Bencher<CudaMeasurement>| {
        b.iter(|| {
            bench_add_bf(&stream).unwrap();
            stream.synchronize().unwrap();
        })
    });
    group.bench_function("mul_bf", |b: &mut Bencher<CudaMeasurement>| {
        b.iter(|| {
            bench_mul_bf(&stream).unwrap();
            stream.synchronize().unwrap();
        })
    });
    group.finish();
}

fn binary_e2(c: &mut Criterion<CudaMeasurement>) {
    let mpc = device_get_attribute(MultiProcessorCount, 0).unwrap() as u64;
    let stream = CudaStream::default();
    let mut group = c.benchmark_group("field");
    group.throughput(Throughput::Elements(mpc * 1024 * 1024 * 16 * 16));
    group.bench_function("add_e2", |b: &mut Bencher<CudaMeasurement>| {
        b.iter(|| {
            bench_add_e2(&stream).unwrap();
            stream.synchronize().unwrap();
        })
    });
    group.bench_function("mul_e2", |b: &mut Bencher<CudaMeasurement>| {
        b.iter(|| {
            bench_mul_e2(&stream).unwrap();
            stream.synchronize().unwrap();
        })
    });
    group.finish();
}

fn binary_e4(c: &mut Criterion<CudaMeasurement>) {
    let mpc = device_get_attribute(MultiProcessorCount, 0).unwrap() as u64;
    let stream = CudaStream::default();
    let mut group = c.benchmark_group("field");
    group.throughput(Throughput::Elements(mpc * 1024 * 1024 * 8 * 8));
    group.bench_function("add_e4", |b: &mut Bencher<CudaMeasurement>| {
        b.iter(|| {
            bench_add_e4(&stream).unwrap();
            stream.synchronize().unwrap();
        })
    });
    group.bench_function("mul_e4", |b: &mut Bencher<CudaMeasurement>| {
        b.iter(|| {
            bench_mul_e4(&stream).unwrap();
            stream.synchronize().unwrap();
        })
    });
    group.finish();
}

fn binary_e6(c: &mut Criterion<CudaMeasurement>) {
    let mpc = device_get_attribute(MultiProcessorCount, 0).unwrap() as u64;
    let stream = CudaStream::default();
    let mut group = c.benchmark_group("field");
    group.throughput(Throughput::Elements(mpc * 1024 * 1024 * 5 * 5));
    group.bench_function("add_e6", |b: &mut Bencher<CudaMeasurement>| {
        b.iter(|| {
            bench_add_e6(&stream).unwrap();
            stream.synchronize().unwrap();
        })
    });
    group.bench_function("mul_e6", |b: &mut Bencher<CudaMeasurement>| {
        b.iter(|| {
            bench_mul_e6(&stream).unwrap();
            stream.synchronize().unwrap();
        })
    });
    group.finish();
}

criterion_group!(
    name = bench;
    config = Criterion::default().with_measurement::<CudaMeasurement>(CudaMeasurement{});
    targets = binary_bf, binary_e2, binary_e4, binary_e6
);
criterion_main!(bench);
