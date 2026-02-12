#![feature(custom_test_frameworks)]
#![test_runner(criterion::runner)]

use criterion::{criterion_group, criterion_main, Criterion};
use era_cudart_sys::CudaDeviceAttr;

fn get_device(c: &mut Criterion) {
    c.bench_function("get_device", |b| {
        b.iter(|| era_cudart::device::get_device().unwrap())
    });
}

fn get_attribute_mpc(c: &mut Criterion) {
    c.bench_function("get_attribute_mpc", |b| {
        b.iter(|| {
            era_cudart::device::device_get_attribute(CudaDeviceAttr::MultiProcessorCount, 0)
                .unwrap()
        })
    });
}

criterion_group!(other, get_device, get_attribute_mpc);
criterion_main!(other);
