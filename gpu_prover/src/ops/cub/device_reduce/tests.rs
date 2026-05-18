use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::stream::CudaStream;

use itertools::Itertools;
use rand::rng;
use serial_test::serial;

use crate::ops::cub::device_reduce::{Reduce, ReduceOperation};
use crate::primitives::device_structures::DeviceMatrix;
use crate::upstream::Field;

type HostFunction<F> = fn(F, F) -> F;

fn generate<F: Field>(count: usize) -> Vec<F> {
    let mut rng = rng();
    (0..count)
        .map(|_| F::random_element(&mut rng))
        .collect_vec()
}

fn reduce<F: Field + Reduce>(operation: ReduceOperation, init: F, host_function: HostFunction<F>) {
    const NUM_ITEMS: usize = 1 << 16;
    let temp_storage_bytes =
        super::get_reduce_temp_storage_bytes::<F>(operation, NUM_ITEMS as i32).unwrap();
    let mut d_temp_storage = DeviceAllocation::alloc(temp_storage_bytes).unwrap();
    let h_in = generate(NUM_ITEMS);
    let mut h_out = [F::default()];
    let mut d_in = DeviceAllocation::alloc(NUM_ITEMS).unwrap();
    let mut d_out = DeviceAllocation::alloc(1).unwrap();
    let stream = CudaStream::default();
    memory_copy_async(&mut d_in, &h_in, &stream).unwrap();
    super::reduce(
        operation,
        &mut d_temp_storage,
        &d_in,
        &mut d_out[0],
        &stream,
    )
    .unwrap();
    memory_copy_async(&mut h_out, &d_out, &stream).unwrap();
    stream.synchronize().unwrap();
    let result = h_in.into_iter().fold(init, host_function);
    assert_eq!(result, h_out[0]);
}

fn batch_reduce<F: Field + Reduce>(
    operation: ReduceOperation,
    init: F,
    host_function: HostFunction<F>,
) {
    const BATCH_SIZE: usize = 1 << 8;
    const NUM_ITEMS: usize = 1 << 8;
    let temp_storage_bytes = super::get_batch_reduce_temp_storage_bytes::<F>(
        operation,
        BATCH_SIZE as i32,
        NUM_ITEMS as i32,
    )
    .unwrap();
    let mut d_temp_storage = DeviceAllocation::alloc(temp_storage_bytes).unwrap();
    let h_in = generate(NUM_ITEMS * BATCH_SIZE);
    let mut h_out = [F::default(); BATCH_SIZE];
    let mut d_in = DeviceAllocation::alloc(NUM_ITEMS * BATCH_SIZE).unwrap();
    let mut d_out = DeviceAllocation::alloc(BATCH_SIZE).unwrap();
    let stream = CudaStream::default();
    memory_copy_async(&mut d_in, &h_in, &stream).unwrap();
    let d_in_matrix = DeviceMatrix::new(&d_in, NUM_ITEMS);
    super::batch_reduce(
        operation,
        &mut d_temp_storage,
        &d_in_matrix,
        &mut d_out,
        &stream,
    )
    .unwrap();
    memory_copy_async(&mut h_out, &d_out, &stream).unwrap();
    stream.synchronize().unwrap();
    let result = h_in
        .into_iter()
        .chunks(NUM_ITEMS)
        .into_iter()
        .map(|c| c.fold(init, host_function))
        .collect_vec();
    assert!(result
        .into_iter()
        .zip(h_out.into_iter())
        .all(|(a, b)| a == b));
}

type TestFunction<F> = fn(ReduceOperation, F, HostFunction<F>);

fn test_sum<F: Field>(test_function: TestFunction<F>) {
    test_function(ReduceOperation::Sum, F::ZERO, |state, x| {
        let mut result = state;
        result.add_assign(&x);
        result
    })
}

fn test_product<F: Field>(test_function: TestFunction<F>) {
    test_function(ReduceOperation::Product, F::ONE, |state, x| {
        let mut result = state;
        result.mul_assign(&x);
        result
    })
}

#[test]
#[serial]
fn sum_bf() {
    test_sum(reduce::<super::BF>)
}

#[test]
#[serial]
fn batch_sum_bf() {
    test_sum(batch_reduce::<super::BF>)
}

#[test]
#[serial]
fn product_bf() {
    test_product(reduce::<super::BF>)
}

#[test]
#[serial]
fn batch_product_bf() {
    test_product(batch_reduce::<super::BF>)
}

#[test]
#[serial]
fn sum_e4() {
    test_sum(reduce::<super::E4>)
}

#[test]
#[serial]
fn batch_sum_e4() {
    test_sum(batch_reduce::<super::E4>)
}

#[test]
#[serial]
fn product_e4() {
    test_product(reduce::<super::E4>)
}

#[test]
#[serial]
fn batch_product_e4() {
    test_product(batch_reduce::<super::E4>)
}
