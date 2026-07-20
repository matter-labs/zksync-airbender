use crate::simple::{Add, BinaryOp, Mul, ParametrizedOp, Pow, SetByRef, SetByVal, Sub};
use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use gpu_core::primitives::field::{BF, E4};

use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

fn set_by_val<T: Field + SetByVal, const LOG_N: u32>() {
    let n = 1 << LOG_N;
    let value = T::ONE;
    let stream = CudaStream::default();
    let mut dst_host = vec![T::ZERO; n];
    let mut dst_device = DeviceAllocation::alloc(n).unwrap();
    memory_copy_async(&mut dst_device, &dst_host, &stream).unwrap();
    super::set_by_val(value, &mut dst_device, &stream).unwrap();
    memory_copy_async(&mut dst_host, &dst_device, &stream).unwrap();
    stream.synchronize().unwrap();
    assert!(dst_host.iter().all(|x| { x.eq(&value) }));
}

#[test]
fn set_by_val_bf() {
    set_by_val::<BF, 20>();
}

#[test]
fn set_by_val_e4() {
    set_by_val::<E4, 18>();
}

fn set_by_ref<T: Field + SetByVal + SetByRef, const LOG_N: u32>() {
    let n = 1 << LOG_N;
    let value = T::ONE;
    let stream = CudaStream::default();
    let mut value_device = DeviceAllocation::alloc(1).unwrap();
    super::set_by_val(value, &mut value_device, &stream).unwrap();
    let mut dst_host = vec![T::ZERO; n];
    let mut dst_device = DeviceAllocation::alloc(n).unwrap();
    memory_copy_async(&mut dst_device, &dst_host, &stream).unwrap();
    super::set_by_ref(&value_device, &mut dst_device, &stream).unwrap();
    memory_copy_async(&mut dst_host, &dst_device, &stream).unwrap();
    stream.synchronize().unwrap();
    assert!(dst_host.iter().all(|x| { x.eq(&value) }));
}

#[test]
fn set_by_ref_bf() {
    set_by_ref::<BF, 20>();
}

#[test]
fn set_by_ref_e4() {
    set_by_ref::<E4, 18>();
}

fn set_to_zero<T: Field, const LOG_N: u32>() {
    let n = 1 << LOG_N;
    let stream = CudaStream::default();
    let mut dst_host = vec![T::ONE; n];
    let mut dst_device = DeviceAllocation::alloc(n).unwrap();
    memory_copy_async(&mut dst_device, &dst_host, &stream).unwrap();
    super::set_to_zero(&mut dst_device, &stream).unwrap();
    memory_copy_async(&mut dst_host, &dst_device, &stream).unwrap();
    stream.synchronize().unwrap();
    assert!(dst_host.iter().all(|x| { x.eq(&T::ZERO) }));
}

#[test]
fn set_to_zero_bf() {
    set_to_zero::<BF, 20>();
}

#[test]
fn set_to_ones_bf() {
    const LOG_N: u32 = 20;
    let n = 1usize << LOG_N;
    let stream = CudaStream::default();
    let mut dst_host = vec![BF::ZERO; n];
    let mut dst_device = DeviceAllocation::alloc(n).unwrap();
    memory_copy_async(&mut dst_device, &dst_host, &stream).unwrap();
    super::set_to_ones(&mut dst_device, &stream).unwrap();
    memory_copy_async(&mut dst_host, &dst_device, &stream).unwrap();
    stream.synchronize().unwrap();
    // set_to_ones is a raw 0xFF byte-fill, not the field element ONE.
    assert!(dst_host.iter().all(|x| x.0 == 0xFFFF_FFFF));
}

fn pow<T: Field, const LOG_N: u32>(additional_values: &[T])
where
    Pow: ParametrizedOp<T>,
{
    let n = 1usize << LOG_N;
    let values = get_values(n, additional_values);
    let exps: [u32; 6] = [0, 1, 2, 3, 17, 255];
    let stream = CudaStream::default();
    let mut d_values = DeviceAllocation::alloc(n).unwrap();
    memory_copy_async(&mut d_values, &values, &stream).unwrap();
    let values_matrix = DeviceMatrix::new(&d_values, n);
    for &exp in &exps {
        let mut d_result = DeviceAllocation::alloc(n).unwrap();
        let mut result_matrix = DeviceMatrixMut::new(&mut d_result, n);
        super::pow(&values_matrix, exp, &mut result_matrix, &stream).unwrap();
        let mut h_result = vec![T::ZERO; n];
        memory_copy_async(&mut h_result, &d_result, &stream).unwrap();
        stream.synchronize().unwrap();
        for i in 0..n {
            assert_eq!(values[i].pow(exp), h_result[i], "exp={exp} i={i}");
        }
    }
}

#[test]
fn pow_bf() {
    pow::<BF, 8>(&BF_VALUES);
}

#[test]
fn pow_e4() {
    pow::<E4, 8>(&E4_VALUES);
}

fn add<T: Field, const LOG_N: u32>(additional_values: &[T])
where
    Add: BinaryOp<T, T, T>,
{
    let device_fn = super::add;
    let host_fn = |x: &T, y: &T| *x.clone().add_assign(y);
    binary_op_test::<T, LOG_N>(device_fn, host_fn, additional_values);
}

#[test]
fn add_bf() {
    add::<BF, 10>(&BF_VALUES);
}

#[test]
fn add_e4() {
    add::<E4, 8>(&E4_VALUES);
}

fn add_into_x<T: Field, const LOG_N: u32>(additional_values: &[T])
where
    Add: BinaryOp<T, T, T>,
{
    let device_fn = super::add_into_x;
    let host_fn = |x: &T, y: &T| *x.clone().add_assign(y);
    binary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
}

#[test]
fn add_into_x_bf() {
    add_into_x::<BF, 10>(&BF_VALUES);
}

fn add_into_y<T: Field, const LOG_N: u32>(additional_values: &[T])
where
    Add: BinaryOp<T, T, T>,
{
    let device_fn = |y: &mut DeviceSlice<T>, x: &DeviceSlice<T>, stream: &CudaStream| {
        super::add_into_y(x, y, stream)
    };
    let host_fn = |y: &T, x: &T| *x.clone().add_assign(y);
    binary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
}

#[test]
fn add_into_y_bf() {
    add_into_y::<BF, 10>(&BF_VALUES);
}

fn mul<T: Field, const LOG_N: u32>(additional_values: &[T])
where
    Mul: BinaryOp<T, T, T>,
{
    let device_fn = super::mul;
    let host_fn = |x: &T, y: &T| *x.clone().mul_assign(y);
    binary_op_test::<T, LOG_N>(device_fn, host_fn, additional_values);
}

#[test]
fn mul_bf() {
    mul::<BF, 10>(&BF_VALUES);
}

#[test]
fn mul_e4() {
    mul::<E4, 8>(&E4_VALUES);
}

fn mul_into_x<T: Field, const LOG_N: u32>(additional_values: &[T])
where
    Mul: BinaryOp<T, T, T>,
{
    let device_fn = super::mul_into_x;
    let host_fn = |x: &T, y: &T| *x.clone().mul_assign(y);
    binary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
}

#[test]
fn mul_into_x_bf() {
    mul_into_x::<BF, 10>(&BF_VALUES);
}

fn mul_into_y<T: Field, const LOG_N: u32>(additional_values: &[T])
where
    Mul: BinaryOp<T, T, T>,
{
    let device_fn = |y: &mut DeviceSlice<T>, x: &DeviceSlice<T>, stream: &CudaStream| {
        super::mul_into_y(x, y, stream)
    };
    let host_fn = |y: &T, x: &T| *x.clone().mul_assign(y);
    binary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
}

#[test]
fn mul_into_y_bf() {
    mul_into_y::<BF, 10>(&BF_VALUES);
}

fn sub<T: Field, const LOG_N: u32>(additional_values: &[T])
where
    Sub: BinaryOp<T, T, T>,
{
    let device_fn = super::sub;
    let host_fn = |x: &T, y: &T| *x.clone().sub_assign(y);
    binary_op_test::<T, LOG_N>(device_fn, host_fn, additional_values);
}

#[test]
fn sub_bf() {
    sub::<BF, 10>(&BF_VALUES);
}

#[test]
fn sub_e4() {
    sub::<E4, 8>(&E4_VALUES);
}

fn sub_into_x<T: Field, const LOG_N: u32>(additional_values: &[T])
where
    Sub: BinaryOp<T, T, T>,
{
    let device_fn = super::sub_into_x;
    let host_fn = |x: &T, y: &T| *x.clone().sub_assign(y);
    binary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
}

#[test]
fn sub_into_x_bf() {
    sub_into_x::<BF, 10>(&BF_VALUES);
}

fn sub_into_y<T: Field, const LOG_N: u32>(additional_values: &[T])
where
    Sub: BinaryOp<T, T, T>,
{
    let device_fn = |y: &mut DeviceSlice<T>, x: &DeviceSlice<T>, stream: &CudaStream| {
        super::sub_into_y(x, y, stream)
    };
    let host_fn = |y: &T, x: &T| *x.clone().sub_assign(y);
    binary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
}

#[test]
fn sub_into_y_bf() {
    sub_into_y::<BF, 10>(&BF_VALUES);
}

#[test]
fn add_mixed_bf_e4() {
    mixed_binary_op_test(&BF_VALUES, &E4_VALUES, super::add::<BF, E4, E4>, |x, y| {
        let mut result = *y;
        result.add_assign_base(x);
        result
    });
}

#[test]
fn add_into_y_mixed_bf_e4() {
    mixed_binary_into_y_test(
        &BF_VALUES,
        &E4_VALUES,
        super::add_into_y::<BF, E4>,
        |x, y| {
            let mut result = *y;
            result.add_assign_base(x);
            result
        },
    );
}

#[test]
fn add_mixed_e4_bf() {
    mixed_binary_op_test(&E4_VALUES, &BF_VALUES, super::add::<E4, BF, E4>, |x, y| {
        let mut result = *x;
        result.add_assign_base(y);
        result
    });
}

#[test]
fn add_into_x_mixed_e4_bf() {
    mixed_binary_into_x_test(
        &E4_VALUES,
        &BF_VALUES,
        super::add_into_x::<E4, BF>,
        |x, y| {
            let mut result = *x;
            result.add_assign_base(y);
            result
        },
    );
}

#[test]
fn mul_mixed_bf_e4() {
    mixed_binary_op_test(&BF_VALUES, &E4_VALUES, super::mul::<BF, E4, E4>, |x, y| {
        let mut result = *y;
        result.mul_assign_by_base(x);
        result
    });
}

#[test]
fn mul_into_y_mixed_bf_e4() {
    mixed_binary_into_y_test(
        &BF_VALUES,
        &E4_VALUES,
        super::mul_into_y::<BF, E4>,
        |x, y| {
            let mut result = *y;
            result.mul_assign_by_base(x);
            result
        },
    );
}

#[test]
fn mul_mixed_e4_bf() {
    mixed_binary_op_test(&E4_VALUES, &BF_VALUES, super::mul::<E4, BF, E4>, |x, y| {
        let mut result = *x;
        result.mul_assign_by_base(y);
        result
    });
}

#[test]
fn mul_into_x_mixed_e4_bf() {
    mixed_binary_into_x_test(
        &E4_VALUES,
        &BF_VALUES,
        super::mul_into_x::<E4, BF>,
        |x, y| {
            let mut result = *x;
            result.mul_assign_by_base(y);
            result
        },
    );
}

#[test]
fn sub_mixed_bf_e4() {
    mixed_binary_op_test(&BF_VALUES, &E4_VALUES, super::sub::<BF, E4, E4>, |x, y| {
        let mut result = *y;
        result.negate();
        result.add_assign_base(x);
        result
    });
}

#[test]
fn sub_into_y_mixed_bf_e4() {
    mixed_binary_into_y_test(
        &BF_VALUES,
        &E4_VALUES,
        super::sub_into_y::<BF, E4>,
        |x, y| {
            let mut result = *y;
            result.negate();
            result.add_assign_base(x);
            result
        },
    );
}

#[test]
fn sub_mixed_e4_bf() {
    mixed_binary_op_test(&E4_VALUES, &BF_VALUES, super::sub::<E4, BF, E4>, |x, y| {
        let mut result = *x;
        result.sub_assign_base(y);
        result
    });
}

#[test]
fn sub_into_x_mixed_e4_bf() {
    mixed_binary_into_x_test(
        &E4_VALUES,
        &BF_VALUES,
        super::sub_into_x::<E4, BF>,
        |x, y| {
            let mut result = *x;
            result.sub_assign_base(y);
            result
        },
    );
}

mod helpers;
use crate::upstream::{Field, FieldExtension};
#[allow(unused_imports)]
use helpers::*;
