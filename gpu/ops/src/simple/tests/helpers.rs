use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::field::{BF, E2, E4, E6};

use crate::upstream::Field;
use itertools::Itertools;

#[cfg(feature = "scaffolding_ops")]
type UnaryDeviceFn<T> = fn(&DeviceSlice<T>, &mut DeviceSlice<T>, &CudaStream) -> CudaResult<()>;

#[cfg(feature = "scaffolding_ops")]
type UnaryDeviceInPlaceFn<T> = fn(&mut DeviceSlice<T>, &CudaStream) -> CudaResult<()>;

#[cfg(feature = "scaffolding_ops")]
type UnaryHostFn<T> = fn(&T) -> T;

#[cfg(feature = "scaffolding_ops")]
#[allow(dead_code)]
type ParametrizedUnaryDeviceFn<T> =
    fn(&DeviceSlice<T>, u32, &mut DeviceSlice<T>, &CudaStream) -> CudaResult<()>;

#[cfg(feature = "scaffolding_ops")]
#[allow(dead_code)]
type ParametrizedUnaryDeviceInPlaceFn<T> =
    fn(&mut DeviceSlice<T>, u32, &CudaStream) -> CudaResult<()>;

#[cfg(feature = "scaffolding_ops")]
#[allow(dead_code)]
type ParametrizedUnaryHostFn<T> = fn(&T, u32) -> T;

type BinaryDeviceFn<T> =
    fn(&DeviceSlice<T>, &DeviceSlice<T>, &mut DeviceSlice<T>, &CudaStream) -> CudaResult<()>;

type BinaryDeviceInPlaceFn<T> =
    fn(&mut DeviceSlice<T>, &DeviceSlice<T>, &CudaStream) -> CudaResult<()>;

type BinaryHostFn<T> = fn(&T, &T) -> T;

type MixedBinaryDeviceFn<T0, T1, TR> =
    fn(&DeviceSlice<T0>, &DeviceSlice<T1>, &mut DeviceSlice<TR>, &CudaStream) -> CudaResult<()>;

type MixedBinaryIntoXDeviceFn<T0, T1> =
    fn(&mut DeviceSlice<T0>, &DeviceSlice<T1>, &CudaStream) -> CudaResult<()>;

type MixedBinaryIntoYDeviceFn<T0, T1> =
    fn(&DeviceSlice<T0>, &mut DeviceSlice<T1>, &CudaStream) -> CudaResult<()>;

type MixedBinaryHostFn<T0, T1, TR> = fn(&T0, &T1) -> TR;

#[cfg(feature = "scaffolding_ops")]
pub(super) fn unary_op_test<T: Field, const LOG_N: u32>(
    device_fn: UnaryDeviceFn<T>,
    host_fn: UnaryHostFn<T>,
    additional_values: &[T],
) {
    let n = 1 << LOG_N;
    let x_host = get_values(n, additional_values);
    let stream = CudaStream::default();
    let mut result_host = vec![T::ZERO; n];
    let mut x_device = DeviceAllocation::alloc(n).unwrap();
    let mut result_device = DeviceAllocation::alloc(n).unwrap();
    memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
    device_fn(&x_device, &mut result_device, &stream).unwrap();
    memory_copy_async(&mut result_host, &result_device, &stream).unwrap();
    stream.synchronize().unwrap();
    for i in 0..n {
        let left = host_fn(&x_host[i]);
        let right = result_host[i];
        assert_eq!(left, right, "i = {}", i);
    }
}

#[cfg(feature = "scaffolding_ops")]
pub(super) fn unary_op_in_place_test<T: Field, const LOG_N: u32>(
    device_fn: UnaryDeviceInPlaceFn<T>,
    host_fn: UnaryHostFn<T>,
    additional_values: &[T],
) {
    let n = 1 << LOG_N;
    let x_host = get_values(n, additional_values);
    let stream = CudaStream::default();
    let mut result_host = vec![T::ZERO; n];
    let mut x_device = DeviceAllocation::alloc(n).unwrap();
    memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
    device_fn(&mut x_device, &stream).unwrap();
    memory_copy_async(&mut result_host, &x_device, &stream).unwrap();
    stream.synchronize().unwrap();
    for i in 0..n {
        let left = host_fn(&x_host[i]);
        let right = result_host[i];
        assert_eq!(left, right, "i = {}", i);
    }
}

#[cfg(feature = "scaffolding_ops")]
#[allow(dead_code)]
pub(super) fn parametrized_unary_op_test<T: Field, const LOG_N: u32>(
    parameter: u32,
    device_fn: ParametrizedUnaryDeviceFn<T>,
    host_fn: ParametrizedUnaryHostFn<T>,
    additional_values: &[T],
) {
    let n = 1 << LOG_N;
    let x_host = get_values(n, additional_values);
    let stream = CudaStream::default();
    let mut result_host = vec![T::ZERO; n];
    let mut x_device = DeviceAllocation::alloc(n).unwrap();
    let mut result_device = DeviceAllocation::alloc(n).unwrap();
    memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
    device_fn(&x_device, parameter, &mut result_device, &stream).unwrap();
    memory_copy_async(&mut result_host, &result_device, &stream).unwrap();
    stream.synchronize().unwrap();
    for i in 0..n {
        let left = host_fn(&x_host[i], parameter);
        let right = result_host[i];
        assert_eq!(left, right, "i = {}", i);
    }
}

#[cfg(feature = "scaffolding_ops")]
#[allow(dead_code)]
pub(super) fn parametrized_unary_op_in_place_test<T: Field, const LOG_N: u32>(
    parameter: u32,
    device_fn: ParametrizedUnaryDeviceInPlaceFn<T>,
    host_fn: ParametrizedUnaryHostFn<T>,
    additional_values: &[T],
) {
    let n = 1 << LOG_N;
    let x_host = get_values(n, additional_values);
    let stream = CudaStream::default();
    let mut result_host = vec![T::ZERO; n];
    let mut x_device = DeviceAllocation::alloc(n).unwrap();
    memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
    device_fn(&mut x_device, parameter, &stream).unwrap();
    memory_copy_async(&mut result_host, &x_device, &stream).unwrap();
    stream.synchronize().unwrap();
    for i in 0..n {
        let left = host_fn(&x_host[i], parameter);
        let right = result_host[i];
        assert_eq!(left, right, "i = {}", i);
    }
}

pub(super) fn binary_op_test<T: Field, const LOG_N: u32>(
    device_fn: BinaryDeviceFn<T>,
    host_fn: BinaryHostFn<T>,
    additional_values: &[T],
) {
    let n = 1 << LOG_N;
    let values = get_values(n, additional_values);
    let mut x_host = Vec::new();
    let mut y_host = Vec::new();
    values
        .iter()
        .cartesian_product(values.iter())
        .for_each(|(&x, &y)| {
            x_host.push(x);
            y_host.push(y);
        });
    let stream = CudaStream::default();
    let length = x_host.len();
    let mut result_host = vec![T::ZERO; length];
    let mut x_device = DeviceAllocation::alloc(length).unwrap();
    let mut y_device = DeviceAllocation::alloc(length).unwrap();
    let mut result_device = DeviceAllocation::alloc(length).unwrap();
    memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
    memory_copy_async(&mut y_device, &y_host, &stream).unwrap();
    device_fn(&x_device, &y_device, &mut result_device, &stream).unwrap();
    memory_copy_async(&mut result_host, &result_device, &stream).unwrap();
    stream.synchronize().unwrap();
    for i in 0..length {
        let left = host_fn(&x_host[i], &y_host[i]);
        let right = result_host[i];
        assert_eq!(left, right, "i = {}", i);
    }
}

pub(super) fn binary_op_in_place_test<T: Field, const LOG_N: u32>(
    device_fn: BinaryDeviceInPlaceFn<T>,
    host_fn: BinaryHostFn<T>,
    additional_values: &[T],
) {
    let n = 1 << LOG_N;
    let values = get_values(n, additional_values);
    let mut x_host = Vec::new();
    let mut y_host = Vec::new();
    values
        .iter()
        .cartesian_product(values.iter())
        .for_each(|(&x, &y)| {
            x_host.push(x);
            y_host.push(y);
        });
    let stream = CudaStream::default();
    let length = x_host.len();
    let mut result_host = vec![T::ZERO; length];
    let mut x_device = DeviceAllocation::alloc(length).unwrap();
    let mut y_device = DeviceAllocation::alloc(length).unwrap();
    memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
    memory_copy_async(&mut y_device, &y_host, &stream).unwrap();
    device_fn(&mut x_device, &y_device, &stream).unwrap();
    memory_copy_async(&mut result_host, &x_device, &stream).unwrap();
    stream.synchronize().unwrap();
    for i in 0..length {
        let left = host_fn(&x_host[i], &y_host[i]);
        let right = result_host[i];
        assert_eq!(left, right, "i = {}", i);
    }
}

pub(super) fn mixed_binary_op_test<T0: Field, T1: Field, TR: Field>(
    x_values: &[T0],
    y_values: &[T1],
    device_fn: MixedBinaryDeviceFn<T0, T1, TR>,
    host_fn: MixedBinaryHostFn<T0, T1, TR>,
) {
    let mut x_host = Vec::new();
    let mut y_host = Vec::new();
    x_values
        .iter()
        .cartesian_product(y_values.iter())
        .for_each(|(&x, &y)| {
            x_host.push(x);
            y_host.push(y);
        });
    let stream = CudaStream::default();
    let length = x_host.len();
    let mut result_host = vec![TR::ZERO; length];
    let mut x_device = DeviceAllocation::alloc(length).unwrap();
    let mut y_device = DeviceAllocation::alloc(length).unwrap();
    let mut result_device = DeviceAllocation::alloc(length).unwrap();
    memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
    memory_copy_async(&mut y_device, &y_host, &stream).unwrap();
    device_fn(&x_device, &y_device, &mut result_device, &stream).unwrap();
    memory_copy_async(&mut result_host, &result_device, &stream).unwrap();
    stream.synchronize().unwrap();
    for i in 0..length {
        let left = host_fn(&x_host[i], &y_host[i]);
        let right = result_host[i];
        assert_eq!(left, right, "i = {}", i);
    }
}

pub(super) fn mixed_binary_into_x_test<T0: Field, T1: Field>(
    x_values: &[T0],
    y_values: &[T1],
    device_fn: MixedBinaryIntoXDeviceFn<T0, T1>,
    host_fn: MixedBinaryHostFn<T0, T1, T0>,
) {
    let mut x_host = Vec::new();
    let mut y_host = Vec::new();
    x_values
        .iter()
        .cartesian_product(y_values.iter())
        .for_each(|(&x, &y)| {
            x_host.push(x);
            y_host.push(y);
        });
    let stream = CudaStream::default();
    let length = x_host.len();
    let mut result_host = vec![T0::ZERO; length];
    let mut x_device = DeviceAllocation::alloc(length).unwrap();
    let mut y_device = DeviceAllocation::alloc(length).unwrap();
    memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
    memory_copy_async(&mut y_device, &y_host, &stream).unwrap();
    device_fn(&mut x_device, &y_device, &stream).unwrap();
    memory_copy_async(&mut result_host, &x_device, &stream).unwrap();
    stream.synchronize().unwrap();
    for i in 0..length {
        let left = host_fn(&x_host[i], &y_host[i]);
        let right = result_host[i];
        assert_eq!(left, right, "i = {}", i);
    }
}

pub(super) fn mixed_binary_into_y_test<T0: Field, T1: Field>(
    x_values: &[T0],
    y_values: &[T1],
    device_fn: MixedBinaryIntoYDeviceFn<T0, T1>,
    host_fn: MixedBinaryHostFn<T0, T1, T1>,
) {
    let mut x_host = Vec::new();
    let mut y_host = Vec::new();
    x_values
        .iter()
        .cartesian_product(y_values.iter())
        .for_each(|(&x, &y)| {
            x_host.push(x);
            y_host.push(y);
        });
    let stream = CudaStream::default();
    let length = x_host.len();
    let mut result_host = vec![T1::ZERO; length];
    let mut x_device = DeviceAllocation::alloc(length).unwrap();
    let mut y_device = DeviceAllocation::alloc(length).unwrap();
    memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
    memory_copy_async(&mut y_device, &y_host, &stream).unwrap();
    device_fn(&x_device, &mut y_device, &stream).unwrap();
    memory_copy_async(&mut result_host, &y_device, &stream).unwrap();
    stream.synchronize().unwrap();
    for i in 0..length {
        let left = host_fn(&x_host[i], &y_host[i]);
        let right = result_host[i];
        assert_eq!(left, right, "i = {}", i);
    }
}

// fn ternary_op_test(device_fn: TernaryDeviceFn, host_fn: TernaryHostFn) {
//     const VALUES_COUNT: usize = 1 << 6;
//     let values = get_values(VALUES_COUNT);
//     let mut x_host = vec![];
//     let mut y_host = vec![];
//     let mut z_host = vec![];
//     values
//         .iter()
//         .cartesian_product(values.iter())
//         .cartesian_product(values.iter())
//         .for_each(|((&x, &y), &z)| {
//             x_host.push(x);
//             y_host.push(y);
//             z_host.push(z);
//         });
//     let stream = CudaStream::default();
//     let length = x_host.len();
//     let mut result_host = vec![BF::ZERO; length];
//     let mut x_device = DeviceAllocation::alloc(length).unwrap();
//     let mut y_device = DeviceAllocation::alloc(length).unwrap();
//     let mut z_device = DeviceAllocation::alloc(length).unwrap();
//     let mut result_device = DeviceAllocation::alloc(length).unwrap();
//     memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
//     memory_copy_async(&mut y_device, &y_host, &stream).unwrap();
//     memory_copy_async(&mut z_device, &z_host, &stream).unwrap();
//     device_fn(&x_device, &y_device, &z_device, &mut result_device, &stream).unwrap();
//     memory_copy_async(&mut result_host, &result_device, &stream).unwrap();
//     stream.synchronize().unwrap();
//     for i in 0..length {
//         let left = host_fn(&x_host[i], &y_host[i], &z_host[i]);
//         let right = result_host[i];
//         assert_eq!(left, right, "i = {}", i);
//     }
// }
//
// fn ternary_op_in_place_test(device_fn: TernaryDeviceInPlaceFn, host_fn: TernaryHostFn) {
//     const VALUES_COUNT: usize = 1 << 6;
//     let values = get_values(VALUES_COUNT);
//     let mut x_host = vec![];
//     let mut y_host = vec![];
//     let mut z_host = vec![];
//     values
//         .iter()
//         .cartesian_product(values.iter())
//         .cartesian_product(values.iter())
//         .for_each(|((&x, &y), &z)| {
//             x_host.push(x);
//             y_host.push(y);
//             z_host.push(z);
//         });
//     let stream = CudaStream::default();
//     let length = x_host.len();
//     let mut result_host = vec![BF::ZERO; length];
//     let mut x_device = DeviceAllocation::alloc(length).unwrap();
//     let mut y_device = DeviceAllocation::alloc(length).unwrap();
//     let mut z_device = DeviceAllocation::alloc(length).unwrap();
//     memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
//     memory_copy_async(&mut y_device, &y_host, &stream).unwrap();
//     memory_copy_async(&mut z_device, &z_host, &stream).unwrap();
//     device_fn(&mut x_device, &y_device, &z_device, &stream).unwrap();
//     memory_copy_async(&mut result_host, &x_device, &stream).unwrap();
//     stream.synchronize().unwrap();
//     for i in 0..length {
//         let left = host_fn(&x_host[i], &y_host[i], &z_host[i]);
//         let right = result_host[i];
//         assert_eq!(left, right, "i = {}", i);
//     }
// }

pub(super) const BF_VALUES: [BF; 6] = [
    BF::new(0),
    BF::new(1),
    BF::new(2),
    BF::new(BF::ORDER - 3),
    BF::new(BF::ORDER - 2),
    BF::new(BF::ORDER - 1),
];

pub(super) const E2_VALUES: [E2; 6] = [
    E2::new(BF_VALUES[0], BF_VALUES[0]),
    E2::new(BF_VALUES[1], BF_VALUES[1]),
    E2::new(BF_VALUES[2], BF_VALUES[2]),
    E2::new(BF_VALUES[3], BF_VALUES[3]),
    E2::new(BF_VALUES[4], BF_VALUES[4]),
    E2::new(BF_VALUES[5], BF_VALUES[5]),
];

pub(super) const E4_VALUES: [E4; 6] = [
    E4::new(E2_VALUES[0], E2_VALUES[0]),
    E4::new(E2_VALUES[1], E2_VALUES[1]),
    E4::new(E2_VALUES[2], E2_VALUES[2]),
    E4::new(E2_VALUES[3], E2_VALUES[3]),
    E4::new(E2_VALUES[4], E2_VALUES[4]),
    E4::new(E2_VALUES[5], E2_VALUES[5]),
];

pub(super) const E6_VALUES: [E6; 6] = [
    E6::new(E2_VALUES[0], E2_VALUES[0], E2_VALUES[0]),
    E6::new(E2_VALUES[1], E2_VALUES[1], E2_VALUES[1]),
    E6::new(E2_VALUES[2], E2_VALUES[2], E2_VALUES[2]),
    E6::new(E2_VALUES[3], E2_VALUES[3], E2_VALUES[3]),
    E6::new(E2_VALUES[4], E2_VALUES[4], E2_VALUES[4]),
    E6::new(E2_VALUES[5], E2_VALUES[5], E2_VALUES[5]),
];

pub(super) fn get_values<T: Field>(count: usize, additional_values: &[T]) -> Vec<T> {
    assert!(count >= additional_values.len());
    let mut rng = rand::rng();
    let mut values: Vec<T> = (0..count - additional_values.len())
        .map(|_| T::random_element(&mut rng))
        .collect();
    values.extend_from_slice(additional_values);
    values
}
