use crate::simple::{Add, BinaryOp, Mul, SetByRef, SetByVal, Sub};
#[cfg(feature = "scaffolding_ops")]
use crate::simple::{Dbl, Inv, Neg, Sqr, UnaryOp};
use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use gpu_core::primitives::field::{BF, E2, E4, E6};

use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use serial_test::serial;

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
#[serial]
fn set_by_val_bf() {
    set_by_val::<BF, 20>();
}

#[test]
#[serial]
fn set_by_val_e2() {
    set_by_val::<E2, 19>();
}

#[test]
#[serial]
fn set_by_val_e4() {
    set_by_val::<E4, 18>();
}

#[test]
#[serial]
fn set_by_val_e6() {
    set_by_val::<E6, 18>();
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
#[serial]
fn set_by_ref_bf() {
    set_by_ref::<BF, 20>();
}

#[test]
#[serial]
fn set_by_ref_e2() {
    set_by_ref::<E2, 19>();
}

#[test]
#[serial]
fn set_by_ref_e4() {
    set_by_ref::<E4, 18>();
}

#[test]
#[serial]
fn set_by_ref_e6() {
    set_by_ref::<E6, 18>();
}

fn set_to_zero<T: Field, const LOG_N: u32>() {
    let n = 1 << 18;
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
#[serial]
fn set_to_zero_bf() {
    set_to_zero::<BF, 20>();
}

#[test]
#[serial]
fn set_to_zero_e2() {
    set_to_zero::<E2, 19>();
}

#[test]
#[serial]
fn set_to_zero_e4() {
    set_to_zero::<E4, 18>();
}

#[cfg(feature = "scaffolding_ops")]
mod scaffolding_unary {
    use super::*;

    fn dbl<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Dbl: UnaryOp<T>,
    {
        let device_fn = crate::simple::dbl;
        let host_fn = |x: &T| *x.clone().double();
        super::unary_op_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    #[serial]
    fn dbl_bf() {
        dbl::<BF, 20>(&BF_VALUES);
    }

    #[test]
    #[serial]
    fn dbl_e2() {
        dbl::<E2, 19>(&E2_VALUES);
    }

    #[test]
    #[serial]
    fn dbl_e4() {
        dbl::<E4, 18>(&E4_VALUES);
    }

    #[test]
    #[serial]
    fn dbl_e6() {
        dbl::<E6, 18>(&E6_VALUES);
    }

    fn dbl_in_place<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Dbl: UnaryOp<T>,
    {
        let device_fn = crate::simple::dbl_in_place;
        let host_fn = |x: &T| *x.clone().double();
        super::unary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    #[serial]
    fn dbl_in_place_bf() {
        dbl_in_place::<BF, 20>(&BF_VALUES);
    }

    #[test]
    #[serial]
    fn dbl_in_place_e2() {
        dbl_in_place::<E2, 19>(&E2_VALUES);
    }

    #[test]
    #[serial]
    fn dbl_in_place_e4() {
        dbl_in_place::<E4, 18>(&E4_VALUES);
    }

    #[test]
    #[serial]
    fn dbl_in_place_e6() {
        dbl_in_place::<E6, 18>(&E6_VALUES);
    }

    fn inv<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Inv: UnaryOp<T>,
    {
        let device_fn = crate::simple::inv;
        let host_fn = |x: &T| x.inverse().unwrap_or(T::ZERO);
        super::unary_op_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    #[serial]
    fn inv_bf() {
        inv::<BF, 20>(&BF_VALUES);
    }

    #[test]
    #[serial]
    fn inv_e2() {
        inv::<E2, 19>(&E2_VALUES);
    }

    #[test]
    #[serial]
    fn inv_e4() {
        inv::<E4, 18>(&E4_VALUES);
    }

    #[test]
    #[serial]
    fn inv_e6() {
        inv::<E6, 18>(&E6_VALUES);
    }

    fn inv_in_place<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Inv: UnaryOp<T>,
    {
        let device_fn = crate::simple::inv_in_place;
        let host_fn = |x: &T| x.inverse().unwrap_or(T::ZERO);
        super::unary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    #[serial]
    fn inv_in_place_bf() {
        inv_in_place::<BF, 20>(&BF_VALUES);
    }

    #[test]
    #[serial]
    fn inv_in_place_e2() {
        inv_in_place::<E2, 19>(&E2_VALUES);
    }

    #[test]
    #[serial]
    fn inv_in_place_e4() {
        inv_in_place::<E4, 18>(&E4_VALUES);
    }

    #[test]
    #[serial]
    fn inv_in_place_e6() {
        inv_in_place::<E6, 18>(&E6_VALUES);
    }

    fn neg<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Neg: UnaryOp<T>,
    {
        let device_fn = crate::simple::neg;
        let host_fn = |x: &T| *x.clone().negate();
        super::unary_op_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    #[serial]
    fn neg_bf() {
        neg::<BF, 20>(&BF_VALUES);
    }

    #[test]
    #[serial]
    fn neg_e2() {
        neg::<E2, 19>(&E2_VALUES);
    }

    #[test]
    #[serial]
    fn neg_e4() {
        neg::<E4, 18>(&E4_VALUES);
    }

    #[test]
    #[serial]
    fn neg_e6() {
        neg::<E6, 18>(&E6_VALUES);
    }

    fn neg_in_place<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Neg: UnaryOp<T>,
    {
        let device_fn = crate::simple::neg_in_place;
        let host_fn = |x: &T| *x.clone().negate();
        super::unary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    #[serial]
    fn neg_in_place_bf() {
        neg_in_place::<BF, 20>(&BF_VALUES);
    }

    #[test]
    #[serial]
    fn neg_in_place_e2() {
        neg_in_place::<E2, 19>(&E2_VALUES);
    }

    #[test]
    #[serial]
    fn neg_in_place_e4() {
        neg_in_place::<E4, 18>(&E4_VALUES);
    }

    #[test]
    #[serial]
    fn neg_in_place_e6() {
        neg_in_place::<E6, 18>(&E6_VALUES);
    }

    fn sqr<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Sqr: UnaryOp<T>,
    {
        let device_fn = crate::simple::sqr;
        let host_fn = |x: &T| *x.clone().square();
        super::unary_op_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    #[serial]
    fn sqr_bf() {
        sqr::<BF, 20>(&BF_VALUES);
    }

    #[test]
    #[serial]
    fn sqr_e2() {
        sqr::<E2, 19>(&E2_VALUES);
    }

    #[test]
    #[serial]
    fn sqr_e4() {
        sqr::<E4, 18>(&E4_VALUES);
    }

    #[test]
    #[serial]
    fn sqr_e6() {
        sqr::<E6, 18>(&E6_VALUES);
    }

    fn sqr_in_place<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Sqr: UnaryOp<T>,
    {
        let device_fn = crate::simple::sqr_in_place;
        let host_fn = |x: &T| *x.clone().square();
        super::unary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    #[serial]
    fn sqr_in_place_bf() {
        sqr_in_place::<BF, 20>(&BF_VALUES);
    }

    #[test]
    #[serial]
    fn sqr_in_place_e2() {
        sqr_in_place::<E2, 19>(&E2_VALUES);
    }

    #[test]
    #[serial]
    fn sqr_in_place_e4() {
        sqr_in_place::<E4, 18>(&E4_VALUES);
    }

    #[test]
    #[serial]
    fn sqr_in_place_e6() {
        sqr_in_place::<E6, 18>(&E6_VALUES);
    }
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
#[serial]
fn add_bf() {
    add::<BF, 10>(&BF_VALUES);
}

#[test]
#[serial]
fn add_e2() {
    add::<E2, 9>(&E2_VALUES);
}

#[test]
#[serial]
fn add_e4() {
    add::<E4, 8>(&E4_VALUES);
}

#[test]
#[serial]
fn add_e6() {
    add::<E6, 8>(&E6_VALUES);
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
#[serial]
fn add_into_x_bf() {
    add_into_x::<BF, 10>(&BF_VALUES);
}

#[test]
#[serial]
fn add_into_x_e2() {
    add_into_x::<E2, 9>(&E2_VALUES);
}

#[test]
#[serial]
fn add_into_x_e4() {
    add_into_x::<E4, 8>(&E4_VALUES);
}

#[test]
#[serial]
fn add_into_x_e6() {
    add_into_x::<E6, 8>(&E6_VALUES);
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
#[serial]
fn add_into_y_bf() {
    add_into_y::<BF, 10>(&BF_VALUES);
}

#[test]
#[serial]
fn add_into_y_e2() {
    add_into_y::<E2, 9>(&E2_VALUES);
}

#[test]
#[serial]
fn add_into_y_e4() {
    add_into_y::<E4, 8>(&E4_VALUES);
}

#[test]
#[serial]
fn add_into_y_e6() {
    add_into_y::<E6, 8>(&E6_VALUES);
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
#[serial]
fn mul_bf() {
    mul::<BF, 10>(&BF_VALUES);
}

#[test]
#[serial]
fn mul_e2() {
    mul::<E2, 9>(&E2_VALUES);
}

#[test]
#[serial]
fn mul_e4() {
    mul::<E4, 8>(&E4_VALUES);
}

#[test]
#[serial]
fn mul_e6() {
    mul::<E6, 8>(&E6_VALUES);
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
#[serial]
fn mul_into_x_bf() {
    mul_into_x::<BF, 10>(&BF_VALUES);
}

#[test]
#[serial]
fn mul_into_x_e2() {
    mul_into_x::<E2, 9>(&E2_VALUES);
}

#[test]
#[serial]
fn mul_into_x_e4() {
    mul_into_x::<E4, 8>(&E4_VALUES);
}

#[test]
#[serial]
fn mul_into_x_e6() {
    mul_into_x::<E6, 8>(&E6_VALUES);
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
#[serial]
fn mul_into_y_bf() {
    mul_into_y::<BF, 10>(&BF_VALUES);
}

#[test]
#[serial]
fn mul_into_y_e2() {
    mul_into_y::<E2, 9>(&E2_VALUES);
}

#[test]
#[serial]
fn mul_into_y_e4() {
    mul_into_y::<E4, 8>(&E4_VALUES);
}

#[test]
#[serial]
fn mul_into_y_e6() {
    mul_into_y::<E6, 8>(&E6_VALUES);
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
#[serial]
fn sub_bf() {
    sub::<BF, 10>(&BF_VALUES);
}

#[test]
#[serial]
fn sub_e2() {
    sub::<E2, 9>(&E2_VALUES);
}

#[test]
#[serial]
fn sub_e4() {
    sub::<E4, 8>(&E4_VALUES);
}

#[test]
#[serial]
fn sub_e6() {
    sub::<E6, 8>(&E6_VALUES);
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
#[serial]
fn sub_into_x_bf() {
    sub_into_x::<BF, 10>(&BF_VALUES);
}

#[test]
#[serial]
fn sub_into_x_e2() {
    sub_into_x::<E2, 9>(&E2_VALUES);
}

#[test]
#[serial]
fn sub_into_x_e4() {
    sub_into_x::<E4, 8>(&E4_VALUES);
}

#[test]
#[serial]
fn sub_into_x_e6() {
    sub_into_x::<E6, 8>(&E6_VALUES);
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
#[serial]
fn sub_into_y_bf() {
    sub_into_y::<BF, 10>(&BF_VALUES);
}

#[test]
#[serial]
fn sub_into_y_e2() {
    sub_into_y::<E2, 9>(&E2_VALUES);
}

#[test]
#[serial]
fn sub_into_y_e4() {
    sub_into_y::<E4, 8>(&E4_VALUES);
}

#[test]
#[serial]
fn sub_into_y_e6() {
    sub_into_y::<E6, 8>(&E6_VALUES);
}

#[test]
#[serial]
fn add_mixed_bf_e4() {
    mixed_binary_op_test(&BF_VALUES, &E4_VALUES, super::add::<BF, E4, E4>, |x, y| {
        let mut result = *y;
        result.add_assign_base(x);
        result
    });
}

#[test]
#[serial]
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
#[serial]
fn add_mixed_e4_bf() {
    mixed_binary_op_test(&E4_VALUES, &BF_VALUES, super::add::<E4, BF, E4>, |x, y| {
        let mut result = *x;
        result.add_assign_base(y);
        result
    });
}

#[test]
#[serial]
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
#[serial]
fn mul_mixed_bf_e4() {
    mixed_binary_op_test(&BF_VALUES, &E4_VALUES, super::mul::<BF, E4, E4>, |x, y| {
        let mut result = *y;
        result.mul_assign_by_base(x);
        result
    });
}

#[test]
#[serial]
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
#[serial]
fn mul_mixed_e4_bf() {
    mixed_binary_op_test(&E4_VALUES, &BF_VALUES, super::mul::<E4, BF, E4>, |x, y| {
        let mut result = *x;
        result.mul_assign_by_base(y);
        result
    });
}

#[test]
#[serial]
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
#[serial]
fn sub_mixed_bf_e4() {
    mixed_binary_op_test(&BF_VALUES, &E4_VALUES, super::sub::<BF, E4, E4>, |x, y| {
        let mut result = *y;
        result.negate();
        result.add_assign_base(x);
        result
    });
}

#[test]
#[serial]
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
#[serial]
fn sub_mixed_e4_bf() {
    mixed_binary_op_test(&E4_VALUES, &BF_VALUES, super::sub::<E4, BF, E4>, |x, y| {
        let mut result = *x;
        result.sub_assign_base(y);
        result
    });
}

#[test]
#[serial]
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
// #[test]
// fn sub() {
//     let device_fn = super::sub;
//     let host_fn = |x: &BF, y: &BF| *x.clone().sub_assign(y);
//     binary_op_test(device_fn, host_fn);
// }
//
// #[test]
// fn sub_into_x() {
//     let device_fn = super::sub_into_x;
//     let host_fn = |x: &BF, y: &BF| *x.clone().sub_assign(y);
//     binary_op_in_place_test(device_fn, host_fn);
// }
//
// #[test]
// fn sub_into_y() {
//     let device_fn = |y: &mut DeviceSlice<BF>, x: &DeviceSlice<BF>, stream: &CudaStream| {
//         super::sub_into_y(x, y, stream)
//     };
//     let host_fn = |y: &BF, x: &BF| *x.clone().sub_assign(y);
//     binary_op_in_place_test(device_fn, host_fn);
// }
//
// #[test]
// fn pow() {
//     let device_fn = super::pow;
//     let host_fn = |x: &BF, power: u32| x.clone().pow(power);
//     for power in [0, 1, 42, 255, 256] {
//         parametrized_unary_op_test(power, device_fn, host_fn);
//     }
// }
//
// #[test]
// fn pow_in_place() {
//     let device_fn = super::pow_in_place;
//     let host_fn = |x: &BF, power: u32| x.clone().pow(power);
//     for power in [0, 1, 42, 255, 256] {
//         parametrized_unary_op_in_place_test(power, device_fn, host_fn);
//     }
// }

// #[test]
// fn mul_add() {
//     let device_fn = super::mul_add;
//     let host_fn = |x: &BF, y: &BF, z: &BF| *x.clone().mul_assign(y).add_assign(z);
//     ternary_op_test(device_fn, host_fn);
// }
//
// #[test]
// fn mul_add_into_x() {
//     let device_fn = super::mul_add_into_x;
//     let host_fn = |x: &BF, y: &BF, z: &BF| *x.clone().mul_assign(y).add_assign(z);
//     ternary_op_in_place_test(device_fn, host_fn);
// }
//
// #[test]
// fn mul_add_into_y() {
//     let device_fn =
//         |y: &mut DeviceSlice<BF>,
//          x: &DeviceSlice<BF>,
//          z: &DeviceSlice<BF>,
//          stream: &CudaStream| super::mul_add_into_y(x, y, z, stream);
//     let host_fn = |y: &BF, x: &BF, z: &BF| *x.clone().mul_assign(y).add_assign(z);
//     ternary_op_in_place_test(device_fn, host_fn);
// }
//
// #[test]
// fn mul_add_into_z() {
//     let device_fn =
//         |z: &mut DeviceSlice<BF>,
//          x: &DeviceSlice<BF>,
//          y: &DeviceSlice<BF>,
//          stream: &CudaStream| super::mul_add_into_z(x, y, z, stream);
//     let host_fn = |z: &BF, x: &BF, y: &BF| *x.clone().mul_assign(y).add_assign(z);
//     ternary_op_in_place_test(device_fn, host_fn);
// }
//
// #[test]
// fn mul_sub() {
//     let device_fn = super::mul_sub;
//     let host_fn = |x: &BF, y: &BF, z: &BF| *x.clone().mul_assign(y).sub_assign(z);
//     ternary_op_test(device_fn, host_fn);
// }
//
// #[test]
// fn mul_sub_into_x() {
//     let device_fn = super::mul_sub_into_x;
//     let host_fn = |x: &BF, y: &BF, z: &BF| *x.clone().mul_assign(y).sub_assign(z);
//     ternary_op_in_place_test(device_fn, host_fn);
// }
//
// #[test]
// fn mul_sub_into_y() {
//     let device_fn =
//         |y: &mut DeviceSlice<BF>,
//          x: &DeviceSlice<BF>,
//          z: &DeviceSlice<BF>,
//          stream: &CudaStream| super::mul_sub_into_y(x, y, z, stream);
//     let host_fn = |y: &BF, x: &BF, z: &BF| *x.clone().mul_assign(y).sub_assign(z);
//     ternary_op_in_place_test(device_fn, host_fn);
// }
//
// #[test]
// fn mul_sub_into_z() {
//     let device_fn =
//         |z: &mut DeviceSlice<BF>,
//          x: &DeviceSlice<BF>,
//          y: &DeviceSlice<BF>,
//          stream: &CudaStream| super::mul_sub_into_z(x, y, z, stream);
//     let host_fn = |z: &BF, x: &BF, y: &BF| *x.clone().mul_assign(y).sub_assign(z);
//     ternary_op_in_place_test(device_fn, host_fn);
// }

mod helpers;
use crate::upstream::{Field, FieldExtension};
#[allow(unused_imports)]
use helpers::*;
