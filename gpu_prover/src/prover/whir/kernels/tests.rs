use super::*;

use crate::primitives::device_structures::DeviceMatrix;
use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use field::{Field, Rand};
use itertools::Itertools;
use rand::rng;
use serial_test::serial;

fn run_partially_evaluate_monomials_by_ref(log_count: usize) {
    use crate::ops::cub::device_reduce::{get_reduce_temp_storage_bytes, reduce, ReduceOperation};
    use fft::utils::bitreverse_enumeration_inplace;

    let count = 1 << log_count;
    let stride = 2 * count;
    let bf_elems = 4 * stride;
    let bitreversed_vectorized_src = (0..bf_elems)
        .map(|_| BF::random_element(&mut rng()))
        .collect_vec();

    let mut h_monomials = (0..count)
        .map(|i| {
            let coeffs = std::array::from_fn(|j| bitreversed_vectorized_src[i + stride * j]);
            E4::from_array_of_base(coeffs)
        })
        .collect_vec();
    bitreverse_enumeration_inplace(&mut h_monomials);
    let z = E4::random_element(&mut rng());
    let mut cpu_result = h_monomials[count - 1];
    for i in 2..=count {
        cpu_result.mul_assign(&z);
        cpu_result.add_assign(&h_monomials[count - i]);
    }

    let stream = CudaStream::default();
    let mut d_src = DeviceAllocation::alloc(bf_elems).unwrap();
    let mut d_z = DeviceAllocation::alloc(1).unwrap();
    let mut scratch0 = DeviceAllocation::alloc(stride / 2).unwrap(); // like GpuWhirState
    let mut scratch1 = DeviceAllocation::alloc(1).unwrap();
    memory_copy_async(&mut d_src, &bitreversed_vectorized_src[..], &stream).unwrap();
    memory_copy_async(&mut d_z, &[z], &stream).unwrap();
    let d_src_matrix = DeviceMatrix::new(&d_src, stride);
    let partials_count = partially_evaluate_monomials_by_ref(
        &d_src_matrix,
        &mut scratch0[..],
        &mut scratch1[..],
        &d_z[..],
        count,
        &stream,
    )
    .unwrap();

    let reduce_temp_bytes =
        get_reduce_temp_storage_bytes::<E4>(ReduceOperation::Sum, partials_count as i32).unwrap();
    let mut reduce_temp = DeviceAllocation::alloc(reduce_temp_bytes).unwrap();
    let mut reduce_result = DeviceAllocation::alloc(1).unwrap();

    reduce(
        ReduceOperation::Sum,
        &mut reduce_temp,
        &scratch0[..partials_count],
        &mut reduce_result[0],
        &stream,
    )
    .unwrap();

    let mut gpu_result = vec![E4::ZERO; 1];
    memory_copy_async(&mut gpu_result[..], &mut reduce_result[..], &stream).unwrap();
    stream.synchronize().unwrap();
    assert_eq!(cpu_result, gpu_result[0]);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_partially_evaluate_monomials_by_ref_small() {
    run_partially_evaluate_monomials_by_ref(6);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn test_partially_evaluate_monomials_by_ref() {
    run_partially_evaluate_monomials_by_ref(23);
}
