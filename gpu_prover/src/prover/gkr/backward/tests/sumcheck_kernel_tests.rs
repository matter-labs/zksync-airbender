use super::super::*;
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::cub::device_reduce::{get_reduce_temp_storage_bytes, ReduceOperation};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::{
    GpuBaseFieldPolySource, GpuExtensionFieldPolyContinuingLaunchDescriptor,
    GpuExtensionFieldPolyInitialSource, GpuSumcheckRound0DeviceLaunchDescriptors,
    GpuSumcheckRound0HostLaunchDescriptors, GpuSumcheckRound0ScheduledLaunchDescriptors,
};
use crate::prover::test_utils::make_test_context;
use era_cudart::memory::memory_copy_async;
use era_cudart::slice::{CudaSlice, CudaSliceMut};

use crate::upstream::Field;
use serial_test::serial;

use super::{
    alloc_and_copy, copy_device_values, eq_values_for_suffix, fold_eq_values_cpu,
    interleaved_pairs_to_strided, make_round0_eq_pair_values, sample_ext,
};

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn pairwise_round0_kernel_matches_cpu() {
    let context = make_test_context(64, 8);
    let input_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
    let output_values = (0..4).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
    let batch_challenge = sample_ext(200);
    let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge]);
    let input = alloc_and_copy(&context, &input_values);
    let output = alloc_and_copy(&context, &output_values);
    let mut contributions = alloc_and_copy(&context, &[E4::ZERO; 4]);

    let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
        callbacks: Callbacks::new(),
        host: GpuSumcheckRound0HostLaunchDescriptors {
            base_field_inputs: unsafe {
                context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
            },
            extension_field_inputs: unsafe {
                context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(1)
            },
            base_field_outputs: unsafe {
                context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
            },
            extension_field_outputs: unsafe {
                context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(1)
            },
        },
        device: GpuSumcheckRound0DeviceLaunchDescriptors {
            base_field_inputs: context
                .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                .unwrap(),
            extension_field_inputs: context
                .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(1, AllocationPlacement::Top)
                .unwrap(),
            base_field_outputs: context
                .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                .unwrap(),
            extension_field_outputs: context
                .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(1, AllocationPlacement::Top)
                .unwrap(),
        },
    };
    unsafe {
        round0
            .host
            .extension_field_inputs
            .get_mut_accessor()
            .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
            start: input.as_ptr(),
            next_layer_size: 4,
        };
        round0
            .host
            .extension_field_outputs
            .get_mut_accessor()
            .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
            start: output.as_ptr(),
            next_layer_size: 2,
        };
    }
    memory_copy_async(
        &mut round0.device.extension_field_inputs,
        &round0.host.extension_field_inputs,
        context.get_exec_stream(),
    )
    .unwrap();
    memory_copy_async(
        &mut round0.device.extension_field_outputs,
        &round0.host.extension_field_outputs,
        context.get_exec_stream(),
    )
    .unwrap();

    launch_pairwise_round0::<E4>(
        &round0,
        batch_challenges_dev.as_ptr(),
        contributions.as_mut_ptr(),
        2,
        &context,
    )
    .unwrap();
    let mut host = unsafe { context.alloc_host_uninit_slice(4) };
    memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    let actual = unsafe { host.get_accessor().get().to_vec() };

    let mut expected = Vec::new();
    for output_index in 0..2 {
        let index = output_index * 2;
        let mut c0 = batch_challenge;
        c0.mul_assign(&output_values[output_index]);
        let mut a = input_values[4 + index];
        a.sub_assign(&input_values[index]);
        let mut b = input_values[4 + index + 1];
        b.sub_assign(&input_values[index + 1]);
        let mut c1 = a;
        c1.mul_assign(&b);
        c1.mul_assign(&batch_challenge);
        expected.push(c0);
        expected.push(c1);
    }

    assert_eq!(actual, interleaved_pairs_to_strided(&expected));
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn lookup_round0_kernel_matches_cpu() {
    let context = make_test_context(64, 8);
    let input0_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
    let input1_values = (0..8).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
    let output_num_values = (0..4).map(|i| sample_ext(200 + i)).collect::<Vec<_>>();
    let output_den_values = (0..4).map(|i| sample_ext(300 + i)).collect::<Vec<_>>();
    let input0 = alloc_and_copy(&context, &input0_values);
    let input1 = alloc_and_copy(&context, &input1_values);
    let output_num = alloc_and_copy(&context, &output_num_values);
    let output_den = alloc_and_copy(&context, &output_den_values);
    let mut contributions: DeviceAllocation<E4> =
        context.alloc(4, AllocationPlacement::Top).unwrap();
    let batch0 = sample_ext(400);
    let batch1 = sample_ext(500);
    let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);

    let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
        callbacks: Callbacks::new(),
        host: GpuSumcheckRound0HostLaunchDescriptors {
            base_field_inputs: unsafe {
                context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
            },
            extension_field_inputs: unsafe {
                context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(2)
            },
            base_field_outputs: unsafe {
                context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
            },
            extension_field_outputs: unsafe {
                context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(2)
            },
        },
        device: GpuSumcheckRound0DeviceLaunchDescriptors {
            base_field_inputs: context
                .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                .unwrap(),
            extension_field_inputs: context
                .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(2, AllocationPlacement::Top)
                .unwrap(),
            base_field_outputs: context
                .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                .unwrap(),
            extension_field_outputs: context
                .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(2, AllocationPlacement::Top)
                .unwrap(),
        },
    };
    unsafe {
        round0
            .host
            .extension_field_inputs
            .get_mut_accessor()
            .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
            start: input0.as_ptr(),
            next_layer_size: 4,
        };
        round0
            .host
            .extension_field_inputs
            .get_mut_accessor()
            .get_mut()[1] = GpuExtensionFieldPolyInitialSource {
            start: input1.as_ptr(),
            next_layer_size: 4,
        };
        round0
            .host
            .extension_field_outputs
            .get_mut_accessor()
            .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
            start: output_num.as_ptr(),
            next_layer_size: 2,
        };
        round0
            .host
            .extension_field_outputs
            .get_mut_accessor()
            .get_mut()[1] = GpuExtensionFieldPolyInitialSource {
            start: output_den.as_ptr(),
            next_layer_size: 2,
        };
    }
    memory_copy_async(
        &mut round0.device.extension_field_inputs,
        &round0.host.extension_field_inputs,
        context.get_exec_stream(),
    )
    .unwrap();
    memory_copy_async(
        &mut round0.device.extension_field_outputs,
        &round0.host.extension_field_outputs,
        context.get_exec_stream(),
    )
    .unwrap();

    launch_lookup_round0::<E4>(
        &round0,
        batch_challenges_dev.as_ptr(),
        contributions.as_mut_ptr(),
        2,
        &context,
    )
    .unwrap();
    let mut host = unsafe { context.alloc_host_uninit_slice(4) };
    memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    let actual = unsafe { host.get_accessor().get().to_vec() };

    let mut expected = Vec::new();
    for output_index in 0..2 {
        let index = output_index * 2;
        let pair_index = index + 1;

        let mut a = input0_values[4 + index];
        a.sub_assign(&input0_values[index]);
        let mut b = input1_values[4 + index];
        b.sub_assign(&input1_values[index]);
        let mut c = input0_values[4 + pair_index];
        c.sub_assign(&input0_values[pair_index]);
        let mut d = input1_values[4 + pair_index];
        d.sub_assign(&input1_values[pair_index]);

        let mut num = a;
        num.mul_assign(&d);
        let mut t = c;
        t.mul_assign(&b);
        num.add_assign(&t);

        let mut den = b;
        den.mul_assign(&d);

        let mut c0 = batch0;
        c0.mul_assign(&output_num_values[output_index]);
        let mut output_den_term = batch1;
        output_den_term.mul_assign(&output_den_values[output_index]);
        c0.add_assign(&output_den_term);

        let mut c1 = batch0;
        c1.mul_assign(&num);
        let mut den_term = batch1;
        den_term.mul_assign(&den);
        c1.add_assign(&den_term);

        expected.push(c0);
        expected.push(c1);
    }

    assert_eq!(actual, interleaved_pairs_to_strided(&expected));
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn lookup_continuation_kernel_matches_cpu() {
    let context = make_test_context(64, 8);
    let prev0 = (0..16).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
    let prev1 = (0..16).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
    let challenge = sample_ext(300);
    let batch0 = sample_ext(400);
    let batch1 = sample_ext(500);
    let prev0_dev = alloc_and_copy(&context, &prev0);
    let prev1_dev = alloc_and_copy(&context, &prev1);
    let cache0: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
    let cache1: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
    let folding_challenge_dev = alloc_and_copy(&context, &[challenge]);
    let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);
    let descriptors = [
        GpuExtensionFieldPolyContinuingLaunchDescriptor {
            previous_layer_start: prev0_dev.as_ptr(),
            this_layer_start: cache0.as_ptr().cast_mut(),
            this_layer_size: 8,
            next_layer_size: 4,
            first_access: true,
        },
        GpuExtensionFieldPolyContinuingLaunchDescriptor {
            previous_layer_start: prev1_dev.as_ptr(),
            this_layer_start: cache1.as_ptr().cast_mut(),
            this_layer_size: 8,
            next_layer_size: 4,
            first_access: true,
        },
    ];
    let descriptors_dev = alloc_and_copy(&context, &descriptors);
    let contributions: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

    launch_lookup_continuation::<E4>(
        descriptors_dev.as_ptr(),
        folding_challenge_dev.as_ptr(),
        batch_challenges_dev.as_ptr(),
        false,
        contributions.as_ptr().cast_mut(),
        2,
        &context,
    )
    .unwrap();
    let mut host = unsafe { context.alloc_host_uninit_slice(4) };
    memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    let actual = unsafe { host.get_accessor().get().to_vec() };

    let fold = |values: &[E4], idx: usize| {
        let mut delta = values[8 + idx];
        delta.sub_assign(&values[idx]);
        let mut result = challenge;
        result.mul_assign(&delta);
        result.add_assign(&values[idx]);
        result
    };
    let mut expected = Vec::new();
    for output_index in 0..2 {
        let idx = output_index * 2;
        let a0 = fold(&prev0, idx);
        let a1_full = fold(&prev0, idx + 4);
        let mut da = a1_full;
        da.sub_assign(&a0);
        let b0 = fold(&prev1, idx);
        let b1_full = fold(&prev1, idx + 4);
        let mut db = b1_full;
        db.sub_assign(&b0);

        let c0 = fold(&prev0, idx + 1);
        let c1_full = fold(&prev0, idx + 5);
        let mut dc = c1_full;
        dc.sub_assign(&c0);
        let d0 = fold(&prev1, idx + 1);
        let d1_full = fold(&prev1, idx + 5);
        let mut dd = d1_full;
        dd.sub_assign(&d0);

        let mut num0 = a0;
        num0.mul_assign(&d0);
        let mut t0 = c0;
        t0.mul_assign(&b0);
        num0.add_assign(&t0);
        let mut den0 = b0;
        den0.mul_assign(&d0);

        let mut num1 = da;
        num1.mul_assign(&dd);
        let mut t1 = dc;
        t1.mul_assign(&db);
        num1.add_assign(&t1);
        let mut den1 = db;
        den1.mul_assign(&dd);

        let mut e0 = batch0;
        e0.mul_assign(&num0);
        let mut e0_den = batch1;
        e0_den.mul_assign(&den0);
        e0.add_assign(&e0_den);

        let mut e1 = batch0;
        e1.mul_assign(&num1);
        let mut e1_den = batch1;
        e1_den.mul_assign(&den1);
        e1.add_assign(&e1_den);

        expected.push(e0);
        expected.push(e1);
    }

    assert_eq!(actual, interleaved_pairs_to_strided(&expected));
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn pairwise_continuation_kernel_matches_cpu() {
    let context = make_test_context(64, 8);
    let prev = (0..16).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
    let challenge = sample_ext(300);
    let batch = sample_ext(400);
    let prev_dev = alloc_and_copy(&context, &prev);
    let cache: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
    let folding_challenge_dev = alloc_and_copy(&context, &[challenge]);
    let batch_challenges_dev = alloc_and_copy(&context, &[batch]);
    let descriptors = [GpuExtensionFieldPolyContinuingLaunchDescriptor {
        previous_layer_start: prev_dev.as_ptr(),
        this_layer_start: cache.as_ptr().cast_mut(),
        this_layer_size: 8,
        next_layer_size: 4,
        first_access: true,
    }];
    let descriptors_dev = alloc_and_copy(&context, &descriptors);
    let mut contributions: DeviceAllocation<E4> =
        context.alloc(4, AllocationPlacement::Top).unwrap();

    launch_pairwise_continuation::<E4>(
        descriptors_dev.as_ptr(),
        folding_challenge_dev.as_ptr(),
        batch_challenges_dev.as_ptr(),
        false,
        contributions.as_mut_ptr(),
        2,
        &context,
    )
    .unwrap();
    let mut host = unsafe { context.alloc_host_uninit_slice(4) };
    memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    let actual = unsafe { host.get_accessor().get().to_vec() };

    let fold = |values: &[E4], idx: usize| {
        let mut delta = values[8 + idx];
        delta.sub_assign(&values[idx]);
        let mut result = challenge;
        result.mul_assign(&delta);
        result.add_assign(&values[idx]);
        result
    };

    let mut expected = Vec::new();
    for output_index in 0..2 {
        let idx = output_index * 2;
        let even0 = fold(&prev, idx);
        let even1 = fold(&prev, idx + 4);
        let mut even_delta = even1;
        even_delta.sub_assign(&even0);

        let odd0 = fold(&prev, idx + 1);
        let odd1 = fold(&prev, idx + 5);
        let mut odd_delta = odd1;
        odd_delta.sub_assign(&odd0);

        let mut c0 = even0;
        c0.mul_assign(&odd0);
        c0.mul_assign(&batch);

        let mut c1 = even_delta;
        c1.mul_assign(&odd_delta);
        c1.mul_assign(&batch);

        expected.push(c0);
        expected.push(c1);
    }

    assert_eq!(actual, interleaved_pairs_to_strided(&expected));
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn accumulator_eq_multiply_and_reduce_match_cpu() {
    let context = make_test_context(64, 8);
    let accumulator = vec![
        sample_ext(10),
        sample_ext(20),
        sample_ext(11),
        sample_ext(21),
    ];
    let eq = vec![sample_ext(30), sample_ext(31)];
    let eq_dev = alloc_and_copy(&context, &eq);
    let mut accumulator_dev = alloc_and_copy(&context, &accumulator);
    let temp_bytes = get_reduce_temp_storage_bytes::<E4>(ReduceOperation::Sum, 2).unwrap();
    let mut temp = context.alloc(temp_bytes, AllocationPlacement::Top).unwrap();
    let mut reduced = context.alloc(2, AllocationPlacement::Top).unwrap();

    super::apply_eq_and_reduce_accumulator(
        &eq_dev,
        &mut accumulator_dev,
        &mut reduced,
        &mut temp,
        2,
        &context,
    )
    .unwrap();

    let mut host = unsafe { context.alloc_host_uninit_slice(2) };
    memory_copy_async(&mut host, &reduced, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    let actual = unsafe { host.get_accessor().get().to_vec() };

    let mut expected = [E4::ZERO; 2];
    for row in 0..2 {
        let mut row0 = accumulator[row];
        row0.mul_assign(&eq[row]);
        expected[0].add_assign(&row0);

        let mut row1 = accumulator[2 + row];
        row1.mul_assign(&eq[row]);
        expected[1].add_assign(&row1);
    }

    assert_eq!(actual, interleaved_pairs_to_strided(&expected));
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn pairwise_round0_kernel_accumulates_into_existing_buffer() {
    let context = make_test_context(64, 8);
    let input_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
    let output_values = (0..4).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
    let batch_challenge = sample_ext(200);
    let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge]);
    let input = alloc_and_copy(&context, &input_values);
    let output = alloc_and_copy(&context, &output_values);
    let initial = vec![
        sample_ext(300),
        sample_ext(301),
        sample_ext(302),
        sample_ext(303),
    ];
    let mut contributions = alloc_and_copy(&context, &initial);

    let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
        callbacks: Callbacks::new(),
        host: GpuSumcheckRound0HostLaunchDescriptors {
            base_field_inputs: unsafe {
                context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
            },
            extension_field_inputs: unsafe {
                context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(1)
            },
            base_field_outputs: unsafe {
                context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
            },
            extension_field_outputs: unsafe {
                context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(1)
            },
        },
        device: GpuSumcheckRound0DeviceLaunchDescriptors {
            base_field_inputs: context
                .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                .unwrap(),
            extension_field_inputs: context
                .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(1, AllocationPlacement::Top)
                .unwrap(),
            base_field_outputs: context
                .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                .unwrap(),
            extension_field_outputs: context
                .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(1, AllocationPlacement::Top)
                .unwrap(),
        },
    };
    unsafe {
        round0
            .host
            .extension_field_inputs
            .get_mut_accessor()
            .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
            start: input.as_ptr(),
            next_layer_size: 4,
        };
        round0
            .host
            .extension_field_outputs
            .get_mut_accessor()
            .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
            start: output.as_ptr(),
            next_layer_size: 2,
        };
    }
    memory_copy_async(
        &mut round0.device.extension_field_inputs,
        &round0.host.extension_field_inputs,
        context.get_exec_stream(),
    )
    .unwrap();
    memory_copy_async(
        &mut round0.device.extension_field_outputs,
        &round0.host.extension_field_outputs,
        context.get_exec_stream(),
    )
    .unwrap();

    launch_pairwise_round0::<E4>(
        &round0,
        batch_challenges_dev.as_ptr(),
        contributions.as_mut_ptr(),
        2,
        &context,
    )
    .unwrap();
    let mut host = unsafe { context.alloc_host_uninit_slice(4) };
    memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    let actual = unsafe { host.get_accessor().get().to_vec() };

    let mut expected = initial;
    for output_index in 0..2 {
        let index = output_index * 2;
        let mut c0 = batch_challenge;
        c0.mul_assign(&output_values[output_index]);
        expected[output_index].add_assign(&c0);

        let mut a = input_values[4 + index];
        a.sub_assign(&input_values[index]);
        let mut b = input_values[4 + index + 1];
        b.sub_assign(&input_values[index + 1]);
        let mut c1 = a;
        c1.mul_assign(&b);
        c1.mul_assign(&batch_challenge);
        expected[2 + output_index].add_assign(&c1);
    }

    assert_eq!(actual, expected);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn build_eq_values_from_point_matches_cpu() {
    let context = make_test_context(1024, 512);

    for (challenge_count, challenge_offset) in
        [(0usize, 0usize), (1, 1), (7, 2), (8, 0), (9, 3), (23, 1)]
    {
        let claim_point_len = challenge_offset + challenge_count + 1;
        let claim_point = (0..claim_point_len)
            .map(|idx| sample_ext(40 + idx as u32))
            .collect::<Vec<_>>();
        let claim_point_dev = alloc_and_copy(&context, &claim_point);
        let acc_size = 1usize << challenge_count;
        let mut eq_group_tables = context
            .alloc(
                eq_group_tables_len(challenge_count).max(1),
                AllocationPlacement::Top,
            )
            .unwrap();
        let mut eq_values = context
            .alloc(acc_size.max(1), AllocationPlacement::Top)
            .unwrap();

        launch_build_eq_values_from_point::<E4>(
            claim_point_dev.as_ptr(),
            challenge_offset,
            challenge_count,
            eq_group_tables.as_mut_ptr(),
            eq_values.as_mut_ptr(),
            acc_size,
            &context,
        )
        .unwrap();

        let actual = copy_device_values(&context, &eq_values);
        let expected = eq_values_for_suffix(
            &claim_point[challenge_offset..challenge_offset + challenge_count],
        );
        assert_eq!(
            actual, expected,
            "challenge_count={challenge_count}, challenge_offset={challenge_offset}"
        );
    }
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn build_round0_eq_values_from_pairs_matches_cpu() {
    let context = make_test_context(1024, 512);

    for challenge_count in [0usize, 1, 7, 8, 9, 23] {
        let claim_point = (0..=challenge_count)
            .map(|idx| sample_ext(400 + idx as u32))
            .collect::<Vec<_>>();
        let eq_pair_values = make_round0_eq_pair_values(&claim_point);
        let acc_size = 1usize << challenge_count;
        let mut eq_pair_values_dev = context
            .alloc(eq_pair_values.len().max(1), AllocationPlacement::Top)
            .unwrap();
        if !eq_pair_values.is_empty() {
            memory_copy_async(
                &mut eq_pair_values_dev,
                &eq_pair_values,
                context.get_exec_stream(),
            )
            .unwrap();
        }
        let eq_group_tables_len = super::round0_eq_group_tables_len(claim_point.len()).max(1);
        let mut eq_group_tables = context
            .alloc(eq_group_tables_len, AllocationPlacement::Top)
            .unwrap();
        let mut eq_values = context
            .alloc(acc_size.max(1), AllocationPlacement::Top)
            .unwrap();

        launch_build_round0_eq_values_from_pairs::<E4>(
            eq_pair_values_dev.as_ptr(),
            challenge_count,
            eq_group_tables.as_mut_ptr(),
            eq_values.as_mut_ptr(),
            acc_size,
            &context,
        )
        .unwrap();

        let actual = copy_device_values(&context, &eq_values);
        let expected = eq_values_for_suffix(&claim_point[1..]);
        assert_eq!(actual, expected, "challenge_count={challenge_count}");
    }
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn fold_eq_values_in_place_matches_cpu() {
    let context = make_test_context(1024, 512);
    let challenge_count = 23usize;
    let claim_point = (0..=challenge_count)
        .map(|idx| sample_ext(500 + idx as u32))
        .collect::<Vec<_>>();
    let mut expected = eq_values_for_suffix(&claim_point[1..]);
    let mut eq_values = alloc_and_copy(&context, &expected);
    let mut current_len = expected.len();

    while current_len > 1 {
        let half_len = current_len / 2;
        launch_fold_eq_values_in_place::<E4>(eq_values.as_mut_ptr(), half_len, &context).unwrap();
        fold_eq_values_cpu(&mut expected);
        let actual = copy_device_values(&context, &eq_values[..half_len]);
        assert_eq!(actual, expected, "current_len={current_len}");
        current_len = half_len;
    }
}

// ---------------------------------------------------------------------------
// CPU ground-truth helpers for the GPU factored-eq layout used by the
// backward GKR sumcheck (Task 1 of the eq-factor plan).
// ---------------------------------------------------------------------------

fn random_e4<R: rand::Rng>(rng: &mut R) -> E4 {
    use field::PrimeField;
    E4::from_array_of_base([
        BF::from_u64_with_reduction(rng.random()),
        BF::from_u64_with_reduction(rng.random()),
        BF::from_u64_with_reduction(rng.random()),
        BF::from_u64_with_reduction(rng.random()),
    ])
}

/// Mirror of the GPU factored eq layout. Returns
/// `(high_groups: Vec<Vec<E4>>, low_group: Vec<E4>)`.
/// Group ordering matches `gkr_build_eq_values_from_group_tables`: group 0
/// covers the HIGH bits of gid, last group covers the LOW bits.
fn cpu_factored_eq(
    claim_point: &[E4],
    challenge_offset: usize,
    challenge_count: usize,
) -> (Vec<Vec<E4>>, Vec<E4>) {
    use crate::prover::gkr::backward::{eq_group_count, GKR_EQ_GROUP_SIZE};
    let g_count = eq_group_count(challenge_count);
    let mut groups: Vec<Vec<E4>> = Vec::with_capacity(g_count);
    let mut consumed = 0usize;
    for _g in 0..g_count {
        let remaining = challenge_count - consumed;
        let g_size = remaining.min(GKR_EQ_GROUP_SIZE);
        let g_len = 1usize << g_size;
        let mut table = vec![E4::ONE; g_len];
        for local in 0..g_len {
            for bit in 0..g_size {
                let shift_in_group = g_size - 1 - bit;
                let is_one = ((local >> shift_in_group) & 1) == 1;
                let challenge_idx = challenge_offset + consumed + bit;
                let r = claim_point[challenge_idx];
                let factor = if is_one {
                    r
                } else {
                    let mut one_minus = E4::ONE;
                    one_minus.sub_assign(&r);
                    one_minus
                };
                table[local].mul_assign(&factor);
            }
        }
        groups.push(table);
        consumed += g_size;
    }
    let low = if groups.is_empty() {
        vec![E4::ONE]
    } else {
        groups.pop().unwrap()
    };
    (groups, low)
}

/// Reconstruct eq_values[gid] for gid in 0..2^challenge_count from the factored
/// representation. Used by tests to compare against `eq_values_for_suffix`.
fn cpu_eval_factored_eq(
    high_groups: &[Vec<E4>],
    low_group: &[E4],
    challenge_count: usize,
) -> Vec<E4> {
    let n = 1usize << challenge_count;
    let mut out = vec![E4::ONE; n];
    for gid in 0..n {
        let mut acc = E4::ONE;
        let mut consumed = 0usize;
        for hg in high_groups {
            let g_size = hg.len().trailing_zeros() as usize;
            let shift = challenge_count - consumed - g_size;
            let local = (gid >> shift) & ((1usize << g_size) - 1);
            acc.mul_assign(&hg[local]);
            consumed += g_size;
        }
        let low_size = low_group.len().trailing_zeros() as usize;
        let local_low = gid & ((1usize << low_size) - 1);
        acc.mul_assign(&low_group[local_low]);
        out[gid] = acc;
    }
    out
}

#[test]
fn cpu_factored_eq_matches_eq_values_for_suffix() {
    use rand::SeedableRng;
    let mut rng = rand::rngs::StdRng::seed_from_u64(0xEF_FA_C7);
    for &(offset, count) in &[(0, 0), (0, 1), (0, 7), (0, 8), (0, 9), (0, 23), (1, 22)] {
        let total = offset + count + 4;
        let claim_point: Vec<E4> = (0..total).map(|_| random_e4(&mut rng)).collect();
        let (highs, low) = cpu_factored_eq(&claim_point, offset, count);
        let reconstructed = cpu_eval_factored_eq(&highs, &low, count);
        let reference = eq_values_for_suffix(&claim_point[offset..offset + count]);
        assert_eq!(reconstructed, reference, "offset={offset} count={count}");
    }
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn build_eq_factored_matches_cpu() {
    use rand::SeedableRng;
    let context = make_test_context(64, 8);
    let mut rng = rand::rngs::StdRng::seed_from_u64(0x_E4_FA_C7_01);

    for &(offset, count) in &[
        (0, 1),
        (0, 7),
        (0, 8),
        (0, 9),
        (0, 16),
        (0, 17),
        (0, 23),
        (1, 22),
    ] {
        let claim_point: Vec<E4> = (0..(offset + count + 1))
            .map(|_| random_e4(&mut rng))
            .collect();
        let d_claim_point = alloc_and_copy(&context, &claim_point);
        let mut d_low: DeviceAllocation<E4> = context
            .alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)
            .unwrap();
        let high_ptr = get_eq_high_constant_device_ptr();
        launch_build_eq_high_and_low_groups_from_point::<E4>(
            d_claim_point.as_ptr(),
            offset,
            count,
            high_ptr,
            d_low.as_mut_ptr(),
            &context,
        )
        .unwrap();
        // Read back the __constant__ high slab via a DeviceSlice synthesized
        // from the symbol's device pointer.
        // SAFETY: ab_gkr_eq_high has GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN
        // elements; the synthesized slice is short-lived and used only for the
        // device→host copy below.
        let high_slice = unsafe {
            era_cudart::slice::DeviceSlice::<E4>::from_raw_parts(
                high_ptr,
                GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN,
            )
        };
        let high_back = copy_device_values(&context, high_slice);
        let low_back = copy_device_values(&context, &d_low[..]);

        let (cpu_highs, cpu_low) = cpu_factored_eq(&claim_point, offset, count);
        for (g, hg) in cpu_highs.iter().enumerate() {
            for (local, expected) in hg.iter().enumerate() {
                assert_eq!(
                    high_back[g * GKR_EQ_GROUP_TABLE_LEN + local],
                    *expected,
                    "offset={offset} count={count} g={g} local={local}"
                );
            }
        }
        for (local, expected) in cpu_low.iter().enumerate() {
            assert_eq!(
                low_back[local], *expected,
                "offset={offset} count={count} low local={local}"
            );
        }
    }
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn inline_eq_matches_cpu_factored() {
    use rand::SeedableRng;
    // Sized to fit the largest case (count = 23): `d_out` is 2^23 * 16 B =
    // 128 MiB on its own; the rest of the per-iteration allocations are
    // small. The same sizing as `build_eq_values_from_point_matches_cpu`.
    let context = make_test_context(1024, 512);
    let mut rng = rand::rngs::StdRng::seed_from_u64(0x_E4_FA_C7_02);

    for &count in &[1usize, 7, 8, 9, 16, 17, 23] {
        let claim_point: Vec<E4> = (0..(count + 1)).map(|_| random_e4(&mut rng)).collect();
        let d_claim_point = alloc_and_copy(&context, &claim_point);
        let mut d_low: DeviceAllocation<E4> = context
            .alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)
            .unwrap();
        let high_ptr = get_eq_high_constant_device_ptr();
        launch_build_eq_high_and_low_groups_from_point::<E4>(
            d_claim_point.as_ptr(),
            0,
            count,
            high_ptr,
            d_low.as_mut_ptr(),
            &context,
        )
        .unwrap();

        let acc_size = 1usize << count;
        let mut d_out: DeviceAllocation<E4> =
            context.alloc(acc_size, AllocationPlacement::Top).unwrap();

        let sizes = make_eq_sizes(count);
        launch_materialize_eq_from_factored_for_test::<E4>(
            d_low.as_ptr(),
            &sizes,
            d_out.as_mut_ptr(),
            acc_size,
            &context,
        )
        .unwrap();

        let got = copy_device_values(&context, &d_out[..]);
        let want = eq_values_for_suffix(&claim_point[0..count]);
        assert_eq!(got, want, "count={count}");
    }
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn fold_eq_high_group_matches_cpu() {
    use rand::SeedableRng;
    let context = make_test_context(1024, 512);
    let mut rng = rand::rngs::StdRng::seed_from_u64(0x_E4_FA_C7_03);
    let count = 17usize;
    let claim_point: Vec<E4> = (0..(count + 1)).map(|_| random_e4(&mut rng)).collect();
    let d_claim_point = alloc_and_copy(&context, &claim_point);
    let mut d_low: DeviceAllocation<E4> = context
        .alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)
        .unwrap();
    let high_ptr = get_eq_high_constant_device_ptr();
    launch_build_eq_high_and_low_groups_from_point::<E4>(
        d_claim_point.as_ptr(),
        0,
        count,
        high_ptr,
        d_low.as_mut_ptr(),
        &context,
    )
    .unwrap();

    // CPU expected result: fold the top high group in half.
    let (mut cpu_highs, _cpu_low) = cpu_factored_eq(&claim_point, 0, count);
    let g0_size_before = (cpu_highs[0].len() as usize).trailing_zeros() as usize;
    let new_g0_size = g0_size_before - 1;
    let new_g0_len = 1usize << new_g0_size;
    let mut new_g0 = vec![E4::ZERO; new_g0_len];
    for i in 0..new_g0_len {
        let mut sum = cpu_highs[0][i];
        sum.add_assign(&cpu_highs[0][i | new_g0_len]);
        new_g0[i] = sum;
    }
    cpu_highs[0] = new_g0;

    // GPU: fold high slot 0 in the __constant__ symbol in place.
    launch_fold_eq_high_in_constant::<E4>(0, g0_size_before, &context).unwrap();

    // Read back slot 0 of the __constant__ symbol.
    // SAFETY: see equivalent block in `cpu_factored_eq_matches_kernel_build`.
    let high_slice = unsafe {
        era_cudart::slice::DeviceSlice::<E4>::from_raw_parts(high_ptr, GKR_EQ_GROUP_TABLE_LEN)
    };
    let high_back = copy_device_values(&context, high_slice);
    for (local, expected) in cpu_highs[0].iter().enumerate() {
        assert_eq!(high_back[local], *expected, "local={local}");
    }
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn multi_round_fold_matches_cpu() {
    use rand::SeedableRng;
    let context = make_test_context(1024, 512);
    let mut rng = rand::rngs::StdRng::seed_from_u64(0x_E4_FA_C7_04);
    let count = 17usize;
    let claim_point: Vec<E4> = (0..(count + 1)).map(|_| random_e4(&mut rng)).collect();
    let d_claim_point = alloc_and_copy(&context, &claim_point);
    let mut d_low: DeviceAllocation<E4> = context
        .alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)
        .unwrap();
    let high_ptr = get_eq_high_constant_device_ptr();
    launch_build_eq_high_and_low_groups_from_point::<E4>(
        d_claim_point.as_ptr(),
        0,
        count,
        high_ptr,
        d_low.as_mut_ptr(),
        &context,
    )
    .unwrap();

    // Drive the production fold helper across all `count` rounds, covering
    // both the high-slab fold path (rounds 0..16) and the low-slab fold path
    // (round 16). The cross-slot transition (slot 0 → slot 1) fires at
    // round 8 of the [8,8,1] partition.
    let mut sizes = make_eq_sizes(count);

    for round in 0..count {
        let acc_size = 1usize << (count - round);
        let mut d_out: DeviceAllocation<E4> =
            context.alloc(acc_size, AllocationPlacement::Top).unwrap();
        launch_materialize_eq_from_factored_for_test::<E4>(
            d_low.as_ptr(),
            &sizes,
            d_out.as_mut_ptr(),
            acc_size,
            &context,
        )
        .unwrap();
        let got = copy_device_values(&context, &d_out[..]);
        let want = eq_values_for_suffix(&claim_point[round..count]);
        assert_eq!(got, want, "round={round}");

        fold_factored_eq_one_round::<E4>(&mut sizes, d_low.as_mut_ptr(), &context).unwrap();
    }
}
