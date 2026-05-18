use super::*;
use crate::allocator::tracker::AllocationPlacement;

use crate::primitives::context::{DeviceAllocation, ProverContext};
use crate::primitives::field::{BF, E4};

use era_cudart::memory::memory_copy_async;
use era_cudart::slice::{CudaSlice, DeviceSlice};
use worker::{IterableWithGeometry, Worker};

fn sample_ext(seed: u32) -> E4 {
    E4::from_array_of_base([
        BF::new(seed),
        BF::new(seed + 1),
        BF::new(seed + 2),
        BF::new(seed + 3),
    ])
}

fn sample_external_challenges(seed: u32) -> GKRExternalChallenges<BF, E4> {
    GKRExternalChallenges {
        permutation_argument_linearization_challenges: std::array::from_fn(|idx| {
            sample_ext(seed + 10 + idx as u32)
        }),
        permutation_argument_additive_part: sample_ext(seed),
        _marker: std::marker::PhantomData,
    }
}

fn successive_powers<E: Field>(base: E, count: usize) -> Vec<E> {
    let mut current = E::ONE;
    (0..count)
        .map(|_| {
            let result = current;
            current.mul_assign(&base);
            result
        })
        .collect()
}

fn interleaved_pairs_to_strided<T: Copy>(values: &[T]) -> Vec<T> {
    assert_eq!(values.len() % 2, 0);
    let pair_count = values.len() / 2;
    let mut result = Vec::with_capacity(values.len());
    for idx in 0..pair_count {
        result.push(values[idx * 2]);
    }
    for idx in 0..pair_count {
        result.push(values[idx * 2 + 1]);
    }
    result
}

fn alloc_and_copy<T: Copy>(context: &ProverContext, values: &[T]) -> DeviceAllocation<T> {
    let mut allocation = context
        .alloc(values.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut allocation, values, context.get_exec_stream()).unwrap();
    allocation
}

fn copy_device_values<T: Copy>(context: &ProverContext, values: &DeviceSlice<T>) -> Vec<T> {
    let mut allocation = unsafe { context.alloc_host_uninit_slice(values.len()) };
    memory_copy_async(&mut allocation, values, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    unsafe { allocation.get_accessor().get().to_vec() }
}

fn eq_values_for_suffix(challenges: &[E4]) -> Vec<E4> {
    let acc_size = 1usize << challenges.len();
    let mut result = vec![E4::ZERO; acc_size];
    // CPU reference for sumcheck tests: acc_size grows to 2^23 at the
    // largest test sizes and each entry costs O(challenges.len()) E4
    // multiplies, so this dominated the test wall time at ~3.4 s each.
    // Each `gid` is independent — parallelize across the column slice.
    let worker = Worker::new();
    worker.scope(acc_size, |scope, geometry| {
        result
            .chunks_for_geometry_mut(geometry)
            .enumerate()
            .for_each(|(idx, chunk)| {
                let chunk_start = geometry.get_chunk_start_pos(idx);
                Worker::smart_spawn(scope, idx == geometry.len() - 1, move |_| {
                    for (offset, slot) in chunk.iter_mut().enumerate() {
                        let gid = chunk_start + offset;
                        let mut acc = E4::ONE;
                        for (i, challenge) in challenges.iter().copied().enumerate() {
                            let bit = ((gid >> (challenges.len() - 1 - i)) & 1) != 0;
                            let term = if bit {
                                challenge
                            } else {
                                let mut one_minus = E4::ONE;
                                one_minus.sub_assign(&challenge);
                                one_minus
                            };
                            acc.mul_assign(&term);
                        }
                        *slot = acc;
                    }
                });
            });
    });
    result
}

fn fold_eq_values_cpu(values: &mut Vec<E4>) {
    assert!(values.len().is_power_of_two());
    let half_len = values.len() / 2;
    for idx in 0..half_len {
        let upper = values[idx + half_len];
        values[idx].add_assign(&upper);
    }
    values.truncate(half_len);
}

mod constraints_and_main_layer_tests;
mod dimension_reduction_tests;
mod helpers;
mod lookup_builders;
mod lookup_expression_tests;
mod sumcheck_kernel_tests;

use crate::upstream::{Field, GKRExternalChallenges};
pub(super) use helpers::build_main_layer_kernel_blueprints;
use helpers::{build_dimension_reducing_kernel_blueprints, make_round0_eq_pair_values};
pub(crate) use lookup_builders::{
    build_lookup_from_vector_input_with_setup_inputs_and_metadata,
    build_lookup_pair_from_base_inputs_inputs_and_metadata,
    build_lookup_pair_from_vector_inputs_inputs_and_metadata,
    build_lookup_unbalanced_pair_with_vector_inputs_inputs_and_metadata,
    build_lookup_with_dens_and_setup_expressions_inputs_and_metadata,
};
