use super::*;
use crate::gkr::prover::forward_loop::utils::mem_access_fn;
use cs::definitions::gkr::AddressSpaceType;
use cs::gkr_compiler::InitsOrTeardownsTimestampAndValue;

pub(crate) fn materialize_inits_and_teardowns_tuple_pair<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const WORD_BITS: u32,
>(
    ts_and_value: &InitsOrTeardownsTimestampAndValue,
    address_high_bits: [u32; 2],
    gkr_storage: &GKRStorage<F, E>,
    trace_len: usize,
    external_challenges: &GKRExternalChallenges<F, E>,
    compiled_circuit: &GKRCircuitArtifact<F>,
    worker: &Worker,
) -> Box<[E]> {
    unsafe {
        let high_bits_offset = high_bits_offset_for_inits_and_teardowns::<WORD_BITS>(trace_len);
        let mut destination = Box::<[E], Global>::new_uninit_slice(trace_len);
        let ext_destination = vec![&mut destination[..]];
        let mut sources = Vec::with_capacity(compiled_circuit.memory_layout.total_width);
        for i in 0..compiled_circuit.memory_layout.total_width {
            let src = gkr_storage.get_base_layer_mem(i);
            sources.push(src);
        }
        let base_layer_memory_sources = &sources[..];
        let address_low = gkr_storage.get_base_layer(GKRAddress::VirtualSetup(
            VirtualSetupPoly::InitsAndTeardownsLow,
        ));
        let address_high = gkr_storage.get_base_layer(GKRAddress::VirtualSetup(
            VirtualSetupPoly::InitsAndTeardownsHigh,
        ));

        apply_row_wise::<F, _>(
            vec![],
            ext_destination,
            trace_len,
            worker,
            |_, ext_dest, chunk_start, chunk_size| {
                assert_eq!(ext_dest.len(), 1);
                let mut ext_dest = ext_dest;
                let dest = ext_dest.pop().unwrap();
                for i in 0..chunk_size {
                    // almost like memory tuple, but very limited
                    let absolute_row_idx = chunk_start + i;

                    let result = match ts_and_value {
                        InitsOrTeardownsTimestampAndValue::Init => {
                            let lhs = evaluate_init(
                                absolute_row_idx,
                                address_high_bits[0],
                                high_bits_offset,
                                address_low,
                                address_high,
                                external_challenges,
                            );
                            let rhs = evaluate_init(
                                absolute_row_idx,
                                address_high_bits[1],
                                high_bits_offset,
                                address_low,
                                address_high,
                                external_challenges,
                            );

                            let mut result = lhs;
                            result.mul_assign(&rhs);

                            result
                        }
                        InitsOrTeardownsTimestampAndValue::Teardown {
                            lhs_timestamp,
                            lhs_value,
                            rhs_timestamp,
                            rhs_value,
                        } => {
                            let lhs = evaluate_teardown(
                                absolute_row_idx,
                                address_high_bits[0],
                                high_bits_offset,
                                *lhs_timestamp,
                                *lhs_value,
                                base_layer_memory_sources,
                                address_low,
                                address_high,
                                external_challenges,
                            );
                            let rhs = evaluate_teardown(
                                absolute_row_idx,
                                address_high_bits[1],
                                high_bits_offset,
                                *rhs_timestamp,
                                *rhs_value,
                                base_layer_memory_sources,
                                address_low,
                                address_high,
                                external_challenges,
                            );

                            let mut result = lhs;
                            result.mul_assign(&rhs);

                            result
                        }
                    };

                    dest.get_unchecked_mut(i).write(result);
                }
            },
        );

        destination.assume_init()
    }
}

pub(crate) fn evaluate_init<F: PrimeField, E: FieldExtension<F> + Field>(
    row: usize,
    address_high_bits: u32,
    high_bits_offset: u32,
    address_low: &[F],
    address_high: &[F],
    external_challenges: &GKRExternalChallenges<F, E>,
) -> E {
    let mut result = external_challenges.permutation_argument_additive_part;
    // address space is RAM
    result.add_assign_base(&F::from_u32_unchecked(AddressSpaceType::RAM as u32));

    // address
    {
        let mut t = external_challenges.permutation_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let el = address_low[row];
        t.mul_assign_by_base(&el);
        result.add_assign(&t);
    }
    {
        let mut t = external_challenges.permutation_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
        let mut el = address_high[row];
        el.add_assign(&F::from_u32_unchecked(
            address_high_bits << high_bits_offset,
        ));
        t.mul_assign_by_base(&el);
        result.add_assign(&t);
    }

    // values and TS are 0

    result
}

pub(crate) fn evaluate_teardown<F: PrimeField, E: FieldExtension<F> + Field>(
    row: usize,
    address_high_bits: u32,
    high_bits_offset: u32,
    timestamp: [usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    value: [usize; 2],
    base_layer_memory_sources: &[&[F]],
    address_low: &[F],
    address_high: &[F],
    external_challenges: &GKRExternalChallenges<F, E>,
) -> E {
    let mut result = external_challenges.permutation_argument_additive_part;
    // address space is RAM
    result.add_assign_base(&F::from_u32_unchecked(AddressSpaceType::RAM as u32));

    // address
    {
        let mut t = external_challenges.permutation_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let el = address_low[row];
        t.mul_assign_by_base(&el);
        result.add_assign(&t);
    }
    {
        let mut t = external_challenges.permutation_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
        let mut el = address_high[row];
        el.add_assign(&F::from_u32_unchecked(
            address_high_bits << high_bits_offset,
        ));
        t.mul_assign_by_base(&el);
        result.add_assign(&t);
    }

    for (idx, offset) in [
        (
            MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
            timestamp[0],
        ),
        (
            MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
            timestamp[1],
        ),
    ] {
        let mut t = external_challenges.permutation_argument_linearization_challenges[idx];
        let el = mem_access_fn(base_layer_memory_sources, offset, row);
        t.mul_assign_by_base(&el);
        result.add_assign(&t);
    }

    for (idx, offset) in [
        (MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX, value[0]),
        (MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX, value[1]),
    ] {
        let mut t = external_challenges.permutation_argument_linearization_challenges[idx];
        let el = mem_access_fn(base_layer_memory_sources, offset, row);
        t.mul_assign_by_base(&el);
        result.add_assign(&t);
    }

    result
}
