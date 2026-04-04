use super::*;
use crate::gkr::prover::apply_row_wise;
use cs::definitions::gkr::NoFieldLinearRelation;
use cs::definitions::gkr::NoFieldSingleColumnLookupRelation;
use cs::definitions::gkr::NoFieldVectorLookupRelation;
use cs::gkr_compiler::NoFieldSpecialMemoryContributionRelation;
use field::{Field, FieldExtension, PrimeField};
use std::alloc::Global;

pub(crate) fn materialize_vector_lookup_input<F: PrimeField, E: FieldExtension<F> + Field>(
    rel: &NoFieldVectorLookupRelation,
    gkr_storage: &GKRStorage<F, E>,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    trace_len: usize,
    preprocessed_generic_lookup: &[E],
    lookup_challenges_multiplicative_part: E,
    decoder_lookup_fill_value: E,
    offset_for_decoder_table: u32,
    decoder_predicate_address: GKRAddress,
    worker: &Worker,
) -> Box<[E]> {
    // we materialize it, but the good thing is that we have a cache of lookups
    let lookup_set_index = rel.lookup_set_index;
    let mut destination = Box::<[E], Global>::new_uninit_slice(trace_len);
    let ext_destination = vec![&mut destination[..]];
    let is_decoder_lookup = lookup_set_index == DECODER_LOOKUP_FORMAL_SET_INDEX;
    let mapping_ref = if is_decoder_lookup == false {
        // println!("Mapping lookup access number {}", lookup_set_index);
        &witness_trace.generic_lookup_mapping[lookup_set_index]
    } else {
        // println!("Mapping decoder lookup");
        assert!(witness_trace.generic_lookup_mapping.len() > 0);
        witness_trace.generic_lookup_mapping.last().unwrap()
    };
    let decoder_predicate = if is_decoder_lookup {
        gkr_storage.get_base_layer(decoder_predicate_address)
    } else {
        &[]
    };
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
                let row = chunk_start + i;
                let mapping_index = mapping_ref[row];
                let mapped_value = preprocessed_generic_lookup[mapping_index as usize];
                if is_decoder_lookup {
                    let decoder_mask_value = decoder_predicate[row].as_boolean();
                    if decoder_mask_value {
                        dest[i].write(mapped_value);
                    } else {
                        dest[i].write(decoder_lookup_fill_value);
                    }
                } else {
                    dest[i].write(mapped_value);
                }

                #[cfg(feature = "gkr_self_checks")]
                {
                    if is_decoder_lookup {
                        let decoder_mask_value = decoder_predicate[row].as_boolean();
                        if decoder_mask_value {
                            assert!(mapping_index >= offset_for_decoder_table, "decoder lookup should have mapping index {} >= decoder table offset {}, and is not zero in padding", mapping_index, offset_for_decoder_table);
                        } else {
                            assert_eq!(
                                mapping_index, 0,
                                "decoder lookup should have mapping index zero in padding"
                            );
                        }
                    } else {
                        assert!(
                            mapping_index < offset_for_decoder_table,
                            "ordinary lookup should have mapping index {} < decoder table offset {}",
                            mapping_index,
                            offset_for_decoder_table
                        );
                    }
                }

                #[cfg(feature = "gkr_self_checks")]
                {
                    let naive_eval = {
                        let mut result = E::from_base(evaluate_linear_relation_at_row(
                            &rel.columns[0],
                            gkr_storage,
                            row,
                        ));
                        let mut challenge = lookup_challenges_multiplicative_part;
                        for rel in rel.columns[1..].iter() {
                            let mut t = challenge;
                            t.mul_assign_by_base(&evaluate_linear_relation_at_row(
                                rel,
                                gkr_storage,
                                row,
                            ));
                            result.add_assign(&t);

                            challenge.mul_assign(&lookup_challenges_multiplicative_part);
                        }

                        result
                    };

                    if is_decoder_lookup {
                        let decoder_mask_value = decoder_predicate[row].as_boolean();
                        if decoder_mask_value {
                            if naive_eval != mapped_value {
                                for (idx, rel) in rel.columns.iter().enumerate() {
                                    let v = evaluate_linear_relation_at_row(rel, gkr_storage, row);
                                    println!("Column {} = {}", idx, v);
                                }
                            }
                            assert_eq!(
                                naive_eval, mapped_value,
                                "decoder lookup diverged at row {} for relation {:?}",
                                row, rel
                            );
                        } else {
                            if naive_eval != decoder_lookup_fill_value {
                                for (idx, rel) in rel.columns.iter().enumerate() {
                                    let v = evaluate_linear_relation_at_row(rel, gkr_storage, row);
                                    println!("Column {} = {}", idx, v);
                                }
                            }
                            assert_eq!(
                                naive_eval, decoder_lookup_fill_value,
                                "decoder lookup diverged at filling row {} for relation {:?}",
                                row, rel
                            );
                        }
                    } else {
                        if naive_eval != mapped_value {
                            for (idx, rel) in rel.columns.iter().enumerate() {
                                let v = evaluate_linear_relation_at_row(rel, gkr_storage, row);
                                println!("Column {} = {}", idx, v);
                            }
                        }
                        assert_eq!(
                            naive_eval, mapped_value,
                            "generic lookup diverged at row {} for relation {:?}",
                            row, rel
                        );
                    }
                }
            }
        },
    );
    let destination = unsafe { destination.assume_init() };

    destination
}

pub(crate) fn materialize_memory_tuple<F: PrimeField, E: FieldExtension<F> + Field>(
    rel: &NoFieldSpecialMemoryContributionRelation,
    gkr_storage: &GKRStorage<F, E>,
    trace_len: usize,
    external_challenges: &GKRExternalChallenges<F, E>,
    compiled_circuit: &GKRCircuitArtifact<F>,
    worker: &Worker,
) -> Box<[E]> {
    unsafe {
        let mut destination = Box::<[E], Global>::new_uninit_slice(trace_len);
        let ext_destination = vec![&mut destination[..]];
        let mut sources = Vec::with_capacity(compiled_circuit.memory_layout.total_width);
        for i in 0..compiled_circuit.memory_layout.total_width {
            let src = gkr_storage.get_base_layer_mem(i);
            sources.push(src);
        }
        let sources_ref = &sources[..];

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
                    let absolute_row_idx = chunk_start + i;
                    let result = evaluate_memory_query(
                        rel,
                        absolute_row_idx,
                        sources_ref,
                        external_challenges,
                    );

                    dest.get_unchecked_mut(i).write(result);
                }
            },
        );

        destination.assume_init()
    }
}

pub(crate) fn evaluate_linear_relation_at_row<F: PrimeField, E: FieldExtension<F> + Field>(
    rel: &NoFieldLinearRelation,
    gkr_storage: &GKRStorage<F, E>,
    row: usize,
) -> F {
    let mut result = F::from_u32_unchecked(rel.constant);
    for (c, address) in rel.linear_terms.iter() {
        let mut t = gkr_storage
            .try_get_base_poly(*address)
            .expect(&format!("base layer poly at address {:?}", address))[row];
        t.mul_assign(&F::from_u32_unchecked(*c));
        result.add_assign(&t);
    }

    result
}

#[inline(always)]
fn mem_access_fn<F: PrimeField>(
    base_layer_memory_sources: &[&[F]],
    column: usize,
    row: usize,
) -> F {
    unsafe {
        debug_assert!(column < base_layer_memory_sources.len());
        let column = *base_layer_memory_sources.get_unchecked(column);
        debug_assert!(row < column.len());
        *column.get_unchecked(row)
    }
}

pub(crate) fn evaluate_memory_query<F: PrimeField, E: FieldExtension<F> + Field>(
    rel: &NoFieldSpecialMemoryContributionRelation,
    row: usize,
    base_layer_memory_sources: &[&[F]],
    external_challenges: &GKRExternalChallenges<F, E>,
) -> E {
    let mut result = external_challenges.permutation_argument_additive_part;
    match rel.address_space {
        CompiledAddressSpaceRelationStrict::Constant(c) => {
            assert!(c < (1u32 << 16));
            result.add_assign_base(&F::from_u32_unchecked(c));
        }
        CompiledAddressSpaceRelationStrict::Is(offset) => {
            let el = mem_access_fn(base_layer_memory_sources, offset, row);
            debug_assert!(el.is_zero() || el.is_one());
            result.add_assign_base(&el);
        }
        CompiledAddressSpaceRelationStrict::Not(offset) => {
            let mut t = F::ONE;
            let el = mem_access_fn(base_layer_memory_sources, offset, row);
            debug_assert!(el.is_zero() || el.is_one());
            t.sub_assign(&el);
            result.add_assign_base(&t);
        }
    }
    match &rel.address {
        &CompiledAddressStrict::ConstantU16(c) => {
            let mut t = external_challenges.permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            t.mul_assign_by_base(&F::from_u32_unchecked(c as u32));
            result.add_assign(&t);
        }
        &CompiledAddressStrict::Constant(c) => {
            assert!(c < (1u32 << 16));
            let mut t = external_challenges.permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            t.mul_assign_by_base(&F::from_u32_unchecked(c));
            result.add_assign(&t);
        }
        &CompiledAddressStrict::U16Space(offset) => {
            let mut t = external_challenges.permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            let el = mem_access_fn(base_layer_memory_sources, offset, row);
            t.mul_assign_by_base(&el);
            result.add_assign(&t);
        }
        &CompiledAddressStrict::U32Space([low, high]) => {
            for (idx, offset) in [
                (MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX, low),
                (MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX, high),
            ] {
                let mut t = external_challenges.permutation_argument_linearization_challenges[idx];
                let el = mem_access_fn(base_layer_memory_sources, offset, row);
                t.mul_assign_by_base(&el);
                result.add_assign(&t);
            }
        }
        CompiledAddressStrict::U32SpaceGeneric(..) => {
            todo!();
        }
        CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base,
            low_dynamic_offset,
            low_offset,
            high,
        } => {
            let mut low_offset = *low_offset;
            if let Some((c, offset)) = *low_dynamic_offset {
                let t = mem_access_fn(base_layer_memory_sources, offset, row).as_u32_reduced();
                low_offset += t.wrapping_mul(c as u32);
            }
            {
                let mut t = external_challenges.permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                let mut el = mem_access_fn(base_layer_memory_sources, *low_base, row);
                el.add_assign(&F::from_u32_unchecked(low_offset));
                t.mul_assign_by_base(&el);
                result.add_assign(&t);
            }
            {
                let mut t = external_challenges.permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                let el = mem_access_fn(base_layer_memory_sources, *high, row);
                t.mul_assign_by_base(&el);
                result.add_assign(&t);
            }
        }
    }
    // timestamp is a little special as we do add constant offset

    match rel.timestamp {
        CompiledMemoryTimestamp::Zero => {}
        CompiledMemoryTimestamp::Normal(ts) => {
            {
                let mut t = external_challenges.permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                let mut el = mem_access_fn(base_layer_memory_sources, ts[0], row);
                el.add_assign(&F::from_u32_unchecked(rel.timestamp_offset as u32));
                t.mul_assign_by_base(&el);
                result.add_assign(&t);
            }
            {
                let mut t = external_challenges.permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                let el = mem_access_fn(base_layer_memory_sources, ts[1], row);
                t.mul_assign_by_base(&el);
                result.add_assign(&t);
            }
        }
    }
    // and values are simplified for now
    match rel.value {
        RamWordRepresentation::Zero => {
            // nothing
        }
        RamWordRepresentation::U16Limbs(read_value) => {
            for (idx, offset) in [
                (MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX, read_value[0]),
                (MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX, read_value[1]),
            ] {
                let mut t = external_challenges.permutation_argument_linearization_challenges[idx];
                let el = mem_access_fn(base_layer_memory_sources, offset, row);
                t.mul_assign_by_base(&el);
                result.add_assign(&t);
            }
        }
        RamWordRepresentation::U8Limbs(read_value_bytes) => {
            let byte_shift = F::from_u32_unchecked(1u32 << 8);
            for (idx, offset_low, offset_high) in [
                (
                    MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                    read_value_bytes[0],
                    read_value_bytes[1],
                ),
                (
                    MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                    read_value_bytes[2],
                    read_value_bytes[3],
                ),
            ] {
                let mut t = external_challenges.permutation_argument_linearization_challenges[idx];
                let el = mem_access_fn(base_layer_memory_sources, offset_low, row);
                let mut recomposed = mem_access_fn(base_layer_memory_sources, offset_high, row);
                recomposed.mul_assign(&byte_shift);
                recomposed.add_assign(&el);
                t.mul_assign_by_base(&recomposed);
                result.add_assign(&t);
            }
        }
    }

    result
}

pub(crate) fn memory_query_as_flattened_relation<F: PrimeField, E: FieldExtension<F> + Field>(
    rel: &NoFieldSpecialMemoryContributionRelation,
    external_challenges: &GKRExternalChallenges<F, E>,
) -> (BTreeMap<GKRAddress, E>, E) {
    let mut result = BTreeMap::new();
    let mut constant_term = external_challenges.permutation_argument_additive_part;
    // no challenge
    match rel.address_space {
        CompiledAddressSpaceRelationStrict::Constant(c) => {
            assert!(c < (1u32 << 16));
            constant_term.add_assign_base(&F::from_u32_unchecked(c));
        }
        CompiledAddressSpaceRelationStrict::Is(offset) => {
            assert!(result
                .insert(GKRAddress::BaseLayerMemory(offset), E::ONE)
                .is_none());
        }
        CompiledAddressSpaceRelationStrict::Not(offset) => {
            assert!(result
                .insert(GKRAddress::BaseLayerMemory(offset), E::MINUS_ONE)
                .is_none());
            constant_term.add_assign_base(&F::ONE);
        }
    }
    match &rel.address {
        &CompiledAddressStrict::ConstantU16(c) => {
            let mut t = external_challenges.permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            t.mul_assign_by_base(&F::from_u32_unchecked(c as u32));
            constant_term.add_assign(&t);
        }
        &CompiledAddressStrict::Constant(c) => {
            assert!(c < (1u32 << 16));
            let mut t = external_challenges.permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            t.mul_assign_by_base(&F::from_u32_unchecked(c));
            constant_term.add_assign(&t);
        }
        &CompiledAddressStrict::U16Space(offset) => {
            let t = external_challenges.permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            assert!(result
                .insert(GKRAddress::BaseLayerMemory(offset), t)
                .is_none());
        }
        &CompiledAddressStrict::U32Space([low, high]) => {
            for (idx, offset) in [
                (MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX, low),
                (MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX, high),
            ] {
                let t = external_challenges.permutation_argument_linearization_challenges[idx];
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(offset), t)
                    .is_none());
            }
        }
        CompiledAddressStrict::U32SpaceGeneric(..) => {
            todo!();
        }
        CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base,
            low_dynamic_offset,
            low_offset,
            high,
        } => {
            if let Some((c, offset)) = *low_dynamic_offset {
                let mut t = external_challenges.permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                t.mul_assign_by_base(&F::from_u32_unchecked(c as u32));
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(offset), t)
                    .is_none());
            }
            {
                let mut t = external_challenges.permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(*low_base), t)
                    .is_none());
                t.mul_assign_by_base(&F::from_u32_unchecked(*low_offset as u32));
                constant_term.add_assign(&t);
            }
            {
                let t = external_challenges.permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(*high), t)
                    .is_none());
            }
        }
    }
    // timestamp is a little special as we do add constant offset

    match rel.timestamp {
        CompiledMemoryTimestamp::Zero => {}
        CompiledMemoryTimestamp::Normal(ts) => {
            {
                let mut t = external_challenges.permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(ts[0]), t)
                    .is_none());
                t.mul_assign_by_base(&F::from_u32_unchecked(rel.timestamp_offset as u32));
                constant_term.add_assign(&t);
            }
            {
                let t = external_challenges.permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(ts[1]), t)
                    .is_none());
            }
        }
    }
    // and values are simplified for now
    match rel.value {
        RamWordRepresentation::Zero => {
            // nothing
        }
        RamWordRepresentation::U16Limbs(read_value) => {
            for (idx, offset) in [
                (MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX, read_value[0]),
                (MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX, read_value[1]),
            ] {
                let t = external_challenges.permutation_argument_linearization_challenges[idx];
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(offset), t)
                    .is_none());
            }
        }
        RamWordRepresentation::U8Limbs(read_value_bytes) => {
            let byte_shift = F::from_u32_unchecked(1u32 << 8);
            for (idx, offset_low, offset_high) in [
                (
                    MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                    read_value_bytes[0],
                    read_value_bytes[1],
                ),
                (
                    MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                    read_value_bytes[2],
                    read_value_bytes[3],
                ),
            ] {
                let mut t = external_challenges.permutation_argument_linearization_challenges[idx];
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(offset_low), t)
                    .is_none());
                t.mul_assign_by_base(&byte_shift);
                assert!(result
                    .insert(GKRAddress::BaseLayerMemory(offset_high), t)
                    .is_none());
            }
        }
    }

    (result, constant_term)
}

pub(crate) fn single_column_lookup_as_flattened_relation<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const WITH_ADDITIVE_PART: bool,
>(
    rel: &NoFieldSingleColumnLookupRelation,
    lookup_challenges_additive_part: E,
) -> (BTreeMap<GKRAddress, E>, E) {
    let mut result = BTreeMap::new();
    let mut constant_term = E::ZERO;
    if WITH_ADDITIVE_PART {
        constant_term = lookup_challenges_additive_part;
    }

    for (coeff, a) in rel.input.linear_terms.iter() {
        assert!(result
            .insert(*a, E::from_base(F::from_u32_unchecked(*coeff)))
            .is_none());
    }
    constant_term.add_assign_base(&F::from_u32_unchecked(rel.input.constant));

    (result, constant_term)
}

pub(crate) fn vector_lookup_as_flattened_relation<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const WITH_ADDITIVE_PART: bool,
>(
    rel: &NoFieldVectorLookupRelation,
    lookup_challenges_multiplicative_part: E,
    lookup_challenges_additive_part: E,
) -> (BTreeMap<GKRAddress, E>, E) {
    let mut result = BTreeMap::new();
    let mut constant_term = E::ZERO;
    if WITH_ADDITIVE_PART {
        constant_term = lookup_challenges_additive_part;
    }

    let mut challenge = E::ONE;
    for column in rel.columns.iter() {
        for (coeff, a) in column.linear_terms.iter() {
            let mut t = challenge;
            t.mul_assign_by_base(&F::from_u32_unchecked(*coeff));

            assert!(result.insert(*a, t).is_none());
        }
        let mut t = challenge;
        t.mul_assign_by_base(&F::from_u32_unchecked(column.constant));
        constant_term.add_assign(&t);

        challenge.mul_assign(&lookup_challenges_multiplicative_part);
    }

    (result, constant_term)
}
