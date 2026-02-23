use super::*;
use crate::gkr::sumcheck::access_and_fold::BaseFieldPoly;
use crate::{cs::definitions::*, gkr::sumcheck::access_and_fold::ExtensionFieldPoly};
use cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, NoFieldGKRRelation,
};
use cs::{
    definitions::{gkr::DECODER_LOOKUP_FORMAL_SET_INDEX, GKRAddress},
    gkr_compiler::{GKRLayerDescription, NoFieldGKRCacheRelation},
};

pub(crate) mod copy;
pub(crate) mod lookup_from_base_inputs;
pub(crate) mod lookup_from_vector_inputs;
pub(crate) mod lookup_pair;
pub(crate) mod mask_product;
pub(crate) mod pairwise_product;

fn evaluate_cache_relation<F: PrimeField, E: FieldExtension<F> + Field>(
    layer_idx: usize,
    address: GKRAddress,
    relation: &NoFieldGKRCacheRelation,
    gkr_storage: &mut GKRStorage<F, E>,
    external_challenges: &GKRExternalChallenges<F, E>,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    trace_len: usize,
    preprocessed_generic_lookup: &[E],
    lookup_challenges_additive_part: E,
    worker: &Worker,
) {
    assert!(address.is_cache());
    unsafe {
        match relation {
            NoFieldGKRCacheRelation::LongLinear => {
                todo!();
            }
            NoFieldGKRCacheRelation::SingleColumnLookup {
                relation,
                range_check_width,
            } => {
                let mut destination = Box::<[F], Global>::new_uninit_slice(trace_len);
                if *range_check_width == 16 {
                    let source = std::mem::replace(
                        &mut witness_trace.range_check_16_lookup_mapping[relation.lookup_set_index],
                        vec![],
                    );
                    let source_ref = &source;
                    assert_eq!(source.len(), trace_len);
                    apply_row_wise::<_, E>(
                        vec![&mut destination],
                        vec![],
                        trace_len,
                        worker,
                        |dest, _, chunk_start, chunk_size| {
                            assert_eq!(dest.len(), 1);
                            let mut dest = dest;
                            let dest = dest.pop().unwrap();
                            for i in 0..chunk_size {
                                let mapping_index = source_ref[chunk_start + i];
                                let mapped_value = F::from_u32_unchecked(mapping_index as u32);
                                dest[i].write(mapped_value);
                            }
                        },
                    );
                } else if *range_check_width == TIMESTAMP_COLUMNS_NUM_BITS as usize {
                    let source = std::mem::replace(
                        &mut witness_trace.timestamp_range_check_lookup_mapping
                            [relation.lookup_set_index],
                        vec![],
                    );
                    let source_ref = &source;
                    assert_eq!(source.len(), trace_len);
                    apply_row_wise::<_, E>(
                        vec![&mut destination],
                        vec![],
                        trace_len,
                        worker,
                        |dest, _, chunk_start, chunk_size| {
                            assert_eq!(dest.len(), 1);
                            let mut dest = dest;
                            let dest = dest.pop().unwrap();
                            for i in 0..chunk_size {
                                let mapping_index = source_ref[chunk_start + i];
                                let mapped_value = F::from_u32_unchecked(mapping_index);
                                dest[i].write(mapped_value);
                            }
                        },
                    );
                } else {
                    unreachable!(
                        "unknown single column lookup range check of width {}",
                        range_check_width
                    );
                };

                let destination = destination.assume_init();
                assert_eq!(layer_idx, 0);
                gkr_storage.insert_base_field_at_layer(0, address, BaseFieldPoly::new(destination));
            }
            NoFieldGKRCacheRelation::MemoryTuple(rel) => {
                let mut destination = Box::<[E], Global>::new_uninit_slice(trace_len);
                let ext_destination = vec![&mut destination[..]];
                let src_ref = &*gkr_storage;
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
                            let mut result = external_challenges.permutation_argument_additive_part;
                            match rel.address_space {
                                CompiledAddressSpaceRelationStrict::Constant(c) => {
                                    assert!(c < (1u32 << 16));
                                    result.add_assign_base(&F::from_u32_unchecked(c));
                                }
                                CompiledAddressSpaceRelationStrict::Is(offset) => {
                                    let el = src_ref
                                        .get_base_layer_mem(offset)
                                        .get_unchecked(chunk_start + i);
                                    debug_assert!(el.is_zero() || el.is_one());
                                    result.add_assign_base(el);
                                }
                                CompiledAddressSpaceRelationStrict::Not(offset) => {
                                    let mut t = F::ONE;
                                    let el = src_ref
                                        .get_base_layer_mem(offset)
                                        .get_unchecked(chunk_start + i);
                                    debug_assert!(el.is_zero() || el.is_one());
                                    t.sub_assign(el);
                                    result.add_assign_base(&t);
                                }
                            }
                            match &rel.address {
                                &CompiledAddressStrict::Constant(c) => {
                                    assert!(c < (1u32 << 16));
                                    let mut t = external_challenges
                                        .permutation_argument_linearization_challenges
                                        [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                                    t.mul_assign_by_base(&F::from_u32_unchecked(c));
                                    result.add_assign(&t);
                                }
                                &CompiledAddressStrict::U16Space(offset) => {
                                    let mut t = external_challenges
                                        .permutation_argument_linearization_challenges
                                        [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                                    let el = src_ref
                                        .get_base_layer_mem(offset)
                                        .get_unchecked(chunk_start + i);
                                    t.mul_assign_by_base(el);
                                    result.add_assign(&t);
                                }
                                &CompiledAddressStrict::U32Space([low, high]) => {
                                    for (idx, offset) in [
                                        (MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX, low),
                                        (MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX, high),
                                    ] {
                                        let mut t = external_challenges
                                            .permutation_argument_linearization_challenges[idx];
                                        let el = src_ref
                                            .get_base_layer_mem(offset)
                                            .get_unchecked(chunk_start + i);
                                        t.mul_assign_by_base(el);
                                        result.add_assign(&t);
                                    }
                                }
                                CompiledAddressStrict::U32SpaceGeneric([low, high]) => {
                                    todo!();
                                }
                                CompiledAddressStrict::U32SpaceSpecialIndirect {
                                    low_base,
                                    low_dynamic_offset,
                                    low_offset,
                                    high,
                                } => {
                                    todo!();
                                }
                            }
                            // timestamp is a little special as we do add constant offset
                            {
                                let mut t = external_challenges
                                    .permutation_argument_linearization_challenges
                                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                                let mut el = *src_ref
                                    .get_base_layer_mem(rel.timestamp[0])
                                    .get_unchecked(chunk_start + i);
                                el.add_assign(&F::from_u32_unchecked(rel.timestamp_offset as u32));
                                t.mul_assign_by_base(&el);
                                result.add_assign(&t);
                            }
                            {
                                let mut t = external_challenges
                                    .permutation_argument_linearization_challenges
                                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                                let el = src_ref
                                    .get_base_layer_mem(rel.timestamp[1])
                                    .get_unchecked(chunk_start + i);
                                t.mul_assign_by_base(el);
                                result.add_assign(&t);
                            }
                            // and values are simplified for now
                            for (idx, offset) in [
                                (MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX, rel.value[0]),
                                (MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX, rel.value[1]),
                            ] {
                                let mut t = external_challenges
                                    .permutation_argument_linearization_challenges[idx];
                                let el = src_ref
                                    .get_base_layer_mem(offset)
                                    .get_unchecked(chunk_start + i);
                                t.mul_assign_by_base(el);
                                result.add_assign(&t);
                            }
                            dest.get_unchecked_mut(i).write(result);
                        }
                    },
                );
                let destination = destination.assume_init();
                assert_eq!(layer_idx, 0);
                gkr_storage.insert_extension_at_layer(
                    0,
                    address,
                    ExtensionFieldPoly::new(destination),
                );
            }
            NoFieldGKRCacheRelation::VectorizedLookup(rel) => {
                // println!("Evaluating vectorized lookup cache relation {:?}", rel);

                // we materialize it, but the good thing is that we have a cache of lookups
                let lookup_set_index = rel.lookup_set_index;
                let mut destination = Box::<[E], Global>::new_uninit_slice(trace_len);
                let ext_destination = vec![&mut destination[..]];
                let mapping_ref = if lookup_set_index != DECODER_LOOKUP_FORMAL_SET_INDEX {
                    // println!("Mapping lookup access number {}", lookup_set_index);
                    assert!(lookup_set_index < witness_trace.generic_lookup_mapping.len() - 1);
                    &witness_trace.generic_lookup_mapping[lookup_set_index]
                } else {
                    // println!("Mapping decoder lookup");
                    assert!(witness_trace.generic_lookup_mapping.len() > 0);
                    witness_trace.generic_lookup_mapping.last().unwrap()
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
                            let mapping_index = mapping_ref[chunk_start + i];
                            let mapped_value = preprocessed_generic_lookup[mapping_index as usize];
                            dest[i].write(mapped_value);
                        }
                    },
                );
                let destination = destination.assume_init();
                assert_eq!(layer_idx, 0);
                gkr_storage.insert_extension_at_layer(
                    0,
                    address,
                    ExtensionFieldPoly::new(destination),
                );
            }
            NoFieldGKRCacheRelation::VectorizedLookupSetup(_rel) => {
                let mut destination = Box::<[E], Global>::new_uninit_slice(trace_len);
                destination[..preprocessed_generic_lookup.len()]
                    .write_copy_of_slice(preprocessed_generic_lookup);
                let _ = destination[preprocessed_generic_lookup.len()..]
                    .write_filled(lookup_challenges_additive_part);
                let destination = destination.assume_init();
                assert_eq!(layer_idx, 0);
                gkr_storage.insert_extension_at_layer(
                    0,
                    address,
                    ExtensionFieldPoly::new(destination),
                );
            }
        }
    }
}

pub fn evaluate_layer<F: PrimeField, E: FieldExtension<F> + Field>(
    layer_idx: usize,
    layer: &GKRLayerDescription,
    gkr_storage: &mut GKRStorage<F, E>,
    compiled_circuit: &GKRCircuitArtifact<F>,
    external_challenges: &GKRExternalChallenges<F, E>,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    trace_len: usize,
    preprocessed_generic_lookup: &[E],
    lookup_challenges_additive_part: E,
    _constraints_batch_challenge: E,
    worker: &Worker,
) {
    println!("Evaluating layer {} in forward direction", layer_idx);

    if layer_idx == 0 {
        // move base field polys
        for (i, poly) in witness_trace
            .column_major_memory_trace
            .drain(..)
            .into_iter()
            .enumerate()
        {
            gkr_storage.insert_base_field_at_layer(
                0,
                GKRAddress::BaseLayerMemory(i),
                BaseFieldPoly::new(poly.into_boxed_slice()),
            );
        }
        for (i, poly) in witness_trace
            .column_major_witness_trace
            .drain(..)
            .into_iter()
            .enumerate()
        {
            gkr_storage.insert_base_field_at_layer(
                0,
                GKRAddress::BaseLayerWitness(i),
                BaseFieldPoly::new(poly.into_boxed_slice()),
            );
        }
    }

    // first we compute caches
    for (addr, cache_relation) in layer.cached_relations.iter() {
        // println!(
        //     "Computing cache relation {:?} for output {:?}",
        //     cache_relation, addr
        // );

        addr.assert_as_layer(layer_idx);
        evaluate_cache_relation(
            layer_idx,
            *addr,
            cache_relation,
            gkr_storage,
            external_challenges,
            witness_trace,
            trace_len,
            preprocessed_generic_lookup,
            lookup_challenges_additive_part,
            worker,
        );
    }

    let expected_output_layer = layer_idx + 1;
    assert!(layer.gates.is_empty() ^ layer.gates_with_external_connections.is_empty());
    if layer_idx != compiled_circuit.layers.len() - 1 {
        assert!(layer.gates_with_external_connections.is_empty());
    } else {
        assert!(layer.gates.is_empty());
    }

    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        assert_eq!(gate.output_layer, expected_output_layer);

        // println!("Should evaluate {:?}", &gate.enforced_relation);

        // let now = std::time::Instant::now();
        match &gate.enforced_relation {
            NoFieldGKRRelation::Copy { input, output } => {
                // println!("Should evaluate {:?}", &gate.enforced_relation);
                copy::forward_evaluate_copy(
                    *input,
                    *output,
                    gkr_storage,
                    expected_output_layer,
                    trace_len,
                    worker,
                );
            }
            NoFieldGKRRelation::InitialGrandProductFromCaches { input, output } => {
                // println!("Should evaluate {:?}", &gate.enforced_relation);
                pairwise_product::forward_evaluate_pairwise_product(
                    *input,
                    *output,
                    gkr_storage,
                    expected_output_layer,
                    trace_len,
                    worker,
                );
            }
            NoFieldGKRRelation::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                // println!("Should evaluate {:?}", &gate.enforced_relation);
                mask_product::forward_evaluate_mask_into_identity(
                    *input,
                    *mask,
                    *output,
                    gkr_storage,
                    expected_output_layer,
                    trace_len,
                    worker,
                );
            }
            NoFieldGKRRelation::TrivialProduct { input, output } => {
                // println!("Should evaluate {:?}", &gate.enforced_relation);
                pairwise_product::forward_evaluate_pairwise_product(
                    *input,
                    *output,
                    gkr_storage,
                    expected_output_layer,
                    trace_len,
                    worker,
                );
            }
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { .. } => {
                // we do nothing as it should result in all zeroes in case if constraints are satisfied
            }
            NoFieldGKRRelation::LookupFromBaseInputsWithSetup { .. } => {
                unimplemented!("not used");
            }
            NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {
                // println!("Should evaluate {:?}", &gate.enforced_relation);
                lookup_from_base_inputs::forward_evaluate_lookup_from_base_inputs_with_setup(
                    *input,
                    *setup,
                    *output,
                    gkr_storage,
                    expected_output_layer,
                    trace_len,
                    lookup_challenges_additive_part,
                    worker,
                );
            }
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, output } => {
                // println!("Should evaluate {:?}", &gate.enforced_relation);
                lookup_from_base_inputs::forward_evaluate_lookup_base_inputs_pair(
                    *input,
                    *output,
                    gkr_storage,
                    expected_output_layer,
                    trace_len,
                    lookup_challenges_additive_part,
                    worker,
                );
            }
            NoFieldGKRRelation::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                // println!("Should evaluate {:?}", &gate.enforced_relation);
                lookup_from_vector_inputs::forward_evaluate_masked_lookup_from_vector_inputs_with_setup(*input, *setup, *output, gkr_storage, expected_output_layer, trace_len, worker);
            }
            NoFieldGKRRelation::LookupPair { input, output } => {
                // println!("Should evaluate {:?}", &gate.enforced_relation);
                lookup_pair::forward_evaluate_lookup_pair(
                    *input,
                    *output,
                    gkr_storage,
                    expected_output_layer,
                    trace_len,
                    worker,
                );
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                // println!("Should evaluate {:?}", &gate.enforced_relation);
                lookup_from_base_inputs::forward_evaluate_lookup_rational_with_base_remainder_input(
                    *input,
                    *remainder,
                    *output,
                    gkr_storage,
                    expected_output_layer,
                    trace_len,
                    lookup_challenges_additive_part,
                    worker,
                );
            }
            rel @ _ => {
                println!("Should evaluate {:?}", rel);
            }
        }
        // println!(
        //     "Evaluating {:?} took {:?}",
        //     &gate.enforced_relation,
        //     now.elapsed()
        // );
    }
}
