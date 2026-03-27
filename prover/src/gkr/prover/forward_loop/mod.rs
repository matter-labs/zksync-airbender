use super::*;
use crate::gkr::prover::forward_loop::utils::evaluate_linear_relation_at_row;
use crate::gkr::sumcheck::access_and_fold::BaseFieldPoly;
use crate::{cs::definitions::*, gkr::sumcheck::access_and_fold::ExtensionFieldPoly};
use cs::definitions::gkr::RamWordRepresentation;
use cs::gkr_compiler::CompiledMemoryTimestamp;
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
pub(crate) mod utils;

fn evaluate_cache_relation<F: PrimeField, E: FieldExtension<F> + Field>(
    layer_idx: usize,
    address: GKRAddress,
    relation: &NoFieldGKRCacheRelation,
    gkr_storage: &mut GKRStorage<F, E>,
    external_challenges: &GKRExternalChallenges<F, E>,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    trace_len: usize,
    lookup_challenges_multiplicative_part: E,
    decoder_lookup_fill_value: E,
    preprocessed_generic_lookup: &[E],
    offset_for_decoder_table: u32,
    decoder_predicate_address: GKRAddress,
    worker: &Worker,
) {
    assert!(address.is_cache());
    unsafe {
        match relation {
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
                                let row = chunk_start + i;
                                let mapping_index = source_ref[row];

                                #[cfg(feature = "gkr_self_checks")]
                                {
                                    let value = evaluate_linear_relation_at_row(
                                        &relation.input,
                                        &*gkr_storage,
                                        row,
                                    )
                                    .as_u32_reduced();
                                    assert!(value < 1 << 16, "range check 16 bits: value is {} at row {} for relation {:?}", value, row, relation);
                                    assert_eq!(value as u16, mapping_index);
                                }

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
                                let row = chunk_start + i;
                                let mapping_index = source_ref[row];

                                #[cfg(feature = "gkr_self_checks")]
                                {
                                    let value = evaluate_linear_relation_at_row(
                                        &relation.input,
                                        &*gkr_storage,
                                        row,
                                    )
                                    .as_u32_reduced();
                                    assert!(value < 1 << TIMESTAMP_COLUMNS_NUM_BITS, "timestamp range check: value is {} at row {} for relation {:?}", value, row, relation);
                                    assert_eq!(value, mapping_index);
                                }

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
                address.assert_as_layer(layer_idx);
                gkr_storage.insert_base_field_at_layer(
                    layer_idx,
                    address,
                    BaseFieldPoly::new(destination),
                );
            }
            NoFieldGKRCacheRelation::MemoryTuple(rel) => {
                let mut destination = Box::<[E], Global>::new_uninit_slice(trace_len);
                let ext_destination = vec![&mut destination[..]];
                let src_ref = &*gkr_storage;
                let byte_shift = F::from_u32_unchecked(1u32 << 8);
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
                                &CompiledAddressStrict::ConstantU16(c) => {
                                    let mut t = external_challenges
                                        .permutation_argument_linearization_challenges
                                        [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                                    t.mul_assign_by_base(&F::from_u32_unchecked(c as u32));
                                    result.add_assign(&t);
                                }
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
                                        let t = src_ref
                                            .get_base_layer_mem(offset)
                                            .get_unchecked(chunk_start + i)
                                            .as_u32_reduced();
                                        low_offset += t.wrapping_mul(c as u32);
                                    }
                                    {
                                        let mut t = external_challenges
                                            .permutation_argument_linearization_challenges
                                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                                        let mut el = *src_ref
                                            .get_base_layer_mem(*low_base)
                                            .get_unchecked(chunk_start + i);
                                        el.add_assign(&F::from_u32_unchecked(low_offset));
                                        t.mul_assign_by_base(&el);
                                        result.add_assign(&t);
                                    }
                                    {
                                        let mut t = external_challenges
                                            .permutation_argument_linearization_challenges
                                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                                        let el = src_ref
                                            .get_base_layer_mem(*high)
                                            .get_unchecked(chunk_start + i);
                                        t.mul_assign_by_base(el);
                                        result.add_assign(&t);
                                    }
                                }
                            }
                            // timestamp is a little special as we do add constant offset

                            match rel.timestamp {
                                CompiledMemoryTimestamp::Zero => {}
                                CompiledMemoryTimestamp::Normal(ts) => {
                                    {
                                        let mut t = external_challenges
                                            .permutation_argument_linearization_challenges
                                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                                        let mut el = *src_ref
                                            .get_base_layer_mem(ts[0])
                                            .get_unchecked(chunk_start + i);
                                        el.add_assign(&F::from_u32_unchecked(
                                            rel.timestamp_offset as u32,
                                        ));
                                        t.mul_assign_by_base(&el);
                                        result.add_assign(&t);
                                    }
                                    {
                                        let mut t = external_challenges
                                            .permutation_argument_linearization_challenges
                                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                                        let el = src_ref
                                            .get_base_layer_mem(ts[1])
                                            .get_unchecked(chunk_start + i);
                                        t.mul_assign_by_base(el);
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
                                        (
                                            MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                                            read_value[0],
                                        ),
                                        (
                                            MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                                            read_value[1],
                                        ),
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
                                RamWordRepresentation::U8Limbs(read_value_bytes) => {
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
                                        let mut t = external_challenges
                                            .permutation_argument_linearization_challenges[idx];
                                        let el = src_ref
                                            .get_base_layer_mem(offset_low)
                                            .get_unchecked(chunk_start + i);
                                        let mut recomposed = *src_ref
                                            .get_base_layer_mem(offset_high)
                                            .get_unchecked(chunk_start + i);
                                        recomposed.mul_assign(&byte_shift);
                                        recomposed.add_assign(el);
                                        t.mul_assign_by_base(&recomposed);
                                        result.add_assign(&t);
                                    }
                                }
                            }

                            dest.get_unchecked_mut(i).write(result);
                        }
                    },
                );
                let destination = destination.assume_init();
                assert_eq!(layer_idx, 0);
                address.assert_as_layer(layer_idx);
                gkr_storage.insert_extension_at_layer(
                    layer_idx,
                    address,
                    ExtensionFieldPoly::new(destination),
                );
            }
            NoFieldGKRCacheRelation::VectorizedLookup(rel) => {
                let destination = utils::materialize_vector_lookup_input(
                    rel,
                    &*gkr_storage,
                    witness_trace,
                    trace_len,
                    preprocessed_generic_lookup,
                    lookup_challenges_multiplicative_part,
                    decoder_lookup_fill_value,
                    offset_for_decoder_table,
                    decoder_predicate_address,
                    worker,
                );
                address.assert_as_layer(layer_idx);
                gkr_storage.insert_extension_at_layer(
                    layer_idx,
                    address,
                    ExtensionFieldPoly::new(destination),
                );
            }
            NoFieldGKRCacheRelation::VectorizedLookupSetup(_rel) => {
                let mut destination = Box::<[E], Global>::new_uninit_slice(trace_len);
                destination[..preprocessed_generic_lookup.len()]
                    .write_copy_of_slice(preprocessed_generic_lookup);
                let _ = destination[preprocessed_generic_lookup.len()..].write_filled(E::ZERO);
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
    lookup_challenges_multiplicative_part: E,
    lookup_challenges_additive_part: E,
    decoder_lookup_fill_value: E,
    _constraints_batch_challenge: E,
    worker: &Worker,
) {
    println!("Evaluating layer {} in forward direction", layer_idx);
    assert_eq!(
        compiled_circuit.scratch_space_mapping.len(),
        compiled_circuit.scratch_space_mapping_rev.len()
    );

    let decoder_predicate_address = if let Some(t) = compiled_circuit.memory_layout.machine_state {
        GKRAddress::BaseLayerMemory(t.execute)
    } else {
        GKRAddress::BaseLayerMemory(usize::MAX)
    };

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
    } else {
        // we can still get some intermediate polys already computed and form
        // the scratch space, and we will insert them here
        for (i, poly) in witness_trace
            .column_major_scratch_space_trace
            .iter_mut()
            .enumerate()
        {
            if let Some(place) = compiled_circuit.scratch_space_mapping_rev.get(&i) {
                if let GKRAddress::InnerLayer { layer, .. } = *place {
                    if layer == layer_idx {
                        assert!(
                            poly.is_empty() == false,
                            "trying to fill {:?} from scratch space, but it's source is empty",
                            place
                        );
                        if gkr_storage.try_get_base_poly(*place).is_none() {
                            // some Copy relations could already fill it
                            let poly = core::mem::replace(poly, vec![]);
                            gkr_storage.insert_base_field_at_layer(
                                layer_idx,
                                *place,
                                BaseFieldPoly::new(poly.into_boxed_slice()),
                            );
                            println!("Filled intermediate poly {:?} from scratch space", place);
                        }
                    }
                }
            }
        }
    }

    // we split forward computation between gates that may be needed for cache relations self-checks,
    // and all others that can use caches in them

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
                copy::forward_evaluate_copy::<F, E, false>(
                    *input,
                    *output,
                    gkr_storage,
                    expected_output_layer,
                    trace_len,
                    worker,
                );
            }
            NoFieldGKRRelation::MaxQuadratic { input, output } => {
                if compiled_circuit.scratch_space_mapping.contains_key(output) {
                    // a value of it will be filled from scratch space in the next round
                } else {
                    println!("Need to evaluate {:?} -> {:?}", input, output);
                    todo!();
                }
            }
            NoFieldGKRRelation::MaterializedVectorLookupInput { input, output } => {
                let value = utils::materialize_vector_lookup_input(
                    input,
                    &*gkr_storage,
                    witness_trace,
                    trace_len,
                    preprocessed_generic_lookup,
                    lookup_challenges_multiplicative_part,
                    decoder_lookup_fill_value,
                    compiled_circuit.offset_for_decoder_table as u32,
                    decoder_predicate_address,
                    worker,
                );
                output.assert_as_layer(expected_output_layer);
                gkr_storage.insert_extension_at_layer(
                    expected_output_layer,
                    *output,
                    ExtensionFieldPoly::new(value),
                );
            }
            _ => {
                // skip
            }
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
            lookup_challenges_multiplicative_part,
            decoder_lookup_fill_value,
            preprocessed_generic_lookup,
            compiled_circuit.offset_for_decoder_table as u32,
            decoder_predicate_address,
            worker,
        );
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
                // even though it's handled above, we may need to copy cache relation to the
                // next layer after making it, so we try again, but infailable option
                copy::forward_evaluate_copy::<F, E, true>(
                    *input,
                    *output,
                    gkr_storage,
                    expected_output_layer,
                    trace_len,
                    worker,
                );
            }
            NoFieldGKRRelation::MaxQuadratic { .. } => {
                // handled above
            }
            NoFieldGKRRelation::MaterializedVectorLookupInput { .. } => {
                // handled above
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
            NoFieldGKRRelation::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                // println!("Should evaluate {:?}", &gate.enforced_relation);
                lookup_from_vector_inputs::forward_evaluate_masked_lookup_from_vector_inputs_with_setup(*input, *setup, *output, gkr_storage, expected_output_layer, trace_len, lookup_challenges_additive_part, worker);
            }
            NoFieldGKRRelation::AggregateLookupRationalPair { input, output } => {
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
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs {
                input,
                remainder,
                output,
            } => {
                // println!("Should evaluate {:?}", &gate.enforced_relation);
                lookup_from_vector_inputs::forward_evaluate_lookup_rational_with_vector_remainder_input(
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
            NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs { input, output } => {
                // println!("Should evaluate {:?}", &gate.enforced_relation);
                lookup_from_vector_inputs::forward_evaluate_lookup_from_vector_inputs_pair(
                    *input,
                    *output,
                    gkr_storage,
                    expected_output_layer,
                    trace_len,
                    lookup_challenges_additive_part,
                    worker,
                );
            }
            NoFieldGKRRelation::LookupFromMaterializedVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                lookup_from_vector_inputs::forward_evaluate_lookup_from_vector_inputs_with_setup(
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
            rel @ _ => {
                panic!("Should evaluate {:?}", rel);
            }
        }
    }
}
