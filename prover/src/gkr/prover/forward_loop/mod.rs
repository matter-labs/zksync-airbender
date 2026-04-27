use super::*;
use crate::gkr::prover::forward_loop::utils::{
    evaluate_linear_relation_at_row, evaluate_memory_query,
};
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
pub(crate) mod inits_and_teardowns;
pub(crate) mod lookup_from_base_inputs;
pub(crate) mod lookup_from_vector_inputs;
pub(crate) mod lookup_pair;
pub(crate) mod mask_product;
pub(crate) mod pairwise_product;
pub(crate) mod single_column_lookup;
pub(crate) mod utils;
pub(crate) mod vector_lookup;

fn evaluate_cache_relation<F: PrimeField, E: FieldExtension<F> + Field>(
    layer_idx: usize,
    address: GKRAddress,
    relation: &NoFieldGKRCacheRelation,
    gkr_storage: &mut GKRStorage<F, E>,
    external_challenges: &GKRExternalChallenges<F, E>,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    compiled_circuit: &GKRCircuitArtifact<F>,
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
                single_column_lookup::evaluate_single_column_lookup_relation(
                    layer_idx,
                    address,
                    relation,
                    *range_check_width as u32,
                    gkr_storage,
                    witness_trace,
                    trace_len,
                    worker,
                );
            }
            NoFieldGKRCacheRelation::MemoryTuple(rel) => {
                let destination = utils::materialize_memory_tuple(
                    rel,
                    &*gkr_storage,
                    trace_len,
                    external_challenges,
                    compiled_circuit,
                    worker,
                );
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
    inits_and_teardowns_top_bits: &[u32],
    trace_len: usize,
    preprocessed_generic_lookup: &[E],
    lookup_challenges_multiplicative_part: E,
    lookup_challenges_additive_part: E,
    decoder_lookup_fill_value: E,
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
        assert_eq!(
            gate.output_layer, expected_output_layer,
            "Unexpected output layer for gate {:?}",
            gate
        );

        // println!("Should evaluate {:?}", &gate.enforced_relation);

        // let now = std::time::Instant::now();
        match &gate.enforced_relation {
            NoFieldGKRRelation::CopyInBaseField { input, output }
            | NoFieldGKRRelation::CopyInExtensionField { input, output } => {
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
            compiled_circuit,
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
            NoFieldGKRRelation::CopyInBaseField { input, output }
            | NoFieldGKRRelation::CopyInExtensionField { input, output } => {
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

            NoFieldGKRRelation::MaterializeSingleLookupInput {
                input,
                output,
                range_check_width,
            } => {
                single_column_lookup::evaluate_single_column_lookup_relation(
                    expected_output_layer,
                    *output,
                    input,
                    *range_check_width as u32,
                    gkr_storage,
                    witness_trace,
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
            NoFieldGKRRelation::InitialGrandProductWithoutCaches { input, output } => {
                // println!("Should evaluate {:?}", &gate.enforced_relation);
                pairwise_product::forward_evaluate_base_layer_pairwise_product_without_caches(
                    input,
                    *output,
                    gkr_storage,
                    external_challenges,
                    expected_output_layer,
                    compiled_circuit,
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
            NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { .. } => {
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
            NoFieldGKRRelation::LookupWithDensAndSetupExpressions {
                input,
                setup,
                output,
            } => {
                assert_eq!(input.0, decoder_predicate_address);
                vector_lookup::materialize_decoder_lookup_minus_setup(
                    input.0,
                    &input.1,
                    setup.0,
                    *output,
                    gkr_storage,
                    witness_trace,
                    trace_len,
                    preprocessed_generic_lookup,
                    lookup_challenges_multiplicative_part,
                    lookup_challenges_additive_part,
                    decoder_lookup_fill_value,
                    compiled_circuit.offset_for_decoder_table as u32,
                    worker,
                );
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
            NoFieldGKRRelation::LookupPairFromBaseInputs {
                input,
                output,
                range_check_width,
            } => {
                if *range_check_width == 16 {
                    lookup_from_base_inputs::forward_evaluate_lookup_base_inputs_pair_range_check_16(
                        input,
                        *output,
                        gkr_storage,
                        expected_output_layer,
                        trace_len,
                        lookup_challenges_additive_part,
                        witness_trace,
                        worker
                    );
                } else if *range_check_width == TIMESTAMP_COLUMNS_NUM_BITS {
                    lookup_from_base_inputs::forward_evaluate_lookup_base_inputs_pair_timestamp_range_check(
                        input,
                        *output,
                        gkr_storage,
                        expected_output_layer,
                        trace_len,
                        lookup_challenges_additive_part,
                        witness_trace,
                        worker
                    );
                } else {
                    unreachable!(
                        "unknown single column lookup range check of width {}",
                        range_check_width
                    );
                }
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
            NoFieldGKRRelation::LookupPairFromVectorInputs { input, output } => {
                vector_lookup::materialize_lookup_expressions_pair(
                    input,
                    *output,
                    gkr_storage,
                    witness_trace,
                    expected_output_layer,
                    trace_len,
                    preprocessed_generic_lookup,
                    lookup_challenges_multiplicative_part,
                    lookup_challenges_additive_part,
                    compiled_circuit.offset_for_decoder_table as u32,
                    worker,
                );
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs {
                input,
                remainder,
                output,
            } => {
                vector_lookup::materialize_lookup_expressions_pair_with_remainder(
                    *input,
                    remainder,
                    *output,
                    gkr_storage,
                    witness_trace,
                    expected_output_layer,
                    trace_len,
                    preprocessed_generic_lookup,
                    lookup_challenges_multiplicative_part,
                    lookup_challenges_additive_part,
                    compiled_circuit.offset_for_decoder_table as u32,
                    worker,
                );
            }
            NoFieldGKRRelation::LookupFromVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                vector_lookup::materialize_lookup_expression_minus_setup(
                    input,
                    setup.0,
                    *output,
                    gkr_storage,
                    witness_trace,
                    trace_len,
                    preprocessed_generic_lookup,
                    lookup_challenges_multiplicative_part,
                    lookup_challenges_additive_part,
                    compiled_circuit.offset_for_decoder_table as u32,
                    worker,
                );
            }
            NoFieldGKRRelation::MaterializeGrandProductTermExpression { input, output } => {
                let destination = utils::materialize_memory_tuple(
                    input,
                    &*gkr_storage,
                    trace_len,
                    external_challenges,
                    compiled_circuit,
                    worker,
                );
                assert_eq!(expected_output_layer, 1);
                output.assert_as_layer(expected_output_layer);
                gkr_storage.insert_extension_at_layer(
                    expected_output_layer,
                    *output,
                    ExtensionFieldPoly::new(destination),
                );
            }
            NoFieldGKRRelation::InitsOrTeardownsInitialPair {
                timestamp_and_value,
                setup,
                output,
                set_idxes,
            } => {
                let destination =
                    inits_and_teardowns::materialize_inits_and_teardowns_tuple_pair::<F, E, 2>(
                        timestamp_and_value,
                        set_idxes.map(|el| inits_and_teardowns_top_bits[el]),
                        &*gkr_storage,
                        trace_len,
                        external_challenges,
                        compiled_circuit,
                        worker,
                    );
                assert_eq!(expected_output_layer, 1);
                output.assert_as_layer(expected_output_layer);
                gkr_storage.insert_extension_at_layer(
                    expected_output_layer,
                    *output,
                    ExtensionFieldPoly::new(destination),
                );
            }
            rel @ _ => {
                panic!("Should evaluate {:?}", rel);
            }
        }
    }
}
