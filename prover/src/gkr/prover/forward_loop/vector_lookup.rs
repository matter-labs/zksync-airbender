use cs::definitions::gkr::NoFieldVectorLookupRelation;

use super::*;

pub(crate) fn materialize_decoder_lookup_minus_setup<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    decoder_predicate_address: GKRAddress,
    decoder_relation: &NoFieldVectorLookupRelation,
    multiplicity_address: GKRAddress,
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    trace_len: usize,
    preprocessed_generic_lookup: &[E],
    lookup_challenges_multiplicative_part: E,
    lookup_challenges_additive_part: E,
    decoder_lookup_fill_value: E,
    offset_for_decoder_table: u32,
    worker: &Worker,
) {
    assert_eq!(
        decoder_relation.lookup_set_index,
        DECODER_LOOKUP_FORMAL_SET_INDEX
    );
    let mut num_destination = Box::<[E], Global>::new_uninit_slice(trace_len);
    let mut den_destination = Box::<[E], Global>::new_uninit_slice(trace_len);
    let mapping_ref = {
        assert!(witness_trace.generic_lookup_mapping.len() > 0);
        witness_trace.generic_lookup_mapping.pop().unwrap()
    };
    assert!(mapping_ref.len() > 0);
    let decoder_predicate = gkr_storage.get_base_layer(decoder_predicate_address);
    let multiplicity = gkr_storage.get_base_layer(multiplicity_address);

    apply_row_wise::<F, _>(
        vec![],
        vec![&mut num_destination, &mut den_destination],
        trace_len,
        worker,
        |_, ext_dest, chunk_start, chunk_size| {
            assert_eq!(ext_dest.len(), 2);
            let [num_dest, den_dest] = ext_dest.try_into().unwrap();
            for i in 0..chunk_size {
                let row = chunk_start + i;
                let mapping_index = mapping_ref[row];
                let decoder_predicate = decoder_predicate[row];
                let decoder_mask_value = decoder_predicate.as_boolean();
                let mapped_value = if decoder_mask_value {
                    preprocessed_generic_lookup[mapping_index as usize]
                } else {
                    decoder_lookup_fill_value
                };

                let multiplicity_value = multiplicity[row];
                let setup_value = preprocessed_generic_lookup
                    .get(row)
                    .copied()
                    .unwrap_or(E::ZERO);

                // a/(b + gamma) - c/(d + gamma) -> (a*(d+gamma) - c*(b+gamma)), (b+gamma) * (d+gamma)

                let mut b = mapped_value;
                b.add_assign(&lookup_challenges_additive_part);

                let mut d = setup_value;
                d.add_assign(&lookup_challenges_additive_part);

                let mut num = d;
                num.mul_assign_by_base(&decoder_predicate);

                let mut t = b;
                t.mul_assign_by_base(&multiplicity_value);

                num.sub_assign(&t);

                let mut den = b;
                den.mul_assign(&d);

                num_dest[i].write(num);
                den_dest[i].write(den);

                #[cfg(feature = "gkr_self_checks")]
                {
                    if decoder_mask_value {
                        assert!(mapping_index >= offset_for_decoder_table, "decoder lookup should have mapping index {} >= decoder table offset {}, and is not zero in padding", mapping_index, offset_for_decoder_table);
                    } else {
                        assert_eq!(
                            mapping_index, 0,
                            "decoder lookup should have mapping index zero in padding"
                        );
                    }

                    let naive_eval = {
                        let mut result = E::from_base(evaluate_linear_relation_at_row(
                            &decoder_relation.columns[0],
                            gkr_storage,
                            row,
                        ));
                        let mut challenge = lookup_challenges_multiplicative_part;
                        for rel in decoder_relation.columns[1..].iter() {
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

                    if decoder_mask_value {
                        if naive_eval != mapped_value {
                            for (idx, rel) in decoder_relation.columns.iter().enumerate() {
                                let v = evaluate_linear_relation_at_row(rel, gkr_storage, row);
                                println!("Column {} = {}", idx, v);
                            }
                        }
                        assert_eq!(
                            naive_eval, mapped_value,
                            "decoder lookup diverged at row {} for relation {:?}",
                            row, decoder_relation
                        );
                    } else {
                        if naive_eval != decoder_lookup_fill_value {
                            for (idx, rel) in decoder_relation.columns.iter().enumerate() {
                                let v = evaluate_linear_relation_at_row(rel, gkr_storage, row);
                                println!("Column {} = {}", idx, v);
                            }
                        }
                        assert_eq!(
                            naive_eval, decoder_lookup_fill_value,
                            "decoder lookup diverged at filling row {} for relation {:?}",
                            row, decoder_relation
                        );
                    }
                }
            }
        },
    );

    for (output, destination) in outputs
        .into_iter()
        .zip([num_destination, den_destination].into_iter())
    {
        let destination = unsafe { destination.assume_init() };
        output.assert_as_layer(1);
        gkr_storage.insert_extension_at_layer(1, output, ExtensionFieldPoly::new(destination));
    }
}

pub(crate) fn materialize_lookup_expressions_pair<F: PrimeField, E: FieldExtension<F> + Field>(
    inputs: &[NoFieldVectorLookupRelation; 2],
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    expected_output_layer: usize,
    trace_len: usize,
    preprocessed_generic_lookup: &[E],
    lookup_challenges_multiplicative_part: E,
    lookup_challenges_additive_part: E,
    offset_for_decoder_table: u32,
    worker: &Worker,
) {
    assert_ne!(inputs[0].lookup_set_index, DECODER_LOOKUP_FORMAL_SET_INDEX);
    assert_ne!(inputs[1].lookup_set_index, DECODER_LOOKUP_FORMAL_SET_INDEX);
    let mut num_destination = Box::<[E], Global>::new_uninit_slice(trace_len);
    let mut den_destination = Box::<[E], Global>::new_uninit_slice(trace_len);
    let lhs_mapping = core::mem::replace(
        &mut witness_trace.generic_lookup_mapping[inputs[0].lookup_set_index],
        Vec::new(),
    );
    let rhs_mapping = core::mem::replace(
        &mut witness_trace.generic_lookup_mapping[inputs[1].lookup_set_index],
        Vec::new(),
    );
    assert!(lhs_mapping.len() > 0);
    assert!(rhs_mapping.len() > 0);

    apply_row_wise::<F, _>(
        vec![],
        vec![&mut num_destination, &mut den_destination],
        trace_len,
        worker,
        |_, ext_dest, chunk_start, chunk_size| {
            assert_eq!(ext_dest.len(), 2);
            let [num_dest, den_dest] = ext_dest.try_into().unwrap();
            for i in 0..chunk_size {
                let row = chunk_start + i;
                let lhs_mapping_index = lhs_mapping[row];
                let rhs_mapping_index = rhs_mapping[row];
                let lhs_mapped_value = preprocessed_generic_lookup[lhs_mapping_index as usize];
                let rhs_mapped_value = preprocessed_generic_lookup[rhs_mapping_index as usize];

                // 1/(b + gamma) + 1/(d + gamma) -> ((d+gamma) + (b+gamma)), (b+gamma) * (d+gamma)

                let mut b = lhs_mapped_value;
                b.add_assign(&lookup_challenges_additive_part);

                let mut d = rhs_mapped_value;
                d.add_assign(&lookup_challenges_additive_part);

                let mut num = d;
                num.add_assign(&b);

                let mut den = b;
                den.mul_assign(&d);

                num_dest[i].write(num);
                den_dest[i].write(den);

                #[cfg(feature = "gkr_self_checks")]
                {
                    for (mapping_index, mapped_value, rel) in [
                        (lhs_mapping_index, lhs_mapped_value, &inputs[0]),
                        (rhs_mapping_index, rhs_mapped_value, &inputs[1]),
                    ] {
                        assert!(mapping_index < offset_for_decoder_table, "generic lookup should have mapping index {} >= decoder table offset {}, and is not zero in padding", mapping_index, offset_for_decoder_table);

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

    for (output, destination) in outputs
        .into_iter()
        .zip([num_destination, den_destination].into_iter())
    {
        let destination = unsafe { destination.assume_init() };
        output.assert_as_layer(expected_output_layer);
        gkr_storage.insert_extension_at_layer(
            expected_output_layer,
            output,
            ExtensionFieldPoly::new(destination),
        );
    }
}

pub(crate) fn materialize_lookup_expressions_pair_with_remainder<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    inputs: [GKRAddress; 2],
    remainder: &NoFieldVectorLookupRelation,
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    expected_output_layer: usize,
    trace_len: usize,
    preprocessed_generic_lookup: &[E],
    lookup_challenges_multiplicative_part: E,
    lookup_challenges_additive_part: E,
    offset_for_decoder_table: u32,
    worker: &Worker,
) {
    assert_ne!(remainder.lookup_set_index, DECODER_LOOKUP_FORMAL_SET_INDEX);
    let mut num_destination = Box::<[E], Global>::new_uninit_slice(trace_len);
    let mut den_destination = Box::<[E], Global>::new_uninit_slice(trace_len);
    let mapping = core::mem::replace(
        &mut witness_trace.generic_lookup_mapping[remainder.lookup_set_index],
        Vec::new(),
    );
    assert!(mapping.len() > 0);
    let mapping_ref = &mapping;
    let num = gkr_storage.get_ext_poly(inputs[0]);
    let den = gkr_storage.get_ext_poly(inputs[1]);

    apply_row_wise::<F, _>(
        vec![],
        vec![&mut num_destination, &mut den_destination],
        trace_len,
        worker,
        |_, ext_dest, chunk_start, chunk_size| {
            assert_eq!(ext_dest.len(), 2);
            let [num_dest, den_dest] = ext_dest.try_into().unwrap();
            for i in 0..chunk_size {
                let row = chunk_start + i;
                let mapping_index = mapping_ref[row];
                let mapped_value = preprocessed_generic_lookup[mapping_index as usize];

                // a/b + 1/(d + gamma) -> (a * (d+gamma) + b), (b+gamma) * (d+gamma)

                let a = num[row];
                let b = den[row];

                let mut d = mapped_value;
                d.add_assign(&lookup_challenges_additive_part);

                let mut num = d;
                num.mul_assign(&a);
                num.add_assign(&b);

                let mut den = b;
                den.mul_assign(&d);

                num_dest[i].write(num);
                den_dest[i].write(den);

                #[cfg(feature = "gkr_self_checks")]
                {
                    assert!(mapping_index < offset_for_decoder_table, "generic lookup should have mapping index {} >= decoder table offset {}, and is not zero in padding", mapping_index, offset_for_decoder_table);

                    let naive_eval = {
                        let mut result = E::from_base(evaluate_linear_relation_at_row(
                            &remainder.columns[0],
                            gkr_storage,
                            row,
                        ));
                        let mut challenge = lookup_challenges_multiplicative_part;
                        for rel in remainder.columns[1..].iter() {
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

                    if naive_eval != mapped_value {
                        for (idx, rel) in remainder.columns.iter().enumerate() {
                            let v = evaluate_linear_relation_at_row(rel, gkr_storage, row);
                            println!("Column {} = {}", idx, v);
                        }
                    }
                    assert_eq!(
                        naive_eval, mapped_value,
                        "generic lookup diverged at row {} for relation {:?}",
                        row, remainder
                    );
                }
            }
        },
    );

    for (output, destination) in outputs
        .into_iter()
        .zip([num_destination, den_destination].into_iter())
    {
        let destination = unsafe { destination.assume_init() };
        output.assert_as_layer(expected_output_layer);
        gkr_storage.insert_extension_at_layer(
            expected_output_layer,
            output,
            ExtensionFieldPoly::new(destination),
        );
    }
}

pub(crate) fn materialize_lookup_expression_minus_setup<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    input: &NoFieldVectorLookupRelation,
    multiplicity_address: GKRAddress,
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    trace_len: usize,
    preprocessed_generic_lookup: &[E],
    lookup_challenges_multiplicative_part: E,
    lookup_challenges_additive_part: E,
    offset_for_decoder_table: u32,
    worker: &Worker,
) {
    assert_ne!(input.lookup_set_index, DECODER_LOOKUP_FORMAL_SET_INDEX);
    let mut num_destination = Box::<[E], Global>::new_uninit_slice(trace_len);
    let mut den_destination = Box::<[E], Global>::new_uninit_slice(trace_len);
    let mapping = core::mem::replace(
        &mut witness_trace.generic_lookup_mapping[input.lookup_set_index],
        Vec::new(),
    );
    assert!(mapping.len() > 0);
    let mapping_ref = &mapping;
    let multiplicity = gkr_storage.get_base_layer(multiplicity_address);

    apply_row_wise::<F, _>(
        vec![],
        vec![&mut num_destination, &mut den_destination],
        trace_len,
        worker,
        |_, ext_dest, chunk_start, chunk_size| {
            assert_eq!(ext_dest.len(), 2);
            let [num_dest, den_dest] = ext_dest.try_into().unwrap();
            for i in 0..chunk_size {
                let row = chunk_start + i;
                let mapping_index = mapping_ref[row];
                let mapped_value = preprocessed_generic_lookup[mapping_index as usize];

                let multiplicity_value = multiplicity[row];
                let setup_value = preprocessed_generic_lookup
                    .get(row)
                    .copied()
                    .unwrap_or(E::ZERO);

                // 1/(b + gamma) - c/(d + gamma) -> ((d+gamma) - c*(b+gamma)), (b+gamma) * (d+gamma)

                let mut b = mapped_value;
                b.add_assign(&lookup_challenges_additive_part);

                let mut d = setup_value;
                d.add_assign(&lookup_challenges_additive_part);

                let mut num = d;

                let mut t = b;
                t.mul_assign_by_base(&multiplicity_value);

                num.sub_assign(&t);

                let mut den = b;
                den.mul_assign(&d);

                num_dest[i].write(num);
                den_dest[i].write(den);

                #[cfg(feature = "gkr_self_checks")]
                {
                    assert!(mapping_index < offset_for_decoder_table, "generic lookup should have mapping index {} >= decoder table offset {}, and is not zero in padding", mapping_index, offset_for_decoder_table);

                    let naive_eval = {
                        let mut result = E::from_base(evaluate_linear_relation_at_row(
                            &input.columns[0],
                            gkr_storage,
                            row,
                        ));
                        let mut challenge = lookup_challenges_multiplicative_part;
                        for rel in input.columns[1..].iter() {
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

                    if naive_eval != mapped_value {
                        for (idx, rel) in input.columns.iter().enumerate() {
                            let v = evaluate_linear_relation_at_row(rel, gkr_storage, row);
                            println!("Column {} = {}", idx, v);
                        }
                    }
                    assert_eq!(
                        naive_eval, mapped_value,
                        "generic lookup diverged at row {} for relation {:?}",
                        row, input
                    );
                }
            }
        },
    );

    for (output, destination) in outputs
        .into_iter()
        .zip([num_destination, den_destination].into_iter())
    {
        let destination = unsafe { destination.assume_init() };
        output.assert_as_layer(1);
        gkr_storage.insert_extension_at_layer(1, output, ExtensionFieldPoly::new(destination));
    }
}
