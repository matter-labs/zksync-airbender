use super::*;
use crate::gkr::prover::apply_row_wise;
use cs::definitions::gkr::NoFieldLinearRelation;
use cs::definitions::gkr::NoFieldVectorLookupRelation;
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
                    let decoder_mask_value =
                        gkr_storage.get_base_layer(decoder_predicate_address)[row].as_boolean();
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
                        let decoder_mask_value =
                            gkr_storage.get_base_layer(decoder_predicate_address)[row].as_boolean();
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
                        let decoder_mask_value =
                            gkr_storage.get_base_layer(decoder_predicate_address)[row].as_boolean();
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
