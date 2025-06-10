use cs::definitions::LookupExpression;

use super::*;

pub(crate) fn produce_boolean_constraint(witness_column: usize, idents: &Idents) -> TokenStream {
    let place = ColumnAddress::WitnessSubtree(witness_column);
    let read_expr = read_value_expr(place, idents, false);

    let Idents {
        individual_term_ident,
        ..
    } = idents;

    quote! {
        let #individual_term_ident = {
            let value = #read_expr;
            let mut t = value;
            t.sub_assign_base(&Mersenne31Field::ONE);
            t.mul_assign(&value);

            t
        };
    }
}

pub(crate) fn transform_degree_2_constraint(
    constraint: CompiledDegree2Constraint<Mersenne31Field>,
    idents: &Idents,
) -> TokenStream {
    if let Some(result) = guess_transform_squaring_of_linear_combination(constraint.clone(), idents)
    {
        return result;
    }

    let CompiledDegree2Constraint {
        quadratic_terms,
        linear_terms,
        constant_term,
    } = constraint;

    let Idents {
        individual_term_ident,
        ..
    } = idents;

    let mut stream = TokenStream::new();
    let mut is_first = true;

    for el in quadratic_terms {
        let (coeff, a, b) = el;
        let read_a_expr = read_value_expr(a, idents, false);
        let read_b_expr = read_value_expr(b, idents, false);
        if is_first {
            is_first = false;
            // first expression will create an accumulator
            let t = if coeff == Mersenne31Field::ONE {
                quote! {
                    let mut #individual_term_ident = {
                        let mut a = #read_a_expr;
                        let b = #read_b_expr;
                        a.mul_assign(&b);

                        a
                    };
                }
            } else if coeff == Mersenne31Field::MINUS_ONE {
                quote! {
                    let mut #individual_term_ident = {
                        let mut a = #read_a_expr;
                        let b = #read_b_expr;
                        a.mul_assign(&b);
                        a.negate();

                        a
                    };
                }
            } else {
                let coeff = coeff.to_reduced_u32();
                quote! {
                    let mut #individual_term_ident = {
                        let mut a = #read_a_expr;
                        let b = #read_b_expr;
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(#coeff));

                        a
                    };
                }
            };

            stream.extend(t);
        } else {
            let t = if coeff == Mersenne31Field::ONE {
                quote! {
                    {
                        let mut a = #read_a_expr;
                        let b = #read_b_expr;
                        a.mul_assign(&b);
                        #individual_term_ident.add_assign(&a);
                    }
                }
            } else if coeff == Mersenne31Field::MINUS_ONE {
                quote! {
                    {
                        let mut a = #read_a_expr;
                        let b = #read_b_expr;
                        a.mul_assign(&b);
                        #individual_term_ident.sub_assign(&a);
                    }
                }
            } else {
                let coeff = coeff.to_reduced_u32();
                quote! {
                    {
                        let mut a = #read_a_expr;
                        let b = #read_b_expr;
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(#coeff));
                        #individual_term_ident.add_assign(&a);
                    }
                }
            };

            stream.extend(t);
        }
    }

    for el in linear_terms {
        let (coeff, a) = el;
        let read_a_expr = read_value_expr(a, idents, false);
        let t = if coeff == Mersenne31Field::ONE {
            quote! {
                {
                    let a = #read_a_expr;
                    #individual_term_ident.add_assign(&a);
                }
            }
        } else if coeff == Mersenne31Field::MINUS_ONE {
            quote! {
                {
                    let a = #read_a_expr;
                    #individual_term_ident.sub_assign(&a);
                }
            }
        } else {
            let coeff = coeff.to_reduced_u32();
            quote! {
                {
                    let mut a = #read_a_expr;
                    a.mul_assign_by_base(&Mersenne31Field(#coeff));
                    #individual_term_ident.add_assign(&a);
                }
            }
        };

        stream.extend(t);
    }

    if constant_term.is_zero() == false {
        let constant_term = constant_term.to_reduced_u32();
        let t = quote! {
            #individual_term_ident.add_assign_base(&Mersenne31Field(#constant_term));
        };

        stream.extend(t);
    }

    quote! {
        let #individual_term_ident = {
            #stream

            #individual_term_ident
        };
    }
}

pub(crate) fn guess_transform_squaring_of_linear_combination(
    constraint: CompiledDegree2Constraint<Mersenne31Field>,
    idents: &Idents,
) -> Option<TokenStream> {
    if constraint.quadratic_terms.len() < 64 {
        return None;
    }

    let input_size = match constraint.quadratic_terms.len() {
        136 => 16,
        153 => 17,
        171 => 18,
        190 => 19,
        210 => 20,
        231 => 21,
        253 => 22,
        276 => 23,
        300 => 24,
        325 => 25,
        351 => 26,
        378 => 27,
        406 => 28,
        435 => 29,
        465 => 30,
        _ => {
            return None;
        }
    };
    let mut expected_start_var = ColumnAddress::OptimizedOut(0);
    let mut a_coeff = Mersenne31Field::ZERO;
    let mut lc = vec![];
    // we know that terms are sorted
    for (i, (coeff, a, b)) in constraint
        .quadratic_terms
        .iter()
        .take(input_size)
        .enumerate()
    {
        if i == 0 {
            if a != b {
                return None;
            }
            let Some(coeff_root) = coeff.sqrt() else {
                return None;
            };
            expected_start_var = *a;
            a_coeff = coeff_root;
            lc.push((a_coeff, *a));
        } else {
            if *a != expected_start_var {
                return None;
            }
            if a == b {
                return None;
            }
            let mut coeff = *coeff;
            coeff.mul_assign(&a_coeff.inverse().unwrap());
            coeff.mul_assign(&Mersenne31Field::TWO.inverse().unwrap());
            lc.push((coeff, *b));
        }
    }

    if expected_start_var == ColumnAddress::OptimizedOut(0) {
        return None;
    }

    // now check backwards

    let mut expected = vec![];
    for i in 0..lc.len() {
        let (a_coeff, a) = lc[i];
        for j in i..lc.len() {
            let (b_coeff, b) = lc[j];
            let mut coeff = a_coeff;
            coeff.mul_assign(&b_coeff);
            if i != j {
                coeff.double();
            }
            expected.push((coeff, a, b));
        }
    }

    if &expected[..] != &constraint.quadratic_terms[..] {
        return None;
    }

    // so we can generate a temporary term for linear combination, before multiplication
    let mut substream = quote! {
        let mut t = Mersenne31Quartic::ZERO;
    };
    for (coeff, place) in lc.into_iter() {
        let read_a_expr = read_value_expr(place, idents, false);
        let coeff = coeff.to_reduced_u32();
        let t = quote! {
            {
                let mut a = #read_a_expr;
                a.mul_assign_by_base(&Mersenne31Field(#coeff));
                t.add_assign(&a);
            }
        };
        substream.extend(t);
    }

    let Idents {
        individual_term_ident,
        ..
    } = idents;

    let CompiledDegree2Constraint {
        quadratic_terms: _,
        linear_terms,
        constant_term,
    } = constraint;

    let mut stream = quote! {
        let mut #individual_term_ident = {
            #substream

            t.square();

            t
        };
    };

    for el in linear_terms {
        let (coeff, a) = el;
        let read_a_expr = read_value_expr(a, idents, false);
        let t = if coeff == Mersenne31Field::ONE {
            quote! {
                {
                    let a = #read_a_expr;
                    #individual_term_ident.add_assign(&a);
                }
            }
        } else if coeff == Mersenne31Field::MINUS_ONE {
            quote! {
                {
                    let a = #read_a_expr;
                    #individual_term_ident.sub_assign(&a);
                }
            }
        } else {
            let coeff = coeff.to_reduced_u32();
            quote! {
                {
                    let mut a = #read_a_expr;
                    a.mul_assign_by_base(&Mersenne31Field(#coeff));
                    #individual_term_ident.add_assign(&a);
                }
            }
        };

        stream.extend(t);
    }

    if constant_term.is_zero() == false {
        let constant_term = constant_term.to_reduced_u32();
        let t = quote! {
            #individual_term_ident.add_assign_base(&Mersenne31Field(#constant_term));
        };

        stream.extend(t);
    }

    let result = quote! {
        let #individual_term_ident = {
            #stream

            #individual_term_ident
        };
    };

    Some(result)
}

pub(crate) fn transform_degree_1_constraint(
    constraint: CompiledDegree1Constraint<Mersenne31Field>,
    idents: &Idents,
) -> TokenStream {
    let CompiledDegree1Constraint {
        linear_terms,
        constant_term,
    } = constraint;

    let Idents {
        individual_term_ident,
        ..
    } = idents;

    if linear_terms.len() == 0 {
        // we can have a case of just literal constant expressed this way
        let constant_term = constant_term.to_reduced_u32();

        let stream = quote! {
            let #individual_term_ident = Mersenne31Field(#constant_term);
        };

        return stream;
    }

    assert!(linear_terms.len() > 0);

    let mut stream = TokenStream::new();
    let mut is_first = true;

    for el in linear_terms {
        let (coeff, a) = el;
        let read_a_expr = read_value_expr(a, idents, false);
        if is_first {
            is_first = false;
            // first expression will create an accumulator
            let t = if coeff == Mersenne31Field::ONE {
                quote! {
                    let mut #individual_term_ident = {
                        let a = #read_a_expr;

                        a
                    };
                }
            } else if coeff == Mersenne31Field::MINUS_ONE {
                quote! {
                    let mut #individual_term_ident = {
                        let mut a = #read_a_expr;
                        a.negate();

                        a
                    };
                }
            } else {
                let coeff = coeff.to_reduced_u32();
                quote! {
                    let mut #individual_term_ident = {
                        let mut a = #read_a_expr;
                        a.mul_assign_by_base(&Mersenne31Field(#coeff));

                        a
                    };
                }
            };

            stream.extend(t);
        } else {
            let t = if coeff == Mersenne31Field::ONE {
                quote! {
                    {
                        let a = #read_a_expr;
                        #individual_term_ident.add_assign(&a);
                    }
                }
            } else if coeff == Mersenne31Field::MINUS_ONE {
                quote! {
                    {
                        let a = #read_a_expr;
                        #individual_term_ident.sub_assign(&a);
                    }
                }
            } else {
                let coeff = coeff.to_reduced_u32();
                quote! {
                    {
                        let mut a = #read_a_expr;
                        a.mul_assign_by_base(&Mersenne31Field(#coeff));
                        #individual_term_ident.add_assign(&a);
                    }
                }
            };

            stream.extend(t);
        };
    }

    if constant_term.is_zero() == false {
        let constant_term = constant_term.to_reduced_u32();
        let t = quote! {
            #individual_term_ident.add_assign_base(&Mersenne31Field(#constant_term));
        };

        stream.extend(t);
    }

    quote! {
        let #individual_term_ident = {
            #stream

            #individual_term_ident
        };
    }
}

fn transform_lookup_expression_for_eval(
    expression: LookupExpression<Mersenne31Field>,
    idents: &Idents,
) -> TokenStream {
    let individual_term_ident = &idents.individual_term_ident;
    match expression {
        LookupExpression::Variable(place) => {
            let expr = read_value_expr(place, idents, false);

            quote! {
                {
                    let value = #expr;

                    value
                }
            }
        }
        LookupExpression::Expression(constraint) => {
            let t = transform_degree_1_constraint(constraint, idents);
            quote! {
                {
                    #t

                    #individual_term_ident
                }
            }
        }
    }
}

pub(crate) fn transform_width_1_range_checks_pair(
    pair: &[LookupExpression<Mersenne31Field>; 2],
    pair_index: usize,
    optimized_layoyt: OptimizedOraclesForLookupWidth1,
    idents: &Idents,
    stage_2_layout: &LookupAndMemoryArgumentLayout,
    add_timestamp_contribution: bool,
) -> (TokenStream, Vec<TokenStream>) {
    let Idents {
        individual_term_ident,
        lookup_argument_gamma_ident,
        lookup_argument_two_gamma_ident,
        memory_timestamp_high_from_sequence_idx_ident,
        ..
    } = idents;

    let c_offset = optimized_layoyt
        .base_field_oracles
        .get_range(pair_index)
        .start;
    // our inputs are not just variables, but expressions potentially, so we should parse them

    let a_stream = transform_lookup_expression_for_eval(pair[0].clone(), idents);
    let b_stream = transform_lookup_expression_for_eval(pair[1].clone(), idents);
    let c_expr = read_stage_2_value_expr(c_offset, idents, false);

    // everything that is accesses across two terms
    let common_stream = if add_timestamp_contribution == false {
        quote! {
            let a = #a_stream;
            let b = #b_stream;
            let c = #c_expr;
        }
    } else {
        // need to account for contribution from timestamping from circuit idx
        quote! {
            let a = #a_stream;
            let mut b = #b_stream;
            b.sub_assign_base(& #memory_timestamp_high_from_sequence_idx_ident);
            let c = #c_expr;
        }
    };

    let mut streams = Vec::with_capacity(2);

    let t0 = quote! {
        let #individual_term_ident = {
            let mut #individual_term_ident = a;
            #individual_term_ident.mul_assign(&b);
            #individual_term_ident.sub_assign(&c);

            #individual_term_ident
        };
    };
    streams.push(t0);

    // now accumulator * denom - numerator == 0
    let acc_offset = optimized_layoyt.get_ext4_poly_index_in_openings(pair_index, stage_2_layout);
    let acc_expr = read_stage_2_value_expr(acc_offset, idents, false);

    let t1 = quote! {
        let #individual_term_ident = {
            let acc_value = #acc_expr;

            let mut denom = #lookup_argument_gamma_ident;
            denom.add_assign(&a);
            denom.add_assign(&b);
            denom.mul_assign(& #lookup_argument_gamma_ident);
            denom.add_assign(&c);
            // C(x) + gamma * (a(x) + b(x)) + gamma^2
            denom.mul_assign(&acc_value);

            let mut numerator = #lookup_argument_two_gamma_ident;
            numerator.add_assign(&a);
            numerator.add_assign(&b);
            // a(x) + b(x) + 2 * gamma

            // Acc(x) * (C(x) + gamma * (a(x) + b(x)) + gamma^2) - (a(x) + b(x) + 2 * gamma)

            let mut #individual_term_ident = denom;
            #individual_term_ident.sub_assign(&numerator);

            #individual_term_ident
        };
    };
    streams.push(t1);

    (common_stream, streams)
}

pub(crate) fn transform_shuffle_ram_lazy_init_range_checks(
    lazy_init_address_range_check_16: OptimizedOraclesForLookupWidth1,
    shuffle_ram_inits_and_teardowns: ShuffleRamInitAndTeardownLayout,
    idents: &Idents,
    stage_2_layout: &LookupAndMemoryArgumentLayout,
) -> Vec<TokenStream> {
    let Idents {
        individual_term_ident,
        lookup_argument_gamma_ident,
        lookup_argument_two_gamma_ident,
        ..
    } = idents;

    let c_offset = lazy_init_address_range_check_16
        .base_field_oracles
        .get_range(0)
        .start;
    let a = shuffle_ram_inits_and_teardowns
        .lazy_init_addresses_columns
        .start();
    let b = a + 1;
    let a_place = ColumnAddress::MemorySubtree(a);
    let b_place = ColumnAddress::MemorySubtree(b);

    let mut streams = Vec::with_capacity(2);

    let a_expr = read_value_expr(a_place, idents, false);
    let b_expr = read_value_expr(b_place, idents, false);
    let c_expr = read_stage_2_value_expr(c_offset, idents, false);

    let t0 = quote! {
        let #individual_term_ident = {
            let a = #a_expr;
            let b = #b_expr;
            let c = #c_expr;

            let mut #individual_term_ident = a;
            #individual_term_ident.mul_assign(&b);
            #individual_term_ident.sub_assign(&c);

            #individual_term_ident
        };
    };
    streams.push(t0);

    // now accumulator * denom - numerator == 0
    let acc_offset =
        lazy_init_address_range_check_16.get_ext4_poly_index_in_openings(0, stage_2_layout);
    let acc_expr = read_stage_2_value_expr(acc_offset, idents, false);

    let t1 = quote! {
        let #individual_term_ident = {
            let a = #a_expr;
            let b = #b_expr;
            let c = #c_expr;
            let acc_value = #acc_expr;

            let mut denom = #lookup_argument_gamma_ident;
            denom.add_assign(&a);
            denom.add_assign(&b);
            denom.mul_assign(& #lookup_argument_gamma_ident);
            denom.add_assign(&c);
            // C(x) + gamma * (a(x) + b(x)) + gamma^2
            denom.mul_assign(&acc_value);

            let mut numerator = #lookup_argument_two_gamma_ident;
            numerator.add_assign(&a);
            numerator.add_assign(&b);
            // a(x) + b(x) + 2 * gamma

            // Acc(x) * (C(x) + gamma * (a(x) + b(x)) + gamma^2) - (a(x) + b(x) + 2 * gamma)

            let mut #individual_term_ident = denom;
            #individual_term_ident.sub_assign(&numerator);

            #individual_term_ident
        };
    };
    streams.push(t1);

    streams
}

// pub(crate) fn transform_generic_lookup(
//     witness_layout: &WitnessSubtree<Mersenne31Field>,
//     stage_2_layout: &LookupAndMemoryArgumentLayout,
//     setup_layout: &SetupLayout,
//     idents: &Idents,
// ) -> Vec<TokenStream> {
//     if stage_2_layout
//         .intermediate_polys_for_generic_lookup
//         .num_elements()
//         == 0
//     {
//         return vec![];
//     }

//     let Idents {
//         individual_term_ident,
//         lookup_argument_linearization_challenges_ident,
//         lookup_argument_gamma_ident,
//         ..
//     } = idents;

//     let mut streams = vec![];

//     let mut dst_iter = stage_2_layout.intermediate_polys_for_generic_lookup.iter();
//     let mut width_3_lookups_with_fixed_col_id = vec![];
//     for lookup in witness_layout.width_3_lookups.iter() {
//         if let TableIndex::Constant(table_type) = lookup.table_index {
//             let src = lookup.input_columns.clone();
//             let dst = dst_iter.next().unwrap().start;
//             let column_type =
//                 Mersenne31Field::from_u64_with_reduction(table_type.to_table_id() as u64);
//             width_3_lookups_with_fixed_col_id.push((src, dst, column_type));
//         }
//     }
//     let mut width_3_lookups_with_variable_col_id = vec![];
//     for lookup in witness_layout.width_3_lookups.iter() {
//         if let TableIndex::Variable(table_type) = lookup.table_index {
//             let src = lookup.input_columns.clone();
//             let dst = dst_iter.next().unwrap().start;
//             let ColumnAddress::WitnessSubtree(table_type_idx) = table_type else {
//                 panic!();
//             };
//             width_3_lookups_with_variable_col_id.push((src, table_type_idx, dst));
//         }
//     }

//     assert!(dst_iter.next().is_none());

//     assert_eq!(setup_layout.generic_lookup_setup_columns.width(), 4);

//     // width-3 generic lookup
//     {
//         let mut i = 0;
//         for (src, _dst, table_type) in width_3_lookups_with_fixed_col_id.iter() {
//             let table_type = table_type.to_reduced_u32();
//             let acc = stage_2_layout
//                 .get_intermediate_polys_for_generic_lookup_absolute_poly_idx_for_verifier(i);
//             let accumulator_expr = read_stage_2_value_expr(acc, idents, false);
//             let src = src.clone();
//             let [src0, src1, src2] = src;
//             let src_0_expr = transform_lookup_expression_for_eval(src0, idents);
//             let src_1_expr = transform_lookup_expression_for_eval(src1, idents);
//             let src_2_expr = transform_lookup_expression_for_eval(src2, idents);

//             let t = quote! {
//                 let #individual_term_ident = {
//                     let src0 = #src_0_expr;
//                     let src1 = #src_1_expr;
//                     let src2 = #src_2_expr;

//                     let mut denom = #lookup_argument_linearization_challenges_ident[2];
//                     let table_id = Mersenne31Field(#table_type);
//                     denom.mul_assign_by_base(&table_id);

//                     let mut t = #lookup_argument_linearization_challenges_ident[1];
//                     t.mul_assign_by_base(&src2);
//                     denom.add_assign(&t);

//                     let mut t = #lookup_argument_linearization_challenges_ident[0];
//                     t.mul_assign_by_base(&src1);
//                     denom.add_assign(&t);

//                     denom.add_assign(&src0);

//                     denom.add_assign(&#lookup_argument_gamma_ident);

//                     let mut #individual_term_ident = denom;
//                     #individual_term_ident.mul_assign(& #accumulator_expr);
//                     #individual_term_ident.sub_assign_base(&Mersenne31Field::ONE);

//                     #individual_term_ident
//                 };
//             };

//             streams.push(t);

//             i += 1;
//         }

//         for (src, table_type_offset, _dst) in width_3_lookups_with_variable_col_id.iter() {
//             let acc = stage_2_layout
//                 .get_intermediate_polys_for_generic_lookup_absolute_poly_idx_for_verifier(i);
//             let accumulator_expr = read_stage_2_value_expr(acc, idents, false);
//             let src = src.clone();
//             let [src0, src1, src2] = src;
//             let src_0_expr = transform_lookup_expression_for_eval(src0, idents);
//             let src_1_expr = transform_lookup_expression_for_eval(src1, idents);
//             let src_2_expr = transform_lookup_expression_for_eval(src2, idents);
//             let src_3_expr = read_value_expr(
//                 ColumnAddress::WitnessSubtree(*table_type_offset),
//                 idents,
//                 false,
//             );

//             let t = quote! {
//                 let #individual_term_ident = {
//                     let src0 = #src_0_expr;
//                     let src1 = #src_1_expr;
//                     let src2 = #src_2_expr;
//                     let table_id = #src_3_expr;

//                     let mut denom = #lookup_argument_linearization_challenges_ident[2];
//                     denom.mul_assign(&table_id);

//                     let mut t = #lookup_argument_linearization_challenges_ident[1];
//                     t.mul_assign_by_base(&src2);
//                     denom.add_assign(&t);

//                     let mut t = #lookup_argument_linearization_challenges_ident[0];
//                     t.mul_assign_by_base(&src1);
//                     denom.add_assign(&t);

//                     denom.add_assign(&src0);

//                     denom.add_assign(&#lookup_argument_gamma_ident);

//                     let mut #individual_term_ident = denom;
//                     #individual_term_ident.mul_assign(& #accumulator_expr);
//                     #individual_term_ident.sub_assign_base(&Mersenne31Field::ONE);

//                     #individual_term_ident
//                 };
//             };

//             streams.push(t);

//             i += 1;
//         }
//     }

//     streams
// }

pub(crate) fn transform_generic_lookup(
    witness_layout: &WitnessSubtree<Mersenne31Field>,
    stage_2_layout: &LookupAndMemoryArgumentLayout,
    setup_layout: &SetupLayout,
    idents: &Idents,
) -> Vec<TokenStream> {
    if stage_2_layout
        .intermediate_polys_for_generic_lookup
        .num_elements()
        == 0
    {
        return vec![];
    }

    let Idents {
        individual_term_ident,
        lookup_argument_linearization_challenges_ident,
        lookup_argument_gamma_ident,
        ..
    } = idents;

    let mut streams = vec![];
    assert_eq!(setup_layout.generic_lookup_setup_columns.width(), 4);

    for (i, (lookup, dst)) in witness_layout
        .width_3_lookups
        .iter()
        .zip(stage_2_layout.intermediate_polys_for_generic_lookup.iter())
        .enumerate()
    {
        let src = lookup.input_columns.clone();
        let dst = dst.start;
        match lookup.table_index {
            TableIndex::Constant(table_type) => {
                let table_type = table_type.to_table_id();
                let acc = stage_2_layout
                    .get_intermediate_polys_for_generic_lookup_absolute_poly_idx_for_verifier(i);
                let accumulator_expr = read_stage_2_value_expr(acc, idents, false);
                let src = src.clone();
                let [src0, src1, src2] = src;
                let src_0_expr = transform_lookup_expression_for_eval(src0, idents);
                let src_1_expr = transform_lookup_expression_for_eval(src1, idents);
                let src_2_expr = transform_lookup_expression_for_eval(src2, idents);

                let t = quote! {
                    let #individual_term_ident = {
                        let src0 = #src_0_expr;
                        let src1 = #src_1_expr;
                        let src2 = #src_2_expr;

                        let mut denom = #lookup_argument_linearization_challenges_ident[2];
                        let table_id = Mersenne31Field(#table_type);
                        denom.mul_assign_by_base(&table_id);

                        let mut t = #lookup_argument_linearization_challenges_ident[1];
                        t.mul_assign_by_base(&src2);
                        denom.add_assign(&t);

                        let mut t = #lookup_argument_linearization_challenges_ident[0];
                        t.mul_assign_by_base(&src1);
                        denom.add_assign(&t);

                        denom.add_assign(&src0);

                        denom.add_assign(&#lookup_argument_gamma_ident);

                        let mut #individual_term_ident = denom;
                        #individual_term_ident.mul_assign(& #accumulator_expr);
                        #individual_term_ident.sub_assign_base(&Mersenne31Field::ONE);

                        #individual_term_ident
                    };
                };

                streams.push(t);
            }
            TableIndex::Variable(table_type) => {
                let ColumnAddress::WitnessSubtree(table_type_column) = table_type else {
                    panic!();
                };
                let acc = stage_2_layout
                    .get_intermediate_polys_for_generic_lookup_absolute_poly_idx_for_verifier(i);
                let accumulator_expr = read_stage_2_value_expr(acc, idents, false);
                let src = src.clone();
                let [src0, src1, src2] = src;
                let src_0_expr = transform_lookup_expression_for_eval(src0, idents);
                let src_1_expr = transform_lookup_expression_for_eval(src1, idents);
                let src_2_expr = transform_lookup_expression_for_eval(src2, idents);
                let src_3_expr = read_value_expr(
                    ColumnAddress::WitnessSubtree(table_type_column),
                    idents,
                    false,
                );

                let t = quote! {
                    let #individual_term_ident = {
                        let src0 = #src_0_expr;
                        let src1 = #src_1_expr;
                        let src2 = #src_2_expr;
                        let table_id = #src_3_expr;

                        let mut denom = #lookup_argument_linearization_challenges_ident[2];
                        denom.mul_assign(&table_id);

                        let mut t = #lookup_argument_linearization_challenges_ident[1];
                        t.mul_assign_by_base(&src2);
                        denom.add_assign(&t);

                        let mut t = #lookup_argument_linearization_challenges_ident[0];
                        t.mul_assign_by_base(&src1);
                        denom.add_assign(&t);

                        denom.add_assign(&src0);

                        denom.add_assign(&#lookup_argument_gamma_ident);

                        let mut #individual_term_ident = denom;
                        #individual_term_ident.mul_assign(& #accumulator_expr);
                        #individual_term_ident.sub_assign_base(&Mersenne31Field::ONE);

                        #individual_term_ident
                    };
                };

                streams.push(t);
            }
        }
    }

    streams
}

pub(crate) fn transform_multiplicities(
    witness_layout: &WitnessSubtree<Mersenne31Field>,
    stage_2_layout: &LookupAndMemoryArgumentLayout,
    setup_layout: &SetupLayout,
    idents: &Idents,
) -> Vec<TokenStream> {
    let mut streams = vec![];

    let Idents {
        individual_term_ident,
        lookup_argument_linearization_challenges_ident,
        lookup_argument_gamma_ident,
        ..
    } = idents;

    let range_check_16_multiplicities_src = witness_layout
        .multiplicities_columns_for_range_check_16
        .start();
    let range_check_16_setup_column = setup_layout.range_check_16_setup_column.start();

    let timestamp_range_check_multiplicities_src = witness_layout
        .multiplicities_columns_for_timestamp_range_check
        .start();
    let timestamp_range_check_setup_column =
        setup_layout.timestamp_range_check_setup_column.start();

    let generic_lookup_multiplicities_src = witness_layout
        .multiplicities_columns_for_generic_lookup
        .start();
    assert_eq!(setup_layout.generic_lookup_setup_columns.width(), 4);

    let generic_lookup_setup_columns_start = setup_layout.generic_lookup_setup_columns.start();

    // range check 16
    {
        let intermediate_poly_expr = read_stage_2_value_expr(
            stage_2_layout
                .range_check_16_intermediate_poly_for_multiplicities_absolute_poly_idx_for_verifier(
                ),
            idents,
            false,
        );

        let multiplicity_expr = read_value_expr(
            ColumnAddress::WitnessSubtree(range_check_16_multiplicities_src),
            idents,
            false,
        );

        let setup_expr = read_value_expr(
            ColumnAddress::SetupSubtree(range_check_16_setup_column),
            idents,
            false,
        );

        let t = quote! {
            let #individual_term_ident = {
                let m = #multiplicity_expr;

                let t = #setup_expr;
                let mut denom = #lookup_argument_gamma_ident;
                denom.add_assign(&t);

                let mut #individual_term_ident = denom;
                #individual_term_ident.mul_assign(& #intermediate_poly_expr);
                #individual_term_ident.sub_assign(&m);

                #individual_term_ident
            };
        };

        streams.push(t);
    }

    // timestamp range check
    {
        let intermediate_poly_expr = read_stage_2_value_expr(
            stage_2_layout
                .timestamp_range_check_intermediate_poly_for_multiplicities_absolute_poly_idx_for_verifier(
                ),
            idents,
            false,
        );

        let multiplicity_expr = read_value_expr(
            ColumnAddress::WitnessSubtree(timestamp_range_check_multiplicities_src),
            idents,
            false,
        );

        let setup_expr = read_value_expr(
            ColumnAddress::SetupSubtree(timestamp_range_check_setup_column),
            idents,
            false,
        );

        let t = quote! {
            let #individual_term_ident = {
                let m = #multiplicity_expr;

                let t = #setup_expr;
                let mut denom = #lookup_argument_gamma_ident;
                denom.add_assign(&t);

                let mut #individual_term_ident = denom;
                #individual_term_ident.mul_assign(& #intermediate_poly_expr);
                #individual_term_ident.sub_assign(&m);

                #individual_term_ident
            };
        };

        streams.push(t);
    }

    // generic lookup
    {
        let bound = stage_2_layout
            .intermediate_polys_for_generic_multiplicities
            .num_elements();
        for i in 0..bound {
            let acc = stage_2_layout
                .generic_width_3_lookup_intermediate_polys_for_multiplicities_absolute_poly_idx_for_verifier(i);
            let accumulator_expr = read_stage_2_value_expr(acc, idents, false);
            let multiplicity_expr = read_value_expr(
                ColumnAddress::WitnessSubtree(generic_lookup_multiplicities_src + i),
                idents,
                false,
            );
            let tuple_offset = generic_lookup_setup_columns_start + i * (COMMON_TABLE_WIDTH + 1);

            let src_0_expr =
                read_value_expr(ColumnAddress::SetupSubtree(tuple_offset), idents, false);
            let src_1_expr =
                read_value_expr(ColumnAddress::SetupSubtree(tuple_offset + 1), idents, false);
            let src_2_expr =
                read_value_expr(ColumnAddress::SetupSubtree(tuple_offset + 2), idents, false);
            let src_3_expr =
                read_value_expr(ColumnAddress::SetupSubtree(tuple_offset + 3), idents, false);

            let t = quote! {
                let #individual_term_ident = {
                    let m = #multiplicity_expr;

                    let mut denom = #lookup_argument_linearization_challenges_ident[2];
                    let table_id = #src_3_expr;
                    denom.mul_assign(&table_id);

                    let mut t = #lookup_argument_linearization_challenges_ident[1];
                    t.mul_assign(& #src_2_expr);
                    denom.add_assign(&t);

                    let mut t = #lookup_argument_linearization_challenges_ident[0];
                    t.mul_assign(& #src_1_expr);
                    denom.add_assign(&t);

                    let t = #src_0_expr;
                    denom.add_assign(&t);

                    denom.add_assign(&#lookup_argument_gamma_ident);

                    let mut #individual_term_ident = denom;
                    #individual_term_ident.mul_assign(& #accumulator_expr);
                    #individual_term_ident.sub_assign(&m);

                    #individual_term_ident
                };
            };

            streams.push(t);
        }
    }

    streams
}

pub(crate) fn transform_delegation_ram_conventions(
    memory_layout: &MemorySubtree,
    idents: &Idents,
) -> (TokenStream, Vec<TokenStream>) {
    let mut streams = vec![];

    let Idents {
        individual_term_ident,
        ..
    } = idents;

    let delegation_processor_layout = memory_layout
        .delegation_processor_layout
        .expect("must exist");
    let predicate_expr = read_value_expr(
        ColumnAddress::MemorySubtree(delegation_processor_layout.multiplicity.start()),
        idents,
        false,
    );
    let mem_abi_offset_expr = read_value_expr(
        ColumnAddress::MemorySubtree(delegation_processor_layout.abi_mem_offset_high.start()),
        idents,
        false,
    );
    let write_timestamp_low_expr = read_value_expr(
        ColumnAddress::MemorySubtree(delegation_processor_layout.write_timestamp.start()),
        idents,
        false,
    );
    let write_timestamp_high_expr = read_value_expr(
        ColumnAddress::MemorySubtree(delegation_processor_layout.write_timestamp.start() + 1),
        idents,
        false,
    );

    let common_stream = quote! {
        let predicate = #predicate_expr;
        let mut predicate_minus_one = predicate;
        predicate_minus_one.sub_assign_base(&Mersenne31Field::ONE);

        let mem_abi_offset = #mem_abi_offset_expr;
        let write_timestamp_low = #write_timestamp_low_expr;
        let write_timestamp_high = #write_timestamp_high_expr;
    };

    // predicate is 0/1
    {
        let t = quote! {
            let #individual_term_ident = {
                let mut #individual_term_ident = predicate;
                #individual_term_ident.mul_assign(&predicate_minus_one);

                #individual_term_ident
            };
        };
        streams.push(t);
    }

    // now the rest of the values have to be 0s
    // we want a constraint of (predicate - 1) * value == 0

    // - mem abi offset == 0
    {
        let t = quote! {
            let #individual_term_ident = {
                let mut #individual_term_ident = mem_abi_offset;
                #individual_term_ident.mul_assign(&predicate_minus_one);

                #individual_term_ident
            };
        };
        streams.push(t);
    }

    // - write timestamp == 0
    {
        let t = quote! {
            let #individual_term_ident = {
                let mut #individual_term_ident = write_timestamp_low;
                #individual_term_ident.mul_assign(&predicate_minus_one);

                #individual_term_ident
            };
        };
        streams.push(t);

        let write_timestamp_high = read_value_expr(
            ColumnAddress::MemorySubtree(delegation_processor_layout.write_timestamp.start() + 1),
            idents,
            false,
        );
        let t = quote! {
            let #individual_term_ident = {
                let mut #individual_term_ident = #write_timestamp_high;
                #individual_term_ident.mul_assign(&predicate_minus_one);

                #individual_term_ident
            };
        };
        streams.push(t);
    }

    // for every value we check that read timestamp == 0
    // for every read value we check that value == 0
    // for every written value value we check that value == 0

    let bound = memory_layout.batched_ram_accesses.len();
    for i in 0..bound {
        let access = memory_layout.batched_ram_accesses[i];
        match access {
            BatchedRamAccessColumns::ReadAccess {
                read_timestamp,
                read_value,
            } => {
                for set in [read_timestamp, read_value].into_iter() {
                    // low and high
                    {
                        let low_expr = read_value_expr(
                            ColumnAddress::MemorySubtree(set.start()),
                            idents,
                            false,
                        );
                        let t = quote! {
                            let #individual_term_ident = {
                                let low = #low_expr;

                                let mut #individual_term_ident = low;
                                #individual_term_ident.mul_assign(&predicate_minus_one);

                                #individual_term_ident
                            };
                        };
                        streams.push(t);

                        let high_expr = read_value_expr(
                            ColumnAddress::MemorySubtree(set.start() + 1),
                            idents,
                            false,
                        );
                        let t = quote! {
                            let #individual_term_ident = {
                                let high = #high_expr;

                                let mut #individual_term_ident = high;
                                #individual_term_ident.mul_assign(&predicate_minus_one);

                                #individual_term_ident
                            };
                        };
                        streams.push(t);
                    }
                }
            }
            BatchedRamAccessColumns::WriteAccess {
                read_timestamp,
                read_value,
                write_value,
            } => {
                for set in [read_timestamp, read_value, write_value].into_iter() {
                    // low and high
                    {
                        let low_expr = read_value_expr(
                            ColumnAddress::MemorySubtree(set.start()),
                            idents,
                            false,
                        );
                        let t = quote! {
                            let #individual_term_ident = {
                                let low = #low_expr;

                                let mut #individual_term_ident = low;
                                #individual_term_ident.mul_assign(&predicate_minus_one);

                                #individual_term_ident
                            };
                        };
                        streams.push(t);

                        let high_expr = read_value_expr(
                            ColumnAddress::MemorySubtree(set.start() + 1),
                            idents,
                            false,
                        );
                        let t = quote! {
                            let #individual_term_ident = {
                                let high = #high_expr;

                                let mut #individual_term_ident = high;
                                #individual_term_ident.mul_assign(&predicate_minus_one);

                                #individual_term_ident
                            };
                        };
                        streams.push(t);
                    }
                }
            }
        }
    }

    // same for indirects
    let bound = memory_layout.register_and_indirect_accesses.len();
    for i in 0..bound {
        let access = &memory_layout.register_and_indirect_accesses[i];
        match access.register_access {
            RegisterAccessColumns::ReadAccess {
                read_timestamp,
                read_value,
                ..
            } => {
                for set in [read_timestamp, read_value].into_iter() {
                    // low and high
                    {
                        let low_expr = read_value_expr(
                            ColumnAddress::MemorySubtree(set.start()),
                            idents,
                            false,
                        );
                        let t = quote! {
                            let #individual_term_ident = {
                                let low = #low_expr;

                                let mut #individual_term_ident = low;
                                #individual_term_ident.mul_assign(&predicate_minus_one);

                                #individual_term_ident
                            };
                        };
                        streams.push(t);

                        let high_expr = read_value_expr(
                            ColumnAddress::MemorySubtree(set.start() + 1),
                            idents,
                            false,
                        );
                        let t = quote! {
                            let #individual_term_ident = {
                                let high = #high_expr;

                                let mut #individual_term_ident = high;
                                #individual_term_ident.mul_assign(&predicate_minus_one);

                                #individual_term_ident
                            };
                        };
                        streams.push(t);
                    }
                }
            }
            RegisterAccessColumns::WriteAccess {
                read_timestamp,
                read_value,
                write_value,
                ..
            } => {
                for set in [read_timestamp, read_value, write_value].into_iter() {
                    // low and high
                    {
                        let low_expr = read_value_expr(
                            ColumnAddress::MemorySubtree(set.start()),
                            idents,
                            false,
                        );
                        let t = quote! {
                            let #individual_term_ident = {
                                let low = #low_expr;

                                let mut #individual_term_ident = low;
                                #individual_term_ident.mul_assign(&predicate_minus_one);

                                #individual_term_ident
                            };
                        };
                        streams.push(t);

                        let high_expr = read_value_expr(
                            ColumnAddress::MemorySubtree(set.start() + 1),
                            idents,
                            false,
                        );
                        let t = quote! {
                            let #individual_term_ident = {
                                let high = #high_expr;

                                let mut #individual_term_ident = high;
                                #individual_term_ident.mul_assign(&predicate_minus_one);

                                #individual_term_ident
                            };
                        };
                        streams.push(t);
                    }
                }
            }
        }

        if access.indirect_accesses.len() > 0 {
            for (idx, access) in access.indirect_accesses.iter().enumerate() {
                match access {
                    IndirectAccessColumns::ReadAccess {
                        read_timestamp,
                        read_value,
                        address_derivation_carry_bit,
                        ..
                    } => {
                        for set in [read_timestamp, read_value].into_iter() {
                            // low and high
                            {
                                let low_expr = read_value_expr(
                                    ColumnAddress::MemorySubtree(set.start()),
                                    idents,
                                    false,
                                );
                                let t = quote! {
                                    let #individual_term_ident = {
                                        let low = #low_expr;

                                        let mut #individual_term_ident = low;
                                        #individual_term_ident.mul_assign(&predicate_minus_one);

                                        #individual_term_ident
                                    };
                                };
                                streams.push(t);

                                let high_expr = read_value_expr(
                                    ColumnAddress::MemorySubtree(set.start() + 1),
                                    idents,
                                    false,
                                );
                                let t = quote! {
                                    let #individual_term_ident = {
                                        let high = #high_expr;

                                        let mut #individual_term_ident = high;
                                        #individual_term_ident.mul_assign(&predicate_minus_one);

                                        #individual_term_ident
                                    };
                                };
                                streams.push(t);
                            }
                        }

                        // carry bit is boolean
                        if idx > 0 && address_derivation_carry_bit.num_elements() > 0 {
                            let carry_bit_expr = read_value_expr(
                                ColumnAddress::MemorySubtree(address_derivation_carry_bit.start()),
                                idents,
                                false,
                            );

                            let t = quote! {
                                let #individual_term_ident = {
                                    let carry_bit = #carry_bit_expr;

                                    let mut #individual_term_ident = carry_bit;
                                    #individual_term_ident.sub_assign_base(&Mersenne31Field::ONE);
                                    #individual_term_ident.mul_assign(&carry_bit);

                                    #individual_term_ident
                                };
                            };

                            streams.push(t);
                        }
                    }
                    IndirectAccessColumns::WriteAccess {
                        read_timestamp,
                        read_value,
                        write_value,
                        address_derivation_carry_bit,
                        ..
                    } => {
                        for set in [read_timestamp, read_value, write_value].into_iter() {
                            // low and high
                            {
                                let low_expr = read_value_expr(
                                    ColumnAddress::MemorySubtree(set.start()),
                                    idents,
                                    false,
                                );
                                let t = quote! {
                                    let #individual_term_ident = {
                                        let low = #low_expr;

                                        let mut #individual_term_ident = low;
                                        #individual_term_ident.mul_assign(&predicate_minus_one);

                                        #individual_term_ident
                                    };
                                };
                                streams.push(t);

                                let high_expr = read_value_expr(
                                    ColumnAddress::MemorySubtree(set.start() + 1),
                                    idents,
                                    false,
                                );
                                let t = quote! {
                                    let #individual_term_ident = {
                                        let high = #high_expr;

                                        let mut #individual_term_ident = high;
                                        #individual_term_ident.mul_assign(&predicate_minus_one);

                                        #individual_term_ident
                                    };
                                };
                                streams.push(t);
                            }
                        }

                        // carry bit is boolean
                        if idx > 0 {
                            if address_derivation_carry_bit.num_elements() > 0 {
                                let carry_bit_expr = read_value_expr(
                                    ColumnAddress::MemorySubtree(
                                        address_derivation_carry_bit.start(),
                                    ),
                                    idents,
                                    false,
                                );

                                let t = quote! {
                                    let #individual_term_ident = {
                                        let carry_bit = #carry_bit_expr;

                                        let mut #individual_term_ident = carry_bit;
                                        #individual_term_ident.sub_assign_base(&Mersenne31Field::ONE);
                                        #individual_term_ident.mul_assign(&carry_bit);

                                        #individual_term_ident
                                    };
                                };

                                streams.push(t);
                            }
                        }
                    }
                }
            }
        }
    }

    (common_stream, streams)
}

pub(crate) fn transform_delegation_requests_creation(
    memory_layout: &MemorySubtree,
    stage_2_layout: &LookupAndMemoryArgumentLayout,
    setup_layout: &SetupLayout,
    idents: &Idents,
) -> Vec<TokenStream> {
    let mut streams = vec![];

    let Idents {
        individual_term_ident,
        delegation_argument_linearization_challenges_ident,
        delegation_argument_gamma_ident,
        memory_timestamp_high_from_sequence_idx_ident,
        ..
    } = idents;

    let delegation_argument = memory_layout
        .delegation_request_layout
        .expect("must exists");
    let timestamp_setup_start = setup_layout.timestamp_setup_columns.start();
    let in_cycle_timestamp = delegation_argument.in_cycle_write_index as u32;

    // multiplicity for width 3 is special, as we need to assemble challenges
    {
        let acc = stage_2_layout
            .get_aux_polys_for_gelegation_argument_absolute_poly_idx_for_verifier()
            .expect("must exist");
        let accumulator_expr = read_stage_2_value_expr(acc, idents, false);
        let multiplicity_expr = read_value_expr(
            ColumnAddress::MemorySubtree(delegation_argument.multiplicity.start()),
            idents,
            false,
        );

        let src_0_expr = read_value_expr(
            ColumnAddress::MemorySubtree(delegation_argument.delegation_type.start()),
            idents,
            false,
        );
        let src_1_expr = read_value_expr(
            ColumnAddress::MemorySubtree(delegation_argument.abi_mem_offset_high.start()),
            idents,
            false,
        );
        let src_2_expr = read_value_expr(
            ColumnAddress::SetupSubtree(timestamp_setup_start),
            idents,
            false,
        );
        let src_3_expr = read_value_expr(
            ColumnAddress::SetupSubtree(timestamp_setup_start + 1),
            idents,
            false,
        );

        let t = quote! {
            let #individual_term_ident = {
                let m = #multiplicity_expr;

                let mut denom = #delegation_argument_linearization_challenges_ident[2];
                let mut timestamp_high = #src_3_expr;
                timestamp_high.add_assign_base(&#memory_timestamp_high_from_sequence_idx_ident);
                denom.mul_assign(&timestamp_high);

                let mut timestamp_low = #src_2_expr;
                timestamp_low.add_assign_base(&Mersenne31Field(#in_cycle_timestamp));
                let mut t = #delegation_argument_linearization_challenges_ident[1];
                t.mul_assign(&timestamp_low);
                denom.add_assign(&t);

                let mem_abi_offset = #src_1_expr;
                let mut t = #delegation_argument_linearization_challenges_ident[0];
                t.mul_assign(&mem_abi_offset);
                denom.add_assign(&t);

                let t = #src_0_expr;
                denom.add_assign(&t);

                denom.add_assign(&#delegation_argument_gamma_ident);

                let mut #individual_term_ident = denom;
                #individual_term_ident.mul_assign(& #accumulator_expr);
                #individual_term_ident.sub_assign(&m);

                #individual_term_ident
            };
        };

        streams.push(t);
    }

    streams
}

pub(crate) fn transform_delegation_requests_processing(
    memory_layout: &MemorySubtree,
    stage_2_layout: &LookupAndMemoryArgumentLayout,
    idents: &Idents,
) -> Vec<TokenStream> {
    let mut streams = vec![];

    let Idents {
        individual_term_ident,
        delegation_argument_linearization_challenges_ident,
        delegation_argument_gamma_ident,
        delegation_type_ident,
        ..
    } = idents;

    let delegation_processor_layout = memory_layout
        .delegation_processor_layout
        .expect("must exists");

    // multiplicity for width 3 is special, as we need to assemble challenges
    {
        let acc = stage_2_layout
            .get_aux_polys_for_gelegation_argument_absolute_poly_idx_for_verifier()
            .expect("must exist");
        let accumulator_expr = read_stage_2_value_expr(acc, idents, false);
        let multiplicity_expr = read_value_expr(
            ColumnAddress::MemorySubtree(delegation_processor_layout.multiplicity.start()),
            idents,
            false,
        );

        // delegation type is a verifier-provided constant

        let src_1_expr = read_value_expr(
            ColumnAddress::MemorySubtree(delegation_processor_layout.abi_mem_offset_high.start()),
            idents,
            false,
        );
        let src_2_expr = read_value_expr(
            ColumnAddress::MemorySubtree(delegation_processor_layout.write_timestamp.start()),
            idents,
            false,
        );
        let src_3_expr = read_value_expr(
            ColumnAddress::MemorySubtree(delegation_processor_layout.write_timestamp.start() + 1),
            idents,
            false,
        );

        let t = quote! {
            let #individual_term_ident = {
                let m = #multiplicity_expr;

                let mut denom = #delegation_argument_linearization_challenges_ident[2];
                let timestamp_high = #src_3_expr;
                denom.mul_assign(&timestamp_high);

                let timestamp_low = #src_2_expr;
                let mut t = #delegation_argument_linearization_challenges_ident[1];
                t.mul_assign(&timestamp_low);
                denom.add_assign(&t);

                let mem_abi_offset = #src_1_expr;
                let mut t = #delegation_argument_linearization_challenges_ident[0];
                t.mul_assign(&mem_abi_offset);
                denom.add_assign(&t);

                let t = #delegation_type_ident;
                denom.add_assign_base(&t);

                denom.add_assign(&#delegation_argument_gamma_ident);

                let mut #individual_term_ident = denom;
                #individual_term_ident.mul_assign(& #accumulator_expr);
                #individual_term_ident.sub_assign(&m);

                #individual_term_ident
            };
        };

        streams.push(t);
    }

    streams
}

pub(crate) fn transform_shuffle_ram_lazy_init_padding(
    shuffle_ram_inits_and_teardowns: ShuffleRamInitAndTeardownLayout,
    lazy_init_address_aux_vars: &ShuffleRamAuxComparisonSet,
    idents: &Idents,
) -> (TokenStream, Vec<TokenStream>) {
    let Idents {
        individual_term_ident,
        ..
    } = idents;

    let lazy_init_address_start = shuffle_ram_inits_and_teardowns
        .lazy_init_addresses_columns
        .start();

    let teardown_values_start = shuffle_ram_inits_and_teardowns
        .lazy_teardown_values_columns
        .start();

    let teardown_timestamps_start = shuffle_ram_inits_and_teardowns
        .lazy_teardown_timestamps_columns
        .start();

    let comparison_aux_vars = lazy_init_address_aux_vars;
    let ShuffleRamAuxComparisonSet { final_borrow, .. } = *comparison_aux_vars;

    let final_borrow_value_expr = read_value_expr(final_borrow, idents, false);

    let common_stream = quote! {
        let final_borrow_value = #final_borrow_value_expr;

        let mut final_borrow_minus_one = final_borrow_value;
        final_borrow_minus_one.sub_assign_base(&Mersenne31Field::ONE);
    };

    let mut streams = vec![];

    // and now we enforce that if comparison is not strictly this address < next address, then this
    // address is 0, along with teardown parts

    for place in [
        ColumnAddress::MemorySubtree(lazy_init_address_start),
        ColumnAddress::MemorySubtree(lazy_init_address_start + 1),
        ColumnAddress::MemorySubtree(teardown_values_start),
        ColumnAddress::MemorySubtree(teardown_values_start + 1),
        ColumnAddress::MemorySubtree(teardown_timestamps_start),
        ColumnAddress::MemorySubtree(teardown_timestamps_start + 1),
    ] {
        let place_expr = read_value_expr(place, idents, false);
        let t = quote! {
            let #individual_term_ident = {
                let value_to_constraint = #place_expr;

                let mut #individual_term_ident = final_borrow_minus_one;
                #individual_term_ident.mul_assign(&value_to_constraint);

                #individual_term_ident
            };
        };

        streams.push(t);
    }

    (common_stream, streams)
}
