use super::*;

pub(crate) struct GFunctionIntermediateValues<F: PrimeField> {
    pub(crate) a_var_chunks_and_constraint: [([(i32, Variable); 1], Constraint<F>); 2],
    pub(crate) c_var_chunks_and_constraint: [([(i32, Variable); 1], Constraint<F>); 2],
}

// NOTE: a element is always special, and it'll live in the form of constraint, as we will drag it along
// from the previous stages
pub(crate) fn g_function<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    a: &mut [Constraint<F>; 2],
    b: &mut [Vec<(usize, Variable)>; 2],
    c: &mut [Constraint<F>; 2],
    d: &mut [Vec<(usize, Variable)>; 2],
    message: [[Variable; 2]; 2],
) -> GFunctionIntermediateValues<F> {
    assert_eq!(b[0].len(), b[1].len());
    assert_eq!(d[0].len(), d[1].len());

    let [x, y] = message;
    // v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    // v[d] = rotate_right::<16>(v[d] ^ v[a]);
    // We will only create a linear constraint here and drag it along into the table,
    // but will have to create aux

    // we will perform tri-addition and chunk `a + b + message[0]`
    let mut a_chunks_and_constraints = vec![];
    {
        // for such addition we need at most 2 carries in low and in high
        let carries_low: [Variable; 2] =
            std::array::from_fn(|_| cs.add_boolean_variable().get_variable().unwrap());
        let carries_high: [Variable; 2] =
            std::array::from_fn(|_| cs.add_boolean_variable().get_variable().unwrap());

        for i in 0..2 {
            let addition_result_chunks: [Variable; 1] = std::array::from_fn(|_| cs.add_variable());
            let a_constraint = a[i].clone();
            assert_eq!(a_constraint.degree(), 1);

            // println!("v[a].wrapping_add(v[b]).wrapping_add(x) part {}", i);

            {
                let inputs: [&[(usize, Variable)]; 2] = [&b[i][..], &[(16, x[i])][..]];
                let output_chunks = [(8, addition_result_chunks[0])];

                if i == 0 {
                    witness_eval_addition_with_constraint(
                        cs,
                        a_constraint.clone(),
                        inputs,
                        [],
                        carries_low,
                        output_chunks,
                    );
                } else {
                    witness_eval_addition_with_constraint(
                        cs,
                        a_constraint.clone(),
                        inputs,
                        carries_low,
                        carries_high,
                        output_chunks,
                    );
                }
            };

            let carries_in = if i == 0 { &[][..] } else { &carries_low[..] };
            let carries_out = if i == 0 {
                &carries_low[..]
            } else {
                &carries_high[..]
            };

            // and now we should produce linear constraint for single chunk, that is linear constraint and will go into the table as-is
            let mut constraint = a_constraint;
            constraint = add_chunks_into_constraint(constraint, &b[i]);
            constraint += Term::from(x[i]);
            constraint = add_carries_into_constraint(constraint, &carries_in);
            constraint = sub_carries_from_constraint(constraint, &carries_out);

            let new_a_constraint = constraint.clone();

            // now we can subtract chunks for lookup relation
            // subtract chunks
            // MARIO: this is the 1 less chunk trick here, i.e. we split a u16 constraint into var+constraint u8 chunks. we do this optimisation everywhere
            constraint -= Term::from(addition_result_chunks[0]);
            // and scale
            constraint.scale(F::from_u32_unchecked(1 << 8).inverse().unwrap());

            a_chunks_and_constraints.push(([(8, addition_result_chunks[0])], constraint));

            // and overwrite
            a[i] = new_a_constraint;
        }
    }

    // now we need to re-chunk `d` if needed and xor-rotate it with result of a above
    // we have two cases for `d` here:
    // - it comes from the input and it's 16 bit pieces
    // - it comes from previous mixing round, and it's 8-bit chunk
    {
        let mut d_not_yet_rotated = vec![];
        if d[0].len() == 1 {
            for i in 0..2 {
                // println!("v[d] = rotate_right::<16>(v[d] ^ v[a]) part {}", i);

                let (width, var) = d[i][0];
                assert_eq!(width, 16);

                let (a_chunks, a_remaining_constraint) = a_chunks_and_constraints[i].clone();
                assert_eq!(a_chunks.len(), 1);
                assert_eq!(a_chunks[0].0, 8);
                assert_eq!(a_remaining_constraint.degree(), 1);

                let low_chunk = cs.add_variable();

                let value_fn = move |placer: &mut CS::WitnessPlacer| {
                    let value = placer.get_u16(var);
                    let low_chunk_value = value.get_lowest_bits(8);

                    placer.assign_u16(low_chunk, &low_chunk_value);
                };
                cs.set_values(value_fn);

                let mut constraint = Constraint::<F>::empty();
                constraint += Term::from(var);
                constraint -= Term::from(low_chunk);
                constraint.scale(F::from_u32_unchecked(1 << 8).inverse().unwrap());

                // and xor
                let [low_xor_result] = cs.get_variables_from_lookup_constrained::<2, 1>(
                    &[
                        LookupInput::Variable(low_chunk),
                        LookupInput::Variable(a_chunks[0].1),
                    ],
                    TableType::Xor,
                );
                let [xor_result_high] = cs.get_variables_from_lookup_constrained::<2, 1>(
                    &[
                        LookupInput::from(constraint),
                        LookupInput::from(a_remaining_constraint),
                    ],
                    TableType::Xor,
                );

                d_not_yet_rotated.push(low_xor_result);
                d_not_yet_rotated.push(xor_result_high);
            }
        } else {
            assert_eq!(d[0].len(), 2);
            assert_eq!(d.len(), a_chunks_and_constraints.len());
            // we are already set
            for i in 0..2 {
                // println!("v[d] = rotate_right::<16>(v[d] ^ v[a]) part {}", i);

                let (a_chunks, a_remaining_constraint) = a_chunks_and_constraints[i].clone();
                assert_eq!(a_chunks.len(), 1);
                assert_eq!(a_chunks[0].0, 8);
                assert_eq!(a_remaining_constraint.degree(), 1);

                let (width, var) = d[i][0];
                assert_eq!(width, 8);
                let [low_xor_result] = cs.get_variables_from_lookup_constrained::<2, 1>(
                    &[
                        LookupInput::Variable(var),
                        LookupInput::Variable(a_chunks[0].1),
                    ],
                    TableType::Xor,
                );

                let (width, var) = d[i][1];
                assert_eq!(width, 8);
                let [xor_result_high] = cs.get_variables_from_lookup_constrained::<2, 1>(
                    &[
                        LookupInput::Variable(var),
                        LookupInput::from(a_remaining_constraint),
                    ],
                    TableType::Xor,
                );

                d_not_yet_rotated.push(low_xor_result);
                d_not_yet_rotated.push(xor_result_high);
            }
        }
        assert_eq!(d_not_yet_rotated.len(), 4);

        // rotate by 16
        *d = [
            vec![(8, d_not_yet_rotated[2]), (8, d_not_yet_rotated[3])],
            vec![(8, d_not_yet_rotated[0]), (8, d_not_yet_rotated[1])],
        ];
    }

    // v[c] = v[c].wrapping_add(v[d]);
    // v[b] = rotate_right::<12>(v[b] ^ v[c]);

    // Here we will use 5 + 7 + 4 decomposition for XOR-rotate by 12

    // `d` at this point is always chunked, but `c` is always carried in as a constraint
    let mut c_chunks_and_constraints = vec![];
    {
        // for such addition we need at most 1 carriy in low and in high
        let carries_low: [Variable; 1] =
            std::array::from_fn(|_| cs.add_boolean_variable().get_variable().unwrap());
        let carries_high: [Variable; 1] =
            std::array::from_fn(|_| cs.add_boolean_variable().get_variable().unwrap());

        for i in 0..2 {
            // println!("v[c] = v[c].wrapping_add(v[d]) part {}", i);

            assert_eq!(d[i].len(), 2);

            let addition_result_chunks: [Variable; 2] = std::array::from_fn(|_| cs.add_variable());
            let c_constraint = c[i].clone();
            assert_eq!(c_constraint.degree(), 1);

            {
                let inputs: [&[(usize, Variable)]; 1] = [&d[i][..]];
                let output_chunks = [
                    (3, addition_result_chunks[0]),
                    (9, addition_result_chunks[1]),
                ];

                if i == 0 {
                    witness_eval_addition_with_constraint(
                        cs,
                        c_constraint.clone(),
                        inputs,
                        [],
                        carries_low,
                        output_chunks,
                    );
                } else {
                    witness_eval_addition_with_constraint(
                        cs,
                        c_constraint.clone(),
                        inputs,
                        carries_low,
                        carries_high,
                        output_chunks,
                    );
                }
            };

            let carries_in = if i == 0 { &[][..] } else { &carries_low[..] };
            let carries_out = if i == 0 {
                &carries_low[..]
            } else {
                &carries_high[..]
            };

            // and now we should produce linear constraint for single chunk, that is linear constraint and will go into the table as-is
            let mut constraint = c_constraint;
            constraint = add_chunks_into_constraint(constraint, &d[i]);
            constraint = add_carries_into_constraint(constraint, &carries_in);
            constraint = sub_carries_from_constraint(constraint, &carries_out);

            let new_c_constraint = constraint.clone();

            // now we can subtract chunks for lookup relation
            // subtract chunks
            constraint -= Term::from(addition_result_chunks[0]);
            constraint -= Term::from((F::from_u32_unchecked(1 << 3), addition_result_chunks[1]));
            // and scale
            constraint.scale(F::from_u32_unchecked(1 << 12).inverse().unwrap());

            c_chunks_and_constraints.push((
                [
                    (3, addition_result_chunks[0]),
                    (9, addition_result_chunks[1]),
                ],
                constraint,
            ));

            // and overwrite
            c[i] = new_c_constraint;
        }
    }

    // now we need to re-chunk `b` if needed and xor-rotate it with result of a above
    // we have two cases for `b` here:
    // - it comes from the input and it's 16 bit pieces
    // - it comes from previous mixing round, and it's 9 + 7 chunks, but it's not matching for our XOR-rot by 12,
    // so we will need to re-chunk
    {
        let mut b_not_yet_rotated = vec![];
        if b[0].len() == 1 {
            // `b` came yet from the input
            for i in 0..2 {
                // println!("v[b] = rotate_right::<12>(v[b] ^ v[c]) part {}", i);

                let (width, var) = b[i][0];
                assert_eq!(width, 16);

                let (c_chunks, c_remaining_constraint) = c_chunks_and_constraints[i].clone();
                assert_eq!(c_chunks.len(), 2);
                assert_eq!(c_chunks[0].0, 3);
                assert_eq!(c_chunks[1].0, 9);
                assert_eq!(c_remaining_constraint.degree(), 1);

                let chunk_3 = cs.add_variable();
                let chunk_9 = cs.add_variable();

                let value_fn = move |placer: &mut CS::WitnessPlacer| {
                    let mut value = placer.get_u16(var);
                    let chunk_3_value = value.get_lowest_bits(3);
                    value = value.shr(3);
                    let chunk_9_value = value.get_lowest_bits(9);

                    placer.assign_u16(chunk_3, &chunk_3_value);
                    placer.assign_u16(chunk_9, &chunk_9_value);
                };
                cs.set_values(value_fn);

                let mut constraint = Constraint::<F>::empty();
                constraint += Term::from(var);
                constraint -= Term::from(chunk_3);
                constraint -= Term::from((F::from_u32_unchecked(1 << 3), chunk_9));
                constraint.scale(F::from_u32_unchecked(1 << 12).inverse().unwrap());

                // and xor
                let [xor_result_3] = cs.get_variables_from_lookup_constrained::<2, 1>(
                    &[
                        LookupInput::Variable(chunk_3),
                        LookupInput::Variable(c_chunks[0].1),
                    ],
                    TableType::Xor3,
                );
                let [xor_result_9] = cs.get_variables_from_lookup_constrained::<2, 1>(
                    &[
                        LookupInput::Variable(chunk_9),
                        LookupInput::Variable(c_chunks[1].1),
                    ],
                    TableType::Xor9,
                );
                let [xor_result_4] = cs.get_variables_from_lookup_constrained::<2, 1>(
                    &[
                        LookupInput::from(constraint),
                        LookupInput::from(c_remaining_constraint),
                    ],
                    TableType::Xor4,
                );

                b_not_yet_rotated.push(xor_result_3);
                b_not_yet_rotated.push(xor_result_9);
                b_not_yet_rotated.push(xor_result_4);
            }
        } else {
            // `b` came from previous mixing round
            assert_eq!(b[0].len(), 2);
            assert_eq!(b.len(), c_chunks_and_constraints.len());
            // we are already set
            for i in 0..2 {
                // println!("v[b] = rotate_right::<12>(v[b] ^ v[c]) part {}", i);

                let (b_low_width, b_low_var) = b[i][0];
                let (b_high_width, b_high_var) = b[i][1];

                assert_eq!(b_low_width, 9);
                assert_eq!(b_high_width, 7);

                let (c_chunks, c_remaining_constraint) = c_chunks_and_constraints[i].clone();
                assert_eq!(c_chunks.len(), 2);
                assert_eq!(c_chunks[0].0, 3);
                assert_eq!(c_chunks[1].0, 9);
                assert_eq!(c_remaining_constraint.degree(), 1);

                let [chunk_3, chunk_9]: [Variable; 2] = std::array::from_fn(|_| cs.add_variable());
                let inputs: [&[(usize, Variable)]; 1] = [&b[i][..]];
                let output_chunks = [(3, chunk_3), (9, chunk_9)];

                // re-chunk b, as it's in the wrong order. Done by using 2 extra variables
                witness_eval_addition_with_constraint(
                    cs,
                    Constraint::empty(),
                    inputs,
                    [],
                    [],
                    output_chunks,
                );

                let mut constraint = Constraint::<F>::empty();
                constraint += Term::from(b_low_var);
                constraint += Term::from((F::from_u32_unchecked(1 << 9), b_high_var));
                constraint -= Term::from(chunk_3);
                constraint -= Term::from((F::from_u32_unchecked(1 << 3), chunk_9));
                constraint.scale(F::from_u32_unchecked(1 << 12).inverse().unwrap());

                // and xor
                let [xor_result_3] = cs.get_variables_from_lookup_constrained::<2, 1>(
                    &[
                        LookupInput::Variable(chunk_3),
                        LookupInput::Variable(c_chunks[0].1),
                    ],
                    TableType::Xor3,
                );
                let [xor_result_9] = cs.get_variables_from_lookup_constrained::<2, 1>(
                    &[
                        LookupInput::Variable(chunk_9),
                        LookupInput::Variable(c_chunks[1].1),
                    ],
                    TableType::Xor9,
                );
                let [xor_result_4] = cs.get_variables_from_lookup_constrained::<2, 1>(
                    &[
                        LookupInput::from(constraint),
                        LookupInput::from(c_remaining_constraint),
                    ],
                    TableType::Xor4,
                );

                b_not_yet_rotated.push(xor_result_3);
                b_not_yet_rotated.push(xor_result_9);
                b_not_yet_rotated.push(xor_result_4);
            }
        }
        assert_eq!(b_not_yet_rotated.len(), 6);

        // rotate by 12
        *b = [
            vec![
                (4, b_not_yet_rotated[2]),
                (3, b_not_yet_rotated[3]),
                (9, b_not_yet_rotated[4]),
            ],
            vec![
                (4, b_not_yet_rotated[5]),
                (3, b_not_yet_rotated[0]),
                (9, b_not_yet_rotated[1]),
            ],
        ];
    }

    // now it's much easier because it's basically all the same, but we have good properties due to our decompositions above

    // v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    // v[d] = rotate_right::<8>(v[d] ^ v[a]);

    let mut a_chunks_and_constraints = vec![];
    {
        // for such addition we need at most 2 carries in low and in high
        let carries_low: [Variable; 2] =
            std::array::from_fn(|_| cs.add_boolean_variable().get_variable().unwrap());
        let carries_high: [Variable; 2] =
            std::array::from_fn(|_| cs.add_boolean_variable().get_variable().unwrap());

        for i in 0..2 {
            // println!("v[a] = v[a].wrapping_add(v[b]).wrapping_add(y) part {}", i);

            let addition_result_chunks: [Variable; 1] = std::array::from_fn(|_| cs.add_variable());
            let a_constraint = a[i].clone();
            assert_eq!(a_constraint.degree(), 1);

            {
                let inputs: [&[(usize, Variable)]; 2] = [&b[i][..], &[(16, y[i])][..]];
                let output_chunks = [(8, addition_result_chunks[0])];

                if i == 0 {
                    witness_eval_addition_with_constraint(
                        cs,
                        a_constraint.clone(),
                        inputs,
                        [],
                        carries_low,
                        output_chunks,
                    );
                } else {
                    witness_eval_addition_with_constraint(
                        cs,
                        a_constraint.clone(),
                        inputs,
                        carries_low,
                        carries_high,
                        output_chunks,
                    );
                }
            };

            let carries_in = if i == 0 { &[][..] } else { &carries_low[..] };
            let carries_out = if i == 0 {
                &carries_low[..]
            } else {
                &carries_high[..]
            };

            // and now we should produce linear constraint for single chunk, that is linear constraint and will go into the table as-is
            let mut constraint = a_constraint;
            constraint = add_chunks_into_constraint(constraint, &b[i]);
            constraint += Term::from(y[i]);
            constraint = add_carries_into_constraint(constraint, &carries_in);
            constraint = sub_carries_from_constraint(constraint, &carries_out);

            let new_a_constraint = constraint.clone();

            // now we can subtract chunks for lookup relation
            // subtract chunks
            constraint -= Term::from(addition_result_chunks[0]);
            // and scale
            constraint.scale(F::from_u32_unchecked(1 << 8).inverse().unwrap());

            a_chunks_and_constraints.push(([(8, addition_result_chunks[0])], constraint));

            // and overwrite
            a[i] = new_a_constraint;
        }
    }

    {
        let mut d_not_yet_rotated = vec![];
        assert_eq!(d[0].len(), 2);
        assert_eq!(d.len(), a_chunks_and_constraints.len());
        // we are already set
        for i in 0..2 {
            // println!("v[d] = rotate_right::<8>(v[d] ^ v[a]) part {}", i);

            let (a_chunks, a_remaining_constraint) = a_chunks_and_constraints[i].clone();
            assert_eq!(a_chunks.len(), 1);
            assert_eq!(a_chunks[0].0, 8);
            assert_eq!(a_remaining_constraint.degree(), 1);

            let (width, var) = d[i][0];
            assert_eq!(width, 8);
            let [low_xor_result] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    LookupInput::Variable(var),
                    LookupInput::Variable(a_chunks[0].1),
                ],
                TableType::Xor,
            );

            let (width, var) = d[i][1];
            assert_eq!(width, 8);
            let [xor_result_high] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    LookupInput::Variable(var),
                    LookupInput::from(a_remaining_constraint),
                ],
                TableType::Xor,
            );

            d_not_yet_rotated.push(low_xor_result);
            d_not_yet_rotated.push(xor_result_high);
        }
        assert_eq!(d_not_yet_rotated.len(), 4);

        // rotate by 8
        *d = [
            vec![(8, d_not_yet_rotated[1]), (8, d_not_yet_rotated[2])],
            vec![(8, d_not_yet_rotated[3]), (8, d_not_yet_rotated[0])],
        ];
    }

    // v[c] = v[c].wrapping_add(v[d]);
    // v[b] = rotate_right::<7>(v[b] ^ v[c]);

    // Here we make chunks of 7 + 9
    let mut c_chunks_and_constraints = vec![];
    {
        // for such addition we need at most 1 carriy in low and in high
        let carries_low: [Variable; 1] =
            std::array::from_fn(|_| cs.add_boolean_variable().get_variable().unwrap());
        let carries_high: [Variable; 1] =
            std::array::from_fn(|_| cs.add_boolean_variable().get_variable().unwrap());

        for i in 0..2 {
            // println!("v[c] = v[c].wrapping_add(v[d]) part {}", i);

            assert_eq!(d[i].len(), 2);

            let addition_result_chunks: [Variable; 1] = std::array::from_fn(|_| cs.add_variable());
            let c_constraint = c[i].clone();
            assert_eq!(c_constraint.degree(), 1);

            {
                let inputs: [&[(usize, Variable)]; 1] = [&d[i][..]];
                let output_chunks = [(7, addition_result_chunks[0])];

                if i == 0 {
                    witness_eval_addition_with_constraint(
                        cs,
                        c_constraint.clone(),
                        inputs,
                        [],
                        carries_low,
                        output_chunks,
                    );
                } else {
                    witness_eval_addition_with_constraint(
                        cs,
                        c_constraint.clone(),
                        inputs,
                        carries_low,
                        carries_high,
                        output_chunks,
                    );
                }
            };

            let carries_in = if i == 0 { &[][..] } else { &carries_low[..] };
            let carries_out = if i == 0 {
                &carries_low[..]
            } else {
                &carries_high[..]
            };

            // and now we should produce linear constraint for single chunk, that is linear constraint and will go into the table as-is
            let mut constraint = c_constraint;
            constraint = add_chunks_into_constraint(constraint, &d[i]);
            constraint = add_carries_into_constraint(constraint, &carries_in);
            constraint = sub_carries_from_constraint(constraint, &carries_out);

            let new_c_constraint = constraint.clone();

            // now we can subtract chunks for lookup relation
            // subtract chunks
            constraint -= Term::from(addition_result_chunks[0]);
            // and scale
            constraint.scale(F::from_u32_unchecked(1 << 7).inverse().unwrap());

            c_chunks_and_constraints.push(([(7, addition_result_chunks[0])], constraint));

            // and overwrite
            c[i] = new_c_constraint;
        }
    }

    {
        let mut b_not_yet_rotated = vec![];
        // `b` came from previous XOR-rotate right above
        assert_eq!(b[0].len(), 3);
        assert_eq!(c_chunks_and_constraints.len(), 2);
        // we are already set
        for i in 0..2 {
            // println!("v[b] = rotate_right::<7>(v[b] ^ v[c]) part {}", i);

            let (width_4, width_4_var) = b[i][0];
            let (width_3, width_3_var) = b[i][1];
            let (width_9, width_9_var) = b[i][2];

            assert_eq!(width_4, 4);
            assert_eq!(width_3, 3);
            assert_eq!(width_9, 9);

            let (c_chunks, c_remaining_constraint) = c_chunks_and_constraints[i].clone();
            assert_eq!(c_chunks.len(), 1);
            assert_eq!(c_chunks[0].0, 7);
            assert_eq!(c_remaining_constraint.degree(), 1);

            // we just use linear expressions and XOR
            let mut xor_7_constraint = Constraint::empty();
            xor_7_constraint += Term::from(width_4_var);
            xor_7_constraint += Term::from((F::from_u32_unchecked(1 << 4), width_3_var));

            let [xor_result_7] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    LookupInput::from(xor_7_constraint),
                    LookupInput::Variable(c_chunks[0].1),
                ],
                TableType::Xor7,
            );
            let [xor_result_9] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    LookupInput::Variable(width_9_var),
                    LookupInput::from(c_remaining_constraint),
                ],
                TableType::Xor9,
            );

            b_not_yet_rotated.push(xor_result_7);
            b_not_yet_rotated.push(xor_result_9);
        }
        assert_eq!(b_not_yet_rotated.len(), 4);

        // rotate by 7
        *b = [
            vec![(9, b_not_yet_rotated[1]), (7, b_not_yet_rotated[2])],
            vec![(9, b_not_yet_rotated[3]), (7, b_not_yet_rotated[0])],
        ];
    }

    let output = GFunctionIntermediateValues {
        a_var_chunks_and_constraint: a_chunks_and_constraints.try_into().unwrap(),
        c_var_chunks_and_constraint: c_chunks_and_constraints.try_into().unwrap(),
    };

    output
}

fn add_chunks_into_constraint<F: PrimeField>(
    mut constraint: Constraint<F>,
    chunks: &[(usize, Variable)],
) -> Constraint<F> {
    let mut shift = 0;
    for (width, var) in chunks.iter() {
        constraint += Term::from((F::from_u32_unchecked(1u32 << shift), *var));
        shift += *width;
    }

    constraint
}

fn add_carries_into_constraint<F: PrimeField>(
    mut constraint: Constraint<F>,
    carries: &[Variable],
) -> Constraint<F> {
    let mut shift = 0;
    for var in carries.iter() {
        constraint += Term::from((F::from_u32_unchecked(1u32 << shift), *var));
        shift += 1;
    }

    constraint
}

fn sub_carries_from_constraint<F: PrimeField>(
    mut constraint: Constraint<F>,
    carries: &[Variable],
) -> Constraint<F> {
    let mut shift = 16;
    for var in carries.iter() {
        constraint -= Term::from((F::from_u32_unchecked(1u32 << shift), *var));
        shift += 1;
    }

    constraint
}

fn witness_eval_addition_with_constraint<
    F: PrimeField,
    CS: Circuit<F>,
    const NUM_INPUTS: usize,
    const NUM_CARRIES_IN: usize,
    const NUM_CARRIES_OUT: usize,
    const OUTPUT_CHUNKS_TO_PRODUCE: usize,
>(
    cs: &mut CS,
    constraint: Constraint<F>,
    inputs: [&[(usize, Variable)]; NUM_INPUTS],
    carries_in: [Variable; NUM_CARRIES_IN],
    carries_out: [Variable; NUM_CARRIES_OUT],
    output_chunks: [(usize, Variable); OUTPUT_CHUNKS_TO_PRODUCE],
) {
    assert!(NUM_INPUTS > 0);
    assert!(NUM_INPUTS < 4);

    // TODO: constraint is just bit shifts + concatenations, so we can specialize for it if needed

    let (quadratic, linear, constant_coeff) = constraint.split_max_quadratic();
    assert!(quadratic.is_empty());
    if linear.len() == 0 {
        assert!(constant_coeff.is_zero());
    }

    let inputs = inputs.map(|el| el.to_vec());

    // add witness fn

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let mut input_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0u32);
        for input_decomposition in inputs.iter() {
            let mut shift = 0u32;
            for (chunk_width, variable) in input_decomposition.iter() {
                let value = placer.get_u16(*variable);
                let value = value.shl(shift as u32);
                let value = value.widen();
                // we have enough capacity to never overflow
                input_value.add_assign(&value);
                shift += *chunk_width as u32;
            }
        }

        let mut constraint_eval_result =
            <CS::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(constant_coeff);
        for (coeff, var) in linear.iter() {
            let a = placer.get_field(*var);
            let c = <CS::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(*coeff);
            constraint_eval_result.add_assign_product(&a, &c);
        }
        let constraint_eval_result = constraint_eval_result.as_integer();
        input_value.add_assign(&constraint_eval_result);

        let mut shift = 0;
        for carry_in in carries_in.iter() {
            let carry_in = placer.get_boolean(*carry_in);
            let carry_in = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::from_mask(carry_in);
            let carry_in = carry_in.shl(shift);
            shift += 1;
            input_value.add_assign(&carry_in);
        }

        // now we should decompose into output chunks
        let mut result = input_value;
        let mut final_shift = 16u32;
        for (width, var) in output_chunks.iter() {
            let chunk = result.get_lowest_bits(*width as u32);
            result = result.shr(*width as u32);
            final_shift -= *width as u32;
            placer.assign_u16(*var, &chunk.truncate());
        }
        // and the rest are carries

        // NOTE: we didn't make top-most chunk, so we need to shift one more time before taking carries (bits 16 and higher)
        result = result.shr(final_shift);
        for carry_out in carries_out.iter() {
            let bit = result.get_bit(0);
            result = result.shr(1u32);
            placer.assign_mask(*carry_out, &bit);
        }
    };

    cs.set_values(value_fn);
}
