use super::*;
use crate::cs::utils::collapse_max_quadratic_constraint_into;
use crate::cs::utils::mask_by_boolean_into_accumulator_constraint;
use crate::cs::witness_placer::*;
use crate::definitions::LookupInput;
use crate::one_row_compiler::Variable;
use crate::types::Boolean;
use crate::types::Num;
use blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS;
use blake2s_u32::{IV, SIGMAS};

const MAX_ROUNDS: usize = 10;

// ABI:
// - 16 R/W words for state
// - 16 RO words for input block
// - 1 word for bitmask for round index

pub fn all_table_types() -> Vec<TableType> {
    vec![
        TableType::Xor,
        TableType::Xor3,
        TableType::Xor4,
        TableType::Xor7,
        TableType::Xor9,
    ]
}

pub fn blake2_single_round_delegation_circuit_create_table_driver<F: PrimeField>() -> TableDriver<F>
{
    let mut table_driver = TableDriver::new();
    for el in all_table_types() {
        table_driver.materialize_table(el);
    }

    table_driver
}

pub fn materialize_tables_into_cs<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    for el in all_table_types() {
        cs.materialize_table(el);
    }
}

pub fn define_blake2_single_round_delegation_circuit<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
) -> Vec<[Variable; 2]> {
    // add tables
    materialize_tables_into_cs(cs);

    // the only convention we must eventually satisfy is that if we do NOT process delegation request,
    // then all memory writes in ABI must be 0s

    let _execute = cs.process_delegation_request();

    let mut rw_markers = vec![];
    // first 16 elements are overwritten
    rw_markers.resize(16, true);
    // then readonly
    rw_markers.resize(16 + 16 + 1, false);

    let mem_accesses = cs.create_batched_memory_accesses(&rw_markers);
    let mut it = mem_accesses.into_iter();

    let mut input_state = vec![];
    let mut output_placeholder_state = vec![];
    for _ in 0..16 {
        let BatchedMemoryAccessType::Write {
            read_value,
            write_value,
        } = it.next().unwrap()
        else {
            panic!()
        };

        input_state.push(read_value);
        output_placeholder_state.push(write_value);
    }

    let mut data_to_absorb = vec![];
    for _ in 0..16 {
        let BatchedMemoryAccessType::Read { read_value } = it.next().unwrap() else {
            panic!()
        };

        data_to_absorb.push(read_value);
    }

    let BatchedMemoryAccessType::Read { read_value } = it.next().unwrap() else {
        panic!()
    };
    let round_bitmask = read_value;

    assert!(it.next().is_none());

    // we can immediately boolean decompose round bitmask's low, and ignore high

    {
        for (i, input) in input_state.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("State element {} = 0x{:08x}", i, value);
            }
        }

        for (i, input) in data_to_absorb.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("Input message element {} = 0x{:08x}", i, value);
            }
        }

        let register = Register::<F>(round_bitmask.map(|el| Num::Var(el)));
        if let Some(value) = register.get_value_unsigned(&*cs) {
            println!("Round bitmask = 0b{:b}", value);
        }
    }

    let round_bitmask =
        Boolean::split_into_bitmask::<F, CS, MAX_ROUNDS>(cs, Num::Var(round_bitmask[0]));

    {
        for (i, el) in round_bitmask.iter().enumerate() {
            if let Some(value) = el.get_value(&*cs) {
                println!("Round bitmask element {} = {}", i, value);
            }
        }
    }
    // now we perform ABI logic convention

    // - if round == 0 (round_bitmask[0] is set) then we overwrite elements 8..12, 13 and 15 of the state

    let first_round = round_bitmask[0];
    for i in [8, 9, 10, 11, 13, 15] {
        let existing = input_state[i];
        let selected_0 = cs.choose(
            first_round,
            Num::Constant(F::from_u64_unchecked(IV[i - 8] as u64 & 0xffff)),
            Num::Var(existing[0]),
        );
        let selected_1 = cs.choose(
            first_round,
            Num::Constant(F::from_u64_unchecked((IV[i - 8] as u64) >> 16)),
            Num::Var(existing[1]),
        );

        input_state[i] = [selected_0.get_variable(), selected_1.get_variable()];
    }

    {
        for (i, input) in input_state.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("State element after masking {} = 0x{:08x}", i, value);
            }
        }
    }

    // now we should select a fixed permutation of the message words

    let mut selected_permutation = vec![];
    for message_word in 0..BLAKE2S_BLOCK_SIZE_U32_WORDS {
        // our permutation is fixed, so we just need to make a constraint
        let mut constraint_0 = Constraint::empty();
        let mut constraint_1 = Constraint::empty();
        for round_index in 0..MAX_ROUNDS {
            let selector = round_bitmask[round_index];
            let inputs = data_to_absorb[SIGMAS[round_index][message_word]];
            constraint_0 = mask_by_boolean_into_accumulator_constraint(
                &selector,
                &Num::Var(inputs[0]),
                constraint_0,
            );
            constraint_1 = mask_by_boolean_into_accumulator_constraint(
                &selector,
                &Num::Var(inputs[1]),
                constraint_1,
            );
        }
        let low = cs.add_variable_from_constraint(constraint_0);
        let high = cs.add_variable_from_constraint(constraint_1);

        selected_permutation.push([low, high]);
    }

    assert_eq!(selected_permutation.len(), 16);

    {
        for (i, input) in selected_permutation.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("Permuted input message element {} = 0x{:08x}", i, value);
            }
        }
    }

    let state: Vec<_> = input_state
        .into_iter()
        .map(|el| el.map(|el| vec![(16, el)]))
        .collect();

    let a_row: [_; 4] = state[0..4].to_vec().try_into().unwrap();
    let mut a_row = a_row.map(|el| {
        el.map(|el| {
            assert_eq!(el.len(), 1);
            let mut constraint = Constraint::<F>::empty();
            constraint += Term::from(el[0].1);

            constraint
        })
    });
    let mut b_row: [_; 4] = state[4..8].to_vec().try_into().unwrap();
    let c_row: [_; 4] = state[8..12].to_vec().try_into().unwrap();
    let mut c_row = c_row.map(|el| {
        el.map(|el| {
            assert_eq!(el.len(), 1);
            let mut constraint = Constraint::<F>::empty();
            constraint += Term::from(el[0].1);

            constraint
        })
    });
    let mut d_row: [_; 4] = state[12..16].to_vec().try_into().unwrap();

    g_function(
        cs,
        &mut a_row[0],
        &mut b_row[0],
        &mut c_row[0],
        &mut d_row[0],
        [selected_permutation[0], selected_permutation[1]],
    );

    g_function(
        cs,
        &mut a_row[1],
        &mut b_row[1],
        &mut c_row[1],
        &mut d_row[1],
        [selected_permutation[2], selected_permutation[3]],
    );

    g_function(
        cs,
        &mut a_row[2],
        &mut b_row[2],
        &mut c_row[2],
        &mut d_row[2],
        [selected_permutation[4], selected_permutation[5]],
    );

    g_function(
        cs,
        &mut a_row[3],
        &mut b_row[3],
        &mut c_row[3],
        &mut d_row[3],
        [selected_permutation[6], selected_permutation[7]],
    );

    // shift

    g_function(
        cs,
        &mut a_row[0],
        &mut b_row[1],
        &mut c_row[2],
        &mut d_row[3],
        [selected_permutation[8], selected_permutation[9]],
    );

    g_function(
        cs,
        &mut a_row[1],
        &mut b_row[2],
        &mut c_row[3],
        &mut d_row[0],
        [selected_permutation[10], selected_permutation[11]],
    );

    g_function(
        cs,
        &mut a_row[2],
        &mut b_row[3],
        &mut c_row[0],
        &mut d_row[1],
        [selected_permutation[12], selected_permutation[13]],
    );

    g_function(
        cs,
        &mut a_row[3],
        &mut b_row[0],
        &mut c_row[1],
        &mut d_row[2],
        [selected_permutation[14], selected_permutation[15]],
    );

    // now we should re-assemble it into output

    // NOTE on final masking: we do NOT need to mask anything here based on the execute/not predicate,
    // because if we do not execute, circuit guarantees that all read values are 0, so we will get 0 at the end here

    let mut it = output_placeholder_state.iter_mut();

    for src in a_row.into_iter() {
        let dst = it.next().unwrap();
        for (src, dst) in src.into_iter().zip(dst.iter_mut()) {
            let mut constraint = src;
            // set value
            collapse_max_quadratic_constraint_into(cs, constraint.clone(), *dst);
            // add constraint
            constraint -= Term::from(*dst);
            cs.add_constraint_allow_explicit_linear(constraint);
        }
    }

    for src in b_row.into_iter() {
        let dst = it.next().unwrap();
        for (src, dst) in src.into_iter().zip(dst.iter_mut()) {
            let mut constraint = Constraint::empty();
            let mut shift = 0;
            for (width, var) in src.into_iter() {
                constraint += Term::from((F::from_u64_unchecked(1u64 << shift), var));
                shift += width;
            }
            // set value
            collapse_max_quadratic_constraint_into(cs, constraint.clone(), *dst);
            // add constraint
            constraint -= Term::from(*dst);
            cs.add_constraint_allow_explicit_linear(constraint);
        }
    }

    for src in c_row.into_iter() {
        let dst = it.next().unwrap();
        for (src, dst) in src.into_iter().zip(dst.iter_mut()) {
            let mut constraint = src;
            // set value
            collapse_max_quadratic_constraint_into(cs, constraint.clone(), *dst);
            // add constraint
            constraint -= Term::from(*dst);
            cs.add_constraint_allow_explicit_linear(constraint);
        }
    }

    for src in d_row.into_iter() {
        let dst = it.next().unwrap();
        for (src, dst) in src.into_iter().zip(dst.iter_mut()) {
            let mut constraint = Constraint::empty();
            let mut shift = 0;
            for (width, var) in src.into_iter() {
                constraint += Term::from((F::from_u64_unchecked(1u64 << shift), var));
                shift += width;
            }
            // set value
            collapse_max_quadratic_constraint_into(cs, constraint.clone(), *dst);
            // add constraint
            constraint -= Term::from(*dst);
            cs.add_constraint_allow_explicit_linear(constraint);
        }
    }

    assert!(it.next().is_none());

    {
        for (i, input) in output_placeholder_state.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("Output state element {} = 0x{:08x}", i, value);
            }
        }
    }

    output_placeholder_state
}

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
            constraint.scale(F::from_u64_unchecked(1 << 8).inverse().unwrap());

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
                constraint.scale(F::from_u64_unchecked(1 << 8).inverse().unwrap());

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
            constraint -= Term::from((F::from_u64_unchecked(1 << 3), addition_result_chunks[1]));
            // and scale
            constraint.scale(F::from_u64_unchecked(1 << 12).inverse().unwrap());

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
                constraint -= Term::from((F::from_u64_unchecked(1 << 3), chunk_9));
                constraint.scale(F::from_u64_unchecked(1 << 12).inverse().unwrap());

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
                constraint += Term::from((F::from_u64_unchecked(1 << 9), b_high_var));
                constraint -= Term::from(chunk_3);
                constraint -= Term::from((F::from_u64_unchecked(1 << 3), chunk_9));
                constraint.scale(F::from_u64_unchecked(1 << 12).inverse().unwrap());

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
            constraint.scale(F::from_u64_unchecked(1 << 8).inverse().unwrap());

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
            constraint.scale(F::from_u64_unchecked(1 << 7).inverse().unwrap());

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
            // we just use linear expressions and XOR
            let mut xor_7_constraint = Constraint::empty();
            xor_7_constraint += Term::from(width_4_var);
            xor_7_constraint += Term::from((F::from_u64_unchecked(1 << 4), width_3_var));

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
        constraint += Term::from((F::from_u64_unchecked(1u64 << shift), *var));
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
        constraint += Term::from((F::from_u64_unchecked(1u64 << shift), *var));
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
        constraint -= Term::from((F::from_u64_unchecked(1u64 << shift), *var));
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
        use crate::cs::witness_placer::*;

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

// // We should assign booleans, and parse from constants what are our chunks and their shifts.
// // We will assign output boolean carries, and chunk variables of the output
// fn choose_witness_gen_function_for_addition_with_constraint<
//     F: PrimeField,
//     const NUM_INPUTS: usize,
//     const NUM_CARRIES_IN: usize,
//     const NUM_CARRIES_OUT: usize,
//     const OUTPUT_CHUNKS_TO_PRODUCE: usize,
// >(
//     (inputs_0_chunks, inputs_1_chunks, inputs_2_chunks): (usize, usize, usize),
//     num_linear_terms_in_constraint: usize,
// ) -> fn(WitnessGenSource<'_, F>, WitnessGenDest<'_, F>, &[F], &TableDriver<F>, TableType) {
//     assert!(NUM_INPUTS > 0);
//     assert!(NUM_INPUTS < 4);
//     assert!(inputs_0_chunks > 0);

//     match NUM_INPUTS {
//         1 => {}
//         2 => {
//             assert!(inputs_1_chunks > 0);
//         }
//         3 => {
//             assert!(inputs_1_chunks > 0);
//             assert!(inputs_2_chunks > 0);
//         }
//         _ => unreachable!(),
//     }

//     seq_macro::seq!(N in 1..4 {
//         if inputs_0_chunks == N {
//             if inputs_1_chunks == 0 {
//                 assert!(inputs_2_chunks == 0);
//                 super_seq_macro::seq!(L in [0, 1, 4, 5, 7, 9, 10, 13] {
//                     if num_linear_terms_in_constraint == L {
//                         return witness_gen_function_for_addition_with_constraint_inner::<F, NUM_INPUTS, N, 0, 0, L, NUM_CARRIES_IN, NUM_CARRIES_OUT, OUTPUT_CHUNKS_TO_PRODUCE>;
//                     }
//                 });

//                 panic!("unsupported number of linear terms in constraint: {}", num_linear_terms_in_constraint);
//             } else {
//                 if inputs_2_chunks == 0 {
//                     seq_macro::seq!(M in 1..4 {
//                         if inputs_1_chunks == M {
//                             super_seq_macro::seq!(L in [0, 1, 5, 7, 11, 15, 16, 22] {
//                                 if num_linear_terms_in_constraint == L {
//                                     return witness_gen_function_for_addition_with_constraint_inner::<F, NUM_INPUTS, N, M, 0, L, NUM_CARRIES_IN, NUM_CARRIES_OUT, OUTPUT_CHUNKS_TO_PRODUCE>;
//                                 }
//                             });

//                             panic!("unsupported number of linear terms in constraint: {}", num_linear_terms_in_constraint);
//                         }
//                     });

//                     panic!("unsupported number of input chunks for arg 1: {}", inputs_1_chunks);
//                 } else {
//                     seq_macro::seq!(M in 1..4 {
//                         if inputs_1_chunks == M {
//                             seq_macro::seq!(K in 1..4 {
//                                 if inputs_2_chunks == K {
//                                     super_seq_macro::seq!(L in [0] {
//                                         if num_linear_terms_in_constraint == L {
//                                             return witness_gen_function_for_addition_with_constraint_inner::<F, NUM_INPUTS, N, M, K, L, NUM_CARRIES_IN, NUM_CARRIES_OUT, OUTPUT_CHUNKS_TO_PRODUCE>;
//                                         }
//                                     });

//                                     panic!("unsupported number of linear terms in constraint: {}", num_linear_terms_in_constraint);
//                                 }
//                             });

//                             panic!("unsupported number of input chunks for arg 2: {}", inputs_2_chunks);
//                         }
//                     });
//                 }
//             }

//             panic!("unsupported number of input chunks for arg 1: {}", inputs_1_chunks);
//         }
//     });

//     panic!(
//         "unsupported number of input chunks for arg 0: {}",
//         inputs_0_chunks
//     );
// }

// fn witness_gen_function_for_addition_with_constraint_inner<
//     F: PrimeField,
//     const NUM_INPUTS: usize,
//     const INPUT_0_NUM_CHUNKS: usize,
//     const INPUT_1_NUM_CHUNKS: usize,
//     const INPUT_2_NUM_CHUNKS: usize,
//     const NUM_LINEAR_TERMS: usize,
//     const NUM_CARRIES_IN: usize,
//     const NUM_CARRIES_OUT: usize,
//     const OUTPUT_CHUNKS_TO_PRODUCE: usize,
// >(
//     inputs: WitnessGenSource<'_, F>,
//     mut outputs: WitnessGenDest<'_, F>,
//     constants: &[F],
//     _table_driver: &TableDriver<F>,
//     _table_type: TableType,
// ) {
//     assert!(NUM_INPUTS > 0);
//     assert!(NUM_INPUTS < 4);
//     let mut constants_it = constants.iter();
//     let mut result = 0u32;
//     let mut i = 0;
//     for input_idx in 0..NUM_INPUTS {
//         let num_chunks = match input_idx {
//             0 => INPUT_0_NUM_CHUNKS,
//             1 => INPUT_1_NUM_CHUNKS,
//             2 => INPUT_2_NUM_CHUNKS,
//             _ => unreachable!(),
//         };

//         let mut shift = 0;
//         for _ in 0..num_chunks {
//             let chunk_el = inputs[i].as_u64_reduced() as u32;
//             i += 1;
//             assert!(chunk_el < 1u32 << 16);
//             result += chunk_el << shift;
//             let chunk_width = constants_it.next().unwrap().as_u64_reduced() as usize;
//             shift += chunk_width
//         }
//     }

//     // now we can read number of carries-in and add them
//     for shift in 0..NUM_CARRIES_IN {
//         result += (inputs[i].as_boolean() as u32) << shift;
//         i += 1;
//     }

//     if NUM_LINEAR_TERMS > 0 {
//         let mut linear_constraint_contribution = *constants_it.next().unwrap();
//         for _ in 0..NUM_LINEAR_TERMS {
//             linear_constraint_contribution
//                 .add_assign_product(&inputs[i], constants_it.next().unwrap());
//             i += 1;
//         }

//         // compute result of the addition
//         let t = linear_constraint_contribution.as_u64_reduced();
//         assert!(t < 1 << 16);
//         result += t as u32;
//     }

//     let mut result_low = result as u16;
//     let mut result_high = result >> 16;

//     // assign carries
//     for i in 0..NUM_CARRIES_OUT {
//         let carry = result_high & 1 == 1;
//         result_high >>= 1;
//         outputs[i] = F::from_boolean(carry);
//     }
//     assert!(result_high == 0);

//     // now we should parse how many chunks we assign and what are their width
//     for i in 0..OUTPUT_CHUNKS_TO_PRODUCE {
//         let chunk_width = constants_it.next().unwrap().as_u64_reduced() as usize;
//         let chunk = result_low & ((1 << chunk_width) - 1);
//         outputs[NUM_CARRIES_OUT + i] = F::from_u64_unchecked(chunk as u64);
//         result_low >>= chunk_width;
//     }

//     assert!(constants_it.next().is_none());
// }

#[cfg(test)]
mod test {
    use super::*;
    use crate::cs::cs_reference::BasicAssembly;
    use crate::one_row_compiler::OneRowCompiler;
    use field::Mersenne31Field;

    #[ignore = "Fails with deprecated"]
    #[test]
    fn test_compile_blake2_single_round() {
        let mut cs = BasicAssembly::<Mersenne31Field>::new();
        define_blake2_single_round_delegation_circuit(&mut cs);
        let (circuit_output, _) = cs.finalize();
        dbg!(&circuit_output.lookups.len());
        let compiler = OneRowCompiler::default();
        let circuit = compiler.compile_to_evaluate_delegations(circuit_output, 20);
        dbg!(circuit.memory_layout.total_width);
        dbg!(circuit.witness_layout.total_width);
        dbg!(circuit.stage_2_layout.total_width);
    }

}
