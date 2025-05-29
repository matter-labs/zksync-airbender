use super::*;
use crate::cs::circuit::*;
use crate::cs::utils::collapse_max_quadratic_constraint_into;
use crate::cs::utils::mask_by_boolean_into_accumulator_constraint;
use crate::cs::witness_placer::WitnessComputationalInteger;
use crate::cs::witness_placer::WitnessPlacer;
use crate::delegation::blake2_single_round::g_function;
use crate::one_row_compiler::LookupInput;
use crate::one_row_compiler::Variable;
use crate::types::Boolean;
use crate::types::Num;
use blake2s_u32::state_with_extended_control_flags::*;
use blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS;
use blake2s_u32::CONFIGURED_IV;
use blake2s_u32::EXNTENDED_CONFIGURED_IV;
use blake2s_u32::SIGMAS;

const MAX_ROUNDS: usize = 10;
const NUM_CONTROL_BITS: usize = 3;

// ABI:
// - registers x10-x13 are used to pass the parameters
// - x10 and x11 are pointers: x10 is a pointer to 24 words of state + extended state, x11 is a pointer to the input to mix
// - x12 and x13 are control registers

pub fn all_table_types() -> Vec<TableType> {
    vec![
        TableType::Xor,
        TableType::Xor3,
        TableType::Xor4,
        TableType::Xor7,
        TableType::Xor9,
    ]
}

pub fn blake2_with_extended_control_delegation_circuit_create_table_driver<F: PrimeField>(
) -> TableDriver<F> {
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

pub fn define_blake2_with_extended_control_delegation_circuit<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
) -> (Vec<[Variable; 2]>, Vec<[Variable; 2]>) {
    // add tables
    materialize_tables_into_cs(cs);

    // the only convention we must eventually satisfy is that if we do NOT process delegation request,
    // then all memory writes in ABI must be 0s

    let _execute = cs.process_delegation_request();

    let x10_request = RegisterAccessRequest {
        register_index: 10,
        register_write: false,
        indirects_alignment_log2: 7, // 128 bytes - 32 + 64 for state and extended state are needed
        indirect_accesses: vec![true; 24],
    };

    let x11_request = RegisterAccessRequest {
        register_index: 11,
        register_write: false,
        indirects_alignment_log2: 2, // just aligned by machine words
        indirect_accesses: vec![false; 16],
    };

    let x12_request = RegisterAccessRequest {
        register_index: 12,
        register_write: false,
        indirects_alignment_log2: 0, // no indirects
        indirect_accesses: vec![],
    };

    let x13_request = RegisterAccessRequest {
        register_index: 13,
        register_write: false,
        indirects_alignment_log2: 0, // no indirects
        indirect_accesses: vec![],
    };

    let x10_and_indirects = cs.create_register_and_indirect_memory_accesses(x10_request);
    let x11_and_indirects = cs.create_register_and_indirect_memory_accesses(x11_request);
    let x12_and_indirects = cs.create_register_and_indirect_memory_accesses(x12_request);
    let x13_and_indirects = cs.create_register_and_indirect_memory_accesses(x13_request);

    assert_eq!(x10_and_indirects.indirect_accesses.len(), 24);
    assert_eq!(x11_and_indirects.indirect_accesses.len(), 16);
    assert!(x12_and_indirects.indirect_accesses.is_empty());
    assert!(x13_and_indirects.indirect_accesses.is_empty());

    let mut input_state = vec![];
    let mut output_placeholder_state = vec![];
    for i in 0..8 {
        let IndirectAccessType::Write {
            read_value,
            write_value,
        } = x10_and_indirects.indirect_accesses[i]
        else {
            panic!()
        };

        input_state.push(read_value);
        output_placeholder_state.push(write_value);
    }

    let mut input_extended_state = vec![];
    let mut output_placeholder_extended_state = vec![];
    for i in 8..24 {
        let IndirectAccessType::Write {
            read_value,
            write_value,
        } = x10_and_indirects.indirect_accesses[i]
        else {
            panic!()
        };

        input_extended_state.push(read_value);
        output_placeholder_extended_state.push(write_value);
    }

    let mut input_words = vec![];
    for i in 0..16 {
        let IndirectAccessType::Read { read_value } = x11_and_indirects.indirect_accesses[i] else {
            panic!()
        };

        input_words.push(read_value);
    }

    let round_bitmask = {
        let RegisterAccessType::Read { read_value } = x12_and_indirects.register_access else {
            panic!()
        };

        read_value
    };

    let control_mask = {
        let RegisterAccessType::Read { read_value } = x13_and_indirects.register_access else {
            panic!()
        };

        read_value
    };

    {
        for (i, input) in input_state.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("Input state element {} = 0x{:08x}", i, value);
            }
        }

        for (i, input) in input_extended_state.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("Input extended state element {} = 0x{:08x}", i, value);
            }
        }

        for (i, input) in input_words.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("Input message element {} = 0x{:08x}", i, value);
            }
        }

        let register = Register::<F>(round_bitmask.map(|el| Num::Var(el)));
        if let Some(value) = register.get_value_unsigned(&*cs) {
            println!("Round bitmask = 0b{:b}", value);
        }

        let register = Register::<F>(control_mask.map(|el| Num::Var(el)));
        if let Some(value) = register.get_value_unsigned(&*cs) {
            println!("Control bitmask = 0b{:b}", value);
        }
    }

    // we can immediately boolean decompose round bitmask's low, and ignore high, and same for control

    let round_bitmask =
        Boolean::split_into_bitmask::<F, CS, MAX_ROUNDS>(cs, Num::Var(round_bitmask[0]));
    let control_bitmask =
        Boolean::split_into_bitmask::<F, CS, NUM_CONTROL_BITS>(cs, Num::Var(control_mask[0]));

    {
        for (i, el) in round_bitmask.iter().enumerate() {
            if let Some(value) = el.get_value(&*cs) {
                println!("Round bitmask element {} = {}", i, value);
            }
        }

        // for (i, el) in control_bitmask.iter().enumerate() {
        //     if let Some(value) = el.get_value(&*cs) {
        //         println!("Control bitmask element {} = {}", i, value);
        //     }
        // }

        if let Some(value) = control_bitmask[LAST_ROUND_BIT_IDX].get_value(&*cs) {
            if value {
                println!("Control bitmask contains `last round`");
            }
        }

        if let Some(value) = control_bitmask[INPUT_IS_RIGHT_NODE_BIT_IDX].get_value(&*cs) {
            if value {
                println!("Control bitmask contains `input is right node`");
            }
        }

        if let Some(value) = control_bitmask[COMPRESSION_MODE_BIT_IDX].get_value(&*cs) {
            if value {
                println!("Control bitmask contains `compression mode`");
            }
        }
    }

    // now we perform ABI logic convention
    let perform_final_xor = control_bitmask[LAST_ROUND_BIT_IDX];
    let input_is_right_node = control_bitmask[INPUT_IS_RIGHT_NODE_BIT_IDX];
    let compression_mode = control_bitmask[COMPRESSION_MODE_BIT_IDX];

    // if round == 0, then
    // - first 8 elements of extended state are taken from IV for compression mode, or unchanged for normal mode
    // - elements 8-16 are either taken from extended ALWAYS, except for elements 12 and 14 - those are unchanged in normal mode, and reset in compression

    let first_round = round_bitmask[0];
    let first_round_var = first_round.get_variable().unwrap();
    let compression_mode_var = compression_mode.get_variable().unwrap();
    let first_round_in_normal_mode = Boolean::and(&first_round, &compression_mode.toggle(), cs);
    let first_round_in_normal_mode_var = first_round_in_normal_mode.get_variable().unwrap();

    // even though we can select first 8 words of the extended state using single quadratic constraint,
    // we will also select separately between constant IV and first 8 elements to use this later on in final XORing

    let mut state_for_final_xoring = vec![];

    for word_idx in 0..8 {
        let existing = &mut input_extended_state[word_idx];
        let state_word = input_state[word_idx];
        let initialization_word = CONFIGURED_IV[word_idx];
        let mut state_for_final_xoring_word = [Variable::placeholder_variable(); 2];
        for i in 0..2 {
            state_for_final_xoring_word[i] = cs
                .choose(
                    compression_mode,
                    Num::Constant(F::from_u64_unchecked(
                        ((initialization_word >> (16 * i)) & 0xffff) as u64,
                    )),
                    Num::Var(state_word[i]),
                )
                .get_variable();
            existing[i] = cs
                .choose(
                    first_round,
                    Num::Var(state_for_final_xoring_word[i]),
                    Num::Var(existing[i]),
                )
                .get_variable();
        }
        state_for_final_xoring.push(state_for_final_xoring_word);
    }

    for word_idx in [8, 9, 10, 11, 13, 15] {
        let existing = &mut input_extended_state[word_idx];
        let initialization_word = EXNTENDED_CONFIGURED_IV[word_idx];
        for i in 0..2 {
            let mut constraint = Constraint::empty();
            // if it's not the first round - keep existing
            constraint = constraint
                + (Term::from(1u64) - Term::from(first_round_var)) * Term::from(existing[i]);
            // otherwise - from constants
            constraint = constraint
                + Term::from(first_round_var)
                    * Term::from((initialization_word >> (16 * i)) as u64 & 0xffff);
            let selected = cs.add_variable_from_constraint(constraint);
            existing[i] = selected;
        }
    }

    for word_idx in [12, 14] {
        let existing = &mut input_extended_state[word_idx];
        let initialization_word = COMPRESSION_MODE_EXTENDED_CONFIGURED_IV[word_idx];
        for i in 0..2 {
            let mut constraint = Constraint::empty();
            // if it's not the first round - keep existing
            constraint = constraint
                + (Term::from(1u64) - Term::from(first_round_var)) * Term::from(existing[i]);
            // if not - two options
            // if it's a normal mode - then we take from existing extended(!) state
            constraint =
                constraint + Term::from(first_round_in_normal_mode_var) * Term::from(existing[i]);
            // otherwise - from constants
            constraint = constraint
                + Term::from(first_round_var)
                    * Term::from(compression_mode_var)
                    * Term::from((initialization_word >> (16 * i)) as u64 & 0xffff);
            let selected = cs.add_variable_from_constraint(constraint);
            existing[i] = selected;
        }
    }

    {
        for (i, input) in input_extended_state.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!(
                    "Extended state element after masking {} = 0x{:08x}",
                    i, value
                );
            }
        }
    }

    // now we should select the input to absorb:
    // - either it's existing input if it's normal mode
    // - otherwise in compression mode it would depend on the left/right flag

    let compression_mode_existing_is_right =
        Boolean::and(&compression_mode, &input_is_right_node, cs);
    let compression_mode_existing_is_left =
        Boolean::and(&compression_mode, &input_is_right_node.toggle(), cs);

    if let Some(value) = compression_mode_existing_is_left.get_value(&*cs) {
        println!(
            "Existing state elements will use used for compression mode as left node = {}",
            value
        );
    }

    if let Some(value) = compression_mode_existing_is_right.get_value(&*cs) {
        println!(
            "Existing state elements will use used for compression mode as right node = {}",
            value
        );
    }

    let input_state = input_state;
    // path element is always first 8 elements
    let input_as_witness_for_compression = input_words[..8].to_vec();

    for word_idx in 0..8 {
        let path_data = input_as_witness_for_compression[word_idx];
        let state_word = input_state[word_idx];

        let existing = &mut input_words[word_idx];

        for i in 0..2 {
            let mut constraint = Constraint::empty();
            // if it's not the first round - keep existing
            constraint = constraint
                + (Term::from(1u64) - Term::from(compression_mode)) * Term::from(existing[i]);
            // if not - take from either existing or state part
            constraint = constraint
                + Term::from(compression_mode_existing_is_right) * Term::from(path_data[i]);
            constraint = constraint
                + Term::from(compression_mode_existing_is_left) * Term::from(state_word[i]);
            let selected = cs.add_variable_from_constraint(constraint);
            existing[i] = selected;
        }
    }

    for word_idx in 8..16 {
        let path_data = input_as_witness_for_compression[word_idx - 8];
        let state_word = input_state[word_idx - 8];

        let existing = &mut input_words[word_idx];
        for i in 0..2 {
            let mut constraint = Constraint::empty();
            // if it's not the first round - keep existing
            constraint = constraint
                + (Term::from(1u64) - Term::from(compression_mode)) * Term::from(existing[i]);
            // if not - take from either existing or state part
            constraint = constraint
                + Term::from(compression_mode_existing_is_right) * Term::from(state_word[i]);
            constraint = constraint
                + Term::from(compression_mode_existing_is_left) * Term::from(path_data[i]);
            let selected = cs.add_variable_from_constraint(constraint);
            existing[i] = selected;
        }
    }

    {
        for (i, input) in input_words.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!(
                    "Input message element after masking {} = 0x{:08x}",
                    i, value
                );
            }
        }
    }

    // now we should select a fixed permutation of the message words depending on the round

    let mut selected_permutation = vec![];
    for message_word in 0..BLAKE2S_BLOCK_SIZE_U32_WORDS {
        // our permutation is fixed, so we just need to make a constraint
        let mut constraint_0 = Constraint::empty();
        let mut constraint_1 = Constraint::empty();
        for round_index in 0..MAX_ROUNDS {
            let selector = round_bitmask[round_index];
            let inputs = input_words[SIGMAS[round_index][message_word]];
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

    let state: Vec<_> = input_extended_state
        .iter()
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

    // perform actual mixing

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

    let output_decompositions_0 = g_function(
        cs,
        &mut a_row[0],
        &mut b_row[1],
        &mut c_row[2],
        &mut d_row[3],
        [selected_permutation[8], selected_permutation[9]],
    );

    let output_decompositions_1 = g_function(
        cs,
        &mut a_row[1],
        &mut b_row[2],
        &mut c_row[3],
        &mut d_row[0],
        [selected_permutation[10], selected_permutation[11]],
    );

    let output_decompositions_2 = g_function(
        cs,
        &mut a_row[2],
        &mut b_row[3],
        &mut c_row[0],
        &mut d_row[1],
        [selected_permutation[12], selected_permutation[13]],
    );

    let output_decompositions_3 = g_function(
        cs,
        &mut a_row[3],
        &mut b_row[0],
        &mut c_row[1],
        &mut d_row[2],
        [selected_permutation[14], selected_permutation[15]],
    );

    // now we should re-assemble it into output, and also xor-mix

    // NOTE on final masking: we do NOT need to mask anything here based on the execute/not predicate,
    // because if we do not execute, circuit guarantees that all read values are 0, so we will get 0 at the end here: there will not be
    // a compression mode active, so mixing will mix 0 extended state with 0 input words

    // we unconditionally set values for extended state
    let mut it = output_placeholder_extended_state.iter_mut();

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

    for src in b_row.iter().cloned() {
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

    for src in d_row.iter().cloned() {
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
        for (i, input) in output_placeholder_extended_state.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("Output extended state element {} = 0x{:08x}", i, value);
            }
        }
    }

    // and now resolve final XORing. Same - it doesn't require final masking as it'll be 0^0^0 in the empty case

    // we have final decomposition of:
    // - `a` as 8 bit low chunk + linear constraint for top 8 bits
    // - `b` as 9 bit low chunk + 7 bit high chunk
    // - `c` as 7 bit chunk + linear constraint for top 9 bits
    // - `d` as 8 and 8 bit chunks

    // Final XORs happen as a_initial ^ a_final ^ c_final
    // and b_initial ^ b_final ^ b_final, and we need to match
    // the chunks. The easiest way is to:
    // - compute a_initial ^ c_final and get 7 + 9 bit chunks
    // - split 9 bit chunk as boolean variable + 8 bits
    // - xor a_final with the corresponding 8 bit chunk and 7+1 bit chunks
    // Similar options applies for b-d pair

    let a_final = [
        output_decompositions_0.a_var_chunks_and_constraint.clone(),
        output_decompositions_1.a_var_chunks_and_constraint.clone(),
        output_decompositions_2.a_var_chunks_and_constraint.clone(),
        output_decompositions_3.a_var_chunks_and_constraint.clone(),
    ];

    // NOTE: here we want c0/c1/c2/c3, but chunks are not in the right order, so we manually reorder them
    let c_final = [
        output_decompositions_2.c_var_chunks_and_constraint.clone(),
        output_decompositions_3.c_var_chunks_and_constraint.clone(),
        output_decompositions_0.c_var_chunks_and_constraint.clone(),
        output_decompositions_1.c_var_chunks_and_constraint.clone(),
    ];

    for ((((a_initial, c_final), a_final), output), read_values) in state_for_final_xoring[..4]
        .iter()
        .zip(c_final)
        .zip(a_final)
        .zip(output_placeholder_state[..4].iter())
        .zip(input_state[..4].iter())
    {
        for i in 0..2 {
            let a = &a_initial[i];
            let ([(c_low_width, c_low)], c_high_constraint) = &c_final[i];
            assert_eq!(*c_low_width, 7);

            let (a_low_chunk, a_high_constraint) = chunk_16_bit_input::<F, CS, 7>(cs, *a);

            let [xor_result_low] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    LookupInput::Variable(a_low_chunk),
                    LookupInput::Variable(*c_low),
                ],
                TableType::Xor7,
            );

            let [xor_result_high] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    LookupInput::from(a_high_constraint),
                    LookupInput::from(c_high_constraint.clone()),
                ],
                TableType::Xor9,
            );

            // now xor with a_final, but for that we need to re-chunk. For that we will split 1 bit from one of the xor results above,
            // and glue it to other side
            let ([(a_low_width, a_low)], a_high_constraint) = &a_final[i];
            assert_eq!(*a_low_width, 8);

            let (a_low, extra_bit) = split_top_bit::<F, CS, 7>(cs, *a_low);

            let [xor_result_low] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    LookupInput::Variable(xor_result_low),
                    LookupInput::Variable(a_low),
                ],
                TableType::Xor7,
            );

            let mut a_high_constraint = a_high_constraint.clone();
            a_high_constraint.scale(F::TWO);
            a_high_constraint += extra_bit.get_terms();

            let [xor_result_high] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    LookupInput::Variable(xor_result_high),
                    LookupInput::from(a_high_constraint),
                ],
                TableType::Xor9,
            );

            // and if we do request final XOR-ing, then we use those value to construct and output, otherwise - use initial values

            let dst = output[i];
            let mut constraint = Constraint::empty();
            constraint += Term::from(xor_result_low);
            constraint += Term::from((F::from_u64_unchecked(1u64 << 7), xor_result_high));
            constraint = constraint * Term::from(perform_final_xor.get_variable().unwrap());
            constraint = constraint
                + (Term::from(1u64) - Term::from(perform_final_xor.get_variable().unwrap()))
                    * Term::from(read_values[i]);
            // set value
            collapse_max_quadratic_constraint_into(cs, constraint.clone(), dst);
            // add constraint
            constraint -= Term::from(dst);
            cs.add_constraint(constraint);
        }
    }

    for ((((b_initial, d_final), b_final), output), read_values) in state_for_final_xoring[4..8]
        .iter()
        .zip(d_row.iter())
        .zip(b_row.iter())
        .zip(output_placeholder_state[4..8].iter())
        .zip(input_state[4..8].iter())
    {
        for i in 0..2 {
            let b = &b_initial[i];
            let b_final = &b_final[i];
            let d_final = &d_final[i];

            assert_eq!(b_final.len(), 2);
            assert_eq!(d_final.len(), 2);

            let (b_low_width, b_low_var) = b_final[0];
            assert_eq!(b_low_width, 9);
            let (b_high_width, b_high_var) = b_final[1];
            assert_eq!(b_high_width, 7);

            let (d_low_width, d_low_var) = d_final[0];
            assert_eq!(d_low_width, 8);
            let (d_high_width, d_high_var) = d_final[1];
            assert_eq!(d_high_width, 8);

            let (b_initial_low_chunk, b_initial_high_constraint) =
                chunk_16_bit_input::<F, CS, 9>(cs, *b);

            let [xor_result_low] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    LookupInput::Variable(b_low_var),
                    LookupInput::Variable(b_initial_low_chunk),
                ],
                TableType::Xor9,
            );
            let [xor_result_high] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    LookupInput::Variable(b_high_var),
                    LookupInput::from(b_initial_high_constraint),
                ],
                TableType::Xor7,
            );

            // rechunk and finish

            let (xor_result_low, extra_bit) = split_top_bit::<F, CS, 8>(cs, xor_result_low);

            let [xor_result_low] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    LookupInput::Variable(d_low_var),
                    LookupInput::Variable(xor_result_low),
                ],
                TableType::Xor,
            );

            let mut constraint = Constraint::empty();
            constraint += extra_bit.get_terms();
            constraint += Term::from((F::TWO, xor_result_high));

            let [xor_result_high] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    LookupInput::Variable(d_high_var),
                    LookupInput::from(constraint),
                ],
                TableType::Xor,
            );

            let dst = output[i];
            let mut constraint = Constraint::empty();
            constraint += Term::from(xor_result_low);
            constraint += Term::from((F::from_u64_unchecked(1u64 << 8), xor_result_high));
            constraint = constraint * Term::from(perform_final_xor.get_variable().unwrap());
            constraint = constraint
                + (Term::from(1u64) - Term::from(perform_final_xor.get_variable().unwrap()))
                    * Term::from(read_values[i]);
            // set value
            collapse_max_quadratic_constraint_into(cs, constraint.clone(), dst);
            // add constraint
            constraint -= Term::from(dst);
            cs.add_constraint(constraint);
        }
    }

    {
        for (i, input) in output_placeholder_state.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("Output state element {} = 0x{:08x}", i, value);
            }
        }
    }

    (output_placeholder_state, output_placeholder_extended_state)
}

pub(crate) fn chunk_16_bit_input<F: PrimeField, CS: Circuit<F>, const LOW_CHUNK_BITS: usize>(
    cs: &mut CS,
    input: Variable,
) -> (Variable, Constraint<F>) {
    let low_chunk = cs.add_variable();

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let value = placer.get_u16(input);
        let low_chunk_value = value.get_lowest_bits(LOW_CHUNK_BITS as u32);

        placer.assign_u16(low_chunk, &low_chunk_value);
    };

    cs.set_values(value_fn);

    let mut constraint = Constraint::<F>::empty();
    constraint += Term::from(input);
    constraint -= Term::from(low_chunk);
    constraint.scale(
        F::from_u64_unchecked(1 << LOW_CHUNK_BITS)
            .inverse()
            .unwrap(),
    );

    (low_chunk, constraint)
}

pub(crate) fn split_top_bit<F: PrimeField, CS: Circuit<F>, const LOW_CHUNK_BITS: usize>(
    cs: &mut CS,
    input: Variable,
) -> (Variable, Boolean) {
    assert!(LOW_CHUNK_BITS < 16);
    let low_chunk = cs.add_variable();
    let bit = cs.add_boolean_variable();

    let bit_var = bit.get_variable().unwrap();

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let value = placer.get_u16(input);
        let low_chunk_value = value.get_lowest_bits(LOW_CHUNK_BITS as u32);
        let top_bit = value.get_bit(LOW_CHUNK_BITS as u32);

        placer.assign_u16(low_chunk, &low_chunk_value);
        placer.assign_mask(bit_var, &top_bit);
    };

    cs.set_values(value_fn);

    let mut constraint = Constraint::<F>::empty();
    constraint += Term::from(input);
    constraint -= Term::from(low_chunk);
    constraint -= Term::from((
        F::from_u64_unchecked(1 << LOW_CHUNK_BITS),
        bit.get_variable().unwrap(),
    ));
    cs.add_constraint_allow_explicit_linear(constraint);

    (low_chunk, bit)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::cs::cs_reference::BasicAssembly;
    use crate::one_row_compiler::OneRowCompiler;
    use crate::utils::serialize_to_file;
    use field::Mersenne31Field;

    #[test]
    fn compile_blake2_with_extended_control() {
        let mut cs = BasicAssembly::<Mersenne31Field>::new();
        define_blake2_with_extended_control_delegation_circuit(&mut cs);
        let (circuit_output, _) = cs.finalize();
        let compiler = OneRowCompiler::default();
        let compiled = compiler.compile_to_evaluate_delegations(circuit_output, 20);

        serialize_to_file(&compiled, "blake_delegation_layout.json");
    }

    #[test]
    fn blake_delegation_get_witness_graph() {
        let ssa_forms = dump_ssa_witness_eval_form_for_delegation::<Mersenne31Field, _>(
            define_blake2_with_extended_control_delegation_circuit,
        );
        serialize_to_file(&ssa_forms, "blake_delegation_ssa.json");
    }
}
