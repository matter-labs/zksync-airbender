//! Blake2s round function with extended control over wider lookup tables.
//!
//! Same ABI, memory accesses and semantics as the original circuit in [`super::legacy`]
//! (`define_blake2_with_extended_control_delegation_circuit` in `legacy.rs`, G function in
//! `legacy/g_function_with_wider_tables.rs`), but with fewer committed witness columns and fewer lookups. The
//! memory columns are the same. Lookup tables are up to 5 columns wide instead of 3.
//!
//! Line references below are to `legacy.rs` and `legacy/g_function_with_wider_tables.rs`. The beginning of the
//! circuit (ABI, control bits, flag of the final round) is shared with the original circuit
//! via `allocate_inputs_and_control` in `mod.rs`. Everything else that is not listed
//! (masking of the extended state in the first round, x12 update, the general flow of the G
//! function and of the final XOR) is copied from the original circuit.
//!
//! # 1. One carry column per limb of `a + b + x`, range checked by a 4th lookup column
//!
//! `g_function_with_wider_tables` adds three 16-bit values per limb of `v[a] = v[a] + v[b] + x`, so a carry is
//! one of {0, 1, 2}. The original code commits it as two booleans, both for `x` and for `y`
//! (`g_function_with_wider_tables.rs:31-35` and `g_function_with_wider_tables.rs:432-436`):
//!
//! ```ignore
//! // for such addition we need at most 2 carries in low and in high
//! let carries_low: [Variable; 2] =
//!     std::array::from_fn(|_| cs.add_boolean_variable().get_variable().unwrap());
//! let carries_high: [Variable; 2] =
//!     std::array::from_fn(|_| cs.add_boolean_variable().get_variable().unwrap());
//! ```
//!
//! and combines them with weights 1 and 2 in `add_carries_into_expr` / `sub_carries_from_expr`
//! (`g_function_with_wider_tables.rs:691-710`). Here a carry is a single column. It is not constrained
//! on its own: it is the 3rd column of the lookup that XORs the low byte of the same limb
//! into `d` right after the addition. Those are the lookups at `g_function_with_wider_tables.rs:131-137`,
//! `163-169` and `514-520`:
//!
//! ```ignore
//! let [low_xor_result] = cs.get_variables_from_lookup_constrained::<2, 1>(
//!     &[LookupInput::Variable(var), LookupInput::Variable(a_chunks[0].1)],
//!     TableType::Xor,
//! );
//! ```
//!
//! They go to `TableType::Xor8WithCarry` with rows `(x, y, carry, x ^ y)`, `carry` in
//! {0, 1, 2}. The number of lookups does not change. 4 columns less per G function, 32 total.
//!
//! # 2. Extended state write columns are used as witness
//!
//! Memory write columns are committed in any case. The original code first computes the new
//! extended state from witness columns, and then copies it into the write columns
//! (`legacy.rs:419-454`, "we unconditionally set values for extended state"):
//!
//! ```ignore
//! for src in a_row.into_iter() {
//!     ...
//!     collapse_max_quadratic_expr_into(cs, src.clone(), *dst);
//!     cs.define_variable_from_expr(*dst, src);
//! }
//! for src in b_row.iter().cloned() {
//!     ...
//!     let expr = compose_chunks_expr(src);
//!     collapse_max_quadratic_expr_into(cs, expr.clone(), *dst);
//!     cs.define_variable_from_expr(*dst, expr);
//! }
//! ```
//!
//! Here the 4 G functions of the column step get the write columns of the words that they
//! finish (`GFunctionWriteColumns`), and use them in place of witness:
//! - `a` and `c` rows: the result limb of the last addition (`v[a] + v[b] + y` at
//!   `g_function_with_wider_tables.rs:427-497`, `v[c] + v[d]` at `g_function_with_wider_tables.rs:544-616`) is the write column
//!   `w` itself, so the carry is the linear expression `(sum - w) / 2^16` and is not
//!   committed. It is range checked in the same way as in (1), by the carry column of
//!   `Xor8WithCarry` (for `a`) or `Xor7WithCarry` (for `c`, replaces `TableType::Xor7` at
//!   `g_function_with_wider_tables.rs:644-650`). The remaining high chunk of the result becomes
//!   `(w - low_chunk) / 2^k`, that is 2 columns instead of a chain through all the previous
//!   additions;
//! - `b` and `d` rows: every limb is `low + 2^k * high` of two XOR results after the
//!   rotation (`g_function_with_wider_tables.rs:538-541` and `g_function_with_wider_tables.rs:665-668`):
//!
//!   ```ignore
//!   // rotate by 8
//!   *d = [
//!       vec![(8, d_not_yet_rotated[1]), (8, d_not_yet_rotated[2])],
//!       vec![(8, d_not_yet_rotated[3]), (8, d_not_yet_rotated[0])],
//!   ];
//!   ```
//!
//!   The `high` one is not a column anymore, the lookup that produces it has
//!   `(w - low) / 2^k` in its output column (`lookup_output_into_write_column`).
//!
//! 8 columns less per G function of the column step, 32 total. The copy constraints above
//! disappear, and so does the loop itself.
//!
//! # 3. `split_top_bit` does not commit the low chunk
//!
//! `legacy.rs:687-714`, called at `legacy.rs:533` and `legacy.rs:609` in the final XOR:
//!
//! ```ignore
//! let low_chunk = cs.add_variable();
//! let bit = cs.add_boolean_variable();
//! ...
//! let expr = Expr::var(input)
//!     - Expr::var(low_chunk)
//!     - Expr::from(bit) * F::from_u32_unchecked(1 << LOW_CHUNK_BITS);
//! cs.add_constraint_expr_allow_explicit_linear(expr);
//! ```
//!
//! The low chunk only goes into a XOR table of exactly `LOW_CHUNK_BITS` bits, that range
//! checks it, so it is the linear expression `input - 2^LOW_CHUNK_BITS * bit` here. 16
//! columns and 16 linear constraints less.
//!
//! # 4. One lookup for 4-bit and 3-bit chunks in `rotate_right::<12>(v[b] ^ v[c])`
//!
//! The original code XORs chunks of 3, 9 and 4 bits of every limb separately
//! (`g_function_with_wider_tables.rs:321-341` and `g_function_with_wider_tables.rs:381-401`):
//!
//! ```ignore
//! let [xor_result_3] = cs.get_variables_from_lookup_constrained::<2, 1>(
//!     &[LookupInput::Variable(chunk_3), LookupInput::Variable(c_chunks[0].1)],
//!     TableType::Xor3,
//! );
//! ...
//! let [xor_result_4] = cs.get_variables_from_lookup_constrained::<2, 1>(
//!     &[LookupInput::from(high_expr), LookupInput::from(c_remaining_constraint)],
//!     TableType::Xor4,
//! );
//! ```
//!
//! After the rotation the 4-bit result of one limb and the 3-bit result of the other limb
//! are neighbours (`g_function_with_wider_tables.rs:411-422`), and the only consumers use them as one 7-bit
//! value (`xor_7_expr` at `g_function_with_wider_tables.rs:641-642`, and additions). `TableType::Xor4x3` with
//! rows `(b4, b3, c4, c3, (b4 ^ c4) + 16 * (b3 ^ c3))` produces this value by one lookup.
//! All 4 inputs are separate columns of the table, so each of them is range checked as
//! before. 2 columns and 2 lookups less per G function, 16 total. `Xor3` and `Xor4` are not
//! used anymore.
//!
//! # 5. Selection of the message word is merged into the permutation
//!
//! The original code first selects 16 message words depending on the mode
//! (`legacy.rs:209-248`), and then permutes them (`legacy.rs:264-279`):
//!
//! ```ignore
//! let keep_existing =
//!     (Expr::<F>::one() - Expr::from(compression_mode)) * Expr::var(existing[i]);
//! let use_path_when_right =
//!     Expr::from(compression_mode_existing_is_right) * Expr::var(path_data[i]);
//! let use_state_when_left =
//!     Expr::from(compression_mode_existing_is_left) * Expr::var(state_word[i]);
//! let expr = keep_existing + use_path_when_right + use_state_when_left;
//! let selected = cs.add_variable_from_expr(expr);
//! ...
//! expr_0 = expr_0 + Expr::var(inputs[0]).mask(selector);
//! ```
//!
//! That is 32 + 32 columns. Here 20 columns `round[r] * compression_left` and
//! `round[r] * compression_right` are committed in place of the first 32, so a permuted word is
//! a quadratic expression of the memory columns. 12 columns less; the 32 constraints for the
//! permuted words have about 4 times more terms.
//!
//! # Total effect
//!
//! As compiled into GKR for trace length 2^20:
//! - witness columns: 647 -> 539 (108 less, 3 of them are multiplicities in both cases), memory
//!   columns are 225 as before;
//! - generic lookups: 208 -> 192, each is 5 columns + table ID instead of 3 + table ID;
//! - base layer constraints: 352 -> 220, but 32 of them (permuted message words) have 36-42
//!   quadratic terms, while the original circuit has at most 10;
//! - GKR depth is the same, inner layers are 16, 8, 4 and 2 values narrower;
//! - total size of the tables: 344384 -> 606208 rows (`Xor3` and `Xor4` are gone,
//!   `Xor8WithCarry`, `Xor7WithCarry` and `Xor4x3` are new).

use super::*;
use crate::cs::utils::collapse_max_quadratic_expr_into;
use crate::gkr_circuits::LookupInput;
use crate::gkr_circuits::Variable;
use crate::structured_expr::Expr;
use crate::types::Boolean;
use crate::types::Num;
use blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS;
use blake2s_u32::CONFIGURED_IV;
use blake2s_u32::EXTENDED_CONFIGURED_IV;
use blake2s_u32::SIGMAS;

// (b4, b3, c4, c3, output) of `Xor4x3` is the widest row
const TOTAL_TABLE_WIDTH: usize = 5;

// ABI:
// - registers x10-x12 are used to pass the parameters
// - x10 and x11 are pointers: x10 is a pointer to 24 words of state + extended state, x11 is a pointer to the input to mix
// - x12 is a control register, bits 17-19 are used for control mask, bits 20-29 are used for round bitmask

pub fn all_table_types() -> Vec<TableType> {
    vec![
        TableType::Xor,
        TableType::Xor7,
        TableType::Xor9,
        TableType::Xor8WithCarry,
        TableType::Xor7WithCarry,
        TableType::Xor4x3,
    ]
}

pub fn blake2_with_extended_control_delegation_circuit_create_table_driver<F: PrimeField>(
) -> TableDriver<F> {
    let mut table_driver = TableDriver::new();
    blake2_with_extended_control_table_driver_fn(&mut table_driver);

    table_driver
}

pub fn blake2_with_extended_control_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    for el in all_table_types() {
        cs.materialize_table::<TOTAL_TABLE_WIDTH>(el);
    }
}

pub fn blake2_with_extended_control_table_driver_fn<F: PrimeField>(
    table_driver: &mut TableDriver<F>,
) {
    for el in all_table_types() {
        table_driver.materialize_table::<TOTAL_TABLE_WIDTH>(el);
    }
}

pub fn define_blake2_with_extended_control_delegation_circuit<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
) -> ([[Variable; 2]; 8], [[Variable; 2]; 16]) {
    // ABI: memory accesses, parsed control register and the final round flag are the same for
    // all arithmetizations
    let Blake2RoundFunctionInputs {
        input_state,
        output_placeholder_state,
        mut input_extended_state,
        output_placeholder_extended_state,
        input_words,
        x12_write_vars,
        control_bitmask,
        round_bitmask,
        input_is_right_node,
        compression_mode,
        perform_final_xor,
    } = allocate_inputs_and_control(cs);

    // NOTE: G function structure is
    // v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    // v[d] = rotate_right::<16>(v[d] ^ v[a]);
    // v[c] = v[c].wrapping_add(v[d]);
    // v[b] = rotate_right::<12>(v[b] ^ v[c]);
    // v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    // v[d] = rotate_right::<8>(v[d] ^ v[a]);
    // v[c] = v[c].wrapping_add(v[d]);
    // v[b] = rotate_right::<7>(v[b] ^ v[c]);

    // and we will do 8 invocations of it (row and column mixes),
    // and eventually may also xor again with the inputs.
    // We do not want to use too many inter-layer copies, so G functions
    // will allocate minimal required witness directly at the base layer,
    // and we will also perform masking of the initial state and extended state at the base layer

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
                    Num::Constant(F::from_u32_unchecked(
                        ((initialization_word >> (16 * i)) & 0xffff) as u32,
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
        let initialization_word = EXTENDED_CONFIGURED_IV[word_idx];
        for i in 0..2 {
            // if it's not the first round - keep existing
            let keep_existing =
                (Expr::<F>::one() - Expr::var(first_round_var)) * Expr::var(existing[i]);
            // otherwise - from constants
            let use_initialization = Expr::var(first_round_var)
                * Expr::from((initialization_word >> (16 * i)) as u32 & 0xffff);
            let expr = keep_existing + use_initialization;
            let selected = cs.add_variable_from_expr(expr);
            existing[i] = selected;
        }
    }

    for word_idx in [12, 14] {
        let existing = &mut input_extended_state[word_idx];
        let initialization_word = COMPRESSION_MODE_EXTENDED_CONFIGURED_IV[word_idx];
        for i in 0..2 {
            // if it's not the first round - keep existing
            let keep_existing =
                (Expr::<F>::one() - Expr::var(first_round_var)) * Expr::var(existing[i]);
            // if not - two options
            // if it's a normal mode - then we take from existing extended(!) state
            let keep_existing_in_normal_mode =
                Expr::var(first_round_in_normal_mode_var) * Expr::var(existing[i]);
            // otherwise - from constants
            let use_initialization_in_compression_mode = Expr::var(first_round_var)
                * Expr::var(compression_mode_var)
                * Expr::from((initialization_word >> (16 * i)) as u32 & 0xffff);
            let expr = keep_existing
                + keep_existing_in_normal_mode
                + use_initialization_in_compression_mode;
            let selected = cs.add_variable_from_expr(expr);
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

    // OPTIMIZATION (5): the original circuit commits the 16 selected message words
    // (`(1 - compression) * word + compression_right * path + compression_left * state`),
    // and then 16 permuted words `sum over rounds of round[r] * selected[SIGMAS[r][word]]`.
    // Here we commit products of the round flags with the two compression mode flags, 20
    // columns in place of the 32 columns of the selected words, so that the permuted word is
    // a quadratic expression of the memory columns directly. Message is
    // - word[k] in normal mode
    // - `state || path` if existing state is a left node, and `path || state` if it's a right one,
    // where path is always first 8 words of the input
    let round_in_compression_mode_as_left: [Variable; BLAKE2S_MAX_ROUNDS] =
        std::array::from_fn(|round_index| {
            cs.add_variable_from_expr(
                Expr::<F>::from(round_bitmask[round_index])
                    * Expr::from(compression_mode_existing_is_left),
            )
        });
    let round_in_compression_mode_as_right: [Variable; BLAKE2S_MAX_ROUNDS] =
        std::array::from_fn(|round_index| {
            cs.add_variable_from_expr(
                Expr::<F>::from(round_bitmask[round_index])
                    * Expr::from(compression_mode_existing_is_right),
            )
        });

    // now we should select a fixed permutation of the message words depending on the round

    let mut selected_permutation = vec![];
    for message_word in 0..BLAKE2S_BLOCK_SIZE_U32_WORDS {
        // our permutation is fixed, so we just need to make a constraint
        let mut exprs = [Expr::<F>::zero(), Expr::<F>::zero()];
        for round_index in 0..BLAKE2S_MAX_ROUNDS {
            let round = Expr::<F>::from(round_bitmask[round_index]);
            let round_as_left = Expr::<F>::var(round_in_compression_mode_as_left[round_index]);
            let round_as_right = Expr::<F>::var(round_in_compression_mode_as_right[round_index]);
            let word_idx = SIGMAS[round_index][message_word];
            for i in 0..2 {
                let contribution = if word_idx < 8 {
                    // input word in normal mode and when existing state is a right node (it's a path then),
                    // and existing state if it is a left node
                    (round.clone() - round_as_left.clone()) * Expr::var(input_words[word_idx][i])
                        + round_as_left.clone() * Expr::var(input_state[word_idx][i])
                } else {
                    // input word in normal mode, existing state if it is a right node,
                    // and path if existing state is a left node
                    (round.clone() - round_as_left.clone() - round_as_right.clone())
                        * Expr::var(input_words[word_idx][i])
                        + round_as_right.clone() * Expr::var(input_state[word_idx - 8][i])
                        + round_as_left.clone() * Expr::var(input_words[word_idx - 8][i])
                };
                exprs[i] = exprs[i].clone() + contribution;
            }
        }
        let [expr_0, expr_1] = exprs;
        let low = cs.add_variable_from_expr(expr_0);
        let high = cs.add_variable_from_expr(expr_1);

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

    // `a` and `c` rows are linear expressions that we drag along, `b` and `d` rows are chunks.
    // Unlike the original circuit, a chunk is a linear expression too, and not always a variable
    let mut a_row: [[Expr<F>; 2]; 4] =
        std::array::from_fn(|i| input_extended_state[i].map(|el| Expr::var(el)));
    let mut b_row: [[Vec<Chunk<F>>; 2]; 4] =
        std::array::from_fn(|i| input_extended_state[4 + i].map(|el| vec![(16, Expr::var(el))]));
    let mut c_row: [[Expr<F>; 2]; 4] =
        std::array::from_fn(|i| input_extended_state[8 + i].map(|el| Expr::var(el)));
    let mut d_row: [[Vec<Chunk<F>>; 2]; 4] =
        std::array::from_fn(|i| input_extended_state[12 + i].map(|el| vec![(16, Expr::var(el))]));

    // perform actual mixing

    g_function_with_wider_tables(
        cs,
        &mut a_row[0],
        &mut b_row[0],
        &mut c_row[0],
        &mut d_row[0],
        [selected_permutation[0], selected_permutation[1]],
        None,
    );

    g_function_with_wider_tables(
        cs,
        &mut a_row[1],
        &mut b_row[1],
        &mut c_row[1],
        &mut d_row[1],
        [selected_permutation[2], selected_permutation[3]],
        None,
    );

    g_function_with_wider_tables(
        cs,
        &mut a_row[2],
        &mut b_row[2],
        &mut c_row[2],
        &mut d_row[2],
        [selected_permutation[4], selected_permutation[5]],
        None,
    );

    g_function_with_wider_tables(
        cs,
        &mut a_row[3],
        &mut b_row[3],
        &mut c_row[3],
        &mut d_row[3],
        [selected_permutation[6], selected_permutation[7]],
        None,
    );

    // shift

    // OPTIMIZATION (2): the original circuit continues to produce `a`/`c` rows as linear
    // expressions and `b`/`d` rows as chunk variables here, and then links them to the write
    // values of the extended state by 32 constraints. These 4 invocations produce the final
    // value of every word of the extended state, so instead we give them the write columns
    // to use directly in place of the witness
    let write_columns_for_column_step = |a: usize, b: usize, c: usize, d: usize| {
        Some(GFunctionWriteColumns {
            a: output_placeholder_extended_state[a],
            b: output_placeholder_extended_state[4 + b],
            c: output_placeholder_extended_state[8 + c],
            d: output_placeholder_extended_state[12 + d],
        })
    };

    let output_decompositions_0 = g_function_with_wider_tables(
        cs,
        &mut a_row[0],
        &mut b_row[1],
        &mut c_row[2],
        &mut d_row[3],
        [selected_permutation[8], selected_permutation[9]],
        write_columns_for_column_step(0, 1, 2, 3),
    );

    let output_decompositions_1 = g_function_with_wider_tables(
        cs,
        &mut a_row[1],
        &mut b_row[2],
        &mut c_row[3],
        &mut d_row[0],
        [selected_permutation[10], selected_permutation[11]],
        write_columns_for_column_step(1, 2, 3, 0),
    );

    let output_decompositions_2 = g_function_with_wider_tables(
        cs,
        &mut a_row[2],
        &mut b_row[3],
        &mut c_row[0],
        &mut d_row[1],
        [selected_permutation[12], selected_permutation[13]],
        write_columns_for_column_step(2, 3, 0, 1),
    );

    let output_decompositions_3 = g_function_with_wider_tables(
        cs,
        &mut a_row[3],
        &mut b_row[0],
        &mut c_row[1],
        &mut d_row[2],
        [selected_permutation[14], selected_permutation[15]],
        write_columns_for_column_step(3, 0, 1, 2),
    );

    // now we should re-assemble it into output, and also xor-mix

    // set value for low bits and constraint it
    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let zero = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0);
        placer.assign_u16(x12_write_vars[0], &zero);
    };
    cs.set_values(value_fn);
    cs.add_constraint_expr_allow_explicit_linear_prevent_optimizations_expr(Expr::var(
        x12_write_vars[0],
    ));

    // now set updated value for high bits and constraint it
    let mut expr = Expr::zero();
    let mut shift = 1;
    for bit in control_bitmask.iter() {
        expr = expr + Expr::var(bit.get_variable().unwrap()) * F::from_u32_unchecked(shift);
        shift <<= 1;
    }
    shift <<= 1; // for the shift bit
    for bit in round_bitmask.iter().take(BLAKE2S_MAX_ROUNDS - 1) {
        expr = expr + Expr::var(bit.get_variable().unwrap()) * F::from_u32_unchecked(shift);
        shift <<= 1;
    }
    assert_eq!(shift, 1u32 << BLAKE2S_NUM_CONTROL_REGISTER_BITS);

    collapse_max_quadratic_expr_into(cs, expr.clone(), x12_write_vars[1]);
    cs.define_variable_from_expr(x12_write_vars[1], expr);

    // OPTIMIZATION (2): values for extended state are already set. Write columns were
    // assigned and constrained by the last 4 G functions, so there is nothing to copy here,
    // and all 4 rows are expressed via the write columns now
    for (word_idx, a) in a_row.iter().enumerate() {
        for i in 0..2 {
            assert_eq!(
                a[i],
                Expr::var(output_placeholder_extended_state[word_idx][i])
            );
        }
    }
    for (word_idx, c) in c_row.iter().enumerate() {
        for i in 0..2 {
            assert_eq!(
                c[i],
                Expr::var(output_placeholder_extended_state[8 + word_idx][i])
            );
        }
    }

    {
        for (i, input) in output_placeholder_extended_state.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("Output extended state element {} = 0x{:08x}", i, value);
            }
        }
    }

    // and now resolve final XORing

    // we have final decomposition of:
    // - `a` as 8 bit low chunk + linear constraint for top 8 bits
    // - `b` as 9 bit low chunk + 7 bit high chunk
    // - `c` as 7 bit chunk + linear constraint for top 9 bits
    // - `d` as 8 and 8 bit chunks

    // Final XORs happen as a_initial ^ a_final ^ c_final
    // and b_initial ^ b_final ^ d_final, and we need to match
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

            // OPTIMIZATION (3): only the bit is a new column, low 7 bits are
            // `a_low - 2^7 * extra_bit` and are range checked by XOR-7 table below
            let (a_low, extra_bit) = split_top_bit::<F, CS, 7>(cs, *a_low);

            let [xor_result_low] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    LookupInput::Variable(xor_result_low),
                    LookupInput::from(a_low),
                ],
                TableType::Xor7,
            );

            let a_high_expr = a_high_constraint.clone() * F::TWO + Expr::from(extra_bit);

            let [xor_result_high] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    LookupInput::Variable(xor_result_high),
                    LookupInput::from(a_high_expr),
                ],
                TableType::Xor9,
            );

            // and if we do request final XOR-ing, then we use those value to construct and output, otherwise - use initial values

            let dst = output[i];
            let final_xor_expr = compose_chunks_expr(&[
                (7, Expr::var(xor_result_low)),
                (9, Expr::var(xor_result_high)),
            ]);
            let expr = final_xor_expr * Expr::var(perform_final_xor)
                + (Expr::<F>::one() - Expr::var(perform_final_xor)) * Expr::var(read_values[i]);
            collapse_max_quadratic_expr_into(cs, expr.clone(), dst);
            cs.define_variable_from_expr(dst, expr);
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

            // OPTIMIZATION (2): high chunks of `b` and `d` are linear expressions that
            // involve write columns of the extended state here, and not variables
            let (b_low_width, b_low) = b_final[0].clone();
            assert_eq!(b_low_width, 9);
            let (b_high_width, b_high) = b_final[1].clone();
            assert_eq!(b_high_width, 7);

            let (d_low_width, d_low) = d_final[0].clone();
            assert_eq!(d_low_width, 8);
            let (d_high_width, d_high) = d_final[1].clone();
            assert_eq!(d_high_width, 8);

            let (b_initial_low_chunk, b_initial_high_constraint) =
                chunk_16_bit_input::<F, CS, 9>(cs, *b);

            let [xor_result_low] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    chunk_into_lookup_input(b_low),
                    LookupInput::Variable(b_initial_low_chunk),
                ],
                TableType::Xor9,
            );
            let [xor_result_high] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    chunk_into_lookup_input(b_high),
                    LookupInput::from(b_initial_high_constraint),
                ],
                TableType::Xor7,
            );

            // rechunk and finish

            // OPTIMIZATION (3): only the bit is a new column, low 8 bits are
            // `xor_result_low - 2^8 * extra_bit` and are range checked by XOR table below
            let (xor_result_low, extra_bit) = split_top_bit::<F, CS, 8>(cs, xor_result_low);

            let [xor_result_low] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    chunk_into_lookup_input(d_low),
                    LookupInput::from(xor_result_low),
                ],
                TableType::Xor,
            );

            let high_expr = Expr::<F>::from(extra_bit) + Expr::var(xor_result_high) * F::TWO;

            let [xor_result_high] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    chunk_into_lookup_input(d_high),
                    LookupInput::from(high_expr),
                ],
                TableType::Xor,
            );

            let dst = output[i];
            let final_xor_expr = compose_chunks_expr(&[
                (8, Expr::var(xor_result_low)),
                (8, Expr::var(xor_result_high)),
            ]);
            let expr = final_xor_expr * Expr::var(perform_final_xor)
                + (Expr::<F>::one() - Expr::var(perform_final_xor)) * Expr::var(read_values[i]);
            collapse_max_quadratic_expr_into(cs, expr.clone(), dst);
            cs.define_variable_from_expr(dst, expr);
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
) -> (Variable, Expr<F>) {
    let low_chunk = cs.add_variable();

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let value = placer.get_u16(input);
        let low_chunk_value = value.get_lowest_bits(LOW_CHUNK_BITS as u32);

        placer.assign_u16(low_chunk, &low_chunk_value);
    };

    cs.set_values(value_fn);

    let expr = (Expr::<F>::var(input) - Expr::var(low_chunk))
        * F::from_u32_unchecked(1 << LOW_CHUNK_BITS)
            .inverse()
            .unwrap();

    (low_chunk, expr)
}

/// Splits the top bit of `LOW_CHUNK_BITS + 1` bit input, returns the low chunk and the bit.
///
/// OPTIMIZATION (3): the original function also allocates a variable for the low chunk and
/// links all three by a linear constraint. Here low chunk is a linear expression. It is NOT
/// range checked here, so the caller must use it in a lookup that is `LOW_CHUNK_BITS` wide.
pub(crate) fn split_top_bit<F: PrimeField, CS: Circuit<F>, const LOW_CHUNK_BITS: usize>(
    cs: &mut CS,
    input: Variable,
) -> (Expr<F>, Boolean) {
    assert!(LOW_CHUNK_BITS < 16);
    let bit = cs.add_boolean_variable();

    let bit_var = bit.get_variable().unwrap();

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let value = placer.get_u16(input);
        let top_bit = value.get_bit(LOW_CHUNK_BITS as u32);

        placer.assign_mask(bit_var, &top_bit);
    };

    cs.set_values(value_fn);

    let low_chunk = Expr::var(input) - Expr::from(bit) * F::from_u32_unchecked(1 << LOW_CHUNK_BITS);

    (low_chunk, bit)
}

/// Bit width and value of a little-endian piece of a 16-bit limb. Value is a linear
/// expression: either a variable, or the remainder of some columns after other chunks.
pub(crate) type Chunk<F> = (usize, Expr<F>);

/// Composes little-endian bit chunks into one structured limb expression.
fn compose_chunks_expr<F: PrimeField>(chunks: &[Chunk<F>]) -> Expr<F> {
    let mut expr = Expr::zero();
    let mut shift = 0;
    for (width, chunk) in chunks.iter() {
        expr = expr + chunk.clone() * F::from_u32_unchecked(1u32 << shift);
        shift += *width;
    }

    expr
}

fn chunk_into_lookup_input<F: PrimeField>(chunk: Expr<F>) -> LookupInput<F> {
    match chunk {
        Expr::Var(variable) => LookupInput::Variable(variable),
        chunk => LookupInput::from(chunk),
    }
}

/// Write columns of the 4 words of the extended state that are final after this invocation
/// of the G function.
#[derive(Clone, Copy, Debug)]
pub(crate) struct GFunctionWriteColumns {
    pub(crate) a: [Variable; 2],
    pub(crate) b: [Variable; 2],
    pub(crate) c: [Variable; 2],
    pub(crate) d: [Variable; 2],
}

pub(crate) struct GFunctionIntermediateValues<F: PrimeField> {
    pub(crate) a_var_chunks_and_constraint: [([(usize, Variable); 1], Expr<F>); 2],
    pub(crate) c_var_chunks_and_constraint: [([(usize, Variable); 1], Expr<F>); 2],
}

// NOTE: a element is always special, and it'll live in the form of expression, as we will drag it along
// from the previous stages
pub(crate) fn g_function_with_wider_tables<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    a: &mut [Expr<F>; 2],
    b: &mut [Vec<Chunk<F>>; 2],
    c: &mut [Expr<F>; 2],
    d: &mut [Vec<Chunk<F>>; 2],
    message: [[Variable; 2]; 2],
    write_columns: Option<GFunctionWriteColumns>,
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
    let mut a_carries = vec![];
    {
        // OPTIMIZATION (1): for such addition carry is one of {0, 1, 2}. The original
        // circuit uses 2 boolean carries in low and 2 in high, here it is one variable per
        // limb. It is range checked below as an extra column of the XOR lookup of the low byte
        let mut carry_in = None;
        for i in 0..2 {
            let addition_result_chunks: [Variable; 1] = std::array::from_fn(|_| cs.add_variable());
            let a_expr = a[i].clone();
            assert_eq!(a_expr.degree(), 1);

            // println!("v[a].wrapping_add(v[b]).wrapping_add(x) part {}", i);

            let mut sum = a_expr;
            sum = sum + compose_chunks_expr(&b[i]);
            sum = sum + Expr::var(x[i]);
            if let Some(carry_in) = carry_in.take() {
                sum = sum + carry_in;
            }

            let (new_a_expr, carry_out) = add_limb(
                cs,
                sum,
                [(8, addition_result_chunks[0])],
                CarryType::Ternary,
                None,
            );

            // and now we should produce linear constraint for single chunk, that is linear constraint and will go into the table as-is
            // MARIO: this is the 1 less chunk trick here, i.e. we split a u16 constraint into var+constraint u8 chunks. we do this optimisation everywhere
            let mut expr = new_a_expr.clone();
            expr = expr - Expr::var(addition_result_chunks[0]);
            // and scale
            expr = expr * F::from_u32_unchecked(1 << 8).inverse().unwrap();

            a_chunks_and_constraints.push(([(8, addition_result_chunks[0])], expr));
            a_carries.push(carry_out.clone());
            carry_in = Some(carry_out);

            // and overwrite
            a[i] = new_a_expr;
        }
    }

    // now we need to re-chunk `d` if needed and xor-rotate it with result of a above
    // we have two cases for `d` here:
    // - it comes from the input and it's 16 bit pieces
    // - it comes from previous mixing round, and it's 8-bit chunk
    {
        if d[0].len() == 1 {
            for i in 0..2 {
                let (width, limb) = d[i][0].clone();
                assert_eq!(width, 16);
                let Expr::Var(var) = limb else {
                    panic!("16-bit input must be a variable");
                };

                let low_chunk = cs.add_variable();

                let value_fn = move |placer: &mut CS::WitnessPlacer| {
                    let value = placer.get_u16(var);
                    let low_chunk_value = value.get_lowest_bits(8);

                    placer.assign_u16(low_chunk, &low_chunk_value);
                };
                cs.set_values(value_fn);

                let high_expr = (Expr::<F>::var(var) - Expr::var(low_chunk))
                    * F::from_u32_unchecked(1 << 8).inverse().unwrap();

                d[i] = vec![(8, Expr::var(low_chunk)), (8, high_expr)];
            }
        }
        assert_eq!(d[0].len(), 2);
        assert_eq!(d.len(), a_chunks_and_constraints.len());

        let mut d_not_yet_rotated = vec![];
        for i in 0..2 {
            // println!("v[d] = rotate_right::<16>(v[d] ^ v[a]) part {}", i);

            let (a_chunks, a_remaining_constraint) = a_chunks_and_constraints[i].clone();
            assert_eq!(a_chunks.len(), 1);
            assert_eq!(a_chunks[0].0, 8);
            assert_eq!(a_remaining_constraint.degree(), 1);

            let (width, d_low) = d[i][0].clone();
            assert_eq!(width, 8);
            // OPTIMIZATION (1): this is XOR of the low bytes as in the original circuit, and
            // the 3rd column range checks the carry out of this limb of the addition above
            let [low_xor_result] = cs.get_variables_from_lookup_constrained::<3, 1>(
                &[
                    chunk_into_lookup_input(d_low),
                    LookupInput::Variable(a_chunks[0].1),
                    chunk_into_lookup_input(a_carries[i].clone()),
                ],
                TableType::Xor8WithCarry,
            );

            let (width, d_high) = d[i][1].clone();
            assert_eq!(width, 8);
            let [xor_result_high] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    chunk_into_lookup_input(d_high),
                    LookupInput::from(a_remaining_constraint),
                ],
                TableType::Xor,
            );

            d_not_yet_rotated.push(low_xor_result);
            d_not_yet_rotated.push(xor_result_high);
        }
        assert_eq!(d_not_yet_rotated.len(), 4);

        // rotate by 16
        *d = [
            vec![
                (8, Expr::var(d_not_yet_rotated[2])),
                (8, Expr::var(d_not_yet_rotated[3])),
            ],
            vec![
                (8, Expr::var(d_not_yet_rotated[0])),
                (8, Expr::var(d_not_yet_rotated[1])),
            ],
        ];
    }

    // v[c] = v[c].wrapping_add(v[d]);
    // v[b] = rotate_right::<12>(v[b] ^ v[c]);

    // Here we will use 3 + 9 + 4 decomposition for XOR-rotate by 12

    // `d` at this point is always chunked, but `c` is always carried in as a constraint
    let mut c_chunks_and_constraints = vec![];
    {
        // for such addition we need at most 1 carry in low and in high, and it is a boolean variable as before
        let mut carry_in = None;
        for i in 0..2 {
            // println!("v[c] = v[c].wrapping_add(v[d]) part {}", i);

            assert_eq!(d[i].len(), 2);

            let addition_result_chunks: [Variable; 2] = std::array::from_fn(|_| cs.add_variable());
            let c_expr = c[i].clone();
            assert_eq!(c_expr.degree(), 1);

            let mut sum = c_expr;
            sum = sum + compose_chunks_expr(&d[i]);
            if let Some(carry_in) = carry_in.take() {
                sum = sum + carry_in;
            }

            let (new_c_expr, carry_out) = add_limb(
                cs,
                sum,
                [
                    (3, addition_result_chunks[0]),
                    (9, addition_result_chunks[1]),
                ],
                CarryType::Boolean,
                None,
            );

            // and now we should produce linear constraint for single chunk, that is linear constraint and will go into the table as-is
            let mut expr = new_c_expr.clone();
            // now we can subtract chunks for lookup relation
            // subtract chunks
            expr = expr - Expr::var(addition_result_chunks[0]);
            expr = expr - Expr::var(addition_result_chunks[1]) * F::from_u32_unchecked(1 << 3);
            // and scale
            expr = expr * F::from_u32_unchecked(1 << 12).inverse().unwrap();

            c_chunks_and_constraints.push((
                [
                    (3, addition_result_chunks[0]),
                    (9, addition_result_chunks[1]),
                ],
                expr,
            ));
            carry_in = Some(carry_out);

            // and overwrite
            c[i] = new_c_expr;
        }
    }

    // now we need to re-chunk `b` and xor-rotate it with result of c above
    // we have two cases for `b` here:
    // - it comes from the input and it's 16 bit pieces
    // - it comes from previous mixing round, and it's 9 + 7 chunks, but it's not matching for our XOR-rot by 12,
    // so we will need to re-chunk
    // In both cases it is a limb that we split as 3 + 9 + 4 using 2 extra variables
    {
        let mut b_chunks_and_constraints = vec![];
        for i in 0..2 {
            let b_limb = compose_chunks_expr(&b[i]);
            assert_eq!(b[i].iter().map(|el| el.0).sum::<usize>(), 16);

            let [chunk_3, chunk_9]: [Variable; 2] = std::array::from_fn(|_| cs.add_variable());
            witness_eval_decomposition(cs, &b_limb, [(3, chunk_3), (9, chunk_9)]);

            let high_expr =
                (b_limb - Expr::var(chunk_3) - Expr::var(chunk_9) * F::from_u32_unchecked(1 << 3))
                    * F::from_u32_unchecked(1 << 12).inverse().unwrap();

            b_chunks_and_constraints.push(([(3, chunk_3), (9, chunk_9)], high_expr));
        }

        // and xor
        let mut xor_results_9 = vec![];
        for i in 0..2 {
            // println!("v[b] = rotate_right::<12>(v[b] ^ v[c]) part {}", i);

            let (b_chunks, _) = &b_chunks_and_constraints[i];
            let (c_chunks, c_remaining_constraint) = &c_chunks_and_constraints[i];
            assert_eq!(c_chunks.len(), 2);
            assert_eq!(c_chunks[0].0, 3);
            assert_eq!(c_chunks[1].0, 9);
            assert_eq!(c_remaining_constraint.degree(), 1);

            let [xor_result_9] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    LookupInput::Variable(b_chunks[1].1),
                    LookupInput::Variable(c_chunks[1].1),
                ],
                TableType::Xor9,
            );
            xor_results_9.push(xor_result_9);
        }

        // OPTIMIZATION (4): the original circuit performs XOR-3 and XOR-4 lookups for every
        // limb, and after rotation by 12 the limb is `xor_4 | xor_3 of another limb | xor_9
        // of another limb`. Low 7 bits there are only ever used together, so we get them by a
        // single lookup into the 5 column table, where 4-bit chunks (remainders of this limb)
        // and 3-bit chunks (variables of another limb) are in separate columns, and so are
        // range checked exactly as before
        let mut xor_results_7 = vec![];
        for i in 0..2 {
            let other = 1 - i;
            let (_, b_remaining_constraint) = &b_chunks_and_constraints[i];
            let (b_chunks_of_other_limb, _) = &b_chunks_and_constraints[other];
            let (_, c_remaining_constraint) = &c_chunks_and_constraints[i];
            let (c_chunks_of_other_limb, _) = &c_chunks_and_constraints[other];

            let [xor_result_7] = cs.get_variables_from_lookup_constrained::<4, 1>(
                &[
                    LookupInput::from(b_remaining_constraint.clone()),
                    LookupInput::Variable(b_chunks_of_other_limb[0].1),
                    LookupInput::from(c_remaining_constraint.clone()),
                    LookupInput::Variable(c_chunks_of_other_limb[0].1),
                ],
                TableType::Xor4x3,
            );
            xor_results_7.push(xor_result_7);
        }

        // rotate by 12
        *b = [
            vec![
                (7, Expr::var(xor_results_7[0])),
                (9, Expr::var(xor_results_9[1])),
            ],
            vec![
                (7, Expr::var(xor_results_7[1])),
                (9, Expr::var(xor_results_9[0])),
            ],
        ];
    }

    // now it's much easier because it's basically all the same, but we have good properties due to our decompositions above

    // v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    // v[d] = rotate_right::<8>(v[d] ^ v[a]);

    let mut a_chunks_and_constraints = vec![];
    let mut a_carries = vec![];
    {
        // OPTIMIZATION (1): again one carry per limb that is range checked below as an extra
        // column of the XOR lookup of the low byte.
        // OPTIMIZATION (2): if it is the last addition into `a`, then its result is a write
        // column of the extended state. Then carry is `(sum - write column) / 2^16` and is
        // not a variable at all, and `a` continues as the write column itself
        let mut carry_in = None;
        for i in 0..2 {
            // println!("v[a] = v[a].wrapping_add(v[b]).wrapping_add(y) part {}", i);

            let addition_result_chunks: [Variable; 1] = std::array::from_fn(|_| cs.add_variable());
            let a_expr = a[i].clone();
            assert_eq!(a_expr.degree(), 1);

            let mut sum = a_expr;
            sum = sum + compose_chunks_expr(&b[i]);
            sum = sum + Expr::var(y[i]);
            if let Some(carry_in) = carry_in.take() {
                sum = sum + carry_in;
            }

            let (new_a_expr, carry_out) = add_limb(
                cs,
                sum,
                [(8, addition_result_chunks[0])],
                CarryType::Ternary,
                write_columns.map(|el| el.a[i]),
            );

            // and now we should produce linear constraint for single chunk, that is linear constraint and will go into the table as-is
            let mut expr = new_a_expr.clone();
            // now we can subtract chunks for lookup relation
            // subtract chunks
            expr = expr - Expr::var(addition_result_chunks[0]);
            // and scale
            expr = expr * F::from_u32_unchecked(1 << 8).inverse().unwrap();

            a_chunks_and_constraints.push(([(8, addition_result_chunks[0])], expr));
            a_carries.push(carry_out.clone());
            carry_in = Some(carry_out);

            // and overwrite
            a[i] = new_a_expr;
        }
    }

    {
        assert_eq!(d[0].len(), 2);
        assert_eq!(d.len(), a_chunks_and_constraints.len());
        // we are already set

        // high bytes first, as their results are low bytes after rotation
        let mut high_xor_results = vec![];
        for i in 0..2 {
            // println!("v[d] = rotate_right::<8>(v[d] ^ v[a]) part {}", i);

            let (a_chunks, a_remaining_constraint) = a_chunks_and_constraints[i].clone();
            assert_eq!(a_chunks.len(), 1);
            assert_eq!(a_chunks[0].0, 8);
            assert_eq!(a_remaining_constraint.degree(), 1);

            let (width, d_high) = d[i][1].clone();
            assert_eq!(width, 8);
            let [xor_result_high] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    chunk_into_lookup_input(d_high),
                    LookupInput::from(a_remaining_constraint),
                ],
                TableType::Xor,
            );
            high_xor_results.push(xor_result_high);
        }

        let mut low_xor_results = vec![];
        for i in 0..2 {
            let (a_chunks, _) = a_chunks_and_constraints[i].clone();

            let (width, d_low) = d[i][0].clone();
            assert_eq!(width, 8);
            // OPTIMIZATION (1): the 3rd column range checks the carry out of this limb of
            // the addition above
            let inputs = [
                chunk_into_lookup_input(d_low),
                LookupInput::Variable(a_chunks[0].1),
                chunk_into_lookup_input(a_carries[i].clone()),
            ];
            let low_xor_result = if let Some(write_columns) = write_columns.as_ref() {
                // OPTIMIZATION (2): rotation by 8 places this result as the high byte of
                // another limb, on top of the result for high bytes of that limb. That limb
                // is final and is a write column, so the result is not a variable, but
                // `(write column - low byte) / 2^8` that is an output column of the lookup
                let other = 1 - i;
                lookup_output_into_write_column::<F, CS, 3, 4>(
                    cs,
                    inputs,
                    TableType::Xor8WithCarry,
                    Expr::var(high_xor_results[other]),
                    8,
                    write_columns.d[other],
                )
            } else {
                let [low_xor_result] = cs.get_variables_from_lookup_constrained::<3, 1>(
                    &inputs,
                    TableType::Xor8WithCarry,
                );

                Expr::var(low_xor_result)
            };
            low_xor_results.push(low_xor_result);
        }

        // rotate by 8
        *d = [
            vec![
                (8, Expr::var(high_xor_results[0])),
                (8, low_xor_results[1].clone()),
            ],
            vec![
                (8, Expr::var(high_xor_results[1])),
                (8, low_xor_results[0].clone()),
            ],
        ];
    }

    // v[c] = v[c].wrapping_add(v[d]);
    // v[b] = rotate_right::<7>(v[b] ^ v[c]);

    // Here we make chunks of 7 + 9
    let mut c_chunks_and_constraints = vec![];
    let mut c_carries = vec![];
    {
        // for such addition we need at most 1 carry in low and in high.
        // OPTIMIZATION (2): if it is the last addition into `c`, then its result is a write
        // column of the extended state. Then carry is `(sum - write column) / 2^16` and is
        // not a variable, and `c` continues as the write column itself
        let mut carry_in = None;
        for i in 0..2 {
            // println!("v[c] = v[c].wrapping_add(v[d]) part {}", i);

            assert_eq!(d[i].len(), 2);

            let addition_result_chunks: [Variable; 1] = std::array::from_fn(|_| cs.add_variable());
            let c_expr = c[i].clone();
            assert_eq!(c_expr.degree(), 1);

            let mut sum = c_expr;
            sum = sum + compose_chunks_expr(&d[i]);
            if let Some(carry_in) = carry_in.take() {
                sum = sum + carry_in;
            }

            let (new_c_expr, carry_out) = add_limb(
                cs,
                sum,
                [(7, addition_result_chunks[0])],
                CarryType::Boolean,
                write_columns.map(|el| el.c[i]),
            );

            // and now we should produce linear constraint for single chunk, that is linear constraint and will go into the table as-is
            let mut expr = new_c_expr.clone();
            // now we can subtract chunks for lookup relation
            // subtract chunks
            expr = expr - Expr::var(addition_result_chunks[0]);
            // and scale
            expr = expr * F::from_u32_unchecked(1 << 7).inverse().unwrap();

            c_chunks_and_constraints.push(([(7, addition_result_chunks[0])], expr));
            c_carries.push(carry_out.clone());
            carry_in = Some(carry_out);

            // and overwrite
            c[i] = new_c_expr;
        }
    }

    {
        // `b` came from previous XOR-rotate right above
        assert_eq!(b[0].len(), 2);
        assert_eq!(c_chunks_and_constraints.len(), 2);
        // we are already set

        // 9-bit chunks first, as their results are low chunks after rotation
        let mut xor_results_9 = vec![];
        for i in 0..2 {
            // println!("v[b] = rotate_right::<7>(v[b] ^ v[c]) part {}", i);

            let (width_9, b_chunk_9) = b[i][1].clone();
            assert_eq!(width_9, 9);

            let (c_chunks, c_remaining_constraint) = c_chunks_and_constraints[i].clone();
            assert_eq!(c_chunks.len(), 1);
            assert_eq!(c_chunks[0].0, 7);
            assert_eq!(c_remaining_constraint.degree(), 1);

            let [xor_result_9] = cs.get_variables_from_lookup_constrained::<2, 1>(
                &[
                    chunk_into_lookup_input(b_chunk_9),
                    LookupInput::from(c_remaining_constraint),
                ],
                TableType::Xor9,
            );
            xor_results_9.push(xor_result_9);
        }

        let mut xor_results_7 = vec![];
        for i in 0..2 {
            // OPTIMIZATION (4): low 7 bits of `b` are a single chunk already, the original
            // circuit has to glue it from 4 and 3 bit variables here
            let (width_7, b_chunk_7) = b[i][0].clone();
            assert_eq!(width_7, 7);

            let (c_chunks, _) = c_chunks_and_constraints[i].clone();

            let xor_result_7 = if let Some(write_columns) = write_columns.as_ref() {
                // OPTIMIZATION (2): rotation by 7 places this result as the high 7 bits of
                // another limb, on top of the result for 9-bit chunks of that limb. That
                // limb is final and is a write column, so the result is not a variable, but
                // `(write column - low 9 bits) / 2^9` that is an output column of the lookup.
                // Carry out of this limb of the addition above is not a variable either, and
                // we range check it as an extra column of the same lookup
                let other = 1 - i;
                lookup_output_into_write_column::<F, CS, 3, 4>(
                    cs,
                    [
                        chunk_into_lookup_input(b_chunk_7),
                        LookupInput::Variable(c_chunks[0].1),
                        chunk_into_lookup_input(c_carries[i].clone()),
                    ],
                    TableType::Xor7WithCarry,
                    Expr::var(xor_results_9[other]),
                    9,
                    write_columns.b[other],
                )
            } else {
                let [xor_result_7] = cs.get_variables_from_lookup_constrained::<2, 1>(
                    &[
                        chunk_into_lookup_input(b_chunk_7),
                        LookupInput::Variable(c_chunks[0].1),
                    ],
                    TableType::Xor7,
                );

                Expr::var(xor_result_7)
            };
            xor_results_7.push(xor_result_7);
        }

        // rotate by 7
        *b = [
            vec![
                (9, Expr::var(xor_results_9[0])),
                (7, xor_results_7[1].clone()),
            ],
            vec![
                (9, Expr::var(xor_results_9[1])),
                (7, xor_results_7[0].clone()),
            ],
        ];
    }

    let output = GFunctionIntermediateValues {
        a_var_chunks_and_constraint: a_chunks_and_constraints.try_into().unwrap(),
        c_var_chunks_and_constraint: c_chunks_and_constraints.try_into().unwrap(),
    };

    output
}

/// How the carry out of a limb is committed if result of the addition is not a write column.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CarryType {
    /// Addition of two limbs, carry is a boolean variable.
    Boolean,
    /// Addition of three limbs, carry is one of {0, 1, 2} in a single variable. It is NOT
    /// range checked here, the caller must put it into the carry column of a lookup.
    Ternary,
}

/// One 16-bit limb of a wrapping addition. `sum` is a linear expression for the sum of the
/// input limbs and of the carry in. Sets witness for the low chunks of the result, and
/// returns linear expressions for the 16-bit result and for the carry out.
///
/// - if `write_column` is `None`, carry out is a new variable of `carry_type`, and the result
///   is `sum - 2^16 * carry`;
/// - otherwise the result is the write column, that is assigned here, and carry out is
///   `(sum - write column) / 2^16`. It is NOT range checked here, the caller must put it into
///   the carry column of a lookup.
///
/// In both cases the result is 16 bits only when the caller range checks the low chunks, and
/// the remainder `(result - low chunks) / 2^k`.
fn add_limb<F: PrimeField, CS: Circuit<F>, const OUTPUT_CHUNKS_TO_PRODUCE: usize>(
    cs: &mut CS,
    sum: Expr<F>,
    output_chunks: [(usize, Variable); OUTPUT_CHUNKS_TO_PRODUCE],
    carry_type: CarryType,
    write_column: Option<Variable>,
) -> (Expr<F>, Expr<F>) {
    let carry_variable = if write_column.is_some() {
        None
    } else {
        let carry = match carry_type {
            CarryType::Boolean => cs.add_boolean_variable().get_variable().unwrap(),
            CarryType::Ternary => cs.add_variable(),
        };

        Some((carry, carry_type))
    };

    // add witness fn

    let (linear, constant_coeff) = split_linear_expr(&sum);

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let input_value =
            evaluate_linear_expr::<F, CS::WitnessPlacer>(placer, &linear, constant_coeff)
                .as_integer();

        if let Some(write_column) = write_column {
            placer.assign_u16(write_column, &input_value.get_lowest_bits(16).truncate());
        }

        // now we should decompose into output chunks
        let mut result = input_value.clone();
        for (width, var) in output_chunks.iter() {
            let chunk = result.get_lowest_bits(*width as u32);
            result = result.shr(*width as u32);
            placer.assign_u16(*var, &chunk.truncate());
        }

        // and the rest is carry (bits 16 and higher)
        let carry_out = input_value.shr(16);
        match carry_variable {
            Some((carry, CarryType::Boolean)) => {
                placer.assign_mask(carry, &carry_out.get_bit(0));
            }
            Some((carry, CarryType::Ternary)) => {
                placer.assign_u16(carry, &carry_out.truncate());
            }
            None => {}
        }
    };

    cs.set_values(value_fn);

    match (write_column, carry_variable) {
        (Some(write_column), None) => {
            let carry_out =
                (sum - Expr::var(write_column)) * F::from_u32_unchecked(1 << 16).inverse().unwrap();

            (Expr::var(write_column), carry_out)
        }
        (None, Some((carry, _))) => {
            let result = sum - Expr::var(carry) * F::from_u32_unchecked(1 << 16);

            (result, Expr::var(carry))
        }
        _ => unreachable!(),
    }
}

/// Sets witness for the low chunks of a limb that is given as a linear expression.
fn witness_eval_decomposition<
    F: PrimeField,
    CS: Circuit<F>,
    const OUTPUT_CHUNKS_TO_PRODUCE: usize,
>(
    cs: &mut CS,
    limb: &Expr<F>,
    output_chunks: [(usize, Variable); OUTPUT_CHUNKS_TO_PRODUCE],
) {
    let (linear, constant_coeff) = split_linear_expr(limb);

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let mut result =
            evaluate_linear_expr::<F, CS::WitnessPlacer>(placer, &linear, constant_coeff)
                .as_integer();
        for (width, var) in output_chunks.iter() {
            let chunk = result.get_lowest_bits(*width as u32);
            result = result.shr(*width as u32);
            placer.assign_u16(*var, &chunk.truncate());
        }
    };

    cs.set_values(value_fn);
}

/// Lookup with `NUM_KEYS` key columns and one output column, where the output is not a new
/// variable. Instead `write_column = low + 2^shift * output` holds for the looked up
/// output, so the write column is assigned here, and `(write_column - low) / 2^shift` is the
/// last column of the enforced tuple. Returns this expression.
fn lookup_output_into_write_column<
    F: PrimeField,
    CS: Circuit<F>,
    const NUM_KEYS: usize,
    const WIDTH: usize,
>(
    cs: &mut CS,
    inputs: [LookupInput<F>; NUM_KEYS],
    table_type: TableType,
    low: Expr<F>,
    shift: usize,
    write_column: Variable,
) -> Expr<F> {
    assert_eq!(NUM_KEYS + 1, WIDTH);

    let (low_linear, low_constant_coeff) = split_linear_expr(&low);
    let witness_inputs = inputs.clone();

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let table_id =
            <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(table_type as u32 as u16);
        let input_values: [_; NUM_KEYS] =
            std::array::from_fn(|i| witness_inputs[i].evaluate(placer));
        // this is an "act of lookup" that also counts multiplicity
        let [output] = placer.lookup::<NUM_KEYS, 1>(&input_values, &table_id);

        let mut value =
            evaluate_linear_expr::<F, CS::WitnessPlacer>(placer, &low_linear, low_constant_coeff);
        let shift = <CS::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(
            F::from_u32_unchecked(1 << shift),
        );
        value.add_assign_product(&output, &shift);
        placer.assign_field(write_column, &value);
    };

    cs.set_values(value_fn);

    let output =
        (Expr::var(write_column) - low) * F::from_u32_unchecked(1 << shift).inverse().unwrap();

    let tuple: [LookupInput<F>; WIDTH] = std::array::from_fn(|i| {
        if i < NUM_KEYS {
            inputs[i].clone()
        } else {
            LookupInput::from(output.clone())
        }
    });
    // multiplicity is counted by the witness function above
    cs.enforce_lookup_tuple_for_fixed_table(&tuple, table_type, true);

    output
}

fn split_linear_expr<F: PrimeField>(expr: &Expr<F>) -> (Vec<(F, Variable)>, F) {
    let constraint = expr.to_max_quadratic_constraint();
    let (quadratic, linear, constant_coeff) = constraint.split_max_quadratic();
    assert!(quadratic.is_empty());

    (linear, constant_coeff)
}

fn evaluate_linear_expr<F: PrimeField, W: WitnessPlacer<F>>(
    placer: &mut W,
    linear: &[(F, Variable)],
    constant_coeff: F,
) -> W::Field {
    let mut result = <W as WitnessTypeSet<F>>::Field::constant(constant_coeff);
    for (coeff, var) in linear.iter() {
        let a = placer.get_field(*var);
        let c = <W as WitnessTypeSet<F>>::Field::constant(*coeff);
        result.add_assign_product(&a, &c);
    }

    result
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use crate::cs::circuit_impl::BasicAssembly;
    use crate::definitions::TimestampScalar;
    use crate::gkr_circuits::decoder_trait::ExecutorFamilyDecoderData;
    use crate::oracle::Oracle;
    use crate::oracle::Placeholder;
    use crate::tables::LookupWrapper;
    use crate::witness_placer::cs_debug_evaluator::CSDebugWitnessEvaluator;
    use ::field::baby_bear::base::BabyBearField;

    // Concrete-witness check: run the original circuit and this one on the same inputs
    // through the debug evaluator, require every constraint, boolean variable and lookup
    // to hold, and every output to match a plain integer model of one round.

    #[derive(Clone, Copy, Debug)]
    struct Input {
        control: u32,
        state_and_extended_state: [u32; 24],
        input: [u32; 16],
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct Output {
        state: [u32; 8],
        extended_state: [u32; 16],
        control: u32,
    }

    struct BlakeOracle(Input);

    impl<F: PrimeField> Oracle<F> for BlakeOracle {
        fn get_witness_from_placeholder(
            &self,
            placeholder: Placeholder,
            subindex: usize,
            trace_row: usize,
        ) -> F {
            let value =
                <Self as Oracle<F>>::get_u32_witness_from_placeholder(self, placeholder, trace_row);
            match subindex {
                0 => F::from_u32_unchecked(value & 0xffff),
                1 => F::from_u32_unchecked(value >> 16),
                _ => unreachable!(),
            }
        }

        fn get_u32_witness_from_placeholder(&self, placeholder: Placeholder, _: usize) -> u32 {
            match placeholder {
                Placeholder::ExecuteDelegation => 1,
                Placeholder::DelegationRegisterReadValue(10) => 1 << 20,
                Placeholder::DelegationRegisterReadValue(11) => 1 << 21,
                Placeholder::DelegationRegisterReadValue(12) => self.0.control,
                // the circuit must overwrite this with its own result
                Placeholder::DelegationRegisterWriteValue(12) => 0xdead_beef,
                Placeholder::DelegationIndirectReadValue {
                    register_index: 10,
                    word_index,
                } => self.0.state_and_extended_state[word_index],
                Placeholder::DelegationIndirectReadValue {
                    register_index: 11,
                    word_index,
                } => self.0.input[word_index],
                _ => panic!("unexpected placeholder {:?}", placeholder),
            }
        }

        fn get_timestamp_witness_from_placeholder(
            &self,
            placeholder: Placeholder,
            _: usize,
        ) -> TimestampScalar {
            panic!("unexpected timestamp placeholder {:?}", placeholder)
        }

        fn get_executor_family_data(&self, _: usize) -> ExecutorFamilyDecoderData {
            unreachable!()
        }
    }

    type F = BabyBearField;
    type DebugCS = BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>;

    struct Stats {
        num_variables: usize,
        num_lookups: usize,
    }

    fn run_circuit(
        input: Input,
        table_addition_fn: &dyn Fn(&mut DebugCS),
        circuit_fn: &dyn Fn(&mut DebugCS) -> ([[Variable; 2]; 8], [[Variable; 2]; 16]),
    ) -> (Output, Stats) {
        let mut cs = DebugCS::new_with_oracle(BlakeOracle(input));
        (table_addition_fn)(&mut cs);
        let (state, extended_state) = (circuit_fn)(&mut cs);
        assert!(cs.is_satisfied(), "input {:?}", input);

        let (output, witness) = cs.finalize();
        let witness = witness.unwrap();
        let get_value = |variable: Variable| -> F { witness.get_value(variable).unwrap() };

        // booleans
        for variable in output.boolean_vars.iter() {
            let value = get_value(*variable).as_u32_reduced();
            assert!(value < 2, "{:?} is not boolean", variable);
        }

        // every lookup is a row of its table
        for query in output.lookups.iter() {
            let LookupQueryTableType::Constant(table_type) = query.table else {
                panic!("unexpected table type {:?}", query.table);
            };
            let LookupWrapper::Initialized(table) =
                &output.table_driver.tables[table_type.to_table_id() as usize]
            else {
                panic!("table {:?} is not initialized", table_type);
            };
            assert_eq!(
                query.row.len(),
                table.width(),
                "lookup into {:?} is of a wrong width",
                table_type
            );
            let mut row = arrayvec::ArrayVec::new();
            for el in query.row.iter() {
                let value = match el {
                    LookupInput::Variable(variable) => get_value(*variable),
                    LookupInput::Expression {
                        linear_terms,
                        constant_coeff,
                    } => {
                        let mut value = *constant_coeff;
                        for (coeff, variable) in linear_terms.iter() {
                            let mut t = get_value(*variable);
                            t.mul_assign(coeff);
                            value.add_assign(&t);
                        }

                        value
                    }
                };
                row.push(value);
            }
            assert!(
                table.content_data.contains_key(&row),
                "{:?} is not in the table {:?}, input {:?}",
                row,
                table_type,
                input
            );
        }

        let read_u32 = |limbs: [Variable; 2]| -> u32 {
            let low = get_value(limbs[0]).as_u32_reduced();
            let high = get_value(limbs[1]).as_u32_reduced();
            assert!(low < 1 << 16);
            assert!(high < 1 << 16);
            low | (high << 16)
        };

        let x12_access = &output.register_and_indirect_memory_accesses[2];
        assert_eq!(x12_access.register_index, 12);
        let RegisterAccessType::Write {
            write_value: x12_write_value,
            ..
        } = x12_access.register_access
        else {
            panic!()
        };

        let result = Output {
            state: std::array::from_fn(|i| read_u32(state[i])),
            extended_state: std::array::from_fn(|i| read_u32(extended_state[i])),
            control: read_u32(x12_write_value),
        };
        let stats = Stats {
            num_variables: output.num_of_variables,
            num_lookups: output.lookups.len(),
        };

        (result, stats)
    }

    fn control_register(compression: bool, right: bool, reduced: bool, round: usize) -> u32 {
        let mut control_bits = 0u32;
        control_bits |= (compression as u32) << COMPRESSION_MODE_BIT_IDX;
        control_bits |= (right as u32) << INPUT_IS_RIGHT_NODE_BIT_IDX;
        control_bits |= (reduced as u32) << REDUCE_ROUNDS_BIT_IDX;
        control_bits |= 1 << (BLAKE2S_NUM_CONTROL_BITS + round);

        control_bits << 16
    }

    // integer model of a single round
    fn reference(input: Input) -> Output {
        let control_bits = input.control >> 16;
        assert_eq!(input.control & 0xffff, 0);
        let compression = control_bits & (1 << COMPRESSION_MODE_BIT_IDX) != 0;
        let right = control_bits & (1 << INPUT_IS_RIGHT_NODE_BIT_IDX) != 0;
        let reduced = control_bits & (1 << REDUCE_ROUNDS_BIT_IDX) != 0;
        let round_bitmask = control_bits >> BLAKE2S_NUM_CONTROL_BITS;
        assert!(round_bitmask.is_power_of_two());
        let round = round_bitmask.trailing_zeros() as usize;
        assert!(round < BLAKE2S_MAX_ROUNDS);

        let state: [u32; 8] = input.state_and_extended_state[..8].try_into().unwrap();
        let mut v: [u32; 16] = input.state_and_extended_state[8..].try_into().unwrap();

        if round == 0 {
            for i in 0..8 {
                v[i] = if compression {
                    CONFIGURED_IV[i]
                } else {
                    state[i]
                };
            }
            for i in [8, 9, 10, 11, 13, 15] {
                v[i] = EXTENDED_CONFIGURED_IV[i];
            }
            if compression {
                for i in [12, 14] {
                    v[i] = COMPRESSION_MODE_EXTENDED_CONFIGURED_IV[i];
                }
            }
        }

        let message: [u32; 16] = std::array::from_fn(|i| match (compression, right) {
            (false, _) => input.input[i],
            // existing state is a left node, path is on the right
            (true, false) => {
                if i < 8 {
                    state[i]
                } else {
                    input.input[i - 8]
                }
            }
            (true, true) => {
                if i < 8 {
                    input.input[i]
                } else {
                    state[i - 8]
                }
            }
        });

        let mut g = |a: usize, b: usize, c: usize, d: usize, x: u32, y: u32| {
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
            v[d] = (v[d] ^ v[a]).rotate_right(16);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(12);
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
            v[d] = (v[d] ^ v[a]).rotate_right(8);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(7);
        };
        let m: [u32; 16] = std::array::from_fn(|i| message[SIGMAS[round][i]]);
        g(0, 4, 8, 12, m[0], m[1]);
        g(1, 5, 9, 13, m[2], m[3]);
        g(2, 6, 10, 14, m[4], m[5]);
        g(3, 7, 11, 15, m[6], m[7]);
        g(0, 5, 10, 15, m[8], m[9]);
        g(1, 6, 11, 12, m[10], m[11]);
        g(2, 7, 8, 13, m[12], m[13]);
        g(3, 4, 9, 14, m[14], m[15]);

        let is_final = round == 9 || (round == 6 && reduced);
        let new_state: [u32; 8] = std::array::from_fn(|i| {
            if is_final {
                let initial = if compression {
                    CONFIGURED_IV[i]
                } else {
                    state[i]
                };
                initial ^ v[i] ^ v[i + 8]
            } else {
                state[i]
            }
        });

        // control bits stay, round bitmask is shifted, and the last round is shifted away
        let control_mask = (1 << BLAKE2S_NUM_CONTROL_BITS) - 1;
        let mut new_control_bits = control_bits & control_mask;
        new_control_bits |= (round_bitmask << 1 << BLAKE2S_NUM_CONTROL_BITS)
            & ((1 << BLAKE2S_NUM_CONTROL_REGISTER_BITS) - 1);

        Output {
            state: new_state,
            extended_state: v,
            control: new_control_bits << 16,
        }
    }

    #[test]
    fn multi_hot_final_round_control_keeps_final_xor_boolean() {
        for (legacy, reduced) in [(false, false), (false, true), (true, false), (true, true)] {
            let control = control_register(false, false, reduced, 6)
                | control_register(false, false, reduced, 9);
            let input = Input {
                control,
                state_and_extended_state: [0; 24],
                input: [0; 16],
            };
            let mut cs = DebugCS::new_with_oracle(BlakeOracle(input));
            if legacy {
                super::super::legacy::blake2_with_extended_control_table_addition_fn(&mut cs);
                let _ =
                    super::super::legacy::define_blake2_with_extended_control_delegation_circuit(
                        &mut cs,
                    );
            } else {
                blake2_with_extended_control_table_addition_fn(&mut cs);
                let _ = define_blake2_with_extended_control_delegation_circuit(&mut cs);
            }
            assert!(cs.is_satisfied(), "input {:?}, legacy {}", input, legacy);
            let final_xor = *cs
                .variable_names
                .iter()
                .find(|(_, name)| name == &"perform final xor flag")
                .unwrap()
                .0;
            let value = cs
                .witness_placer
                .as_ref()
                .unwrap()
                .get_value(final_xor)
                .unwrap()
                .as_u32_reduced();
            assert_eq!(value, reduced as u32);
        }
    }

    #[test]
    fn blake2_with_wider_tables_matches_reference_model_and_legacy_circuit() {
        skip_if_ci!();

        // xorshift64* for deterministic inputs
        let mut rng_state = 0x9e3779b97f4a7c15u64;
        let mut next_u32 = move || -> u32 {
            rng_state ^= rng_state >> 12;
            rng_state ^= rng_state << 25;
            rng_state ^= rng_state >> 27;
            (rng_state.wrapping_mul(0x2545f4914f6cdd1d) >> 32) as u32
        };

        let mut num_cases = 0;
        let mut stats = None;
        for (compression, right) in [(false, false), (true, false), (true, true)] {
            for reduced in [false, true] {
                for round in 0..BLAKE2S_MAX_ROUNDS {
                    let control = control_register(compression, right, reduced, round);
                    let mut inputs = vec![
                        // extreme values for carries
                        Input {
                            control,
                            state_and_extended_state: [u32::MAX; 24],
                            input: [u32::MAX; 16],
                        },
                        Input {
                            control,
                            state_and_extended_state: [0; 24],
                            input: [0; 16],
                        },
                    ];
                    for _ in 0..2 {
                        inputs.push(Input {
                            control,
                            state_and_extended_state: std::array::from_fn(|_| next_u32()),
                            input: std::array::from_fn(|_| next_u32()),
                        });
                    }

                    for input in inputs.into_iter() {
                        let expected = reference(input);

                        let (legacy, legacy_stats) = run_circuit(
                            input,
                            &|cs| {
                                super::super::legacy::blake2_with_extended_control_table_addition_fn(
                                    cs,
                                )
                            },
                            &|cs| {
                                super::super::legacy::define_blake2_with_extended_control_delegation_circuit(cs)
                            },
                        );
                        assert_eq!(legacy, expected, "legacy, input {:?}", input);

                        let (new, new_stats) = run_circuit(
                            input,
                            &|cs| blake2_with_extended_control_table_addition_fn(cs),
                            &|cs| define_blake2_with_extended_control_delegation_circuit(cs),
                        );
                        assert_eq!(new, expected, "wider tables, input {:?}", input);

                        stats = Some((legacy_stats, new_stats));
                        num_cases += 1;
                    }
                }
            }
        }

        let (legacy_stats, new_stats) = stats.unwrap();
        println!(
            "{} cases passed for each of 2 circuits. Variables (with memory): {} -> {}, lookups: {} -> {}",
            num_cases,
            legacy_stats.num_variables,
            new_stats.num_variables,
            legacy_stats.num_lookups,
            new_stats.num_lookups,
        );
        // optimizations (1) - (5) remove 108 witness columns and 16 lookups
        assert_eq!(new_stats.num_variables + 108, legacy_stats.num_variables);
        assert_eq!(new_stats.num_lookups + 16, legacy_stats.num_lookups);
    }
}
