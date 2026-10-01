//! Blake2s round function with extended control.
//!
//! There are two arithmetizations of the same ABI and semantics:
//! - [`wider_tables`] is the default one. It uses lookup tables of up to 5 columns to commit
//!   fewer witness columns, see the module documentation for the list of changes;
//! - [`legacy`] is the original one over 3-column tables only. It is selected by the
//!   `legacy_blake_round_function` feature. Its G function is also reused by
//!   `blake2_g_function`.
//!
//! Both are always compiled, the feature only selects the re-exports below, that are what the
//! rest of the workspace uses.
//!
//! The beginning of the circuit (ABI, control register, flag of the final round) does not
//! depend on the arithmetization and is in [`allocate_inputs_and_control`].

use super::*;
use crate::cs::circuit::*;
use crate::gkr_circuits::Variable;
use crate::structured_expr::Expr;
use crate::types::Boolean;
use crate::types::Num;
use crate::witness_placer::*;
use blake2s_u32::state_with_extended_control_flags::*;
use common_constants::delegation_types::blake2s_with_control::*;

pub mod legacy;
pub mod wider_tables;

// standalone G function circuit is built on top of the original G function
pub(crate) use self::legacy::g_function;

#[cfg(feature = "legacy_blake_round_function")]
pub use self::legacy::{
    all_table_types, blake2_with_extended_control_delegation_circuit_create_table_driver,
    blake2_with_extended_control_table_addition_fn, blake2_with_extended_control_table_driver_fn,
    define_blake2_with_extended_control_delegation_circuit,
};
#[cfg(not(feature = "legacy_blake_round_function"))]
pub use self::wider_tables::{
    all_table_types, blake2_with_extended_control_delegation_circuit_create_table_driver,
    blake2_with_extended_control_table_addition_fn, blake2_with_extended_control_table_driver_fn,
    define_blake2_with_extended_control_delegation_circuit,
};

/// Everything that the arithmetizations get from the common beginning of the circuit, see
/// [`allocate_inputs_and_control`].
pub(crate) struct Blake2RoundFunctionInputs {
    /// Read values of the 8 words of the state.
    pub(crate) input_state: Vec<[Variable; 2]>,
    /// Write values of the 8 words of the state, not assigned or constrained yet.
    pub(crate) output_placeholder_state: [[Variable; 2]; 8],
    /// Read values of the 16 words of the extended state.
    pub(crate) input_extended_state: Vec<[Variable; 2]>,
    /// Write values of the 16 words of the extended state, not assigned or constrained yet.
    pub(crate) output_placeholder_extended_state: [[Variable; 2]; 16],
    /// Read values of the 16 words of the input to mix.
    pub(crate) input_words: Vec<[Variable; 2]>,
    /// Write value of x12, not assigned or constrained yet.
    pub(crate) x12_write_vars: [Variable; 2],
    pub(crate) control_bitmask: [Boolean; BLAKE2S_NUM_CONTROL_BITS],
    pub(crate) round_bitmask: [Boolean; BLAKE2S_MAX_ROUNDS],
    pub(crate) input_is_right_node: Boolean,
    pub(crate) compression_mode: Boolean,
    /// Constrained to be 1 in the final round (10th, or 7th if rounds are reduced).
    pub(crate) perform_final_xor: Variable,
}

/// Common beginning of both arithmetizations: allocates the delegation state and all
/// register and indirect memory accesses of the ABI, splits the control register into the
/// control and round bitmasks, and defines the flag of the final round.
pub(crate) fn allocate_inputs_and_control<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
) -> Blake2RoundFunctionInputs {
    let (_execute, _invocation_timestamp) =
        cs.allocate_delegation_state(BLAKE2S_DELEGATION_CSR_REGISTER as u16);

    // we do not expect any variable offsets, so we allocate all register and indirect reads/writes right away

    let state_accesses = (0..24)
        .into_iter()
        .map(|access_idx| IndirectAccessOffset {
            variable_dependent: None,
            offset_constant: (access_idx * core::mem::size_of::<u32>()) as u32,
            assume_no_alignment_overflow: true,
            is_write_access: true,
        })
        .collect();

    let x10_request = RegisterAccessRequest {
        register_index: 10,
        register_write: false,
        indirects_alignment_log2: 7, // 128 bytes - 32 + 64 for state and extended state are needed
        indirect_accesses: state_accesses,
    };

    let input_accesses = (0..16)
        .into_iter()
        .map(|access_idx| IndirectAccessOffset {
            variable_dependent: None,
            offset_constant: (access_idx * core::mem::size_of::<u32>()) as u32,
            assume_no_alignment_overflow: true,
            is_write_access: false,
        })
        .collect();

    let x11_request = RegisterAccessRequest {
        register_index: 11,
        register_write: false,
        indirects_alignment_log2: 6, // just aligned by machine words
        indirect_accesses: input_accesses,
    };

    let x12_request = RegisterAccessRequest {
        register_index: 12,
        register_write: true,
        indirects_alignment_log2: 0, // no indirects
        indirect_accesses: vec![],
    };

    let x10_and_indirects = cs.request_register_and_indirect_memory_accesses(
        x10_request,
        "state read/write from x10",
        2,
    );
    let x11_and_indirects =
        cs.request_register_and_indirect_memory_accesses(x11_request, "input read from x11", 2);
    let x12_and_indirects = cs.request_register_and_indirect_memory_accesses(
        x12_request,
        "control read/write from x12",
        2,
    );

    assert_eq!(x10_and_indirects.indirect_accesses.len(), 24);
    assert_eq!(x11_and_indirects.indirect_accesses.len(), 16);
    assert!(x12_and_indirects.indirect_accesses.is_empty());

    let mut input_state = vec![];
    let mut output_placeholder_state = vec![];
    for i in 0..8 {
        let IndirectAccessType::Write {
            read_value,
            write_value,
            ..
        } = x10_and_indirects.indirect_accesses[i]
        else {
            panic!()
        };

        input_state.push(read_value);
        output_placeholder_state.push(write_value);
    }
    let output_placeholder_state: [[Variable; 2]; 8] = output_placeholder_state.try_into().unwrap();

    let mut input_extended_state = vec![];
    let mut output_placeholder_extended_state = vec![];
    for i in 8..24 {
        let IndirectAccessType::Write {
            read_value,
            write_value,
            ..
        } = x10_and_indirects.indirect_accesses[i]
        else {
            panic!()
        };

        input_extended_state.push(read_value);
        output_placeholder_extended_state.push(write_value);
    }
    let output_placeholder_extended_state: [[Variable; 2]; 16] =
        output_placeholder_extended_state.try_into().unwrap();

    let mut input_words = vec![];
    for i in 0..16 {
        let IndirectAccessType::Read { read_value, .. } = x11_and_indirects.indirect_accesses[i]
        else {
            panic!()
        };

        input_words.push(read_value);
    }

    let (x12_vars, x12_write_vars) = {
        let RegisterAccessType::Write {
            read_value,
            write_value,
        } = x12_and_indirects.register_access
        else {
            panic!()
        };

        (read_value, write_value)
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

        let register = Register::<F>(x12_vars.map(|el| Num::Var(el)));
        if let Some(value) = register.get_value_unsigned(&*cs) {
            println!("Control register = 0b{:b}", value);
        }
    }

    // set updated bitmask for high bits and constraint it
    let control_register_bits = Boolean::split_into_bitmask::<
        F,
        CS,
        BLAKE2S_NUM_CONTROL_REGISTER_BITS,
    >(cs, Num::Var(x12_vars[1]));

    let control_bitmask: [Boolean; BLAKE2S_NUM_CONTROL_BITS] = control_register_bits
        [0..BLAKE2S_NUM_CONTROL_BITS]
        .try_into()
        .unwrap();
    let round_bitmask: [Boolean; BLAKE2S_MAX_ROUNDS] = control_register_bits
        [BLAKE2S_NUM_CONTROL_BITS..BLAKE2S_NUM_CONTROL_REGISTER_BITS]
        .try_into()
        .unwrap();

    // TODO: for all cases that we care round bitmask is exclusive, consider adding a constraint for it
    {
        for (i, el) in round_bitmask.iter().enumerate() {
            if let Some(value) = el.get_value(&*cs) {
                println!("Round bitmask element {} = {}", i, value);
            }
        }

        if let Some(value) = control_bitmask[REDUCE_ROUNDS_BIT_IDX].get_value(&*cs) {
            if value {
                println!("Control bitmask contains `reduce rounds`");
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
    let reduce_rounds = control_bitmask[REDUCE_ROUNDS_BIT_IDX];
    let input_is_right_node = control_bitmask[INPUT_IS_RIGHT_NODE_BIT_IDX];
    let compression_mode = control_bitmask[COMPRESSION_MODE_BIT_IDX];

    // round is final if it's 10th or if it's 7th and we do reduce rounds. For all cases
    // that we care round bitmasks is exclusive, so we can do one constraint via addition
    let perform_final_xor = cs.add_named_variable("perform final xor flag");
    {
        let last_round_if_reduced_var = round_bitmask[6].get_variable().unwrap();
        let last_round_if_full_var = round_bitmask[9].get_variable().unwrap();
        let reduced_rounds_var = reduce_rounds.get_variable().unwrap();
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let last_round_if_reduced = placer.get_boolean(last_round_if_reduced_var);
            let last_round_if_full = placer.get_boolean(last_round_if_full_var);
            let reduced_round = placer.get_boolean(reduced_rounds_var);
            let t = last_round_if_reduced
                .and(&reduced_round)
                .or(&last_round_if_full);
            placer.assign_mask(perform_final_xor, &t);
        };
        cs.set_values(value_fn);
    }
    cs.add_constraint_expr(
        Expr::from(round_bitmask[6]) * Expr::from(reduce_rounds) + Expr::from(round_bitmask[9])
            - Expr::var(perform_final_xor),
    );
    // let perform_final_xor = Boolean::or(
    //     &round_bitmask[9],
    //     &Boolean::and(&round_bitmask[6], &reduce_rounds, cs),
    //     cs,
    // );

    Blake2RoundFunctionInputs {
        input_state,
        output_placeholder_state,
        input_extended_state,
        output_placeholder_extended_state,
        input_words,
        x12_write_vars,
        control_bitmask,
        round_bitmask,
        input_is_right_node,
        compression_mode,
        perform_final_xor,
    }
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use crate::gkr_compiler::compile_delegation_circuit_into_gkr;
    use crate::gkr_compiler::compile_delegation_circuit_into_gkr_without_caches;
    use crate::gkr_compiler::dump_ssa_witness_eval_form;
    use crate::utils::serialize_to_file;

    // All tests below compile the selected (re-exported) arithmetization.
    // `AIRBENDER_COMPILED_CIRCUITS_OUT` redirects the artifacts away from `compiled_circuits/`
    fn out_path(name: &str) -> String {
        let dir = std::env::var("AIRBENDER_COMPILED_CIRCUITS_OUT")
            .unwrap_or_else(|_| "compiled_circuits".to_string());
        format!("{}/{}", dir, name)
    }

    #[test]
    fn compile_blake2_with_extended_control_into_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let gkr_compiled = compile_delegation_circuit_into_gkr::<BabyBearField>(
            &|cs| blake2_with_extended_control_table_addition_fn(cs),
            &|cs| {
                let _ = define_blake2_with_extended_control_delegation_circuit(cs);
            },
            20,
        );

        serialize_to_file(
            &gkr_compiled,
            &out_path("blake2_with_extended_control_layout_gkr.json"),
        );
    }

    #[test]
    fn compile_blake2_with_extended_control_witness_graph() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let ssa_forms = dump_ssa_witness_eval_form::<BabyBearField>(
            &|cs| blake2_with_extended_control_table_addition_fn(cs),
            &|cs| {
                let _ = define_blake2_with_extended_control_delegation_circuit(cs);
            },
        );
        serialize_to_file(
            &ssa_forms,
            &out_path("blake2_with_extended_control_ssa_gkr.json"),
        );
    }

    #[test]
    fn compile_blake2_with_extended_control_into_no_caches_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let gkr_compiled = compile_delegation_circuit_into_gkr_without_caches::<BabyBearField>(
            &|cs| blake2_with_extended_control_table_addition_fn(cs),
            &|cs| {
                let _ = define_blake2_with_extended_control_delegation_circuit(cs);
            },
            20,
        );

        serialize_to_file(
            &gkr_compiled,
            &out_path("blake2_with_extended_control_layout_no_caches_gkr.json"),
        );
    }
}
