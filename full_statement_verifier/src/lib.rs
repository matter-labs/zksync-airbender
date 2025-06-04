#![cfg_attr(not(any(test, feature = "replace_csr")), no_std)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use core::mem::MaybeUninit;

pub use verifier_common;

use verifier_common::blake2s_u32::{BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use verifier_common::cs::definitions::{
    NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP, NUM_TIMESTAMP_COLUMNS_FOR_RAM, TIMESTAMP_COLUMNS_NUM_BITS,
};
use verifier_common::field::{Field, Mersenne31Field, Mersenne31Quartic, PrimeField};
use verifier_common::prover::definitions::MerkleTreeCap;

mod constants;

use self::constants::*;

use verifier_common::non_determinism_source::NonDeterminismSource;
use verifier_common::prover::definitions::ExternalChallenges;
use verifier_common::transcript::Blake2sBufferingTranscript;
use verifier_common::VerifierFunctionPointer;
use verifier_common::{parse_field_els_as_u32_checked, ProofPublicInputs};
use verifier_common::{prover, ProofOutput};

pub const MAX_BASE_LAYER_CIRCUITS: usize = const {
    let max_unique_timestamps =
        1u64 << (TIMESTAMP_COLUMNS_NUM_BITS as usize * NUM_TIMESTAMP_COLUMNS_FOR_RAM);
    let max_cycles = max_unique_timestamps >> NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP;
    let max_circuits =
        max_cycles / ((risc_v_cycles_verifier::concrete::size_constants::TRACE_LEN as u64) - 1);

    max_circuits as usize
};

pub const MAX_RECURSION_LAYER_CIRCUITS: usize = MAX_BASE_LAYER_CIRCUITS;

pub const RISC_V_VERIFIER_PTR: VerifierFunctionPointer<
    CAP_SIZE,
    NUM_COSETS,
    NUM_DELEGATION_CHALLENGES,
    1,
    2,
> = risc_v_cycles_verifier::verify;

pub const RISC_V_REDUCED_MACHINE_VERIFIER_PTR: VerifierFunctionPointer<
    CAP_SIZE,
    NUM_COSETS,
    NUM_DELEGATION_CHALLENGES,
    1,
    2,
> = reduced_risc_v_machine_verifier::verify;

pub const RISC_V_FINAL_REDUCED_MACHINE_VERIFIER_PTR: VerifierFunctionPointer<
    CAP_SIZE,
    NUM_COSETS,
    NUM_DELEGATION_CHALLENGES,
    1,
    2,
> = final_reduced_risc_v_machine_verifier::verify;

pub const BLAKE_WITH_COMPRESSION_VERIFIER_PTR: VerifierFunctionPointer<
    CAP_SIZE,
    NUM_COSETS,
    NUM_DELEGATION_CHALLENGES,
    0,
    0,
> = blake2_with_compression_verifier::verify;

pub const BIGINT_WITH_CONTROL_VERIFIER_PTR: VerifierFunctionPointer<
    CAP_SIZE,
    NUM_COSETS,
    NUM_DELEGATION_CHALLENGES,
    0,
    0,
> = bigint_with_control_verifier::verify;

use crate::constants::ALL_DELEGATION_CIRCUITS_PARAMS;

pub const BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS: &[(
    u32, // delegation type
    u32, // delegation capacity
    &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0>,
)] = &[
    (
        ALL_DELEGATION_CIRCUITS_PARAMS[0].0,
        ALL_DELEGATION_CIRCUITS_PARAMS[0].1,
        &ALL_DELEGATION_CIRCUITS_PARAMS[0].2,
        BLAKE_WITH_COMPRESSION_VERIFIER_PTR,
    ),
    (
        ALL_DELEGATION_CIRCUITS_PARAMS[1].0,
        ALL_DELEGATION_CIRCUITS_PARAMS[1].1,
        &ALL_DELEGATION_CIRCUITS_PARAMS[1].2,
        BIGINT_WITH_CONTROL_VERIFIER_PTR,
    ),
];

pub const RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS: &[(
    u32,
    u32,
    &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0>,
)] = &[(
    ALL_DELEGATION_CIRCUITS_PARAMS[0].0,
    ALL_DELEGATION_CIRCUITS_PARAMS[0].1,
    &ALL_DELEGATION_CIRCUITS_PARAMS[0].2,
    BLAKE_WITH_COMPRESSION_VERIFIER_PTR,
)];

pub const FINAL_RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS: &[(
    u32,
    u32,
    &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0>,
)] = &[];

const _: () = {
    let mut t = BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS[0].0;
    let mut i = 1;
    while i < BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS.len() {
        assert!(t < BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS[i].0);
        t = BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS[i].0;
        i += 1
    }

    let mut t = RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS[0].0;
    let mut i = 1;
    while i < RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS.len() {
        assert!(t < RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS[i].0);
        t = RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS[i].0;
        i += 1
    }

    ()
};

/// If we recurse over user's program -> we must provide expected final PC,
/// and setup caps (that encode the program itself!),
/// otherwise we only need to provide final PC
#[allow(invalid_value)]
#[inline(never)]
unsafe fn verify_full_statement<const BASE_LAYER: bool>(
    main_risc_v_circuit_verifier: VerifierFunctionPointer<
        CAP_SIZE,
        NUM_COSETS,
        NUM_DELEGATION_CHALLENGES,
        1,
        2,
    >,
    delegation_circuits_verifiers: &[(
        u32,
        u32,
        &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
        VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0>,
    )],
) -> [u32; 16] {
    // we should in parallel verify proofs, and drag along the transcript to assert equality of challenges
    let mut transcript = Blake2sBufferingTranscript::new();

    let mut registers_buffer = MaybeUninit::<[u32; 32 + 2 * 32]>::uninit().assume_init();

    // first we need to get final register values and timestamps
    for reg_idx in 0..32 {
        let value = verifier_common::DefaultNonDeterminismSource::read_word();
        let timestamp_low = verifier_common::DefaultNonDeterminismSource::read_word();
        let timestamp_high = verifier_common::DefaultNonDeterminismSource::read_word();
        registers_buffer[reg_idx * 3] = value;
        registers_buffer[reg_idx * 3 + 1] = timestamp_low;
        registers_buffer[reg_idx * 3 + 2] = timestamp_high;
    }

    // x0 is always 0, for sanity
    assert_eq!(registers_buffer[0], 0);

    transcript.absorb(&registers_buffer);

    // continue with main RISC-V cycles
    let mut expected_input_pc = 0; // entry point
    let mut memory_grand_product_accumulator = Mersenne31Quartic::ONE;
    let mut delegation_set_accumulator = Mersenne31Quartic::ZERO;

    // loop over main circuit type
    let mut proof_output_0: ProofOutput<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 1> =
        MaybeUninit::uninit().assume_init();
    let mut proof_output_1: ProofOutput<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 1> =
        MaybeUninit::uninit().assume_init();
    let mut state_variables = ProofPublicInputs::uninit();

    let num_circuits = verifier_common::DefaultNonDeterminismSource::read_word();
    assert!(num_circuits > 0);
    if BASE_LAYER {
        assert!(num_circuits <= MAX_BASE_LAYER_CIRCUITS as u32);
    } else {
        assert!(num_circuits <= MAX_RECURSION_LAYER_CIRCUITS as u32);
    }
    for circuit_sequence in 0..num_circuits {
        let (current, previous) = if circuit_sequence & 1 == 0 {
            (&mut proof_output_0, &proof_output_1)
        } else {
            (&mut proof_output_1, &proof_output_0)
        };
        // Note: this will make sure that all external challenges are the same as we progress,
        // and so we will only need to save the result at the very end
        (main_risc_v_circuit_verifier)(current, &mut state_variables);

        assert_eq!(current.circuit_sequence, circuit_sequence);
        assert_eq!(current.delegation_type, 0);

        if circuit_sequence == 0 {
            // commit setup into transcript
            transcript.absorb(current.setup_caps_flattened());
        }
        // and commit memory caps
        transcript.absorb(current.memory_caps_flattened());

        // now we should check all invariants about continuity

        // first over ProofOutput
        if circuit_sequence > 0 {
            // and check equality of the setup
            assert!(MerkleTreeCap::compare(
                &previous.setup_caps,
                &current.setup_caps
            ));
            // check that all challenges are the same
            assert_eq!(previous.memory_challenges, current.memory_challenges);
            assert_eq!(
                previous.delegation_challenges,
                current.delegation_challenges
            );

            // check lazy inits
            let last_previous = parse_field_els_as_u32_checked(
                previous.lazy_init_boundary_values[0].lazy_init_one_before_last_row,
            );
            let first_current = parse_field_els_as_u32_checked(
                current.lazy_init_boundary_values[0].lazy_init_first_row,
            );

            // if it's
            if first_current > last_previous {
                // nothing, we are all good
            } else {
                // we require padding of 0 init address, and 0 teardown value and timestamp
                let teardown_value = parse_field_els_as_u32_checked(
                    previous.lazy_init_boundary_values[0].teardown_value_one_before_last_row,
                );
                let teardown_timestamp = parse_field_els_as_u32_checked(
                    previous.lazy_init_boundary_values[0].teardown_timestamp_one_before_last_row,
                );
                assert_eq!(last_previous, 0);
                assert_eq!(teardown_value, 0);
                assert_eq!(teardown_timestamp, 0);
            }
        }
        // then over state variables

        // check continuous PC
        let start_pc = parse_field_els_as_u32_checked(state_variables.input_state_variables);
        assert_eq!(start_pc, expected_input_pc);
        let end_pc = parse_field_els_as_u32_checked(state_variables.output_state_variables);
        expected_input_pc = end_pc;

        // update accumulators
        memory_grand_product_accumulator.mul_assign(&current.memory_grand_product_accumulator);
        if NUM_DELEGATION_CHALLENGES > 0 {
            delegation_set_accumulator.add_assign(&current.delegation_argument_accumulator[0]);
        }
    }

    // If we will even want to break an execution here, we will have full buffer (unflushed)
    assert!(transcript.get_current_buffer_offset() == BLAKE2S_BLOCK_SIZE_U32_WORDS);

    // since we have > 0 main circuits, then we can always use `proof_output_0` below

    // ok, now we forget about main circuit and potentially parse delegations
    if NUM_DELEGATION_CHALLENGES > 0 {
        let mut previous_delegation_type = 0u32;
        let mut state_variables = ProofPublicInputs::uninit();
        let mut delegation_proof_output = MaybeUninit::uninit().assume_init();

        let mut total_delegation_requests = 0u64;

        for (delegation_type, delegation_requests_per_circuit, setup_caps, verification_function) in
            delegation_circuits_verifiers.iter()
        {
            assert!(previous_delegation_type < *delegation_type);
            previous_delegation_type = *delegation_type;

            let num_circuits = verifier_common::DefaultNonDeterminismSource::read_word();

            if num_circuits > 0 {
                let mut buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
                buffer[0] = *delegation_type;
                transcript.absorb(&buffer);
            }

            for circuit_sequence in 0..num_circuits {
                // Note: this will make sure that all external challenges are the same as we progress,
                // and so we will only need to save the result at the very end
                (verification_function)(&mut delegation_proof_output, &mut state_variables);

                assert_eq!(delegation_proof_output.circuit_sequence, 0);
                assert_eq!(delegation_proof_output.delegation_type, *delegation_type);
                assert!(MerkleTreeCap::compare(
                    &delegation_proof_output.setup_caps,
                    setup_caps
                ));

                // and commit memory caps
                transcript.absorb(delegation_proof_output.memory_caps_flattened());

                // check that we use the same challenges
                assert_eq!(
                    delegation_proof_output.memory_challenges,
                    proof_output_0.memory_challenges
                );
                assert_eq!(
                    delegation_proof_output.delegation_challenges,
                    proof_output_0.delegation_challenges
                );

                // update accumulators
                memory_grand_product_accumulator
                    .mul_assign(&delegation_proof_output.memory_grand_product_accumulator);
                delegation_set_accumulator
                    .sub_assign(&delegation_proof_output.delegation_argument_accumulator[0]);

                total_delegation_requests += (*delegation_requests_per_circuit) as u64;
            }

            // If we will even want to break an execution here, we will have full buffer (unflushed)
            assert!(transcript.get_current_buffer_offset() == BLAKE2S_BLOCK_SIZE_U32_WORDS);
        }

        // we use LogUp like argument for permutation between all delegation requests and responses.
        // All requests are unique (due to timestamps), so to ensure soundness we just require that total number
        // of responses processed it < field size
        assert!(total_delegation_requests < Mersenne31Field::CHARACTERISTICS as u64);
    }

    // finish with the transcript, compare memory values from transcript with ones used in proofs
    let memory_seed = transcript.finalize_reset();

    let expected_challenges =
        ExternalChallenges::draw_from_transcript_seed(memory_seed, NUM_DELEGATION_CHALLENGES > 0);
    assert_eq!(
        expected_challenges.memory_argument,
        proof_output_0.memory_challenges
    );
    if NUM_DELEGATION_CHALLENGES > 0 {
        assert_eq!(
            expected_challenges.delegation_argument.unwrap_unchecked(),
            proof_output_0.delegation_challenges[0]
        );
    }

    // conclude that our memory argument is valid
    let register_contribution =
        prover::definitions::produce_register_contribution_into_memory_accumulator_raw(
            core::mem::transmute(&registers_buffer),
            proof_output_0
                .memory_challenges
                .memory_argument_linearization_challenges,
            proof_output_0.memory_challenges.memory_argument_gamma,
        );
    memory_grand_product_accumulator.mul_assign(&register_contribution);
    assert_eq!(memory_grand_product_accumulator, Mersenne31Quartic::ONE);
    assert_eq!(delegation_set_accumulator, Mersenne31Quartic::ZERO);

    // Now we only need to reason about "which program do we execute", and "did it finish successfully or not".

    let mut output: [u32; 16] = MaybeUninit::uninit().assume_init();
    // in any case we carry registers 10-17 to the next layer - those are the output of the base program
    for i in 0..8 {
        output[i] = registers_buffer[(10 + i) * 3];
    }

    // the final piece is to make sure that we ended on the PC that is "expected" (basically - loops to itself, and at the right place),
    // so the program ended logical execution and we can conclude that the set of register values is meaningful

    let mut result_hasher = Blake2sBufferingTranscript::new();
    result_hasher.absorb(&[expected_input_pc]);
    result_hasher.absorb(proof_output_0.setup_caps_flattened());
    let end_params_output = result_hasher.finalize_reset();

    if BASE_LAYER {
        // we REQUIRE that remaining 8 registers are 0 in our convention
        let mut all_zeroes = true;
        for i in 8..16 {
            let value = registers_buffer[(10 + i) * 3];
            all_zeroes &= value == 0;
        }
        assert!(all_zeroes);

        // we only start a chain, so we will hash a concatenation of 8x0u32 and end_params_output
        let mut buffer = [0u32; 16];
        for i in 0..8 {
            buffer[8 + i] = end_params_output.0[i];
        }
        result_hasher.absorb(&buffer);
        let recursion_chain_output = result_hasher.finalize_reset();
        for i in 8..16 {
            output[i] = recursion_chain_output.0[i - 8];
        }
    } else {
        // we require that remaining 8 registers are some hash output in nature, that encodes our
        // chain of executed programs

        let mut aux_registers: [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS] =
            MaybeUninit::uninit().assume_init();
        for i in 8..16 {
            let value = registers_buffer[(10 + i) * 3];
            aux_registers[i - 8] = value;
        }

        // So prover can ALWAYS present a preimage
        let mut preimage: [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS * 2] =
            MaybeUninit::uninit().assume_init();
        for i in 0..BLAKE2S_DIGEST_SIZE_U32_WORDS * 2 {
            preimage[i] = verifier_common::DefaultNonDeterminismSource::read_word();
        }
        result_hasher.absorb(&preimage);
        let preimage_hash = result_hasher.finalize_reset();
        // manually unrolled to avoid memcmp
        let mut equal = true;
        for i in 0..8 {
            equal &= preimage_hash.0[i] == aux_registers[i];
        }
        assert!(equal);

        // then if last elements of the preimage are equal to the current end parameters - we do not need to continue the chain
        let mut equal = true;
        for i in 0..8 {
            equal &= preimage[i + 8] == end_params_output.0[i];
        }

        if equal {
            // we do not need to continue the chain. So for valid recursion chain is
            // always just a blake ( blake([0u32; 8] || base_program_end_params) || recursion_step_end_params)
            // for the case of all successful ends of execution
            for i in 8..16 {
                output[i] = aux_registers[i - 8];
            }
        } else {
            // concatenate and hash
            let mut input: [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS * 2] =
                MaybeUninit::uninit().assume_init();
            for i in 0..8 {
                input[i] = aux_registers[i];
                input[i + 8] = end_params_output.0[i];
            }
            result_hasher.absorb(&input);
            let new_output_registers = result_hasher.finalize_reset();
            for i in 8..16 {
                output[i] = new_output_registers.0[i - 8];
            }
        }
    }

    output
}

pub fn verify_base_layer() -> [u32; 16] {
    unsafe {
        verify_full_statement::<true>(
            RISC_V_VERIFIER_PTR,
            BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS,
        )
    }
}

pub fn verify_recursion_layer() -> [u32; 16] {
    unsafe {
        verify_full_statement::<false>(
            RISC_V_REDUCED_MACHINE_VERIFIER_PTR,
            RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS,
        )
    }
}

pub fn verify_final_recursion_layer() -> [u32; 16] {
    unsafe {
        verify_full_statement::<false>(
            RISC_V_FINAL_REDUCED_MACHINE_VERIFIER_PTR,
            FINAL_RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS,
        )
    }
}
