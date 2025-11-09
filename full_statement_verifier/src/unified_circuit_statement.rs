use super::*;
use crate::unrolled_proof_statement::read_setups;
use common_constants::{INITIAL_PC, INITIAL_TIMESTAMP};
use verifier_common::{cs::definitions::split_timestamp, DefaultNonDeterminismSource};

pub const REDUCED_UNIFIED_CIRCUIT_VERIFIER_PTR: VerifierFunctionPointer<
    CAP_SIZE,
    NUM_COSETS,
    1,
    1,
    0,
    1,
> = unified_reduced_machine_verifier::verify;
pub const REDUCED_UNIFIED_CIRCUIT_CAPACITY: u32 =
    (unified_reduced_machine_verifier::concrete::size_constants::TRACE_LEN - 1) as u32;

/// Unified circuit inherits PC + timestamp permutation technique from unrolled ones,
/// but also keeps inits and teardowns in the one an only circuit
#[allow(invalid_value)]
#[inline(never)]
pub unsafe fn verify_unified_circuit_statement<const BASE_LAYER: bool>(
    unified_circuit_setup: &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    unified_circuit_capacity: u32,
    unified_circuit_verifier: VerifierFunctionPointer<
        CAP_SIZE,
        NUM_COSETS,
        NUM_DELEGATION_CHALLENGES,
        1,
        0,
        1,
    >,
    delegation_circuits_verifiers: &[(
        u32,
        u32,
        &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
        VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0, 0>,
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

    use crate::unrolled_proof_statement::*;

    let mut final_pc_buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
    let final_pc = verifier_common::DefaultNonDeterminismSource::read_word();
    let final_ts_low = verifier_common::DefaultNonDeterminismSource::read_word();
    let final_ts_high = verifier_common::DefaultNonDeterminismSource::read_word();
    final_pc_buffer[FINAL_PC_BUFFER_PC_IDX] = final_pc;
    final_pc_buffer[FINAL_PC_BUFFER_TS_LOW_IDX] = final_ts_low;
    final_pc_buffer[FINAL_PC_BUFFER_TS_HIGH_IDX] = final_ts_high;

    transcript.absorb(&final_pc_buffer);

    // continue with main RISC-V cycles
    let mut grand_product_accumulator = Mersenne31Quartic::ONE;
    let mut delegation_set_accumulator = Mersenne31Quartic::ZERO;

    // loop over main circuit type
    let mut proof_output_0: ProofOutput<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 1, 1> =
        MaybeUninit::uninit().assume_init();
    let mut proof_output_1: ProofOutput<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 1, 1> =
        MaybeUninit::uninit().assume_init();
    let mut state_variables = ProofPublicInputs::uninit();

    let num_circuits = verifier_common::DefaultNonDeterminismSource::read_word();
    assert!(num_circuits > 0);
    let mut buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
    buffer[0] = common_constants::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32;
    transcript.absorb(&buffer);

    let mut total_cycles = 0u64;
    for circuit_sequence in 0..num_circuits {
        total_cycles += unified_circuit_capacity as u64;
        assert!(total_cycles < MAX_CYCLES);
        let (current, previous) = if circuit_sequence & 1 == 0 {
            (&mut proof_output_0, &proof_output_1)
        } else {
            (&mut proof_output_1, &proof_output_0)
        };
        // Note: this will make sure that all external challenges are the same as we progress,
        // and so we will only need to save the result at the very end
        (unified_circuit_verifier)(current, &mut state_variables);

        // Circuit sequence is legacy and unused
        assert_eq!(current.circuit_sequence, 0);
        assert_eq!(current.delegation_type, 0);

        // and commit memory caps
        transcript.absorb(current.memory_caps_flattened());

        // now we should check all invariants about continuity

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

            // and we also check inits/teardowns
            // check lazy inits
            let last_previous = parse_field_els_as_u32_from_u16_limbs_checked(
                previous.lazy_init_boundary_values[0].lazy_init_one_before_last_row,
            );
            let first_current = parse_field_els_as_u32_from_u16_limbs_checked(
                current.lazy_init_boundary_values[0].lazy_init_first_row,
            );

            if first_current > last_previous {
                // nothing, we are all good
            } else {
                // we require padding of 0 init address, and 0 teardown value and timestamp
                assert_eq!(last_previous, 0);

                // just compare to 0 after reduction to avoid parsing u16 or timestamp bits
                assert_eq!(
                    previous.lazy_init_boundary_values[0].teardown_value_one_before_last_row[0]
                        .to_reduced_u32(),
                    0
                );
                assert_eq!(
                    previous.lazy_init_boundary_values[0].teardown_value_one_before_last_row[1]
                        .to_reduced_u32(),
                    0
                );

                assert_eq!(
                    previous.lazy_init_boundary_values[0].teardown_timestamp_one_before_last_row[0]
                        .to_reduced_u32(),
                    0
                );
                assert_eq!(
                    previous.lazy_init_boundary_values[0].teardown_timestamp_one_before_last_row[1]
                        .to_reduced_u32(),
                    0
                );
            }
        } else {
            assert!(MerkleTreeCap::compare(
                unified_circuit_setup,
                &current.setup_caps
            ));
        }

        // update accumulators
        grand_product_accumulator.mul_assign(&current.grand_product_accumulator);
        if NUM_DELEGATION_CHALLENGES > 0 {
            delegation_set_accumulator.add_assign(&current.delegation_argument_accumulator[0]);
        }
    }

    // NOTE: it's purely to match dumping code for unrolled circuits
    let num_init_and_teardown_circuits = verifier_common::DefaultNonDeterminismSource::read_word();
    assert_eq!(num_init_and_teardown_circuits, 0);

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

            for _circuit_sequence in 0..num_circuits {
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
                grand_product_accumulator
                    .mul_assign(&delegation_proof_output.grand_product_accumulator);
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
    let machine_state_contribution =
        prover::definitions::produce_pc_into_permutation_accumulator_raw(
            INITIAL_PC,
            split_timestamp(INITIAL_TIMESTAMP),
            final_pc,
            (final_ts_low, final_ts_high),
            &proof_output_0.machine_state_permutation_challenges[0].linearization_challenges,
            &proof_output_0.machine_state_permutation_challenges[0].additive_term,
        );
    grand_product_accumulator.mul_assign(&register_contribution);
    grand_product_accumulator.mul_assign(&machine_state_contribution);

    assert_eq!(grand_product_accumulator, Mersenne31Quartic::ONE);
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
    final_pc_buffer[FINAL_PC_BUFFER_TS_LOW_IDX] = 0;
    final_pc_buffer[FINAL_PC_BUFFER_TS_HIGH_IDX] = 0;

    result_hasher.absorb(&final_pc_buffer);
    result_hasher.absorb(proof_output_0.setup_caps_flattened());
    let end_params_output = result_hasher.finalize_reset();

    // `end_params_output` now fully describes an ending PC + setups (and setups include program binary)

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

pub fn verify_unified_circuit_recursion_layer() -> [u32; 16] {
    unsafe {
        let main_setup = read_setups::<DefaultNonDeterminismSource, 1>();
        verify_unified_circuit_statement::<false>(
            &main_setup[0],
            REDUCED_UNIFIED_CIRCUIT_CAPACITY,
            REDUCED_UNIFIED_CIRCUIT_VERIFIER_PTR,
            RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS,
        )
    }
}

pub const OP_VERIFY_UNROLLED_RECURSION_LAYER: u32 = 1;
pub const OP_VERIFY_UNIFIED_RECURSION_LAYER: u32 = 2;

pub fn verify_unrolled_or_unified_circuit_recursion_layer() -> [u32; 16] {
    // we just branch
    let op_type = DefaultNonDeterminismSource::read_word();
    match op_type {
        OP_VERIFY_UNROLLED_RECURSION_LAYER => {
            crate::unrolled_proof_statement::verify_unrolled_recursion_layer()
        }
        OP_VERIFY_UNIFIED_RECURSION_LAYER => verify_unified_circuit_recursion_layer(),
        _ => {
            panic!("Uknown op");
        }
    }
}
