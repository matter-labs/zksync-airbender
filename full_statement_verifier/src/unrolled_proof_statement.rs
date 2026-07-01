use crate::statement_common::{
    read_setup_cap, FINAL_PC_BUFFER_PC_IDX, FINAL_PC_BUFFER_TS_HIGH_IDX, FINAL_PC_BUFFER_TS_LOW_IDX,
};
use common_constants::{INITIAL_PC, INITIAL_TIMESTAMP};
use verifier_common::cs::definitions::split_timestamp;
use verifier_common::cs::definitions::NUM_REGISTERS;

use super::*;
use crate::delegation_params::*;
use crate::unrolled_circuit_params::*;

/// If we recurse over user's program -> we must provide expected final PC,
/// and setup caps (that encode the program itself!),
/// otherwise we only need to provide final PC
#[allow(invalid_value)]
#[inline(never)]
pub unsafe fn verify_full_statement_for_unrolled_circuits<
    I: NonDeterminismSource<BabyBearField>,
    E: ErrorCreator,
    const BASE_LAYER: bool,
    const REDUCED_ROUNDS: bool,
>(
    circuits_families_setups: &[&MerkleTreeCap<{ prover::definitions::DEFAULT_CAP_SIZE }>],
    // circuit type/delegation type, verifier function
    circuits_families_verifiers: &[(
        u32,
        fn(
            &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
            &mut I,
        ) -> Result<crate::imports::UnrolledCircuitOutput, E::Error>,
    )],
    inits_and_teardowns_verifier: fn(
        &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
        &mut I,
    ) -> Result<
        crate::imports::InitsAndTeardownsCircuitOutput,
        E::Error,
    >,
    // circuit type/delegation type, capacity, setup, verifier function
    delegation_circuits_params: &[DelegationCircuitSetupData<{ prover::definitions::DEFAULT_CAP_SIZE }>;
         NUM_DELEGATION_CIRCUIT_TYPES],
    delegation_circuits_verifiers: &[fn(
        &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
        &mut I,
    ) -> Result<crate::imports::DelegationCircuitOutput, E::Error>;
         NUM_DELEGATION_CIRCUIT_TYPES],
    nd_source: &mut I,
) -> Result<[u32; 16], E::Error> {
    assert_eq!(
        circuits_families_setups.len(),
        circuits_families_verifiers.len()
    );
    debug_assert!(circuits_families_verifiers.is_sorted_by(|a, b| { a.0 < b.0 }));
    // we should in parallel verify proofs, and drag along the transcript to assert equality of challenges
    let mut transcript = Blake2sBufferingTranscript::<REDUCED_ROUNDS>::new();

    let mut registers_buffer = MaybeUninit::<[u32; 32 + 2 * 32]>::uninit().assume_init();

    // first we need to get final register values and timestamps
    for reg_idx in 0..32 {
        let value = nd_source.read_word();
        let timestamp_low = nd_source.read_word();
        let timestamp_high = nd_source.read_word();
        registers_buffer[reg_idx * 3] = value;
        registers_buffer[reg_idx * 3 + 1] = timestamp_low;
        registers_buffer[reg_idx * 3 + 2] = timestamp_high;
    }

    // x0 is always 0, for sanity
    assert_eq!(registers_buffer[0], 0);

    transcript.absorb(&registers_buffer);

    let mut final_pc_buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
    let final_pc = nd_source.read_word();
    let final_ts_low = nd_source.read_word();
    let final_ts_high = nd_source.read_word();
    final_pc_buffer[FINAL_PC_BUFFER_PC_IDX] = final_pc;
    final_pc_buffer[FINAL_PC_BUFFER_TS_LOW_IDX] = final_ts_low;
    final_pc_buffer[FINAL_PC_BUFFER_TS_HIGH_IDX] = final_ts_high;

    transcript.absorb(&final_pc_buffer);

    // continue with main RISC-V cycles
    let mut read_set_product_accumulator = BabyBearExt4::ONE;
    let mut write_set_product_accumulator = BabyBearExt4::ONE;

    // NOTE: in unrolled circuits we do have contribution from setup values into
    // memory or delegation, so we skip setups here (same as we do with delegation circuits in general)

    // read external challenges
    let external_challenges =
        ::verifier_common::read_external_challenges::<BabyBearField, BabyBearExt4, I>(nd_source);

    let mut total_cycles = 0u64;
    for ((circuit_family, verifier_fn), setup) in circuits_families_verifiers
        .iter()
        .zip(circuits_families_setups.iter())
    {
        let num_circuits = nd_source.read_word();
        if num_circuits > 0 {
            let mut buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
            buffer[0] = *circuit_family;
            transcript.absorb(&buffer);
        }

        for _circuit_sequence in 0..num_circuits {
            total_cycles += 1u64 << 24; // TODO
            assert!(total_cycles < MAX_CYCLES);

            let proof_output = (*verifier_fn)(&external_challenges, nd_source)?;

            // and commit memory caps
            transcript.absorb(proof_output.memory_caps_flattened());

            // now we should check all invariants about continuity

            assert!(MerkleTreeCap::compare_single_with_flattened(
                *setup,
                &proof_output.setup_caps[0]
            ));

            // update accumulators
            read_set_product_accumulator
                .mul_assign(&proof_output.grand_product_read_set_accumulator);
            write_set_product_accumulator
                .mul_assign(&proof_output.grand_product_write_set_accumulator);
        }
    }

    // then init/teardown circuits - we expect to have exactly 1
    {
        let num_circuits = nd_source.read_word();
        assert_eq!(num_circuits, 1);
        if num_circuits > 0 {
            let mut buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
            buffer[0] =
                common_constants::circuit_families::INITS_AND_TEARDOWNS_FORMAL_CIRCUIT_FAMILY_IDX
                    as u32;
            transcript.absorb(&buffer);
        }

        for _circuit_sequence in 0..num_circuits {
            let proof_output = (inits_and_teardowns_verifier)(&external_challenges, nd_source)?;

            // we expect that for all the top bits we have a continuous sequence
            for i in 0..proof_output.inits_and_teardowns_top_bits.len() {
                assert_eq!(i as u32, proof_output.inits_and_teardowns_top_bits[i]);
            }

            // and commit memory caps
            transcript.absorb(proof_output.memory_caps_flattened());

            // there is no setup for inits/teardowns
            debug_assert_eq!(proof_output.setup_caps.len(), 0);

            // update accumulators
            read_set_product_accumulator
                .mul_assign(&proof_output.grand_product_read_set_accumulator);
            write_set_product_accumulator
                .mul_assign(&proof_output.grand_product_write_set_accumulator);
        }
    }

    // If we will even want to break an execution here, we will have full buffer (unflushed)
    assert!(transcript.get_current_buffer_offset() == BLAKE2S_BLOCK_SIZE_U32_WORDS);

    let mut total_permutation_elements = total_cycles << 2; // 4 permutation elements per cycle - 1 from machine state and 3 memory accesses

    // ok, now we forget about main circuit and potentially parse delegations
    {
        for (delegation_circuit_params, verifier_fn) in delegation_circuits_params
            .iter()
            .zip(delegation_circuits_verifiers)
        {
            let num_circuits = nd_source.read_word();

            if num_circuits > 0 {
                let mut buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
                buffer[0] = delegation_circuit_params.delegation_type;
                transcript.absorb(&buffer);
            }

            for _circuit_sequence in 0..num_circuits {
                let proof_output = (verifier_fn)(&external_challenges, nd_source)?;

                // and commit memory caps
                transcript.absorb(proof_output.memory_caps_flattened());

                assert!(MerkleTreeCap::compare_single_with_flattened(
                    &delegation_circuit_params.setup_cap,
                    &proof_output.setup_caps[0]
                ));

                // update accumulators
                read_set_product_accumulator
                    .mul_assign(&proof_output.grand_product_read_set_accumulator);
                write_set_product_accumulator
                    .mul_assign(&proof_output.grand_product_write_set_accumulator);

                total_permutation_elements +=
                    delegation_circuit_params.num_permutation_terms_per_circuit as u64;
            }

            // If we will even want to break an execution here, we will have full buffer (unflushed)
            assert!(transcript.get_current_buffer_offset() == BLAKE2S_BLOCK_SIZE_U32_WORDS);
        }
    }

    // TODO: assert that number of permutation elements is less than we computed for security levels
    assert!(total_permutation_elements < 1u64 << 40);

    // finish with the transcript, compare memory values from transcript with ones used in proofs
    let memory_seed = transcript.finalize_reset();

    let pow_challenge_low = nd_source.read_word();
    let pow_challenge_high = nd_source.read_word();
    let pow_challenge = (pow_challenge_high as u64) << 32 | (pow_challenge_low as u64);

    let expected_challenges = GKRExternalChallenges::draw_from_transcript_seed(
        memory_seed,
        MEMORY_DELEGATION_POW_BITS,
        pow_challenge,
    );

    assert_eq!(expected_challenges, external_challenges);

    // conclude that our memory argument is valid
    let (machine_state_read_set_contribution, machine_state_write_set_contribution) =
        prover::definitions::produce_initial_permutation_product_separate_contributions(
            core::mem::transmute::<_, &[(u32, (u32, u32)); NUM_REGISTERS]>(&registers_buffer),
            INITIAL_PC,
            split_timestamp(INITIAL_TIMESTAMP),
            final_pc,
            (final_ts_low, final_ts_high),
            &external_challenges,
        );

    read_set_product_accumulator.mul_assign(&machine_state_read_set_contribution);
    write_set_product_accumulator.mul_assign(&machine_state_write_set_contribution);

    assert_eq!(read_set_product_accumulator, write_set_product_accumulator);

    // Now we only need to reason about "which program do we execute", and "did it finish successfully or not".

    let mut output: [u32; 16] = MaybeUninit::uninit().assume_init();
    // in any case we carry registers 10-17 to the next layer - those are the output of the base program
    for i in 0..8 {
        output[i] = registers_buffer[(10 + i) * 3];
    }

    // the final piece is to make sure that we ended on the PC that is "expected" (basically - loops to itself, and at the right place),
    // so the program ended logical execution and we can conclude that the set of register values is meaningful

    let mut result_hasher = Blake2sBufferingTranscript::<REDUCED_ROUNDS>::new();
    // NOTE: for parameters we are no longer interested in the timestamp when we ended execution,
    // just on PC
    final_pc_buffer[FINAL_PC_BUFFER_TS_LOW_IDX] = 0;
    final_pc_buffer[FINAL_PC_BUFFER_TS_HIGH_IDX] = 0;

    result_hasher.absorb(&final_pc_buffer);
    for setup in circuits_families_setups.iter() {
        result_hasher.absorb(MerkleTreeCap::flatten_single(*setup));
    }
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
            preimage[i] = nd_source.read_word();
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

    Ok(output)
}

pub fn verify_unrolled_base_layer<
    I: NonDeterminismSource<BabyBearField>,
    E: ErrorCreator,
    const REDUCED_ROUNDS: bool,
>(
    nd_source: &mut I,
) -> Result<[u32; 16], E::Error> {
    unsafe {
        let circuits_setups: [MerkleTreeCap<_>; NUM_BASE_LAYER_CIRCUITS] =
            core::array::from_fn(|_| {
                read_setup_cap::<I, { prover::definitions::DEFAULT_CAP_SIZE }>(nd_source)
            });
        let circuits_setups_refs = circuits_setups.each_ref();
        verify_full_statement_for_unrolled_circuits::<I, E, true, REDUCED_ROUNDS>(
            &circuits_setups_refs,
            &crate::unrolled_circuit_params::unrolled_circuit_verifiers_for_base_layer::<I, E>(),
            crate::unrolled_circuit_params::inits_and_teardowns_verifier::<I, E>(),
            &crate::constants::DELEGATION_CIRCUITS_SETUP_PARAMS,
            &crate::delegation_params::all_delegation_circuit_verifiers::<I, E>(),
            nd_source,
        )
    }
}

pub fn verify_unrolled_recursion_layer<
    I: NonDeterminismSource<BabyBearField>,
    E: ErrorCreator,
    const REDUCED_ROUNDS: bool,
>(
    nd_source: &mut I,
) -> Result<[u32; 16], E::Error> {
    unsafe {
        let circuits_setups: [MerkleTreeCap<_>; NUM_RECURSION_LAYER_CIRCUITS] =
            core::array::from_fn(|_| {
                read_setup_cap::<I, { prover::definitions::DEFAULT_CAP_SIZE }>(nd_source)
            });
        let circuits_setups_refs = circuits_setups.each_ref();
        verify_full_statement_for_unrolled_circuits::<I, E, false, REDUCED_ROUNDS>(
            &circuits_setups_refs,
            &crate::unrolled_circuit_params::unrolled_circuit_verifiers_for_recursion_layer::<I, E>(
            ),
            crate::unrolled_circuit_params::inits_and_teardowns_verifier::<I, E>(),
            &crate::constants::DELEGATION_CIRCUITS_SETUP_PARAMS,
            &crate::delegation_params::all_delegation_circuit_verifiers::<I, E>(),
            nd_source,
        )
    }
}

pub fn verify_base_or_recursion_unrolled_circuits<
    I: NonDeterminismSource<BabyBearField>,
    E: ErrorCreator,
    const REDUCED_ROUNDS: bool,
>(
    nd_source: &mut I,
) -> Result<[u32; 16], E::Error> {
    // we just branch
    let op_type = nd_source.read_word();
    use crate::definitions::*;
    match op_type {
        OP_VERIFY_BASE_LAYER_IN_UNROLLED_CIRCUITS => {
            verify_unrolled_base_layer::<I, E, REDUCED_ROUNDS>(nd_source)
        }
        OP_VERIFY_RECURSIVE_LAYER_IN_UNROLLED_CIRCUITS => {
            verify_unrolled_recursion_layer::<I, E, REDUCED_ROUNDS>(nd_source)
        }
        _ => {
            panic!("Unknown op");
        }
    }
}
