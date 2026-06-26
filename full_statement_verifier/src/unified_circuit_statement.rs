use super::*;
use crate::delegation_params::*;
use crate::imports::{DelegationCircuitOutput, UnifiedCircuitOutput};
use crate::statement_common::{
    read_setup_cap, FINAL_PC_BUFFER_PC_IDX, FINAL_PC_BUFFER_TS_HIGH_IDX, FINAL_PC_BUFFER_TS_LOW_IDX,
};
use common_constants::{INITIAL_PC, INITIAL_TIMESTAMP};
use prover::definitions::DEFAULT_CAP_SIZE;
use verifier_common::cs::definitions::split_timestamp;

/// Full-statement verifier for the unified reduced-machine circuit (recursion layer only).
///
/// Mirrors [`crate::unrolled_proof_statement::verify_full_statement_for_unrolled_circuits`]
/// but with the unified circuit's specifics:
/// - a single folded reduced-machine family (no separate inits/teardowns circuit);
/// - inits/teardowns are carried only by the **last `num_it_circuits`** instances (the
///   prover sends `num_it_circuits` as an extra word). For those trailing instances we
///   multiply their (now separately-surfaced) i/t grand-product into the accumulators and
///   require their `top_bits` to be **strictly increasing**.
///
/// Multiple unified instances are sound: the GKR-verified i/t address window is bound to
/// each instance's runtime, FS-committed `top_bits` (the generated verifier computes
/// `set_bits = top_bits[set_idx] << shift`, mirroring the prover), so the
/// `MAX_TOP_BIT`-bounded, strictly-increasing `top_bits` sequence forces the i/t-carrying
/// instances onto disjoint memory super-blocks. A prover therefore cannot make two
/// instances cover the same range while reporting distinct `top_bits`.
#[allow(invalid_value)]
#[inline(never)]
pub unsafe fn verify_full_statement_for_unified_circuit<
    I: NonDeterminismSource,
    E: ErrorCreator,
    const BASE_LAYER: bool,
    const REDUCED_ROUNDS: bool,
    UniVerifyFn,
    DelVerifyFn,
>(
    unified_circuit_setup: &MerkleTreeCap<DEFAULT_CAP_SIZE>,
    unified_circuit_verifier: UniVerifyFn,
    delegation_circuits_params: &[DelegationCircuitSetupData<DEFAULT_CAP_SIZE>;
         NUM_DELEGATION_CIRCUIT_TYPES],
    delegation_circuits_verifiers: &[DelVerifyFn; NUM_DELEGATION_CIRCUIT_TYPES],
    nd_source: &mut I,
) -> Result<[u32; 16], E::Error>
where
    UniVerifyFn: Fn(
        &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
        &mut I,
    ) -> Result<UnifiedCircuitOutput, E::Error>,
    DelVerifyFn: Fn(
        &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
        &mut I,
    ) -> Result<DelegationCircuitOutput, E::Error>,
{
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

    let mut read_set_product_accumulator = BabyBearExt4::ONE;
    let mut write_set_product_accumulator = BabyBearExt4::ONE;

    // read external challenges
    let external_challenges =
        ::verifier_common::read_external_challenges::<BabyBearField, BabyBearExt4, I>(nd_source);

    // One or more reduced-machine instances with folded inits/teardowns. Multiple instances
    // are sound: the GKR-verified i/t address window is bound to each instance's runtime,
    // FS-committed `top_bits` (see `set_bits = top_bits[set_idx] << shift` in the generated
    // verifier), and the `MAX_TOP_BIT` ceiling + strictly-increasing `top_bits` check below
    // force the trailing i/t-carrying instances onto disjoint memory super-blocks.
    let num_unified_circuits = nd_source.read_word();
    assert!(num_unified_circuits > 0);

    // extra word: how many of the *trailing* circuits carry real inits/teardowns
    let num_it_circuits = nd_source.read_word();
    assert!(num_it_circuits >= 1);
    assert!(num_it_circuits <= num_unified_circuits);
    let first_it_circuit = num_unified_circuits - num_it_circuits;

    let mut total_cycles = 0u64;

    const ADDRESS_HIGH_BITS_SHIFT: u32 = 10;
    const MAX_TOP_BIT: u32 = 1 << (32 - 16 - ADDRESS_HIGH_BITS_SHIFT);

    // Strictly-increasing check over the concatenated `top_bits` of all i/t-carrying
    // instances. The GKR-verified i/t address window is now bound to exactly these runtime
    // `top_bits` (`set_bits = top_bits[set_idx] << shift`), and `MAX_TOP_BIT` keeps
    // each window inside the high-address field, so strictly-increasing top_bits ⇒ disjoint
    // per-instance super-blocks: no two instances can init/teardown the same range.
    let mut prev_top_bit: i32 = -1;
    let mut it_circuits_seen = 0u32;
    for circuit_sequence in 0..num_unified_circuits {
        // TODO: unified circuit's trace len.
        // This should be derived from the circuit, not hardcoded
        total_cycles += 1u64 << 24;
        assert!(total_cycles < MAX_CYCLES);

        let proof_output = (unified_circuit_verifier)(&external_challenges, nd_source)?;

        // Commit the reduced-machine family idx + THIS instance's inits/teardowns `top_bits`,
        // then the memory caps. Mirrors the prover's `fs_transform_unified_for_permutation_argument`:
        // binding `top_bits` into the Fiat-Shamir challenge (not just the memory columns) closes
        // the gap where a prover could pick the GKR i/t window's `top_bits` adaptively after
        // seeing the challenges. `INIT_AND_TEARDOWN_SETS < BLAKE2S_BLOCK_SIZE_U32_WORDS` holds for
        // the unified circuit, so the family idx + all top_bits fit in one transcript block.
        {
            let mut buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
            buffer[0] = common_constants::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32;
            // `top_bits` is a fixed-size `[u32; INIT_AND_TEARDOWN_SETS]`, so this copy has a
            // compile-time length: the transpiler unrolls it into word stores rather than a
            // runtime-bounded loop.
            let top_bits = &proof_output.inits_and_teardowns_top_bits;
            buffer[1..1 + top_bits.len()].copy_from_slice(top_bits);
            transcript.absorb(&buffer);
        }
        transcript.absorb(proof_output.memory_caps_flattened());

        // continuity: every instance shares the same setup
        assert!(MerkleTreeCap::compare_single_with_flattened(
            unified_circuit_setup,
            &proof_output.setup_caps[0]
        ));

        // execution-memory permutation product: include for ALL instances
        read_set_product_accumulator.mul_assign(&proof_output.grand_product_read_set_accumulator);
        write_set_product_accumulator.mul_assign(&proof_output.grand_product_write_set_accumulator);

        // inits/teardowns: include ONLY for the trailing instances; the rest are excluded.
        // Disjointness across these trailing instances is structurally backed by the GKR
        // window binding (their i/t address windows track the strictly-increasing,
        // ceiling-bounded `top_bits` checked below), not merely by this count split.
        if circuit_sequence >= first_it_circuit {
            let it = proof_output
                .inits_and_teardowns
                .expect("trailing unified instance must carry inits/teardowns");
            read_set_product_accumulator.mul_assign(&it.read_product);
            write_set_product_accumulator.mul_assign(&it.write_product);

            for top_bit in proof_output.inits_and_teardowns_top_bits.iter() {
                assert!(*top_bit < MAX_TOP_BIT, "top_bit out of range");
                assert!((*top_bit as i32) > prev_top_bit);
                prev_top_bit = *top_bit as i32;
            }
            it_circuits_seen += 1;
        } else {
            // we ask for conventional values
            for top_bit in proof_output.inits_and_teardowns_top_bits.iter() {
                assert_eq!(*top_bit, 0);
            }
        }
    }
    assert_eq!(it_circuits_seen, num_it_circuits);

    // If we will even want to break an execution here, we will have full buffer (unflushed)
    assert!(transcript.get_current_buffer_offset() == BLAKE2S_BLOCK_SIZE_U32_WORDS);

    let mut total_permutation_elements = total_cycles << 2; // 4 permutation elements per cycle

    // now parse delegations (same as unrolled circuits)
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
            core::mem::transmute::<_, &[(u32, (u32, u32)); 32]>(&registers_buffer),
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
    result_hasher.absorb(MerkleTreeCap::flatten_single(unified_circuit_setup));
    let end_params_output = result_hasher.finalize_reset();

    // `end_params_output` now fully describes an ending PC + setup (and setup includes program binary)

    if BASE_LAYER {
        // base layer: we REQUIRE that the remaining 8 registers are 0 in our convention,
        // and we START a fresh recursion chain (no preimage needed).
        let mut all_zeroes = true;
        for i in 8..16 {
            let value = registers_buffer[(10 + i) * 3];
            all_zeroes &= value == 0;
        }
        assert!(all_zeroes);

        // hash a concatenation of 8x0u32 and end_params_output
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
        // recursion layer: we require that the upper 8 registers are a hash output that encodes
        // our chain of executed programs.
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

pub fn verify_unified_circuit_base_layer<
    I: NonDeterminismSource,
    E: ErrorCreator,
    const REDUCED_ROUNDS: bool,
>(
    nd_source: &mut I,
) -> Result<[u32; 16], E::Error> {
    unsafe {
        let unified_setup =
            read_setup_cap::<I, { prover::definitions::DEFAULT_CAP_SIZE }>(nd_source);
        verify_full_statement_for_unified_circuit::<I, E, true, REDUCED_ROUNDS, _, _>(
            &unified_setup,
            crate::imports::unified_reduced_machine_sec_80::verify::<I, E>,
            &crate::constants::DELEGATION_CIRCUITS_SETUP_PARAMS,
            &crate::delegation_params::all_delegation_circuit_verifiers::<I, E>(),
            nd_source,
        )
    }
}

pub fn verify_unified_circuit_recursion_layer<
    I: NonDeterminismSource,
    E: ErrorCreator,
    const REDUCED_ROUNDS: bool,
>(
    nd_source: &mut I,
) -> Result<[u32; 16], E::Error> {
    unsafe {
        let unified_setup =
            read_setup_cap::<I, { prover::definitions::DEFAULT_CAP_SIZE }>(nd_source);
        verify_full_statement_for_unified_circuit::<I, E, false, REDUCED_ROUNDS, _, _>(
            &unified_setup,
            crate::imports::unified_reduced_machine_sec_80::verify::<I, E>,
            &crate::constants::DELEGATION_CIRCUITS_SETUP_PARAMS,
            &crate::delegation_params::all_delegation_circuit_verifiers::<I, E>(),
            nd_source,
        )
    }
}

pub fn verify_unrolled_or_unified_circuit_recursion_layer<
    I: NonDeterminismSource,
    E: ErrorCreator,
    const REDUCED_ROUNDS: bool,
>(
    nd_source: &mut I,
) -> Result<[u32; 16], E::Error> {
    // we just branch
    let op_type = nd_source.read_word();
    use crate::definitions::*;
    match op_type {
        OP_VERIFY_UNROLLED_RECURSION_LAYER_IN_UNIFIED_CIRCUIT => {
            #[cfg(feature = "verifiers")]
            {
                crate::unrolled_proof_statement::verify_unrolled_recursion_layer::<
                    I,
                    E,
                    REDUCED_ROUNDS,
                >(nd_source)
            }
            #[cfg(not(feature = "verifiers"))]
            {
                let _ = nd_source;
                panic!("Unrolled recursion layer verification is not available. Enable `verifiers` feature.");
            }
        }
        OP_VERIFY_UNIFIED_RECURSION_LAYER_IN_UNIFIED_CIRCUIT => {
            verify_unified_circuit_recursion_layer::<I, E, REDUCED_ROUNDS>(nd_source)
        }
        _ => {
            panic!("Unknown op");
        }
    }
}
