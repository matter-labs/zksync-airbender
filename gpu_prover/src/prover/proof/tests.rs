use super::*;

use crate::primitives::field::{BF, E4};
use crate::upstream::{
    assemble_query_index, draw_query_bits, BitSource, GKRExternalChallenges, Seed, Transcript,
};
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use worker::Worker;

fn draw_query_bits_with_external_nonce(
    seed: &mut Seed,
    num_bits_for_queries: usize,
    pow_bits: u32,
    external_nonce: u64,
) -> (u64, BitSource) {
    if pow_bits == 0 {
        assert_eq!(
            external_nonce, 0,
            "pow_bits=0 expects the external nonce to be zero",
        );
    }
    Transcript::verify_pow(seed, external_nonce, pow_bits);

    (
        external_nonce,
        draw_query_bits_after_verified_pow(seed, num_bits_for_queries),
    )
}

fn draw_query_bits_after_verified_pow(seed: &mut Seed, num_bits_for_queries: usize) -> BitSource {
    let num_required_words =
        num_bits_for_queries.next_multiple_of(u32::BITS as usize) / (u32::BITS as usize);
    let num_required_words_padded =
        (num_required_words + 1).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
    let mut source = vec![0u32; num_required_words_padded];
    Transcript::draw_randomness(seed, &mut source);

    BitSource::new(source[1..].to_vec())
}

fn build_initial_transcript_input(
    canonical_top_bits: &[u32],
    external_challenges: &GKRExternalChallenges<BF, E4>,
    flattened_setup_tree_caps: &[u32],
    flattened_memory_tree_caps: &[u32],
    flattened_witness_tree_caps: &[u32],
) -> Vec<u32> {
    let mut transcript_input = Vec::new();
    transcript_input.extend_from_slice(canonical_top_bits);
    external_challenges.flatten_into_buffer(&mut transcript_input);
    if !flattened_setup_tree_caps.is_empty() {
        transcript_input.extend_from_slice(flattened_setup_tree_caps);
    }
    if !flattened_memory_tree_caps.is_empty() {
        transcript_input.extend_from_slice(flattened_memory_tree_caps);
    }
    if !flattened_witness_tree_caps.is_empty() {
        transcript_input.extend_from_slice(flattened_witness_tree_caps);
    }

    transcript_input
}

#[test]
fn external_nonce_query_bits_match_cpu_draw_query_bits() {
    let worker = Worker::new();
    let cases = [
        (Seed([1, 2, 3, 4, 5, 6, 7, 8]), 23usize, 22usize, 24u32),
        (
            Seed([11, 12, 13, 14, 15, 16, 17, 18]),
            12usize,
            21usize,
            24u32,
        ),
        (
            Seed([21, 22, 23, 24, 25, 26, 27, 28]),
            10usize,
            18usize,
            16u32,
        ),
        (
            Seed([31, 32, 33, 34, 35, 36, 37, 38]),
            10usize,
            14usize,
            0u32,
        ),
    ];

    for (seed, num_queries, query_index_bits, pow_bits) in cases {
        let num_bits_for_queries = num_queries * query_index_bits;
        let mut cpu_seed = seed;
        let mut external_seed = seed;
        let (cpu_nonce, mut cpu_bits) =
            draw_query_bits(&mut cpu_seed, num_bits_for_queries, pow_bits, &worker);
        let (external_nonce, mut external_bits) = draw_query_bits_with_external_nonce(
            &mut external_seed,
            num_bits_for_queries,
            pow_bits,
            cpu_nonce,
        );

        assert_eq!(external_nonce, cpu_nonce, "external nonce changed");
        assert_eq!(external_seed, cpu_seed, "seed after external PoW diverged");

        let mut cpu_indexes = Vec::with_capacity(num_queries);
        let mut external_indexes = Vec::with_capacity(num_queries);
        for _ in 0..num_queries {
            cpu_indexes.push(assemble_query_index(query_index_bits, &mut cpu_bits));
            external_indexes.push(assemble_query_index(query_index_bits, &mut external_bits));
        }
        assert_eq!(
            external_indexes, cpu_indexes,
            "query indexes diverged for pow_bits={pow_bits}"
        );
    }
}

#[test]
fn initial_transcript_input_matches_cpu_order_with_and_without_setup_caps() {
    let external_challenges = GKRExternalChallenges {
        permutation_argument_linearization_challenges: std::array::from_fn(|idx| {
            E4::from_array_of_base([
                BF::new(10 + idx as u32),
                BF::new(20 + idx as u32),
                BF::new(30 + idx as u32),
                BF::new(40 + idx as u32),
            ])
        }),
        permutation_argument_additive_part: E4::from_array_of_base([
            BF::new(1),
            BF::new(2),
            BF::new(3),
            BF::new(4),
        ]),
        _marker: std::marker::PhantomData,
    };
    let canonical_top_bits = vec![0u32, 1, 2, 3];
    let setup_caps = vec![11u32, 12, 13, 14];
    let memory_caps = vec![21u32, 22, 23, 24];
    let witness_caps = vec![31u32, 32, 33, 34];

    let with_setup = build_initial_transcript_input(
        &canonical_top_bits,
        &external_challenges,
        &setup_caps,
        &memory_caps,
        &witness_caps,
    );
    let without_setup = build_initial_transcript_input(
        &canonical_top_bits,
        &external_challenges,
        &[],
        &memory_caps,
        &witness_caps,
    );

    let mut expected_with_setup = canonical_top_bits.clone();
    external_challenges.flatten_into_buffer(&mut expected_with_setup);
    expected_with_setup.extend_from_slice(&setup_caps);
    expected_with_setup.extend_from_slice(&memory_caps);
    expected_with_setup.extend_from_slice(&witness_caps);
    assert_eq!(with_setup, expected_with_setup);

    let mut expected_without_setup = canonical_top_bits.clone();
    external_challenges.flatten_into_buffer(&mut expected_without_setup);
    expected_without_setup.extend_from_slice(&memory_caps);
    expected_without_setup.extend_from_slice(&witness_caps);
    assert_eq!(without_setup, expected_without_setup);

    let with_setup_seed = Transcript::commit_initial(&with_setup);
    let mut expected_with_setup_seed = canonical_top_bits.clone();
    external_challenges.flatten_into_buffer(&mut expected_with_setup_seed);
    expected_with_setup_seed.extend_from_slice(&setup_caps);
    expected_with_setup_seed.extend_from_slice(&memory_caps);
    expected_with_setup_seed.extend_from_slice(&witness_caps);
    assert_eq!(
        with_setup_seed,
        Transcript::commit_initial(&expected_with_setup_seed)
    );

    let without_setup_seed = Transcript::commit_initial(&without_setup);
    let mut expected_without_setup_seed = canonical_top_bits;
    external_challenges.flatten_into_buffer(&mut expected_without_setup_seed);
    expected_without_setup_seed.extend_from_slice(&memory_caps);
    expected_without_setup_seed.extend_from_slice(&witness_caps);
    assert_eq!(
        without_setup_seed,
        Transcript::commit_initial(&expected_without_setup_seed)
    );
}
