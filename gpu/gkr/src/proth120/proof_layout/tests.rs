use std::collections::BTreeSet;
use std::path::PathBuf;

use prover::gkr::prover::{CommitmentMode, GKRProof};
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use prover::transcript::{Keccak256Transcript, Transcript};
use serde::Deserialize;

use super::{M6ProofFields, ProofLayoutPr};
use crate::upstream::{SecurityLevel, PR};

pub(crate) fn programs() -> crate::proth120::programs::GkrProgramsPr {
    let artifact = serde_json::from_slice(include_bytes!(
        "../../../../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json"
    ))
    .unwrap();
    crate::proth120::programs::GkrProgramsPr::compile(
        gpu_trace::witness::circuit_type::CircuitType::L1Wrap,
        std::sync::Arc::new(artifact),
    )
    .unwrap()
}

#[repr(align(32))]
#[derive(Clone)]
#[allow(dead_code)]
struct AlignedBlock([u8; 32]);

pub(crate) struct HostSlab(Vec<AlignedBlock>);
impl HostSlab {
    pub(crate) fn new(bytes: usize) -> Self {
        Self(vec![AlignedBlock([0; 32]); bytes.div_ceil(32)])
    }
    pub(crate) fn bytes(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.0.as_ptr().cast(), self.0.len() * 32) }
    }
    pub(crate) fn bytes_mut(&mut self) -> &mut [u8] {
        unsafe { std::slice::from_raw_parts_mut(self.0.as_mut_ptr().cast(), self.0.len() * 32) }
    }
}

#[derive(Deserialize)]
struct ReferenceBundle {
    proof: GKRProof<PR, PR, Keccak256MerkleTreeWithCap>,
    commitment_mode: CommitmentMode,
}

pub(crate) fn assert_m6_fields_equal(actual: &M6ProofFields, expected: &M6ProofFields) {
    assert_eq!(actual.external_challenges, expected.external_challenges);
    assert_eq!(
        actual.lookup_challenges_pow_nonce,
        expected.lookup_challenges_pow_nonce
    );
    assert_eq!(
        actual.final_explicit_evaluations,
        expected.final_explicit_evaluations
    );
    assert_eq!(
        actual.grand_product_accumulator_computed,
        expected.grand_product_accumulator_computed
    );
    assert_eq!(
        actual.batched_proximity_check_pow_nonce,
        expected.batched_proximity_check_pow_nonce
    );
    assert_eq!(actual.merged_claims, expected.merged_claims);
    assert_eq!(actual.evaluation_point, expected.evaluation_point);
    assert_eq!(actual.batching_challenge, expected.batching_challenge);
    assert_eq!(
        actual.intermediate_transcript_seed,
        expected.intermediate_transcript_seed
    );
    assert_eq!(
        actual.sumcheck_intermediate_values.len(),
        expected.sumcheck_intermediate_values.len()
    );
    for (index, expected) in &expected.sumcheck_intermediate_values {
        let actual = &actual.sumcheck_intermediate_values[index];
        assert_eq!(
            actual.sumcheck_num_rounds, expected.sumcheck_num_rounds,
            "layer {index}"
        );
        assert_eq!(
            actual.internal_round_coefficients.len(),
            expected.internal_round_coefficients.len(),
            "layer {index}"
        );
        for (round, (actual, expected)) in actual
            .internal_round_coefficients
            .iter()
            .zip(&expected.internal_round_coefficients)
            .enumerate()
        {
            assert_eq!(
                actual.as_multilinear(),
                expected.as_multilinear(),
                "layer {index}, round {round}"
            );
        }
        assert_eq!(
            actual.final_step_evaluations, expected.final_step_evaluations,
            "layer {index}"
        );
        assert_eq!(
            actual.extra_evaluations_from_caching_relations,
            expected.extra_evaluations_from_caching_relations,
            "layer {index}"
        );
    }
}

#[test]
fn cpu_proof_layout_pr_roundtrip() {
    let programs = programs();
    let config = prover::gkr::prover_config::example_configs::evm_production_packed_prover_config(
        SecurityLevel::Sec100,
    );
    let layout = ProofLayoutPr::new(&programs, &config);
    let directory = std::env::var_os("AB_PROTH120_REFERENCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../../prover_pipeline/fixtures/l1_reference")
        });
    let path = directory.join("l1_bundle.json");
    let bundle: ReferenceBundle = serde_json::from_reader(std::io::BufReader::new(
        std::fs::File::open(&path)
            .unwrap_or_else(|error| panic!("Proth120 M0 bundle open {}: {error}", path.display())),
    ))
    .unwrap();
    let proof = bundle.proof;
    let prefix = crate::proth120::packed_challenges::boundary_prefix_words(&bundle.commitment_mode);
    let words: Vec<_> = prefix
        .iter()
        .copied()
        .chain(proof.inits_and_teardowns_top_bits.iter().copied())
        .chain(
            proof
                .whir_proof
                .setup_commitment
                .commitment
                .cap
                .cap
                .iter()
                .flatten()
                .copied(),
        )
        .chain(
            proof
                .whir_proof
                .memory_commitment
                .commitment
                .cap
                .cap
                .iter()
                .flatten()
                .copied(),
        )
        .collect();
    let mut seed = <Keccak256Transcript as Transcript<PR, PR>>::commit_initial_u32(&words);
    let bits = crate::proth120::packed_challenges::PackedChallengeConfig::new(
        &programs.runtime_circuit,
        &config,
        &bundle.commitment_mode,
        true,
    )
    .pow_bits;
    <Keccak256Transcript as Transcript<PR, PR>>::verify_pow(
        &mut seed,
        proof.lookup_challenges_pow_nonce,
        bits,
    );
    let challenges = prover::gkr::prover::transcript_utils::draw_random_field_els::<
        PR,
        PR,
        Keccak256Transcript,
    >(&mut seed, 9);
    assert_eq!(
        prover::definitions::GKRExternalChallenges::<PR, PR>::from_slice(&challenges[..7]),
        proof.external_challenges
    );
    let expected = M6ProofFields {
        external_challenges: proof.external_challenges,
        lookup_challenges_pow_nonce: proof.lookup_challenges_pow_nonce,
        final_explicit_evaluations: proof.final_explicit_evaluations,
        sumcheck_intermediate_values: proof.sumcheck_intermediate_values,
        grand_product_accumulator_computed: proof.grand_product_accumulator_computed,
        batched_proximity_check_pow_nonce: proof.batched_proximity_check_pow_nonce,
        merged_claims: (
            proof.whir_proof.memory_commitment.evals,
            proof.whir_proof.setup_commitment.evals,
        ),
        evaluation_point: proof
            .whir_proof
            .original_evaluation_point
            .expect("Proth120 M0 bundle point is missing"),
        batching_challenge: proof
            .whir_proof
            .batching_challenge
            .expect("Proth120 M0 bundle batching challenge is missing"),
        intermediate_transcript_seed: proof
            .intermediate_transcript_seed
            .expect("Proth120 M0 bundle seed is missing"),
    };
    assert_eq!(expected.merged_claims.0.len(), 7);
    assert_eq!(expected.merged_claims.1.len(), 1);
    assert_eq!(expected.evaluation_point.len(), 26);
    let mut slab = HostSlab::new(layout.bytes_len());
    layout.write_m6_fields(slab.bytes_mut(), &expected, [challenges[7], challenges[8]]);
    assert_eq!(
        layout.host_fields(slab.bytes(), &layout.external_challenges),
        challenges
    );
    assert_eq!(
        layout.host_fields(slab.bytes(), &layout.grand_product_accumulator_computed),
        [expected.grand_product_accumulator_computed]
    );
    assert_m6_fields_equal(&layout.parse_m6_fields(slab.bytes()), &expected);
    println!(
        "M6_TYPED_ROUNDTRIP layers={} fields={} raw_column_claims=114 merged_claims=8 point=26",
        expected.sumcheck_intermediate_values.len(),
        layout.bytes_len() / 16
    );
}

#[test]
fn cpu_proof_layout_pr_geometry() {
    let programs = programs();
    let config = prover::gkr::prover_config::example_configs::evm_production_packed_prover_config(
        SecurityLevel::Sec100,
    );
    let layout = ProofLayoutPr::new(&programs, &config);
    layout.validate_geometry(22, 5);
    let mut ranges = vec![
        layout.output_evaluations_range.clone(),
        layout.external_challenges.clone(),
        layout.lookup_challenges_pow_nonce.clone(),
        layout.grand_product_accumulator_computed.clone(),
        layout.memory_claims.start..layout.setup_claims.end,
        layout.evaluation_point.clone(),
        layout.batching_challenge.clone(),
        layout.batched_proximity_check_pow_nonce.clone(),
        layout.intermediate_transcript_seed.clone(),
    ];
    for layer in &layout.backward_layers {
        ranges.extend([
            layer.internal_round_coefficients.clone(),
            layer.final_step_evaluations.clone(),
            layer.extra_evaluations.clone(),
        ]);
        assert_eq!(
            layer.final_step_eval_degree,
            if layer.layer_idx < 5 { 1 } else { 2 }
        );
        assert_eq!(
            layer.sumcheck_num_rounds,
            if layer.layer_idx < 5 {
                22
            } else {
                26 - layer.layer_idx
            }
        );
    }
    ranges.sort_by_key(|range| range.start);
    assert!(ranges
        .iter()
        .all(|range| range.start % 32 == 0 && range.end <= layout.bytes_len()));
    for pair in ranges.windows(2) {
        assert!(pair[0].end <= pair[1].start);
    }
    assert_eq!(
        layout
            .backward_layers
            .iter()
            .map(|layer| layer.layer_idx)
            .collect::<BTreeSet<_>>(),
        (0..23).collect()
    );
    assert_eq!(layout.memory_claims.len(), 7 * 16);
    assert_eq!(layout.memory_claims.end, layout.setup_claims.start);
    assert_eq!(layout.setup_claims.len(), 16);
    assert_eq!(layout.evaluation_point.len(), 26 * 16);
    assert_eq!(layout.batching_challenge.len(), 16);
    assert_eq!(layout.external_challenges.len(), 9 * 16);
    assert_eq!(layout.intermediate_transcript_seed.end, layout.bytes_len());
    let slab = HostSlab::new(layout.bytes_len() + 32);
    let check = |bytes: &[u8], expected: &str| {
        let panic = std::panic::catch_unwind(|| layout.parse_m6_fields(bytes)).unwrap_err();
        let message = panic
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| panic.downcast_ref::<&str>().copied())
            .unwrap();
        assert!(message.contains(expected), "{message}");
    };
    check(
        &slab.bytes()[..layout.bytes_len() - 1],
        "Proth120 proof blob is undersized",
    );
    check(
        &slab.bytes()[1..layout.bytes_len() + 1],
        "Proth120 proof blob is misaligned",
    );
    assert_eq!(
        layout
            .backward_layers
            .last()
            .unwrap()
            .extra_evaluations_addresses
            .len(),
        15
    );
    println!(
        "M6_PROOF_GEOMETRY layers=23 point=26 merged=7+1 sections={} bytes={} whir_sections=0",
        ranges.len(),
        layout.bytes_len()
    );
}
