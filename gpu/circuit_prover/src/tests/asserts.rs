use super::*;

pub(super) fn assert_sumcheck_intermediate_values_eq_for_test_with_layer<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    actual: &prover::gkr::prover::SumcheckIntermediateProofValues<F, E>,
    expected: &prover::gkr::prover::SumcheckIntermediateProofValues<F, E>,
    layer_idx: usize,
) {
    assert_eq!(
        actual.sumcheck_num_rounds, expected.sumcheck_num_rounds,
        "layer {layer_idx}: sumcheck_num_rounds mismatch"
    );
    assert_eq!(
        actual.internal_round_coefficients.len(),
        expected.internal_round_coefficients.len(),
        "layer {layer_idx}: internal_round_coefficients length mismatch"
    );
    for (round_idx, (actual_coeffs, expected_coeffs)) in actual
        .internal_round_coefficients
        .iter()
        .zip(expected.internal_round_coefficients.iter())
        .enumerate()
    {
        for (coeff_idx, (&actual_coeff, &expected_coeff)) in
            actual_coeffs.iter().zip(expected_coeffs.iter()).enumerate()
        {
            assert_eq!(
                actual_coeff, expected_coeff,
                "layer {layer_idx}: internal_round_coefficients mismatch at round {round_idx}, coeff {coeff_idx}"
            );
        }
    }
    assert_eq!(
        actual.final_step_evaluations, expected.final_step_evaluations,
        "layer {layer_idx}: final_step_evaluations mismatch"
    );
}

pub(super) fn assert_base_field_query_eq_for_test(
    actual: &prover::gkr::whir::BaseFieldQuery<BF, DefaultTreeConstructor>,
    expected: &prover::gkr::whir::BaseFieldQuery<BF, DefaultTreeConstructor>,
) {
    assert_eq!(actual.index, expected.index);
    assert_eq!(
        actual.leaf_values_concatenated,
        expected.leaf_values_concatenated
    );
    assert_eq!(actual.path, expected.path);
}

pub(super) fn assert_extension_field_query_eq_for_test(
    actual: &prover::gkr::whir::ExtensionFieldQuery<BF, E4, DefaultTreeConstructor>,
    expected: &prover::gkr::whir::ExtensionFieldQuery<BF, E4, DefaultTreeConstructor>,
) {
    assert_eq!(actual.index, expected.index);
    assert_eq!(
        actual.leaf_values_concatenated,
        expected.leaf_values_concatenated
    );
    assert_eq!(actual.path, expected.path);
}

pub(super) fn assert_whir_proof_eq_for_test(
    actual: &prover::gkr::whir::WhirPolyCommitProof<BF, E4, DefaultTreeConstructor>,
    expected: &prover::gkr::whir::WhirPolyCommitProof<BF, E4, DefaultTreeConstructor>,
) {
    assert_eq!(
        actual.sumcheck_polys.len(),
        expected.sumcheck_polys.len(),
        "WHIR sumcheck round count diverged",
    );
    for (round_idx, (actual_poly, expected_poly)) in actual
        .sumcheck_polys
        .iter()
        .zip(expected.sumcheck_polys.iter())
        .enumerate()
    {
        assert_eq!(
            actual_poly.len(),
            expected_poly.len(),
            "WHIR sumcheck polynomial degree diverged at round {round_idx}",
        );
        for (coeff_idx, (&actual_coeff, &expected_coeff)) in
            actual_poly.iter().zip(expected_poly.iter()).enumerate()
        {
            assert_eq!(
                actual_coeff, expected_coeff,
                "WHIR sumcheck coefficient diverged at round {round_idx}, coeff {coeff_idx}",
            );
        }
    }
    assert_eq!(
        actual.ood_samples, expected.ood_samples,
        "WHIR OOD samples diverged"
    );
    assert_eq!(
        actual.pow_nonces, expected.pow_nonces,
        "WHIR PoW nonces diverged"
    );
    assert_eq!(
        actual.final_monomials, expected.final_monomials,
        "WHIR final monomials diverged",
    );
    assert_eq!(
        actual.batching_challenge, expected.batching_challenge,
        "WHIR batching challenge diverged",
    );
    assert_eq!(
        actual.original_evaluation_point, expected.original_evaluation_point,
        "WHIR original evaluation point diverged",
    );
    assert_eq!(
        actual.batched_opening, expected.batched_opening,
        "WHIR batched opening diverged",
    );

    for (actual_commitment, expected_commitment) in [
        (&actual.memory_commitment, &expected.memory_commitment),
        (&actual.witness_commitment, &expected.witness_commitment),
        (&actual.setup_commitment, &expected.setup_commitment),
    ] {
        assert_eq!(
            actual_commitment.commitment.cap,
            expected_commitment.commitment.cap
        );
        assert_eq!(
            actual_commitment.num_columns,
            expected_commitment.num_columns
        );
        assert_eq!(actual_commitment.evals, expected_commitment.evals);
        assert_eq!(
            actual_commitment.queries.len(),
            expected_commitment.queries.len()
        );
        for (actual_query, expected_query) in actual_commitment
            .queries
            .iter()
            .zip(expected_commitment.queries.iter())
        {
            assert_base_field_query_eq_for_test(actual_query, expected_query);
        }
    }

    assert_eq!(
        actual.intermediate_whir_oracles.len(),
        expected.intermediate_whir_oracles.len()
    );
    for (actual_oracle, expected_oracle) in actual
        .intermediate_whir_oracles
        .iter()
        .zip(expected.intermediate_whir_oracles.iter())
    {
        assert_eq!(actual_oracle.commitment.cap, expected_oracle.commitment.cap);
        assert_eq!(actual_oracle.queries.len(), expected_oracle.queries.len());
        for (actual_query, expected_query) in actual_oracle
            .queries
            .iter()
            .zip(expected_oracle.queries.iter())
        {
            assert_extension_field_query_eq_for_test(actual_query, expected_query);
        }
    }
}

pub(super) fn assert_gkr_proof_eq_for_test(
    actual: &GKRProof<BF, E4, DefaultTreeConstructor>,
    expected: &GKRProof<BF, E4, DefaultTreeConstructor>,
) {
    assert_eq!(actual.external_challenges, expected.external_challenges);
    assert_eq!(
        actual.final_explicit_evaluations,
        expected.final_explicit_evaluations
    );
    assert_eq!(
        actual.grand_product_accumulator_computed,
        expected.grand_product_accumulator_computed
    );
    assert_eq!(
        actual.sumcheck_intermediate_values.len(),
        expected.sumcheck_intermediate_values.len()
    );
    for (layer_idx, expected_values) in expected.sumcheck_intermediate_values.iter() {
        let actual_values = actual
            .sumcheck_intermediate_values
            .get(layer_idx)
            .unwrap_or_else(|| panic!("missing proof layer {layer_idx}"));
        assert_sumcheck_intermediate_values_eq_for_test_with_layer(
            actual_values,
            expected_values,
            *layer_idx,
        );
    }
    assert_whir_proof_eq_for_test(&actual.whir_proof, &expected.whir_proof);
    assert_eq!(
        actual.intermediate_transcript_seed, expected.intermediate_transcript_seed,
        "intermediate transcript seed diverged",
    );
    assert_eq!(
        actual.lookup_challenges_pow_nonce, expected.lookup_challenges_pow_nonce,
        "lookup-challenges PoW nonce diverged",
    );
    assert_eq!(
        actual.batched_proximity_check_pow_nonce, expected.batched_proximity_check_pow_nonce,
        "batched-proximity-check PoW nonce diverged",
    );
}

pub(super) fn assert_gkr_proof_structure_for_test(
    proof: &GKRProof<BF, E4, DefaultTreeConstructor>,
    whir_schedule: &WhirSchedule,
) {
    assert!(
        !proof.sumcheck_intermediate_values.is_empty(),
        "proof must contain sumcheck intermediate values",
    );
    // `PermutationProduct` (the memory argument) is the only output type every
    // circuit carries. The 16-bit / timestamp / generic lookups are present for
    // the executor families but NOT for the memory-only inits-and-teardowns
    // circuit, whose layout emits `PermutationProduct` alone. So the structural
    // invariant is: PermutationProduct present, and every present key is a known
    // output type — not that all four are present.
    assert!(
        proof
            .final_explicit_evaluations
            .contains_key(&OutputType::PermutationProduct),
        "proof must contain explicit evaluations for PermutationProduct",
    );
    for key in proof.final_explicit_evaluations.keys() {
        assert!(
            matches!(
                key,
                OutputType::PermutationProduct
                    | OutputType::Lookup16Bits
                    | OutputType::LookupTimestamps
                    | OutputType::GenericLookup
                    | OutputType::InitsAndTeardownsProduct
            ),
            "proof contains unexpected explicit-evaluation output type {key:?}",
        );
    }
    assert_eq!(
        proof.whir_proof.pow_nonces.len(),
        whir_schedule.whir_pow_schedule.len(),
        "proof must contain one PoW nonce per WHIR round",
    );
}

pub(super) fn stage1_subcaps_from_cap(
    cap: &MerkleTreeCapVarLength,
    subcap_size: usize,
) -> Vec<MerkleTreeCapVarLength> {
    cap.cap
        .chunks_exact(subcap_size)
        .map(|chunk| MerkleTreeCapVarLength {
            cap: chunk.to_vec(),
        })
        .collect_vec()
}
