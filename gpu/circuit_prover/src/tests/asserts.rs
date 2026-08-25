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
        for (coeff_idx, (&actual_coeff, &expected_coeff)) in actual_coeffs
            .as_multilinear()
            .iter()
            .zip(expected_coeffs.as_multilinear().iter())
            .enumerate()
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
    assert_eq!(
        actual.extra_evaluations_from_caching_relations,
        expected.extra_evaluations_from_caching_relations,
        "layer {layer_idx}: cached-relation evaluations mismatch"
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
    // Committed-state values and lengths first: a length mismatch would make the
    // per-round ladder below misalign.
    assert_eq!(
        actual.batching_challenge, expected.batching_challenge,
        "WHIR batching challenge diverged"
    );
    assert_eq!(
        actual.original_evaluation_point, expected.original_evaluation_point,
        "WHIR original evaluation point diverged"
    );
    assert_eq!(
        actual.batched_opening, expected.batched_opening,
        "WHIR batched opening diverged"
    );
    assert_eq!(
        actual.whir_schedule, expected.whir_schedule,
        "WHIR schedule diverged"
    );
    assert_eq!(
        actual.sumcheck_polys.len(),
        expected.sumcheck_polys.len(),
        "WHIR sumcheck round count diverged",
    );
    assert_eq!(
        actual.intermediate_whir_oracles.len(),
        expected.intermediate_whir_oracles.len(),
        "WHIR intermediate oracle count diverged",
    );
    assert_eq!(
        actual.ood_samples.len(),
        expected.ood_samples.len(),
        "WHIR OOD sample count diverged",
    );
    assert_eq!(
        actual.pow_nonces.len(),
        expected.pow_nonces.len(),
        "WHIR PoW nonce count diverged",
    );
    assert_eq!(
        actual.final_monomials.len(),
        expected.final_monomials.len(),
        "WHIR final monomial count diverged",
    );

    // Base-layer commitments: their caps are absorbed before the first fold
    // round, and their evals are the batched-opening inputs.
    for (name, actual_commitment, expected_commitment) in [
        (
            "setup",
            &actual.setup_commitment,
            &expected.setup_commitment,
        ),
        (
            "memory",
            &actual.memory_commitment,
            &expected.memory_commitment,
        ),
        (
            "witness",
            &actual.witness_commitment,
            &expected.witness_commitment,
        ),
    ] {
        assert_eq!(
            actual_commitment.commitment.cap, expected_commitment.commitment.cap,
            "WHIR {name} base cap diverged",
        );
        assert_eq!(
            actual_commitment.num_columns, expected_commitment.num_columns,
            "WHIR {name} base column count diverged",
        );
        assert_eq!(
            actual_commitment.evals, expected_commitment.evals,
            "WHIR {name} base evals diverged",
        );
    }

    // Transcript order, so the first failing assert names the cause rather than
    // a downstream symptom.
    let mut round_idx = 0usize;
    let group_count = expected.whir_schedule.whir_steps_schedule.len();
    for (group_idx, &steps) in expected
        .whir_schedule
        .whir_steps_schedule
        .iter()
        .enumerate()
    {
        for _ in 0..steps {
            assert_eq!(
                actual.sumcheck_polys[round_idx], expected.sumcheck_polys[round_idx],
                "WHIR sumcheck polynomial diverged at round {round_idx}",
            );
            round_idx += 1;
        }
        if group_idx + 1 < group_count {
            assert_eq!(
                actual.intermediate_whir_oracles[group_idx].commitment.cap,
                expected.intermediate_whir_oracles[group_idx].commitment.cap,
                "WHIR intermediate oracle cap diverged at oracle {group_idx}",
            );
            assert_eq!(
                actual.ood_samples[group_idx], expected.ood_samples[group_idx],
                "WHIR OOD sample diverged at oracle {group_idx}",
            );
        } else {
            assert_eq!(
                actual.final_monomials, expected.final_monomials,
                "WHIR final monomials diverged",
            );
        }
        assert_eq!(
            actual.pow_nonces[group_idx], expected.pow_nonces[group_idx],
            "WHIR PoW nonce diverged at round {group_idx}",
        );
    }
    assert_eq!(
        round_idx,
        expected.sumcheck_polys.len(),
        "WHIR schedule does not account for every sumcheck round",
    );

    // Queries are answered from already-committed oracles, so they sit after
    // the transcript ladder above.
    for (name, actual_commitment, expected_commitment) in [
        (
            "setup",
            &actual.setup_commitment,
            &expected.setup_commitment,
        ),
        (
            "memory",
            &actual.memory_commitment,
            &expected.memory_commitment,
        ),
        (
            "witness",
            &actual.witness_commitment,
            &expected.witness_commitment,
        ),
    ] {
        assert_eq!(
            actual_commitment.queries.len(),
            expected_commitment.queries.len(),
            "WHIR {name} base query count diverged",
        );
        for actual_query in actual_commitment
            .queries
            .iter()
            .zip(expected_commitment.queries.iter())
        {
            assert_base_field_query_eq_for_test(actual_query.0, actual_query.1);
        }
    }
    for (oracle_idx, (actual_oracle, expected_oracle)) in actual
        .intermediate_whir_oracles
        .iter()
        .zip(expected.intermediate_whir_oracles.iter())
        .enumerate()
    {
        assert_eq!(
            actual_oracle.queries.len(),
            expected_oracle.queries.len(),
            "WHIR intermediate query count diverged at oracle {oracle_idx}",
        );
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
        actual.inits_and_teardowns_top_bits, expected.inits_and_teardowns_top_bits,
        "inits-and-teardowns top bits diverged",
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
    assert_serialized_proof_bytes_eq(expected, actual);
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

pub(super) fn canonical_serialized_bytes_for_test<T: serde::Serialize>(value: &T) -> Vec<u8> {
    let mut bytes = Vec::new();
    serde_json::to_writer_pretty(&mut bytes, value).unwrap();
    bytes
}

pub(super) fn assert_serialized_bytes_eq_for_test<T: serde::Serialize>(
    cpu: &T,
    gpu: &T,
    label: &str,
) {
    let cpu_bytes = canonical_serialized_bytes_for_test(cpu);
    let gpu_bytes = canonical_serialized_bytes_for_test(gpu);
    if cpu_bytes == gpu_bytes {
        return;
    }
    let first_diff = cpu_bytes
        .iter()
        .zip(gpu_bytes.iter())
        .position(|(cpu_byte, gpu_byte)| cpu_byte != gpu_byte)
        .unwrap_or_else(|| cpu_bytes.len().min(gpu_bytes.len()));
    let window = |bytes: &[u8]| {
        let start = first_diff.saturating_sub(32);
        let end = (first_diff + 32).min(bytes.len());
        String::from_utf8_lossy(&bytes[start..end]).into_owned()
    };
    panic!(
        "{label}: serialized bytes diverged at offset {first_diff} \
         (cpu {} bytes, gpu {} bytes)\n  cpu: {}\n  gpu: {}",
        cpu_bytes.len(),
        gpu_bytes.len(),
        window(&cpu_bytes),
        window(&gpu_bytes),
    );
}

// Catches anything the field-by-field asserts above do not walk.
pub(super) fn assert_serialized_proof_bytes_eq(
    cpu: &GKRProof<BF, E4, DefaultTreeConstructor>,
    gpu: &GKRProof<BF, E4, DefaultTreeConstructor>,
) {
    assert_serialized_bytes_eq_for_test(cpu, gpu, "GKR proof");
}
