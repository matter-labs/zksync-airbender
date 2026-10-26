extern crate alloc;
use alloc::vec::Vec;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::{Field, FieldExtension, PrimeField};
use prover::gkr::prover::GKRProof;
use prover::gkr::whir::WhirIntermediateCommitmentAndQueries;
use prover::merkle_trees::ColumnMajorMerkleTreeConstructor;

fn flatten_field_els<F: PrimeField, E: FieldExtension<F>>(src: &[E], dst: &mut Vec<u32>) {
    for el in src {
        let coeffs = E::into_coeffs(*el);
        dst.extend(coeffs.as_ref().iter().map(|e| e.as_u32_raw_repr_reduced()));
    }
}

fn push_nonce(nonce: u64, dst: &mut Vec<u32>) {
    dst.push(nonce as u32);
    dst.push((nonce >> 32) as u32);
}

/// One sumcheck round in transcript order: every round polynomial, each
/// followed by its folding-challenge PoW nonce when the round's folding draws
/// are gated (`nonces` is then one per polynomial, empty otherwise).
fn flatten_sumcheck<F: PrimeField, E: FieldExtension<F>>(
    polys: &[[E; 3]],
    nonces: &[u64],
    dst: &mut Vec<u32>,
) {
    assert!(
        nonces.is_empty() || nonces.len() == polys.len(),
        "one folding PoW nonce per sumcheck polynomial, or none"
    );
    for (i, poly) in polys.iter().enumerate() {
        flatten_field_els::<F, E>(poly.as_slice(), dst);
        if let Some(nonce) = nonces.get(i) {
            push_nonce(*nonce, dst);
        }
    }
}

/// A just-committed intermediate oracle's transcript entries: its cap, then
/// its OOD sampling (the OOD PoW nonce when the draw is gated, then the
/// claimed evaluations).
fn flatten_commitment_and_ood<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    oracle: &WhirIntermediateCommitmentAndQueries<F, E, T>,
    dst: &mut Vec<u32>,
) {
    oracle.commitment.cap.add_into_buffer(dst);
    if let Some(nonce) = oracle.ood_pow_nonce {
        push_nonce(nonce, dst);
    }
    flatten_field_els::<F, E>(&oracle.ood_samples, dst);
}

fn flatten_intermediate_queries<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    oracle: &WhirIntermediateCommitmentAndQueries<F, E, T>,
    dst: &mut Vec<u32>,
) {
    for query in oracle.queries.iter() {
        flatten_field_els::<F, E>(&query.leaf_values_concatenated, dst);
        for sibling in query.path.iter() {
            dst.extend_from_slice(sibling);
        }
    }
}

pub fn flatten_gkr_proof_for_nds<F: PrimeField, E: FieldExtension<F> + Field, T>(
    proof: &GKRProof<F, E, T>,
    compiled_circuit: &GKRCircuitArtifact<F>,
) -> Vec<u32>
where
    T: ColumnMajorMerkleTreeConstructor<F>,
{
    let mut result = Vec::new();

    result.extend_from_slice(&proof.inits_and_teardowns_top_bits);
    if proof.whir_proof.setup_commitment.num_columns > 0 {
        proof
            .whir_proof
            .setup_commitment
            .commitment
            .cap
            .add_into_buffer(&mut result);
    }
    if proof.whir_proof.memory_commitment.num_columns > 0 {
        proof
            .whir_proof
            .memory_commitment
            .commitment
            .cap
            .add_into_buffer(&mut result);
    }
    if proof.whir_proof.witness_commitment.num_columns > 0 {
        proof
            .whir_proof
            .witness_commitment
            .commitment
            .cap
            .add_into_buffer(&mut result);
    }

    // Lookup-challenge PoW nonce: read by the verifier right after `commit_initial`, before
    // drawing the lookup challenges (and before reading the explicit evaluations below).
    push_nonce(proof.lookup_challenges_pow_nonce, &mut result);

    for pair in proof.final_explicit_evaluations.values() {
        flatten_field_els::<F, E>(&pair[0], &mut result);
        flatten_field_els::<F, E>(&pair[1], &mut result);
    }

    let num_standard_layers = compiled_circuit.layers.len();
    let initial_layer_for_sumcheck = *proof
        .sumcheck_intermediate_values
        .keys()
        .max()
        .expect("proof must have sumcheck values");

    let dim_reducing_indices: Vec<usize> = (num_standard_layers..=initial_layer_for_sumcheck)
        .rev()
        .collect();

    let standard_indices: Vec<usize> = (0..num_standard_layers).rev().collect();

    for &layer_idx in dim_reducing_indices.iter().chain(standard_indices.iter()) {
        let proof_values = proof
            .sumcheck_intermediate_values
            .get(&layer_idx)
            .expect("missing sumcheck values for layer");

        for coeffs in &proof_values.internal_round_coefficients {
            flatten_field_els::<F, E>(coeffs.as_multilinear(), &mut result);
        }

        for evals in proof_values.final_step_evaluations.values() {
            flatten_field_els::<F, E>(evals, &mut result);
        }

        for eval in proof_values
            .extra_evaluations_from_caching_relations
            .values()
        {
            flatten_field_els::<F, E>(&[*eval], &mut result);
        }
    }

    let whir = &proof.whir_proof;
    let whir_schedule = &whir.whir_schedule;

    // WHIR batching-challenge PoW nonce (the batched-proximity PoW, or the initial-folding
    // PoW under virtual packing): read by the verifier at the end of GKR, right before
    // drawing the batching challenge and entering WHIR.
    push_nonce(whir.batching_challenge_pow_nonce, &mut result);

    let oracles = &whir.intermediate_whir_oracles;
    assert_eq!(
        oracles.len(),
        whir_schedule.internal_rounds.len(),
        "one committed intermediate oracle per internal round"
    );
    assert!(!oracles.is_empty());

    // Round 0: the base sumcheck (none under virtual packing), intermediate
    // oracle 0 with its OOD sampling, the base query draw and the base-oracle
    // openings.
    flatten_sumcheck::<F, E>(
        &whir.base_sumcheck_polys,
        &whir.base_folding_pow_nonces,
        &mut result,
    );
    flatten_commitment_and_ood(&oracles[0], &mut result);
    push_nonce(whir.base_queries_pow_nonce, &mut result);
    {
        let values_per_leaf = whir_schedule.base_values_per_leaf();
        let base_oracles = [
            &whir.memory_commitment,
            &whir.witness_commitment,
            &whir.setup_commitment,
        ];
        let num_queries = base_oracles
            .iter()
            .map(|o| o.queries.len())
            .max()
            .unwrap_or(0);
        for q in 0..num_queries {
            for oracle in &base_oracles {
                if q < oracle.queries.len() {
                    let leaf = &oracle.queries[q].leaf_values_concatenated;
                    let num_cols = leaf.len() / values_per_leaf;
                    for col in 0..num_cols {
                        for pos in 0..values_per_leaf {
                            result.push(leaf[pos * num_cols + col].as_u32_raw_repr_reduced());
                        }
                    }
                    for sibling in &oracle.queries[q].path {
                        result.extend_from_slice(sibling);
                    }
                }
            }
        }
    }

    // Internal rounds: fold intermediate oracle `i`, commit (and OOD-sample)
    // oracle `i + 1`, query oracle `i`.
    for i in 0..oracles.len() - 1 {
        let oracle = &oracles[i];
        flatten_sumcheck::<F, E>(
            &oracle.sumcheck_polys,
            &oracle.folding_pow_nonces,
            &mut result,
        );
        flatten_commitment_and_ood(&oracles[i + 1], &mut result);
        push_nonce(oracle.queries_pow_nonce, &mut result);
        flatten_intermediate_queries(oracle, &mut result);
    }

    // Final round: fold the last oracle, ship the plain-text tail, query the
    // last oracle.
    let last = oracles.last().unwrap();
    flatten_sumcheck::<F, E>(&last.sumcheck_polys, &last.folding_pow_nonces, &mut result);
    flatten_field_els::<F, E>(&whir.final_monomials, &mut result);
    push_nonce(last.queries_pow_nonce, &mut result);
    flatten_intermediate_queries(last, &mut result);

    result
}
