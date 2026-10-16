extern crate alloc;
use alloc::vec::Vec;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::{Field, FieldExtension, PrimeField};
use prover::gkr::prover::GKRProof;
use prover::merkle_trees::ColumnMajorMerkleTreeConstructor;

/// Append direct prover output, with a compatibility adapter for historical JSON fixtures.
/// New proofs contain no per-query paths and require no compaction here.
pub fn append_merkle_multiproof<'a>(
    queries: impl Iterator<Item = (usize, &'a [[u32; 8]])>,
    multiproof: Option<&prover::merkle_trees::multiproof::MerkleMultiProof>,
    dst: &mut Vec<u32>,
) {
    use prover::merkle_trees::multiproof::boundary_nodes;
    let queries: Vec<_> = queries.collect();
    let indices: Vec<_> = queries.iter().map(|q| q.0).collect();
    if let Some(proof) = multiproof {
        assert!(
            queries.iter().all(|q| q.1.is_empty()),
            "mixed compact and legacy paths"
        );
        assert_eq!(
            boundary_nodes(&indices, proof.depth).len(),
            proof.siblings.len()
        );
        for sibling in &proof.siblings {
            dst.extend_from_slice(sibling);
        }
    } else if let Some(first) = queries.first() {
        let depth = first.1.len();
        assert!(queries.iter().all(|q| q.1.len() == depth));
        for (level, index) in boundary_nodes(&indices, depth) {
            let query = queries
                .iter()
                .find(|q| ((q.0 >> level) ^ 1) == index)
                .expect("boundary node must occur in a legacy query path");
            dst.extend_from_slice(&query.1[level]);
        }
    }
}

fn flatten_field_els<F: PrimeField, E: FieldExtension<F>>(src: &[E], dst: &mut Vec<u32>) {
    for el in src {
        let coeffs = E::into_coeffs(*el);
        dst.extend(coeffs.as_ref().iter().map(|e| e.as_u32_raw_repr_reduced()));
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
    let lookup_nonce = proof.lookup_challenges_pow_nonce;
    result.push(lookup_nonce as u32);
    result.push((lookup_nonce >> 32) as u32);

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

    // Batched-proximity (WHIR batching) PoW nonce: read by the verifier at the end of GKR, right
    // before drawing the WHIR batching challenge and entering WHIR.
    let batching_nonce = proof.batched_proximity_check_pow_nonce;
    result.push(batching_nonce as u32);
    result.push((batching_nonce >> 32) as u32);

    let whir = &proof.whir_proof;
    let whir_schedule = &whir.whir_schedule;

    let num_rounds = whir
        .ood_samples
        .len()
        .min(whir_schedule.whir_steps_schedule.len());
    let mut sumcheck_poly_cursor = 0;

    for round in 0..num_rounds {
        let fold_steps = whir_schedule.whir_steps_schedule[round];

        for i in 0..fold_steps {
            flatten_field_els::<F, E>(
                whir.sumcheck_polys[sumcheck_poly_cursor + i].as_slice(),
                &mut result,
            );
        }
        sumcheck_poly_cursor += fold_steps;

        if round < whir.intermediate_whir_oracles.len() {
            whir.intermediate_whir_oracles[round]
                .commitment
                .cap
                .add_into_buffer(&mut result);
        }

        flatten_field_els::<F, E>(&[whir.ood_samples[round]], &mut result);

        let nonce = whir.pow_nonces[round];
        result.push(nonce as u32);
        result.push((nonce >> 32) as u32);

        if round == 0 {
            let values_per_leaf = 1usize << whir_schedule.whir_steps_schedule[0];
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
                    }
                }
            }
            for oracle in &base_oracles {
                append_merkle_multiproof(
                    oracle.queries.iter().map(|q| (q.index, q.path.as_slice())),
                    oracle.multiproof.as_ref(),
                    &mut result,
                );
            }
        } else {
            let oracle = &whir.intermediate_whir_oracles[round - 1];
            for query in oracle.queries.iter() {
                flatten_field_els::<F, E>(&query.leaf_values_concatenated, &mut result);
            }
            append_merkle_multiproof(
                oracle.queries.iter().map(|q| (q.index, q.path.as_slice())),
                oracle.multiproof.as_ref(),
                &mut result,
            );
        }
    }

    let final_round_idx = whir_schedule.whir_steps_schedule.len() - 1;
    if num_rounds < whir_schedule.whir_steps_schedule.len() {
        let fold_steps = whir_schedule.whir_steps_schedule[final_round_idx];

        for i in 0..fold_steps {
            flatten_field_els::<F, E>(
                whir.sumcheck_polys[sumcheck_poly_cursor + i].as_slice(),
                &mut result,
            );
        }

        flatten_field_els::<F, E>(&whir.final_monomials, &mut result);

        let nonce = whir.pow_nonces[final_round_idx];
        result.push(nonce as u32);
        result.push((nonce >> 32) as u32);

        let last_oracle = whir.intermediate_whir_oracles.last().unwrap();
        for query in last_oracle.queries.iter() {
            flatten_field_els::<F, E>(&query.leaf_values_concatenated, &mut result);
        }
        append_merkle_multiproof(
            last_oracle
                .queries
                .iter()
                .map(|q| (q.index, q.path.as_slice())),
            last_oracle.multiproof.as_ref(),
            &mut result,
        );
    }

    result
}
