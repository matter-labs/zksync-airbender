extern crate alloc;
use alloc::vec::Vec;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::{Field, FieldExtension, PrimeField};
use prover::gkr::prover::{GKRProof, WhirSchedule};
use prover::merkle_trees::ColumnMajorMerkleTreeConstructor;

fn flatten_field_els<F: PrimeField, E: FieldExtension<F>>(src: &[E], dst: &mut Vec<u32>)
where
    [(); E::DEGREE]: Sized,
{
    use field::FixedArrayConvertible;
    for el in src {
        let coeffs = E::into_coeffs(*el)
            .into_array::<{ E::DEGREE }>()
            .map(|e: F| e.as_u32_raw_repr_reduced());
        dst.extend(coeffs);
    }
}

pub fn flatten_gkr_proof_for_nds<F: PrimeField, E: FieldExtension<F> + Field, T>(
    proof: &GKRProof<F, E, T>,
    compiled_circuit: &GKRCircuitArtifact<F>,
    whir_schedule: &WhirSchedule,
    inits_and_teardowns_top_bits: &[u32],
) -> Vec<u32>
where
    T: ColumnMajorMerkleTreeConstructor<F>,
    [(); E::DEGREE]: Sized,
{
    let mut result = Vec::new();

    result.extend_from_slice(inits_and_teardowns_top_bits);
    proof.external_challenges.flatten_into_buffer(&mut result);
    if compiled_circuit.generic_lookup_tables_width > 0 {
        proof
            .whir_proof
            .setup_commitment
            .commitment
            .cap
            .add_into_buffer(&mut result);
    }
    if compiled_circuit.memory_layout.total_width > 0 {
        proof
            .whir_proof
            .memory_commitment
            .commitment
            .cap
            .add_into_buffer(&mut result);
    }
    if compiled_circuit.witness_layout.total_width > 0 {
        proof
            .whir_proof
            .witness_commitment
            .commitment
            .cap
            .add_into_buffer(&mut result);
    }

    for (_output_type, pair) in &proof.final_explicit_evaluations {
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
            flatten_field_els::<F, E>(coeffs, &mut result);
        }

        for (_addr, evals) in &proof_values.final_step_evaluations {
            flatten_field_els::<F, E>(evals, &mut result);
        }

        for (_addr, eval) in &proof_values.extra_evaluations_from_caching_relations {
            flatten_field_els::<F, E>(&[*eval], &mut result);
        }
    }

    let whir = &proof.whir_proof;

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
                        for sibling in &oracle.queries[q].path {
                            result.extend_from_slice(sibling);
                        }
                    }
                }
            }
        } else {
            let oracle = &whir.intermediate_whir_oracles[round - 1];
            for query in oracle.queries.iter() {
                flatten_field_els::<F, E>(&query.leaf_values_concatenated, &mut result);
                for sibling in query.path.iter() {
                    result.extend_from_slice(sibling);
                }
            }
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
            for sibling in query.path.iter() {
                result.extend_from_slice(sibling);
            }
        }
    }

    result
}
