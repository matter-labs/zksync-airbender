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
    for el in src.iter() {
        let coeffs = E::into_coeffs(*el)
            .into_array::<{ E::DEGREE }>()
            .map(|e: F| e.as_u32_raw_repr_reduced());
        dst.extend(coeffs);
    }
}

/// Flatten a GKR proof into NDS reading order.
///
/// The output stream contains (in order):
/// 1. Initial transcript preamble (reconstructed from proof fields):
///    - `inits_and_teardowns_top_bits` (if present)
///    - external challenges
///    - setup, memory, witness Merkle caps
/// 2. `final_explicit_evaluations` (in BTreeMap order by OutputType, poly0 then poly1)
/// 3. Per-layer sumcheck data (dim-reducing first top-to-bottom, then standard top-to-bottom):
///    - For each regular round: 4 field elements `[E; 4]`
///    - For each final step: evaluations per address (2 for standard, 4 for dim-reducing)
/// 4. `grand_product_accumulator_computed` (1 field element)
pub fn flatten_gkr_proof_for_nds<F: PrimeField, E: FieldExtension<F> + Field, T>(
    proof: &GKRProof<F, E, T>,
    compiled_circuit: &GKRCircuitArtifact<F>,
    whir_schedule: &WhirSchedule,
) -> Vec<u32>
where
    T: ColumnMajorMerkleTreeConstructor<F>,
    [(); E::DEGREE]: Sized,
{
    let mut result = Vec::new();

    if let Some(top_bits) = proof.inits_and_teardowns_top_bits {
        result.push(top_bits);
    }
    proof.external_challenges.flatten_into_buffer(&mut result);
    proof
        .whir_proof
        .setup_commitment
        .commitment
        .cap
        .add_into_buffer(&mut result);
    proof
        .whir_proof
        .memory_commitment
        .commitment
        .cap
        .add_into_buffer(&mut result);
    proof
        .whir_proof
        .witness_commitment
        .commitment
        .cap
        .add_into_buffer(&mut result);

    for (_output_type, pair) in proof.final_explicit_evaluations.iter() {
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

        for coeffs in proof_values.internal_round_coefficients.iter() {
            flatten_field_els::<F, E>(coeffs, &mut result);
        }

        for (_addr, evals) in proof_values.final_step_evaluations.iter() {
            flatten_field_els::<F, E>(evals, &mut result);
        }

        for (_addr, eval) in proof_values.extra_evaluations_from_caching_relations.iter() {
            flatten_field_els::<F, E>(&[*eval], &mut result);
        }
    }

    flatten_field_els::<F, E>(&[proof.grand_product_accumulator_computed], &mut result);

    // --- WHIR oracle evals (read by verifier before sumcheck) ---
    let whir = &proof.whir_proof;
    flatten_field_els::<F, E>(&whir.memory_commitment.evals, &mut result);
    flatten_field_els::<F, E>(&whir.witness_commitment.evals, &mut result);
    flatten_field_els::<F, E>(&whir.setup_commitment.evals, &mut result);

    // --- WHIR proof data, interleaved per-round to match verifier reading order ---
    // Only flatten rounds for which the proof has data
    let num_rounds = whir
        .ood_samples
        .len()
        .min(whir_schedule.whir_steps_schedule.len());
    let mut sumcheck_poly_cursor = 0;

    for round in 0..num_rounds {
        let fold_steps = whir_schedule.whir_steps_schedule[round];

        // 1. Sumcheck poly coefficients for this round (fold_steps polys, each [E; 3])
        for i in 0..fold_steps {
            flatten_field_els::<F, E>(
                whir.sumcheck_polys[sumcheck_poly_cursor + i].as_slice(),
                &mut result,
            );
        }
        sumcheck_poly_cursor += fold_steps;

        // 2. Intermediate oracle cap (written when the oracle exists)
        if round < whir.intermediate_whir_oracles.len() {
            whir.intermediate_whir_oracles[round]
                .commitment
                .cap
                .add_into_buffer(&mut result);
        }

        // 3. OOD sample
        flatten_field_els::<F, E>(&[whir.ood_samples[round]], &mut result);

        // 4. PoW nonce
        let nonce = whir.pow_nonces[round];
        result.push(nonce as u32);
        result.push((nonce >> 32) as u32);

        // 5. Query data for this round
        if round == 0 {
            // Initial round: base oracle queries (memory, witness, setup)
            let num_queries = whir.memory_commitment.queries.len();
            for q in 0..num_queries {
                // Memory leaf values + Merkle path
                for &val in whir.memory_commitment.queries[q]
                    .leaf_values_concatenated
                    .iter()
                {
                    result.push(val.as_u32_raw_repr_reduced());
                }
                for sibling in whir.memory_commitment.queries[q].path.iter() {
                    result.extend_from_slice(sibling);
                }
                // Witness leaf values + Merkle path
                for &val in whir.witness_commitment.queries[q]
                    .leaf_values_concatenated
                    .iter()
                {
                    result.push(val.as_u32_raw_repr_reduced());
                }
                for sibling in whir.witness_commitment.queries[q].path.iter() {
                    result.extend_from_slice(sibling);
                }
                // Setup leaf values + Merkle path
                for &val in whir.setup_commitment.queries[q]
                    .leaf_values_concatenated
                    .iter()
                {
                    result.push(val.as_u32_raw_repr_reduced());
                }
                for sibling in whir.setup_commitment.queries[q].path.iter() {
                    result.extend_from_slice(sibling);
                }
            }
        } else {
            // Intermediate rounds: query the previous round's oracle
            let oracle = &whir.intermediate_whir_oracles[round - 1];
            for query in oracle.queries.iter() {
                flatten_field_els::<F, E>(&query.leaf_values_concatenated, &mut result);
                for sibling in query.path.iter() {
                    result.extend_from_slice(sibling);
                }
            }
        }
    }

    // --- Final WHIR round (no OOD sample, no new oracle cap, no delinearization) ---
    let final_round_idx = whir_schedule.whir_steps_schedule.len() - 1;
    if num_rounds < whir_schedule.whir_steps_schedule.len() {
        let fold_steps = whir_schedule.whir_steps_schedule[final_round_idx];

        // 1. Sumcheck poly coefficients
        for i in 0..fold_steps {
            flatten_field_els::<F, E>(
                whir.sumcheck_polys[sumcheck_poly_cursor + i].as_slice(),
                &mut result,
            );
        }

        // 2. PoW nonce
        let nonce = whir.pow_nonces[final_round_idx];
        result.push(nonce as u32);
        result.push((nonce >> 32) as u32);

        // 3. Query data from the last intermediate oracle
        let last_oracle = whir.intermediate_whir_oracles.last().unwrap();
        for query in last_oracle.queries.iter() {
            flatten_field_els::<F, E>(&query.leaf_values_concatenated, &mut result);
            for sibling in query.path.iter() {
                result.extend_from_slice(sibling);
            }
        }
    }

    // Final monomials
    flatten_field_els::<F, E>(&whir.final_monomials, &mut result);

    result
}
