use alloc::vec::Vec;
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use core::alloc::Allocator;
use cs::definitions::ShuffleRamInitAndTeardownLayout;
use prover::field::*;
use prover::merkle_trees::MerkleTreeCapVarLength;
use prover::prover_stages::{Proof, QuerySet};

fn flatten_merkle_caps_into<A: Allocator>(trees: &[MerkleTreeCapVarLength], dst: &mut Vec<u32, A>) {
    for subtree in trees.iter() {
        for cap_element in subtree.cap.iter() {
            dst.extend_from_slice(cap_element);
        }
    }
}

fn flatten_leaf_into<A: Allocator>(leaf: &[Mersenne31Field], dst: &mut Vec<u32, A>) {
    for el in leaf.iter() {
        dst.push(el.to_reduced_u32());
    }
}

fn flatten_merkle_path_into<A: Allocator>(
    leaf: &[[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]],
    dst: &mut Vec<u32, A>,
) {
    for el in leaf.iter() {
        dst.extend_from_slice(el);
    }
}

pub fn flatten_proof_for_skeleton(
    proof: &Proof,
    lazy_inits_and_teardowns: &[ShuffleRamInitAndTeardownLayout],
) -> Vec<u32> {
    let mut result = Vec::new();

    // sequence idx
    result.push(proof.circuit_sequence as u32);
    // delegation type
    result.push(proof.delegation_type as u32);
    // and public input
    result.extend(proof.public_inputs.iter().map(|el| el.to_reduced_u32()));

    // setup merkle cap
    flatten_merkle_caps_into(&proof.setup_tree_caps, &mut result);
    // memory argument challenges
    result.extend(proof.external_values.challenges.memory_argument.flatten());
    // delegation argument challenges
    if let Some(delegation_argument) = proof.external_values.challenges.delegation_argument {
        result.extend(delegation_argument.flatten());
    }
    if lazy_inits_and_teardowns.len() > 0 {
        assert_eq!(lazy_inits_and_teardowns.len(), 1);
        result.extend(proof.external_values.aux_boundary_values.flatten());
    }
    // witness and memory trees
    flatten_merkle_caps_into(&proof.witness_tree_caps, &mut result);
    flatten_merkle_caps_into(&proof.memory_tree_caps, &mut result);
    // stage 2 root
    flatten_merkle_caps_into(&proof.stage_2_tree_caps, &mut result);
    // grand product and delegation accumulators
    result.extend(
        proof
            .memory_grand_product_accumulator
            .into_coeffs_in_base()
            .map(|el: Mersenne31Field| el.to_reduced_u32()),
    );
    if let Some(delegation_argument_accumulator) = proof.delegation_argument_accumulator {
        result.extend(
            delegation_argument_accumulator
                .into_coeffs_in_base()
                .map(|el: Mersenne31Field| el.to_reduced_u32()),
        );
    }
    // quotient root
    flatten_merkle_caps_into(&proof.quotient_tree_caps, &mut result);
    result.extend(
        proof
            .evaluations_at_random_points
            .iter()
            .map(|el| {
                el.into_coeffs_in_base()
                    .map(|el: Mersenne31Field| el.to_reduced_u32())
            })
            .flatten(),
    );
    flatten_merkle_caps_into(&proof.deep_poly_caps, &mut result);
    for el in proof.intermediate_fri_oracle_caps.iter() {
        flatten_merkle_caps_into(el, &mut result);
    }
    if proof.last_fri_step_plain_leaf_values.len() > 0 {
        for el in proof.last_fri_step_plain_leaf_values.iter() {
            result.extend(
                el.iter()
                    .map(|el| {
                        el.into_coeffs_in_base()
                            .map(|el: Mersenne31Field| el.to_reduced_u32())
                    })
                    .flatten(),
            );
        }
    }
    result.extend(
        proof
            .final_monomial_form
            .iter()
            .map(|el| {
                el.into_coeffs_in_base()
                    .map(|el: Mersenne31Field| el.to_reduced_u32())
            })
            .flatten(),
    );
    result.push(proof.pow_nonce as u32);
    result.push((proof.pow_nonce >> 32) as u32);

    result
}

pub fn flatten_query(query: &QuerySet) -> Vec<u32> {
    assert_eq!(
        query.witness_query.query_index,
        query.memory_query.query_index
    );
    assert_eq!(
        query.witness_query.query_index,
        query.stage_2_query.query_index
    );
    assert_eq!(
        query.witness_query.query_index,
        query.quotient_query.query_index
    );
    assert_eq!(
        query.witness_query.query_index,
        query.setup_query.query_index
    );

    let mut result = Vec::new();
    result.push(query.witness_query.query_index);
    flatten_leaf_into(&query.setup_query.leaf_content, &mut result);
    flatten_leaf_into(&query.witness_query.leaf_content, &mut result);
    flatten_leaf_into(&query.memory_query.leaf_content, &mut result);
    flatten_leaf_into(&query.stage_2_query.leaf_content, &mut result);
    flatten_leaf_into(&query.quotient_query.leaf_content, &mut result);
    flatten_leaf_into(&query.initial_fri_query.leaf_content, &mut result);
    for el in query.intermediate_fri_queries.iter() {
        flatten_leaf_into(&el.leaf_content, &mut result);
    }

    // and then merkle paths in the same sequence
    flatten_merkle_path_into(&query.setup_query.merkle_proof, &mut result);
    flatten_merkle_path_into(&query.witness_query.merkle_proof, &mut result);
    flatten_merkle_path_into(&query.memory_query.merkle_proof, &mut result);
    flatten_merkle_path_into(&query.stage_2_query.merkle_proof, &mut result);
    flatten_merkle_path_into(&query.quotient_query.merkle_proof, &mut result);
    flatten_merkle_path_into(&query.initial_fri_query.merkle_proof, &mut result);
    for el in query.intermediate_fri_queries.iter() {
        flatten_merkle_path_into(&el.merkle_proof, &mut result);
    }

    result
}

pub fn flatten_full_proof(
    proof: &Proof,
    lazy_inits_and_teardowns: &[ShuffleRamInitAndTeardownLayout],
) -> Vec<u32> {
    let mut result = flatten_proof_for_skeleton(proof, lazy_inits_and_teardowns);
    for query in proof.queries.iter() {
        result.extend(flatten_query(query));
    }

    result
}
