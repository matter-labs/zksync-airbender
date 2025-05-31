use super::*;

#[derive(Debug, Clone, Hash)]
#[repr(C, align(16))]
pub struct ProofSkeleton<
    const SKELETON_PADDING: usize,
    const CAP_SIZE: usize,
    const NUM_COSETS: usize,
    const NUM_PUBLIC_INPUTS: usize,
    const NUM_DELEGATION_CHALLENGES: usize,
    const NUM_AUX_BOUNDARY_VALUES: usize,
    const NUM_PUBLIC_INPUTS_FROM_STATE_ELEMENTS: usize,
    const NUM_OPENINGS_AT_Z: usize,
    const NUM_OPENINGS_AT_Z_OMEGA: usize,
    const NUM_FRI_STEPS_WITH_ORACLES: usize,
    const FINAL_FRI_STEP_LEAF_SIZE_PER_COSET: usize,
    const FRI_FINAL_DEGREE: usize,
> {
    pub _padding: [u32; SKELETON_PADDING],
    pub circuit_sequence_idx: u32,
    pub delegation_type: u32,
    pub public_inputs: [Mersenne31Field; NUM_PUBLIC_INPUTS_FROM_STATE_ELEMENTS],
    pub setup_caps: [MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    pub memory_argument_challenges: ExternalMemoryArgumentChallenges,
    pub delegation_argument_challenges:
        [ExternalDelegationArgumentChallenges; NUM_DELEGATION_CHALLENGES],
    pub aux_boundary_values: [AuxArgumentsBoundaryValues; NUM_AUX_BOUNDARY_VALUES],
    pub witness_caps: [MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    pub memory_caps: [MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    pub stage_2_caps: [MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    pub memory_grand_product_accumulator: Mersenne31Quartic,
    pub delegation_argument_accumulator: [Mersenne31Quartic; NUM_DELEGATION_CHALLENGES],
    pub quotient_caps: [MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    pub openings_at_z: [Mersenne31Quartic; NUM_OPENINGS_AT_Z],
    pub openings_at_z_omega: [Mersenne31Quartic; NUM_OPENINGS_AT_Z_OMEGA],
    pub fri_intermediate_oracles:
        [[MerkleTreeCap<CAP_SIZE>; NUM_COSETS]; NUM_FRI_STEPS_WITH_ORACLES],
    pub fri_final_step_leafs: [[Mersenne31Quartic; FINAL_FRI_STEP_LEAF_SIZE_PER_COSET]; NUM_COSETS],
    pub monomial_coeffs: [Mersenne31Quartic; FRI_FINAL_DEGREE],
    pub pow_nonce: u64,
}

// NOTE: leaf is tightly packed, we can fill it in the tight loop
#[derive(Debug, Clone, Hash)]
#[repr(C, align(16))]
pub struct QueryValues<
    const BITS_FOR_QUERY_INDEX: usize,
    const DEFAULT_MERKLE_PATH_LENGTH: usize,
    const TOTAL_FRI_ORACLES_PATHS_LENGTH: usize,
    const LEAF_SIZE_SETUP: usize,
    const LEAF_SIZE_WITNESS_TREE: usize,
    const LEAF_SIZE_MEMORY_TREE: usize,
    const LEAF_SIZE_STAGE_2: usize,
    const LEAF_SIZE_QUOTIENT: usize,
    const TOTAL_FRI_LEAFS_SIZES: usize,
    const NUM_FRI_STEPS: usize, // we will still bind it here
> {
    pub query_index: u32,
    pub setup_leaf: [Mersenne31Field; LEAF_SIZE_SETUP],
    pub witness_leaf: [Mersenne31Field; LEAF_SIZE_WITNESS_TREE],
    pub memory_leaf: [Mersenne31Field; LEAF_SIZE_MEMORY_TREE],
    pub stage_2_leaf: [Mersenne31Field; LEAF_SIZE_STAGE_2],
    pub quotient_leaf: [Mersenne31Field; LEAF_SIZE_QUOTIENT],
    pub fri_oracles_leafs: [Mersenne31Field; TOTAL_FRI_LEAFS_SIZES],
}

#[cfg(test)]
mod test {
    use core::usize;

    use verifier_common::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS;

    #[test]
    fn compute_optimal_fri_sequence() {
        let lde_factor = 2;
        let folding_log_2 = [2, 3, 4, 5];
        let initial_degree = 22;
        const NUM_STEPS: usize = 4;
        let num_queries = 53;

        let mut optimal_sequence = [0; NUM_STEPS];

        let mut best_case_found = usize::MAX;
        let mut found_min_degree = 0;
        let mut found_cap_size = 0;

        for min_degree in 2..8 {
            for cap_size_log_2 in 1..7 {
                for path_idx in 0..folding_log_2.len() {
                    let mut num_hashes_used = usize::MAX;
                    step::<NUM_STEPS>(
                        &mut num_hashes_used,
                        &mut optimal_sequence,
                        0,
                        [0; NUM_STEPS],
                        min_degree,
                        cap_size_log_2,
                        initial_degree,
                        0,
                        &folding_log_2,
                        path_idx,
                    );

                    let mut hashes_for_caps = 0;
                    let mut current_degree = initial_degree;
                    for el in optimal_sequence.iter() {
                        current_degree -= *el;
                        if current_degree > min_degree {
                            // we still have some paths
                            hashes_for_caps += (1 << (cap_size_log_2 - 1)) * lde_factor;
                        } else {
                            // we hashed folded tuples into leafs, but we still need to put those
                            // into transcript
                            hashes_for_caps += (1 << (current_degree - 1)) * lde_factor;
                        }
                    }

                    if num_hashes_used != usize::MAX {
                        let total_hashes_used = num_hashes_used * num_queries + hashes_for_caps;

                        if total_hashes_used < best_case_found {
                            best_case_found = total_hashes_used;
                            found_min_degree = min_degree;
                            found_cap_size = cap_size_log_2;
                        }
                    }
                }
            }
        }

        dbg!(best_case_found);
        dbg!(optimal_sequence);
        dbg!(found_min_degree);
        dbg!(found_cap_size);
    }

    fn step<const NUM_STEPS: usize>(
        num_hashes: &mut usize,
        optimal_sequence: &mut [usize; NUM_STEPS],
        used_hashes: usize,
        current_sequence: [usize; NUM_STEPS],
        min_degree: usize,
        cap_size_log2: usize,
        remaining_degree: usize,
        depth: usize,
        possible_foldings: &[usize],
        path_idx: usize,
    ) {
        let folding_degree = possible_foldings[path_idx];
        if remaining_degree <= folding_degree {
            // we can not fold by such degree, but it's unlikely to be
            // the optimal sequence
            return;
        }
        if remaining_degree <= min_degree {
            // we folded enough in the previous steps, so in practice we can fold using shorter path
            if used_hashes < *num_hashes {
                *num_hashes = used_hashes;
                *optimal_sequence = current_sequence;
            }
            return;
        }

        let mut remaining_degree = remaining_degree;
        let hashes_for_leaf = (4 * (1 << folding_degree)) / BLAKE2S_BLOCK_SIZE_U32_WORDS;
        remaining_degree -= folding_degree;
        let mut hashes_to_use = hashes_for_leaf;
        if remaining_degree > cap_size_log2 {
            let leaf_hashes_to_use = remaining_degree - cap_size_log2;
            hashes_to_use += leaf_hashes_to_use;
        } else {
            // we can use folded leaf hashes as cap already
        }

        let used_hashes = used_hashes + hashes_to_use;
        let mut current_sequence = current_sequence;
        current_sequence[depth] = folding_degree;

        if depth != NUM_STEPS - 1 {
            for path_idx in 0..possible_foldings.len() {
                step::<NUM_STEPS>(
                    num_hashes,
                    optimal_sequence,
                    used_hashes,
                    current_sequence,
                    min_degree,
                    cap_size_log2,
                    remaining_degree,
                    depth + 1,
                    possible_foldings,
                    path_idx,
                );
            }
        } else {
            // write back
            if remaining_degree <= min_degree {
                if used_hashes < *num_hashes {
                    *num_hashes = used_hashes;
                    *optimal_sequence = current_sequence;
                }
            }
        }
    }
}
