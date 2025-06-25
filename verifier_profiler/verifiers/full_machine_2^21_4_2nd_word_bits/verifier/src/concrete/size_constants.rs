use super::layout_import::VERIFIER_COMPILED_LAYOUT;
use field::{Field, Mersenne31Complex, Mersenne31Field};
use verifier_common::blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use verifier_common::cs::definitions::REGISTER_SIZE;
use verifier_common::cs::definitions::TIMESTAMP_COLUMNS_NUM_BITS;

pub const LEAF_SIZE_WITNESS_TREE: usize = VERIFIER_COMPILED_LAYOUT.witness_layout.total_width;
pub const LEAF_SIZE_MEMORY_TREE: usize = VERIFIER_COMPILED_LAYOUT.memory_layout.total_width;
pub const LEAF_SIZE_STAGE_2: usize = VERIFIER_COMPILED_LAYOUT.stage_2_layout.total_width;
pub const LEAF_SIZE_SETUP: usize = VERIFIER_COMPILED_LAYOUT.setup_layout.total_width;
pub const LEAF_SIZE_QUOTIENT: usize = 4;
const _: () = const {
    assert!(LEAF_SIZE_QUOTIENT % 4 == 0);

    ()
};
pub const NUM_STATE_ELEMENTS: usize = VERIFIER_COMPILED_LAYOUT.public_inputs.len() / 2;
pub const NUM_PUBLIC_INPUTS_FROM_STATE_ELEMENTS: usize = NUM_STATE_ELEMENTS * 2;

pub const TRACE_LEN_LOG2: usize = VERIFIER_COMPILED_LAYOUT.trace_len_log2;
pub const TRACE_LEN: usize = 1 << TRACE_LEN_LOG2;
pub const FOLDING_PROPERTIES: verifier_common::prover::definitions::FoldingDescription =
    verifier_common::prover::definitions::OPTIMAL_FOLDING_PROPERTIES[TRACE_LEN_LOG2];
pub const TREE_INDEX_MASK: u32 = (1u32 << TRACE_LEN_LOG2) - 1;
pub const FRI_FACTOR_LOG2: usize = 1;
pub const NUM_COSETS: usize = 1 << FRI_FACTOR_LOG2;
pub const POW_BITS: usize = 28;
pub const TOTAL_TREE_CAP_SIZE: usize = 1 << FOLDING_PROPERTIES.total_caps_size_log2;
pub const TREE_CAP_SIZE: usize = TOTAL_TREE_CAP_SIZE / NUM_COSETS;
pub const TREE_CAP_SIZE_LOG2: usize = TREE_CAP_SIZE.trailing_zeros() as usize;
pub const DEFAULT_MERKLE_PATH_LENGTH: usize = TRACE_LEN_LOG2 - TREE_CAP_SIZE_LOG2;
pub const SECURITY_BITS: usize = 80;
pub const SECURITY_BITS_PER_QUERY: usize = FRI_FACTOR_LOG2;
pub const NUM_QUERIES: usize = (SECURITY_BITS - POW_BITS) / SECURITY_BITS_PER_QUERY + 1;
pub const BITS_FOR_QUERY_INDEX: usize = TRACE_LEN_LOG2 + FRI_FACTOR_LOG2;
pub const CAP_ELEMENT_INDEX_MASK: u32 = TREE_CAP_SIZE as u32 - 1;
pub const CAP_INDEX_SHIFT: u32 = TREE_CAP_SIZE_LOG2 as u32;
const MIN_REQUIRED_WORDS_FOR_QUERY_INDEXES: usize = (BITS_FOR_QUERY_INDEX * NUM_QUERIES)
    .next_multiple_of(u32::BITS as usize)
    / (u32::BITS as usize);
// here we do +1 because PoW is checked via the top word
pub const NUM_REQUIRED_WORDS_FOR_QUERY_INDEXES: usize =
    (MIN_REQUIRED_WORDS_FOR_QUERY_INDEXES + 1).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);

pub const NUM_FRI_MERKLE_TREE_CAPS: usize = FOLDING_PROPERTIES.folding_sequence.len() - 1;
pub const NUM_FRI_STEPS: usize = FOLDING_PROPERTIES.folding_sequence.len();
pub const FRI_FINAL_DEGREE: usize = 1 << FOLDING_PROPERTIES.final_monomial_degree_log2;
pub const FRI_FOLDING_SCHEDULE: &[usize] = FOLDING_PROPERTIES.folding_sequence;
pub const FRI_ORACLE_PATH_LENGTHS: [usize; NUM_FRI_STEPS] = compute_fri_folding_properties().1;
pub const TOTAL_FRI_LEAFS_SIZES: usize = compute_fri_folding_properties().2;
pub const TOTAL_FRI_ORACLES_PATHS_LENGTH: usize = const {
    let mut result = 0;
    let mut i = 0;
    while i < NUM_FRI_STEPS {
        result += FRI_ORACLE_PATH_LENGTHS[i];
        i += 1;
    }

    result
};

const fn compute_last_fri_folding_step_properties() -> (bool, usize) {
    let bound = if NUM_QUERIES.is_power_of_two() {
        NUM_QUERIES
    } else {
        NUM_QUERIES.next_power_of_two()
    };

    let mut last_fri_step_expose_leafs = false;
    let mut last_fri_step_leafs_total_size_per_coset = 0;

    let mut final_degree_log2 = TRACE_LEN_LOG2;
    let mut i = 0;
    while i < NUM_FRI_STEPS - 1 {
        final_degree_log2 -= FRI_FOLDING_SCHEDULE[i];
        i += 1;
    }

    let final_num_leafs = 1 << (final_degree_log2 - FRI_FOLDING_SCHEDULE[NUM_FRI_STEPS - 1]);
    // account that we will need to put leaf hashes into transcript,
    // but also that we have cosets
    if (final_num_leafs * 2) / NUM_COSETS <= bound {
        last_fri_step_expose_leafs = true;
        last_fri_step_leafs_total_size_per_coset = 1 << final_degree_log2;
    }

    (
        last_fri_step_expose_leafs,
        last_fri_step_leafs_total_size_per_coset,
    )
}

pub const LAST_FRI_STEP_EXPOSE_LEAFS: bool = compute_last_fri_folding_step_properties().0;
pub const LAST_FRI_STEP_LEAFS_TOTAL_SIZE_PER_COSET: usize =
    compute_last_fri_folding_step_properties().1;
pub const NUM_FRI_STEPS_WITH_ORACLES: usize = NUM_FRI_STEPS - (LAST_FRI_STEP_EXPOSE_LEAFS as usize);

const fn compute_fri_folding_properties() -> ([usize; NUM_FRI_STEPS], [usize; NUM_FRI_STEPS], usize)
{
    let mut total_fri_leaf_sizes = 0;
    let folding_schedule = [0; NUM_FRI_STEPS];
    let mut path_lengths = [0usize; NUM_FRI_STEPS];
    let mut final_degree_log2 = TRACE_LEN_LOG2;
    let mut fri_subtree_path_len = DEFAULT_MERKLE_PATH_LENGTH;
    let mut i = 0;
    while i < NUM_FRI_STEPS {
        if i == NUM_FRI_STEPS - 1 {
            if LAST_FRI_STEP_EXPOSE_LEAFS {
                // do not add
            } else {
                total_fri_leaf_sizes += 4 * (1 << FRI_FOLDING_SCHEDULE[i]);
                fri_subtree_path_len -= FRI_FOLDING_SCHEDULE[i];
                path_lengths[i] = fri_subtree_path_len;
            }
        } else {
            total_fri_leaf_sizes += 4 * (1 << FRI_FOLDING_SCHEDULE[i]);
            fri_subtree_path_len -= FRI_FOLDING_SCHEDULE[i];
            path_lengths[i] = fri_subtree_path_len;
        }

        // and since we folded, next step expected degree is smaller
        final_degree_log2 -= FRI_FOLDING_SCHEDULE[i];
        i += 1;
    }

    // Only last step length can be 0
    let mut i = 0;
    while i < NUM_FRI_STEPS - 1 {
        assert!(path_lengths[i] > 0);
        i += 1;
    }

    assert!(final_degree_log2 == FOLDING_PROPERTIES.final_monomial_degree_log2);

    (folding_schedule, path_lengths, total_fri_leaf_sizes)
}

const _: () = const {
    let mut sum = 0;
    let mut i = 0;
    while i < FRI_FOLDING_SCHEDULE.len() {
        sum += FRI_FOLDING_SCHEDULE[i];
        i += 1;
    }

    assert!(sum < TRACE_LEN_LOG2 + FRI_FACTOR_LOG2);

    ()
};

pub const NUM_WITNESS_OPENINGS: usize = VERIFIER_COMPILED_LAYOUT.witness_layout.total_width;
pub const NUM_MEMORY_OPENINGS: usize = VERIFIER_COMPILED_LAYOUT.memory_layout.total_width;
pub const NUM_SETUP_OPENINGS: usize = VERIFIER_COMPILED_LAYOUT.setup_layout.total_width;
pub const NUM_STAGE2_OPENINGS: usize = VERIFIER_COMPILED_LAYOUT
    .stage_2_layout
    .num_base_field_polys()
    + VERIFIER_COMPILED_LAYOUT
        .stage_2_layout
        .num_ext4_field_polys();

pub const NUM_OPENINGS_AT_Z: usize = VERIFIER_COMPILED_LAYOUT.num_openings_at_z();
pub const NUM_OPENINGS_AT_Z_OMEGA: usize = VERIFIER_COMPILED_LAYOUT.num_openings_at_z_omega();
pub const NUM_STATE_LINKIGE_CONSTRAINTS: usize =
    VERIFIER_COMPILED_LAYOUT.num_state_linkage_constraints();
pub const TOTAL_NUM_OPENINGS: usize = NUM_OPENINGS_AT_Z + NUM_OPENINGS_AT_Z_OMEGA;
pub const NUM_QUOTIENT_TERMS: usize = VERIFIER_COMPILED_LAYOUT.num_quotient_terms();
pub const NUM_DELEGATION_CHALLENGES: usize = const {
    let process_delegations = VERIFIER_COMPILED_LAYOUT
        .memory_layout
        .delegation_request_layout
        .is_some()
        | VERIFIER_COMPILED_LAYOUT
            .memory_layout
            .delegation_processor_layout
            .is_some();

    process_delegations as usize
};
pub const NUM_AUX_BOUNDARY_VALUES: usize = VERIFIER_COMPILED_LAYOUT
    .memory_layout
    .shuffle_ram_inits_and_teardowns
    .is_some() as usize;

const _: () = const {
    assert!(
        NUM_WITNESS_OPENINGS + NUM_MEMORY_OPENINGS + NUM_SETUP_OPENINGS + NUM_STAGE2_OPENINGS + 1
            == NUM_OPENINGS_AT_Z
    );

    ()
};

pub const NUM_WITNESS_OPENING_NEXT_ROW: usize = NUM_STATE_ELEMENTS;
pub const WITNESS_NEXT_ROW_OPENING_INDEXES: [usize; NUM_WITNESS_OPENING_NEXT_ROW] = const {
    let mut result = [0usize; NUM_WITNESS_OPENING_NEXT_ROW];
    let mut i: usize = 0;
    use verifier_common::cs::definitions::ColumnAddress;
    while i < NUM_WITNESS_OPENING_NEXT_ROW {
        let (_src, dst) = VERIFIER_COMPILED_LAYOUT.state_linkage_constraints[i];
        let ColumnAddress::WitnessSubtree(index) = dst else {
            panic!()
        };

        result[i] = index;
        i += 1;
    }

    result
};

pub const NUM_MEMORY_OPENING_NEXT_ROW: usize = const {
    if VERIFIER_COMPILED_LAYOUT
        .memory_layout
        .shuffle_ram_inits_and_teardowns
        .is_some()
    {
        // RAM address space
        REGISTER_SIZE
    } else {
        0
    }
};
pub const MEMORY_NEXT_ROW_OPENING_INDEXES: [usize; NUM_MEMORY_OPENING_NEXT_ROW] = const {
    let mut result = [0usize; NUM_WITNESS_OPENING_NEXT_ROW];
    let mut i: usize = 0;
    while i < NUM_WITNESS_OPENING_NEXT_ROW {
        let index = VERIFIER_COMPILED_LAYOUT
            .memory_layout
            .shuffle_ram_inits_and_teardowns
            .as_ref()
            .unwrap()
            .lazy_init_addresses_columns
            .start()
            + i;

        result[i] = index;
        i += 1;
    }

    result
};

const NUM_BITS_IN_TIMESTAMP_FOR_INDEX_LOG_2: usize = const {
    if VERIFIER_COMPILED_LAYOUT
        .memory_layout
        .shuffle_ram_access_sets
        .len()
        > 0
    {
        use crate::NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP;
        let t = VERIFIER_COMPILED_LAYOUT
            .memory_layout
            .shuffle_ram_access_sets
            .len()
            .next_power_of_two()
            .trailing_zeros();
        assert!(t == NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP);

        t as usize
    } else {
        0
    }
};

pub const CIRCUIT_SEQUENCE_BITS_SHIFT: usize = (TRACE_LEN_LOG2
    + NUM_BITS_IN_TIMESTAMP_FOR_INDEX_LOG_2)
    - (TIMESTAMP_COLUMNS_NUM_BITS as usize);

pub const MEMORY_GRAND_PRODUCT_ACCUMULATOR_OFFSET: usize = VERIFIER_COMPILED_LAYOUT
    .stage_2_layout
    .intermediate_polys_for_memory_argument
    .num_elements()
    - 1;
pub const MEMORY_GRAND_PRODUCT_ACCUMULATOR_POLY_INDEX: usize = VERIFIER_COMPILED_LAYOUT
    .stage_2_layout
    .get_intermediate_polys_for_memory_argument_absolute_poly_idx_for_verifier(
        MEMORY_GRAND_PRODUCT_ACCUMULATOR_OFFSET,
    );

// we should also count a padding so that variable-length parts of the skeleton structs (like public inputs, etc),
// end up in such a way, that we start "setup caps" at offset 0 mod 16, and this way everything after that will be also
// aligned

pub const SKELETON_PADDING: usize = const {
    let mut size = 0;
    // circuit sequence
    size += core::mem::size_of::<u32>();
    // delegation type
    size += core::mem::size_of::<u32>();
    // variable number of public inputs
    assert!(core::mem::size_of::<u32>() == core::mem::size_of::<Mersenne31Field>());
    size += core::mem::size_of::<Mersenne31Field>() * NUM_PUBLIC_INPUTS_FROM_STATE_ELEMENTS;
    let size_mod_16 = size % 16;
    let required_padding_bytes = (16 - size_mod_16) % 16;
    assert!(required_padding_bytes % core::mem::size_of::<u32>() == 0);

    required_padding_bytes / core::mem::size_of::<u32>()
};

pub const MAX_FRI_FOLDING_ROOTS: usize = 1 << 4;
pub const SHARED_FACTORS_FOR_FOLDING: [Mersenne31Complex; MAX_FRI_FOLDING_ROOTS] = const {
    let max_generator = Mersenne31Complex::TWO_ADICITY_GENERATORS_INVERSED[5];
    let mut result = [Mersenne31Complex::ZERO; MAX_FRI_FOLDING_ROOTS];
    let mut i = 0;
    let mut current = Mersenne31Complex::ONE;
    while i < MAX_FRI_FOLDING_ROOTS {
        let index = i.reverse_bits() >> (usize::BITS - 4);
        result[index] = current;
        current.mul_assign_impl(&max_generator);
        i += 1;
    }

    result
};
