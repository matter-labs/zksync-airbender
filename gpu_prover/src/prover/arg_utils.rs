use cs::definitions::{
    IndirectAccessColumns, LookupExpression, OptimizedOraclesForLookupWidth1,
    RegisterAccessColumns, RegisterAndIndirectAccessDescription, ShuffleRamAuxComparisonSet,
    ShuffleRamInitAndTeardownLayout, MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX, MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX, NUM_DELEGATION_ARGUMENT_KEY_PARTS,
    NUM_LOOKUP_ARGUMENT_KEY_PARTS, NUM_MEM_ARGUMENT_KEY_PARTS, NUM_TIMESTAMP_COLUMNS_FOR_RAM,
    REGISTER_SIZE,
};
use cs::one_row_compiler::{
    BatchedRamAccessColumns, ColumnAddress, CompiledCircuitArtifact,
    LookupWidth1SourceDestInformation, LookupWidth1SourceDestInformationForExpressions,
    RegisterOnlyAccessAddress, RegisterOrRamAccessAddress, ShuffleRamAddress,
    ShuffleRamQueryColumns,
};
use field::{Field, FieldExtension, PrimeField};
use prover::definitions::{ExternalDelegationArgumentChallenges, ExternalMemoryArgumentChallenges};
use prover::prover_stages::cached_data::ProverCachedData;

use super::{BF, E4};
use std::mem::size_of;
// TODO: Once we have an overall prove function, consider making a big standalon helper
// that creates all args common to stages 2 and 3.

#[derive(Clone, Default)]
#[repr(C)]
pub struct LookupChallenges {
    pub linearization_challenges: [E4; NUM_LOOKUP_ARGUMENT_KEY_PARTS - 1],
    pub gamma: E4,
}

impl LookupChallenges {
    #[allow(dead_code)]
    pub fn new(challenges: &[E4], gamma: E4) -> Self {
        // ensures size matches corresponding cuda struct
        assert_eq!(NUM_LOOKUP_ARGUMENT_KEY_PARTS, 4);
        assert_eq!(challenges.len(), NUM_LOOKUP_ARGUMENT_KEY_PARTS - 1);
        let linearization_challenges: [E4; NUM_LOOKUP_ARGUMENT_KEY_PARTS - 1] =
            std::array::from_fn(|i| challenges[i]);
        Self {
            linearization_challenges,
            gamma,
        }
    }
}

#[derive(Clone)]
#[repr(C)]
pub struct RangeCheck16ArgsLayout {
    pub num_dst_cols: u32,
    pub src_cols_start: u32,
    pub bf_args_start: u32,
    pub e4_args_start: u32,
    // to be used if num_src_cols is odd, currently not supported on CPU
    // pub maybe_e4_arg_remainder_col: u32,
}

impl RangeCheck16ArgsLayout {
    pub fn new<F: Fn(usize) -> usize>(
        circuit: &CompiledCircuitArtifact<BF>,
        range_check_16_width_1_lookups_access: &Vec<LookupWidth1SourceDestInformation>,
        range_check_16_width_1_lookups_access_via_expressions: &Vec<
            LookupWidth1SourceDestInformationForExpressions<BF>,
        >,
        translate_e4_offset: &F,
    ) -> Self {
        let num_src_cols = circuit.witness_layout.range_check_16_columns.num_elements();
        assert_eq!(num_src_cols % 2, 0);
        let num_dst_cols = num_src_cols / 2;
        let src_cols_start = circuit.witness_layout.range_check_16_columns.start();
        let args_metadata = &circuit.stage_2_layout.intermediate_polys_for_range_check_16;
        assert_eq!(
            num_dst_cols + range_check_16_width_1_lookups_access_via_expressions.len(),
            args_metadata.base_field_oracles.num_elements()
        );
        assert_eq!(
            args_metadata.base_field_oracles.num_elements(),
            args_metadata.ext_4_field_oracles.num_elements()
        );
        let bf_args_start = args_metadata.base_field_oracles.start();
        let e4_args_start = translate_e4_offset(args_metadata.ext_4_field_oracles.start());
        // double-check that expected layout is consistent with layout in CachedData
        assert_eq!(range_check_16_width_1_lookups_access.len(), num_dst_cols);
        for (i, lookup_set) in range_check_16_width_1_lookups_access.iter().enumerate() {
            assert_eq!(lookup_set.a_col, src_cols_start + 2 * i);
            assert_eq!(lookup_set.b_col, src_cols_start + 2 * i + 1);
            assert_eq!(
                lookup_set.base_field_quadratic_oracle_col,
                bf_args_start + i
            );
            assert_eq!(
                translate_e4_offset(lookup_set.ext4_field_inverses_columns_start),
                e4_args_start + i,
            );
        }
        Self {
            num_dst_cols: num_dst_cols as u32,
            src_cols_start: src_cols_start as u32,
            bf_args_start: bf_args_start as u32,
            e4_args_start: e4_args_start as u32,
        }
    }
}

#[derive(Clone, Default)]
#[repr(C)]
pub struct DelegationChallenges {
    pub linearization_challenges: [E4; NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1],
    pub gamma: E4,
}

// At the time I write this, DelegationChallenges happens to have the same layout as
// zksync_airbender's ExternalDelegationArgumentChallenges.
// But I shouldn't pass an ExternalDelegationArgumentChallenges to a kernel launch,
// because CUDA blindly bitcopies inputs into kernel args, and the kernel expects
// a certain layout. If zksync_airbender changed its layout, I'd get silent data corruption.
// Therefore, I always repack zksync_airbender's struct into a struct I explicitly control.
impl DelegationChallenges {
    pub fn new(challenges: &ExternalDelegationArgumentChallenges) -> Self {
        // ensures size matches corresponding cuda struct
        assert_eq!(NUM_DELEGATION_ARGUMENT_KEY_PARTS, 4);
        assert_eq!(
            challenges
                .delegation_argument_linearization_challenges
                .len(),
            NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1
        );
        let linearization_challenges: [E4; NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1] =
            std::array::from_fn(|i| challenges.delegation_argument_linearization_challenges[i]);
        Self {
            linearization_challenges,
            gamma: challenges.delegation_argument_gamma,
        }
    }
}

#[derive(Default)]
#[repr(C)]
pub struct DelegationRequestMetadata {
    pub multiplicity_col: u32,
    pub timestamp_setup_col: u32,
    pub memory_timestamp_high_from_circuit_idx: BF,
    pub delegation_type_col: u32,
    pub abi_mem_offset_high_col: u32,
    pub in_cycle_write_idx: BF,
}

#[derive(Default)]
#[repr(C)]
pub struct DelegationProcessingMetadata {
    pub multiplicity_col: u32,
    pub delegation_type: BF,
    pub abi_mem_offset_high_col: u32,
    pub write_timestamp_col: u32,
}

pub fn get_delegation_metadata(
    cached_data: &ProverCachedData,
    circuit: &CompiledCircuitArtifact<BF>,
) -> (DelegationRequestMetadata, DelegationProcessingMetadata) {
    let handle_delegation_requests = cached_data.handle_delegation_requests;
    let process_delegations = cached_data.process_delegations;
    let execute_delegation_argument = cached_data.execute_delegation_argument;
    let delegation_request_layout = cached_data.delegation_request_layout;
    let delegation_processor_layout = cached_data.delegation_processor_layout;
    let memory_timestamp_high_from_circuit_idx = cached_data.memory_timestamp_high_from_circuit_idx;
    let delegation_type = cached_data.delegation_type;
    assert_eq!(
        execute_delegation_argument,
        handle_delegation_requests || process_delegations
    );
    // NB: handle_delegation_requests and process_delegations are mutually exclusive
    if handle_delegation_requests {
        assert!(!process_delegations);
        let layout = delegation_request_layout;
        let request_metadata = DelegationRequestMetadata {
            multiplicity_col: layout.multiplicity.start() as u32,
            timestamp_setup_col: circuit.setup_layout.timestamp_setup_columns.start() as u32,
            memory_timestamp_high_from_circuit_idx,
            delegation_type_col: layout.delegation_type.start() as u32,
            abi_mem_offset_high_col: layout.abi_mem_offset_high.start() as u32,
            in_cycle_write_idx: BF::from_u64_unchecked(layout.in_cycle_write_index as u64),
        };
        (request_metadata, DelegationProcessingMetadata::default())
    } else if process_delegations {
        assert!(!handle_delegation_requests); // redundant, for clarity
        let layout = delegation_processor_layout;
        let processing_metadata = DelegationProcessingMetadata {
            multiplicity_col: layout.multiplicity.start() as u32,
            delegation_type,
            abi_mem_offset_high_col: layout.abi_mem_offset_high.start() as u32,
            write_timestamp_col: layout.write_timestamp.start() as u32,
        };
        (DelegationRequestMetadata::default(), processing_metadata)
    } else {
        (
            DelegationRequestMetadata::default(),
            DelegationProcessingMetadata::default(),
        )
    }
}

#[derive(Clone)]
#[repr(C)]
pub struct MemoryChallenges {
    pub address_low_challenge: E4,
    pub address_high_challenge: E4,
    pub timestamp_low_challenge: E4,
    pub timestamp_high_challenge: E4,
    pub value_low_challenge: E4,
    pub value_high_challenge: E4,
    pub gamma: E4,
}

impl MemoryChallenges {
    pub fn new(external_challenges: &ExternalMemoryArgumentChallenges) -> Self {
        let challenges = &external_challenges.memory_argument_linearization_challenges;
        assert_eq!(NUM_MEM_ARGUMENT_KEY_PARTS, 7);
        assert_eq!(challenges.len(), NUM_MEM_ARGUMENT_KEY_PARTS - 1);
        Self {
            address_low_challenge: challenges[MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
            address_high_challenge: challenges[MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX],
            timestamp_low_challenge: challenges[MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX],
            timestamp_high_challenge: challenges[MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX],
            value_low_challenge: challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX],
            value_high_challenge: challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX],
            gamma: external_challenges.memory_argument_gamma,
        }
    }
}

const MAX_EXPRESSION_PAIRS: usize = 84;
const MAX_EXPRESSIONS: usize = 2 * MAX_EXPRESSION_PAIRS;
const MAX_TERMS_PER_EXPRESSION: usize = 4;
const MAX_EXPRESSION_TERMS: usize = MAX_TERMS_PER_EXPRESSION * MAX_EXPRESSIONS;

#[non_exhaustive]
pub enum ColTypeFlags {}

impl ColTypeFlags {
    #[allow(unused)]
    pub const WITNESS: u16 = 0; // must be 0
    pub const MEMORY: u16 = 1 << 14;
    pub const SETUP: u16 = 1 << 15;
}

// We expect (and assert) that non-shuffle-ram expressions have constant_term = 0
// and use only memory and witness (not setup) columns.
#[derive(Clone)]
#[repr(C)]
pub struct FlattenedLookupExpressionsLayout {
    pub coeffs: [u32; MAX_EXPRESSION_TERMS],
    pub col_idxs: [u16; MAX_EXPRESSION_TERMS],
    pub constant_terms: [BF; MAX_EXPRESSIONS],
    pub num_terms_per_expression: [u8; MAX_EXPRESSIONS],
    pub bf_dst_cols: [u8; MAX_EXPRESSION_PAIRS],
    pub e4_dst_cols: [u8; MAX_EXPRESSION_PAIRS],
    pub num_range_check_16_expression_pairs: u32,
    pub num_timestamp_expression_pairs: u32,
    pub range_check_16_constant_terms_are_zero: bool,
    pub timestamp_constant_terms_are_zero: bool,
}

// I could make separate instances for the range check 16 and timestamp expressions,
// but flattening them both together is more space-efficient and not too difficult.
impl FlattenedLookupExpressionsLayout {
    pub fn new<F: Fn(usize) -> usize>(
        range_check_16_expression_pairs: &Vec<LookupWidth1SourceDestInformationForExpressions<BF>>,
        timestamp_expression_pairs: &Vec<LookupWidth1SourceDestInformationForExpressions<BF>>,
        num_stage_2_bf_cols: usize,
        num_stage_2_e4_cols: usize,
        expect_constant_terms_are_zero: bool,
        translate_e4_offset: &F,
    ) -> Self {
        assert!(
            range_check_16_expression_pairs.len() + timestamp_expression_pairs.len()
                < MAX_EXPRESSION_PAIRS
        );
        // safer to check each individual conversion
        // assert!(num_stage_2_bf_cols <= u8::MAX as usize);
        // assert!(num_stage_2_e4_cols <= u8::MAX as usize);
        let mut coeffs = [0 as u32; MAX_EXPRESSION_TERMS];
        let mut col_idxs = [0 as u16; MAX_EXPRESSION_TERMS];
        let mut constant_terms = [BF::ZERO; MAX_EXPRESSIONS];
        let mut num_terms_per_expression = [0 as u8; MAX_EXPRESSIONS];
        let mut bf_dst_cols = [0 as u8; MAX_EXPRESSION_PAIRS];
        let mut e4_dst_cols = [0 as u8; MAX_EXPRESSION_PAIRS];
        let mut range_check_16_constant_terms_are_zero: bool = true;
        let mut timestamp_constant_terms_are_zero: bool = true;
        let mut expression_idx: usize = 0;
        let mut flat_term_idx: usize = 0;
        let mut stash_expr = |expr: &LookupExpression<BF>,
                              expression_idx: &mut usize,
                              flat_term_idx: &mut usize,
                              constant_terms_are_zero: &mut bool| {
            let LookupExpression::Expression(a) = expr else {
                unreachable!()
            };
            let num_terms = a.linear_terms.len();
            assert!(num_terms > 0);
            assert!(num_terms <= MAX_TERMS_PER_EXPRESSION);
            if expect_constant_terms_are_zero {
                assert_eq!(a.constant_term, BF::ZERO);
            } else {
                if a.constant_term != BF::ZERO {
                    *constant_terms_are_zero = false;
                }
                constant_terms[*expression_idx] = a.constant_term;
            };
            num_terms_per_expression[*expression_idx] = u8::try_from(num_terms).unwrap();
            for (coeff, column_address) in a.linear_terms.iter() {
                coeffs[*flat_term_idx] = coeff.0;
                col_idxs[*flat_term_idx] = match column_address {
                    ColumnAddress::WitnessSubtree(col) => *col as u16,
                    ColumnAddress::MemorySubtree(col) => (*col as u16) | ColTypeFlags::MEMORY,
                    _ => panic!(
                        "Non-shuffle-ram expressions are expected to use witness and memory cols only",
                    ),
                };
                *flat_term_idx = *flat_term_idx + 1;
            }
            *expression_idx = *expression_idx + 1;
        };
        let mut i = 0; // expression pair idx
        for lookup_set in range_check_16_expression_pairs.iter() {
            stash_expr(
                &lookup_set.a_expr,
                &mut expression_idx,
                &mut flat_term_idx,
                &mut range_check_16_constant_terms_are_zero,
            );
            stash_expr(
                &lookup_set.b_expr,
                &mut expression_idx,
                &mut flat_term_idx,
                &mut range_check_16_constant_terms_are_zero,
            );
            let bf_dst_col = lookup_set.base_field_quadratic_oracle_col;
            assert!(bf_dst_col < num_stage_2_bf_cols);
            bf_dst_cols[i] = u8::try_from(bf_dst_col).unwrap();
            let e4_dst_col = translate_e4_offset(lookup_set.ext4_field_inverses_columns_start);
            assert!(e4_dst_col < num_stage_2_e4_cols);
            e4_dst_cols[i] = u8::try_from(e4_dst_col).unwrap();
            i += 1;
        }
        for lookup_set in timestamp_expression_pairs.iter() {
            stash_expr(
                &lookup_set.a_expr,
                &mut expression_idx,
                &mut flat_term_idx,
                &mut timestamp_constant_terms_are_zero,
            );
            stash_expr(
                &lookup_set.b_expr,
                &mut expression_idx,
                &mut flat_term_idx,
                &mut timestamp_constant_terms_are_zero,
            );
            let bf_dst_col = lookup_set.base_field_quadratic_oracle_col;
            assert!(bf_dst_col < num_stage_2_bf_cols);
            bf_dst_cols[i] = u8::try_from(bf_dst_col).unwrap();
            let e4_dst_col = translate_e4_offset(lookup_set.ext4_field_inverses_columns_start);
            assert!(e4_dst_col < num_stage_2_e4_cols);
            e4_dst_cols[i] = u8::try_from(e4_dst_col).unwrap();
            i += 1;
        }
        assert_eq!(timestamp_constant_terms_are_zero, true); // just testing a theory
        Self {
            coeffs,
            col_idxs,
            constant_terms,
            num_terms_per_expression,
            bf_dst_cols,
            e4_dst_cols,
            num_range_check_16_expression_pairs: range_check_16_expression_pairs.len() as u32,
            num_timestamp_expression_pairs: timestamp_expression_pairs.len() as u32,
            range_check_16_constant_terms_are_zero,
            timestamp_constant_terms_are_zero,
        }
    }
}

impl Default for FlattenedLookupExpressionsLayout {
    fn default() -> Self {
        Self {
            coeffs: [0; MAX_EXPRESSION_TERMS],
            col_idxs: [0; MAX_EXPRESSION_TERMS],
            constant_terms: [BF::ZERO; MAX_EXPRESSIONS],
            num_terms_per_expression: [0; MAX_EXPRESSIONS],
            bf_dst_cols: [0; MAX_EXPRESSION_PAIRS],
            e4_dst_cols: [0; MAX_EXPRESSION_PAIRS],
            num_range_check_16_expression_pairs: 0,
            num_timestamp_expression_pairs: 0,
            range_check_16_constant_terms_are_zero: true,
            timestamp_constant_terms_are_zero: true,
        }
    }
}

const MAX_EXPRESSION_PAIRS_FOR_SHUFFLE_RAM: usize = 4;
const MAX_EXPRESSIONS_FOR_SHUFFLE_RAM: usize = 2 * MAX_EXPRESSION_PAIRS_FOR_SHUFFLE_RAM;
const MAX_EXPRESSION_TERMS_FOR_SHUFFLE_RAM: usize =
    MAX_TERMS_PER_EXPRESSION * MAX_EXPRESSIONS_FOR_SHUFFLE_RAM;

// Each shuffle ram lookup expressions may have a nonzero constant_term.
// Each column may be witness, memory, or setup.
#[derive(Clone)]
#[repr(C)]
pub struct FlattenedLookupExpressionsForShuffleRamLayout {
    pub coeffs: [u32; MAX_EXPRESSION_TERMS_FOR_SHUFFLE_RAM],
    pub col_idxs: [u16; MAX_EXPRESSION_TERMS_FOR_SHUFFLE_RAM],
    pub constant_terms: [BF; MAX_EXPRESSIONS_FOR_SHUFFLE_RAM],
    pub num_terms_per_expression: [u8; MAX_EXPRESSIONS_FOR_SHUFFLE_RAM],
    pub bf_dst_cols: [u8; MAX_EXPRESSION_PAIRS_FOR_SHUFFLE_RAM],
    pub e4_dst_cols: [u8; MAX_EXPRESSION_PAIRS_FOR_SHUFFLE_RAM],
    pub num_expression_pairs: u32,
}

impl FlattenedLookupExpressionsForShuffleRamLayout {
    pub fn new<F: Fn(usize) -> usize>(
        expression_pairs: &Vec<LookupWidth1SourceDestInformationForExpressions<BF>>,
        num_stage_2_bf_cols: usize,
        num_stage_2_e4_cols: usize,
        translate_e4_offset: &F,
    ) -> Self {
        assert!(expression_pairs.len() <= MAX_EXPRESSION_PAIRS_FOR_SHUFFLE_RAM);
        // safer to check each individual conversion
        // assert!(num_stage_2_bf_cols <= u8::MAX as usize);
        // assert!(num_stage_2_e4_cols <= u8::MAX as usize);
        let mut coeffs = [0 as u32; MAX_EXPRESSION_TERMS_FOR_SHUFFLE_RAM];
        let mut col_idxs = [0 as u16; MAX_EXPRESSION_TERMS_FOR_SHUFFLE_RAM];
        let mut constant_terms = [BF::ZERO; MAX_EXPRESSIONS_FOR_SHUFFLE_RAM];
        let mut num_terms_per_expression = [0 as u8; MAX_EXPRESSIONS_FOR_SHUFFLE_RAM];
        let mut bf_dst_cols = [0 as u8; MAX_EXPRESSION_PAIRS_FOR_SHUFFLE_RAM];
        let mut e4_dst_cols = [0 as u8; MAX_EXPRESSION_PAIRS_FOR_SHUFFLE_RAM];
        let mut expression_idx: usize = 0;
        let mut flat_term_idx: usize = 0;
        let mut stash_expr = |expr: &LookupExpression<BF>,
                              expression_idx: &mut usize,
                              flat_term_idx: &mut usize| {
            let LookupExpression::Expression(a) = expr else {
                unreachable!()
            };
            let num_terms = a.linear_terms.len();
            assert!(num_terms > 0);
            assert!(num_terms <= MAX_TERMS_PER_EXPRESSION);
            constant_terms[*expression_idx] = a.constant_term;
            num_terms_per_expression[*expression_idx] = u8::try_from(num_terms).unwrap();
            for (coeff, column_address) in a.linear_terms.iter() {
                coeffs[*flat_term_idx] = coeff.0;
                col_idxs[*flat_term_idx] = match column_address {
                    ColumnAddress::WitnessSubtree(col) => *col as u16,
                    ColumnAddress::MemorySubtree(col) => (*col as u16) | ColTypeFlags::MEMORY,
                    ColumnAddress::SetupSubtree(col) => (*col as u16) | ColTypeFlags::SETUP,
                    _ => panic!(
                        "Non-shuffle-ram expressions are expected to use witness and memory cols only",
                    ),
                };
                *flat_term_idx = *flat_term_idx + 1;
            }
            *expression_idx = *expression_idx + 1;
        };
        for (i, lookup_set) in expression_pairs.iter().enumerate() {
            stash_expr(&lookup_set.a_expr, &mut expression_idx, &mut flat_term_idx);
            stash_expr(&lookup_set.b_expr, &mut expression_idx, &mut flat_term_idx);
            let bf_dst_col = lookup_set.base_field_quadratic_oracle_col;
            assert!(bf_dst_col < num_stage_2_bf_cols);
            bf_dst_cols[i] = u8::try_from(bf_dst_col).unwrap();
            let e4_dst_col = translate_e4_offset(lookup_set.ext4_field_inverses_columns_start);
            assert!(e4_dst_col < num_stage_2_e4_cols);
            e4_dst_cols[i] = u8::try_from(e4_dst_col).unwrap();
        }
        Self {
            coeffs,
            col_idxs,
            constant_terms,
            num_terms_per_expression,
            bf_dst_cols,
            e4_dst_cols,
            num_expression_pairs: expression_pairs.len() as u32,
        }
    }
}

impl Default for FlattenedLookupExpressionsForShuffleRamLayout {
    fn default() -> Self {
        Self {
            coeffs: [0; MAX_EXPRESSION_TERMS_FOR_SHUFFLE_RAM],
            col_idxs: [0; MAX_EXPRESSION_TERMS_FOR_SHUFFLE_RAM],
            constant_terms: [BF::ZERO; MAX_EXPRESSIONS_FOR_SHUFFLE_RAM],
            num_terms_per_expression: [0; MAX_EXPRESSIONS_FOR_SHUFFLE_RAM],
            bf_dst_cols: [0; MAX_EXPRESSION_PAIRS_FOR_SHUFFLE_RAM],
            e4_dst_cols: [0; MAX_EXPRESSION_PAIRS_FOR_SHUFFLE_RAM],
            num_expression_pairs: 0,
        }
    }
}

#[derive(Clone)]
#[repr(C)]
pub struct LazyInitTeardownLayout {
    pub init_address_start: u32,
    pub teardown_value_start: u32,
    pub teardown_timestamp_start: u32,
    pub init_address_aux_low: u32,
    pub init_address_aux_high: u32,
    pub init_address_intermediate_borrow: u32,
    pub init_address_final_borrow: u32,
    pub bf_arg_col: u32,
    pub e4_arg_col: u32,
    pub process_shuffle_ram_init: bool,
}

impl LazyInitTeardownLayout {
    fn unpack_witness_column_address(column_address: ColumnAddress) -> usize {
        if let ColumnAddress::WitnessSubtree(col) = column_address {
            col
        } else {
            panic!("shuffle ram aux helpers should be in witness")
        }
    }

    pub fn new<F: Fn(usize) -> usize>(
        circuit: &CompiledCircuitArtifact<BF>,
        lookup_set: &OptimizedOraclesForLookupWidth1,
        shuffle_ram_inits_and_teardowns: &ShuffleRamInitAndTeardownLayout,
        translate_e4_offset: &F,
    ) -> Self {
        let init_address_start = shuffle_ram_inits_and_teardowns
            .lazy_init_addresses_columns
            .start();
        let teardown_value_start = shuffle_ram_inits_and_teardowns
            .lazy_teardown_values_columns
            .start();
        let teardown_timestamp_start = shuffle_ram_inits_and_teardowns
            .lazy_teardown_timestamps_columns
            .start();
        let lazy_init_address_aux_vars = circuit.lazy_init_address_aux_vars.expect("should exist");
        let ShuffleRamAuxComparisonSet {
            aux_low_high: [address_aux_low, address_aux_high],
            intermediate_borrow,
            final_borrow,
        } = lazy_init_address_aux_vars;
        let init_address_aux_low = Self::unpack_witness_column_address(address_aux_low);
        let init_address_aux_high = Self::unpack_witness_column_address(address_aux_high);
        let intermediate_borrow = Self::unpack_witness_column_address(intermediate_borrow);
        let final_borrow = Self::unpack_witness_column_address(final_borrow);
        Self {
            init_address_start: init_address_start as u32,
            teardown_value_start: teardown_value_start as u32,
            teardown_timestamp_start: teardown_timestamp_start as u32,
            init_address_aux_low: init_address_aux_low as u32,
            init_address_aux_high: init_address_aux_high as u32,
            init_address_intermediate_borrow: intermediate_borrow as u32,
            init_address_final_borrow: final_borrow as u32,
            bf_arg_col: lookup_set.base_field_oracles.start() as u32,
            e4_arg_col: translate_e4_offset(lookup_set.ext_4_field_oracles.start()) as u32,
            process_shuffle_ram_init: true,
        }
    }
}

impl Default for LazyInitTeardownLayout {
    fn default() -> Self {
        Self {
            init_address_start: 0,
            teardown_value_start: 0,
            teardown_timestamp_start: 0,
            init_address_aux_low: 0,
            init_address_aux_high: 0,
            init_address_intermediate_borrow: 0,
            init_address_final_borrow: 0,
            bf_arg_col: 0,
            e4_arg_col: 0,
            process_shuffle_ram_init: false,
        }
    }
}

#[derive(Clone, Copy, Default)]
#[repr(C)]
pub struct ShuffleRamAccess {
    pub address_start: u32,
    pub read_timestamp_start: u32,
    pub read_value_start: u32,
    pub maybe_write_value_start: u32,
    pub maybe_is_register_start: u32,
    pub is_write: bool,
    pub is_register_only: bool,
}

const MAX_SHUFFLE_RAM_ACCESSES: usize = 3;

#[derive(Clone)]
#[repr(C)]
pub struct ShuffleRamAccesses {
    pub accesses: [ShuffleRamAccess; MAX_SHUFFLE_RAM_ACCESSES],
    pub num_accesses: u32,
    pub write_timestamp_in_setup_start: u32,
}

impl ShuffleRamAccesses {
    pub fn new(
        shuffle_ram_access_sets: &Vec<ShuffleRamQueryColumns>,
        write_timestamp_in_setup_start: usize,
    ) -> Self {
        let mut accesses = [ShuffleRamAccess::default(); MAX_SHUFFLE_RAM_ACCESSES];
        let num_accesses = shuffle_ram_access_sets.len();
        assert!(num_accesses <= MAX_SHUFFLE_RAM_ACCESSES);
        // imitates zksync_airbender's stage2.rs
        for (i, memory_access_columns) in shuffle_ram_access_sets.iter().enumerate() {
            match memory_access_columns {
                ShuffleRamQueryColumns::Readonly(columns) => {
                    let (is_register_only, address_start, maybe_is_register_start) =
                        match memory_access_columns.get_address() {
                            ShuffleRamAddress::RegisterOnly(RegisterOnlyAccessAddress {
                                register_index,
                            }) => (true, register_index.start(), 0),
                            ShuffleRamAddress::RegisterOrRam(RegisterOrRamAccessAddress {
                                is_register,
                                address,
                            }) => (false, address.start(), is_register.start()),
                        };
                    accesses[i] = ShuffleRamAccess {
                        address_start: address_start as u32,
                        read_timestamp_start: columns.read_timestamp.start() as u32,
                        read_value_start: columns.read_value.start() as u32,
                        maybe_write_value_start: 0,
                        maybe_is_register_start: maybe_is_register_start as u32,
                        is_write: false,
                        is_register_only,
                    };
                }
                ShuffleRamQueryColumns::Write(columns) => {
                    let (is_register_only, address_start, maybe_is_register_start) =
                        match memory_access_columns.get_address() {
                            ShuffleRamAddress::RegisterOnly(RegisterOnlyAccessAddress {
                                register_index,
                            }) => (true, register_index.start(), 0),
                            ShuffleRamAddress::RegisterOrRam(RegisterOrRamAccessAddress {
                                is_register,
                                address,
                            }) => (false, address.start(), is_register.start()),
                        };
                    accesses[i] = ShuffleRamAccess {
                        address_start: address_start as u32,
                        read_timestamp_start: columns.read_timestamp.start() as u32,
                        read_value_start: columns.read_value.start() as u32,
                        maybe_write_value_start: columns.write_value.start() as u32,
                        maybe_is_register_start: maybe_is_register_start as u32,
                        is_write: true,
                        is_register_only,
                    };
                }
                #[allow(unreachable_patterns)]
                _ => unreachable!("Unexpected ShuffleRamQueryColumns variant"),
            }
        }
        Self {
            accesses,
            num_accesses: num_accesses as u32,
            write_timestamp_in_setup_start: write_timestamp_in_setup_start as u32,
        }
    }
}

impl Default for ShuffleRamAccesses {
    fn default() -> Self {
        Self {
            accesses: [ShuffleRamAccess::default(); MAX_SHUFFLE_RAM_ACCESSES],
            num_accesses: 0,
            write_timestamp_in_setup_start: 0,
        }
    }
}

#[derive(Clone, Copy, Default)]
#[repr(C)]
pub struct BatchedRamAccess {
    pub gamma_plus_address_low_contribution: E4,
    pub read_timestamp_col: u32,
    pub read_value_col: u32,
    pub maybe_write_value_col: u32,
    pub is_write: bool,
}

pub const MAX_BATCHED_RAM_ACCESSES: usize = 36;

#[derive(Clone)]
#[repr(C)]
pub struct BatchedRamAccesses {
    pub accesses: [BatchedRamAccess; MAX_BATCHED_RAM_ACCESSES],
    pub num_accesses: u32,
    pub write_timestamp_col: u32,
    pub abi_mem_offset_high_col: u32,
}

impl BatchedRamAccesses {
    pub fn new(
        challenges: &MemoryChallenges,
        batched_ram_accesses: &Vec<BatchedRamAccessColumns>,
        write_timestamp_col: usize,
        abi_mem_offset_high_col: usize,
    ) -> Self {
        let mut accesses = [BatchedRamAccess::default(); MAX_BATCHED_RAM_ACCESSES];
        let num_accesses = batched_ram_accesses.len();
        assert!(num_accesses <= MAX_BATCHED_RAM_ACCESSES);
        // imitates zksync_airbender's stage2.rs
        for (i, memory_access_columns) in batched_ram_accesses.iter().enumerate() {
            let offset = i * std::mem::size_of::<u32>();
            let address_low = BF::from_u64_unchecked(offset as u64);
            let mut gamma_plus_address_low_contribution = challenges.address_low_challenge.clone();
            gamma_plus_address_low_contribution.mul_assign_by_base(&address_low);
            gamma_plus_address_low_contribution.add_assign(&challenges.gamma);
            match memory_access_columns {
                BatchedRamAccessColumns::ReadAccess {
                    read_timestamp,
                    read_value,
                } => {
                    accesses[i] = BatchedRamAccess {
                        gamma_plus_address_low_contribution,
                        read_timestamp_col: read_timestamp.start() as u32,
                        read_value_col: read_value.start() as u32,
                        maybe_write_value_col: 0,
                        is_write: false,
                    };
                }
                BatchedRamAccessColumns::WriteAccess {
                    read_timestamp,
                    read_value,
                    write_value,
                } => {
                    accesses[i] = BatchedRamAccess {
                        gamma_plus_address_low_contribution,
                        read_timestamp_col: read_timestamp.start() as u32,
                        read_value_col: read_value.start() as u32,
                        maybe_write_value_col: write_value.start() as u32,
                        is_write: true,
                    };
                }
                #[allow(unreachable_patterns)]
                _ => unreachable!("Unexpected BatchedRamAccessColumns variant"),
            }
        }
        Self {
            accesses,
            num_accesses: num_accesses as u32,
            write_timestamp_col: write_timestamp_col as u32,
            abi_mem_offset_high_col: abi_mem_offset_high_col as u32,
        }
    }
}

impl Default for BatchedRamAccesses {
    fn default() -> Self {
        Self {
            accesses: [BatchedRamAccess::default(); MAX_BATCHED_RAM_ACCESSES],
            num_accesses: 0,
            write_timestamp_col: 0,
            abi_mem_offset_high_col: 0,
        }
    }
}

#[derive(Clone, Copy, Default)]
#[repr(C)]
pub struct RegisterAccess {
    pub gamma_plus_one_plus_address_low_contribution: E4,
    pub read_timestamp_col: u32,
    pub read_value_col: u32,
    pub maybe_write_value_col: u32,
    pub is_write: bool,
}

#[derive(Clone, Copy, Default)]
#[repr(C)]
pub struct IndirectAccess {
    pub offset: u32,
    pub read_timestamp_col: u32,
    pub read_value_col: u32,
    pub maybe_write_value_col: u32,
    pub address_derivation_carry_bit_col: u32,
    pub address_derivation_carry_bit_num_elements: u32,
    pub is_write: bool,
}

pub const MAX_REGISTER_ACCESSES: usize = 4;
pub const MAX_INDIRECT_ACCESSES: usize = 40;

#[derive(Clone)]
#[repr(C)]
pub struct RegisterAndIndirectAccesses {
    pub register_accesses: [RegisterAccess; MAX_REGISTER_ACCESSES],
    pub indirect_accesses: [IndirectAccess; MAX_INDIRECT_ACCESSES],
    pub indirect_accesses_per_register_access: [u32; MAX_REGISTER_ACCESSES],
    pub num_register_accesses: u32,
    pub write_timestamp_col: u32,
}

impl RegisterAndIndirectAccesses {
    pub fn new(
        challenges: &MemoryChallenges,
        register_and_indirect_accesses: &Vec<RegisterAndIndirectAccessDescription>,
        write_timestamp_col: usize,
    ) -> Self {
        assert_eq!(NUM_TIMESTAMP_COLUMNS_FOR_RAM, 2);
        assert_eq!(REGISTER_SIZE, 2);
        let mut register_accesses = [RegisterAccess::default(); MAX_REGISTER_ACCESSES];
        let mut indirect_accesses = [IndirectAccess::default(); MAX_INDIRECT_ACCESSES];
        let mut indirect_accesses_per_register_access = [0; MAX_REGISTER_ACCESSES];
        let num_register_accesses = register_and_indirect_accesses.len();
        assert!(num_register_accesses <= MAX_REGISTER_ACCESSES);
        // imitates zksync_airbender's stage2.rs
        let mut flat_indirect_idx = 0;
        for (i, register_access_columns) in register_and_indirect_accesses.iter().enumerate() {
            match register_access_columns.register_access {
                RegisterAccessColumns::ReadAccess {
                    read_timestamp,
                    read_value,
                    register_index,
                } => {
                    let address_low = BF::from_u64_unchecked(register_index as u64);
                    let mut gamma_plus_one_plus_address_low_contribution =
                        challenges.address_low_challenge.clone();
                    gamma_plus_one_plus_address_low_contribution.mul_assign_by_base(&address_low);
                    gamma_plus_one_plus_address_low_contribution.add_assign_base(&BF::ONE);
                    gamma_plus_one_plus_address_low_contribution.add_assign(&challenges.gamma);
                    register_accesses[i] = RegisterAccess {
                        gamma_plus_one_plus_address_low_contribution,
                        read_timestamp_col: read_timestamp.start() as u32,
                        read_value_col: read_value.start() as u32,
                        maybe_write_value_col: 0,
                        is_write: false,
                    };
                }
                RegisterAccessColumns::WriteAccess {
                    read_timestamp,
                    read_value,
                    write_value,
                    register_index,
                } => {
                    let address_low = BF::from_u64_unchecked(register_index as u64);
                    let mut gamma_plus_one_plus_address_low_contribution =
                        challenges.address_low_challenge.clone();
                    gamma_plus_one_plus_address_low_contribution.mul_assign_by_base(&address_low);
                    gamma_plus_one_plus_address_low_contribution.add_assign_base(&BF::ONE);
                    gamma_plus_one_plus_address_low_contribution.add_assign(&challenges.gamma);
                    register_accesses[i] = RegisterAccess {
                        gamma_plus_one_plus_address_low_contribution,
                        read_timestamp_col: read_timestamp.start() as u32,
                        read_value_col: read_value.start() as u32,
                        maybe_write_value_col: write_value.start() as u32,
                        is_write: true,
                    };
                }
                #[allow(unreachable_patterns)]
                _ => unreachable!("Unexpected RegisterAccessColumns variant"),
            }
            indirect_accesses_per_register_access[i] =
                register_access_columns.indirect_accesses.len() as u32;
            for (j, indirect_access_columns) in
                register_access_columns.indirect_accesses.iter().enumerate()
            {
                match indirect_access_columns {
                    IndirectAccessColumns::ReadAccess {
                        offset,
                        read_timestamp,
                        read_value,
                        address_derivation_carry_bit,
                        ..
                    } => {
                        assert_eq!(j == 0, *offset == 0);
                        indirect_accesses[flat_indirect_idx] = IndirectAccess {
                            offset: *offset,
                            read_timestamp_col: read_timestamp.start() as u32,
                            read_value_col: read_value.start() as u32,
                            maybe_write_value_col: 0,
                            address_derivation_carry_bit_col: address_derivation_carry_bit.start()
                                as u32,
                            address_derivation_carry_bit_num_elements: address_derivation_carry_bit
                                .num_elements()
                                as u32,
                            is_write: false,
                        };
                    }
                    IndirectAccessColumns::WriteAccess {
                        offset,
                        read_timestamp,
                        read_value,
                        write_value,
                        address_derivation_carry_bit,
                        ..
                    } => {
                        assert_eq!(j == 0, *offset == 0);
                        indirect_accesses[flat_indirect_idx] = IndirectAccess {
                            offset: *offset,
                            read_timestamp_col: read_timestamp.start() as u32,
                            read_value_col: read_value.start() as u32,
                            maybe_write_value_col: write_value.start() as u32,
                            address_derivation_carry_bit_col: address_derivation_carry_bit.start()
                                as u32,
                            address_derivation_carry_bit_num_elements: address_derivation_carry_bit
                                .num_elements()
                                as u32,
                            is_write: true,
                        };
                    }
                    #[allow(unreachable_patterns)]
                    _ => unreachable!("Unexpected IndirectAccessColumns variant"),
                }
                flat_indirect_idx += 1;
            }
        }
        Self {
            register_accesses,
            indirect_accesses,
            indirect_accesses_per_register_access,
            num_register_accesses: num_register_accesses as u32,
            write_timestamp_col: write_timestamp_col as u32,
        }
    }
}

impl Default for RegisterAndIndirectAccesses {
    fn default() -> Self {
        Self {
            register_accesses: [RegisterAccess::default(); MAX_REGISTER_ACCESSES],
            indirect_accesses: [IndirectAccess::default(); MAX_INDIRECT_ACCESSES],
            indirect_accesses_per_register_access: [0; MAX_REGISTER_ACCESSES],
            num_register_accesses: 0,
            write_timestamp_col: 0,
        }
    }
}

pub fn print_size<T>(name: &str) -> usize {
    let size = size_of::<T>();
    println!("{}: {}", name, size);
    size
}

pub fn get_grand_product_col(
    circuit: &CompiledCircuitArtifact<BF>,
    cached_data: &ProverCachedData,
) -> usize {
    // Get storage offset for grand product in stage_2_e4_cols
    // It's a little tricky because afaict zksync_airbender regards
    // bf and e4 stage 2 cols as chunks of a unified allocation,
    // and uses raw pointer arithmetic and casts to read some cols as e4.
    // Our case is different: we have a separate allocation for stage_2_e4_cols.
    // We need to translate zksync_airbender's offset in its unified allocation
    // to the offset we need in the separate stage_2_e4_cols allocation.
    // The following code is copied from zksync_airbender's stage4.rs:
    // TODO: this offset may need to change for batched-ram circuits.
    // Now translate zksync_airbender's offset into the offset we need:
    let raw_offset_for_grand_product_poly = circuit
        .stage_2_layout
        .intermediate_polys_for_memory_argument
        .get_range(cached_data.offset_for_grand_product_accumulation_poly)
        .start;
    assert!(raw_offset_for_grand_product_poly >= circuit.stage_2_layout.ext4_polys_offset);
    assert_eq!(raw_offset_for_grand_product_poly % 4, 0);
    assert_eq!(circuit.stage_2_layout.ext4_polys_offset % 4, 0);
    let bf_elems_offset =
        raw_offset_for_grand_product_poly - circuit.stage_2_layout.ext4_polys_offset;
    let stage_2_memory_grand_product_offset = bf_elems_offset / 4;
    stage_2_memory_grand_product_offset
}

#[allow(dead_code)]
pub fn print_sizes() {
    print_size::<LookupChallenges>("LookupChallenges");
    print_size::<RangeCheck16ArgsLayout>("RangeCheck16ArgsLayout");
    print_size::<DelegationChallenges>("DelegationChallenges");
    print_size::<DelegationRequestMetadata>("DelegationRequestMetadata");
    print_size::<DelegationProcessingMetadata>("DelegationProcessingMetadata");
    print_size::<MemoryChallenges>("MemoryChallenges");
    print_size::<FlattenedLookupExpressionsLayout>("FlattenedLookupExpressionsLayout");
    print_size::<FlattenedLookupExpressionsForShuffleRamLayout>(
        "FlattenedLookupExpressionsForShuffleRamLayout",
    );
    print_size::<LazyInitTeardownLayout>("LazyInitTeardownLayout");
    print_size::<ShuffleRamAccess>("ShuffleRamAccess");
    print_size::<ShuffleRamAccesses>("ShuffleRamAccesses");
    print_size::<BatchedRamAccess>("BatchedRamAccess");
    print_size::<BatchedRamAccesses>("BatchedRamAccesses");
    print_size::<RegisterAndIndirectAccesses>("RegisterAndIndirectAccesses");
}
