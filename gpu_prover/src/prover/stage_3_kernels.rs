use super::arg_utils::*;
use crate::device_structures::{
    DeviceMatrixChunk, DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride,
    PtrAndStride,
};
use crate::field::{BaseField, Ext2Field, Ext4Field};
use crate::utils::WARP_SIZE;
use cs::definitions::{
    BoundaryConstraintLocation, LookupExpression, TableIndex, COMMON_TABLE_WIDTH,
    DELEGATION_ARGUMENT_CHALLENGED_IDX_FOR_TIMESTAMP_HIGH,
    DELEGATION_ARGUMENT_CHALLENGED_IDX_FOR_TIMESTAMP_LOW, NUM_LOOKUP_ARGUMENT_KEY_PARTS,
};
use cs::one_row_compiler::{ColumnAddress, CompiledCircuitArtifact};
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use field::{Field, FieldExtension, PrimeField};
use prover::definitions::ExternalValues;
use prover::prover_stages::cached_data::ProverCachedData;
use prover::prover_stages::stage3::AlphaPowersLayout;
use std::alloc::Allocator;
use std::mem::MaybeUninit;

type BF = BaseField;
type E2 = Ext2Field;
type E4 = Ext4Field;

pub const BETA_POWERS_COUNT: usize = 6;

fn stash_coeff(
    coeff: BF,
    coeffs_info: &mut [u8],
    explicit_coeffs: &mut [BF],
    flat_term_idx: &mut usize,
    explicit_coeff_idx: &mut usize,
) {
    if coeff == BF::ONE {
        coeffs_info[*flat_term_idx] = COEFF_IS_ONE;
    } else if coeff == BF::MINUS_ONE {
        coeffs_info[*flat_term_idx] = COEFF_IS_MINUS_ONE;
    } else {
        coeffs_info[*flat_term_idx] = COEFF_IS_EXPLICIT;
        explicit_coeffs[*explicit_coeff_idx] = coeff;
        *explicit_coeff_idx += 1;
    }
    *flat_term_idx += 1;
}

/// These values are hand-picked, so that the biggest circuit (bigint) fits.
/// What is here must match values from stage_3.cu
const MAX_NON_BOOLEAN_CONSTRAINTS: usize = 192;
const MAX_TERMS: usize = 1824;
const MAX_EXPLICIT_COEFFS: usize = 632;
const MAX_FLAT_COL_IDXS: usize = 3488;
const MAX_QUADRATIC_TERMS_PER_CONSTRAINT: usize = 256;
const MAX_LINEAR_TERMS_PER_CONSTRAINT: usize = 256;
const COEFF_IS_ONE: u8 = 0x00;
const COEFF_IS_MINUS_ONE: u8 = 0x01;
const COEFF_IS_EXPLICIT: u8 = 0x02;

// The total size of FlattenedGenericConstraintsMetadata should be <= 8192 B.
// The data is, as long as the compiler gives us a compact layout.
// Clone but not Copy, I'd rather know explicitly when it's being cloned.
#[derive(Clone)]
#[repr(C)]
struct FlattenedGenericConstraintsMetadata {
    pub coeffs_info: [u8; MAX_TERMS],
    pub explicit_coeffs: [BF; MAX_EXPLICIT_COEFFS],
    pub col_idxs: [u16; MAX_FLAT_COL_IDXS],
    pub num_linear_and_quadratic_terms_per_constraint: [[u8; 2]; MAX_NON_BOOLEAN_CONSTRAINTS],
    // TODO: consider making this array for quadratic constraints only.
    // In practice there are relatively few linear constraints so it doesn't make much difference.
    pub decompression_factor: E2,
    pub decompression_factor_squared: E2,
    pub every_row_zerofier: E2,
    pub omega_inv: E2,
    pub current_flat_col_idx: u32,
    pub current_flat_term_idx: u32,
    pub num_boolean_constraints: u32,
    pub num_non_boolean_quadratic_constraints: u32,
    pub num_non_boolean_constraints: u32,
}

impl FlattenedGenericConstraintsMetadata {
    fn stash_column_address(address: &ColumnAddress) -> u16 {
        match address {
            ColumnAddress::WitnessSubtree(col) => *col as u16,
            ColumnAddress::MemorySubtree(col) => (*col as u16) | ColTypeFlags::MEMORY,
            _ => panic!("unexpected ColumnAddress variant"),
        }
    }

    fn compute_every_row_zerofier(decompression_factor_squared: E2) -> E2 {
        let mut zerofier = decompression_factor_squared.clone();
        assert_eq!(zerofier, E2::from_base(BF::MINUS_ONE));
        zerofier.sub_assign_base(&BF::ONE);
        zerofier.inverse().expect("must exist")
    }

    pub fn new(
        circuit: &CompiledCircuitArtifact<BF>,
        alpha_powers: &[E4],
        tau: E2,
        omega_inv: E2,
        domain_size: usize,
        constants_times_challenges: &mut ConstantsTimesChallenges,
    ) -> Self {
        let d1cs = &circuit.degree_1_constraints;
        let d2cs = &circuit.degree_2_constraints;
        let num_degree_2_constraints = d2cs.len();
        let num_degree_1_constraints = d1cs.len();
        let num_quadratic_terms: usize = d2cs.iter().map(|x| x.quadratic_terms.len()).sum();
        let num_boolean_constraints = circuit
            .witness_layout
            .boolean_vars_columns_range
            .num_elements();
        let boolean_constraints_start = circuit.witness_layout.boolean_vars_columns_range.start();
        let num_linear_terms_in_quadratic_constraints: usize =
            d2cs.iter().map(|x| x.linear_terms.len()).sum();
        let num_linear_terms_in_linear_constraints: usize =
            d1cs.iter().map(|x| x.linear_terms.len()).sum();

        let mut coeffs_info = [0 as u8; MAX_TERMS];
        let mut explicit_coeffs = [BF::ZERO; MAX_EXPLICIT_COEFFS];
        let mut col_idxs = [0 as u16; MAX_FLAT_COL_IDXS];
        let mut num_linear_and_quadratic_terms_per_constraint =
            [[0 as u8; 2]; MAX_NON_BOOLEAN_CONSTRAINTS];
        let mut flat_col_idx = 0;
        let mut d2cs_iter = d2cs.iter();
        // Special economized treatment of boolean quadratic constraints
        for i in 0..num_boolean_constraints {
            let constraint = d2cs_iter.next().unwrap();
            // double-check we're actually dealing with a boolean constraint
            assert_eq!(constraint.quadratic_terms.len(), 1);
            assert_eq!(constraint.linear_terms.len(), 1);
            let (coeff, a, b) = constraint.quadratic_terms[0];
            assert_eq!(coeff, BF::ONE);
            assert_eq!(a, b);
            let (coeff, a) = constraint.linear_terms[0];
            assert_eq!(coeff, BF::MINUS_ONE);
            assert_eq!(a, b);
            if let ColumnAddress::WitnessSubtree(col) = a {
                assert_eq!(col, i + boolean_constraints_start);
                col_idxs[flat_col_idx] = col as u16;
            } else {
                panic!("Boolean vars columns should be in witness trace");
            };
            flat_col_idx += 1;
        }
        let mut constraint_idx = 0;
        let mut flat_term_idx = 0;
        let mut explicit_coeff_idx = 0;
        // Non-boolean quadratic constraints
        for _ in num_boolean_constraints..num_degree_2_constraints {
            let constraint = d2cs_iter.next().unwrap();
            let num_quadratic_terms = constraint.quadratic_terms.len();
            assert!(num_quadratic_terms < MAX_QUADRATIC_TERMS_PER_CONSTRAINT);
            for (coeff, a, b) in constraint.quadratic_terms.iter() {
                stash_coeff(
                    *coeff,
                    &mut coeffs_info,
                    &mut explicit_coeffs,
                    &mut flat_term_idx,
                    &mut explicit_coeff_idx,
                );
                col_idxs[flat_col_idx] = Self::stash_column_address(a);
                flat_col_idx += 1;
                col_idxs[flat_col_idx] = Self::stash_column_address(b);
                flat_col_idx += 1;
            }
            let num_quadratic_terms = u8::try_from(num_quadratic_terms).unwrap();
            let num_linear_terms = constraint.linear_terms.len();
            assert!(num_linear_terms < MAX_LINEAR_TERMS_PER_CONSTRAINT);
            for (coeff, a) in constraint.linear_terms.iter() {
                stash_coeff(
                    *coeff,
                    &mut coeffs_info,
                    &mut explicit_coeffs,
                    &mut flat_term_idx,
                    &mut explicit_coeff_idx,
                );
                col_idxs[flat_col_idx] = Self::stash_column_address(a);
                flat_col_idx += 1;
            }
            let num_linear_terms = u8::try_from(num_linear_terms).unwrap();
            num_linear_and_quadratic_terms_per_constraint[constraint_idx] =
                [num_quadratic_terms, num_linear_terms];
            let mut constant_times_challenge =
                alpha_powers[constraint_idx + num_boolean_constraints];
            constant_times_challenge.mul_assign_by_base(&constraint.constant_term);
            constants_times_challenges
                .sum
                .add_assign(&constant_times_challenge);
            constraint_idx += 1;
        }
        assert_eq!(d2cs_iter.next(), None);
        for constraint in d1cs.iter() {
            let num_linear_terms = constraint.linear_terms.len();
            assert!(num_linear_terms < MAX_LINEAR_TERMS_PER_CONSTRAINT);
            for (coeff, a) in constraint.linear_terms.iter() {
                stash_coeff(
                    *coeff,
                    &mut coeffs_info,
                    &mut explicit_coeffs,
                    &mut flat_term_idx,
                    &mut explicit_coeff_idx,
                );
                col_idxs[flat_col_idx] = Self::stash_column_address(a);
                flat_col_idx += 1;
            }
            let num_linear_terms = u8::try_from(num_linear_terms).unwrap();
            num_linear_and_quadratic_terms_per_constraint[constraint_idx] =
                [0 as u8, num_linear_terms];
            let mut constant_times_challenge =
                alpha_powers[constraint_idx + num_boolean_constraints];
            constant_times_challenge.mul_assign_by_base(&constraint.constant_term);
            constants_times_challenges
                .sum
                .add_assign(&constant_times_challenge);
            constraint_idx += 1;
        }

        // double-check that we accounted for all constraints, terms, and cols
        assert_eq!(
            constraint_idx,
            num_degree_2_constraints + num_degree_1_constraints - num_boolean_constraints,
        );
        // we skipped the boolean constraints when incrementing flat_term_idx
        assert_eq!(
            flat_term_idx + 2 * num_boolean_constraints,
            num_quadratic_terms
                + num_linear_terms_in_quadratic_constraints
                + num_linear_terms_in_linear_constraints,
        );
        // Boolean constraints pack 3 col idxs into 1 effective col idx
        assert_eq!(
            flat_col_idx + 2 * num_boolean_constraints,
            2 * num_quadratic_terms
                + num_linear_terms_in_quadratic_constraints
                + num_linear_terms_in_linear_constraints,
        );
        let decompression_factor = tau.pow((domain_size / 2) as u32);
        let decompression_factor_squared = *decompression_factor.clone().square();
        let every_row_zerofier = Self::compute_every_row_zerofier(decompression_factor_squared);
        Self {
            coeffs_info,
            explicit_coeffs,
            col_idxs,
            num_linear_and_quadratic_terms_per_constraint,
            decompression_factor,
            decompression_factor_squared,
            every_row_zerofier,
            omega_inv,
            current_flat_col_idx: flat_col_idx as u32,
            current_flat_term_idx: flat_term_idx as u32,
            num_boolean_constraints: num_boolean_constraints as u32,
            num_non_boolean_quadratic_constraints: (num_degree_2_constraints
                - num_boolean_constraints)
                as u32,
            num_non_boolean_constraints: (num_degree_2_constraints + num_degree_1_constraints
                - num_boolean_constraints) as u32,
        }
    }
}

cuda_kernel!(
    GenericConstraints,
    generic_constraints,
    metadata: FlattenedGenericConstraintsMetadata,
    witness_cols: PtrAndStride<BF>,
    memory_cols: PtrAndStride<BF>,
    alpha_powers: *const E4,
    quotient: MutPtrAndStride<BF>,
    log_n: u32,
);

generic_constraints!(generic_constraints_kernel);

pub(super) const MAX_HELPER_VALUES: usize = 1536;

// A width 3 lookup is a tuple of 3 values.
// We're on the coset domain, so I don't think we can get any free lunches
// using precomputed denom tables.

const LOOKUP_VAL_IS_COL_FLAG: u8 = u8::MAX;

#[derive(Clone)]
#[repr(C)]
struct Width3LookupsLayout<
    const MAX_WIDTH_3_LOOKUPS: usize,
    const MAX_WIDTH_3_LOOKUP_VALS: usize,
    const MAX_WIDTH_3_LOOKUP_COEFFS: usize,
    const MAX_TERMS_PER_EXPRESSION: usize,
    const MAX_WIDTH_3_LOOKUP_COLS: usize,
> {
    coeffs: [u32; MAX_WIDTH_3_LOOKUP_COEFFS],
    col_idxs: [u16; MAX_WIDTH_3_LOOKUP_COLS],
    num_terms_per_expression: [u8; MAX_WIDTH_3_LOOKUP_VALS],
    table_id_is_col: [bool; MAX_WIDTH_3_LOOKUPS],
    e4_arg_cols: [u16; MAX_WIDTH_3_LOOKUPS],
    helpers_offset: u32,
    num_helpers_used: u32,
    num_lookups: u32,
    e4_arg_cols_start: u32,
}

impl<
        const MAX_WIDTH_3_LOOKUPS: usize,
        const MAX_WIDTH_3_LOOKUP_VALS: usize,
        const MAX_WIDTH_3_LOOKUP_COEFFS: usize,
        const MAX_TERMS_PER_EXPRESSION: usize,
        const MAX_WIDTH_3_LOOKUP_COLS: usize,
    >
    Width3LookupsLayout<
        MAX_WIDTH_3_LOOKUPS,
        MAX_WIDTH_3_LOOKUP_VALS,
        MAX_WIDTH_3_LOOKUP_COEFFS,
        MAX_TERMS_PER_EXPRESSION,
        MAX_WIDTH_3_LOOKUP_COLS,
    >
{
    pub fn new<F: Fn(usize) -> usize>(
        circuit: &CompiledCircuitArtifact<BF>,
        lookup_challenges: &[E4],
        lookup_gamma: E4,
        alphas: &[E4],
        alphas_offset: &mut usize,
        helpers: &mut Vec<E4, impl Allocator>,
        decompression_factor_inv: E2,
        constants_times_challenges: &mut ConstantsTimesChallenges,
        translate_e4_offset: &F,
    ) -> Self {
        assert_eq!(COMMON_TABLE_WIDTH, 3);
        let mut coeffs = [0 as u32; MAX_WIDTH_3_LOOKUP_COEFFS];
        let mut col_idxs = [0 as u16; MAX_WIDTH_3_LOOKUP_COLS];
        let mut num_terms_per_expression = [0 as u8; MAX_WIDTH_3_LOOKUP_VALS];
        let mut table_id_is_col = [false; MAX_WIDTH_3_LOOKUPS];
        let mut e4_arg_cols = [0; MAX_WIDTH_3_LOOKUPS];
        let mut val_idx: usize = 0;
        let mut col_idx: usize = 0;
        let mut coeff_idx: usize = 0;
        let table_id_challenge = lookup_challenges[NUM_LOOKUP_ARGUMENT_KEY_PARTS - 2];
        let mut val_challenges = Vec::with_capacity(NUM_LOOKUP_ARGUMENT_KEY_PARTS - 1);
        val_challenges.push(E4::ONE);
        val_challenges
            .append(&mut (&lookup_challenges[0..(NUM_LOOKUP_ARGUMENT_KEY_PARTS - 2)]).to_vec());
        let num_lookups = circuit.witness_layout.width_3_lookups.len();
        assert!(num_lookups > 0);
        assert_eq!(
            num_lookups,
            circuit
                .stage_2_layout
                .intermediate_polys_for_generic_lookup
                .num_elements()
        );
        let helpers_offset = helpers.len();
        for (term_idx, lookup_set) in circuit.witness_layout.width_3_lookups.iter().enumerate() {
            let e4_arg_col = translate_e4_offset(
                circuit
                    .stage_2_layout
                    .intermediate_polys_for_generic_lookup
                    .get_range(term_idx)
                    .start,
            );
            e4_arg_cols[term_idx] = u16::try_from(e4_arg_col).unwrap();
            let alpha = alphas[*alphas_offset];
            *alphas_offset += 1;
            match lookup_set.table_index {
                TableIndex::Constant(table_type) => {
                    let id = BF::from_u64_unchecked(table_type.to_table_id() as u64);
                    helpers.push(
                        *table_id_challenge
                            .clone()
                            .mul_assign_by_base(&id)
                            .add_assign(&lookup_gamma)
                            .mul_assign_by_base(&decompression_factor_inv)
                            .mul_assign(&alpha),
                    );
                }
                TableIndex::Variable(place) => {
                    table_id_is_col[term_idx] = true;
                    col_idxs[col_idx] = match place {
                        ColumnAddress::WitnessSubtree(col) => col as u16,
                        _ => panic!("unexpected ColumnAddress variant"),
                    };
                    col_idx += 1;
                    helpers.push(
                        *alpha
                            .clone()
                            .mul_assign(&lookup_gamma)
                            .mul_assign_by_base(&decompression_factor_inv),
                    );
                    helpers.push(*alpha.clone().mul_assign(&table_id_challenge));
                }
            }
            let mut lookup_is_empty = true;
            for (val, val_challenge) in lookup_set.input_columns.iter().zip(val_challenges.iter()) {
                match val {
                    LookupExpression::Variable(place) => {
                        lookup_is_empty = false;
                        helpers.push(*alpha.clone().mul_assign(&val_challenge));
                        col_idxs[col_idx] = match place {
                            ColumnAddress::WitnessSubtree(col) => *col as u16,
                            ColumnAddress::MemorySubtree(col) => {
                                (*col as u16) | ColTypeFlags::MEMORY
                            }
                            _ => panic!("unexpected ColumnAddress variant"),
                        };
                        col_idx += 1;
                        num_terms_per_expression[val_idx] = LOOKUP_VAL_IS_COL_FLAG;
                        val_idx += 1;
                    }
                    LookupExpression::Expression(a) => {
                        let num_terms = a.linear_terms.len();
                        if num_terms > 0 {
                            lookup_is_empty = false;
                            helpers.push(*alpha.clone().mul_assign(&val_challenge));
                        }
                        assert_eq!(a.constant_term, BF::ZERO);
                        assert!(num_terms <= MAX_TERMS_PER_EXPRESSION);
                        num_terms_per_expression[val_idx] = u8::try_from(num_terms).unwrap();
                        for (coeff, column_address) in a.linear_terms.iter() {
                            coeffs[coeff_idx] = coeff.0;
                            col_idxs[col_idx] = match column_address {
                                ColumnAddress::WitnessSubtree(col) => *col as u16,
                                ColumnAddress::MemorySubtree(col) => {
                                    (*col as u16) | ColTypeFlags::MEMORY
                                }
                                _ => panic!("unexpected ColumnAddress variant"),
                            };
                            coeff_idx += 1;
                            col_idx += 1;
                        }
                        val_idx += 1;
                    }
                };
            }
            assert!(!lookup_is_empty);
            constants_times_challenges.sum.sub_assign(&alpha);
        }
        let e4_arg_cols_start = translate_e4_offset(
            circuit
                .stage_2_layout
                .intermediate_polys_for_generic_lookup
                .start(),
        );
        assert_eq!(e4_arg_cols_start, e4_arg_cols[0] as usize);
        let num_helpers_used = helpers.len() - helpers_offset;
        Self {
            coeffs,
            col_idxs,
            num_terms_per_expression,
            table_id_is_col,
            e4_arg_cols,
            helpers_offset: helpers_offset as u32,
            num_helpers_used: num_helpers_used as u32,
            num_lookups: num_lookups as u32,
            e4_arg_cols_start: e4_arg_cols_start as u32,
        }
    }
}

const DELEGATED_MAX_WIDTH_3_LOOKUPS: usize = 224;
const DELEGATED_MAX_WIDTH_3_LOOKUP_VALS: usize = 640;
const DELEGATED_MAX_WIDTH_3_LOOKUP_COEFFS: usize = 1408;
const DELEGATED_MAX_TERMS_PER_EXPRESSION: usize = 32;
const DELEGATED_MAX_WIDTH_3_LOOKUP_COLS: usize = 1888;

const NON_DELEGATED_MAX_WIDTH_3_LOOKUPS: usize = 24;
const NON_DELEGATED_MAX_WIDTH_3_LOOKUP_VALS: usize = 72;
const NON_DELEGATED_MAX_WIDTH_3_LOOKUP_COEFFS: usize = 32;
const NON_DELEGATED_MAX_TERMS_PER_EXPRESSION: usize = 32;
const NON_DELEGATED_MAX_WIDTH_3_LOOKUP_COLS: usize = 96;

type DelegatedWidth3LookupsLayout = Width3LookupsLayout<
    DELEGATED_MAX_WIDTH_3_LOOKUPS,
    DELEGATED_MAX_WIDTH_3_LOOKUP_VALS,
    DELEGATED_MAX_WIDTH_3_LOOKUP_COEFFS,
    DELEGATED_MAX_TERMS_PER_EXPRESSION,
    DELEGATED_MAX_WIDTH_3_LOOKUP_COLS,
>;

impl Default for DelegatedWidth3LookupsLayout {
    fn default() -> Self {
        Self {
            coeffs: [0 as u32; DELEGATED_MAX_WIDTH_3_LOOKUP_COEFFS],
            col_idxs: [0 as u16; DELEGATED_MAX_WIDTH_3_LOOKUP_COLS],
            num_terms_per_expression: [0 as u8; DELEGATED_MAX_WIDTH_3_LOOKUP_VALS],
            table_id_is_col: [false; DELEGATED_MAX_WIDTH_3_LOOKUPS],
            e4_arg_cols: [0; DELEGATED_MAX_WIDTH_3_LOOKUPS],
            helpers_offset: 0,
            num_helpers_used: 0,
            num_lookups: 0,
            e4_arg_cols_start: 0,
        }
    }
}

type NonDelegatedWidth3LookupsLayout = Width3LookupsLayout<
    NON_DELEGATED_MAX_WIDTH_3_LOOKUPS,
    NON_DELEGATED_MAX_WIDTH_3_LOOKUP_VALS,
    NON_DELEGATED_MAX_WIDTH_3_LOOKUP_COEFFS,
    NON_DELEGATED_MAX_TERMS_PER_EXPRESSION,
    NON_DELEGATED_MAX_WIDTH_3_LOOKUP_COLS,
>;

impl NonDelegatedWidth3LookupsLayout {
    pub fn new_placeholder(
        num_helpers_used: u32,
        num_lookups: u32,
        e4_arg_cols_start: u32,
    ) -> Self {
        Self {
            coeffs: [0 as u32; NON_DELEGATED_MAX_WIDTH_3_LOOKUP_COEFFS],
            col_idxs: [0 as u16; NON_DELEGATED_MAX_WIDTH_3_LOOKUP_COLS],
            num_terms_per_expression: [0 as u8; NON_DELEGATED_MAX_WIDTH_3_LOOKUP_VALS],
            table_id_is_col: [false; NON_DELEGATED_MAX_WIDTH_3_LOOKUPS],
            e4_arg_cols: [0; NON_DELEGATED_MAX_WIDTH_3_LOOKUPS],
            helpers_offset: 0,
            num_helpers_used,
            num_lookups,
            e4_arg_cols_start,
        }
    }
}

impl Default for NonDelegatedWidth3LookupsLayout {
    fn default() -> Self {
        Self {
            coeffs: [0 as u32; NON_DELEGATED_MAX_WIDTH_3_LOOKUP_COEFFS],
            col_idxs: [0 as u16; NON_DELEGATED_MAX_WIDTH_3_LOOKUP_COLS],
            num_terms_per_expression: [0 as u8; NON_DELEGATED_MAX_WIDTH_3_LOOKUP_VALS],
            table_id_is_col: [false; NON_DELEGATED_MAX_WIDTH_3_LOOKUPS],
            e4_arg_cols: [0; NON_DELEGATED_MAX_WIDTH_3_LOOKUPS],
            helpers_offset: 0,
            num_helpers_used: 0,
            num_lookups: 0,
            e4_arg_cols_start: 0,
        }
    }
}

// these need their own kernel because the metadata struct is almost 8KB
cuda_kernel!(
    DelegatedWidth3Lookups,
    delegated_width_3_lookups,
    layout: DelegatedWidth3LookupsLayout,
    witness_cols: PtrAndStride<BF>,
    memory_cols: PtrAndStride<BF>,
    stage_2_e4_cols: PtrAndStride<BF>,
    e4_helpers: *const E4,
    quotient: MutPtrAndStride<BF>,
    decompression_factor_squared: E2,
    log_n: u32,
);

delegated_width_3_lookups!(delegated_width_3_lookups_kernel);

#[derive(Clone)]
#[repr(C)]
struct MultiplicitiesLayout {
    pub src_cols_start: u32,
    pub dst_cols_start: u32,
    pub setup_cols_start: u32,
    pub num_dst_cols: u32,
}

impl MultiplicitiesLayout {
    pub fn new<F: Fn(usize) -> usize>(
        src_cols_start: usize,
        dst_cols_start: usize,
        setup_cols_start: usize,
        num_dst_cols: usize,
        entry_width: usize,
        lookup_challenges: &LookupChallenges,
        alphas: &[E4],
        alpha_offset: &mut usize,
        helpers: &mut Vec<E4, impl Allocator>,
        decompression_factor_inv: E2,
        translate_e4_offset: &F,
    ) -> Self {
        for _ in 0..num_dst_cols {
            let alpha = alphas[*alpha_offset];
            *alpha_offset = *alpha_offset + 1;
            helpers.push(
                *alpha
                    .clone()
                    .mul_assign(&lookup_challenges.gamma)
                    .mul_assign_by_base(&decompression_factor_inv),
            );
            for j in 0..entry_width - 1 {
                helpers.push(
                    *alpha
                        .clone()
                        .mul_assign(&lookup_challenges.linearization_challenges[j]),
                );
            }
        }
        Self {
            src_cols_start: src_cols_start as u32,
            dst_cols_start: translate_e4_offset(dst_cols_start) as u32,
            setup_cols_start: setup_cols_start as u32,
            num_dst_cols: num_dst_cols as u32,
        }
    }
}

const MAX_STATE_LINKAGE_CONSTRAINTS: usize = 2;

#[derive(Clone)]
#[repr(C)]
struct StateLinkageConstraints {
    pub srcs: [u32; MAX_STATE_LINKAGE_CONSTRAINTS],
    pub dsts: [u32; MAX_STATE_LINKAGE_CONSTRAINTS],
    num_constraints: u32,
}

impl StateLinkageConstraints {
    pub fn new(circuit: &CompiledCircuitArtifact<BF>) -> Self {
        let num_constraints = circuit.state_linkage_constraints.len();
        assert!(num_constraints <= MAX_STATE_LINKAGE_CONSTRAINTS);
        let mut srcs = [0; MAX_STATE_LINKAGE_CONSTRAINTS];
        let mut dsts = [0; MAX_STATE_LINKAGE_CONSTRAINTS];
        for (i, (src, dst)) in circuit.state_linkage_constraints.iter().enumerate() {
            let ColumnAddress::WitnessSubtree(col) = *src else {
                panic!()
            };
            srcs[i] = col as u32;
            let ColumnAddress::WitnessSubtree(col) = *dst else {
                panic!()
            };
            dsts[i] = col as u32;
        }
        Self {
            srcs,
            dsts,
            num_constraints: num_constraints as u32,
        }
    }
}

const MAX_BOUNDARY_CONSTRAINTS_FIRST_ROW: usize = 8;
const MAX_BOUNDARY_CONSTRAINTS_ONE_BEFORE_LAST_ROW: usize = 8;

#[derive(Clone)]
#[repr(C)]
struct BoundaryConstraints {
    first_row_cols: [u32; MAX_BOUNDARY_CONSTRAINTS_FIRST_ROW],
    one_before_last_row_cols: [u32; MAX_BOUNDARY_CONSTRAINTS_ONE_BEFORE_LAST_ROW],
    num_first_row: u32,
    num_one_before_last_row: u32,
}

#[derive(Clone, Default)]
#[repr(C)]
pub(super) struct ConstantsTimesChallenges {
    first_row: E4,
    one_before_last_row: E4,
    sum: E4,
}

impl BoundaryConstraints {
    fn unpack_public_input_column_address(column_address: ColumnAddress) -> u32 {
        if let ColumnAddress::WitnessSubtree(col) = column_address {
            col as u32
        } else {
            panic!("public inputs should be in witness")
        }
    }

    pub fn new(
        circuit: &CompiledCircuitArtifact<BF>,
        external_values: &ExternalValues,
        public_inputs: &[BF],
        process_shuffle_ram_init: bool,
        lazy_init_address_start: usize, // in memory cols. The kernel knows.
        lazy_teardown_value_start: usize, // in memory cols
        lazy_teardown_timestamp_start: usize, // in memory cols
        alphas_first_row: &[E4],
        alphas_one_before_last_row: &[E4],
        helpers: &mut Vec<E4, impl Allocator>,
        beta_powers: &[E4],
        decompression_factor: E2,
        constants_times_challenges: &mut ConstantsTimesChallenges,
    ) -> Self {
        let mut first_row_cols = [0; MAX_BOUNDARY_CONSTRAINTS_FIRST_ROW];
        let mut one_before_last_row_cols = [0; MAX_BOUNDARY_CONSTRAINTS_ONE_BEFORE_LAST_ROW];
        constants_times_challenges.first_row = E4::ZERO;
        constants_times_challenges.one_before_last_row = E4::ZERO;
        let mut num_first_row = 0;
        let mut num_one_before_last_row = 0;
        let mut helpers_first_row = Vec::with_capacity(MAX_BOUNDARY_CONSTRAINTS_FIRST_ROW);
        let mut helpers_one_before_last_row =
            Vec::with_capacity(MAX_BOUNDARY_CONSTRAINTS_ONE_BEFORE_LAST_ROW);
        if process_shuffle_ram_init {
            let beta_power = beta_powers[3];
            let mut stash_limb_pair = |start_col: usize, vals: &[BF]| {
                for i in 0..=1 {
                    let mut alpha = alphas_first_row[num_first_row];
                    alpha.mul_assign(&beta_power);
                    helpers_first_row
                        .push(*alpha.clone().mul_assign_by_base(&decompression_factor));
                    first_row_cols[num_first_row] = (start_col + i) as u32;
                    constants_times_challenges
                        .first_row
                        .sub_assign(alpha.mul_assign_by_base(&vals[i]));
                    num_first_row += 1;
                }
            };
            stash_limb_pair(
                lazy_init_address_start,
                &external_values.aux_boundary_values.lazy_init_first_row[..],
            );
            stash_limb_pair(
                lazy_teardown_value_start,
                &external_values.aux_boundary_values.teardown_value_first_row[..],
            );
            stash_limb_pair(
                lazy_teardown_timestamp_start,
                &external_values
                    .aux_boundary_values
                    .teardown_timestamp_first_row[..],
            );
            let beta_power = beta_powers[2];
            let mut stash_limb_pair = |start_col: usize, vals: &[BF]| {
                for i in 0..=1 {
                    let mut alpha = alphas_one_before_last_row[num_one_before_last_row];
                    alpha.mul_assign(&beta_power);
                    helpers_one_before_last_row
                        .push(*alpha.clone().mul_assign_by_base(&decompression_factor));
                    one_before_last_row_cols[num_one_before_last_row] = (start_col + i) as u32;
                    constants_times_challenges
                        .one_before_last_row
                        .sub_assign(alpha.mul_assign_by_base(&vals[i]));
                    num_one_before_last_row += 1;
                }
            };
            stash_limb_pair(
                lazy_init_address_start,
                &external_values
                    .aux_boundary_values
                    .lazy_init_one_before_last_row[..],
            );
            stash_limb_pair(
                lazy_teardown_value_start,
                &external_values
                    .aux_boundary_values
                    .teardown_value_one_before_last_row[..],
            );
            stash_limb_pair(
                lazy_teardown_timestamp_start,
                &external_values
                    .aux_boundary_values
                    .teardown_timestamp_one_before_last_row[..],
            );
        }
        for ((location, column_address), val) in
            circuit.public_inputs.iter().zip(public_inputs.iter())
        {
            match location {
                BoundaryConstraintLocation::FirstRow => {
                    first_row_cols[num_first_row] =
                        Self::unpack_public_input_column_address(*column_address);
                    let beta_power = beta_powers[3];
                    let mut alpha = alphas_first_row[num_first_row];
                    alpha.mul_assign(&beta_power);
                    helpers_first_row
                        .push(*alpha.clone().mul_assign_by_base(&decompression_factor));
                    constants_times_challenges
                        .first_row
                        .sub_assign(alpha.clone().mul_assign_by_base(val));
                    num_first_row += 1;
                }
                BoundaryConstraintLocation::OneBeforeLastRow => {
                    one_before_last_row_cols[num_one_before_last_row] =
                        Self::unpack_public_input_column_address(*column_address);
                    let beta_power = beta_powers[2];
                    let mut alpha = alphas_one_before_last_row[num_one_before_last_row];
                    alpha.mul_assign(&beta_power);
                    helpers_one_before_last_row
                        .push(*alpha.clone().mul_assign_by_base(&decompression_factor));
                    constants_times_challenges
                        .one_before_last_row
                        .sub_assign(alpha.mul_assign_by_base(val));
                    num_one_before_last_row += 1;
                }
                BoundaryConstraintLocation::LastRow => {
                    panic!("public inputs on the last row are not supported");
                }
            }
        }
        // account for memory accumulator, which requires a first row constraint
        let mut alpha = alphas_first_row[num_first_row];
        alpha.mul_assign(&beta_powers[3]);
        let grand_product_helper = *alpha.clone().mul_assign_by_base(&decompression_factor);
        constants_times_challenges.first_row.sub_assign(&alpha);
        // pushing grand product helper first is a bit more convenient for the kernel
        helpers.push(grand_product_helper);
        helpers.extend_from_slice(&helpers_first_row);
        helpers.extend_from_slice(&helpers_one_before_last_row);
        assert!(num_first_row <= MAX_BOUNDARY_CONSTRAINTS_FIRST_ROW);
        assert!(num_one_before_last_row <= MAX_BOUNDARY_CONSTRAINTS_ONE_BEFORE_LAST_ROW);
        Self {
            first_row_cols,
            one_before_last_row_cols,
            num_first_row: num_first_row as u32,
            num_one_before_last_row: num_first_row as u32,
        }
    }
}

// TODO:
// Maybe the generally optimal way to express and evaluate constraints is:
//  - Each term may be quadratic or linear.
//  - Each term component may be a col or an expression.
//    - each expression may or may not have a constant term
//  - Each term may or may not have an E4 coeff.
//  - Constant terms * challenges are folded into a global sum.
//  - Per-constraint challenges are folded into E4 coeffs and stashed in the helper array.
// Even with this format, we'd need substantial hardcoded CPU logic to pack each constraint.
cuda_kernel!(
    HardcodedConstraints,
    hardcoded_constraints,
    setup_cols: PtrAndStride<BF>,
    witness_cols: PtrAndStride<BF>,
    memory_cols: PtrAndStride<BF>,
    stage_2_bf_cols: PtrAndStride<BF>,
    stage_2_e4_cols: PtrAndStride<BF>,
    process_delegations: bool,
    handle_delegation_requests: bool,
    delegation_aux_poly_col: u32,
    delegation_challenges: DelegationChallenges,
    delegation_processing_metadata: DelegationProcessingMetadata,
    delegation_request_metadata: DelegationRequestMetadata,
    memory_args_start: u32,
    memory_grand_product_col: u32,
    lazy_init_teardown_layout: LazyInitTeardownLayout,
    shuffle_ram_accesses: ShuffleRamAccesses,
    process_batch_ram_access: bool,
    batched_ram_accesses: BatchedRamAccesses,
    process_registers_and_indirect_access: bool,
    register_and_indirect_accesses: RegisterAndIndirectAccesses,
    range_check_16_layout: RangeCheck16ArgsLayout,
    expressions_layout: FlattenedLookupExpressionsLayout,
    expressions_for_shuffle_ram_layout: FlattenedLookupExpressionsForShuffleRamLayout,
    width_3_lookups_layout: NonDelegatedWidth3LookupsLayout,
    range_check_16_multiplicities_layout: MultiplicitiesLayout,
    timestamp_range_check_multiplicities_layout: MultiplicitiesLayout,
    generic_lookup_multiplicities_layout: MultiplicitiesLayout,
    state_linkage_constraints: StateLinkageConstraints,
    boundary_constraints: BoundaryConstraints,
    alpha_powers: *const E4,
    alpha_powers_every_row_except_last_two: *const E4,
    beta_powers: *const E4,
    e4_helpers: *const E4,
    constants_times_challenges_sum: *const ConstantsTimesChallenges,
    quotient: MutPtrAndStride<BF>,
    memory_timestamp_high_from_circuit_idx: BF,
    decompression_factor: E2,
    decompression_factor_squared: E2,
    every_row_zerofier: E2,
    omega_inv: E2,
    omega_inv_squared: E2,
    log_n: u32,
);

hardcoded_constraints!(hardcoded_constraints_kernel);

pub struct Metadata {
    alpha_powers_layout: AlphaPowersLayout,
    flat_generic_constraints_metadata: FlattenedGenericConstraintsMetadata,
    delegated_width_3_lookups_layout: DelegatedWidth3LookupsLayout,
    non_delegated_width_3_lookups_layout: NonDelegatedWidth3LookupsLayout,
    range_check_16_layout: RangeCheck16ArgsLayout,
    expressions_layout: FlattenedLookupExpressionsLayout,
    expressions_for_shuffle_ram_layout: FlattenedLookupExpressionsForShuffleRamLayout,
    generic_lookup_multiplicities_layout: MultiplicitiesLayout,
    state_linkage_constraints: StateLinkageConstraints,
    boundary_constraints: BoundaryConstraints,
    memory_args_start: usize,
    memory_grand_product_col: usize,
    lazy_init_teardown_layout: LazyInitTeardownLayout,
    shuffle_ram_accesses: ShuffleRamAccesses,
    batched_ram_accesses: BatchedRamAccesses,
    range_check_16_multiplicities_layout: MultiplicitiesLayout,
    timestamp_range_check_multiplicities_layout: MultiplicitiesLayout,
    delegation_aux_poly_col: usize,
    num_generic_constraints: usize,
    delegation_challenges: DelegationChallenges,
    delegation_processing_metadata: DelegationProcessingMetadata,
    delegation_request_metadata: DelegationRequestMetadata,
    register_and_indirect_accesses: RegisterAndIndirectAccesses,
}

impl Metadata {
    pub(crate) fn new(
        h_alpha_powers: &[E4],
        h_beta_powers: &[E4],
        tau: E2,
        omega: E2,
        omega_inv: E2,
        lookup_challenges: &LookupChallenges,
        cached_data: &ProverCachedData,
        circuit: &CompiledCircuitArtifact<BF>,
        external_values: &ExternalValues,
        public_inputs: &[BF],
        grand_product_accumulator: E4,
        sum_over_delegation_poly: E4,
        log_n: u32,
        helpers: &mut Vec<E4, impl Allocator>,
        constants_times_challenges: &mut ConstantsTimesChallenges,
    ) -> Metadata {
        let n = 1 << log_n;
        let num_stage_2_bf_cols = circuit.stage_2_layout.num_base_field_polys();
        let num_stage_2_e4_cols = circuit.stage_2_layout.num_ext4_field_polys();
        let e4_cols_offset = circuit.stage_2_layout.ext4_polys_offset;
        assert_eq!(e4_cols_offset % 4, 0);
        assert!(num_stage_2_bf_cols <= e4_cols_offset);
        assert!(e4_cols_offset - num_stage_2_bf_cols < 4);
        let alpha_powers_layout =
            AlphaPowersLayout::new(&circuit, cached_data.num_stage_3_quotient_terms);
        let ProverCachedData {
            trace_len,
            memory_timestamp_high_from_circuit_idx,
            delegation_type: _,
            memory_argument_challenges,
            execute_delegation_argument: _,
            delegation_challenges,
            process_shuffle_ram_init,
            shuffle_ram_inits_and_teardowns,
            lazy_init_address_range_check_16,
            handle_delegation_requests,
            delegation_request_layout: _,
            process_batch_ram_access,
            process_registers_and_indirect_access,
            delegation_processor_layout,
            process_delegations,
            delegation_processing_aux_poly,
            num_set_polys_for_memory_shuffle,
            offset_for_grand_product_accumulation_poly,
            range_check_16_multiplicities_src,
            range_check_16_multiplicities_dst,
            range_check_16_setup_column,
            timestamp_range_check_multiplicities_src,
            timestamp_range_check_multiplicities_dst,
            timestamp_range_check_setup_column,
            generic_lookup_multiplicities_src_start,
            generic_lookup_multiplicities_dst_start,
            generic_lookup_setup_columns_start,
            range_check_16_width_1_lookups_access,
            range_check_16_width_1_lookups_access_via_expressions,
            timestamp_range_check_width_1_lookups_access_via_expressions,
            timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram,
            memory_accumulator_dst_start,
            ..
        } = cached_data.clone();

        // println!(
        //     "memory_timestamp_high_from_circuit_idx {}",
        //     memory_timestamp_high_from_circuit_idx
        // );

        assert_eq!(trace_len, n);

        // We keep references to host AND device copies of challenge powers,
        // because host copies come in handy to precompute challenges_times_powers_sum
        // and other helper values.
        let AlphaPowersLayout {
            num_quotient_terms_every_row_except_last,
            num_quotient_terms_every_row_except_last_two,
            num_quotient_terms_first_row,
            num_quotient_terms_one_before_last_row,
            num_quotient_terms_last_row,
            num_quotient_terms_last_row_and_at_zero,
            precomputation_size,
        } = alpha_powers_layout;
        assert_eq!(h_alpha_powers.len(), precomputation_size);
        let h_alphas_for_every_row_except_last =
            &h_alpha_powers[(precomputation_size - num_quotient_terms_every_row_except_last)..];
        let h_alphas_for_every_row_except_last_two =
            &h_alpha_powers[(precomputation_size - num_quotient_terms_every_row_except_last_two)..];
        let h_alphas_for_first_row =
            &h_alpha_powers[(precomputation_size - num_quotient_terms_first_row)..];
        // let d_alphas_for_first_row = &d_alphas[(precomputation_size - num_quotient_terms_first_row)..];
        let h_alphas_for_one_before_last_row =
            &h_alpha_powers[(precomputation_size - num_quotient_terms_one_before_last_row)..];
        // let d_alphas_for_one_before_last_row =
        //     &d_alphas[(precomputation_size - num_quotient_terms_one_before_last_row)..];
        let h_alphas_for_last_row =
            &h_alpha_powers[(precomputation_size - num_quotient_terms_last_row)..];
        // let d_alphas_for_last_row = &d_alphas[(precomputation_size - num_quotient_terms_last_row)..];
        let h_alphas_for_last_row_and_at_zero =
            &h_alpha_powers[(precomputation_size - num_quotient_terms_last_row_and_at_zero)..];
        // let d_alphas_for_last_row_and_at_zero =
        //     &d_alphas[(precomputation_size - num_quotient_terms_last_row_and_at_zero)..];
        // Generic constraints
        let num_generic_constraints =
            circuit.degree_2_constraints.len() + circuit.degree_1_constraints.len();
        let (h_alphas_for_generic_constraints, h_alphas_for_hardcoded_every_row_except_last) =
            h_alphas_for_every_row_except_last.split_at(num_generic_constraints);
        constants_times_challenges.sum = E4::ZERO;
        let flat_generic_constraints_metadata = FlattenedGenericConstraintsMetadata::new(
            circuit,
            h_alphas_for_generic_constraints,
            tau,
            omega_inv,
            n,
            constants_times_challenges,
        );
        // Hardcoded constraints
        // TODO: Many metadata structs shared with stage2.rs have been deduplicated and placed in arg_utils,
        // but there's still a substantial amount of partially-duplicated code surrounding their construction.
        // Once everything is working, figure out how much more can be deduplicated.
        let translate_e4_offset = |raw_col: usize| -> usize {
            assert_eq!(raw_col % 4, 0);
            assert!(raw_col >= e4_cols_offset);
            (raw_col - e4_cols_offset) / 4
        };
        let num_range_check_16_multiplicities_cols = circuit
            .witness_layout
            .multiplicities_columns_for_range_check_16
            .num_elements();
        assert_eq!(num_range_check_16_multiplicities_cols, 1);
        assert_eq!(
            num_range_check_16_multiplicities_cols,
            circuit
                .stage_2_layout
                .intermediate_poly_for_range_check_16_multiplicity
                .num_elements(),
        );
        let num_timestamp_range_check_multiplicities_cols = circuit
            .witness_layout
            .multiplicities_columns_for_timestamp_range_check
            .num_elements();
        assert!(
            (num_timestamp_range_check_multiplicities_cols == 0)
                || (num_timestamp_range_check_multiplicities_cols == 1)
        );
        assert_eq!(
            num_timestamp_range_check_multiplicities_cols,
            circuit
                .stage_2_layout
                .intermediate_poly_for_timestamp_range_check_multiplicity
                .num_elements(),
        );
        let num_generic_multiplicities_cols = circuit
            .setup_layout
            .generic_lookup_setup_columns
            .num_elements();
        assert_eq!(circuit.setup_layout.generic_lookup_setup_columns.width(), 4,);
        assert_eq!(
            num_generic_multiplicities_cols,
            circuit
                .witness_layout
                .multiplicities_columns_for_generic_lookup
                .num_elements(),
        );
        assert_eq!(
            generic_lookup_setup_columns_start,
            circuit.setup_layout.generic_lookup_setup_columns.start()
        );
        let (delegation_aux_poly_col, delegation_challenges) =
            if handle_delegation_requests || process_delegations {
                (
                    translate_e4_offset(delegation_processing_aux_poly.start()),
                    DelegationChallenges::new(&delegation_challenges),
                )
            } else {
                (0, DelegationChallenges::default())
            };
        let (delegation_request_metadata, delegation_processing_metadata) =
            get_delegation_metadata(cached_data, circuit);
        let memory_challenges = MemoryChallenges::new(&memory_argument_challenges);
        let num_memory_args = circuit
            .stage_2_layout
            .intermediate_polys_for_memory_argument
            .num_elements();
        let batched_ram_accesses = if process_batch_ram_access {
            assert!(!process_shuffle_ram_init);
            assert_eq!(circuit.memory_layout.shuffle_ram_access_sets.len(), 0);
            assert!(!process_registers_and_indirect_access);
            assert_eq!(
                circuit.memory_layout.register_and_indirect_accesses.len(),
                0
            );
            let batched_ram_accesses = &circuit.memory_layout.batched_ram_accesses;
            assert!(batched_ram_accesses.len() > 0);
            let write_timestamp_col = delegation_processor_layout.write_timestamp.start();
            let abi_mem_offset_high_col = delegation_processor_layout.abi_mem_offset_high.start();
            assert_eq!(
                num_memory_args,
                batched_ram_accesses.len() + 1, /* grand product */
            );
            assert_eq!(num_memory_args, num_set_polys_for_memory_shuffle);
            BatchedRamAccesses::new(
                &memory_challenges,
                batched_ram_accesses,
                write_timestamp_col,
                abi_mem_offset_high_col,
            )
        } else {
            BatchedRamAccesses::default()
        };
        let register_and_indirect_accesses = if process_registers_and_indirect_access {
            assert!(!process_shuffle_ram_init);
            assert_eq!(circuit.memory_layout.shuffle_ram_access_sets.len(), 0);
            assert!(!process_batch_ram_access);
            assert_eq!(circuit.memory_layout.batched_ram_accesses.len(), 0);
            let register_and_indirect_accesses =
                &circuit.memory_layout.register_and_indirect_accesses;
            assert!(register_and_indirect_accesses.len() > 0);
            let write_timestamp_col = delegation_processor_layout.write_timestamp.start();
            let mut num_intermediate_polys_for_register_accesses = 0;
            for el in register_and_indirect_accesses.iter() {
                num_intermediate_polys_for_register_accesses += 1;
                num_intermediate_polys_for_register_accesses += el.indirect_accesses.len();
            }
            assert_eq!(
                num_memory_args,
                num_intermediate_polys_for_register_accesses + 1, /* grand product */
            );
            assert_eq!(num_memory_args, num_set_polys_for_memory_shuffle);
            RegisterAndIndirectAccesses::new(
                &memory_challenges,
                register_and_indirect_accesses,
                write_timestamp_col,
            )
        } else {
            RegisterAndIndirectAccesses::default()
        };
        let range_check_16_layout = RangeCheck16ArgsLayout::new(
            circuit,
            &range_check_16_width_1_lookups_access,
            &range_check_16_width_1_lookups_access_via_expressions,
            &translate_e4_offset,
        );
        let expressions_layout = if range_check_16_width_1_lookups_access_via_expressions.len() > 0
            || timestamp_range_check_width_1_lookups_access_via_expressions.len() > 0
        {
            let expect_constant_terms_are_zero = process_shuffle_ram_init;
            // Timestamp constant terms are probably always zero.
            FlattenedLookupExpressionsLayout::new(
                &range_check_16_width_1_lookups_access_via_expressions,
                &timestamp_range_check_width_1_lookups_access_via_expressions,
                num_stage_2_bf_cols,
                num_stage_2_e4_cols,
                expect_constant_terms_are_zero,
                &translate_e4_offset,
            )
        } else {
            FlattenedLookupExpressionsLayout::default()
        };
        let expressions_for_shuffle_ram_layout =
            if timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram.len()
                > 0
            {
                FlattenedLookupExpressionsForShuffleRamLayout::new(
                    &timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram,
                    num_stage_2_bf_cols,
                    num_stage_2_e4_cols,
                    &translate_e4_offset,
                )
            } else {
                FlattenedLookupExpressionsForShuffleRamLayout::default()
            };
        // 32-bit lazy init addresses are treated as a pair of range check 16 cols
        let lazy_init_teardown_layout = if process_shuffle_ram_init {
            assert!(circuit.lazy_init_address_aux_vars.is_some());
            LazyInitTeardownLayout::new(
                circuit,
                &lazy_init_address_range_check_16,
                &shuffle_ram_inits_and_teardowns,
                &translate_e4_offset,
            )
        } else {
            assert!(circuit.lazy_init_address_aux_vars.is_none());
            LazyInitTeardownLayout::default()
        };
        // Host work to precompute constants_times_challenges_sum and some helpers that
        // streamline device computation
        assert_eq!(helpers.len(), 0);
        assert_eq!(helpers.capacity(), MAX_HELPER_VALUES);
        let decompression_factor = flat_generic_constraints_metadata.decompression_factor;
        let decompression_factor_inv = decompression_factor.inverse().expect("must exist");
        let two = BF::from_u64_unchecked(2);
        let lookup_linearization_challenges = &lookup_challenges.linearization_challenges;
        let lookup_gamma = lookup_challenges.gamma;
        let lookup_gamma_squared = *lookup_gamma.clone().square();
        let lookup_two_gamma = *lookup_gamma.clone().mul_assign_by_base(&two);
        let mut alpha_offset = 0;
        if process_delegations {
            alpha_offset += 4;
        }
        if process_batch_ram_access {
            for i in 0..batched_ram_accesses.num_accesses as usize {
                if batched_ram_accesses.accesses[i].is_write {
                    alpha_offset += 6;
                } else {
                    alpha_offset += 4;
                }
            }
        }
        if process_registers_and_indirect_access {
            let mut flat_indirect_idx = 0;
            for i in 0..register_and_indirect_accesses.num_register_accesses as usize {
                let register_access = &register_and_indirect_accesses.register_accesses[i];
                if register_access.is_write {
                    alpha_offset += 6;
                } else {
                    alpha_offset += 4;
                }
                for j in 0..register_and_indirect_accesses.indirect_accesses_per_register_access[i]
                {
                    let indirect_access =
                        &register_and_indirect_accesses.indirect_accesses[flat_indirect_idx];
                    if indirect_access.is_write {
                        alpha_offset += 6;
                    } else {
                        alpha_offset += 4;
                    }
                    if j > 0 && indirect_access.address_derivation_carry_bit_num_elements > 0 {
                        alpha_offset += 1; // address_derivation_carry_bit constraint
                    }
                    flat_indirect_idx += 1;
                }
            }
        }
        // We must assign challenges for bare range check 16s,
        // range check 16 expressions, timestamp range check expressions,
        // and timestamp range check expressions for shuffle ram
        // in the same order challenges are assigned in the CPU code.
        let mut bound = range_check_16_width_1_lookups_access.len();
        if expressions_layout.range_check_16_constant_terms_are_zero {
            bound += range_check_16_width_1_lookups_access_via_expressions.len();
        }
        // bare (non-expression) range check 16s, plus range check 16 expressions if
        // all those expressions are known not to have constant terms
        for _ in 0..bound {
            alpha_offset += 1;
            let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
            helpers.push(*alpha.clone().mul_assign(&lookup_gamma));
            helpers.push(
                *alpha
                    .clone()
                    .mul_assign(&lookup_gamma_squared)
                    .mul_assign_by_base(&decompression_factor_inv),
            );
            constants_times_challenges
                .sum
                .sub_assign(alpha.clone().mul_assign(&lookup_two_gamma));
            alpha_offset += 1;
        }
        // Expressions may contain constant terms that need special handling. Pain.
        // need to pass alpha_offset rather than borrow it, because it's also used by
        // non-closure invocations during the lifetime of the closure
        let stash_helpers_for_expressions_with_constant_terms =
            |num_expression_pairs: usize,
             constant_terms: &[BF],
             alpha_offset: &mut usize,
             helpers: &mut Vec<E4, _>,
             constants_times_challenges: &mut ConstantsTimesChallenges| {
                for i in 0..num_expression_pairs {
                    let mut alpha = h_alphas_for_hardcoded_every_row_except_last[*alpha_offset];
                    let a_constant_term = constant_terms[2 * i];
                    let b_constant_term = constant_terms[2 * i + 1];
                    let constants_prod = *a_constant_term.clone().mul_assign(&b_constant_term);
                    constants_times_challenges
                        .sum
                        .add_assign(alpha.mul_assign_by_base(&constants_prod));
                    *alpha_offset += 1;
                    let alpha = h_alphas_for_hardcoded_every_row_except_last[*alpha_offset];
                    helpers.push(*alpha.clone().mul_assign(&lookup_gamma));
                    let constants_sum = *a_constant_term.clone().add_assign(&b_constant_term);
                    let mut gamma_corrections =
                        *lookup_gamma.clone().mul_assign_by_base(&constants_sum);
                    gamma_corrections.add_assign(&lookup_gamma_squared);
                    helpers.push(
                        *alpha
                            .clone()
                            .mul_assign(&gamma_corrections)
                            .mul_assign_by_base(&decompression_factor_inv),
                    );
                    constants_times_challenges
                        .sum
                        .sub_assign(alpha.clone().mul_assign_by_base(&constants_sum));
                    constants_times_challenges
                        .sum
                        .sub_assign(alpha.clone().mul_assign(&lookup_two_gamma));
                    *alpha_offset += 1;
                }
            };
        // range check 16 expressions, if constant terms are present
        if !expressions_layout.range_check_16_constant_terms_are_zero {
            let num_pairs = expressions_layout.num_range_check_16_expression_pairs as usize;
            stash_helpers_for_expressions_with_constant_terms(
                num_pairs as usize,
                &expressions_layout.constant_terms[0..2 * num_pairs],
                &mut alpha_offset,
                helpers,
                constants_times_challenges,
            );
        }
        // lazy init addresses range checks
        if process_shuffle_ram_init {
            alpha_offset += 1;
            let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
            helpers.push(*alpha.clone().mul_assign(&lookup_gamma));
            helpers.push(
                *alpha
                    .clone()
                    .mul_assign(&lookup_gamma_squared)
                    .mul_assign_by_base(&decompression_factor_inv),
            );
            constants_times_challenges
                .sum
                .sub_assign(alpha.clone().mul_assign(&lookup_two_gamma));
            alpha_offset += 1;
        }
        // timestamp range check expressions
        if expressions_layout.timestamp_constant_terms_are_zero {
            for _ in 0..expressions_layout.num_timestamp_expression_pairs as usize {
                alpha_offset += 1;
                let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
                helpers.push(*alpha.clone().mul_assign(&lookup_gamma));
                helpers.push(
                    *alpha
                        .clone()
                        .mul_assign(&lookup_gamma_squared)
                        .mul_assign_by_base(&decompression_factor_inv),
                );
                constants_times_challenges
                    .sum
                    .sub_assign(alpha.clone().mul_assign(&lookup_two_gamma));
                alpha_offset += 1;
            }
        } else {
            let num_pairs = expressions_layout.num_timestamp_expression_pairs as usize;
            let start = 2 * expressions_layout.num_range_check_16_expression_pairs as usize;
            let end = start + 2 * num_pairs;
            stash_helpers_for_expressions_with_constant_terms(
                num_pairs,
                &expressions_layout.constant_terms[start..end],
                &mut alpha_offset,
                helpers,
                constants_times_challenges,
            );
        }
        // Keeping these as comments because they're useful for debugging
        // println!(
        //     "num_range_check_16_expression_pairs {}",
        //     expressions_layout.num_range_check_16_expression_pairs
        // );
        // println!(
        //     "num_timestamp_expression_pairs {}",
        //     expressions_layout.num_timestamp_expression_pairs
        // );
        // println!(
        //     "range_check_16_constant_terms_are_zero {}",
        //     expressions_layout.range_check_16_constant_terms_are_zero
        // );
        // println!(
        //     "timestamp_constant_terms_are_zero {}",
        //     expressions_layout.timestamp_constant_terms_are_zero
        // );
        // println!(
        //     "expressions_for_shuffle_ram_layout.num_expression_pairs {}",
        //     expressions_for_shuffle_ram_layout.num_expression_pairs
        // );
        // timestamp range check expressions for shuffle ram
        let num_pairs = expressions_for_shuffle_ram_layout.num_expression_pairs as usize;
        let constant_terms_with_timestamp_high_circuit_idx_adjustment: Vec<BF> =
            expressions_for_shuffle_ram_layout
                .constant_terms
                .iter()
                .enumerate()
                .map(|(i, val)| {
                    if i % 2 == 0 {
                        *val
                    } else {
                        *val.clone()
                            .sub_assign(&memory_timestamp_high_from_circuit_idx)
                    }
                })
                .collect();
        stash_helpers_for_expressions_with_constant_terms(
            num_pairs,
            &constant_terms_with_timestamp_high_circuit_idx_adjustment[0..2 * num_pairs],
            &mut alpha_offset,
            helpers,
            constants_times_challenges,
        );
        let (delegated_width_3_lookups_layout, non_delegated_width_3_lookups_layout) =
            if process_delegations {
                let delegated_layout = DelegatedWidth3LookupsLayout::new(
                    circuit,
                    lookup_linearization_challenges,
                    lookup_gamma,
                    &h_alphas_for_hardcoded_every_row_except_last,
                    &mut alpha_offset,
                    helpers,
                    decompression_factor_inv,
                    constants_times_challenges,
                    &translate_e4_offset,
                );
                let non_delegated_placeholder = NonDelegatedWidth3LookupsLayout::new_placeholder(
                    delegated_layout.num_helpers_used,
                    delegated_layout.num_lookups,
                    delegated_layout.e4_arg_cols_start,
                );
                (delegated_layout, non_delegated_placeholder)
            } else {
                (
                    DelegatedWidth3LookupsLayout::default(),
                    NonDelegatedWidth3LookupsLayout::new(
                        circuit,
                        lookup_linearization_challenges,
                        lookup_gamma,
                        &h_alphas_for_hardcoded_every_row_except_last,
                        &mut alpha_offset,
                        helpers,
                        decompression_factor_inv,
                        constants_times_challenges,
                        &translate_e4_offset,
                    ),
                )
            };
        let range_check_16_multiplicities_layout = MultiplicitiesLayout::new(
            range_check_16_multiplicities_src,
            range_check_16_multiplicities_dst,
            range_check_16_setup_column,
            num_range_check_16_multiplicities_cols,
            1,
            &lookup_challenges,
            &h_alphas_for_hardcoded_every_row_except_last,
            &mut alpha_offset,
            helpers,
            decompression_factor_inv,
            &translate_e4_offset,
        );
        let timestamp_range_check_multiplicities_layout = MultiplicitiesLayout::new(
            timestamp_range_check_multiplicities_src,
            timestamp_range_check_multiplicities_dst,
            timestamp_range_check_setup_column,
            num_timestamp_range_check_multiplicities_cols,
            1,
            &lookup_challenges,
            &h_alphas_for_hardcoded_every_row_except_last,
            &mut alpha_offset,
            helpers,
            decompression_factor_inv,
            &translate_e4_offset,
        );
        let generic_lookup_multiplicities_layout = MultiplicitiesLayout::new(
            generic_lookup_multiplicities_src_start,
            generic_lookup_multiplicities_dst_start,
            generic_lookup_setup_columns_start,
            num_generic_multiplicities_cols,
            NUM_LOOKUP_ARGUMENT_KEY_PARTS,
            &lookup_challenges,
            &h_alphas_for_hardcoded_every_row_except_last,
            &mut alpha_offset,
            helpers,
            decompression_factor_inv,
            &translate_e4_offset,
        );
        if handle_delegation_requests {
            let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
            alpha_offset += 1;
            let mut timestamp_low_constant = delegation_challenges.linearization_challenges
                [DELEGATION_ARGUMENT_CHALLENGED_IDX_FOR_TIMESTAMP_LOW];
            timestamp_low_constant
                .mul_assign_by_base(&delegation_request_metadata.in_cycle_write_idx);
            let mut timestamp_high_constant = delegation_challenges.linearization_challenges
                [DELEGATION_ARGUMENT_CHALLENGED_IDX_FOR_TIMESTAMP_HIGH];
            timestamp_high_constant.mul_assign_by_base(&memory_timestamp_high_from_circuit_idx);
            helpers.push(
                *delegation_challenges
                    .gamma
                    .clone()
                    .add_assign(&timestamp_low_constant)
                    .add_assign(&timestamp_high_constant)
                    .mul_assign(&alpha)
                    .mul_assign_by_base(&decompression_factor_inv),
            );
            for challenge in delegation_challenges.linearization_challenges.iter() {
                helpers.push(*alpha.clone().mul_assign(&challenge));
            }
        }
        if process_delegations {
            let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
            alpha_offset += 1;
            helpers.push(
                *delegation_challenges
                    .gamma
                    .clone()
                    .add_assign_base(&delegation_processing_metadata.delegation_type)
                    .mul_assign(&alpha)
                    .mul_assign_by_base(&decompression_factor_inv),
            );
            for challenge in delegation_challenges.linearization_challenges.iter() {
                helpers.push(*alpha.clone().mul_assign(&challenge));
            }
        }
        let memory_args_start = translate_e4_offset(memory_accumulator_dst_start);
        if process_shuffle_ram_init {
            // the initial increment by 6 corresponds to the constraints that
            // ensure lazy init limbs are zero if "final borrow" is zero
            alpha_offset += 6;
            let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
            alpha_offset += 1;
            let alpha_times_gamma = *alpha.clone().mul_assign(&memory_challenges.gamma);
            constants_times_challenges
                .sum
                .sub_assign(&alpha_times_gamma);
            let mc = &memory_challenges;
            helpers.push(*alpha.clone().mul_assign(&mc.address_low_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.address_high_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.value_low_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.value_high_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.timestamp_low_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.timestamp_high_challenge));
            helpers.push(
                *alpha_times_gamma
                    .clone()
                    .mul_assign_by_base(&decompression_factor_inv),
            );
        }

        let shuffle_ram_accesses = if process_shuffle_ram_init {
            let shuffle_ram_access_sets = &circuit.memory_layout.shuffle_ram_access_sets;
            let write_timestamp_in_setup_start =
                circuit.setup_layout.timestamp_setup_columns.start();
            ShuffleRamAccesses::new(shuffle_ram_access_sets, write_timestamp_in_setup_start)
        } else {
            ShuffleRamAccesses::default()
        };
        for i in 0..shuffle_ram_accesses.num_accesses as usize {
            let access = &shuffle_ram_accesses.accesses[i];
            let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
            alpha_offset += 1;
            let mc = &memory_challenges;
            let mut numerator_constant = mc.gamma;
            if access.is_register_only {
                numerator_constant.add_assign_base(&BF::ONE);
            }
            let mut denom_constant = numerator_constant;
            let write_timestamp_low_constant = *mc
                .timestamp_low_challenge
                .clone()
                .mul_assign_by_base(&BF::from_u64_unchecked(i as u64));
            let write_timestamp_high_constant = *mc
                .timestamp_high_challenge
                .clone()
                .mul_assign_by_base(&memory_timestamp_high_from_circuit_idx);
            numerator_constant
                .add_assign(&write_timestamp_low_constant)
                .add_assign(&write_timestamp_high_constant);
            helpers.push(*alpha.clone().mul_assign(&mc.address_low_challenge));
            if !access.is_register_only {
                helpers.push(*alpha.clone().mul_assign(&mc.address_high_challenge));
            }
            helpers.push(*alpha.clone().mul_assign(&mc.value_low_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.value_high_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.timestamp_low_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.timestamp_high_challenge));
            helpers.push(
                *denom_constant
                    .mul_assign(&alpha)
                    .mul_assign_by_base(&decompression_factor_inv),
            );
            helpers.push(
                *numerator_constant
                    .mul_assign(&alpha)
                    .mul_assign_by_base(&decompression_factor_inv),
            );
        }
        for i in 0..batched_ram_accesses.num_accesses as usize {
            let access = &batched_ram_accesses.accesses[i];
            let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
            alpha_offset += 1;
            let mc = &memory_challenges;
            let mut constant = access.gamma_plus_address_low_contribution;
            constant.mul_assign(&alpha);
            if i == 0 {
                constants_times_challenges.sum.sub_assign(&constant);
            }
            helpers.push(*alpha.clone().mul_assign(&mc.address_high_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.value_low_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.value_high_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.timestamp_low_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.timestamp_high_challenge));
            helpers.push(*constant.mul_assign_by_base(&decompression_factor_inv));
        }
        let mut flat_indirect_idx = 0;
        for i in 0..register_and_indirect_accesses.num_register_accesses as usize {
            let register_access = &register_and_indirect_accesses.register_accesses[i];
            let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
            alpha_offset += 1;
            let mc = &memory_challenges;
            let mut constant = register_access.gamma_plus_one_plus_address_low_contribution;
            constant.mul_assign(&alpha);
            if i == 0 {
                constants_times_challenges.sum.sub_assign(&constant);
            }
            helpers.push(*alpha.clone().mul_assign(&mc.value_low_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.value_high_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.timestamp_low_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.timestamp_high_challenge));
            helpers.push(*constant.mul_assign_by_base(&decompression_factor_inv));
            for j in 0..register_and_indirect_accesses.indirect_accesses_per_register_access[i] {
                let indirect_access =
                    &register_and_indirect_accesses.indirect_accesses[flat_indirect_idx];
                flat_indirect_idx += 1;
                let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
                alpha_offset += 1;
                // we expect offset == 0 for the first indirect access and offset > 0 for others
                assert_eq!(j == 0, indirect_access.offset == 0);
                let offset = BF::from_u64_unchecked(indirect_access.offset as u64);
                let mut constant = *mc
                    .address_low_challenge
                    .clone()
                    .mul_assign_by_base(&offset)
                    .add_assign(&mc.gamma)
                    .mul_assign(&alpha);
                helpers.push(*alpha.clone().mul_assign(&mc.address_low_challenge));
                helpers.push(*alpha.clone().mul_assign(&mc.address_high_challenge));
                helpers.push(*alpha.clone().mul_assign(&mc.value_low_challenge));
                helpers.push(*alpha.clone().mul_assign(&mc.value_high_challenge));
                helpers.push(*alpha.clone().mul_assign(&mc.timestamp_low_challenge));
                helpers.push(*alpha.clone().mul_assign(&mc.timestamp_high_challenge));
                helpers.push(*constant.mul_assign_by_base(&decompression_factor_inv));
            }
        }
        assert_eq!(
            offset_for_grand_product_accumulation_poly,
            num_memory_args - 1
        );
        let memory_grand_product_col = memory_args_start + num_memory_args - 1;
        alpha_offset += 1;
        assert_eq!(
            alpha_offset,
            h_alphas_for_hardcoded_every_row_except_last.len()
        );
        // Prepare args and helpers for constraints on all rows except the last two
        alpha_offset = 0;
        let state_linkage_constraints = StateLinkageConstraints::new(circuit);
        alpha_offset += state_linkage_constraints.num_constraints as usize;
        if process_shuffle_ram_init {
            // alphas for "next lazy init timestamp > current lazy init timestamp"
            alpha_offset += 2;
        }
        assert_eq!(alpha_offset, h_alphas_for_every_row_except_last_two.len());
        // Args and helpers for boundary constraints (first row and second-to-last row)
        let boundary_constraints = BoundaryConstraints::new(
            circuit,
            external_values,
            public_inputs,
            process_shuffle_ram_init,
            lazy_init_teardown_layout.init_address_start as usize,
            lazy_init_teardown_layout.teardown_value_start as usize,
            lazy_init_teardown_layout.teardown_timestamp_start as usize,
            h_alphas_for_first_row,
            h_alphas_for_one_before_last_row,
            helpers,
            h_beta_powers,
            decompression_factor,
            constants_times_challenges,
        );
        // "+ 1" accounts for the additional grand product == 1 at row 0 constraint
        assert_eq!(
            boundary_constraints.num_first_row as usize + 1,
            h_alphas_for_first_row.len()
        );
        assert_eq!(
            boundary_constraints.num_one_before_last_row as usize,
            h_alphas_for_one_before_last_row.len()
        );
        // Just one constraint at last row (grand product accumulator)
        let mut alpha = h_alphas_for_last_row[0];
        alpha.mul_assign(&h_beta_powers[1]);
        helpers.push(*alpha.clone().mul_assign_by_base(&decompression_factor));
        helpers.push(*alpha.negate().mul_assign(&grand_product_accumulator));
        assert_eq!(1, h_alphas_for_last_row.len());
        // Constraints at last row and zero
        // range check 16 e4 arg sums
        // first make sure we can reconstruct e4 arg locations from
        // layout data the kernel already has
        let args_metadata = &circuit.stage_2_layout.intermediate_polys_for_range_check_16;
        let num_range_check_16_e4_args = args_metadata.ext_4_field_oracles.num_elements();
        assert_eq!(num_range_check_16_e4_args, args_metadata.num_pairs);
        assert_eq!(
            circuit
                .witness_layout
                .multiplicities_columns_for_range_check_16
                .num_elements(),
            1
        );
        assert_eq!(
            num_range_check_16_e4_args,
            (range_check_16_layout.num_dst_cols
                + expressions_layout.num_range_check_16_expression_pairs) as usize,
        );
        assert_eq!(
            translate_e4_offset(args_metadata.ext_4_field_oracles.start()),
            range_check_16_layout.e4_args_start as usize
        );
        let mut alpha_offset = 0;
        let mut alpha = h_alphas_for_last_row_and_at_zero[alpha_offset];
        alpha_offset += 1;
        helpers.push(*alpha.negate().mul_assign_by_base(&decompression_factor));
        // timestamp range check e4 arg sums
        if timestamp_range_check_multiplicities_layout.num_dst_cols > 0 {
            // first make sure we can reconstruct e4 arg locations from
            // layout data the kernel already has
            let args_metadata = &circuit
                .stage_2_layout
                .intermediate_polys_for_timestamp_range_checks;
            let num_timestamp_range_check_e4_args =
                args_metadata.ext_4_field_oracles.num_elements();
            let num_non_shuffle_ram_args =
                expressions_layout.num_timestamp_expression_pairs as usize;
            let num_shuffle_ram_args =
                expressions_for_shuffle_ram_layout.num_expression_pairs as usize;
            assert_eq!(num_timestamp_range_check_e4_args, args_metadata.num_pairs);
            assert_eq!(
                num_timestamp_range_check_e4_args,
                num_non_shuffle_ram_args + num_shuffle_ram_args,
            );
            let offset = expressions_layout.num_range_check_16_expression_pairs as usize;
            for (i, dst) in args_metadata.ext_4_field_oracles.iter().enumerate() {
                if i < num_non_shuffle_ram_args {
                    assert_eq!(
                        expressions_layout.e4_dst_cols[i + offset] as usize,
                        translate_e4_offset(dst.start),
                    );
                } else {
                    assert_eq!(
                        expressions_for_shuffle_ram_layout.e4_dst_cols[i - num_non_shuffle_ram_args]
                            as usize,
                        translate_e4_offset(dst.start),
                    );
                }
            }
            let mut alpha = h_alphas_for_last_row_and_at_zero[alpha_offset];
            alpha_offset += 1;
            helpers.push(*alpha.negate().mul_assign_by_base(&decompression_factor));
        }
        // generic lookup e4 arg sums
        assert!(num_generic_multiplicities_cols > 0);
        let mut alpha = h_alphas_for_last_row_and_at_zero[alpha_offset];
        alpha_offset += 1;
        helpers.push(*alpha.negate().mul_assign_by_base(&decompression_factor));
        if handle_delegation_requests || process_delegations {
            let mut alpha = h_alphas_for_last_row_and_at_zero[alpha_offset];
            alpha_offset += 1;
            let mut delegation_accumulator_interpolant_prefactor = sum_over_delegation_poly;
            delegation_accumulator_interpolant_prefactor
                .negate()
                .mul_assign_by_base(&omega)
                .mul_assign_by_base(&decompression_factor_inv);
            helpers.push(delegation_accumulator_interpolant_prefactor);
            helpers.push(*alpha.mul_assign_by_base(&decompression_factor));
        }
        assert_eq!(alpha_offset, h_alphas_for_last_row_and_at_zero.len());
        assert!(helpers.len() <= MAX_HELPER_VALUES);
        helpers
            .spare_capacity_mut()
            .fill(MaybeUninit::new(E4::ZERO));
        unsafe {
            helpers.set_len(MAX_HELPER_VALUES);
        }
        // print_sizes();
        Metadata {
            alpha_powers_layout,
            flat_generic_constraints_metadata,
            delegated_width_3_lookups_layout,
            non_delegated_width_3_lookups_layout,
            range_check_16_layout,
            expressions_layout,
            expressions_for_shuffle_ram_layout,
            generic_lookup_multiplicities_layout,
            state_linkage_constraints,
            boundary_constraints,
            memory_args_start,
            memory_grand_product_col,
            lazy_init_teardown_layout,
            shuffle_ram_accesses,
            batched_ram_accesses,
            range_check_16_multiplicities_layout,
            timestamp_range_check_multiplicities_layout,
            delegation_aux_poly_col,
            num_generic_constraints,
            delegation_challenges,
            delegation_processing_metadata,
            delegation_request_metadata,
            register_and_indirect_accesses,
        }
    }
}

pub fn compute_stage_3_composition_quotient_on_coset(
    cached_data: &ProverCachedData,
    circuit: &CompiledCircuitArtifact<BF>,
    metadata: Metadata,
    setup_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    witness_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    memory_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    stage_2_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    d_alpha_powers: &DeviceSlice<E4>,
    d_beta_powers: &DeviceSlice<E4>,
    d_helpers: &DeviceSlice<E4>,
    d_constants_times_challenges: &DeviceVariable<ConstantsTimesChallenges>,
    quotient: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let n = 1 << log_n;
    let num_setup_cols = circuit.setup_layout.total_width;
    let num_witness_cols = circuit.witness_layout.total_width;
    let num_memory_cols = circuit.memory_layout.total_width;
    let num_stage_2_bf_cols = circuit.stage_2_layout.num_base_field_polys();
    let num_stage_2_e4_cols = circuit.stage_2_layout.num_ext4_field_polys();
    let e4_cols_offset = circuit.stage_2_layout.ext4_polys_offset;
    assert_eq!(e4_cols_offset % 4, 0);
    assert!(num_stage_2_bf_cols <= e4_cols_offset);
    assert!(e4_cols_offset - num_stage_2_bf_cols < 4);
    assert_eq!(setup_cols.rows(), n);
    assert_eq!(setup_cols.cols(), num_setup_cols);
    assert_eq!(witness_cols.rows(), n);
    assert_eq!(witness_cols.cols(), num_witness_cols,);
    assert_eq!(memory_cols.rows(), n);
    assert_eq!(memory_cols.cols(), num_memory_cols,);
    assert_eq!(quotient.rows(), n);
    assert_eq!(quotient.cols(), 4);
    let ProverCachedData {
        trace_len,
        memory_timestamp_high_from_circuit_idx,
        handle_delegation_requests,
        process_batch_ram_access,
        process_registers_and_indirect_access,
        process_delegations,
        ..
    } = cached_data.clone();
    assert_eq!(trace_len, n);
    let Metadata {
        alpha_powers_layout,
        flat_generic_constraints_metadata,
        delegated_width_3_lookups_layout,
        non_delegated_width_3_lookups_layout,
        range_check_16_layout,
        expressions_layout,
        expressions_for_shuffle_ram_layout,
        generic_lookup_multiplicities_layout,
        state_linkage_constraints,
        boundary_constraints,
        memory_args_start,
        memory_grand_product_col,
        lazy_init_teardown_layout,
        shuffle_ram_accesses,
        batched_ram_accesses,
        range_check_16_multiplicities_layout,
        timestamp_range_check_multiplicities_layout,
        delegation_aux_poly_col,
        num_generic_constraints,
        delegation_challenges,
        delegation_processing_metadata,
        delegation_request_metadata,
        register_and_indirect_accesses,
    } = metadata;
    let AlphaPowersLayout {
        num_quotient_terms_every_row_except_last,
        num_quotient_terms_every_row_except_last_two,
        precomputation_size,
        ..
    } = alpha_powers_layout;
    let d_e4_helpers = d_helpers.as_ptr();
    let d_constants_times_challenges = d_constants_times_challenges.as_ptr();
    assert_eq!(d_alpha_powers.len(), precomputation_size);
    let d_alphas_for_every_row_except_last =
        &d_alpha_powers[(precomputation_size - num_quotient_terms_every_row_except_last)..];
    let d_alphas_for_every_row_except_last_two =
        &d_alpha_powers[(precomputation_size - num_quotient_terms_every_row_except_last_two)..];
    let (d_alphas_for_generic_constraints, d_alphas_for_hardcoded_every_row_except_last) =
        d_alphas_for_every_row_except_last.split_at(num_generic_constraints);
    // it's handy to keep a copy
    let generic_constraints_metadata = flat_generic_constraints_metadata.clone();
    let witness_cols = witness_cols.as_ptr_and_stride();
    let memory_cols = memory_cols.as_ptr_and_stride();
    let d_alphas_for_generic_constraints = d_alphas_for_generic_constraints.as_ptr();
    let quotient = quotient.as_mut_ptr_and_stride();
    let block_dim = 4 * WARP_SIZE;
    let grid_dim = (n as u32 + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenericConstraintsArguments::new(
        generic_constraints_metadata,
        witness_cols,
        memory_cols,
        d_alphas_for_generic_constraints,
        quotient,
        log_n,
    );
    GenericConstraintsFunction(generic_constraints_kernel).launch(&config, &args)?;
    // for convenience, demarcate bf and vectorized e4 sections of stage_2_cols
    assert_eq!(stage_2_cols.rows(), n);
    assert_eq!(
        stage_2_cols.cols(),
        e4_cols_offset + 4 * num_stage_2_e4_cols
    );
    let (stage_2_bf_cols, stage_2_e4_cols) = {
        let stride = stage_2_cols.stride();
        let offset = stage_2_cols.offset();
        let slice = stage_2_cols.slice();
        let (bf_slice, e4_slice) = slice.split_at(e4_cols_offset * stride);
        (
            DeviceMatrixChunk::new(
                &bf_slice[0..num_stage_2_bf_cols * stride],
                stride,
                offset,
                n,
            ),
            DeviceMatrixChunk::new(e4_slice, stride, offset, n),
        )
    };
    let setup_cols = setup_cols.as_ptr_and_stride();
    let stage_2_bf_cols = stage_2_bf_cols.as_ptr_and_stride();
    let stage_2_e4_cols = stage_2_e4_cols.as_ptr_and_stride();
    let d_alphas_for_hardcoded_every_row_except_last =
        d_alphas_for_hardcoded_every_row_except_last.as_ptr();
    let d_alphas_for_every_row_except_last_two = d_alphas_for_every_row_except_last_two.as_ptr();
    let d_beta_powers = d_beta_powers.as_ptr();
    let block_dim = 4 * WARP_SIZE;
    let grid_dim = (n as u32 + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    if process_delegations {
        let args = DelegatedWidth3LookupsArguments::new(
            delegated_width_3_lookups_layout,
            witness_cols,
            memory_cols,
            stage_2_e4_cols,
            d_e4_helpers,
            quotient,
            flat_generic_constraints_metadata.decompression_factor_squared,
            log_n,
        );
        DelegatedWidth3LookupsFunction(delegated_width_3_lookups_kernel).launch(&config, &args)?;
    }
    let omega_inv = flat_generic_constraints_metadata.omega_inv;
    let omega_inv_squared = *omega_inv.clone().square();
    let args = HardcodedConstraintsArguments::new(
        setup_cols,
        witness_cols,
        memory_cols,
        stage_2_bf_cols,
        stage_2_e4_cols,
        process_delegations,
        handle_delegation_requests,
        delegation_aux_poly_col as u32,
        delegation_challenges,
        delegation_processing_metadata,
        delegation_request_metadata,
        memory_args_start as u32,
        memory_grand_product_col as u32,
        lazy_init_teardown_layout,
        shuffle_ram_accesses,
        process_batch_ram_access,
        batched_ram_accesses,
        process_registers_and_indirect_access,
        register_and_indirect_accesses,
        range_check_16_layout,
        expressions_layout,
        expressions_for_shuffle_ram_layout,
        non_delegated_width_3_lookups_layout,
        range_check_16_multiplicities_layout,
        timestamp_range_check_multiplicities_layout,
        generic_lookup_multiplicities_layout,
        state_linkage_constraints,
        boundary_constraints,
        d_alphas_for_hardcoded_every_row_except_last,
        d_alphas_for_every_row_except_last_two,
        d_beta_powers,
        d_e4_helpers,
        d_constants_times_challenges,
        quotient,
        memory_timestamp_high_from_circuit_idx,
        flat_generic_constraints_metadata.decompression_factor,
        flat_generic_constraints_metadata.decompression_factor_squared,
        flat_generic_constraints_metadata.every_row_zerofier,
        omega_inv,
        omega_inv_squared,
        log_n,
    );
    HardcodedConstraintsFunction(hardcoded_constraints_kernel).launch(&config, &args)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::Context;
    use crate::device_structures::{DeviceMatrix, DeviceMatrixMut};
    use std::alloc::Global;

    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use fft::materialize_powers_serial_starting_with_one;
    use field::Field;
    use prover::tests::{run_basic_delegation_test_impl, GpuComparisonArgs};
    use serial_test::serial;

    type BF = BaseField;
    type E4 = Ext4Field;

    fn comparison_hook(gpu_comparison_args: &GpuComparisonArgs) {
        let GpuComparisonArgs {
            circuit,
            setup,
            external_values,
            public_inputs,
            twiddles,
            lde_precomputations,
            table_driver: _,
            lookup_mapping: _,
            log_n,
            circuit_sequence,
            delegation_processing_type,
            prover_data,
        } = gpu_comparison_args;
        let log_n = *log_n;
        let circuit_sequence = *circuit_sequence;
        let delegation_processing_type = delegation_processing_type.unwrap_or(0);
        let domain_size = 1 << log_n;
        let stage_1_output = &prover_data.stage_1_result;
        let stage_2_output = &prover_data.stage_2_result;
        let stage_3_output = &prover_data.quotient_commitment_result;
        let domain_index = 1;
        let tau = lde_precomputations.domain_bound_precomputations[domain_index]
            .as_ref()
            .unwrap()
            .coset_offset;

        let cached_data = ProverCachedData::new(
            &circuit,
            &external_values,
            domain_size,
            circuit_sequence,
            delegation_processing_type,
        );

        print_size::<FlattenedGenericConstraintsMetadata>("FlattenedGenericConstraintsMetadata");
        print_size::<DelegatedWidth3LookupsLayout>("DelegatedWidth3LookupsLayout");
        print_size::<NonDelegatedWidth3LookupsLayout>("NonDelegatedWidth3LookupsLayout");
        print_size::<StateLinkageConstraints>("StageLinkageConstraints");
        print_size::<BoundaryConstraints>("BoundaryConstraints");
        print_sizes();

        // Repackage row-major data as column-major for GPU
        let range = 0..domain_size;
        let num_setup_cols = circuit.setup_layout.total_width;
        let num_witness_cols = circuit.witness_layout.total_width;
        let num_memory_cols = circuit.memory_layout.total_width;
        let num_trace_cols = num_witness_cols + num_memory_cols;
        let num_stage_2_cols = circuit.stage_2_layout.total_width;

        // Internally, AlphaPowersLayout::new calls circuit.as_verifier_compiled_artifact
        // We expect this to be negligible, but it doesn't hurt to sanity check.
        let now = std::time::Instant::now();
        let alpha_powers_layout =
            AlphaPowersLayout::new(&circuit, cached_data.num_stage_3_quotient_terms);
        let duration = now.elapsed();
        println!("Time to construct AlphaPowersLayout {:?}", duration);
        assert!(duration < std::time::Duration::from_micros(50));

        let mut h_setup_cols: Vec<BF> = vec![BF::ZERO; domain_size * num_setup_cols];
        let mut h_trace_cols: Vec<BF> = vec![BF::ZERO; domain_size * num_trace_cols];
        let mut h_stage_2_cols: Vec<BF> = vec![BF::ZERO; domain_size * num_stage_2_cols];
        let mut h_quotient: Vec<BF> = vec![BF::ZERO; 4 * domain_size];
        let mut h_alpha_powers: Vec<E4> = materialize_powers_serial_starting_with_one::<_, Global>(
            stage_3_output.quotient_alpha,
            alpha_powers_layout.precomputation_size,
        );
        h_alpha_powers.reverse();
        let h_beta_powers = materialize_powers_serial_starting_with_one::<_, Global>(
            stage_3_output.quotient_beta,
            BETA_POWERS_COUNT,
        );

        // imitating access patterns in zksync_airbender's prover_stages/stage4.rs
        let mut setup_trace_view = setup.ldes[domain_index].trace.row_view(range.clone());
        let mut trace_view = stage_1_output.ldes[domain_index]
            .trace
            .row_view(range.clone());
        let mut stage_2_trace_view = stage_2_output.ldes[domain_index]
            .trace
            .row_view(range.clone());
        unsafe {
            for i in 0..domain_size {
                let setup_trace_view_row = setup_trace_view.current_row_ref();
                let trace_view_row = trace_view.current_row_ref();
                let stage_2_trace_view_row = stage_2_trace_view.current_row_ref();
                {
                    let mut src = setup_trace_view_row.as_ptr();
                    for j in 0..num_setup_cols {
                        h_setup_cols[i + j * domain_size] = src.read();
                        src = src.add(1);
                    }
                }
                {
                    let mut src = trace_view_row.as_ptr();
                    for j in 0..num_trace_cols {
                        h_trace_cols[i + j * domain_size] = src.read();
                        src = src.add(1);
                    }
                }
                {
                    let mut src = stage_2_trace_view_row.as_ptr();
                    for j in 0..num_stage_2_cols {
                        h_stage_2_cols[i + j * domain_size] = src.read();
                        src = src.add(1);
                    }
                }
                setup_trace_view.advance_row();
                trace_view.advance_row();
                stage_2_trace_view.advance_row();
            }
        }
        let mut h_helpers = Vec::with_capacity(MAX_HELPER_VALUES);
        let mut h_constants_times_challenges = ConstantsTimesChallenges::default();
        let lookup_challenges = LookupChallenges::new(
            &prover_data
                .stage_2_result
                .lookup_argument_linearization_challenges,
            prover_data.stage_2_result.lookup_argument_gamma,
        );
        let metadata = Metadata::new(
            &h_alpha_powers,
            &h_beta_powers,
            tau,
            twiddles.omega,
            twiddles.omega_inv,
            &lookup_challenges,
            &cached_data,
            &circuit,
            &external_values,
            &public_inputs,
            stage_2_output.grand_product_accumulator,
            stage_2_output.sum_over_delegation_poly,
            log_n as u32,
            &mut h_helpers,
            &mut h_constants_times_challenges,
        );
        // Allocate GPU memory
        let stream = CudaStream::default();
        let mut d_alloc_setup_cols =
            DeviceAllocation::<BF>::alloc(domain_size * num_setup_cols).unwrap();
        let mut d_alloc_trace_cols =
            DeviceAllocation::<BF>::alloc(domain_size * num_trace_cols).unwrap();
        let mut d_alloc_stage_2_cols =
            DeviceAllocation::<BF>::alloc(domain_size * num_stage_2_cols).unwrap();
        let mut d_alpha_powers =
            DeviceAllocation::<E4>::alloc(alpha_powers_layout.precomputation_size).unwrap();
        let mut d_beta_powers = DeviceAllocation::alloc(BETA_POWERS_COUNT).unwrap();
        let mut d_helpers = DeviceAllocation::<E4>::alloc(MAX_HELPER_VALUES).unwrap();
        let mut d_constants_times_challenges = DeviceAllocation::alloc(1).unwrap();
        let mut d_alloc_quotient = DeviceAllocation::<BF>::alloc(4 * domain_size).unwrap();
        memory_copy_async(&mut d_alloc_setup_cols, &h_setup_cols, &stream).unwrap();
        memory_copy_async(&mut d_alloc_trace_cols, &h_trace_cols, &stream).unwrap();
        memory_copy_async(&mut d_alloc_stage_2_cols, &h_stage_2_cols, &stream).unwrap();
        memory_copy_async(&mut d_alpha_powers, &h_alpha_powers, &stream).unwrap();
        memory_copy_async(&mut d_beta_powers, &h_beta_powers, &stream).unwrap();
        memory_copy_async(&mut d_helpers, &h_helpers, &stream).unwrap();
        memory_copy_async(
            &mut d_constants_times_challenges,
            &[h_constants_times_challenges],
            &stream,
        )
        .unwrap();
        let d_setup_cols = DeviceMatrix::new(&d_alloc_setup_cols, domain_size);
        let d_trace_cols = DeviceMatrix::new(&d_alloc_trace_cols, domain_size);
        let slice = d_trace_cols.slice();
        let stride = d_trace_cols.stride();
        let offset = d_trace_cols.offset();
        let d_witness_cols = DeviceMatrixChunk::new(
            &slice[0..num_witness_cols * stride],
            stride,
            offset,
            domain_size,
        );
        let d_memory_cols = DeviceMatrixChunk::new(
            &slice[num_witness_cols * stride..],
            stride,
            offset,
            domain_size,
        );
        let d_stage_2_cols = DeviceMatrix::new(&d_alloc_stage_2_cols, domain_size);
        let mut d_quotient = DeviceMatrixMut::new(&mut d_alloc_quotient, domain_size);
        compute_stage_3_composition_quotient_on_coset(
            &cached_data,
            &circuit,
            metadata,
            &d_setup_cols,
            &d_witness_cols,
            &d_memory_cols,
            &d_stage_2_cols,
            &d_alpha_powers,
            &d_beta_powers,
            &d_helpers,
            &d_constants_times_challenges[0],
            &mut d_quotient,
            log_n as u32,
            &stream,
        )
        .unwrap();
        memory_copy_async(&mut h_quotient, &d_alloc_quotient, &stream).unwrap();
        stream.synchronize().unwrap();

        let mut cpu_result_view = stage_3_output.ldes[domain_index]
            .trace
            .row_view(0..domain_size);
        unsafe {
            for i in 0..domain_size {
                let cpu_result_view_row = cpu_result_view.current_row_ref();
                let cpu_src = cpu_result_view_row.as_ptr().cast::<E4>();
                assert!(cpu_src.is_aligned());
                let gpu_result: [BF; 4] = std::array::from_fn(|j| h_quotient[i + j * domain_size]);
                assert_eq!(
                    E4::from_array_of_base(gpu_result),
                    cpu_src.read(),
                    "failed at row {}",
                    i,
                );
                cpu_result_view.advance_row();
            }
        }
    }

    // #[test]
    // #[serial]
    // fn test_stage_3_for_basic_circuit() {
    //     let ctx = Context::create(12).unwrap();
    //     run_basic_test_impl(Some(Box::new(comparison_hook)));
    //     ctx.destroy().unwrap();
    // }

    #[test]
    #[serial]
    fn test_stage_3_for_delegation_circuit() {
        let ctx = Context::create(12).unwrap();
        run_basic_delegation_test_impl(
            Some(Box::new(comparison_hook)),
            Some(Box::new(comparison_hook)),
        );
        ctx.destroy().unwrap();
    }
}
