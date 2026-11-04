use super::arg_utils::*;
use crate::field::{BaseField, Ext2Field, Ext4Field};
use cs::definitions::{
    BoundaryConstraintLocation, LookupExpression, TableIndex, COMMON_TABLE_WIDTH,
    EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_LINEARIZATION_CHALLENGES, NUM_LOOKUP_ARGUMENT_KEY_PARTS,
};
use cs::one_row_compiler::{
    ColumnAddress, CompiledCircuitArtifact, IntermediateStatePermutationVariables,
};
use field::{Field, FieldExtension, PrimeField};
use prover::definitions::AuxArgumentsBoundaryValues;
use std::alloc::Allocator;

type BF = BaseField;
type E2 = Ext2Field;
type E4 = Ext4Field;

pub const BETA_POWERS_COUNT: usize = 6;

fn stash_witness_or_memory_column_address(address: &ColumnAddress) -> u16 {
    match address {
        ColumnAddress::WitnessSubtree(col) => *col as u16,
        ColumnAddress::MemorySubtree(col) => (*col as u16) | ColTypeFlags::MEMORY,
        _ => panic!("unexpected ColumnAddress variant"),
    }
}

#[derive(Clone, Default)]
#[repr(C)]
pub(super) struct ConstantsTimesChallenges {
    pub first_row: E4,
    pub one_before_last_row: E4,
    pub every_row_except_last: E4,
}

// These values are hand-picked, so that the biggest circuit (keccak) fits.
// What is here must match values from stage_3.cu
const MAX_NON_BOOLEAN_CONSTRAINTS: usize = 192;
const MAX_TERMS: usize = 2208;
const MAX_EXPLICIT_COEFFS: usize = 928;
const MAX_FLAT_COL_IDXS: usize = 4192;
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
pub(super) struct FlattenedGenericConstraintsMetadata {
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

    fn compute_every_row_zerofier(decompression_factor_squared: E2) -> E2 {
        let mut zerofier = decompression_factor_squared.clone();
        assert_eq!(zerofier, E2::from_base(BF::MINUS_ONE));
        zerofier.sub_assign_base(&BF::ONE);
        zerofier.inverse().expect("must exist")
    }

    pub fn new(
        circuit: &CompiledCircuitArtifact<BF>,
        tau: E2,
        omega_inv: E2,
        domain_size: usize,
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
                Self::stash_coeff(
                    *coeff,
                    &mut coeffs_info,
                    &mut explicit_coeffs,
                    &mut flat_term_idx,
                    &mut explicit_coeff_idx,
                );
                col_idxs[flat_col_idx] = stash_witness_or_memory_column_address(a);
                flat_col_idx += 1;
                col_idxs[flat_col_idx] = stash_witness_or_memory_column_address(b);
                flat_col_idx += 1;
            }
            let num_quadratic_terms = u8::try_from(num_quadratic_terms).unwrap();
            let num_linear_terms = constraint.linear_terms.len();
            assert!(num_linear_terms < MAX_LINEAR_TERMS_PER_CONSTRAINT);
            for (coeff, a) in constraint.linear_terms.iter() {
                Self::stash_coeff(
                    *coeff,
                    &mut coeffs_info,
                    &mut explicit_coeffs,
                    &mut flat_term_idx,
                    &mut explicit_coeff_idx,
                );
                col_idxs[flat_col_idx] = stash_witness_or_memory_column_address(a);
                flat_col_idx += 1;
            }
            let num_linear_terms = u8::try_from(num_linear_terms).unwrap();
            num_linear_and_quadratic_terms_per_constraint[constraint_idx] =
                [num_quadratic_terms, num_linear_terms];
            constraint_idx += 1;
        }
        assert_eq!(d2cs_iter.next(), None);
        for constraint in d1cs.iter() {
            let num_linear_terms = constraint.linear_terms.len();
            assert!(num_linear_terms < MAX_LINEAR_TERMS_PER_CONSTRAINT);
            for (coeff, a) in constraint.linear_terms.iter() {
                Self::stash_coeff(
                    *coeff,
                    &mut coeffs_info,
                    &mut explicit_coeffs,
                    &mut flat_term_idx,
                    &mut explicit_coeff_idx,
                );
                col_idxs[flat_col_idx] = stash_witness_or_memory_column_address(a);
                flat_col_idx += 1;
            }
            let num_linear_terms = u8::try_from(num_linear_terms).unwrap();
            num_linear_and_quadratic_terms_per_constraint[constraint_idx] =
                [0 as u8, num_linear_terms];
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

    pub fn prepare_async_challenge_data(
        &self,
        circuit: &CompiledCircuitArtifact<BF>,
        alpha_powers: &[E4],
        constants_times_challenges: &mut ConstantsTimesChallenges,
    ) {
        let mut constraint_idx = 0;
        let num_boolean_constraints = self.num_boolean_constraints as usize;
        let d2cs = &circuit.degree_2_constraints[num_boolean_constraints..];
        for constraint in d2cs.iter() {
            let mut constant_times_challenge =
                alpha_powers[constraint_idx + num_boolean_constraints];
            constant_times_challenge.mul_assign_by_base(&constraint.constant_term);
            constants_times_challenges
                .every_row_except_last
                .add_assign(&constant_times_challenge);
            constraint_idx += 1;
        }
        for constraint in circuit.degree_1_constraints.iter() {
            let mut constant_times_challenge =
                alpha_powers[constraint_idx + num_boolean_constraints];
            constant_times_challenge.mul_assign_by_base(&constraint.constant_term);
            constants_times_challenges
                .every_row_except_last
                .add_assign(&constant_times_challenge);
            constraint_idx += 1;
        }
    }
}

// just a guess, tune as needed
pub(super) const MAX_HELPER_VALUES: usize = 1536;

// A width 3 lookup is a tuple of 3 values.
// We're on the coset domain, so I don't think we can get any free lunches
// using precomputed denom tables.

const LOOKUP_VAL_IS_COL_FLAG: u8 = u8::MAX;

#[derive(Clone)]
#[repr(C)]
pub(super) struct Width3LookupsLayout<
    const MAX_WIDTH_3_LOOKUPS: usize,
    const MAX_WIDTH_3_LOOKUP_VALS: usize,
    const MAX_WIDTH_3_LOOKUP_COEFFS: usize,
    const MAX_TERMS_PER_EXPRESSION: usize,
    const MAX_WIDTH_3_LOOKUP_COLS: usize,
> {
    pub coeffs: [u32; MAX_WIDTH_3_LOOKUP_COEFFS],
    pub col_idxs: [u16; MAX_WIDTH_3_LOOKUP_COLS],
    pub num_terms_per_expression: [u8; MAX_WIDTH_3_LOOKUP_VALS],
    pub table_id_is_col: [bool; MAX_WIDTH_3_LOOKUPS],
    pub e4_arg_cols: [u16; MAX_WIDTH_3_LOOKUPS],
    pub helpers_offset: u32,
    pub num_helpers_used: u32,
    pub num_lookups: u32,
    pub e4_arg_cols_start: u32,
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
        helpers_offset: usize,
        is_unrolled: bool,
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
        let mut num_helpers_used = 0;
        let num_lookups = circuit.witness_layout.width_3_lookups.len();
        assert!(num_lookups > 0);
        assert_eq!(
            num_lookups,
            circuit
                .stage_2_layout
                .intermediate_polys_for_generic_lookup
                .num_elements()
        );
        for (term_idx, lookup_set) in circuit.witness_layout.width_3_lookups.iter().enumerate() {
            let e4_arg_col = translate_e4_offset(
                circuit
                    .stage_2_layout
                    .intermediate_polys_for_generic_lookup
                    .get_range(term_idx)
                    .start,
            );
            e4_arg_cols[term_idx] = u16::try_from(e4_arg_col).unwrap();
            match lookup_set.table_index {
                TableIndex::Constant(_table_type) => num_helpers_used += 1,
                TableIndex::Variable(place) => {
                    table_id_is_col[term_idx] = true;
                    col_idxs[col_idx] = match place {
                        ColumnAddress::WitnessSubtree(col) => col as u16,
                        _ => panic!("unexpected ColumnAddress variant"),
                    };
                    col_idx += 1;
                    num_helpers_used += 2;
                }
            }
            let mut lookup_is_empty = true;
            for val in lookup_set.input_columns.iter() {
                match val {
                    LookupExpression::Variable(place) => {
                        lookup_is_empty = false;
                        num_helpers_used += 1;
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
                            num_helpers_used += 1;
                        }
                        if !is_unrolled {
                            assert_eq!(a.constant_term, BF::ZERO);
                        }
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
        }
        let e4_arg_cols_start = translate_e4_offset(
            circuit
                .stage_2_layout
                .intermediate_polys_for_generic_lookup
                .start(),
        );
        assert_eq!(e4_arg_cols_start, e4_arg_cols[0] as usize);
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

    pub fn prepare_async_challenge_data(
        &self,
        circuit: &CompiledCircuitArtifact<BF>,
        lookup_challenges: &[E4],
        lookup_gamma: E4,
        alphas: &[E4],
        alpha_offset: &mut usize,
        helpers: &mut Vec<E4, impl Allocator>,
        decompression_factor_inv: E2,
        constants_times_challenges: &mut ConstantsTimesChallenges,
    ) {
        let table_id_challenge = lookup_challenges[NUM_LOOKUP_ARGUMENT_KEY_PARTS - 2];
        let mut val_challenges = Vec::with_capacity(NUM_LOOKUP_ARGUMENT_KEY_PARTS - 1);
        val_challenges.push(E4::ONE);
        val_challenges
            .append(&mut (&lookup_challenges[0..(NUM_LOOKUP_ARGUMENT_KEY_PARTS - 2)]).to_vec());
        assert_eq!(self.helpers_offset as usize, helpers.len());
        for lookup_set in circuit.witness_layout.width_3_lookups.iter() {
            let alpha = alphas[*alpha_offset];
            *alpha_offset += 1;
            let internal_constants_helper_idx = helpers.len();
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
                TableIndex::Variable(_place) => {
                    helpers.push(
                        *alpha
                            .clone()
                            .mul_assign(&lookup_gamma)
                            .mul_assign_by_base(&decompression_factor_inv),
                    );
                    helpers.push(*alpha.clone().mul_assign(&table_id_challenge));
                }
            }
            for (val, val_challenge) in lookup_set.input_columns.iter().zip(val_challenges.iter()) {
                match val {
                    LookupExpression::Variable(_place) => {
                        helpers.push(*alpha.clone().mul_assign(val_challenge));
                    }
                    LookupExpression::Expression(a) => {
                        let num_terms = a.linear_terms.len();
                        if num_terms > 0 {
                            helpers.push(*alpha.clone().mul_assign(&val_challenge));
                        }
                        helpers[internal_constants_helper_idx].add_assign(
                            alpha
                                .clone()
                                .mul_assign(&val_challenge)
                                .mul_assign_by_base(&a.constant_term)
                                .mul_assign_by_base(&decompression_factor_inv),
                        );
                    }
                };
            }
            constants_times_challenges
                .every_row_except_last
                .sub_assign(&alpha);
        }
        assert_eq!(
            self.num_helpers_used as usize,
            helpers.len() - self.helpers_offset as usize
        );
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

pub(super) type DelegatedWidth3LookupsLayout = Width3LookupsLayout<
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

pub(super) type NonDelegatedWidth3LookupsLayout = Width3LookupsLayout<
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

#[derive(Clone)]
#[repr(C)]
pub(super) struct MultiplicitiesLayout {
    pub src_cols_start: u32,
    pub dst_cols_start: u32,
    pub setup_cols_start: u32,
    pub num_dst_cols: u32,
}

impl MultiplicitiesLayout {
    pub fn prepare_async_challenge_data(
        &self,
        entry_width: usize,
        gamma: E4,
        linearization_challenges: &[E4],
        alphas: &[E4],
        alpha_offset: &mut usize,
        helpers: &mut Vec<E4, impl Allocator>,
        decompression_factor_inv: E2,
    ) {
        assert_eq!(entry_width - 1, linearization_challenges.len());
        for _ in 0..self.num_dst_cols as usize {
            let alpha = alphas[*alpha_offset];
            *alpha_offset = *alpha_offset + 1;
            helpers.push(
                *alpha
                    .clone()
                    .mul_assign(&gamma)
                    .mul_assign_by_base(&decompression_factor_inv),
            );
            for j in 0..entry_width - 1 {
                helpers.push(*alpha.clone().mul_assign(&linearization_challenges[j]));
            }
        }
    }
}

impl Default for MultiplicitiesLayout {
    fn default() -> Self {
        Self {
            src_cols_start: 0,
            dst_cols_start: 0,
            setup_cols_start: 0,
            num_dst_cols: 0,
        }
    }
}

#[derive(Clone)]
#[repr(C)]
pub(super) struct IntermediateStateLookupLayout {
    pub execute: u32,
    pub pc: u32,
    // pub timestamp : u32, // not used for lookup
    pub rs1_index: u32,
    pub rs2_index: u32,
    pub rd_index: u32,
    // pub decoder_witness_is_in_memory: bool, // should be false
    pub rd_is_zero: u32,
    pub imm: u32,
    pub funct3: u32,
    // pub funct7: u32, // should be empty
    // pub circuit_family: u32, // should be empty
    pub circuit_family_extra_mask: u32,
    pub intermediate_poly: u32,
    pub has_decoder: bool,
}

impl IntermediateStateLookupLayout {
    pub fn new<F: Fn(usize) -> usize>(
        circuit: &CompiledCircuitArtifact<BF>,
        translate_e4_offset: &F,
    ) -> Self {
        let intermediate_state_layout = circuit
            .memory_layout
            .intermediate_state_layout
            .as_ref()
            .unwrap();
        let IntermediateStatePermutationVariables {
            execute,
            pc,
            timestamp: _,
            rs1_index,
            rs2_index,
            rd_index,
            decoder_witness_is_in_memory,
            rd_is_zero,
            imm,
            funct3,
            funct7,
            circuit_family,
            circuit_family_extra_mask,
        } = *intermediate_state_layout;
        assert_eq!(decoder_witness_is_in_memory, false);
        assert_eq!(funct7.num_elements(), 0);
        assert_eq!(circuit_family.num_elements(), 0);
        let intermediate_poly = translate_e4_offset(
            circuit
                .stage_2_layout
                .intermediate_poly_for_decoder_accesses
                .start(),
        );
        Self {
            execute: execute.start() as u32,
            pc: pc.start() as u32,
            rs1_index: rs1_index.start() as u32,
            rs2_index: stash_witness_or_memory_column_address(&rs2_index) as u32,
            rd_index: stash_witness_or_memory_column_address(&rd_index) as u32,
            rd_is_zero: rd_is_zero.start() as u32,
            imm: imm.start() as u32,
            funct3: funct3.start() as u32,
            circuit_family_extra_mask: stash_witness_or_memory_column_address(
                &circuit_family_extra_mask,
            ) as u32,
            intermediate_poly: intermediate_poly as u32,
            has_decoder: true,
        }
    }

    pub fn prepare_async_challenge_data(
        &self,
        challenges: &DecoderTableChallenges,
        alphas: &[E4],
        alpha_offset: &mut usize,
        helpers: &mut Vec<E4, impl Allocator>,
        decompression_factor_inv: E2,
    ) {
        assert!(self.has_decoder);
        let alpha = alphas[*alpha_offset];
        *alpha_offset = *alpha_offset + 1;
        helpers.push(
            *alpha
                .clone()
                .mul_assign(&challenges.gamma)
                .mul_assign_by_base(&decompression_factor_inv),
        );
        for j in 0..EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_LINEARIZATION_CHALLENGES {
            helpers.push(
                *alpha
                    .clone()
                    .mul_assign(&challenges.linearization_challenges[j]),
            );
        }
    }
}

impl Default for IntermediateStateLookupLayout {
    fn default() -> Self {
        Self {
            execute: 0,
            pc: 0,
            rs1_index: 0,
            rs2_index: 0,
            rd_index: 0,
            rd_is_zero: 0,
            imm: 0,
            funct3: 0,
            circuit_family_extra_mask: 0,
            intermediate_poly: 0,
            has_decoder: false,
        }
    }
}

const MAX_PUBLIC_INPUTS_FIRST_ROW: usize = 2;
const MAX_PUBLIC_INPUTS_ONE_BEFORE_LAST_ROW: usize = 2;
const MAX_BOUNDARY_CONSTRAINTS_FIRST_ROW: usize =
    6 * MAX_LAZY_INIT_TEARDOWN_SETS + MAX_PUBLIC_INPUTS_FIRST_ROW;
const MAX_BOUNDARY_CONSTRAINTS_ONE_BEFORE_LAST_ROW: usize =
    6 * MAX_LAZY_INIT_TEARDOWN_SETS + MAX_PUBLIC_INPUTS_ONE_BEFORE_LAST_ROW;

#[derive(Clone)]
#[repr(C)]
pub(super) struct BoundaryConstraints {
    pub first_row_cols: [u32; MAX_BOUNDARY_CONSTRAINTS_FIRST_ROW],
    pub one_before_last_row_cols: [u32; MAX_BOUNDARY_CONSTRAINTS_ONE_BEFORE_LAST_ROW],
    pub num_init_teardown: u32,
    pub num_public_first_row: u32,
    pub num_public_one_before_last_row: u32,
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
        process_shuffle_ram_init: bool,
        lazy_init_teardown_layouts: &LazyInitTeardownLayouts,
    ) -> Self {
        let mut first_row_cols = [0; MAX_BOUNDARY_CONSTRAINTS_FIRST_ROW];
        let mut one_before_last_row_cols = [0; MAX_BOUNDARY_CONSTRAINTS_ONE_BEFORE_LAST_ROW];
        let mut num_init_teardown = 0;
        assert_eq!(
            process_shuffle_ram_init,
            lazy_init_teardown_layouts.num_init_teardown_sets > 0,
        );
        for i in 0..lazy_init_teardown_layouts.num_init_teardown_sets as usize {
            // init address at first and second-to-last rows
            let start_col = lazy_init_teardown_layouts.layouts[i].init_address_start;
            first_row_cols[num_init_teardown] = start_col;
            one_before_last_row_cols[num_init_teardown] = start_col;
            num_init_teardown += 1;
            first_row_cols[num_init_teardown] = start_col + 1;
            one_before_last_row_cols[num_init_teardown] = start_col + 1;
            num_init_teardown += 1;
            // teardown value at first and second-to-last rows
            let start_col = lazy_init_teardown_layouts.layouts[i].teardown_value_start;
            first_row_cols[num_init_teardown] = start_col;
            one_before_last_row_cols[num_init_teardown] = start_col;
            num_init_teardown += 1;
            first_row_cols[num_init_teardown] = start_col + 1;
            one_before_last_row_cols[num_init_teardown] = start_col + 1;
            num_init_teardown += 1;
            // teardown timestamp at first and second-to-last rows
            let start_col = lazy_init_teardown_layouts.layouts[i].teardown_timestamp_start;
            first_row_cols[num_init_teardown] = start_col;
            one_before_last_row_cols[num_init_teardown] = start_col;
            num_init_teardown += 1;
            first_row_cols[num_init_teardown] = start_col + 1;
            one_before_last_row_cols[num_init_teardown] = start_col + 1;
            num_init_teardown += 1;
        }
        let mut num_public_first_row = 0;
        let mut num_public_one_before_last_row = 0;
        for (location, column_address) in circuit.public_inputs.iter() {
            match location {
                BoundaryConstraintLocation::FirstRow => {
                    first_row_cols[num_init_teardown + num_public_first_row] =
                        Self::unpack_public_input_column_address(*column_address);
                    num_public_first_row += 1;
                }
                BoundaryConstraintLocation::OneBeforeLastRow => {
                    one_before_last_row_cols[num_init_teardown + num_public_one_before_last_row] =
                        Self::unpack_public_input_column_address(*column_address);
                    num_public_one_before_last_row += 1;
                }
                BoundaryConstraintLocation::LastRow => {
                    panic!("public inputs on the last row are not supported");
                }
            }
        }
        assert_eq!(num_public_first_row, num_public_one_before_last_row);
        assert!(num_init_teardown + num_public_first_row <= MAX_BOUNDARY_CONSTRAINTS_FIRST_ROW);
        assert!(
            num_init_teardown + num_public_one_before_last_row
                <= MAX_BOUNDARY_CONSTRAINTS_ONE_BEFORE_LAST_ROW
        );
        Self {
            first_row_cols,
            one_before_last_row_cols,
            num_init_teardown: num_init_teardown as u32,
            num_public_first_row: num_public_first_row as u32,
            num_public_one_before_last_row: num_public_one_before_last_row as u32,
        }
    }

    pub fn prepare_async_challenge_data(
        &self,
        circuit: &CompiledCircuitArtifact<BF>,
        aux_boundary_values: &[AuxArgumentsBoundaryValues],
        public_inputs: &[BF],
        process_shuffle_ram_init: bool,
        alphas_first_row: &[E4],
        alphas_one_before_last_row: &[E4],
        helpers: &mut Vec<E4, impl Allocator>,
        beta_powers: &[E4],
        decompression_factor: E2,
        constants_times_challenges: &mut ConstantsTimesChallenges,
    ) {
        constants_times_challenges.first_row = E4::ZERO;
        constants_times_challenges.one_before_last_row = E4::ZERO;
        let mut num_first_row = 0;
        let mut num_one_before_last_row = 0;
        let mut helpers_first_row = Vec::with_capacity(MAX_BOUNDARY_CONSTRAINTS_FIRST_ROW);
        let mut helpers_one_before_last_row =
            Vec::with_capacity(MAX_BOUNDARY_CONSTRAINTS_ONE_BEFORE_LAST_ROW);
        if process_shuffle_ram_init {
            assert_eq!(
                self.num_init_teardown as usize,
                6 * aux_boundary_values.len()
            );
            let helpers_for_limb_pair =
                |counter: &mut usize,
                 vals: &[BF],
                 alphas: &[E4],
                 beta_power: &E4,
                 helpers: &mut Vec<E4, _>,
                 constants_times_challenges: &mut E4| {
                    for j in 0..=1 {
                        let mut alpha = alphas[*counter];
                        alpha.mul_assign(beta_power);
                        helpers.push(*alpha.clone().mul_assign_by_base(&decompression_factor));
                        constants_times_challenges.sub_assign(alpha.mul_assign_by_base(&vals[j]));
                        *counter = *counter + 1;
                    }
                };
            for values in aux_boundary_values.iter() {
                helpers_for_limb_pair(
                    &mut num_first_row,
                    &values.lazy_init_first_row[..],
                    alphas_first_row,
                    &beta_powers[3],
                    &mut helpers_first_row,
                    &mut constants_times_challenges.first_row,
                );
                helpers_for_limb_pair(
                    &mut num_first_row,
                    &values.teardown_value_first_row[..],
                    alphas_first_row,
                    &beta_powers[3],
                    &mut helpers_first_row,
                    &mut constants_times_challenges.first_row,
                );
                helpers_for_limb_pair(
                    &mut num_first_row,
                    &values.teardown_timestamp_first_row[..],
                    alphas_first_row,
                    &beta_powers[3],
                    &mut helpers_first_row,
                    &mut constants_times_challenges.first_row,
                );
                helpers_for_limb_pair(
                    &mut num_one_before_last_row,
                    &values.lazy_init_one_before_last_row[..],
                    alphas_one_before_last_row,
                    &beta_powers[2],
                    &mut helpers_one_before_last_row,
                    &mut constants_times_challenges.one_before_last_row,
                );
                helpers_for_limb_pair(
                    &mut num_one_before_last_row,
                    &values.teardown_value_one_before_last_row[..],
                    alphas_one_before_last_row,
                    &beta_powers[2],
                    &mut helpers_one_before_last_row,
                    &mut constants_times_challenges.one_before_last_row,
                );
                helpers_for_limb_pair(
                    &mut num_one_before_last_row,
                    &values.teardown_timestamp_one_before_last_row[..],
                    alphas_one_before_last_row,
                    &beta_powers[2],
                    &mut helpers_one_before_last_row,
                    &mut constants_times_challenges.one_before_last_row,
                );
            }
        }
        assert_eq!(num_first_row, self.num_init_teardown as usize);
        assert_eq!(num_one_before_last_row, self.num_init_teardown as usize);
        for ((location, _column_address), val) in
            circuit.public_inputs.iter().zip(public_inputs.iter())
        {
            match location {
                BoundaryConstraintLocation::FirstRow => {
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
        assert_eq!(helpers_first_row.len(), helpers_one_before_last_row.len());
        assert_eq!(
            helpers_first_row.len(),
            (self.num_init_teardown + self.num_public_first_row) as usize,
        );
        // account for memory accumulator, which requires a first row constraint
        let mut alpha = alphas_first_row[num_first_row];
        alpha.mul_assign(&beta_powers[3]);
        let grand_product_helper = *alpha.clone().mul_assign_by_base(&decompression_factor);
        constants_times_challenges.first_row.sub_assign(&alpha);
        // pushing grand product helper first is a bit more convenient for the kernel
        helpers.push(grand_product_helper);
        helpers.extend_from_slice(&helpers_first_row);
        helpers.extend_from_slice(&helpers_one_before_last_row);
    }
}
