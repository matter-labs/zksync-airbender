use std::collections::BTreeMap;

use super::*;
use crate::constraint::Term;
use crate::cs::circuit::CircuitOutput;
use crate::cs::circuit::*;
use crate::cs::circuit::{LookupQuery, LookupQueryTableType, RangeCheckQuery};
pub use crate::definitions::*;
use constraint::Constraint;
use field::FieldExtension;
use field::PrimeField;
use field::{Field, Mersenne31Complex};
use field::{Mersenne31Field, Mersenne31Quartic};
use quote::quote;
use std::collections::BTreeSet;

mod bytecode_preprocessed_executor;
mod compile_layout;
mod decoder_compilation;
mod executor_compilation;

pub mod delegation;
pub mod layout_utils;
pub mod stage_2_layout;

pub use self::layout_utils::*;
pub use self::stage_2_layout::*;

pub const SHIFT_16: u64 = 1 << 16;

pub fn array_to_tokens<T: quote::ToTokens, const N: usize>(
    els: &[T; N],
) -> proc_macro2::TokenStream {
    use quote::quote;
    use quote::TokenStreamExt;

    let mut stream = proc_macro2::TokenStream::new();
    stream.append_separated(
        els.into_iter().map(|el| {
            quote! { #el }
        }),
        quote! {,},
    );
    let stream = quote! {
        [#stream]
    };

    stream
}

pub fn slice_to_tokens<T: quote::ToTokens>(els: &[T]) -> proc_macro2::TokenStream {
    use quote::quote;
    use quote::TokenStreamExt;

    let mut stream = proc_macro2::TokenStream::new();
    stream.append_separated(
        els.into_iter().map(|el| {
            quote! { #el }
        }),
        quote! {,},
    );
    let stream = quote! {
        &[#stream]
    };

    stream
}

pub fn slice_to_token_array<T: quote::ToTokens>(els: &[T]) -> proc_macro2::TokenStream {
    use quote::quote;
    use quote::TokenStreamExt;

    let mut stream = proc_macro2::TokenStream::new();
    stream.append_separated(
        els.into_iter().map(|el| {
            quote! { #el }
        }),
        quote! {,},
    );
    let stream = quote! {
        [#stream]
    };

    stream
}

impl<const WIDTH: usize> quote::ToTokens for ColumnSet<WIDTH> {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let width = WIDTH;
        let Self {
            start,
            num_elements,
        } = *self;
        let stream = quote! {
            ColumnSet::<#width> {
                start: #start,
                num_elements: #num_elements,
            }
        };

        tokens.extend(stream);
    }
}

impl<const WIDTH: usize> quote::ToTokens for AlignedColumnSet<WIDTH> {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let width = WIDTH;
        let Self {
            start,
            num_elements,
        } = *self;
        let stream = quote! {
            AlignedColumnSet::<#width> {
                start: #start,
                num_elements: #num_elements,
            }
        };

        tokens.extend(stream);
    }
}

#[derive(Default)]
pub struct OneRowCompiler<F: PrimeField> {
    _marker: std::marker::PhantomData<F>,
}

impl quote::ToTokens for ColumnAddress {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let stream = match *self {
            ColumnAddress::WitnessSubtree(offset) => {
                quote! {
                    ColumnAddress::WitnessSubtree(#offset)
                }
            }
            ColumnAddress::MemorySubtree(offset) => {
                quote! {
                    ColumnAddress::MemorySubtree(#offset)
                }
            }
            ColumnAddress::SetupSubtree(offset) => {
                quote! {
                    ColumnAddress::SetupSubtree(#offset)
                }
            }
            ColumnAddress::OptimizedOut(offset) => {
                quote! {
                    ColumnAddress::OptimizedOut(#offset)
                }
            }
        };

        tokens.extend(stream);
    }
}

impl<F: PrimeField> LookupInput<F> {
    pub fn empty() -> Self {
        LookupInput::Expression {
            linear_terms: vec![],
            constant_coeff: F::ZERO,
        }
    }
}

impl<F: PrimeField> From<Variable> for LookupInput<F> {
    fn from(value: Variable) -> Self {
        Self::Variable(value)
    }
}

impl<F: PrimeField> From<Constraint<F>> for LookupInput<F> {
    #[track_caller]
    fn from(value: Constraint<F>) -> Self {
        // NOTE: we allow literal constants here
        assert!(value.degree() <= 1);
        let mut value = value;
        value.normalize();
        let (_, linear_terms, constant_coeff) = value.split_max_quadratic();
        Self::Expression {
            linear_terms,
            constant_coeff,
        }
    }
}

impl CompiledDegree2Constraint<Mersenne31Field> {
    pub fn evaluate_at_row_on_main_domain(
        &self,
        witness_row: &[Mersenne31Field],
        memory_row: &[Mersenne31Field],
    ) -> Mersenne31Field {
        let mut result = self.constant_term;
        for (coeff, place) in self.linear_terms.iter() {
            let mut value = read_value(*place, witness_row, memory_row);
            value.mul_assign(coeff);
            result.add_assign(&value);
        }

        for (coeff, a, b) in self.quadratic_terms.iter() {
            let mut value = read_value(*a, witness_row, memory_row);
            let b = read_value(*b, witness_row, memory_row);
            value.mul_assign(&b);
            value.mul_assign(coeff);
            result.add_assign(&value);
        }

        result
    }

    pub fn evaluate_at_row_with_accumulation(
        &self,
        witness_row: &[Mersenne31Field],
        memory_row: &[Mersenne31Field],
        challenge: &Mersenne31Quartic,
        quadratic_accumulator: &mut Mersenne31Quartic,
        linear_accumulator: &mut Mersenne31Quartic,
        constant_accumulator: &mut Mersenne31Quartic,
    ) {
        let mut t = *challenge;
        t.mul_assign_by_base(&self.constant_term);
        constant_accumulator.add_assign(&t);

        let mut acc = Mersenne31Field::ZERO;
        for (coeff, a, b) in self.quadratic_terms.iter() {
            let mut value = read_value(*a, witness_row, memory_row);
            let b = read_value(*b, witness_row, memory_row);
            value.mul_assign(&b);
            value.mul_assign(coeff);
            acc.add_assign(&value);
        }
        let mut t = *challenge;
        t.mul_assign_by_base(&acc);
        quadratic_accumulator.add_assign(&t);

        let mut acc = Mersenne31Field::ZERO;
        for (coeff, place) in self.linear_terms.iter() {
            let mut value = read_value(*place, witness_row, memory_row);
            value.mul_assign(coeff);
            acc.add_assign(&value);
        }
        let mut t = *challenge;
        t.mul_assign_by_base(&acc);
        linear_accumulator.add_assign(&t);
    }

    #[inline(always)]
    pub fn evaluate_at_row(
        &self,
        witness_row: &[Mersenne31Field],
        memory_row: &[Mersenne31Field],
        tau_in_domain_by_half: &Mersenne31Complex,
        tau_in_domain: &Mersenne31Complex,
    ) -> Mersenne31Complex {
        let mut acc = Mersenne31Field::ZERO;
        for (coeff, a, b) in self.quadratic_terms.iter() {
            let mut value = read_value(*a, witness_row, memory_row);
            let b = read_value(*b, witness_row, memory_row);
            value.mul_assign(&b);
            value.mul_assign(coeff);
            acc.add_assign(&value);
        }
        let mut t = *tau_in_domain;
        t.mul_assign_by_base(&acc);

        let mut acc = Mersenne31Field::ZERO;
        for (coeff, place) in self.linear_terms.iter() {
            let mut value = read_value(*place, witness_row, memory_row);
            value.mul_assign(coeff);
            acc.add_assign(&value);
        }

        let mut result = *tau_in_domain_by_half;
        result.mul_assign_by_base(&acc);
        result.add_assign_base(&self.constant_term);
        result.add_assign(&t);

        result
    }

    #[inline(always)]
    pub fn evaluate_at_row_with_special_domain_choice(
        &self,
        witness_row: &[Mersenne31Field],
        memory_row: &[Mersenne31Field],
    ) -> Mersenne31Complex {
        // we know that tau^H/2 = (0, -1) and tau^H = (-1, 0)
        let mut acc = Mersenne31Field::ZERO;
        for (coeff, a, b) in self.quadratic_terms.iter() {
            let mut value = read_value(*a, witness_row, memory_row);
            let b = read_value(*b, witness_row, memory_row);
            value.mul_assign(&b);
            value.mul_assign(coeff);
            acc.add_assign(&value);
        }
        let mut c0 = self.constant_term;
        c0.sub_assign(&acc);

        let mut acc = Mersenne31Field::ZERO;
        for (coeff, place) in self.linear_terms.iter() {
            let mut value = read_value(*place, witness_row, memory_row);
            value.mul_assign(coeff);
            acc.add_assign(&value);
        }
        acc.negate();

        Mersenne31Complex { c0, c1: acc }
    }
}

impl StaticVerifierCompiledDegree2Constraint<Mersenne31Field> {
    pub fn evaluate_at_row(
        &self,
        witness_row: &[Mersenne31Quartic],
        memory_row: &[Mersenne31Quartic],
    ) -> Mersenne31Quartic {
        let mut result = Mersenne31Quartic::from_base(self.constant_term);

        // hope for promoted constant here
        if self.linear_terms.len() > 0 {
            for (coeff, place) in self.linear_terms.iter() {
                let mut value = read_value(*place, witness_row, memory_row);
                value.mul_assign_by_base(coeff);
                result.add_assign_base(&value);
            }
        }

        debug_assert!(self.quadratic_terms.len() > 0);

        for (coeff, a, b) in self.quadratic_terms.iter() {
            let mut value = read_value(*a, witness_row, memory_row);
            let b = read_value(*b, witness_row, memory_row);
            value.mul_assign(&b);
            value.mul_assign_by_base(coeff);
            result.add_assign_base(&value);
        }

        result
    }
}

impl CompiledDegree1Constraint<Mersenne31Field> {
    #[inline]
    pub fn evaluate_at_row_on_main_domain(
        &self,
        witness_row: &[Mersenne31Field],
        memory_row: &[Mersenne31Field],
    ) -> Mersenne31Field {
        let mut result = self.constant_term;
        for (coeff, place) in self.linear_terms.iter() {
            let mut value = read_value(*place, witness_row, memory_row);
            value.mul_assign(coeff);
            result.add_assign(&value);
        }

        result
    }

    #[inline]
    pub fn evaluate_at_row_on_main_domain_ext(
        &self,
        witness_row: &[Mersenne31Field],
        memory_row: &[Mersenne31Field],
        setup_row: &[Mersenne31Field],
    ) -> Mersenne31Field {
        let mut result = self.constant_term;
        for (coeff, place) in self.linear_terms.iter() {
            let mut value =
                read_value_with_setup_access(*place, witness_row, memory_row, setup_row);
            value.mul_assign(coeff);
            result.add_assign(&value);
        }

        result
    }

    pub fn evaluate_at_row_with_accumulation(
        &self,
        witness_row: &[Mersenne31Field],
        memory_row: &[Mersenne31Field],
        challenge: &Mersenne31Quartic,
        linear_accumulator: &mut Mersenne31Quartic,
        constant_accumulator: &mut Mersenne31Quartic,
    ) {
        let mut t = *challenge;
        t.mul_assign_by_base(&self.constant_term);
        constant_accumulator.add_assign(&t);

        let mut acc = Mersenne31Field::ZERO;
        for (coeff, place) in self.linear_terms.iter() {
            let mut value = read_value(*place, witness_row, memory_row);
            value.mul_assign(coeff);
            acc.add_assign(&value);
        }
        let mut t = *challenge;
        t.mul_assign_by_base(&acc);
        linear_accumulator.add_assign(&t);
    }

    #[inline(always)]
    pub fn evaluate_at_row(
        &self,
        witness_row: &[Mersenne31Field],
        memory_row: &[Mersenne31Field],
        tau_in_domain_by_half: &Mersenne31Complex,
    ) -> Mersenne31Complex {
        let mut acc = Mersenne31Field::ZERO;
        for (coeff, place) in self.linear_terms.iter() {
            let mut value = read_value(*place, witness_row, memory_row);
            value.mul_assign(coeff);
            acc.add_assign(&value);
        }

        let mut result = *tau_in_domain_by_half;
        result.mul_assign_by_base(&acc);
        result.add_assign_base(&self.constant_term);

        result
    }

    #[inline(always)]
    pub fn evaluate_at_row_ext(
        &self,
        witness_row: &[Mersenne31Field],
        memory_row: &[Mersenne31Field],
        setup_row: &[Mersenne31Field],
        tau_in_domain_by_half: &Mersenne31Complex,
    ) -> Mersenne31Complex {
        let mut acc = Mersenne31Field::ZERO;
        for (coeff, place) in self.linear_terms.iter() {
            let mut value =
                read_value_with_setup_access(*place, witness_row, memory_row, setup_row);
            value.mul_assign(coeff);
            acc.add_assign(&value);
        }

        let mut result = *tau_in_domain_by_half;
        result.mul_assign_by_base(&acc);
        result.add_assign_base(&self.constant_term);

        result
    }

    #[inline(always)]
    pub fn evaluate_at_row_with_special_domain_choice(
        &self,
        witness_row: &[Mersenne31Field],
        memory_row: &[Mersenne31Field],
    ) -> Mersenne31Complex {
        // we know that tau^H/2 = (0, -1) and tau^H = (-1, 0)
        let mut acc = Mersenne31Field::ZERO;
        for (coeff, place) in self.linear_terms.iter() {
            let mut value = read_value(*place, witness_row, memory_row);
            value.mul_assign(coeff);
            acc.add_assign(&value);
        }
        acc.negate();

        Mersenne31Complex {
            c0: self.constant_term,
            c1: acc,
        }
    }
}

impl StaticVerifierCompiledDegree1Constraint<Mersenne31Field> {
    pub fn evaluate_at_row(
        &self,
        witness_row: &[Mersenne31Quartic],
        memory_row: &[Mersenne31Quartic],
    ) -> Mersenne31Quartic {
        let mut result = Mersenne31Quartic::from_base(self.constant_term);
        for (coeff, place) in self.linear_terms.iter() {
            let mut value = read_value(*place, witness_row, memory_row);
            value.mul_assign_by_base(coeff);
            result.add_assign_base(&value);
        }

        result
    }
}

#[derive(
    Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct OptimizedCompiledDegree2Constraint<F: PrimeField> {
    pub inner_linear_terms: Box<[(F, ColumnAddress)]>,
    pub inner_constant_term: F,
    pub outer_variable: ColumnAddress,
    pub outer_constant_term: F,
}

impl quote::ToTokens for RegisterOnlyAccessAddress {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let Self { register_index } = *self;
        let stream = quote! {
            RegisterOnlyAccessAddress {
                register_index: #register_index,
            }
        };

        tokens.extend(stream);
    }
}

impl quote::ToTokens for RegisterOrRamAccessAddress {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let Self {
            is_register,
            address,
        } = *self;
        let stream = quote! {
            RegisterOrRamAccessAddress {
                is_register: #is_register,
                address: #address,
            }
        };

        tokens.extend(stream);
    }
}

impl quote::ToTokens for ShuffleRamAddress {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            Self::RegisterOnly(t) => {
                let stream = quote! {
                    ShuffleRamAddress::RegisterOnly(#t)
                };

                tokens.extend(stream);
            }
            Self::RegisterOrRam(t) => {
                let stream = quote! {
                    ShuffleRamAddress::RegisterOrRam(#t)
                };

                tokens.extend(stream);
            }
        }
    }
}

impl quote::ToTokens for ShuffleRamQueryReadColumns {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let Self {
            in_cycle_write_index,
            address,
            read_timestamp,
            read_value,
        } = *self;

        let stream = quote! {
            ShuffleRamQueryReadColumns {
                in_cycle_write_index: #in_cycle_write_index,
                address: #address,
                read_timestamp: #read_timestamp,
                read_value: #read_value,
            }
        };

        tokens.extend(stream);
    }
}

impl quote::ToTokens for ShuffleRamAuxComparisonSet {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let Self {
            aux_low_high: [low, high],
            intermediate_borrow,
            final_borrow,
        } = *self;

        let stream = quote! {
            ShuffleRamAuxComparisonSet {
                aux_low_high: [#low, #high],
                intermediate_borrow: #intermediate_borrow,
                final_borrow: #final_borrow,
            }
        };

        tokens.extend(stream);
    }
}

impl quote::ToTokens for ShuffleRamQueryWriteColumns {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let Self {
            in_cycle_write_index,
            address,
            read_timestamp,
            read_value,
            write_value,
        } = *self;

        let stream = quote! {
            ShuffleRamQueryWriteColumns {
                in_cycle_write_index: #in_cycle_write_index,
                address: #address,
                read_timestamp: #read_timestamp,
                read_value: #read_value,
                write_value: #write_value,
            }
        };

        tokens.extend(stream);
    }
}

impl quote::ToTokens for ShuffleRamQueryColumns {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let stream = match *self {
            Self::Readonly(readonly) => {
                quote! {
                    ShuffleRamQueryColumns::Readonly(#readonly)
                }
            }
            Self::Write(write) => {
                quote! {
                    ShuffleRamQueryColumns::Write(#write)
                }
            }
        };

        tokens.extend(stream);
    }
}

impl quote::ToTokens for TableIndex {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let stream = match *self {
            TableIndex::Variable(column) => {
                quote! {
                    TableIndex::Variable(#column)
                }
            }
            TableIndex::Constant(table_type) => {
                quote! {
                    TableIndex::Constant(#table_type)
                }
            }
        };

        tokens.extend(stream);
    }
}

impl quote::ToTokens for BatchedRamAccessColumns {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let stream = match *self {
            BatchedRamAccessColumns::ReadAccess {
                read_timestamp,
                read_value,
            } => {
                quote! {
                    BatchedRamAccessColumns::ReadAccess { read_timestamp: #read_timestamp, read_value: #read_value }
                }
            }
            BatchedRamAccessColumns::WriteAccess {
                read_timestamp,
                read_value,
                write_value,
            } => {
                quote! {
                    BatchedRamAccessColumns::WriteAccess { read_timestamp: #read_timestamp, read_value: #read_value, write_value: #write_value }
                }
            }
        };

        tokens.extend(stream);
    }
}

impl quote::ToTokens for RegisterAccessColumns {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let stream = match *self {
            RegisterAccessColumns::ReadAccess {
                read_timestamp,
                read_value,
                register_index,
            } => {
                quote! {
                    RegisterAccessColumns::ReadAccess { read_timestamp: #read_timestamp, read_value: #read_value, register_index: #register_index }
                }
            }
            RegisterAccessColumns::WriteAccess {
                read_timestamp,
                read_value,
                write_value,
                register_index,
            } => {
                quote! {
                    RegisterAccessColumns::WriteAccess { read_timestamp: #read_timestamp, read_value: #read_value, write_value: #write_value, register_index: #register_index }
                }
            }
        };

        tokens.extend(stream);
    }
}

impl quote::ToTokens for IndirectAccessColumns {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let stream = match *self {
            IndirectAccessColumns::ReadAccess {
                read_timestamp,
                read_value,
                offset,
                address_derivation_carry_bit,
            } => {
                quote! {
                    IndirectAccessColumns::ReadAccess { read_timestamp: #read_timestamp, read_value: #read_value, offset: #offset, address_derivation_carry_bit: #address_derivation_carry_bit }
                }
            }
            IndirectAccessColumns::WriteAccess {
                read_timestamp,
                read_value,
                write_value,
                offset,
                address_derivation_carry_bit,
            } => {
                quote! {
                    IndirectAccessColumns::WriteAccess { read_timestamp: #read_timestamp, read_value: #read_value, write_value: #write_value, offset: #offset, address_derivation_carry_bit: #address_derivation_carry_bit }
                }
            }
        };

        tokens.extend(stream);
    }
}

impl quote::ToTokens for RegisterAndIndirectAccessDescription {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let RegisterAndIndirectAccessDescription {
            register_access,
            indirect_accesses,
        } = self;

        let indirect_accesses_stream = slice_to_tokens(indirect_accesses);

        let stream = quote! {
            CompiledRegisterAndIndirectAccessDescription::<'static> {
                register_access: #register_access,
                indirect_accesses: #indirect_accesses_stream,
            }
        };

        tokens.extend(stream);
    }
}

impl quote::ToTokens for ShuffleRamInitAndTeardownLayout {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let ShuffleRamInitAndTeardownLayout {
            lazy_init_addresses_columns,
            lazy_teardown_values_columns,
            lazy_teardown_timestamps_columns,
        } = self;
        let stream = quote! {
            ShuffleRamInitAndTeardownLayout {
                lazy_init_addresses_columns: #lazy_init_addresses_columns,
                lazy_teardown_values_columns: #lazy_teardown_values_columns,
                lazy_teardown_timestamps_columns: #lazy_teardown_timestamps_columns,
            }
        };

        tokens.extend(stream);
    }
}

impl quote::ToTokens for DelegationRequestLayout {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let DelegationRequestLayout {
            multiplicity,
            delegation_type,
            abi_mem_offset_high,
            in_cycle_write_index,
        } = self;
        let stream = quote! {
            DelegationRequestLayout {
                multiplicity: #multiplicity,
                delegation_type: #delegation_type,
                abi_mem_offset_high: #abi_mem_offset_high,
                in_cycle_write_index: #in_cycle_write_index,
            }
        };

        tokens.extend(stream);
    }
}

impl quote::ToTokens for DelegationProcessingLayout {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let DelegationProcessingLayout {
            multiplicity,
            abi_mem_offset_high,
            write_timestamp,
        } = self;
        let stream = quote! {
            DelegationProcessingLayout {
                multiplicity: #multiplicity,
                abi_mem_offset_high: #abi_mem_offset_high,
                write_timestamp: #write_timestamp,
            }
        };

        tokens.extend(stream);
    }
}

impl quote::ToTokens for BoundaryConstraintLocation {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let stream = match *self {
            BoundaryConstraintLocation::FirstRow => {
                quote! {
                    BoundaryConstraintLocation::FirstRow
                }
            }
            BoundaryConstraintLocation::LastRow => {
                quote! {
                    BoundaryConstraintLocation::FirstRow
                }
            }
            BoundaryConstraintLocation::OneBeforeLastRow => {
                quote! {
                    BoundaryConstraintLocation::FirstRow
                }
            }
        };

        tokens.extend(stream);
    }
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct CompiledCircuitArtifact<F: PrimeField> {
    pub witness_layout: WitnessSubtree<F>,
    pub memory_layout: MemorySubtree,
    pub setup_layout: SetupLayout,
    pub stage_2_layout: LookupAndMemoryArgumentLayout,
    pub degree_2_constraints: Vec<CompiledDegree2Constraint<F>>,
    pub degree_1_constraints: Vec<CompiledDegree1Constraint<F>>,
    pub state_linkage_constraints: Vec<(ColumnAddress, ColumnAddress)>,
    pub public_inputs: Vec<(BoundaryConstraintLocation, ColumnAddress)>,

    pub variable_mapping: BTreeMap<Variable, ColumnAddress>,

    pub scratch_space_size_for_witness_gen: usize,

    pub lazy_init_address_aux_vars: Option<ShuffleRamAuxComparisonSet>,

    // we need the field below to generate witness only
    pub memory_queries_timestamp_comparison_aux_vars: Vec<ColumnAddress>,
    pub batched_memory_access_timestamp_comparison_aux_vars: BatchedRamTimestampComparisonAuxVars,
    pub register_and_indirect_access_timestamp_comparison_aux_vars:
        RegisterAndIndirectAccessTimestampComparisonAuxVars,
    pub executor_family_circuit_next_timestamp_aux_var: Option<ColumnAddress>,

    pub executor_family_decoder_table_size: usize,
    pub trace_len: usize,
    pub table_offsets: Vec<u32>,
    pub total_tables_size: usize,
}

impl<F: PrimeField> CompiledCircuitArtifact<F> {
    pub fn as_verifier_compiled_artifact<'a>(
        &'a self,
        lookup_description_buffer: &'a mut Vec<
            VerifierCompiledLookupSetDescription<'a, F, COMMON_TABLE_WIDTH>,
        >,
        single_lookup_expressions_buffer: &'a mut Vec<VerifierCompiledLookupExpression<'a, F>>,
        degree_2_buffer: &'a mut Vec<VerifierCompiledDegree2Constraint<'a, F>>,
        degree_1_buffer: &'a mut Vec<VerifierCompiledDegree1Constraint<'a, F>>,
        indirect_accesses_buffer: &'a mut Vec<CompiledRegisterAndIndirectAccessDescription<'a>>,
    ) -> VerifierCompiledCircuitArtifact<'a, F> {
        assert!(degree_2_buffer.is_empty());
        assert!(degree_1_buffer.is_empty());

        for el in self.degree_2_constraints.iter() {
            degree_2_buffer.push(el.as_compiled());
        }

        for el in self.degree_1_constraints.iter() {
            degree_1_buffer.push(el.as_compiled());
        }

        assert!(self.trace_len.is_power_of_two());
        let trace_len_log2 = self.trace_len.trailing_zeros() as usize;

        VerifierCompiledCircuitArtifact {
            witness_layout: self
                .witness_layout
                .as_compiled(lookup_description_buffer, single_lookup_expressions_buffer),
            memory_layout: self.memory_layout.as_compiled(indirect_accesses_buffer),
            setup_layout: self.setup_layout,
            stage_2_layout: self.stage_2_layout,
            degree_2_constraints: &*degree_2_buffer,
            degree_1_constraints: &*degree_1_buffer,
            state_linkage_constraints: &self.state_linkage_constraints,
            public_inputs: &self.public_inputs,
            lazy_init_address_aux_vars: self.lazy_init_address_aux_vars,
            // memory_queries_timestamp_comparison_aux_vars: &self
            //     .memory_queries_timestamp_comparison_aux_vars,
            // batched_memory_access_timestamp_comparison_aux_vars: self
            //     .batched_memory_access_timestamp_comparison_aux_vars.as_compiled(),
            trace_len_log2,
        }
    }

    pub fn compute_num_quotient_terms(&self) -> usize {
        let mut lookup_description_buffer = vec![];
        let mut range_check_16_buffer = vec![];
        let mut degree_2_buffer = vec![];
        let mut degree_1_buffer = vec![];
        let mut indirects_buffer = vec![];

        self.as_verifier_compiled_artifact(
            &mut lookup_description_buffer,
            &mut range_check_16_buffer,
            &mut degree_2_buffer,
            &mut degree_1_buffer,
            &mut indirects_buffer,
        )
        .num_quotient_terms()
    }

    pub fn num_openings_at_z(&self) -> usize {
        let mut lookup_description_buffer = vec![];
        let mut range_check_16_buffer = vec![];
        let mut degree_2_buffer = vec![];
        let mut degree_1_buffer = vec![];
        let mut indirects_buffer = vec![];

        self.as_verifier_compiled_artifact(
            &mut lookup_description_buffer,
            &mut range_check_16_buffer,
            &mut degree_2_buffer,
            &mut degree_1_buffer,
            &mut indirects_buffer,
        )
        .num_openings_at_z()
    }

    pub fn num_openings_at_z_omega(&self) -> usize {
        let mut lookup_description_buffer = vec![];
        let mut range_check_16_buffer = vec![];
        let mut degree_2_buffer = vec![];
        let mut degree_1_buffer = vec![];
        let mut indirects_buffer = vec![];

        self.as_verifier_compiled_artifact(
            &mut lookup_description_buffer,
            &mut range_check_16_buffer,
            &mut degree_2_buffer,
            &mut degree_1_buffer,
            &mut indirects_buffer,
        )
        .num_openings_at_z_omega()
    }
}

#[track_caller]
fn layout_witness_subtree_variable_at_column(
    offset: usize,
    variable: Variable,
    all_variables_to_place: &mut BTreeSet<Variable>,
    layout: &mut BTreeMap<Variable, ColumnAddress>,
) -> ColumnAddress {
    assert!(
        all_variables_to_place.remove(&variable),
        "variable {:?} was already placed",
        variable
    );
    let address = ColumnAddress::WitnessSubtree(offset);
    let existing = layout.insert(variable, address);
    assert!(existing.is_none());

    address
}

#[track_caller]
fn layout_witness_subtree_variable(
    offset: &mut usize,
    variable: Variable,
    all_variables_to_place: &mut BTreeSet<Variable>,
    layout: &mut BTreeMap<Variable, ColumnAddress>,
) -> ColumnSet<1> {
    layout_witness_subtree_multiple_variables(offset, [variable], all_variables_to_place, layout)
}

#[track_caller]
fn layout_memory_subtree_variable(
    offset: &mut usize,
    variable: Variable,
    all_variables_to_place: &mut BTreeSet<Variable>,
    layout: &mut BTreeMap<Variable, ColumnAddress>,
) -> ColumnSet<1> {
    layout_memory_subtree_multiple_variables(offset, [variable], all_variables_to_place, layout)
}

#[track_caller]
fn layout_witness_subtree_multiple_variables<const N: usize>(
    offset: &mut usize,
    variables: [Variable; N],
    all_variables_to_place: &mut BTreeSet<Variable>,
    layout: &mut BTreeMap<Variable, ColumnAddress>,
) -> ColumnSet<N> {
    let mut place_offset = *offset;
    let columns = ColumnSet::layout_at(offset, 1);
    for variable in variables.into_iter() {
        let place = ColumnAddress::WitnessSubtree(place_offset);
        place_offset += 1;

        assert!(
            all_variables_to_place.remove(&variable),
            "variable {:?} was already placed",
            variable
        );
        let existing = layout.insert(variable, place);
        assert!(existing.is_none());
    }

    assert_eq!(place_offset, *offset);

    columns
}

#[track_caller]
fn layout_memory_subtree_multiple_variables<const N: usize>(
    offset: &mut usize,
    variables: [Variable; N],
    all_variables_to_place: &mut BTreeSet<Variable>,
    layout: &mut BTreeMap<Variable, ColumnAddress>,
) -> ColumnSet<N> {
    let mut place_offset = *offset;
    let columns = ColumnSet::layout_at(offset, 1);
    for variable in variables.into_iter() {
        let place = ColumnAddress::MemorySubtree(place_offset);
        place_offset += 1;

        assert!(
            all_variables_to_place.remove(&variable),
            "variable {:?} was already placed",
            variable
        );
        let existing = layout.insert(variable, place);
        assert!(existing.is_none());
    }

    assert_eq!(place_offset, *offset);

    columns
}
