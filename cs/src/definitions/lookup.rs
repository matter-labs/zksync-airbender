use super::*;
use alloc::boxed::Box;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum TableIndex {
    Variable(ColumnAddress),
    Constant(TableType),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LookupInput<F: PrimeField> {
    Variable(Variable),
    Expression {
        linear_terms: Vec<(F, Variable)>,
        constant_coeff: F,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VerifierCompiledLookupExpression<'a, F: PrimeField> {
    Variable(ColumnAddress),
    Expression(VerifierCompiledDegree1Constraint<'a, F>),
}

pub type StaticVerifierCompiledLookupExpression<F: PrimeField> =
    VerifierCompiledLookupExpression<'static, F>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VerifierCompiledLookupSetDescription<'a, F: PrimeField, const N: usize> {
    pub input_columns: [VerifierCompiledLookupExpression<'a, F>; N],
    pub table_index: TableIndex,
}

#[derive(
    Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub enum LookupExpression<F: PrimeField> {
    Variable(ColumnAddress),
    Expression(CompiledDegree1Constraint<F>),
}

impl<F: PrimeField> LookupExpression<F> {
    pub fn zero() -> Self {
        Self::Expression(CompiledDegree1Constraint {
            linear_terms: Box::new([]),
            constant_term: F::ZERO,
        })
    }

    pub fn as_compiled<'a>(&'a self) -> VerifierCompiledLookupExpression<'a, F> {
        match self {
            LookupExpression::Variable(var) => VerifierCompiledLookupExpression::Variable(*var),
            LookupExpression::Expression(constraint) => {
                VerifierCompiledLookupExpression::Expression(constraint.as_compiled())
            }
        }
    }
}

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct LookupSetDescription<F: PrimeField, const N: usize> {
    #[serde(bound(deserialize = "[LookupExpression<F>; N]: serde::Deserialize<'de>"))]
    #[serde(bound(serialize = "[LookupExpression<F>; N]: serde::Serialize"))]
    pub input_columns: [LookupExpression<F>; N],
    pub table_index: TableIndex,
}

impl<F: PrimeField, const N: usize> LookupSetDescription<F, N> {
    pub fn as_compiled<'a>(&'a self) -> VerifierCompiledLookupSetDescription<'a, F, N> {
        VerifierCompiledLookupSetDescription {
            input_columns: core::array::from_fn(|i| match &self.input_columns[i] {
                LookupExpression::Variable(var) => VerifierCompiledLookupExpression::Variable(*var),
                LookupExpression::Expression(constraint) => {
                    VerifierCompiledLookupExpression::Expression(constraint.as_compiled())
                }
            }),
            table_index: self.table_index,
        }
    }
}

#[derive(Clone, Copy, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub struct OptimizedOraclesForLookupWidth1 {
    pub num_pairs: usize,
    pub base_field_oracles: AlignedColumnSet<1>,
    pub ext_4_field_oracles: AlignedColumnSet<4>,
}

impl OptimizedOraclesForLookupWidth1 {
    pub const fn empty() -> Self {
        Self {
            num_pairs: 0,
            base_field_oracles: AlignedColumnSet::empty(),
            ext_4_field_oracles: AlignedColumnSet::empty(),
        }
    }
    pub fn get_ext4_poly_index_in_openings(
        &self,
        argument_index: usize,
        stage_2_layout: &LookupAndMemoryArgumentLayout,
    ) -> usize {
        assert!(argument_index < self.ext_4_field_oracles.num_elements);
        let absolute_ext4_poly_index = self.ext_4_field_oracles.get_range(argument_index).start
            - stage_2_layout.ext4_polys_offset;
        assert_eq!(absolute_ext4_poly_index % 4, 0);
        let absolute_ext4_poly_index = absolute_ext4_poly_index / 4;

        stage_2_layout.num_base_field_polys() + absolute_ext4_poly_index
    }
}
