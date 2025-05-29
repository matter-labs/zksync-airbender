use super::field::FieldNodeExpression;
use super::integer::FixedWidthIntegerNodeExpression;
use super::*;
use crate::cs::placeholder::Placeholder;
use crate::cs::witness_placer::WitnessMask;
use crate::one_row_compiler::Variable;
use ::field::PrimeField;
use std::collections::BTreeSet;

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum BoolNodeExpression<F: PrimeField> {
    Place(Variable),
    SubExpression(usize),
    Constant(bool),
    OracleValue {
        placeholder: Placeholder,
    },
    FromGenericInteger(Box<FixedWidthIntegerNodeExpression<F>>),
    FromGenericIntegerEquality {
        lhs: Box<FixedWidthIntegerNodeExpression<F>>,
        rhs: Box<FixedWidthIntegerNodeExpression<F>>,
    },
    FromGenericIntegerCarry {
        lhs: Box<FixedWidthIntegerNodeExpression<F>>,
        rhs: Box<FixedWidthIntegerNodeExpression<F>>,
    },
    FromGenericIntegerBorrow {
        lhs: Box<FixedWidthIntegerNodeExpression<F>>,
        rhs: Box<FixedWidthIntegerNodeExpression<F>>,
    },
    FromField(Box<FieldNodeExpression<F>>),
    FromFieldEquality {
        lhs: Box<FieldNodeExpression<F>>,
        rhs: Box<FieldNodeExpression<F>>,
    },
    And {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    Or {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    Select {
        selector: Box<Self>,
        if_true: Box<Self>,
        if_false: Box<Self>,
    },
    Negate(Box<Self>),
}

impl<F: PrimeField> BoolNodeExpression<F> {
    pub fn report_origins(
        &self,
        dst: &mut BTreeSet<Variable>,
        oracles: &mut BTreeSet<(Placeholder, usize)>,
        lookup_fn: &impl Fn(usize, usize) -> Vec<Expression<F>>,
    ) {
        match self {
            Self::Place(place) => {
                dst.insert(*place);
            }
            // the rest is recursive
            Self::Negate(inner) => {
                inner.report_origins(dst, oracles, lookup_fn);
            }
            Self::FromField(inner) => {
                inner.report_origins(dst, oracles, lookup_fn);
            }
            Self::FromGenericInteger(inner) => {
                inner.report_origins(dst, oracles, lookup_fn);
            }
            Self::OracleValue { placeholder } => {
                oracles.insert((*placeholder, 0));
            }
            // Binops
            Self::FromGenericIntegerEquality { lhs, rhs }
            | Self::FromGenericIntegerCarry { lhs, rhs }
            | Self::FromGenericIntegerBorrow { lhs, rhs } => {
                lhs.report_origins(dst, oracles, lookup_fn);
                rhs.report_origins(dst, oracles, lookup_fn);
            }
            Self::FromFieldEquality { lhs, rhs } => {
                lhs.report_origins(dst, oracles, lookup_fn);
                rhs.report_origins(dst, oracles, lookup_fn);
            }
            Self::And { lhs, rhs } | Self::Or { lhs, rhs } => {
                lhs.report_origins(dst, oracles, lookup_fn);
                rhs.report_origins(dst, oracles, lookup_fn);
            }
            Self::Select {
                selector,
                if_true,
                if_false,
            } => {
                selector.report_origins(dst, oracles, lookup_fn);
                if_true.report_origins(dst, oracles, lookup_fn);
                if_false.report_origins(dst, oracles, lookup_fn);
            }
            Self::Constant(..) => {}
            Self::SubExpression(..) => {
                unreachable!("must not be used after subexpression elimination")
            }
        }
    }

    pub fn make_subexpressions(
        &mut self,
        set: &mut SubexpressionsMapper<F>,
        lookup_fn: &impl Fn(usize, usize) -> Vec<Expression<F>>,
    ) {
        match self {
            Self::Place(_place) => {
                // Do nothing, it can not be subexpression
            }
            // the rest is recursive
            Self::Negate(inner) => {
                inner.make_subexpressions(set, lookup_fn);
                // set.add_boolean_subexprs(inner);
            }
            Self::FromField(inner) => {
                inner.make_subexpressions(set, lookup_fn);
                // set.add_field_subexprs(inner);
            }
            Self::FromGenericInteger(inner) => {
                inner.make_subexpressions(set, lookup_fn);
                // set.add_integer_subexprs(inner);
            }
            Self::OracleValue { .. } => {
                // nothing
            }
            // Binops
            Self::FromGenericIntegerEquality { lhs, rhs }
            | Self::FromGenericIntegerCarry { lhs, rhs }
            | Self::FromGenericIntegerBorrow { lhs, rhs } => {
                lhs.make_subexpressions(set, lookup_fn);
                rhs.make_subexpressions(set, lookup_fn);
                // set.add_integer_subexprs(lhs);
                // set.add_integer_subexprs(rhs);
            }
            Self::FromFieldEquality { lhs, rhs } => {
                lhs.make_subexpressions(set, lookup_fn);
                rhs.make_subexpressions(set, lookup_fn);
                // set.add_field_subexprs(lhs);
                // set.add_field_subexprs(rhs);
            }
            Self::And { lhs, rhs } | Self::Or { lhs, rhs } => {
                lhs.make_subexpressions(set, lookup_fn);
                rhs.make_subexpressions(set, lookup_fn);
                // set.add_boolean_subexprs(lhs);
                // set.add_boolean_subexprs(rhs);
            }
            Self::Select {
                selector,
                if_true,
                if_false,
            } => {
                selector.make_subexpressions(set, lookup_fn);
                if_true.make_subexpressions(set, lookup_fn);
                if_false.make_subexpressions(set, lookup_fn);
                // set.add_boolean_subexprs(selector);
                // set.add_boolean_subexprs(if_true);
                // set.add_boolean_subexprs(if_true);
            }
            Self::Constant(..) => {}
            Self::SubExpression(..) => {
                unreachable!("must not be used after subexpression elimination")
            }
        }
        set.add_boolean_subexprs(self);
    }
}

impl<F: PrimeField> WitnessMask for BoolNodeExpression<F> {
    fn and(&self, other: &Self) -> Self {
        let new_node = Self::And {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        new_node
    }
    fn or(&self, other: &Self) -> Self {
        let new_node = Self::Or {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        new_node
    }
    fn negate(&self) -> Self {
        Self::Negate(Box::new(self.clone()))
    }
    fn constant(value: bool) -> Self {
        Self::Constant(value)
    }
    fn select(mask: &Self, a: &Self, b: &Self) -> Self {
        let new_node = Self::Select {
            selector: Box::new(mask.clone()),
            if_true: Box::new(a.clone()),
            if_false: Box::new(b.clone()),
        };

        new_node
    }
    fn select_into(dst: &mut Self, mask: &Self, a: &Self, b: &Self) {
        *dst = Self::select(mask, a, b);
    }
}
