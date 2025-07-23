use super::*;
use super::{boolean::BoolNodeExpression, integer::FixedWidthIntegerNodeExpression};
use crate::cs::{placeholder::Placeholder, witness_placer::WitnessComputationalField};
use crate::one_row_compiler::Variable;
use ::field::PrimeField;
use std::collections::BTreeSet;

#[derive(Clone, Debug, Eq, serde::Serialize, serde::Deserialize)]
pub enum FieldNodeExpression<F: PrimeField> {
    Place(Variable),
    SubExpression(usize),
    Constant(F),
    FromInteger(Box<FixedWidthIntegerNodeExpression<F>>),
    FromMask(Box<BoolNodeExpression<F>>),
    OracleValue {
        placeholder: Placeholder,
        subindex: usize,
    },
    Add {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    Sub {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    Mul {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    AddProduct {
        additive_term: Box<Self>,
        mul_0: Box<Self>,
        mul_1: Box<Self>,
    },
    Select {
        selector: Box<BoolNodeExpression<F>>,
        if_true: Box<Self>,
        if_false: Box<Self>,
    },
    InverseUnchecked(Box<Self>),
    InverseOrZero(Box<Self>),
    LookupOutput {
        lookup_idx: usize,
        output_idx: usize,
    },
    MaybeLookupOutput {
        lookup_idx: usize,
        output_idx: usize,
    },
}

impl<F: PrimeField> PartialEq for FieldNodeExpression<F> {
    #[inline(never)]
    fn eq(&self, other: &Self) -> bool {
        use FieldNodeExpression::*;
        match (self, other) {
            (Place(a), Place(b)) => a == b,
            (SubExpression(a), SubExpression(b)) => a == b,
            (Constant(a), Constant(b)) => a == b,
            (FromInteger(a), FromInteger(b)) => a == b,
            (FromMask(a), FromMask(b)) => a == b,
            (
                OracleValue {
                    placeholder: p1,
                    subindex: s1,
                },
                OracleValue {
                    placeholder: p2,
                    subindex: s2,
                },
            ) => p1 == p2 && s1 == s2,
            (Add { lhs: l1, rhs: r1 }, Add { lhs: l2, rhs: r2 }) => l1 == l2 && r1 == r2,
            (Sub { lhs: l1, rhs: r1 }, Sub { lhs: l2, rhs: r2 }) => l1 == l2 && r1 == r2,
            (Mul { lhs: l1, rhs: r1 }, Mul { lhs: l2, rhs: r2 }) => l1 == l2 && r1 == r2,
            (
                AddProduct {
                    additive_term: a1,
                    mul_0: m01,
                    mul_1: m11,
                },
                AddProduct {
                    additive_term: a2,
                    mul_0: m02,
                    mul_1: m12,
                },
            ) => a1 == a2 && m01 == m02 && m11 == m12,
            (
                Select {
                    selector: s1,
                    if_true: t1,
                    if_false: f1,
                },
                Select {
                    selector: s2,
                    if_true: t2,
                    if_false: f2,
                },
            ) => s1 == s2 && t1 == t2 && f1 == f2,
            (InverseUnchecked(a), InverseUnchecked(b)) => a == b,
            (InverseOrZero(a), InverseOrZero(b)) => a == b,
            (
                LookupOutput {
                    lookup_idx: i1,
                    output_idx: o1,
                },
                LookupOutput {
                    lookup_idx: i2,
                    output_idx: o2,
                },
            ) => i1 == i2 && o1 == o2,
            (
                MaybeLookupOutput {
                    lookup_idx: i1,
                    output_idx: o1,
                },
                MaybeLookupOutput {
                    lookup_idx: i2,
                    output_idx: o2,
                },
            ) => i1 == i2 && o1 == o2,
            _ => false,
        }
    }
}

use core::hash::{Hash, Hasher};

impl<F: PrimeField> Hash for FieldNodeExpression<F> {
    #[inline(never)]
    fn hash<H: Hasher>(&self, state: &mut H) {
        use FieldNodeExpression::*;
        std::mem::discriminant(self).hash(state); // include variant tag
        match self {
            Place(v) => v.hash(state),
            SubExpression(i) => i.hash(state),
            Constant(c) => c.hash(state),
            FromInteger(e) => e.hash(state), // calls FixedWidthIntegerNodeExpression::hash
            FromMask(b) => b.hash(state),
            OracleValue {
                placeholder,
                subindex,
            } => {
                placeholder.hash(state);
                subindex.hash(state);
            }
            Add { lhs, rhs } | Sub { lhs, rhs } | Mul { lhs, rhs } => {
                lhs.hash(state);
                rhs.hash(state);
            }
            AddProduct {
                additive_term,
                mul_0,
                mul_1,
            } => {
                additive_term.hash(state);
                mul_0.hash(state);
                mul_1.hash(state);
            }
            Select {
                selector,
                if_true,
                if_false,
            } => {
                selector.hash(state);
                if_true.hash(state);
                if_false.hash(state);
            }
            InverseUnchecked(x) | InverseOrZero(x) => x.hash(state),
            LookupOutput {
                lookup_idx,
                output_idx,
            }
            | MaybeLookupOutput {
                lookup_idx,
                output_idx,
            } => {
                lookup_idx.hash(state);
                output_idx.hash(state);
            }
        }
    }
}

impl<F: PrimeField> FieldNodeExpression<F> {
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
            Self::FromInteger(inner) => {
                inner.report_origins(dst, oracles, lookup_fn);
            }
            Self::FromMask(inner) => {
                inner.report_origins(dst, oracles, lookup_fn);
            }
            Self::InverseUnchecked(inner) => {
                inner.report_origins(dst, oracles, lookup_fn);
            }
            Self::InverseOrZero(inner) => {
                inner.report_origins(dst, oracles, lookup_fn);
            }
            Self::OracleValue {
                placeholder,
                subindex,
            } => {
                oracles.insert((*placeholder, *subindex));
            }
            // Binops
            Self::Add { lhs, rhs } | Self::Sub { lhs, rhs } | Self::Mul { lhs, rhs } => {
                lhs.report_origins(dst, oracles, lookup_fn);
                rhs.report_origins(dst, oracles, lookup_fn);
            }
            Self::AddProduct {
                additive_term,
                mul_0,
                mul_1,
            } => {
                additive_term.report_origins(dst, oracles, lookup_fn);
                mul_0.report_origins(dst, oracles, lookup_fn);
                mul_1.report_origins(dst, oracles, lookup_fn);
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
            Self::LookupOutput {
                lookup_idx,
                output_idx,
            } => {
                let suborigins = (lookup_fn)(*lookup_idx, *output_idx);
                for el in suborigins.into_iter() {
                    el.report_origins(dst, oracles, lookup_fn);
                }
            }
            Self::MaybeLookupOutput {
                lookup_idx,
                output_idx,
            } => {
                let suborigins = (lookup_fn)(*lookup_idx, *output_idx);
                for el in suborigins.into_iter() {
                    el.report_origins(dst, oracles, lookup_fn);
                }
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
                // nothing
            }
            // the rest is recursive
            Self::FromInteger(inner) => {
                inner.make_subexpressions(set, lookup_fn);
                // set.add_integer_subexprs(inner);
            }
            Self::FromMask(inner) => {
                inner.make_subexpressions(set, lookup_fn);
                // set.add_boolean_subexprs(inner);
            }
            Self::InverseUnchecked(inner) => {
                inner.make_subexpressions(set, lookup_fn);
                // set.add_field_subexprs(inner);
            }
            Self::InverseOrZero(inner) => {
                inner.make_subexpressions(set, lookup_fn);
                // set.add_field_subexprs(inner);
            }
            Self::OracleValue {
                placeholder: _,
                subindex: _,
            } => {
                // nothing
            }
            // Binops
            Self::Add { lhs, rhs } | Self::Sub { lhs, rhs } | Self::Mul { lhs, rhs } => {
                lhs.make_subexpressions(set, lookup_fn);
                rhs.make_subexpressions(set, lookup_fn);
                // set.add_field_subexprs(lhs);
                // set.add_field_subexprs(rhs);
            }
            Self::AddProduct {
                additive_term,
                mul_0,
                mul_1,
            } => {
                additive_term.make_subexpressions(set, lookup_fn);
                mul_0.make_subexpressions(set, lookup_fn);
                mul_1.make_subexpressions(set, lookup_fn);
                // set.add_field_subexprs(additive_term);
                // set.add_field_subexprs(mul_0);
                // set.add_field_subexprs(mul_1);
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
                // set.add_field_subexprs(if_true);
                // set.add_field_subexprs(if_true);
            }
            Self::LookupOutput {
                lookup_idx: _,
                output_idx: _,
            } => {
                // nothing - we do not peek further
            }
            Self::MaybeLookupOutput {
                lookup_idx: _,
                output_idx: _,
            } => {
                // nothing - we do not peek further
            }
            Self::Constant(..) => {}
            Self::SubExpression(..) => {
                unreachable!("must not be used after subexpression elimination")
            }
        }
        set.add_field_subexprs(self);
    }
}

impl<F: PrimeField> WitnessComputationalField<F> for FieldNodeExpression<F> {
    type Mask = BoolNodeExpression<F>;
    type IntegerRepresentation = FixedWidthIntegerNodeExpression<F>;

    fn add_assign(&mut self, other: &Self) {
        let new_node = Self::Add {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        *self = new_node;
    }
    fn sub_assign(&mut self, other: &Self) {
        let new_node = Self::Sub {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        *self = new_node;
    }
    fn mul_assign(&mut self, other: &Self) {
        let new_node = Self::Mul {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        *self = new_node;
    }
    fn fused_mul_add_assign(&mut self, a: &Self, b: &Self) {
        let new_node = Self::AddProduct {
            additive_term: Box::new(b.clone()),
            mul_0: Box::new(self.clone()),
            mul_1: Box::new(a.clone()),
        };

        *self = new_node;
    }
    fn add_assign_product(&mut self, a: &Self, b: &Self) {
        let new_node = Self::AddProduct {
            additive_term: Box::new(self.clone()),
            mul_0: Box::new(a.clone()),
            mul_1: Box::new(b.clone()),
        };

        *self = new_node;
    }
    fn add_assign_masked(&mut self, mask: &Self::Mask, other: &Self) {
        let new_node = Self::Add {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };
        let new_node = Self::Select {
            selector: Box::new(mask.clone()),
            if_true: Box::new(new_node),
            if_false: Box::new(self.clone()),
        };

        *self = new_node;
    }
    fn add_assign_product_masked(&mut self, mask: &Self::Mask, a: &Self, b: &Self) {
        let new_node = Self::AddProduct {
            additive_term: Box::new(self.clone()),
            mul_0: Box::new(a.clone()),
            mul_1: Box::new(b.clone()),
        };

        let new_node = Self::Select {
            selector: Box::new(mask.clone()),
            if_true: Box::new(new_node),
            if_false: Box::new(self.clone()),
        };

        *self = new_node;
    }
    fn select(mask: &Self::Mask, a: &Self, b: &Self) -> Self {
        let new_node = Self::Select {
            selector: Box::new(mask.clone()),
            if_true: Box::new(a.clone()),
            if_false: Box::new(b.clone()),
        };

        new_node
    }
    fn select_into(dst: &mut Self, mask: &Self::Mask, a: &Self, b: &Self) {
        *dst = Self::select(mask, a, b);
    }
    fn into_mask(self) -> Self::Mask {
        BoolNodeExpression::FromField(Box::new(self))
    }
    fn from_mask(value: Self::Mask) -> Self {
        Self::FromMask(Box::new(value))
    }
    fn is_zero(&self) -> Self::Mask {
        BoolNodeExpression::FromFieldEquality {
            lhs: Box::new(self.clone()),
            rhs: Box::new(Self::Constant(F::ZERO)),
        }
    }
    fn is_one(&self) -> Self::Mask {
        BoolNodeExpression::FromFieldEquality {
            lhs: Box::new(self.clone()),
            rhs: Box::new(Self::Constant(F::ONE)),
        }
    }
    fn constant(value: F) -> Self {
        Self::Constant(value)
    }
    fn equal(&self, other: &Self) -> Self::Mask {
        BoolNodeExpression::FromFieldEquality {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        }
    }
    fn inverse(&self) -> Self {
        Self::InverseUnchecked(Box::new(self.clone()))
    }
    fn inverse_or_zero(&self) -> Self {
        Self::InverseOrZero(Box::new(self.clone()))
    }
    fn as_integer(self) -> Self::IntegerRepresentation {
        FixedWidthIntegerNodeExpression::U32FromField(Box::new(self))
    }
    fn from_integer(value: Self::IntegerRepresentation) -> Self {
        Self::FromInteger(Box::new(value))
    }
}
