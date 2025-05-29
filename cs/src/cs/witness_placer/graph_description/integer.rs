use super::boolean::BoolNodeExpression;
use super::field::FieldNodeExpression;
use super::*;
use crate::cs::placeholder::Placeholder;
use crate::cs::witness_placer::{
    WitnessComputationCore, WitnessComputationalI32, WitnessComputationalInteger,
    WitnessComputationalU16, WitnessComputationalU32, WitnessComputationalU8,
};
use crate::one_row_compiler::Variable;
use ::field::PrimeField;
use core::fmt::Debug;
use std::collections::BTreeSet;

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum FixedWidthIntegerNodeExpression<F: PrimeField> {
    U8Place(Variable),
    U16Place(Variable),
    U8SubExpression(usize),
    U16SubExpression(usize),
    U32SubExpression(usize),
    U32OracleValue {
        placeholder: Placeholder,
    },
    U16OracleValue {
        placeholder: Placeholder,
    },
    U8OracleValue {
        placeholder: Placeholder,
    },
    ConstantU8(u8),
    ConstantU16(u16),
    ConstantU32(u32),
    U32FromMask(Box<BoolNodeExpression<F>>),
    U32FromField(Box<FieldNodeExpression<F>>),
    WidenFromU8(Box<Self>),
    WidenFromU16(Box<Self>),
    TruncateFromU16(Box<Self>),
    TruncateFromU32(Box<Self>),
    I32FromU32(Box<Self>),
    U32FromI32(Box<Self>),
    WrappingAdd {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    WrappingSub {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    WrappingShl {
        lhs: Box<Self>,
        magnitude: u32,
    },
    WrappingShr {
        lhs: Box<Self>,
        magnitude: u32,
    },
    MulLow {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    MulHigh {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    AddProduct {
        additive_term: Box<Self>,
        mul_0: Box<Self>,
        mul_1: Box<Self>,
    },
    Select {
        selector: BoolNodeExpression<F>,
        if_true: Box<Self>,
        if_false: Box<Self>,
    },
    LowestBits {
        value: Box<Self>,
        num_bits: u32,
    },
    DivAssumeNonzero {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    RemAssumeNonzero {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    SignedDivAssumeNonzeroNoOverflowBits {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    SignedRemAssumeNonzeroNoOverflowBits {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    SignedMulLowBits {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    SignedMulHighBits {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    SignedByUnsignedMulLowBits {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    SignedByUnsignedMulHighBits {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
}

impl<F: PrimeField> FixedWidthIntegerNodeExpression<F> {
    pub fn bit_width(&self) -> u32 {
        match self {
            Self::U8Place(_place) => 8u32,
            Self::U16Place(_place) => 16u32,
            // the rest is recursive
            Self::U32FromMask(_inner) => 32u32,
            Self::U32FromField(_inner) => 32u32,
            Self::TruncateFromU32(inner) => {
                assert_eq!(inner.bit_width(), 32);
                16u32
            }
            Self::WidenFromU8(inner) => {
                assert_eq!(inner.bit_width(), 8);
                16u32
            }
            Self::TruncateFromU16(inner) => {
                assert_eq!(inner.bit_width(), 16, "{:?}", self);
                8u32
            }
            Self::WidenFromU16(inner) => {
                assert_eq!(inner.bit_width(), 16);
                32u32
            }
            Self::I32FromU32(inner) | Self::U32FromI32(inner) => {
                assert_eq!(inner.bit_width(), 32);
                32u32
            }
            Self::U32OracleValue { placeholder: _ } => 32,
            Self::U16OracleValue { placeholder: _ } => 16,
            Self::U8OracleValue { placeholder: _ } => 8,
            // Binops
            Self::WrappingAdd { lhs, rhs }
            | Self::WrappingSub { lhs, rhs }
            | Self::MulLow { lhs, rhs }
            | Self::MulHigh { lhs, rhs } => {
                let lhs_width = lhs.bit_width();
                let rhs_width = rhs.bit_width();
                assert_eq!(lhs_width, rhs_width, "{:?}", self);

                rhs_width
            }
            Self::WrappingShl { lhs, .. } | Self::WrappingShr { lhs, .. } => {
                let lhs_width = lhs.bit_width();

                lhs_width
            }
            Self::DivAssumeNonzero { lhs, rhs }
            | Self::RemAssumeNonzero { lhs, rhs }
            | Self::SignedDivAssumeNonzeroNoOverflowBits { lhs, rhs }
            | Self::SignedRemAssumeNonzeroNoOverflowBits { lhs, rhs }
            | Self::SignedMulLowBits { lhs, rhs }
            | Self::SignedMulHighBits { lhs, rhs }
            | Self::SignedByUnsignedMulLowBits { lhs, rhs }
            | Self::SignedByUnsignedMulHighBits { lhs, rhs } => {
                let lhs_width = lhs.bit_width();
                let rhs_width = rhs.bit_width();
                assert_eq!(lhs_width, rhs_width);
                assert_eq!(lhs_width, 32);

                32u32
            }
            Self::AddProduct {
                additive_term,
                mul_0,
                mul_1,
            } => {
                let additive_width = additive_term.bit_width();
                let mul_0_width = mul_0.bit_width();
                let mul_1_width = mul_1.bit_width();
                assert_eq!(additive_width, mul_0_width);
                assert_eq!(additive_width, mul_1_width);

                additive_width
            }
            Self::Select {
                selector: _,
                if_true,
                if_false,
            } => {
                let lhs_width = if_true.bit_width();
                let rhs_width = if_false.bit_width();
                assert_eq!(lhs_width, rhs_width);

                rhs_width
            }
            Self::LowestBits { value, .. } => value.bit_width(),
            Self::ConstantU8(..) => 8u32,
            Self::ConstantU16(..) => 16u32,
            Self::ConstantU32(..) => 32u32,
            Self::U8SubExpression(..) => 8u32,
            Self::U16SubExpression(..) => 16u32,
            Self::U32SubExpression(..) => 32u32,
        }
    }

    pub fn report_origins(
        &self,
        dst: &mut BTreeSet<Variable>,
        oracles: &mut BTreeSet<(Placeholder, usize)>,
        lookup_fn: &impl Fn(usize, usize) -> Vec<Expression<F>>,
    ) {
        match self {
            Self::U8Place(place) => {
                dst.insert(*place);
            }
            Self::U16Place(place) => {
                dst.insert(*place);
            }
            // the rest is recursive
            Self::U32FromMask(inner) => {
                inner.report_origins(dst, oracles, lookup_fn);
            }
            Self::U32FromField(inner) => {
                inner.report_origins(dst, oracles, lookup_fn);
            }
            Self::U32OracleValue { placeholder } => {
                oracles.insert((*placeholder, 0));
            }
            Self::U16OracleValue { placeholder } => {
                oracles.insert((*placeholder, 0));
            }
            Self::U8OracleValue { placeholder } => {
                oracles.insert((*placeholder, 0));
            }
            Self::WidenFromU8(inner)
            | Self::WidenFromU16(inner)
            | Self::TruncateFromU16(inner)
            | Self::TruncateFromU32(inner)
            | Self::I32FromU32(inner)
            | Self::U32FromI32(inner)
            | Self::WrappingShl { lhs: inner, .. }
            | Self::WrappingShr { lhs: inner, .. } => {
                inner.report_origins(dst, oracles, lookup_fn);
            }
            // Binops
            Self::WrappingAdd { lhs, rhs }
            | Self::WrappingSub { lhs, rhs }
            | Self::MulLow { lhs, rhs }
            | Self::MulHigh { lhs, rhs }
            | Self::DivAssumeNonzero { lhs, rhs }
            | Self::RemAssumeNonzero { lhs, rhs }
            | Self::SignedDivAssumeNonzeroNoOverflowBits { lhs, rhs }
            | Self::SignedRemAssumeNonzeroNoOverflowBits { lhs, rhs }
            | Self::SignedMulLowBits { lhs, rhs }
            | Self::SignedMulHighBits { lhs, rhs }
            | Self::SignedByUnsignedMulLowBits { lhs, rhs }
            | Self::SignedByUnsignedMulHighBits { lhs, rhs } => {
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
            Self::LowestBits { value, .. } => {
                value.report_origins(dst, oracles, lookup_fn);
            }
            Self::ConstantU8(..) | Self::ConstantU16(..) | Self::ConstantU32(..) => {}
            Self::U8SubExpression(..) | Self::U16SubExpression(..) | Self::U32SubExpression(..) => {
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
            Self::U8Place(_place) => {
                // nothing
            }
            Self::U16Place(_place) => {
                // nothing
            }
            // the rest is recursive
            Self::U32FromMask(inner) => {
                inner.make_subexpressions(set, lookup_fn);
                // set.add_boolean_subexprs(inner);
            }
            Self::U32FromField(inner) => {
                inner.make_subexpressions(set, lookup_fn);
                // set.add_field_subexprs(inner);
            }
            Self::U32OracleValue { placeholder: _ } => {
                // nothing
            }
            Self::U16OracleValue { placeholder: _ } => {
                // nothing
            }
            Self::U8OracleValue { placeholder: _ } => {
                // nothing
            }
            Self::WidenFromU8(inner)
            | Self::WidenFromU16(inner)
            | Self::TruncateFromU16(inner)
            | Self::TruncateFromU32(inner)
            | Self::I32FromU32(inner)
            | Self::U32FromI32(inner)
            | Self::WrappingShl { lhs: inner, .. }
            | Self::WrappingShr { lhs: inner, .. } => {
                inner.make_subexpressions(set, lookup_fn);
                // set.add_integer_subexprs(inner);
            }
            // Binops
            Self::WrappingAdd { lhs, rhs }
            | Self::WrappingSub { lhs, rhs }
            | Self::MulLow { lhs, rhs }
            | Self::MulHigh { lhs, rhs }
            | Self::DivAssumeNonzero { lhs, rhs }
            | Self::RemAssumeNonzero { lhs, rhs }
            | Self::SignedDivAssumeNonzeroNoOverflowBits { lhs, rhs }
            | Self::SignedRemAssumeNonzeroNoOverflowBits { lhs, rhs }
            | Self::SignedMulLowBits { lhs, rhs }
            | Self::SignedMulHighBits { lhs, rhs }
            | Self::SignedByUnsignedMulLowBits { lhs, rhs }
            | Self::SignedByUnsignedMulHighBits { lhs, rhs } => {
                lhs.make_subexpressions(set, lookup_fn);
                rhs.make_subexpressions(set, lookup_fn);
                // set.add_integer_subexprs(lhs);
                // set.add_integer_subexprs(rhs);
            }
            Self::AddProduct {
                additive_term,
                mul_0,
                mul_1,
            } => {
                additive_term.make_subexpressions(set, lookup_fn);
                mul_0.make_subexpressions(set, lookup_fn);
                mul_1.make_subexpressions(set, lookup_fn);
                // set.add_integer_subexprs(additive_term);
                // set.add_integer_subexprs(mul_0);
                // set.add_integer_subexprs(mul_1);
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
                // set.add_integer_subexprs(if_true);
                // set.add_integer_subexprs(if_true);
            }
            Self::LowestBits { value, .. } => {
                value.make_subexpressions(set, lookup_fn);
                // set.add_integer_subexprs(value);
            }
            Self::ConstantU8(..) | Self::ConstantU16(..) | Self::ConstantU32(..) => {}
            Self::U8SubExpression(..) | Self::U16SubExpression(..) | Self::U32SubExpression(..) => {
                unreachable!("must not be used after subexpression elimination")
            }
        }
        set.add_integer_subexprs(self);
    }
}

impl<F: PrimeField> WitnessComputationCore for FixedWidthIntegerNodeExpression<F> {
    type Mask = BoolNodeExpression<F>;

    fn from_mask(value: Self::Mask) -> Self {
        Self::U32FromMask(Box::new(value))
    }

    fn add_assign(&mut self, other: &Self) {
        let new_node = Self::WrappingAdd {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        *self = new_node;
    }
    fn sub_assign(&mut self, other: &Self) {
        let new_node = Self::WrappingSub {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        *self = new_node;
    }
    fn add_assign_masked(&mut self, mask: &Self::Mask, other: &Self) {
        let new_node = Self::WrappingAdd {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };
        let new_node = Self::Select {
            selector: mask.clone(),
            if_true: Box::new(new_node),
            if_false: Box::new(self.clone()),
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
    fn add_assign_product_masked(&mut self, mask: &Self::Mask, a: &Self, b: &Self) {
        let new_node = Self::AddProduct {
            additive_term: Box::new(self.clone()),
            mul_0: Box::new(a.clone()),
            mul_1: Box::new(b.clone()),
        };

        let new_node = Self::Select {
            selector: mask.clone(),
            if_true: Box::new(new_node),
            if_false: Box::new(self.clone()),
        };

        *self = new_node;
    }
    fn select(mask: &Self::Mask, a: &Self, b: &Self) -> Self {
        let new_node = Self::Select {
            selector: mask.clone(),
            if_true: Box::new(a.clone()),
            if_false: Box::new(b.clone()),
        };

        new_node
    }
    fn select_into(dst: &mut Self, mask: &Self::Mask, a: &Self, b: &Self) {
        *dst = Self::select(mask, a, b);
    }
    fn into_mask(self) -> Self::Mask {
        BoolNodeExpression::FromGenericInteger(Box::new(self.clone()))
    }
}

impl<F: PrimeField> WitnessComputationalInteger<u8> for FixedWidthIntegerNodeExpression<F> {
    fn is_zero(&self) -> Self::Mask {
        WitnessComputationalInteger::<u8>::equal(self, &Self::ConstantU8(0))
    }
    fn is_one(&self) -> Self::Mask {
        WitnessComputationalInteger::<u8>::equal(self, &Self::ConstantU8(1))
    }
    fn constant(value: u8) -> Self {
        Self::ConstantU8(value)
    }
    fn equal(&self, other: &Self) -> Self::Mask {
        BoolNodeExpression::FromGenericIntegerEquality {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        }
    }
    fn overflowing_add(&self, other: &Self) -> (Self, Self::Mask) {
        let integer = Self::WrappingAdd {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };
        let carry = BoolNodeExpression::FromGenericIntegerCarry {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        (integer, carry)
    }
    fn overflowing_sub(&self, other: &Self) -> (Self, Self::Mask) {
        let integer = Self::WrappingSub {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };
        let carry = BoolNodeExpression::FromGenericIntegerBorrow {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        (integer, carry)
    }
    fn overflowing_add_with_carry(&self, other: &Self, carry: &Self::Mask) -> (Self, Self::Mask) {
        // we will let optimizer to handle this
        let carry = Self::TruncateFromU16(Box::new(Self::TruncateFromU32(Box::new(
            Self::from_mask(carry.clone()),
        ))));
        let (t, of0) = WitnessComputationalInteger::<u8>::overflowing_add(self, other);
        let (t, of1) = WitnessComputationalInteger::<u8>::overflowing_add(&t, &carry);

        let carry = BoolNodeExpression::Or {
            lhs: Box::new(of0),
            rhs: Box::new(of1),
        };
        (t, carry)
    }
    fn overflowing_sub_with_borrow(&self, other: &Self, borrow: &Self::Mask) -> (Self, Self::Mask) {
        // we will let optimizer to handle this
        let borrow = Self::TruncateFromU16(Box::new(Self::TruncateFromU32(Box::new(
            Self::from_mask(borrow.clone()),
        ))));
        let (t, of0) = WitnessComputationalInteger::<u8>::overflowing_sub(self, other);
        let (t, of1) = WitnessComputationalInteger::<u8>::overflowing_sub(&t, &borrow);

        let borrow = BoolNodeExpression::Or {
            lhs: Box::new(of0),
            rhs: Box::new(of1),
        };
        (t, borrow)
    }
    fn shl(&self, shift_magnitude: u32) -> Self {
        Self::WrappingShl {
            lhs: Box::new(self.clone()),
            magnitude: shift_magnitude,
        }
    }
    fn shr(&self, shift_magnitude: u32) -> Self {
        Self::WrappingShr {
            lhs: Box::new(self.clone()),
            magnitude: shift_magnitude,
        }
    }
    fn get_bit(&self, bit_idx: u32) -> Self::Mask {
        let src = if bit_idx == 0 {
            self.clone()
        } else {
            WitnessComputationalInteger::<u8>::shr(self, bit_idx)
        };
        let lowest_bit = WitnessComputationalInteger::<u8>::get_lowest_bits(&src, 1);

        BoolNodeExpression::FromGenericInteger(Box::new(lowest_bit))
    }
    fn equal_to_constant(&self, value: u8) -> Self::Mask {
        WitnessComputationalInteger::<u8>::equal(self, &Self::ConstantU8(value))
    }
    fn get_lowest_bits(&self, num_bits: u32) -> Self {
        Self::LowestBits {
            value: Box::new(self.clone()),
            num_bits,
        }
    }
}

impl<F: PrimeField> WitnessComputationalInteger<u16> for FixedWidthIntegerNodeExpression<F> {
    fn is_zero(&self) -> Self::Mask {
        WitnessComputationalInteger::<u16>::equal(self, &Self::ConstantU16(0))
    }
    fn is_one(&self) -> Self::Mask {
        WitnessComputationalInteger::<u16>::equal(self, &Self::ConstantU16(1))
    }
    fn constant(value: u16) -> Self {
        Self::ConstantU16(value)
    }
    fn equal(&self, other: &Self) -> Self::Mask {
        BoolNodeExpression::FromGenericIntegerEquality {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        }
    }
    fn overflowing_add(&self, other: &Self) -> (Self, Self::Mask) {
        let integer = Self::WrappingAdd {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };
        let carry = BoolNodeExpression::FromGenericIntegerCarry {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        (integer, carry)
    }
    fn overflowing_sub(&self, other: &Self) -> (Self, Self::Mask) {
        let integer = Self::WrappingSub {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };
        let carry = BoolNodeExpression::FromGenericIntegerBorrow {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        (integer, carry)
    }
    fn overflowing_add_with_carry(&self, other: &Self, carry: &Self::Mask) -> (Self, Self::Mask) {
        // we will let optimizer to handle this
        let carry = Self::TruncateFromU32(Box::new(Self::from_mask(carry.clone())));
        let (t, of0) = WitnessComputationalInteger::<u16>::overflowing_add(self, other);
        let (t, of1) = WitnessComputationalInteger::<u16>::overflowing_add(&t, &carry);

        let carry = BoolNodeExpression::Or {
            lhs: Box::new(of0),
            rhs: Box::new(of1),
        };
        (t, carry)
    }
    fn overflowing_sub_with_borrow(&self, other: &Self, borrow: &Self::Mask) -> (Self, Self::Mask) {
        // we will let optimizer to handle this
        let borrow = Self::TruncateFromU32(Box::new(Self::from_mask(borrow.clone())));
        let (t, of0) = WitnessComputationalInteger::<u16>::overflowing_sub(self, other);
        let (t, of1) = WitnessComputationalInteger::<u16>::overflowing_sub(&t, &borrow);

        let borrow = BoolNodeExpression::Or {
            lhs: Box::new(of0),
            rhs: Box::new(of1),
        };
        (t, borrow)
    }
    fn shl(&self, shift_magnitude: u32) -> Self {
        Self::WrappingShl {
            lhs: Box::new(self.clone()),
            magnitude: shift_magnitude,
        }
    }
    fn shr(&self, shift_magnitude: u32) -> Self {
        Self::WrappingShr {
            lhs: Box::new(self.clone()),
            magnitude: shift_magnitude,
        }
    }
    fn get_bit(&self, bit_idx: u32) -> Self::Mask {
        let src = if bit_idx == 0 {
            self.clone()
        } else {
            WitnessComputationalInteger::<u16>::shr(self, bit_idx)
        };
        let lowest_bit = WitnessComputationalInteger::<u16>::get_lowest_bits(&src, 1);

        BoolNodeExpression::FromGenericInteger(Box::new(lowest_bit))
    }
    fn equal_to_constant(&self, value: u16) -> Self::Mask {
        WitnessComputationalInteger::<u16>::equal(self, &Self::ConstantU16(value))
    }
    fn get_lowest_bits(&self, num_bits: u32) -> Self {
        Self::LowestBits {
            value: Box::new(self.clone()),
            num_bits,
        }
    }
}

impl<F: PrimeField> WitnessComputationalInteger<u32> for FixedWidthIntegerNodeExpression<F> {
    fn is_zero(&self) -> Self::Mask {
        WitnessComputationalInteger::<u32>::equal(self, &Self::ConstantU32(0))
    }
    fn is_one(&self) -> Self::Mask {
        WitnessComputationalInteger::<u32>::equal(self, &Self::ConstantU32(1))
    }
    fn constant(value: u32) -> Self {
        Self::ConstantU32(value)
    }
    fn equal(&self, other: &Self) -> Self::Mask {
        BoolNodeExpression::FromGenericIntegerEquality {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        }
    }
    fn overflowing_add(&self, other: &Self) -> (Self, Self::Mask) {
        let integer = Self::WrappingAdd {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };
        let carry = BoolNodeExpression::FromGenericIntegerCarry {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        (integer, carry)
    }
    fn overflowing_sub(&self, other: &Self) -> (Self, Self::Mask) {
        let integer = Self::WrappingSub {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };
        let carry = BoolNodeExpression::FromGenericIntegerBorrow {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        (integer, carry)
    }
    fn overflowing_add_with_carry(&self, other: &Self, carry: &Self::Mask) -> (Self, Self::Mask) {
        // we will let optimizer to handle this
        let carry = Self::from_mask(carry.clone());
        let (t, of0) = WitnessComputationalInteger::<u32>::overflowing_add(self, other);
        let (t, of1) = WitnessComputationalInteger::<u32>::overflowing_add(&t, &carry);

        let carry = BoolNodeExpression::Or {
            lhs: Box::new(of0),
            rhs: Box::new(of1),
        };
        (t, carry)
    }
    fn overflowing_sub_with_borrow(&self, other: &Self, borrow: &Self::Mask) -> (Self, Self::Mask) {
        // we will let optimizer to handle this
        let borrow = Self::from_mask(borrow.clone());
        let (t, of0) = WitnessComputationalInteger::<u32>::overflowing_sub(self, other);
        let (t, of1) = WitnessComputationalInteger::<u32>::overflowing_sub(&t, &borrow);

        let borrow = BoolNodeExpression::Or {
            lhs: Box::new(of0),
            rhs: Box::new(of1),
        };
        (t, borrow)
    }
    fn shl(&self, shift_magnitude: u32) -> Self {
        Self::WrappingShl {
            lhs: Box::new(self.clone()),
            magnitude: shift_magnitude,
        }
    }
    fn shr(&self, shift_magnitude: u32) -> Self {
        Self::WrappingShr {
            lhs: Box::new(self.clone()),
            magnitude: shift_magnitude,
        }
    }
    fn get_bit(&self, bit_idx: u32) -> Self::Mask {
        let src = if bit_idx == 0 {
            self.clone()
        } else {
            WitnessComputationalInteger::<u32>::shr(self, bit_idx)
        };
        let lowest_bit = WitnessComputationalInteger::<u32>::get_lowest_bits(&src, 1);

        BoolNodeExpression::FromGenericInteger(Box::new(lowest_bit))
    }
    fn equal_to_constant(&self, value: u32) -> Self::Mask {
        WitnessComputationalInteger::<u32>::equal(self, &Self::ConstantU32(value))
    }
    fn get_lowest_bits(&self, num_bits: u32) -> Self {
        Self::LowestBits {
            value: Box::new(self.clone()),
            num_bits,
        }
    }
}

impl<F: PrimeField> WitnessComputationalU32 for FixedWidthIntegerNodeExpression<F> {
    type Narrow = Self;

    fn truncate(&self) -> Self::Narrow {
        FixedWidthIntegerNodeExpression::<F>::TruncateFromU32(Box::new(self.clone()))
    }
    fn wrapping_product(&self, other: &Self) -> Self {
        Self::MulLow {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        }
    }
    fn split_widening_product(&self, other: &Self) -> (Self, Self) {
        let low = Self::MulLow {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        let high = Self::MulHigh {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        (low, high)
    }
    fn div_rem_assume_nonzero_divisor(divident: &Self, divisor: &Self) -> (Self, Self) {
        let q = Self::DivAssumeNonzero {
            lhs: Box::new(divident.clone()),
            rhs: Box::new(divisor.clone()),
        };

        let r = Self::RemAssumeNonzero {
            lhs: Box::new(divident.clone()),
            rhs: Box::new(divisor.clone()),
        };

        (q, r)
    }
}

impl<F: PrimeField> WitnessComputationalU16 for FixedWidthIntegerNodeExpression<F> {
    type Wide = Self;
    type Narrow = Self;

    fn widen(&self) -> Self::Wide {
        FixedWidthIntegerNodeExpression::<F>::WidenFromU16(Box::new(self.clone()))
    }
    fn truncate(&self) -> Self::Narrow {
        FixedWidthIntegerNodeExpression::<F>::TruncateFromU16(Box::new(self.clone()))
    }
    fn wrapping_product(&self, other: &Self) -> Self {
        Self::MulLow {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        }
    }
    fn widening_product(&self, other: &Self) -> Self::Wide {
        let wide_self = WitnessComputationalU16::widen(self);
        let wide_other = WitnessComputationalU16::widen(other);

        Self::MulLow {
            lhs: Box::new(wide_self),
            rhs: Box::new(wide_other),
        }
    }
    fn split_widening_product(&self, other: &Self) -> (Self, Self) {
        let low = Self::MulLow {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        let high = Self::MulHigh {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        (low, high)
    }
}

impl<F: PrimeField> WitnessComputationalU8 for FixedWidthIntegerNodeExpression<F> {
    type Wide = Self;

    fn widen(&self) -> Self::Wide {
        FixedWidthIntegerNodeExpression::<F>::WidenFromU8(Box::new(self.clone()))
    }
    fn wrapping_product(&self, other: &Self) -> Self {
        Self::MulLow {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        }
    }
    fn widening_product(&self, other: &Self) -> Self::Wide {
        let wide_self = WitnessComputationalU8::widen(self);
        let wide_other = WitnessComputationalU8::widen(other);

        Self::MulLow {
            lhs: Box::new(wide_self),
            rhs: Box::new(wide_other),
        }
    }
    fn split_widening_product(&self, other: &Self) -> (Self, Self) {
        let low = Self::MulLow {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        let high = Self::MulHigh {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        (low, high)
    }
}

impl<F: PrimeField> WitnessComputationalI32 for FixedWidthIntegerNodeExpression<F> {
    type UnsignedRepresentation = Self;
    fn from_unsigned(value: Self::UnsignedRepresentation) -> Self {
        Self::I32FromU32(Box::new(value))
    }
    fn as_unsigned(self) -> Self::UnsignedRepresentation {
        Self::U32FromI32(Box::new(self))
    }
    fn widening_product_bits(
        &self,
        other: &Self,
    ) -> (Self::UnsignedRepresentation, Self::UnsignedRepresentation) {
        let low = Self::SignedMulLowBits {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        let high = Self::SignedMulHighBits {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        (low, high)
    }
    fn mixed_widening_product_bits(
        &self,
        other: &Self::UnsignedRepresentation,
    ) -> (Self::UnsignedRepresentation, Self::UnsignedRepresentation) {
        let low = Self::SignedByUnsignedMulLowBits {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        let high = Self::SignedByUnsignedMulHighBits {
            lhs: Box::new(self.clone()),
            rhs: Box::new(other.clone()),
        };

        (low, high)
    }
    fn div_rem_assume_nonzero_divisor_no_overflow(divident: &Self, divisor: &Self) -> (Self, Self) {
        let q = Self::SignedDivAssumeNonzeroNoOverflowBits {
            lhs: Box::new(divident.clone()),
            rhs: Box::new(divisor.clone()),
        };

        let r = Self::SignedRemAssumeNonzeroNoOverflowBits {
            lhs: Box::new(divident.clone()),
            rhs: Box::new(divisor.clone()),
        };

        (q, r)
    }
}
