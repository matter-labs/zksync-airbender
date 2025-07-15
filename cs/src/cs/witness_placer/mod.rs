use super::placeholder::Placeholder;
use crate::definitions::*;
use core::fmt::Debug;
use field::{Field, PrimeField};
use std::any::Any;

pub mod cs_debug_evaluator;
pub mod graph_description;
pub mod scalar_witness_type_set;

pub trait WitnessResolutionDescription<F: PrimeField, W: WitnessPlacer<F>>: 'static + Any {
    fn evaluate(&self, placer: &mut W);
    fn box_clone(&self) -> Box<dyn WitnessResolutionDescription<F, W>>;
    fn clone_self(&self) -> Self
    where
        Self: Sized;
}

impl<F: PrimeField, W: WitnessPlacer<F>> WitnessResolutionDescription<F, W>
    for Box<dyn WitnessResolutionDescription<F, W>>
{
    fn evaluate(&self, placer: &mut W) {
        let inner = &**self;
        inner.evaluate(placer);
    }
    fn box_clone(&self) -> Box<dyn WitnessResolutionDescription<F, W>> {
        let inner = &**self;
        WitnessResolutionDescription::box_clone(inner)
    }
    fn clone_self(&self) -> Self
    where
        Self: Sized,
    {
        let inner = &**self;
        WitnessResolutionDescription::box_clone(inner)
    }
}

impl<F: PrimeField, W: WitnessPlacer<F>> Clone for Box<dyn WitnessResolutionDescription<F, W>> {
    fn clone(&self) -> Self {
        let inner = &**self;
        WitnessResolutionDescription::box_clone(inner)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct EmptyResolution;

impl<F: PrimeField, W: WitnessPlacer<F>> WitnessResolutionDescription<F, W> for EmptyResolution {
    fn evaluate(&self, _placer: &mut W) {
        // NOP
    }

    fn box_clone(&self) -> Box<dyn WitnessResolutionDescription<F, W>> {
        Box::new(self.clone()) as Box<dyn WitnessResolutionDescription<F, W>>
    }

    fn clone_self(&self) -> Self
    where
        Self: Sized,
    {
        *self
    }
}

#[derive(Clone)]
pub struct WitnessResolutionNode<
    F: PrimeField,
    W: WitnessPlacer<F>,
    T: WitnessResolutionDescription<F, W>,
    U: WitnessResolutionDescription<F, W>,
> {
    a: T,
    b: U,
    _marker: std::marker::PhantomData<(F, W)>,
}

impl<
        F: PrimeField,
        W: WitnessPlacer<F>,
        T: WitnessResolutionDescription<F, W>,
        U: WitnessResolutionDescription<F, W>,
    > WitnessResolutionDescription<F, W> for WitnessResolutionNode<F, W, T, U>
{
    fn evaluate(&self, placer: &mut W) {
        self.a.evaluate(placer);
        self.b.evaluate(placer);
    }

    fn box_clone(&self) -> Box<dyn WitnessResolutionDescription<F, W>> {
        Box::new(self.clone_self()) as Box<dyn WitnessResolutionDescription<F, W>>
    }

    fn clone_self(&self) -> Self
    where
        Self: Sized,
    {
        Self {
            a: self.a.clone_self(),
            b: self.b.clone_self(),
            _marker: core::marker::PhantomData,
        }
    }
}

pub struct WitnessResolutionGraph<F: PrimeField, W: WitnessPlacer<F>> {
    inner: WitnessResolutionNode<
        F,
        W,
        Box<dyn WitnessResolutionDescription<F, W>>,
        Box<dyn WitnessResolutionDescription<F, W>>,
    >,
    reorder_fn: Box<
        dyn FnOnce(
            Box<dyn WitnessResolutionDescription<F, W>>,
            Box<dyn WitnessResolutionDescription<F, W>>,
            Box<dyn WitnessResolutionDescription<F, W>>,
        ) -> WitnessResolutionNode<
            F,
            W,
            Box<dyn WitnessResolutionDescription<F, W>>,
            Box<dyn WitnessResolutionDescription<F, W>>,
        >,
    >,
    _marker: std::marker::PhantomData<(F, W)>,
}

impl<F: PrimeField, W: WitnessPlacer<F>> WitnessResolutionGraph<F, W> {
    fn placeholder() -> Self {
        Self {
            inner: WitnessResolutionNode {
                a: Box::new(EmptyResolution),
                b: Box::new(EmptyResolution),
                _marker: core::marker::PhantomData,
            },
            reorder_fn: Box::new(|_, _, _| WitnessResolutionNode {
                a: Box::new(EmptyResolution),
                b: Box::new(EmptyResolution),
                _marker: core::marker::PhantomData,
            }),
            _marker: core::marker::PhantomData,
        }
    }
    pub fn append<T: WitnessResolutionDescription<F, W>>(self, node: T) -> Self {
        let Self {
            inner, reorder_fn, ..
        } = self;

        // we manually make next step via dyn cast

        let WitnessResolutionNode { a, b, .. } = inner;
        let next_step = Box::new(node) as Box<dyn WitnessResolutionDescription<F, W>>;
        let result = (reorder_fn)(a, b, next_step);

        let reorder_fn = Box::new(
            |a: Box<dyn WitnessResolutionDescription<F, W>>,
             b: Box<dyn WitnessResolutionDescription<F, W>>,
             next: Box<dyn WitnessResolutionDescription<F, W>>| {
                // now we can partially monomorphize

                let b = *Box::<dyn Any>::downcast::<T>(b).expect("must downcast");

                let new_a = WitnessResolutionNode {
                    a,
                    b,
                    _marker: core::marker::PhantomData,
                };
                let full_node = WitnessResolutionNode {
                    a: Box::new(new_a) as Box<dyn WitnessResolutionDescription<F, W>>,
                    b: next,
                    _marker: core::marker::PhantomData,
                };

                full_node
            },
        );

        Self {
            inner: result,
            reorder_fn,
            _marker: core::marker::PhantomData,
        }
    }

    pub fn append_inplace<T: WitnessResolutionDescription<F, W>>(&mut self, node: T) {
        let this = core::mem::replace(self, Self::placeholder());
        *self = this.append(node);
    }

    pub fn new() -> Self {
        let first_step = WitnessResolutionNode {
            a: Box::new(EmptyResolution) as Box<dyn WitnessResolutionDescription<F, W>>,
            b: Box::new(EmptyResolution) as Box<dyn WitnessResolutionDescription<F, W>>,
            _marker: core::marker::PhantomData,
        };

        let reorder_fn = Box::new(
            |a: Box<dyn WitnessResolutionDescription<F, W>>,
             b: Box<dyn WitnessResolutionDescription<F, W>>,
             next: Box<dyn WitnessResolutionDescription<F, W>>| {
                // now we can partially monomorphize

                let b = *Box::<dyn Any>::downcast::<EmptyResolution>(b).expect("must downcast");

                let new_a = WitnessResolutionNode {
                    a,
                    b,
                    _marker: core::marker::PhantomData,
                };
                let full_node = WitnessResolutionNode {
                    a: Box::new(new_a) as Box<dyn WitnessResolutionDescription<F, W>>,
                    b: next,
                    _marker: core::marker::PhantomData,
                };

                full_node
            },
        );

        Self {
            inner: first_step,
            reorder_fn,
            _marker: core::marker::PhantomData,
        }
    }
}

// default implementation for any closure (and only closures are possible as implementing `Fn` is not yet allowed)
impl<F: PrimeField, W: WitnessPlacer<F>, T: 'static + Clone + Fn(&mut W) -> ()>
    WitnessResolutionDescription<F, W> for T
{
    fn evaluate(&self, placer: &mut W) {
        (self)(placer)
    }

    fn box_clone(&self) -> Box<dyn WitnessResolutionDescription<F, W>> {
        Box::new(self.clone()) as Box<dyn WitnessResolutionDescription<F, W>>
    }

    fn clone_self(&self) -> Self
    where
        Self: Sized,
    {
        self.clone()
    }
}

pub trait WitnessTypeSet<F: PrimeField>: 'static + Sized {
    const CAN_BRANCH: bool;
    const MERGE_LOOKUP_AND_MULTIPLICITY_COUNT: bool = false;

    type Mask: WitnessMask;
    type Field: WitnessComputationalField<F, Mask = Self::Mask, IntegerRepresentation = Self::U32>;
    type I32: WitnessComputationalI32<UnsignedRepresentation = Self::U32>;
    type U32: WitnessComputationalU32<Mask = Self::Mask, Narrow = Self::U16>;
    type U16: WitnessComputationalU16<Wide = Self::U32, Narrow = Self::U8, Mask = Self::Mask>;
    type U8: WitnessComputationalU8<Wide = Self::U16, Mask = Self::Mask>;

    fn branch(mask: &Self::Mask) -> bool;
}

/// We want to compute and place witness Variable as index,
/// and use any arbitrary types to express computation of values
pub trait WitnessPlacer<F: PrimeField>: WitnessTypeSet<F> {
    fn record_resolver(&mut self, resolver: impl WitnessResolutionDescription<F, Self>);

    fn get_oracle_field(&mut self, placeholder: Placeholder, subindex: usize) -> Self::Field;
    fn get_oracle_u32(&mut self, placeholder: Placeholder) -> Self::U32;
    fn get_oracle_u16(&mut self, placeholder: Placeholder) -> Self::U16;
    fn get_oracle_u8(&mut self, placeholder: Placeholder) -> Self::U8;
    fn get_oracle_boolean(&mut self, placeholder: Placeholder) -> Self::Mask;

    fn get_field(&mut self, variable: Variable) -> Self::Field;
    fn get_boolean(&mut self, variable: Variable) -> Self::Mask;

    #[inline(always)]
    fn get_u32_from_u16_parts(&mut self, variables: [Variable; 2]) -> Self::U32 {
        // default implementation
        let [low, high] = variables;
        let low = self.get_u16(low).widen();
        let high = self.get_u16(high).widen();

        let mut high = high.shl(16);
        high.add_assign(&low);

        high
    }

    #[inline(always)]
    fn get_u32_from_u8_parts(&mut self, variables: [Variable; 4]) -> Self::U32 {
        // default implementation
        let low = [variables[0], variables[1]];
        let high = [variables[2], variables[3]];
        let low = self.get_u16_from_u8_parts(low).widen();
        let high = self.get_u16_from_u8_parts(high).widen();

        let mut high = high.shl(16);
        high.add_assign(&low);

        high
    }

    fn get_u16(&mut self, variable: Variable) -> Self::U16;

    #[inline(always)]
    fn get_u16_from_u8_parts(&mut self, variables: [Variable; 2]) -> Self::U16 {
        // default implementation
        let [low, high] = variables;
        let low = self.get_u8(low).widen();
        let high = self.get_u8(high).widen();

        let mut high = high.shl(8);
        high.add_assign(&low);

        high
    }

    fn get_u8(&mut self, variable: Variable) -> Self::U8;

    fn assign_mask(&mut self, variable: Variable, value: &Self::Mask);
    fn assign_field(&mut self, variable: Variable, value: &Self::Field);

    #[inline(always)]
    fn assign_u32_from_u16_parts(&mut self, variables: [Variable; 2], value: &Self::U32) {
        let [low, high] = variables;

        let low_val = value.truncate();
        let high_val = value.shr(16).truncate();
        self.assign_u16(low, &low_val);
        self.assign_u16(high, &high_val);
    }

    fn assign_u16(&mut self, variable: Variable, value: &Self::U16);

    #[inline(always)]
    fn assign_u16_from_u8_parts(&mut self, variables: [Variable; 2], value: &Self::U16) {
        let [low, high] = variables;

        let low_val = value.truncate();
        let high_val = value.shr(8).truncate();
        self.assign_u8(low, &low_val);
        self.assign_u8(high, &high_val);
    }

    fn assign_u8(&mut self, variable: Variable, value: &Self::U8);

    // We also want conditional assign

    fn conditionally_assign_mask(
        &mut self,
        variable: Variable,
        mask: &Self::Mask,
        value: &Self::Mask,
    );
    fn conditionally_assign_field(
        &mut self,
        variable: Variable,
        mask: &Self::Mask,
        value: &Self::Field,
    );
    fn conditionally_assign_u32(
        &mut self,
        variables: [Variable; 2],
        mask: &Self::Mask,
        value: &Self::U32,
    ) {
        let [low, high] = variables;

        let low_val = value.truncate();
        let high_val = value.shr(16).truncate();
        self.conditionally_assign_u16(low, mask, &low_val);
        self.conditionally_assign_u16(high, mask, &high_val);
    }
    fn conditionally_assign_u16(
        &mut self,
        variable: Variable,
        mask: &Self::Mask,
        value: &Self::U16,
    );
    fn conditionally_assign_u8(&mut self, variable: Variable, mask: &Self::Mask, value: &Self::U8);

    fn lookup<const M: usize, const N: usize>(
        &mut self,
        inputs: &[Self::Field; M],
        table_id: &Self::U16,
    ) -> [Self::Field; N];

    fn maybe_lookup<const M: usize, const N: usize>(
        &mut self,
        inputs: &[Self::Field; M],
        table_id: &Self::U16,
        mask: &Self::Mask,
    ) -> [Self::Field; N];

    fn lookup_enforce<const M: usize>(&mut self, inputs: &[Self::Field; M], table_id: &Self::U16);

    fn assume_assigned(&mut self, variable: Variable);
    fn spec_decoder_relation(&mut self, pc: [Variable; 2], decoder_data: &DecoderData<F>);
}

pub trait WitnessMask: 'static + Sized + Clone + Debug {
    fn and(&self, other: &Self) -> Self;
    fn or(&self, other: &Self) -> Self;
    fn negate(&self) -> Self;
    fn constant(value: bool) -> Self;
    #[inline(always)]
    fn assign_masked(&mut self, mask: &Self, other: &Self) {
        *self = Self::select(mask, other, &*self);
    }
    fn select(mask: &Self, a: &Self, b: &Self) -> Self;
    fn select_into(dst: &mut Self, mask: &Self, a: &Self, b: &Self);
}

pub trait WitnessComputationCore: 'static + Sized + Clone + Debug {
    type Mask: WitnessMask;

    // wrapping
    fn add_assign(&mut self, other: &Self);
    // wrapping
    fn sub_assign(&mut self, other: &Self);
    #[inline(always)]
    fn assign_masked(&mut self, mask: &Self::Mask, other: &Self) {
        *self = Self::select(mask, other, &*self);
    }
    // wrapping
    fn add_assign_masked(&mut self, mask: &Self::Mask, other: &Self);
    fn add_assign_product(&mut self, a: &Self, b: &Self);
    fn add_assign_product_masked(&mut self, mask: &Self::Mask, a: &Self, b: &Self);
    fn select(mask: &Self::Mask, a: &Self, b: &Self) -> Self;
    fn select_into(dst: &mut Self, mask: &Self::Mask, a: &Self, b: &Self);
    fn from_mask(value: Self::Mask) -> Self;
    fn into_mask(self) -> Self::Mask;
}

pub trait WitnessComputationalField<F: PrimeField>: 'static + Sized + Clone + Debug {
    type Mask: WitnessMask;
    type IntegerRepresentation;

    fn add_assign(&mut self, other: &Self);
    fn sub_assign(&mut self, other: &Self);
    fn mul_assign(&mut self, other: &Self);
    fn fused_mul_add_assign(&mut self, a: &Self, b: &Self);
    fn add_assign_product(&mut self, a: &Self, b: &Self);
    #[inline(always)]
    fn assign_masked(&mut self, mask: &Self::Mask, other: &Self) {
        *self = Self::select(mask, other, &*self);
    }
    fn add_assign_masked(&mut self, mask: &Self::Mask, other: &Self);
    fn add_assign_product_masked(&mut self, mask: &Self::Mask, a: &Self, b: &Self);
    fn select(mask: &Self::Mask, a: &Self, b: &Self) -> Self;
    fn select_into(dst: &mut Self, mask: &Self::Mask, a: &Self, b: &Self);
    fn into_mask(self) -> Self::Mask;
    fn from_mask(value: Self::Mask) -> Self;
    fn is_zero(&self) -> Self::Mask;
    fn is_one(&self) -> Self::Mask;
    fn constant(value: F) -> Self;
    fn equal(&self, other: &Self) -> Self::Mask;
    fn inverse(&self) -> Self;
    fn inverse_or_zero(&self) -> Self;
    fn as_integer(self) -> Self::IntegerRepresentation;
    fn from_integer(value: Self::IntegerRepresentation) -> Self;
}

pub trait WitnessComputationalInteger<T: 'static + Sized>: WitnessComputationCore {
    fn is_zero(&self) -> Self::Mask;
    fn is_one(&self) -> Self::Mask;
    fn constant(value: T) -> Self;
    fn equal(&self, other: &Self) -> Self::Mask;
    fn overflowing_add(&self, other: &Self) -> (Self, Self::Mask);
    fn overflowing_sub(&self, other: &Self) -> (Self, Self::Mask);
    fn overflowing_add_with_carry(&self, other: &Self, carry: &Self::Mask) -> (Self, Self::Mask);
    fn overflowing_sub_with_borrow(&self, other: &Self, borrow: &Self::Mask) -> (Self, Self::Mask);
    fn shl(&self, shift_magnitude: u32) -> Self;
    fn shr(&self, shift_magnitude: u32) -> Self;
    fn get_bit(&self, bit_idx: u32) -> Self::Mask;
    fn equal_to_constant(&self, value: T) -> Self::Mask;
    fn get_lowest_bits(&self, num_bits: u32) -> Self;
}

pub trait WitnessComputationalU32: WitnessComputationalInteger<u32> {
    type Narrow: WitnessComputationalU16<Wide = Self, Mask = Self::Mask>;

    fn truncate(&self) -> Self::Narrow;
    fn wrapping_product(&self, other: &Self) -> Self;
    fn split_widening_product(&self, other: &Self) -> (Self, Self);
    fn div_rem_assume_nonzero_divisor(divident: &Self, divisor: &Self) -> (Self, Self);
}

pub trait WitnessComputationalU16: WitnessComputationalInteger<u16> {
    type Wide: WitnessComputationalU32<Narrow = Self, Mask = Self::Mask>;
    type Narrow: WitnessComputationalU8<Wide = Self, Mask = Self::Mask>;

    fn widen(&self) -> Self::Wide;
    fn truncate(&self) -> Self::Narrow;
    #[inline(always)]
    fn wrapping_product(&self, other: &Self) -> Self {
        Self::split_widening_product(&self, other).0
    }
    fn widening_product(&self, other: &Self) -> Self::Wide;
    fn split_widening_product(&self, other: &Self) -> (Self, Self);
}

pub trait WitnessComputationalU8: WitnessComputationalInteger<u8> {
    type Wide: WitnessComputationalU16<Narrow = Self, Mask = Self::Mask>;

    fn widen(&self) -> Self::Wide;
    #[inline(always)]
    fn wrapping_product(&self, other: &Self) -> Self {
        Self::split_widening_product(&self, other).0
    }
    fn widening_product(&self, other: &Self) -> Self::Wide;
    fn split_widening_product(&self, other: &Self) -> (Self, Self);
}

// pub trait WitnessComputationalI32: WitnessComputationalInteger<i32> {
pub trait WitnessComputationalI32: 'static + Sized + Clone + Debug {
    type UnsignedRepresentation: WitnessComputationalU32;
    fn from_unsigned(value: Self::UnsignedRepresentation) -> Self;
    fn as_unsigned(self) -> Self::UnsignedRepresentation;
    fn widening_product_bits(
        &self,
        other: &Self,
    ) -> (Self::UnsignedRepresentation, Self::UnsignedRepresentation);
    fn mixed_widening_product_bits(
        &self,
        other: &Self::UnsignedRepresentation,
    ) -> (Self::UnsignedRepresentation, Self::UnsignedRepresentation);
    fn div_rem_assume_nonzero_divisor_no_overflow(divident: &Self, divisor: &Self) -> (Self, Self);
}

impl WitnessMask for bool {
    #[inline(always)]
    fn constant(value: bool) -> Self {
        value
    }
    #[inline(always)]
    fn and(&self, other: &Self) -> Self {
        *self && *other
    }
    #[inline(always)]
    fn or(&self, other: &Self) -> Self {
        *self || *other
    }
    #[inline(always)]
    fn negate(&self) -> Self {
        !*self
    }
    #[inline(always)]
    fn select(mask: &Self, a: &Self, b: &Self) -> Self {
        if *mask {
            *a
        } else {
            *b
        }
    }
    fn select_into(dst: &mut Self, mask: &Self, a: &Self, b: &Self) {
        if *mask {
            *dst = *a;
        } else {
            *dst = *b;
        }
    }
}

impl<F: PrimeField> WitnessComputationalField<F> for F {
    type Mask = bool;
    type IntegerRepresentation = u32;

    #[inline(always)]
    fn add_assign(&mut self, other: &Self) {
        Field::add_assign(self, other);
    }
    #[inline(always)]
    fn sub_assign(&mut self, other: &Self) {
        Field::sub_assign(self, other);
    }
    #[inline(always)]
    fn mul_assign(&mut self, other: &Self) {
        Field::mul_assign(self, other);
    }
    #[inline(always)]
    fn fused_mul_add_assign(&mut self, a: &Self, b: &Self) {
        Field::fused_mul_add_assign(self, a, b);
    }
    #[inline(always)]
    fn add_assign_product(&mut self, a: &Self, b: &Self) {
        Field::add_assign_product(self, a, b);
    }
    #[inline(always)]
    fn add_assign_masked(&mut self, mask: &Self::Mask, other: &Self) {
        if *mask {
            Field::add_assign(self, other);
        }
    }
    #[inline(always)]
    fn add_assign_product_masked(&mut self, mask: &Self::Mask, a: &Self, b: &Self) {
        if *mask {
            Field::add_assign_product(self, a, b);
        }
    }
    #[inline(always)]
    fn select(mask: &Self::Mask, a: &Self, b: &Self) -> Self {
        if *mask {
            *a
        } else {
            *b
        }
    }
    #[inline(always)]
    fn select_into(dst: &mut Self, mask: &Self::Mask, a: &Self, b: &Self) {
        if *mask {
            *dst = *a;
        } else {
            *dst = *b;
        }
    }
    #[inline(always)]
    fn into_mask(self) -> Self::Mask {
        self.as_boolean()
    }

    #[inline(always)]
    fn from_mask(value: Self::Mask) -> Self {
        F::from_boolean(value)
    }

    #[inline(always)]
    fn is_zero(&self) -> Self::Mask {
        Field::is_zero(self)
    }

    #[inline(always)]
    fn is_one(&self) -> Self::Mask {
        Field::is_one(self)
    }

    #[inline(always)]
    fn constant(value: F) -> Self {
        value
    }

    #[inline(always)]
    fn equal(&self, other: &Self) -> Self::Mask {
        *self == *other
    }

    #[inline(always)]
    fn inverse(&self) -> Self {
        Field::inverse(self).unwrap()
    }

    #[inline(always)]
    fn inverse_or_zero(&self) -> Self {
        Field::inverse(self).unwrap_or(F::ZERO)
    }

    #[inline(always)]
    fn as_integer(self) -> Self::IntegerRepresentation {
        self.as_u64_reduced() as u32
    }

    #[inline(always)]
    fn from_integer(value: Self::IntegerRepresentation) -> Self {
        Self::from_u64_with_reduction(value as u64)
    }
}

macro_rules! impl_comp_core {
    ($t: ty) => {
        impl WitnessComputationCore for $t {
            type Mask = bool;

            #[inline(always)]
            fn add_assign(&mut self, other: &Self) {
                *self = self.wrapping_add(*other);
            }
            #[inline(always)]
            fn sub_assign(&mut self, other: &Self) {
                *self = self.wrapping_sub(*other);
            }
            #[inline(always)]
            fn add_assign_masked(&mut self, mask: &Self::Mask, other: &Self) {
                if *mask {
                    *self = self.wrapping_add(*other);
                }
            }
            #[inline(always)]
            fn add_assign_product(&mut self, a: &Self, b: &Self) {
                *self += *a * *b;
            }
            #[inline(always)]
            fn add_assign_product_masked(&mut self, mask: &Self::Mask, a: &Self, b: &Self) {
                if *mask {
                    *self += *a * *b;
                }
            }
            #[inline(always)]
            fn select(mask: &Self::Mask, a: &Self, b: &Self) -> Self {
                if *mask {
                    *a
                } else {
                    *b
                }
            }
            #[inline(always)]
            fn select_into(dst: &mut Self, mask: &Self::Mask, a: &Self, b: &Self) {
                if *mask {
                    *dst = *a;
                } else {
                    *dst = *b;
                }
            }
            #[inline(always)]
            fn from_mask(value: Self::Mask) -> Self {
                value as $t
            }
            #[inline(always)]
            fn into_mask(self) -> Self::Mask {
                self == 1
            }
        }

        impl WitnessComputationalInteger<$t> for $t {
            #[inline(always)]
            fn is_zero(&self) -> Self::Mask {
                *self == 0
            }
            #[inline(always)]
            fn is_one(&self) -> Self::Mask {
                *self == 1
            }
            #[inline(always)]
            fn constant(value: $t) -> Self {
                value
            }
            #[inline(always)]
            fn equal(&self, other: &Self) -> Self::Mask {
                *self == *other
            }
            #[inline(always)]
            fn overflowing_add(&self, other: &Self) -> (Self, Self::Mask) {
                <$t>::overflowing_add(*self, *other)
            }
            #[inline(always)]
            fn overflowing_sub(&self, other: &Self) -> (Self, Self::Mask) {
                <$t>::overflowing_sub(*self, *other)
            }
            #[inline(always)]
            fn overflowing_add_with_carry(
                &self,
                other: &Self,
                carry: &Self::Mask,
            ) -> (Self, Self::Mask) {
                let (t, of0) = <$t>::overflowing_add(*self, *other);
                let (t, of1) = <$t>::overflowing_add(t, *carry as $t);
                let carry = of0 || of1;

                (t, carry)
            }
            #[inline(always)]
            fn overflowing_sub_with_borrow(
                &self,
                other: &Self,
                borrow: &Self::Mask,
            ) -> (Self, Self::Mask) {
                let (t, of0) = <$t>::overflowing_sub(*self, *other);
                let (t, of1) = <$t>::overflowing_sub(t, *borrow as $t);
                let borrow = of0 || of1;

                (t, borrow)
            }
            #[inline(always)]
            fn shl(&self, shift_magnitude: u32) -> Self {
                *self << shift_magnitude
            }
            #[inline(always)]
            fn shr(&self, shift_magnitude: u32) -> Self {
                *self >> shift_magnitude
            }
            #[inline(always)]
            fn get_bit(&self, bit_idx: u32) -> Self::Mask {
                *self & (1 << bit_idx) != 0
            }
            #[inline(always)]
            fn equal_to_constant(&self, value: $t) -> Self::Mask {
                *self == value
            }
            #[inline(always)]
            fn get_lowest_bits(&self, num_bits: u32) -> Self {
                *self & ((1 << num_bits) - 1)
            }
        }
    };
}

impl_comp_core!(u8);
impl_comp_core!(u16);
impl_comp_core!(u32);
impl_comp_core!(i32);

impl WitnessComputationalU32 for u32 {
    type Narrow = u16;

    #[inline(always)]
    fn truncate(&self) -> Self::Narrow {
        *self as u16
    }
    #[inline(always)]
    fn wrapping_product(&self, other: &Self) -> Self {
        self.wrapping_mul(*other)
    }
    #[inline(always)]
    fn split_widening_product(&self, other: &Self) -> (Self, Self) {
        let result = (*self as u64) * (*other as u64);

        (result as u32, (result >> 32) as u32)
    }
    #[inline(always)]
    fn div_rem_assume_nonzero_divisor(divident: &Self, divisor: &Self) -> (Self, Self) {
        let q = divident / divisor;
        let r = divident % divisor;

        (q, r)
        // divident.div_rem(*divisor)
    }
}

impl WitnessComputationalU16 for u16 {
    type Wide = u32;
    type Narrow = u8;

    #[inline(always)]
    fn widen(&self) -> Self::Wide {
        *self as u32
    }
    #[inline(always)]
    fn truncate(&self) -> Self::Narrow {
        *self as u8
    }
    #[inline(always)]
    fn wrapping_product(&self, other: &Self) -> Self {
        self.wrapping_mul(*other)
    }
    #[inline(always)]
    fn widening_product(&self, other: &Self) -> Self::Wide {
        (*self as u32) * (*other as u32)
    }
    #[inline(always)]
    fn split_widening_product(&self, other: &Self) -> (Self, Self) {
        let result = (*self as u32) * (*other as u32);

        (result as u16, (result >> 16) as u16)
    }
}

impl WitnessComputationalU8 for u8 {
    type Wide = u16;

    #[inline(always)]
    fn widen(&self) -> Self::Wide {
        *self as u16
    }
    #[inline(always)]
    fn wrapping_product(&self, other: &Self) -> Self {
        self.wrapping_mul(*other)
    }
    #[inline(always)]
    fn widening_product(&self, other: &Self) -> Self::Wide {
        (*self as u16) * (*other as u16)
    }
    #[inline(always)]
    fn split_widening_product(&self, other: &Self) -> (Self, Self) {
        let result = (*self as u16) * (*other as u16);

        (result as u8, (result >> 8) as u8)
    }
}

impl WitnessComputationalI32 for i32 {
    type UnsignedRepresentation = u32;
    #[inline(always)]
    fn from_unsigned(value: Self::UnsignedRepresentation) -> Self {
        value as i32
    }
    #[inline(always)]
    fn as_unsigned(self) -> Self::UnsignedRepresentation {
        self as u32
    }
    #[inline(always)]
    fn widening_product_bits(
        &self,
        other: &Self,
    ) -> (Self::UnsignedRepresentation, Self::UnsignedRepresentation) {
        use crate::utils::sign_extend_u32;
        let result =
            sign_extend_u32(*self as u32).wrapping_mul(sign_extend_u32(*other as u32)) as u64;
        (result as u32, (result >> 32) as u32)
    }
    #[inline(always)]
    fn mixed_widening_product_bits(
        &self,
        other: &Self::UnsignedRepresentation,
    ) -> (Self::UnsignedRepresentation, Self::UnsignedRepresentation) {
        use crate::utils::sign_extend_u32;
        let result = sign_extend_u32(*self as u32).wrapping_mul(*other as i64) as u64;
        (result as u32, (result >> 32) as u32)
    }
    #[inline(always)]
    fn div_rem_assume_nonzero_divisor_no_overflow(divident: &Self, divisor: &Self) -> (Self, Self) {
        let q = divident / divisor;
        let r = divident % divisor;

        (q, r)
        // divident.div_rem(*divisor)
    }
}

pub fn witness_early_branch_if_possible<
    F: PrimeField,
    W: WitnessPlacer<F>,
    T: WitnessResolutionDescription<F, W>,
>(
    branch_mask: W::Mask,
    placer: &mut W,
    node: &T,
) {
    if W::CAN_BRANCH {
        if W::branch(&branch_mask) {
            node.evaluate(placer);
        }
    } else {
        // we should use conditional assignment anyway
        node.evaluate(placer);
    }
}
