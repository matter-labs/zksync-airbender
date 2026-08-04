use ::field::*;
use cs::definitions::GKRAddress;

pub mod base;
pub mod once_folded;

pub trait EvaluationRepresentaionBase<F: PrimeField, E: FieldExtension<F> + Field>:
    'static + Clone + Copy + core::fmt::Debug + Send + Sync
{
    type Product: EvaluationRepresentaionExt<F, E, Base = Self, CTX = Self::CTX>;
    type CTX: 'static + Clone + Copy + core::fmt::Debug + Send + Sync;

    fn into_ext(self, ctx: &Self::CTX) -> E;

    fn add_other(self, other: &Self) -> Self;
    fn sub_other(self, other: &Self) -> Self;

    fn mul_by_base(self, other: &F) -> Self;
    fn mul_by_ext_and_into_ext(self, other: &E, ctx: &Self::CTX) -> E;
}

pub trait EvaluationRepresentaionExt<F: PrimeField, E: FieldExtension<F> + Field>:
    'static + Clone + Copy + core::fmt::Debug + Send + Sync
{
    type Base: EvaluationRepresentaionBase<F, E, Product = Self, CTX = Self::CTX>;

    type CTX: 'static + Clone + Copy + core::fmt::Debug + Send + Sync;

    fn into_ext(self, ctx: &Self::CTX) -> E;

    fn add_other(self, other: &Self) -> Self;
    fn sub_other(self, other: &Self) -> Self;

    fn add_base_repr(self, other: &Self::Base) -> Self;
    fn sub_base_repr(self, other: &Self::Base) -> Self;

    fn mul_by_base(self, other: &F) -> Self;
    fn add_with_ext_and_into_ext(self, other: &E, ctx: &Self::CTX) -> E;
    fn mul_by_ext_and_into_ext(self, other: &E, ctx: &Self::CTX) -> E;
}

pub trait SumcheckRoundSource<F: PrimeField, E: FieldExtension<F> + Field>: Send + Sync {
    type BaseFieldInput: EvaluationRepresentaionBase<F, E>;
    type BaseInputAccessor<'a>: PolyAccessor<F, E, Representation = Self::BaseFieldInput>
    where
        Self: 'a;

    type ExtFieldInput: EvaluationRepresentaionBase<F, E>;
    type ExtInputAccessor<'a>: PolyAccessor<F, E, Representation = Self::ExtFieldInput>
    where
        Self: 'a;

    fn base_field_input_ctx(
        &self,
    ) -> <Self::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX;
    fn ext_field_input_ctx(
        &self,
    ) -> <Self::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX;
    fn get_source_for_base_poly<'a>(&'a self, address: GKRAddress) -> Self::BaseInputAccessor<'a>;
    fn get_source_for_ext_poly<'a>(&'a self, address: GKRAddress) -> Self::ExtInputAccessor<'a>;
}

pub trait PolyAccessor<F: PrimeField, E: FieldExtension<F> + Field>: Send + Sync {
    const SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP: bool;
    type Representation: EvaluationRepresentaionBase<F, E>;

    fn get_at_index(&self, index: usize) -> Self::Representation;
    #[inline(always)]
    fn get_f0_only(&self, index: usize) -> Self::Representation {
        self.get_f0_and_f1_minus_f0(index)[0]
    }
    #[inline(always)]
    fn get_f1_minus_f0_only(&self, index: usize) -> Self::Representation {
        self.get_f0_and_f1_minus_f0(index)[1]
    }
    fn get_f0_and_f1(&self, index: usize) -> [Self::Representation; 2];
    #[inline(always)]
    fn get_f0_and_f1_minus_f0(&self, index: usize) -> [Self::Representation; 2] {
        let [f0, f1_minus_f0] = self.get_f0_and_f1(index);
        f1_minus_f0.sub_other(&f0);

        [f0, f1_minus_f0]
    }
    #[inline(always)]
    fn get_two_points<const EXPLICIT_FORM: bool>(&self, index: usize) -> [Self::Representation; 2] {
        if EXPLICIT_FORM {
            self.get_f0_and_f1(index)
        } else {
            self.get_f0_and_f1_minus_f0(index)
        }
    }
}

// #[derive(Clone, Copy, Debug)]
// pub struct ExtensionFieldRepresentation<F: PrimeField, E: FieldExtension<F> + Field> {
//     pub(crate) value: E,
//     pub(crate) _marker: core::marker::PhantomData<F>,
// }

// impl<F: PrimeField, E: FieldExtension<F> + Field> ExtensionFieldRepresentation<F, E> {
//     #[inline(always)]
//     pub fn new(value: E) -> Self {
//         Self {
//             value,
//             _marker: core::marker::PhantomData,
//         }
//     }
//     #[inline(always)]
//     pub fn into_value(self) -> E {
//         self.value
//     }
// }

// impl<F: PrimeField, E: FieldExtension<F> + Field> EvaluationRepresentation<F, E>
//     for ExtensionFieldRepresentation<F, E>
// {
//     type CollapseContext = ();
//     #[inline(always)]
//     fn from_base_constant(value: F) -> Self {
//         Self {
//             value: E::from_base(value),
//             _marker: core::marker::PhantomData,
//         }
//     }
//     #[inline(always)]
//     fn collapse_as_ext_field_element(self, _ctx: &Self::CollapseContext) -> E {
//         self.value
//     }
//     #[inline(always)]
//     fn collapse_into_ext_with_challenge(self, _ctx: &Self::CollapseContext, challenge: &E) -> E {
//         let mut result = self.value;
//         result.mul_assign(challenge);
//         result
//     }
//     #[inline(always)]
//     fn repr_add_assign<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&mut self, other: &Self) {
//         self.value.add_assign(&other.value);
//     }
//     #[inline(always)]
//     fn repr_sub_assign<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&mut self, other: &Self) {
//         self.value.sub_assign(&other.value);
//     }
//     #[inline(always)]
//     fn repr_mul_assign<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&mut self, other: &Self) {
//         self.value.mul_assign(&other.value);
//     }
//     #[inline(always)]
//     fn add_with_ext<const ASSUME_NO_PRODUCTS_BEFORE: bool>(
//         &self,
//         other: &E,
//         _ctx: &Self::CollapseContext,
//     ) -> E {
//         let mut t = self.value;
//         t.add_assign(other);

//         t
//     }
//     #[inline(always)]
//     fn mul_by_ext<const ASSUME_NO_PRODUCTS_BEFORE: bool>(
//         &self,
//         other: &E,
//         _ctx: &Self::CollapseContext,
//     ) -> E {
//         let mut t = self.value;
//         t.mul_assign(other);

//         t
//     }
//     #[inline(always)]
//     fn sub_from_ext<const ASSUME_NO_PRODUCTS_BEFORE: bool>(
//         &self,
//         other: &E,
//         _ctx: &Self::CollapseContext,
//     ) -> E {
//         let mut result = *other;
//         result.sub_assign(&self.value);

//         result
//     }
//     #[inline(always)]
//     fn mul_by_base<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&self, other: &F) -> Self {
//         let mut result = *self;
//         result.value.mul_assign_by_base(other);

//         result
//     }
// }

// pub trait EvaluationFormStorage<
//     F: PrimeField,
//     E: FieldExtension<F> + Field,
//     R: EvaluationRepresentation<F, E>,
// >: Send + Sync
// {
//     const SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP: bool;

//     fn get_collapse_context(&self) -> &R::CollapseContext;
//     fn get_at_index(&self, index: usize) -> R;
//     #[inline(always)]
//     fn get_f0_only(&self, index: usize) -> R {
//         self.get_f0_and_f1_minus_f0(index)[0]
//     }
//     #[inline(always)]
//     fn get_f1_minus_f0_only(&self, index: usize) -> R {
//         self.get_f0_and_f1_minus_f0(index)[1]
//     }
//     fn get_f0_and_f1(&self, index: usize) -> [R; 2];
//     #[inline(always)]
//     fn get_f0_and_f1_minus_f0(&self, index: usize) -> [R; 2] {
//         let [f0, mut f1_minus_f0] = self.get_f0_and_f1(index);
//         f1_minus_f0.repr_sub_assign::<true>(&f0);

//         [f0, f1_minus_f0]
//     }
//     #[inline(always)]
//     fn get_two_points<const EXPLICIT_FORM: bool>(&self, index: usize) -> [R; 2] {
//         if EXPLICIT_FORM {
//             self.get_f0_and_f1(index)
//         } else {
//             self.get_f0_and_f1_minus_f0(index)
//         }
//     }
// }

// impl<F: PrimeField, E: FieldExtension<F> + Field, R: EvaluationRepresentation<F, E>>
//     EvaluationFormStorage<F, E, R> for ()
// {
//     const SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP: bool = false;

//     #[inline(always)]
//     fn get_collapse_context(&self) -> &R::CollapseContext {
//         unreachable!()
//     }
//     #[inline(always)]
//     fn get_at_index(&self, _index: usize) -> R {
//         unreachable!()
//     }
//     #[inline(always)]
//     fn get_f0_and_f1(&self, _index: usize) -> [R; 2] {
//         unreachable!()
//     }
// }
