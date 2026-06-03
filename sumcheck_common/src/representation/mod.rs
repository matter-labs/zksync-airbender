use ::field::*;
use cs::definitions::GKRAddress;

pub mod base;
pub mod ext;
pub mod once_folded;

pub trait EvaluationRepresentaionBase<F: PrimeField, E: FieldExtension<F> + Field>:
    'static + Clone + Copy + core::fmt::Debug + Send + Sync
{
    type Product: EvaluationRepresentaionExt<F, E, Base = Self, CTX = Self::CTX>;
    type CTX: 'static + Clone + Copy + core::fmt::Debug + Send + Sync;

    fn zero() -> Self;
    fn into_ext(self, ctx: &Self::CTX) -> E;
    fn negate(self) -> Self;

    fn add_other(self, other: &Self) -> Self;
    fn sub_other(self, other: &Self) -> Self;

    fn add_base(self, other: &F) -> Self;
    fn mul_by_base(self, other: &F) -> Self;
    fn add_with_ext(self, other: &E, ctx: &Self::CTX) -> E;
    fn sub_from_ext(self, other: &E, ctx: &Self::CTX) -> E;
    fn mul_by_ext(self, other: &E, ctx: &Self::CTX) -> E;
    fn mul_with_other(self, other: &Self) -> Self::Product;
}

pub trait EvaluationRepresentaionExt<F: PrimeField, E: FieldExtension<F> + Field>:
    'static + Clone + Copy + core::fmt::Debug + Send + Sync
{
    type Base: EvaluationRepresentaionBase<F, E, Product = Self, CTX = Self::CTX>;

    type CTX: 'static + Clone + Copy + core::fmt::Debug + Send + Sync;

    fn zero() -> Self;
    fn into_ext(self, ctx: &Self::CTX) -> E;
    fn negate(self) -> Self;

    fn add_other(self, other: &Self) -> Self;
    fn sub_other(self, other: &Self) -> Self;

    fn add_base_repr(self, other: &Self::Base) -> Self;
    fn sub_base_repr(self, other: &Self::Base) -> Self;

    fn add_base(self, other: &F) -> Self;
    fn mul_by_base(self, other: &F) -> Self;
    fn add_with_ext(self, other: &E, ctx: &Self::CTX) -> E;
    fn mul_by_ext(self, other: &E, ctx: &Self::CTX) -> E;
}

pub trait SumcheckRoundSource<F: PrimeField, E: FieldExtension<F> + Field>: Send + Sync {
    type BaseFieldInput: EvaluationRepresentaionBase<F, E>;
    type BaseInputAccessor: PolyAccessor<F, E, Representation = Self::BaseFieldInput>;

    type ExtFieldInput: EvaluationRepresentaionBase<F, E>;
    type ExtInputAccessor: PolyAccessor<F, E, Representation = Self::ExtFieldInput>;

    fn base_field_input_ctx(
        &self,
    ) -> <Self::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX;
    fn ext_field_input_ctx(
        &self,
    ) -> <Self::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX;
    fn get_source_for_base_poly(&mut self, address: GKRAddress) -> Self::BaseInputAccessor;
    fn get_source_for_ext_poly(&mut self, address: GKRAddress) -> Self::ExtInputAccessor;
}

pub trait PolyAccessor<F: PrimeField, E: FieldExtension<F> + Field>: Send + Sync {
    const SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP: bool;
    type Representation: EvaluationRepresentaionBase<F, E>;

    fn get_at_index<const ASSUME_PREFOLDED: bool>(&self, index: usize) -> Self::Representation;
    #[inline(always)]
    fn get_f0_only<const ASSUME_PREFOLDED: bool>(&self, index: usize) -> Self::Representation {
        self.get_f0_and_f1_minus_f0::<ASSUME_PREFOLDED>(index)[0]
    }
    #[inline(always)]
    fn get_f1_minus_f0_only<const ASSUME_PREFOLDED: bool>(
        &self,
        index: usize,
    ) -> Self::Representation {
        self.get_f0_and_f1_minus_f0::<ASSUME_PREFOLDED>(index)[1]
    }
    fn get_f0_and_f1<const ASSUME_PREFOLDED: bool>(
        &self,
        index: usize,
    ) -> [Self::Representation; 2];
    #[inline(always)]
    fn get_f0_and_f1_minus_f0<const ASSUME_PREFOLDED: bool>(
        &self,
        index: usize,
    ) -> [Self::Representation; 2] {
        let [f0, f1] = self.get_f0_and_f1::<ASSUME_PREFOLDED>(index);
        let f1_minus_f0 = f1.sub_other(&f0);

        [f0, f1_minus_f0]
    }
    #[inline(always)]
    fn get_two_points<const ASSUME_PREFOLDED: bool, const EXPLICIT_FORM: bool>(
        &self,
        index: usize,
    ) -> [Self::Representation; 2] {
        if EXPLICIT_FORM {
            self.get_f0_and_f1::<ASSUME_PREFOLDED>(index)
        } else {
            self.get_f0_and_f1_minus_f0::<ASSUME_PREFOLDED>(index)
        }
    }
}
