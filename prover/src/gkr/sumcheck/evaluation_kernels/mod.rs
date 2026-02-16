use crate::gkr::sumcheck::access_and_fold::GKRStorage;
use cs::definitions::GKRAddress;
use field::{Field, FieldExtension, PrimeField};
use std::collections::BTreeMap;
use worker::Worker;

pub mod fixed_kernels;
pub mod kernel_impls;

pub mod generic_kernel;
pub mod simple_in_base;
pub mod simple_in_extension;
pub mod simple_mixed;

pub use self::fixed_kernels::*;
pub use self::generic_kernel::*;
pub use self::kernel_impls::*;
pub use self::simple_in_base::*;
pub use self::simple_in_extension::*;
pub use self::simple_mixed::*;

pub trait EvaluationRepresentation<F: PrimeField, E: FieldExtension<F> + Field>:
    'static + Clone + Copy + core::fmt::Debug + Send + Sync
{
    type CollapseContext: 'static + Clone + Copy + core::fmt::Debug + Send + Sync;
    type CollapsedForm: Field;
    fn collapse(self, ctx: &Self::CollapseContext) -> Self::CollapsedForm;

    fn collapse_for_batch_eval(self, ctx: &Self::CollapseContext, challenge: &E) -> E;

    fn repr_add_assign<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&mut self, other: &Self);
    fn repr_sub_assign<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&mut self, other: &Self);
    fn repr_mul_assign<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&mut self, other: &Self);

    fn add_with_ext<const ASSUME_NO_PRODUCTS_BEFORE: bool>(
        &self,
        other: &E,
        ctx: &Self::CollapseContext,
    ) -> E;
    fn sub_from_ext<const ASSUME_NO_PRODUCTS_BEFORE: bool>(
        &self,
        other: &E,
        ctx: &Self::CollapseContext,
    ) -> E;
    fn mul_by_ext<const ASSUME_NO_PRODUCTS_BEFORE: bool>(
        &self,
        other: &E,
        ctx: &Self::CollapseContext,
    ) -> E;
    fn add_base_constant(&mut self, constant: F) {
        todo!()
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field> EvaluationRepresentation<F, E> for () {
    type CollapseContext = ();
    type CollapsedForm = F;
    #[inline(always)]
    fn collapse(self, _ctx: &Self::CollapseContext) -> Self::CollapsedForm {
        F::ZERO
    }
    #[inline(always)]
    fn collapse_for_batch_eval(self, _ctx: &Self::CollapseContext, _challenge: &E) -> E {
        E::ZERO
    }
    #[inline(always)]
    fn repr_add_assign<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&mut self, _other: &Self) {}
    #[inline(always)]
    fn repr_sub_assign<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&mut self, _other: &Self) {}
    #[inline(always)]
    fn repr_mul_assign<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&mut self, _other: &Self) {}
    #[inline(always)]
    fn add_with_ext<const ASSUME_NO_PRODUCTS_BEFORE: bool>(
        &self,
        _other: &E,
        _ctx: &Self::CollapseContext,
    ) -> E {
        unreachable!()
    }
    #[inline(always)]
    fn mul_by_ext<const ASSUME_NO_PRODUCTS_BEFORE: bool>(
        &self,
        _other: &E,
        _ctx: &Self::CollapseContext,
    ) -> E {
        unreachable!()
    }
    #[inline(always)]
    fn sub_from_ext<const ASSUME_NO_PRODUCTS_BEFORE: bool>(
        &self,
        _other: &E,
        _ctx: &Self::CollapseContext,
    ) -> E {
        unreachable!()
    }
}

#[derive(Clone, Copy, Debug)]
pub struct BaseFieldRepresentation<F: PrimeField>(pub(crate) F);

impl<F: PrimeField, E: FieldExtension<F> + Field> EvaluationRepresentation<F, E>
    for BaseFieldRepresentation<F>
{
    type CollapseContext = ();
    type CollapsedForm = F;
    #[inline(always)]
    fn collapse(self, _ctx: &Self::CollapseContext) -> Self::CollapsedForm {
        self.0
    }
    #[inline(always)]
    fn collapse_for_batch_eval(self, _ctx: &Self::CollapseContext, challenge: &E) -> E {
        let mut result = *challenge;
        result.mul_assign_by_base(&self.0);
        result
    }
    #[inline(always)]
    fn repr_add_assign<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&mut self, other: &Self) {
        self.0.add_assign(&other.0);
    }
    #[inline(always)]
    fn repr_sub_assign<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&mut self, other: &Self) {
        self.0.sub_assign(&other.0);
    }
    #[inline(always)]
    fn repr_mul_assign<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&mut self, other: &Self) {
        self.0.mul_assign(&other.0);
    }
    #[inline(always)]
    fn add_with_ext<const ASSUME_NO_PRODUCTS_BEFORE: bool>(
        &self,
        other: &E,
        _ctx: &Self::CollapseContext,
    ) -> E {
        let mut result = *other;
        result.add_assign_base(&self.0);
        result
    }
    #[inline(always)]
    fn mul_by_ext<const ASSUME_NO_PRODUCTS_BEFORE: bool>(
        &self,
        other: &E,
        _ctx: &Self::CollapseContext,
    ) -> E {
        let mut result = *other;
        result.mul_assign_by_base(&self.0);
        result
    }
    #[inline(always)]
    fn sub_from_ext<const ASSUME_NO_PRODUCTS_BEFORE: bool>(
        &self,
        other: &E,
        _ctx: &Self::CollapseContext,
    ) -> E {
        let mut result = *other;
        result.sub_assign_base(&self.0);

        result
    }
}

#[derive(Clone, Copy, Debug)]
pub struct BaseFieldFoldedOnceRepresentation<F: PrimeField> {
    pub(crate) c0: F,
    pub(crate) c1: F,
    pub(crate) computed_r2_coeff: F,
}

impl<F: PrimeField> BaseFieldFoldedOnceRepresentation<F> {
    #[inline(always)]
    pub fn new(c0: F, c1: F) -> Self {
        Self {
            c0,
            c1,
            computed_r2_coeff: F::ZERO,
        }
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field> EvaluationRepresentation<F, E>
    for BaseFieldFoldedOnceRepresentation<F>
{
    type CollapseContext = (E, E);
    type CollapsedForm = E;
    #[inline(always)]
    fn collapse(self, ctx: &Self::CollapseContext) -> Self::CollapsedForm {
        let (mut r, r2) = *ctx;
        let mut result = r2;
        result.mul_assign_by_base(&self.computed_r2_coeff);
        r.mul_assign_by_base(&self.c1);
        result.add_assign(&r);
        result.add_assign_base(&self.c0);

        result
    }
    #[inline(always)]
    fn collapse_for_batch_eval(self, ctx: &Self::CollapseContext, challenge: &E) -> E {
        let mut result = self.collapse(ctx);
        result.mul_assign(challenge);
        result
    }
    #[inline(always)]
    fn repr_add_assign<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&mut self, other: &Self) {
        self.c0.add_assign(&other.c0);
        self.c1.add_assign(&other.c1);
        if ASSUME_NO_PRODUCTS_BEFORE == false {
            self.computed_r2_coeff.add_assign(&other.computed_r2_coeff);
        }
    }
    #[inline(always)]
    fn repr_sub_assign<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&mut self, other: &Self) {
        self.c0.sub_assign(&other.c0);
        self.c1.sub_assign(&other.c1);
        if ASSUME_NO_PRODUCTS_BEFORE == false {
            self.computed_r2_coeff.sub_assign(&other.computed_r2_coeff);
        }
    }
    #[inline(always)]
    fn repr_mul_assign<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&mut self, other: &Self) {
        if ASSUME_NO_PRODUCTS_BEFORE == false {
            panic!();
        }
        self.computed_r2_coeff = self.c1;
        self.computed_r2_coeff.mul_assign(&other.c1);
        self.c1.mul_assign(&other.c0);
        let mut tt = self.c0;
        tt.mul_assign(&other.c1);
        self.c1.add_assign(&tt);

        self.c0.mul_assign(&other.c0);
    }
    #[inline(always)]
    fn add_with_ext<const ASSUME_NO_PRODUCTS_BEFORE: bool>(
        &self,
        other: &E,
        ctx: &Self::CollapseContext,
    ) -> E {
        if ASSUME_NO_PRODUCTS_BEFORE == false {
            panic!();
        }
        let mut t = ctx.0;
        t.mul_assign_by_base(&self.c1);
        t.add_assign_base(&self.c0);
        t.add_assign(other);

        t
    }
    #[inline(always)]
    fn mul_by_ext<const ASSUME_NO_PRODUCTS_BEFORE: bool>(
        &self,
        other: &E,
        ctx: &Self::CollapseContext,
    ) -> E {
        if ASSUME_NO_PRODUCTS_BEFORE == false {
            panic!();
        }
        let mut t = ctx.0;
        t.mul_assign_by_base(&self.c1);
        t.add_assign_base(&self.c0);
        t.mul_assign(other);

        t
    }
    #[inline(always)]
    fn sub_from_ext<const ASSUME_NO_PRODUCTS_BEFORE: bool>(
        &self,
        other: &E,
        ctx: &Self::CollapseContext,
    ) -> E {
        let mut result = *other;
        let mut t = ctx.0;
        t.mul_assign_by_base(&self.c1);
        t.add_assign_base(&self.c0);

        result.sub_assign(&t);

        result
    }
}

#[derive(Clone, Copy, Debug)]
pub struct ExtensionFieldRepresentation<F: PrimeField, E: FieldExtension<F> + Field> {
    pub(crate) value: E,
    pub(crate) _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> ExtensionFieldRepresentation<F, E> {
    #[inline(always)]
    pub fn new(value: E) -> Self {
        Self {
            value,
            _marker: core::marker::PhantomData,
        }
    }
    #[inline(always)]
    pub fn into_value(self) -> E {
        self.value
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field> EvaluationRepresentation<F, E>
    for ExtensionFieldRepresentation<F, E>
{
    type CollapseContext = ();
    type CollapsedForm = E;
    #[inline(always)]
    fn collapse(self, _ctx: &Self::CollapseContext) -> Self::CollapsedForm {
        self.value
    }
    #[inline(always)]
    fn collapse_for_batch_eval(self, ctx: &Self::CollapseContext, challenge: &E) -> E {
        let mut result = self.collapse(ctx);
        result.mul_assign(challenge);
        result
    }
    #[inline(always)]
    fn repr_add_assign<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&mut self, other: &Self) {
        self.value.add_assign(&other.value);
    }
    #[inline(always)]
    fn repr_sub_assign<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&mut self, other: &Self) {
        self.value.sub_assign(&other.value);
    }
    #[inline(always)]
    fn repr_mul_assign<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&mut self, other: &Self) {
        self.value.mul_assign(&other.value);
    }
    #[inline(always)]
    fn add_with_ext<const ASSUME_NO_PRODUCTS_BEFORE: bool>(
        &self,
        other: &E,
        _ctx: &Self::CollapseContext,
    ) -> E {
        let mut t = self.value;
        t.add_assign(other);

        t
    }
    #[inline(always)]
    fn mul_by_ext<const ASSUME_NO_PRODUCTS_BEFORE: bool>(
        &self,
        other: &E,
        _ctx: &Self::CollapseContext,
    ) -> E {
        let mut t = self.value;
        t.mul_assign(other);

        t
    }
    #[inline(always)]
    fn sub_from_ext<const ASSUME_NO_PRODUCTS_BEFORE: bool>(
        &self,
        other: &E,
        _ctx: &Self::CollapseContext,
    ) -> E {
        let mut result = *other;
        result.sub_assign(&self.value);

        result
    }
}

pub trait EvaluationFormStorage<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    R: EvaluationRepresentation<F, E>,
>: Send + Sync
{
    const SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP: bool;

    fn dummy() -> Self;
    fn get_collapse_context(&self) -> &R::CollapseContext;
    fn get_at_index(&self, index: usize) -> R;
    #[inline(always)]
    fn get_f0_only(&self, index: usize) -> R {
        self.get_f0_and_f1_minus_f0(index)[0]
    }
    #[inline(always)]
    fn get_f1_minus_f0_only(&self, index: usize) -> R {
        self.get_f0_and_f1_minus_f0(index)[1]
    }
    fn get_f0_and_f1(&self, index: usize) -> [R; 2];
    #[inline(always)]
    fn get_f0_and_f1_minus_f0(&self, index: usize) -> [R; 2] {
        let [f0, mut f1_minus_f0] = self.get_f0_and_f1(index);
        f1_minus_f0.repr_sub_assign::<true>(&f0);

        [f0, f1_minus_f0]
    }
    #[inline(always)]
    fn get_two_points<const EXPLICIT_FORM: bool>(&self, index: usize) -> [R; 2] {
        if EXPLICIT_FORM {
            self.get_f0_and_f1(index)
        } else {
            self.get_f0_and_f1_minus_f0(index)
        }
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field, R: EvaluationRepresentation<F, E>>
    EvaluationFormStorage<F, E, R> for ()
{
    const SHOULD_ACCESS_TO_PREPARE_FOR_NEXT_STEP: bool = false;

    fn dummy() -> Self {
        ()
    }
    #[inline(always)]
    fn get_collapse_context(&self) -> &R::CollapseContext {
        unreachable!()
    }
    #[inline(always)]
    fn get_at_index(&self, _index: usize) -> R {
        unreachable!()
    }
    #[inline(always)]
    fn get_f0_and_f1(&self, _index: usize) -> [R; 2] {
        unreachable!()
    }
}

pub trait SingleInputTypeBatchSumcheckEvaluationKernel<F: PrimeField, E: FieldExtension<F> + Field>:
    Send + Sync
{
    fn num_challenges(&self) -> usize;
    fn evaluate_first_round<
        R0: EvaluationRepresentation<F, E>,
        S0: EvaluationFormStorage<F, E, R0>,
        ROUT: EvaluationRepresentation<F, E>,
        SOUT: EvaluationFormStorage<F, E, ROUT>,
    >(
        &self,
        index: usize,
        r0_sources: &[S0],
        _output_sources: &[SOUT],
        batch_challenges: &[E],
        collapse_ctx: &R0::CollapseContext,
    ) -> [E; 2] {
        self.evaluate::<R0, S0, false>(index, r0_sources, batch_challenges, collapse_ctx)
    }

    fn evaluate<
        R0: EvaluationRepresentation<F, E>,
        S0: EvaluationFormStorage<F, E, R0>,
        const EXPLICIT_FORM: bool,
    >(
        &self,
        index: usize,
        r0_sources: &[S0],
        batch_challenges: &[E],
        collapse_ctx: &R0::CollapseContext,
    ) -> [E; 2];
}

pub trait TwoInputTypesBatchSumcheckEvaluationKernel<F: PrimeField, E: FieldExtension<F> + Field> {
    fn num_challenges(&self) -> usize;

    fn evaluate_first_round<
        R0: EvaluationRepresentation<F, E>,
        S0: EvaluationFormStorage<F, E, R0>,
        R1: EvaluationRepresentation<F, E>,
        S1: EvaluationFormStorage<F, E, R1>,
        ROUT: EvaluationRepresentation<F, E>,
        SOUT: EvaluationFormStorage<F, E, ROUT>,
    >(
        &self,
        index: usize,
        r0_sources: &[S0],
        r1_sources: &[S1],
        _output_sources: &[SOUT],
        batch_challenges: &[E],
    ) -> [E; 2] {
        self.evaluate::<R0, S0, R1, S1, false>(index, r0_sources, r1_sources, batch_challenges)
    }

    fn evaluate<
        R0: EvaluationRepresentation<F, E>,
        S0: EvaluationFormStorage<F, E, R0>,
        R1: EvaluationRepresentation<F, E>,
        S1: EvaluationFormStorage<F, E, R1>,
        const EXPLICIT_FORM: bool,
    >(
        &self,
        index: usize,
        r0_sources: &[S0],
        r1_sources: &[S1],
        batch_challenges: &[E],
    ) -> [E; 2];
}
