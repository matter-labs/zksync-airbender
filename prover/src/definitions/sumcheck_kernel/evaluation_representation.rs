use super::*;

pub trait EvaluationRepresentation<F: PrimeField, E: FieldExtension<F> + Field>:
    'static + Clone + Copy + core::fmt::Debug + Send + Sync
{
    type CollapseContext: 'static + Clone + Copy + core::fmt::Debug + Send + Sync;
    fn collapse_as_ext_field_element(self, ctx: &Self::CollapseContext) -> E;

    fn collapse_into_ext_with_challenge(self, ctx: &Self::CollapseContext, challenge: &E) -> E;

    fn from_base_constant(value: F) -> Self;
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
    fn mul_by_base<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&self, other: &F) -> Self;
}

impl<F: PrimeField, E: FieldExtension<F> + Field> EvaluationRepresentation<F, E> for () {
    type CollapseContext = ();
    #[inline(always)]
    fn from_base_constant(_value: F) -> Self {
        ()
    }
    #[inline(always)]
    fn collapse_as_ext_field_element(self, _ctx: &Self::CollapseContext) -> E {
        E::ZERO
    }
    #[inline(always)]
    fn collapse_into_ext_with_challenge(self, _ctx: &Self::CollapseContext, _challenge: &E) -> E {
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
    #[inline(always)]
    fn mul_by_base<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&self, _other: &F) -> Self {
        unreachable!()
    }
}

#[derive(Clone, Copy, Debug)]
pub struct BaseFieldRepresentation<F: PrimeField>(pub(crate) F);

impl<F: PrimeField, E: FieldExtension<F> + Field> EvaluationRepresentation<F, E>
    for BaseFieldRepresentation<F>
{
    type CollapseContext = ();
    #[inline(always)]
    fn from_base_constant(value: F) -> Self {
        Self(value)
    }
    #[inline(always)]
    fn collapse_as_ext_field_element(self, _ctx: &Self::CollapseContext) -> E {
        E::from_base(self.0)
    }
    #[inline(always)]
    fn collapse_into_ext_with_challenge(self, _ctx: &Self::CollapseContext, challenge: &E) -> E {
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
    #[inline(always)]
    fn mul_by_base<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&self, other: &F) -> Self {
        let mut result = *other;
        result.mul_assign(&self.0);

        Self(result)
    }
}

// lazy representation as c0 + c1 * folding_challenge == f0 + (f1 - f0) * folding_challenge

#[derive(Clone, Copy, Debug)]
pub struct BaseFieldFoldedOnceRepresentation<F: PrimeField> {
    pub(crate) c0: F, // f0
    pub(crate) c1: F, // f1 - f0
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
    #[inline(always)]
    fn from_base_constant(value: F) -> Self {
        Self {
            c0: value,
            c1: F::ZERO,
            computed_r2_coeff: F::ZERO,
        }
    }
    #[inline(always)]
    fn collapse_as_ext_field_element(self, ctx: &Self::CollapseContext) -> E {
        let (mut r, r2) = *ctx;
        let mut result = r2;
        result.mul_assign_by_base(&self.computed_r2_coeff);

        r.mul_assign_by_base(&self.c1);
        result.add_assign(&r);

        result.add_assign_base(&self.c0);

        result
    }
    #[inline(always)]
    fn collapse_into_ext_with_challenge(self, ctx: &Self::CollapseContext, challenge: &E) -> E {
        let mut result = self.collapse_as_ext_field_element(ctx);
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
        assert_eq!(self.computed_r2_coeff, F::ZERO);

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
        assert_eq!(self.computed_r2_coeff, F::ZERO);

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
    #[inline(always)]
    fn mul_by_base<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&self, other: &F) -> Self {
        let mut result = *self;
        result.c0.mul_assign(other);
        result.c1.mul_assign(other);
        if ASSUME_NO_PRODUCTS_BEFORE == false {
            result.computed_r2_coeff.mul_assign(other);
        }

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
    #[inline(always)]
    fn from_base_constant(value: F) -> Self {
        Self {
            value: E::from_base(value),
            _marker: core::marker::PhantomData,
        }
    }
    #[inline(always)]
    fn collapse_as_ext_field_element(self, _ctx: &Self::CollapseContext) -> E {
        self.value
    }
    #[inline(always)]
    fn collapse_into_ext_with_challenge(self, _ctx: &Self::CollapseContext, challenge: &E) -> E {
        let mut result = self.value;
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
    #[inline(always)]
    fn mul_by_base<const ASSUME_NO_PRODUCTS_BEFORE: bool>(&self, other: &F) -> Self {
        let mut result = *self;
        result.value.mul_assign_by_base(other);

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
