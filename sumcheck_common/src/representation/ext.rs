use super::*;

#[derive(Clone, Copy, Debug)]
pub struct ExtensionFieldRepresentation<F: PrimeField, E: FieldExtension<F> + Field>(
    pub(crate) E,
    pub(crate) core::marker::PhantomData<F>,
);

impl<F: PrimeField, E: FieldExtension<F> + Field> ExtensionFieldRepresentation<F, E> {
    #[inline(always)]
    pub fn new(value: E) -> Self {
        Self(value, core::marker::PhantomData)
    }
    #[inline(always)]
    pub fn into_value(self) -> E {
        self.0
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field> EvaluationRepresentaionBase<F, E>
    for ExtensionFieldRepresentation<F, E>
{
    type Product = Self;
    type CTX = ();

    #[inline(always)]
    fn zero() -> Self {
        Self::new(E::ZERO)
    }
    #[inline(always)]
    fn into_ext(self, _ctx: &Self::CTX) -> E {
        self.0
    }
    #[inline(always)]
    fn add_other(self, other: &Self) -> Self {
        let mut t = self.0;
        t.add_assign(&other.0);
        Self(t, core::marker::PhantomData)
    }
    #[inline(always)]
    fn sub_other(self, other: &Self) -> Self {
        let mut t = self.0;
        t.sub_assign(&other.0);
        Self(t, core::marker::PhantomData)
    }
    #[inline(always)]
    fn add_base(self, other: &F) -> Self {
        let mut t = self.0;
        t.add_assign_base(other);
        Self(t, core::marker::PhantomData)
    }
    #[inline(always)]
    fn mul_by_base(self, other: &F) -> Self {
        let mut t = self.0;
        t.mul_assign_by_base(other);
        Self(t, core::marker::PhantomData)
    }
    #[inline(always)]
    fn add_with_ext(self, other: &E, _ctx: &Self::CTX) -> E {
        let mut result = self.0;
        result.add_assign(other);
        result
    }
    #[inline(always)]
    fn sub_from_ext(self, other: &E, _ctx: &Self::CTX) -> E {
        let mut result = *other;
        result.sub_assign(&self.0);
        result
    }
    #[inline(always)]
    fn mul_by_ext(self, other: &E, _ctx: &Self::CTX) -> E {
        let mut result = *other;
        result.mul_assign(&self.0);
        result
    }
    #[inline(always)]
    fn mul_with_other(self, other: &Self) -> Self::Product {
        let mut t = self.0;
        t.mul_assign(&other.0);
        Self(t, core::marker::PhantomData)
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field> EvaluationRepresentaionExt<F, E>
    for ExtensionFieldRepresentation<F, E>
{
    type Base = Self;
    type CTX = ();

    #[inline(always)]
    fn zero() -> Self {
        Self::new(E::ZERO)
    }
    #[inline(always)]
    fn into_ext(self, _ctx: &Self::CTX) -> E {
        self.0
    }
    #[inline(always)]
    fn add_other(self, other: &Self) -> Self {
        let mut t = self.0;
        t.add_assign(&other.0);
        Self(t, core::marker::PhantomData)
    }
    #[inline(always)]
    fn sub_other(self, other: &Self) -> Self {
        let mut t = self.0;
        t.sub_assign(&other.0);
        Self(t, core::marker::PhantomData)
    }
    #[inline(always)]
    fn add_base_repr(self, other: &Self::Base) -> Self {
        let mut t = self.0;
        t.add_assign(&other.0);
        Self(t, core::marker::PhantomData)
    }
    #[inline(always)]
    fn sub_base_repr(self, other: &Self::Base) -> Self {
        let mut t = self.0;
        t.sub_assign(&other.0);
        Self(t, core::marker::PhantomData)
    }
    #[inline(always)]
    fn add_base(self, other: &F) -> Self {
        let mut t = self.0;
        t.add_assign_base(other);
        Self(t, core::marker::PhantomData)
    }
    #[inline(always)]
    fn mul_by_base(self, other: &F) -> Self {
        let mut t = self.0;
        t.mul_assign_by_base(other);
        Self(t, core::marker::PhantomData)
    }
    #[inline(always)]
    fn add_with_ext(self, other: &E, _ctx: &Self::CTX) -> E {
        let mut result = *other;
        result.add_assign(&self.0);
        result
    }
    #[inline(always)]
    fn mul_by_ext(self, other: &E, _ctx: &Self::CTX) -> E {
        let mut result = *other;
        result.mul_assign(&self.0);
        result
    }
}
