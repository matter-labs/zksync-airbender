use super::*;

#[derive(Clone, Copy, Debug)]
pub struct BaseFieldRepresentation<F: PrimeField>(pub(crate) F);

impl<F: PrimeField, E: FieldExtension<F> + Field> EvaluationRepresentaionBase<F, E>
    for BaseFieldRepresentation<F>
{
    type Product = Self;
    type CTX = ();

    #[inline(always)]
    fn into_ext(self, _ctx: &Self::CTX) -> E {
        E::from_base(self.0)
    }
    #[inline(always)]
    fn add_other(self, other: &Self) -> Self {
        let mut t = self.0;
        t.add_assign(&other.0);
        Self(t)
    }
    #[inline(always)]
    fn sub_other(self, other: &Self) -> Self {
        let mut t = self.0;
        t.sub_assign(&other.0);
        Self(t)
    }
    #[inline(always)]
    fn mul_by_base(self, other: &F) -> Self {
        let mut t = self.0;
        t.sub_assign(&other);
        Self(t)
    }
    #[inline(always)]
    fn mul_by_ext_and_into_ext(self, other: &E, _ctx: &Self::CTX) -> E {
        let mut result = *other;
        result.mul_assign_by_base(&self.0);
        result
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field> EvaluationRepresentaionExt<F, E>
    for BaseFieldRepresentation<F>
{
    type Base = Self;
    type CTX = ();

    #[inline(always)]
    fn into_ext(self, _ctx: &Self::CTX) -> E {
        E::from_base(self.0)
    }
    #[inline(always)]
    fn add_other(self, other: &Self) -> Self {
        let mut t = self.0;
        t.add_assign(&other.0);
        Self(t)
    }
    #[inline(always)]
    fn sub_other(self, other: &Self) -> Self {
        let mut t = self.0;
        t.sub_assign(&other.0);
        Self(t)
    }
    #[inline(always)]
    fn add_base_repr(self, other: &Self::Base) -> Self {
        let mut t = self.0;
        t.add_assign(&other.0);
        Self(t)
    }
    #[inline(always)]
    fn sub_base_repr(self, other: &Self::Base) -> Self {
        let mut t = self.0;
        t.sub_assign(&other.0);
        Self(t)
    }
    #[inline(always)]
    fn mul_by_base(self, other: &F) -> Self {
        let mut t = self.0;
        t.mul_assign(&other);
        Self(t)
    }
    #[inline(always)]
    fn add_with_ext_and_into_ext(self, other: &E, _ctx: &Self::CTX) -> E {
        let mut result = *other;
        result.add_assign_base(&self.0);
        result
    }
    #[inline(always)]
    fn mul_by_ext_and_into_ext(self, other: &E, _ctx: &Self::CTX) -> E {
        let mut result = *other;
        result.mul_assign_by_base(&self.0);
        result
    }
}
