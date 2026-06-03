use super::*;

// lazy representation as c0 + c1 * folding_challenge == f0 + (f1 - f0) * folding_challenge

#[derive(Clone, Copy, Debug)]
pub struct BaseFieldFoldedOnceRepresentation<F: PrimeField> {
    pub(crate) c0: F, // f0
    pub(crate) c1: F, // f1 - f0
}

impl<F: PrimeField> BaseFieldFoldedOnceRepresentation<F> {
    #[inline(always)]
    pub fn new(c0: F, c1: F) -> Self {
        Self { c0, c1 }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct BaseFieldFoldedOnceRepresentationProduct<F: PrimeField> {
    pub(crate) c0: F, // f0
    pub(crate) c1: F, // f1 - f0
    pub(crate) c2: F,
}

impl<F: PrimeField> BaseFieldFoldedOnceRepresentationProduct<F> {
    #[inline(always)]
    pub fn new(c0: F, c1: F, c2: F) -> Self {
        Self { c0, c1, c2 }
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field> EvaluationRepresentaionBase<F, E>
    for BaseFieldFoldedOnceRepresentation<F>
{
    type Product = BaseFieldFoldedOnceRepresentationProduct<F>;
    type CTX = (E, E);

    #[inline(always)]
    fn zero() -> Self {
        Self {
            c0: F::ZERO,
            c1: F::ZERO,
        }
    }
    #[inline(always)]
    fn into_ext(self, ctx: &Self::CTX) -> E {
        let mut result = ctx.0;
        result.mul_assign_by_base(&self.c1);
        result.add_assign_base(&self.c0);

        result
    }
    #[inline(always)]
    fn negate(self) -> Self {
        let mut c0 = self.c0;
        let mut c1 = self.c1;
        c0.negate();
        c1.negate();

        Self { c0, c1 }
    }
    #[inline(always)]
    fn add_other(self, other: &Self) -> Self {
        let mut c0 = self.c0;
        let mut c1 = self.c1;
        c0.add_assign(&other.c0);
        c1.add_assign(&other.c1);

        Self { c0, c1 }
    }
    #[inline(always)]
    fn sub_other(self, other: &Self) -> Self {
        let mut c0 = self.c0;
        let mut c1 = self.c1;
        c0.sub_assign(&other.c0);
        c1.sub_assign(&other.c1);

        Self { c0, c1 }
    }
    #[inline(always)]
    fn add_base(self, other: &F) -> Self {
        // only c0 coefficient
        let mut c0 = self.c0;
        let c1 = self.c1;
        c0.add_assign(other);

        Self { c0, c1 }
    }
    #[inline(always)]
    fn mul_by_base(self, other: &F) -> Self {
        let mut c0 = self.c0;
        let mut c1 = self.c1;
        c0.mul_assign(&other);
        c1.mul_assign(&other);

        Self { c0, c1 }
    }
    #[inline(always)]
    fn add_with_ext(self, other: &E, ctx: &Self::CTX) -> E {
        let mut result = self.into_ext(ctx);
        result.add_assign(other);
        result
    }
    #[inline(always)]
    fn sub_from_ext(self, other: &E, ctx: &Self::CTX) -> E {
        let mut result = *other;
        result.sub_assign(&self.into_ext(ctx));
        result
    }
    #[inline(always)]
    fn mul_by_ext(self, other: &E, ctx: &Self::CTX) -> E {
        let mut result = self.into_ext(ctx);
        result.mul_assign(other);
        result
    }
    #[inline(always)]
    fn mul_with_other(self, other: &Self) -> Self::Product {
        // schoolbook (c0 + r * c1) * (c0 + r * c1)
        let mut c0 = self.c0;
        c0.mul_assign(&other.c0);

        let mut c1 = self.c1;
        c1.mul_assign(&other.c0);
        let mut t = self.c0;
        t.mul_assign(&other.c1);
        c1.add_assign(&t);

        let mut c2 = self.c1;
        c2.mul_assign(&other.c1);

        BaseFieldFoldedOnceRepresentationProduct { c0, c1, c2 }
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field> EvaluationRepresentaionExt<F, E>
    for BaseFieldFoldedOnceRepresentationProduct<F>
{
    type Base = BaseFieldFoldedOnceRepresentation<F>;
    type CTX = (E, E);

    #[inline(always)]
    fn zero() -> Self {
        Self {
            c0: F::ZERO,
            c1: F::ZERO,
            c2: F::ZERO,
        }
    }
    #[inline(always)]
    fn into_ext(self, ctx: &Self::CTX) -> E {
        let (mut r, r2) = *ctx;
        let mut result = r2;
        result.mul_assign_by_base(&self.c2);

        r.mul_assign_by_base(&self.c1);
        result.add_assign(&r);

        result.add_assign_base(&self.c0);

        result
    }
    #[inline(always)]
    fn negate(self) -> Self {
        let mut c0 = self.c0;
        let mut c1 = self.c1;
        let mut c2 = self.c2;
        c0.negate();
        c1.negate();
        c2.negate();

        Self { c0, c1, c2 }
    }
    #[inline(always)]
    fn add_other(self, other: &Self) -> Self {
        let mut c0 = self.c0;
        let mut c1 = self.c1;
        let mut c2 = self.c2;
        c0.add_assign(&other.c0);
        c1.add_assign(&other.c1);
        c2.add_assign(&other.c2);

        Self { c0, c1, c2 }
    }
    #[inline(always)]
    fn sub_other(self, other: &Self) -> Self {
        let mut c0 = self.c0;
        let mut c1 = self.c1;
        let mut c2 = self.c2;
        c0.sub_assign(&other.c0);
        c1.sub_assign(&other.c1);
        c2.sub_assign(&other.c2);

        Self { c0, c1, c2 }
    }
    #[inline(always)]
    fn add_base_repr(self, other: &Self::Base) -> Self {
        let mut c0 = self.c0;
        let mut c1 = self.c1;
        c0.add_assign(&other.c0);
        c1.add_assign(&other.c1);

        Self {
            c0,
            c1,
            c2: self.c2,
        }
    }
    #[inline(always)]
    fn sub_base_repr(self, other: &Self::Base) -> Self {
        let mut c0 = self.c0;
        let mut c1 = self.c1;
        c0.sub_assign(&other.c0);
        c1.sub_assign(&other.c1);

        Self {
            c0,
            c1,
            c2: self.c2,
        }
    }
    #[inline(always)]
    fn add_base(self, other: &F) -> Self {
        // only c0 coefficient
        let mut c0 = self.c0;
        let c1 = self.c1;
        let c2 = self.c2;
        c0.add_assign(other);

        Self { c0, c1, c2 }
    }
    #[inline(always)]
    fn mul_by_base(self, other: &F) -> Self {
        let mut c0 = self.c0;
        let mut c1 = self.c1;
        let mut c2 = self.c2;
        c0.mul_assign(other);
        c1.mul_assign(other);
        c2.mul_assign(other);

        Self { c0, c1, c2 }
    }
    #[inline(always)]
    fn add_with_ext(self, other: &E, ctx: &Self::CTX) -> E {
        let mut result = self.into_ext(ctx);
        result.add_assign(other);
        result
    }
    #[inline(always)]
    fn mul_by_ext(self, other: &E, ctx: &Self::CTX) -> E {
        let mut result = self.into_ext(ctx);
        result.mul_assign(other);
        result
    }
}
