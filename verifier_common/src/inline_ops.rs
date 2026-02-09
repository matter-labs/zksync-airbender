use field::{Field, FieldExtension};

// RISC-V verifier builds benefit from preserving direct inlined arithmetic,
// so generated quotient code can use this module as the fast-path backend.

#[inline(always)]
pub fn add_assign<'a, T: Field>(lhs: &'a mut T, rhs: &T) -> &'a mut T {
    lhs.add_assign(rhs)
}

#[inline(always)]
pub fn sub_assign<'a, T: Field>(lhs: &'a mut T, rhs: &T) -> &'a mut T {
    lhs.sub_assign(rhs)
}

#[inline(always)]
pub fn mul_assign<'a, T: Field>(lhs: &'a mut T, rhs: &T) -> &'a mut T {
    lhs.mul_assign(rhs)
}

#[inline(always)]
pub fn negate<T: Field>(lhs: &mut T) -> &mut T {
    lhs.negate()
}

#[inline(always)]
pub fn square<T: Field>(lhs: &mut T) -> &mut T {
    lhs.square()
}

#[inline(always)]
pub fn double<T: Field>(lhs: &mut T) -> &mut T {
    lhs.double()
}

#[inline(always)]
pub fn add_assign_base<'a, T, Base>(lhs: &'a mut T, rhs: &Base) -> &'a mut T
where
    Base: Field,
    T: FieldExtension<Base>,
{
    lhs.add_assign_base(rhs)
}

#[inline(always)]
pub fn sub_assign_base<'a, T, Base>(lhs: &'a mut T, rhs: &Base) -> &'a mut T
where
    Base: Field,
    T: FieldExtension<Base>,
{
    lhs.sub_assign_base(rhs)
}

#[inline(always)]
pub fn mul_assign_by_base<'a, T, Base>(lhs: &'a mut T, rhs: &Base) -> &'a mut T
where
    Base: Field,
    T: FieldExtension<Base>,
{
    lhs.mul_assign_by_base(rhs)
}
