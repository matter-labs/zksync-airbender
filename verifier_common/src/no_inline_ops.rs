use field::{Field, FieldExtension};

// Verifier quotient code can be very large once inlined constraints are expanded.
// These wrappers keep hot arithmetic calls out-of-line to reduce compile-time blowup
// in verifier-only crates, while prover code keeps using direct field methods.

#[inline(never)]
pub fn add_assign<'a, T: Field>(lhs: &'a mut T, rhs: &T) -> &'a mut T {
    lhs.add_assign(rhs)
}

#[inline(never)]
pub fn sub_assign<'a, T: Field>(lhs: &'a mut T, rhs: &T) -> &'a mut T {
    lhs.sub_assign(rhs)
}

#[inline(never)]
pub fn mul_assign<'a, T: Field>(lhs: &'a mut T, rhs: &T) -> &'a mut T {
    lhs.mul_assign(rhs)
}

#[inline(never)]
pub fn negate<T: Field>(lhs: &mut T) -> &mut T {
    lhs.negate()
}

#[inline(never)]
pub fn square<T: Field>(lhs: &mut T) -> &mut T {
    lhs.square()
}

#[inline(never)]
pub fn double<T: Field>(lhs: &mut T) -> &mut T {
    lhs.double()
}

#[inline(never)]
pub fn add_assign_base<'a, T, Base>(lhs: &'a mut T, rhs: &Base) -> &'a mut T
where
    Base: Field,
    T: FieldExtension<Base>,
{
    lhs.add_assign_base(rhs)
}

#[inline(never)]
pub fn sub_assign_base<'a, T, Base>(lhs: &'a mut T, rhs: &Base) -> &'a mut T
where
    Base: Field,
    T: FieldExtension<Base>,
{
    lhs.sub_assign_base(rhs)
}

#[inline(never)]
pub fn mul_assign_by_base<'a, T, Base>(lhs: &'a mut T, rhs: &Base) -> &'a mut T
where
    Base: Field,
    T: FieldExtension<Base>,
{
    lhs.mul_assign_by_base(rhs)
}
