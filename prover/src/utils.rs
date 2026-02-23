use field::FieldExtension;
use field::{Mersenne31Field, Mersenne31Quartic};

#[cfg(feature = "prover")]
use field::{FixedArrayConvertible, PrimeField};

#[inline(always)]
pub fn mersenne_quartic_into_base_coeffs(el: Mersenne31Quartic) -> [Mersenne31Field; 4] {
    <Mersenne31Quartic as FieldExtension<Mersenne31Field>>::into_coeffs(el)
}

#[inline(always)]
pub fn mersenne_quartic_from_base_coeffs(coeffs: [Mersenne31Field; 4]) -> Mersenne31Quartic {
    <Mersenne31Quartic as FieldExtension<Mersenne31Field>>::from_coeffs(coeffs)
}

#[cfg(feature = "prover")]
#[inline(always)]
pub fn extension_field_into_base_coeffs<F: PrimeField, E: FieldExtension<F>>(
    el: E,
) -> [F; E::DEGREE]
where
    [(); E::DEGREE]: Sized,
{
    <E as FieldExtension<F>>::into_coeffs(el).into_array::<{ E::DEGREE }>()
}

#[cfg(feature = "prover")]
#[inline(always)]
pub fn extension_field_from_base_coeffs<F: PrimeField, E: FieldExtension<F>>(
    coeffs: [F; E::DEGREE],
) -> E
where
    [(); E::DEGREE]: Sized,
{
    <E as FieldExtension<F>>::from_coeffs(<E as FieldExtension<F>>::Coeffs::from_array(coeffs))
}
