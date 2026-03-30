use field::Field;
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

#[inline(always)]
pub(crate) fn lookup_index_into_encoding_tuple(
    lookup_row: usize,
    lookup_encoding_capacity: usize,
) -> (u32, u32) {
    let column = lookup_row / lookup_encoding_capacity;
    let row = lookup_row % lookup_encoding_capacity;

    (column as u32, row as u32)
}

#[inline(always)]
pub(crate) fn encoding_tuple_into_lookup_index(
    column: u32,
    row: u32,
    lookup_encoding_capacity: usize,
) -> usize {
    let offset = (column as usize) * lookup_encoding_capacity;
    offset + (row as usize)
}

#[cfg(feature = "prover")]
#[inline(always)]
pub(crate) fn compute_aggregated_key_value_dyn<F: PrimeField, E: FieldExtension<F> + Field>(
    base_value: F,
    key_values_to_aggregate: &[F],
    aggregation_challenges: &[E],
    additive_part: &E,
) -> E {
    assert_eq!(key_values_to_aggregate.len(), aggregation_challenges.len());
    let mut result = *additive_part;
    result.add_assign_base(&base_value);
    for (a, b) in key_values_to_aggregate
        .into_iter()
        .zip(aggregation_challenges.into_iter())
    {
        let mut t = *b;
        t.mul_assign_by_base(a);
        result.add_assign(&t);
    }

    result
}
