use super::*;

#[inline(always)]
pub(crate) fn read_ext_and_fold_8<F: Field>(
    src: &DisjointAccessQuasiSlice<F, false>,
    precomputed_eq_prefix: &[F; 8],
    stride: usize,
    row: usize,
) -> F {
    let mut offset = row;
    let mut result = precomputed_eq_prefix[0];
    result.mul_assign(&src.read(offset));
    offset += stride;
    for i in 1..8 {
        let mut t = precomputed_eq_prefix[i];
        t.mul_assign(&src.read(offset));
        result.add_assign(&t);
        offset += stride;
    }

    result
}

#[inline(always)]
pub(crate) fn read_ext_and_fold_2<F: Field>(
    src: &DisjointAccessQuasiSlice<F, false>,
    challenge: &F,
    stride: usize,
    row: usize,
) -> F {
    let f0 = src.read(row);
    let f1 = src.read(row + stride);
    let mut t = f1;
    t.sub_assign(&f0);
    t.mul_assign(&challenge);
    t.add_assign(&f0);

    t
}
