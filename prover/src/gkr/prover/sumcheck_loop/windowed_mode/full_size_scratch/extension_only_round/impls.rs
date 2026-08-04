use super::*;

#[inline(always)]
pub(crate) fn read_ext_and_fold_8<F: Field>(
    src: &DisjointAccessQuasiSlice<F, false>,
    precomputed_eq_prefix: &[F; 8],
    stride: usize,
    row: usize,
) -> F {
    #[cfg(target_arch = "aarch64")]
    if crate::gkr::prover::sumcheck_loop::windowed_mode::neon::is_bb4::<F>() {
        unsafe {
            let result = crate::gkr::prover::sumcheck_loop::windowed_mode::neon::fold8_ext(
                src.ptr as *const _,
                &*(precomputed_eq_prefix as *const [F; 8] as *const _),
                stride,
                row,
            );
            return *(&result as *const _ as *const F);
        }
    }
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
    #[cfg(target_arch = "aarch64")]
    if crate::gkr::prover::sumcheck_loop::windowed_mode::neon::is_bb4::<F>() {
        unsafe {
            let result = crate::gkr::prover::sumcheck_loop::windowed_mode::neon::fold2_ext(
                src.ptr as *const _,
                &*(challenge as *const F as *const _),
                stride,
                row,
            );
            return *(&result as *const _ as *const F);
        }
    }
    let f0 = src.read(row);
    let f1 = src.read(row + stride);
    let mut t = f1;
    t.sub_assign(&f0);
    t.mul_assign(&challenge);
    t.add_assign(&f0);

    t
}
