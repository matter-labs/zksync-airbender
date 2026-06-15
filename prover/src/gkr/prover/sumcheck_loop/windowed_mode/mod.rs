use super::*;

use crate::gkr::prover::sumcheck::access_and_fold::*;

pub(crate) mod full_size_scratch;
pub(crate) mod sumcheck_loop;

#[inline(always)]
fn interpolate_at_inf_from_0_1_basis<F: Field>(a: F, b: F) -> F {
    let mut result = b;
    result.sub_assign(&a);
    result
}

#[inline(always)]
fn read_and_interpolate_field<F: Field>(
    dst: &mut [F; 27],
    src: &DisjointAccessQuasiSlice<F, false>,
    input_size: usize,
    row: usize,
) {
    let stride_step = input_size / 2;
    for x0 in 0..2 {
        let stride = stride_step * x0;
        let dst_offset = 9 * x0;
        for x1 in 0..2 {
            let stride_step = stride_step / 2;
            let stride = stride + x1 * stride_step;
            let dst_offset = dst_offset + 3 * x1;
            {
                let stride_step = stride_step / 2;
                let src_0_idx = stride + row;
                let src_1_idx = src_0_idx + stride_step;

                dst[dst_offset] = src.read(src_0_idx);
                dst[dst_offset + 1] = src.read(src_1_idx);
                dst[dst_offset + 2] =
                    interpolate_at_inf_from_0_1_basis(dst[dst_offset], dst[dst_offset + 1]);
            }
            // here we filled all options of (x0, x1, 0/1/inf)
        }

        // now get inf over x1
        for x2 in 0..3 {
            let src_0_idx = dst_offset + x2;
            let src_1_idx = dst_offset + 3 + x2;
            dst[dst_offset + 3 * 2 + x2] =
                interpolate_at_inf_from_0_1_basis(dst[src_0_idx], dst[src_1_idx]);
        }
    }

    // and get inf over x0
    for x1 in 0..3 {
        let dst_offset = 3 * x1;
        for x2 in 0..3 {
            let src_0_idx = 0 + dst_offset + x2;
            let src_1_idx = 9 + dst_offset + x2;
            dst[18 + dst_offset + x2] =
                interpolate_at_inf_from_0_1_basis(dst[src_0_idx], dst[src_1_idx]);
        }
    }
}

#[inline(always)]
fn read_without_interpolation<F: Field>(
    dst: &mut [F; 27],
    src: &DisjointAccessQuasiSlice<F, false>,
    input_size: usize,
    row: usize,
) {
    let stride_step = input_size / 2;
    for x0 in 0..2 {
        let stride = stride_step * x0;
        let dst_offset = 9 * x0;
        for x1 in 0..2 {
            let stride_step = stride_step / 2;
            let stride = stride + x1 * stride_step;
            let dst_offset = dst_offset + 3 * x1;
            {
                let stride_step = stride_step / 2;
                let src_0_idx = stride + row;
                let src_1_idx = src_0_idx + stride_step;

                dst[dst_offset] = src.read(src_0_idx);
                dst[dst_offset + 1] = src.read(src_1_idx);
            }
            // here we filled all options of (x0, x1, 0/1/inf)
        }
    }
}

#[inline(always)]
fn evaluate_quadratic_base<F: PrimeField, E: FieldExtension<F> + Field>(
    dst: &mut [E; 27],
    a: &[F; 27],
    b: &[F; 27],
    prefactor: &E,
) {
    for i in 0..27 {
        let mut t = a[i];
        t.mul_assign(&b[i]);
        let mut acc = *prefactor;
        acc.mul_assign_by_base(&t);
        dst[i].add_assign(&acc);
    }
}

#[inline(always)]
fn evaluate_quadratic_mixed<F: PrimeField, E: FieldExtension<F> + Field>(
    dst: &mut [E; 27],
    a: &[E; 27],
    b: &[F; 27],
    prefactor: &E,
) {
    for i in 0..27 {
        let mut t = a[i];
        t.mul_assign_by_base(&b[i]);
        let mut acc = *prefactor;
        acc.mul_assign(&t);
        dst[i].add_assign(&acc);
    }
}

#[inline(always)]
fn evaluate_quadratic_ext<F: Field, const N: usize>(
    dst: &mut [F; N],
    a: &[F; N],
    b: &[F; N],
    prefactor: &F,
) {
    for i in 0..N {
        let mut t = a[i];
        t.mul_assign(&b[i]);
        let mut acc = *prefactor;
        acc.mul_assign(&t);
        dst[i].add_assign(&acc);
    }
}

#[inline(always)]
fn evaluate_linear_base<F: PrimeField, E: FieldExtension<F> + Field>(
    dst: &mut [E; 27],
    a: &[F; 27],
    prefactor: &E,
) {
    // we only need a limited set of terms
    for i in 0..2 {
        let offset = 9 * i;
        for j in 0..2 {
            let offset = offset + 3 * j;
            for k in 0..2 {
                let mut acc = *prefactor;
                let t = a[offset + k];
                acc.mul_assign_by_base(&t);
                dst[offset + k].add_assign(&acc);
            }
        }
    }
}

#[inline(always)]
fn evaluate_linear_ext<F: Field>(dst: &mut [F; 27], a: &[F; 27], prefactor: &F) {
    // we only need a limited set of terms
    for i in 0..2 {
        let offset = 9 * i;
        for j in 0..2 {
            let offset = offset + 3 * j;
            for k in 0..2 {
                let mut acc = *prefactor;
                let t = a[offset + k];
                acc.mul_assign(&t);
                dst[offset + k].add_assign(&acc);
            }
        }
    }
}

#[inline(always)]
fn read_base_and_fold<F: PrimeField, E: FieldExtension<F> + Field>(
    src: &DisjointAccessQuasiSlice<F, false>,
    precomputed_eq_prefix: &[E; 8],
    stride: usize,
    row: usize,
) -> E {
    let mut offset = row;
    let mut result = precomputed_eq_prefix[0];
    result.mul_assign_by_base(&src.read(offset));
    offset += stride;
    for i in 1..8 {
        let mut t = precomputed_eq_prefix[i];
        t.mul_assign_by_base(&src.read(offset));
        result.add_assign(&t);
        offset += stride;
    }

    result
}

#[inline(always)]
fn read_base_then_fold_and_interpolate<F: PrimeField, E: FieldExtension<F> + Field>(
    dst: &mut [E; 27],
    src: &DisjointAccessQuasiSlice<F, false>,
    buffer: &mut DisjointAccessQuasiSlice<E, true>,
    precomputed_eq_prefix: &[E; 8],
    original_input_size: usize,
    row: usize,
) {
    let base_input_stride = original_input_size / 8;
    let input_size = base_input_stride;
    let stride_step = input_size / 2;
    for x0 in 0..2 {
        let stride = stride_step * x0;
        let dst_offset = 9 * x0;
        for x1 in 0..2 {
            let stride_step = stride_step / 2;
            let stride = stride + x1 * stride_step;
            let dst_offset = dst_offset + 3 * x1;
            {
                let stride_step = stride_step / 2;
                let src_0_idx = stride + row;
                let src_1_idx = src_0_idx + stride_step;

                let folded_0 =
                    read_base_and_fold(src, precomputed_eq_prefix, base_input_stride, src_0_idx);
                buffer.write(src_0_idx, folded_0);
                dst[dst_offset] = folded_0;

                let folded_1 =
                    read_base_and_fold(src, precomputed_eq_prefix, base_input_stride, src_0_idx);
                buffer.write(src_1_idx, folded_1);
                dst[dst_offset + 1] = folded_1;

                dst[dst_offset + 2] =
                    interpolate_at_inf_from_0_1_basis(dst[dst_offset], dst[dst_offset + 1]);
            }
            // here we filled all options of (x0, x1, 0/1/inf)
        }

        // now get inf over x1
        for x2 in 0..3 {
            let src_0_idx = dst_offset + x2;
            let src_1_idx = dst_offset + 3 + x2;
            dst[dst_offset + 3 * 2 + x2] =
                interpolate_at_inf_from_0_1_basis(dst[src_0_idx], dst[src_1_idx]);
        }
    }

    // and get inf over x0
    for x1 in 0..3 {
        let dst_offset = 3 * x1;
        for x2 in 0..3 {
            let src_0_idx = 0 + dst_offset + x2;
            let src_1_idx = 9 + dst_offset + x2;
            dst[18 + dst_offset + x2] =
                interpolate_at_inf_from_0_1_basis(dst[src_0_idx], dst[src_1_idx]);
        }
    }
}

#[inline(always)]
fn read_base_then_fold_without_interpolation<F: PrimeField, E: FieldExtension<F> + Field>(
    dst: &mut [E; 27],
    src: &DisjointAccessQuasiSlice<F, false>,
    buffer: &mut DisjointAccessQuasiSlice<E, true>,
    precomputed_eq_prefix: &[E; 8],
    original_input_size: usize,
    row: usize,
) {
    let base_input_stride = original_input_size / 8;
    let input_size = base_input_stride;
    let stride_step = input_size / 2;
    for x0 in 0..2 {
        let stride = stride_step * x0;
        let dst_offset = 9 * x0;
        for x1 in 0..2 {
            let stride_step = stride_step / 2;
            let stride = stride + x1 * stride_step;
            let dst_offset = dst_offset + 3 * x1;
            {
                let stride_step = stride_step / 2;
                let src_0_idx = stride + row;
                let src_1_idx = src_0_idx + stride_step;

                let folded_0 =
                    read_base_and_fold(src, precomputed_eq_prefix, base_input_stride, src_0_idx);
                buffer.write(src_0_idx, folded_0);
                dst[dst_offset] = folded_0;

                let folded_1 =
                    read_base_and_fold(src, precomputed_eq_prefix, base_input_stride, src_0_idx);
                buffer.write(src_1_idx, folded_1);
                dst[dst_offset + 1] = folded_1;
            }
            // here we filled all options of (x0, x1, 0/1/inf)
        }
    }
}

#[inline(always)]
fn read_ext_and_fold<F: Field>(
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
fn read_ext_then_fold_and_interpolate<F: PrimeField, E: FieldExtension<F> + Field>(
    dst: &mut [E; 27],
    src: &DisjointAccessQuasiSlice<E, false>,
    buffer: &mut DisjointAccessQuasiSlice<E, true>,
    precomputed_eq_prefix: &[E; 8],
    original_input_size: usize,
    row: usize,
) {
    let base_input_stride = original_input_size / 8;
    let input_size = base_input_stride;
    let stride_step = input_size / 2;
    for x0 in 0..2 {
        let stride = stride_step * x0;
        let dst_offset = 9 * x0;
        for x1 in 0..2 {
            let stride_step = stride_step / 2;
            let stride = stride + x1 * stride_step;
            let dst_offset = dst_offset + 3 * x1;
            {
                let stride_step = stride_step / 2;
                let src_0_idx = stride + row;
                let src_1_idx = src_0_idx + stride_step;

                let folded_0 =
                    read_ext_and_fold(src, precomputed_eq_prefix, base_input_stride, src_0_idx);
                buffer.write(src_0_idx, folded_0);
                dst[dst_offset] = folded_0;

                let folded_1 =
                    read_ext_and_fold(src, precomputed_eq_prefix, base_input_stride, src_0_idx);
                buffer.write(src_1_idx, folded_1);
                dst[dst_offset + 1] = folded_1;

                dst[dst_offset + 2] =
                    interpolate_at_inf_from_0_1_basis(dst[dst_offset], dst[dst_offset + 1]);
            }
            // here we filled all options of (x0, x1, 0/1/inf)
        }

        // now get inf over x1
        for x2 in 0..3 {
            let src_0_idx = dst_offset + x2;
            let src_1_idx = dst_offset + 3 + x2;
            dst[dst_offset + 3 * 2 + x2] =
                interpolate_at_inf_from_0_1_basis(dst[src_0_idx], dst[src_1_idx]);
        }
    }

    // and get inf over x0
    for x1 in 0..3 {
        let dst_offset = 3 * x1;
        for x2 in 0..3 {
            let src_0_idx = 0 + dst_offset + x2;
            let src_1_idx = 9 + dst_offset + x2;
            dst[18 + dst_offset + x2] =
                interpolate_at_inf_from_0_1_basis(dst[src_0_idx], dst[src_1_idx]);
        }
    }
}

#[inline(always)]
fn read_ext_then_fold_without_interpolation<F: PrimeField, E: FieldExtension<F> + Field>(
    dst: &mut [E; 27],
    src: &DisjointAccessQuasiSlice<E, false>,
    buffer: &mut DisjointAccessQuasiSlice<E, true>,
    precomputed_eq_prefix: &[E; 8],
    original_input_size: usize,
    row: usize,
) {
    let base_input_stride = original_input_size / 8;
    let input_size = base_input_stride;
    let stride_step = input_size / 2;
    for x0 in 0..2 {
        let stride = stride_step * x0;
        let dst_offset = 9 * x0;
        for x1 in 0..2 {
            let stride_step = stride_step / 2;
            let stride = stride + x1 * stride_step;
            let dst_offset = dst_offset + 3 * x1;
            {
                let stride_step = stride_step / 2;
                let src_0_idx = stride + row;
                let src_1_idx = src_0_idx + stride_step;

                let folded_0 =
                    read_ext_and_fold(src, precomputed_eq_prefix, base_input_stride, src_0_idx);
                buffer.write(src_0_idx, folded_0);
                dst[dst_offset] = folded_0;

                let folded_1 =
                    read_ext_and_fold(src, precomputed_eq_prefix, base_input_stride, src_0_idx);
                buffer.write(src_1_idx, folded_1);
                dst[dst_offset + 1] = folded_1;
            }
            // here we filled all options of (x0, x1, 0/1/inf)
        }
    }
}

#[inline(always)]
fn read_ext_then_fold_and_interpolate_inplace<F: PrimeField, E: FieldExtension<F> + Field>(
    dst: &mut [E; 27],
    buffer: &mut DisjointAccessQuasiSlice<E, false>,
    unfolded_input_size: usize,
    precomputed_eq_prefix: &[E; 8],
    row: usize,
) {
    let unfolded_input_stride = unfolded_input_size / 8;
    let input_size = unfolded_input_stride;
    let stride_step = input_size / 2;
    for x0 in 0..2 {
        let stride = stride_step * x0;
        let dst_offset = 9 * x0;
        for x1 in 0..2 {
            let stride_step = stride_step / 2;
            let stride = stride + x1 * stride_step;
            let dst_offset = dst_offset + 3 * x1;
            {
                let stride_step = stride_step / 2;
                let src_0_idx = stride + row;
                let src_1_idx = src_0_idx + stride_step;

                let folded_0 = read_ext_and_fold(
                    buffer,
                    precomputed_eq_prefix,
                    unfolded_input_stride,
                    src_0_idx,
                );
                buffer.write(src_0_idx, folded_0);
                dst[dst_offset] = folded_0;

                let folded_1 = read_ext_and_fold(
                    buffer,
                    precomputed_eq_prefix,
                    unfolded_input_stride,
                    src_0_idx,
                );
                buffer.write(src_1_idx, folded_1);
                dst[dst_offset + 1] = folded_1;

                dst[dst_offset + 2] =
                    interpolate_at_inf_from_0_1_basis(dst[dst_offset], dst[dst_offset + 1]);
            }
            // here we filled all options of (x0, x1, 0/1/inf)
        }

        // now get inf over x1
        for x2 in 0..3 {
            let src_0_idx = dst_offset + x2;
            let src_1_idx = dst_offset + 3 + x2;
            dst[dst_offset + 3 * 2 + x2] =
                interpolate_at_inf_from_0_1_basis(dst[src_0_idx], dst[src_1_idx]);
        }
    }

    // and get inf over x0
    for x1 in 0..3 {
        let dst_offset = 3 * x1;
        for x2 in 0..3 {
            let src_0_idx = 0 + dst_offset + x2;
            let src_1_idx = 9 + dst_offset + x2;
            dst[18 + dst_offset + x2] =
                interpolate_at_inf_from_0_1_basis(dst[src_0_idx], dst[src_1_idx]);
        }
    }
}

#[inline(always)]
fn read_ext_then_fold_without_interpolation_inplace<F: PrimeField, E: FieldExtension<F> + Field>(
    dst: &mut [E; 27],
    buffer: &mut DisjointAccessQuasiSlice<E, false>,
    unfolded_input_stride: usize,
    precomputed_eq_prefix: &[E; 8],
    row: usize,
) {
    let unfolded_input_stride = unfolded_input_stride / 8;
    let input_size = unfolded_input_stride;
    let stride_step = input_size / 2;
    for x0 in 0..2 {
        let stride = stride_step * x0;
        let dst_offset = 9 * x0;
        for x1 in 0..2 {
            let stride_step = stride_step / 2;
            let stride = stride + x1 * stride_step;
            let dst_offset = dst_offset + 3 * x1;
            {
                let stride_step = stride_step / 2;
                let src_0_idx = stride + row;
                let src_1_idx = src_0_idx + stride_step;

                let folded_0 = read_ext_and_fold(
                    buffer,
                    precomputed_eq_prefix,
                    unfolded_input_stride,
                    src_0_idx,
                );
                buffer.write(src_0_idx, folded_0);
                dst[dst_offset] = folded_0;

                let folded_1 = read_ext_and_fold(
                    buffer,
                    precomputed_eq_prefix,
                    unfolded_input_stride,
                    src_0_idx,
                );
                buffer.write(src_1_idx, folded_1);
                dst[dst_offset + 1] = folded_1;
            }
            // here we filled all options of (x0, x1, 0/1/inf)
        }
    }
}

pub fn evaluate_claim_from_intermediate_matrix_27<E: Field>(
    eq_prefix: &[E; 4],
    accumulator: &[E; 27],
) -> [E; 3] {
    let mut evals = [E::ZERO; 3];
    for x0 in 0..3 {
        let dst_offset = 9 * x0;
        for x1 in 0..2 {
            let eq_offset = x1 * 2;
            let dst_offset = dst_offset + 3 * x1;
            for x2 in 0..2 {
                let dst_offset = dst_offset + x2;
                let eq_offset = eq_offset + x2;
                let mut value = accumulator[dst_offset];
                value.mul_assign(&eq_prefix[eq_offset]);
                evals[x0].add_assign(&value);
            }
        }
    }

    evals
}

pub fn evaluate_claim_from_intermediate_matrix_9<E: Field>(
    eq_prefix: &[E; 2],
    accumulator: &[E; 9],
) -> [E; 3] {
    let mut evals = [E::ZERO; 3];
    for x1 in 0..3 {
        let dst_offset = 3 * x1;
        for x2 in 0..2 {
            let dst_offset = dst_offset + x2;
            let eq_offset = x2;
            let mut value = accumulator[dst_offset];
            value.mul_assign(&eq_prefix[eq_offset]);
            evals[x1].add_assign(&value);
        }
    }

    evals
}

#[inline(always)]
pub fn bind_univariate<F: Field>(c0: F, c1: F, c2: F, challenge: F) -> F {
    // The univariate is given by its values at {0, 1, inf}: c0 = P(0), c1 = P(1),
    // c2 = leading coefficient. So P(X) = c0 + (c1 - c2 - c0) * X + c2 * X^2.
    let mut c1 = c1;
    c1.sub_assign(&c2);
    c1.sub_assign(&c0);
    c1.mul_assign(&challenge);

    let mut c2 = c2;
    c2.mul_assign(&challenge);
    c2.mul_assign(&challenge);

    let mut binded = c0;
    binded.add_assign(&c1);
    binded.add_assign(&c2);

    binded
}

pub fn bind_accumulator_27<E: Field>(accumulator: &[E; 27], challenge: &E) -> [E; 9] {
    let mut next_accumulator = [E::ZERO; 9];
    for x1 in 0..3 {
        let src_offset = 3 * x1;
        let dst_offset = 3 * x1;
        for x2 in 0..3 {
            let src_offset = src_offset + x2;
            let dst_offset = dst_offset + x2;
            {
                let binded = bind_univariate(
                    accumulator[0 + src_offset],
                    accumulator[9 + src_offset],
                    accumulator[18 + src_offset],
                    *challenge,
                );
                next_accumulator[dst_offset] = binded;
            }
        }
    }

    next_accumulator
}

pub fn bind_accumulator_9<E: Field>(accumulator: &[E; 9], challenge: &E) -> [E; 3] {
    let mut next_accumulator = [E::ZERO; 3];
    for x2 in 0..3 {
        let src_offset = x2;
        let dst_offset = x2;
        {
            let binded = bind_univariate(
                accumulator[0 + src_offset],
                accumulator[3 + src_offset],
                accumulator[6 + src_offset],
                *challenge,
            );
            next_accumulator[dst_offset] = binded;
        }
    }

    next_accumulator
}
