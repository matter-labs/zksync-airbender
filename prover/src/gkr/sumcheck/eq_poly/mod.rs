use std::mem::MaybeUninit;

use field::{Field, FieldExtension, TwoAdicField};
use worker::{IterableWithGeometry, Worker};

use crate::gkr::PAR_THRESHOLD;

use super::*;





/// Interleaved-doubling layer step for the LSB nested tables: the newly
/// consumed (lowest-variable) coordinate's two factors land ADJACENT in
/// memory: out[2j] = (1 - c) * prev[j], out[2j + 1] = c * prev[j].
fn compute_next_layer_interleaved<E: Field>(prev: &[E], out: &mut [MaybeUninit<E>], c: &E) {
    debug_assert_eq!(out.len(), prev.len() * 2);
    for (p, dst) in prev.iter().zip(out.chunks_exact_mut(2)) {
        let mut one = *p;
        one.mul_assign(c);
        let mut zero = *p;
        zero.sub_assign(&one);
        dst[0].write(zero);
        dst[1].write(one);
    }
}

/// Nested eq tables for an LSB-binding round loop. `result[k]` has size
/// 2^k and covers the LAST k coordinates of `challenges` in VARIABLE
/// order: table index bit b <-> challenges[len - k + b]. The round loop at
/// step t (binding variable t of n) uses `result[n - 1 - t]`, the suffix
/// table over variables t+1..n.
pub fn make_eq_poly_in_full_lsb<E: Field>(challenges: &[E], worker: &Worker) -> Vec<Box<[E]>> {
    make_eq_poly_impl_lsb::<E, true>(challenges, worker)
}

/// Reduced variant of [`make_eq_poly_in_full_lsb`]: stops one table short
/// (the largest table covers the last `len - 1` coordinates).
pub fn make_eq_poly_reduced_lsb<E: Field>(challenges: &[E], worker: &Worker) -> Vec<Box<[E]>> {
    make_eq_poly_impl_lsb::<E, false>(challenges, worker)
}

pub fn make_eq_poly_impl_lsb<E: Field, const FULL: bool>(
    challenges: &[E],
    worker: &Worker,
) -> Vec<Box<[E]>> {
    assert!(!challenges.is_empty());

    let mut result: Vec<Box<[E]>> = Vec::with_capacity(challenges.len() + 1);
    result.push(vec![E::ONE].into_boxed_slice());

    let bound = if FULL {
        challenges.len() + 1
    } else {
        challenges.len()
    };
    let mut size = 1usize;
    let mut idx = challenges.len();
    for _ in 1..bound {
        let half_size = size;
        size *= 2;
        idx -= 1;
        let challenge = challenges[idx];

        let mut layer = Box::new_uninit_slice(size);
        let previous_layer = result.last().expect("is present");
        assert_eq!(previous_layer.len(), half_size);

        worker.scope_with_threshold(half_size, PAR_THRESHOLD, |scope, geometry| {
            let mut prev_rest: &[E] = previous_layer;
            let mut out_rest: &mut [MaybeUninit<E>] = &mut layer;
            for thread_idx in 0..geometry.num_chunks {
                let chunk = geometry.get_chunk_size(thread_idx);
                let (prev, prev_tail) = prev_rest.split_at(chunk);
                let (out, out_tail) = core::mem::take(&mut out_rest).split_at_mut(chunk * 2);
                prev_rest = prev_tail;
                out_rest = out_tail;
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    compute_next_layer_interleaved(prev, out, &challenge)
                });
            }
        });

        result.push(unsafe { layer.assume_init() });
    }

    result
}


/// Tensor eq table from per-entry WEIGHT BLOCKS: block `b` has length
/// `2^{w_b}` and covers the next `w_b` variables (LSB-first in entry
/// order), so `table[i0 + |B0|*(i1 + |B1|*(..))] = B0[i0]*B1[i1]*..`.
/// A plain coordinate `p` contributes the 2-block `[1-p, p]`; a uniskip
/// entry contributes its `2^w` fold weights. This is the flatten step of
/// the mixed evaluation-point representation: downstream sumchecks consume
/// the table exactly like a standard eq table.
pub fn make_eq_table_from_weight_blocks<E: Field>(blocks: &[&[E]], worker: &Worker) -> Vec<E> {
    use crate::gkr::PAR_THRESHOLD;
    let total: usize = blocks.iter().map(|b| b.len()).product();
    let mut table = vec![E::ONE; total.max(1)];
    let mut live = 1usize;
    for block in blocks.iter() {
        assert!(block.len().is_power_of_two() && block.len() >= 2);
        // scale copies of the live prefix by each block weight: the j-th
        // copy lands at [j*live .. (j+1)*live)
        let (lo_all, hi_all) = table.split_at_mut(live);
        for (j, w) in block.iter().enumerate().skip(1) {
            let dst = &mut hi_all[(j - 1) * live..j * live];
            worker.scope_with_threshold(live, PAR_THRESHOLD, |scope, geometry| {
                let mut lo_rest: &[E] = lo_all;
                let mut dst_rest: &mut [E] = dst;
                for thread_idx in 0..geometry.num_chunks {
                    let chunk = geometry.get_chunk_size(thread_idx);
                    let (lo, lo_tail) = lo_rest.split_at(chunk);
                    let (d, d_tail) = core::mem::take(&mut dst_rest).split_at_mut(chunk);
                    lo_rest = lo_tail;
                    dst_rest = d_tail;
                    let w = *w;
                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        for (dv, lv) in d.iter_mut().zip(lo.iter()) {
                            let mut v = *lv;
                            v.mul_assign(&w);
                            *dv = v;
                        }
                    });
                }
            });
        }
        // scale the base copy (j = 0) in place LAST (it is the source above)
        let w0 = block[0];
        worker.scope_with_threshold(live, PAR_THRESHOLD, |scope, geometry| {
            let mut lo_rest: &mut [E] = lo_all;
            for thread_idx in 0..geometry.num_chunks {
                let chunk = geometry.get_chunk_size(thread_idx);
                let (lo, lo_tail) = core::mem::take(&mut lo_rest).split_at_mut(chunk);
                lo_rest = lo_tail;
                let w0 = w0;
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    for lv in lo.iter_mut() {
                        lv.mul_assign(&w0);
                    }
                });
            }
        });
        live *= block.len();
    }
    assert_eq!(live, total.max(1));
    table
}

/// Eq table for a point in the DIMENSION-REDUCING emission layout
/// `[bits 1.., bit 0]` (the gate coordinate is bound last and stored last):
/// index bit 0 pairs with the LAST entry, index bit `b >= 1` with entry
/// `b - 1`. The layout mapping is internal -- callers pass the stored point.
pub fn make_eq_table_dim_reducing_point<E: Field>(point: &[E], worker: &Worker) -> Vec<E> {
    use crate::gkr::PAR_THRESHOLD;
    let n = point.len();
    let mut table = vec![E::ONE; 1usize << n];
    for b in 0..n {
        let c = if b == 0 { point[n - 1] } else { point[b - 1] };
        let mut om = E::ONE;
        om.sub_assign(&c);
        let half = 1usize << b;
        let (lo_all, hi_all) = table.split_at_mut(half);
        let hi_all = &mut hi_all[..half];
        worker.scope_with_threshold(half, PAR_THRESHOLD, |scope, geometry| {
            let mut lo_rest: &mut [E] = lo_all;
            let mut hi_rest: &mut [E] = hi_all;
            for thread_idx in 0..geometry.num_chunks {
                let chunk = geometry.get_chunk_size(thread_idx);
                let (lo, lo_tail) = core::mem::take(&mut lo_rest).split_at_mut(chunk);
                let (hi, hi_tail) = core::mem::take(&mut hi_rest).split_at_mut(chunk);
                lo_rest = lo_tail;
                hi_rest = hi_tail;
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    for (l, h) in lo.iter_mut().zip(hi.iter_mut()) {
                        let mut v = *l;
                        v.mul_assign(&c);
                        *h = v;
                        l.mul_assign(&om);
                    }
                });
            }
        });
    }
    table
}

/// Single eq table with the LSB-first index orientation used by the
/// LSB-binding engines: index bit `b` pairs with `challenges[b]`, so
/// `table[i] = prod_b (i_b ? challenges[b] : 1 - challenges[b])`. Built
/// level by level in ONE allocation (no intermediate tables); each doubling
/// is data-parallel over the existing half, so large levels fan out across
/// the worker pool and levels below the threshold run inline.
pub fn make_eq_table_lsb_first<E: Field>(challenges: &[E], worker: &Worker) -> Vec<E> {
    use crate::gkr::PAR_THRESHOLD;
    let mut table = vec![E::ONE; 1usize << challenges.len()];
    for (b, c) in challenges.iter().enumerate() {
        let half = 1usize << b;
        let mut om = E::ONE;
        om.sub_assign(c);
        let c = *c;
        let (lo_all, hi_all) = table.split_at_mut(half);
        let hi_all = &mut hi_all[..half];
        worker.scope_with_threshold(half, PAR_THRESHOLD, |scope, geometry| {
            let mut lo_rest: &mut [E] = lo_all;
            let mut hi_rest: &mut [E] = hi_all;
            for thread_idx in 0..geometry.num_chunks {
                let chunk = geometry.get_chunk_size(thread_idx);
                let (lo, lo_tail) = core::mem::take(&mut lo_rest).split_at_mut(chunk);
                let (hi, hi_tail) = core::mem::take(&mut hi_rest).split_at_mut(chunk);
                lo_rest = lo_tail;
                hi_rest = hi_tail;
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    for (l, h) in lo.iter_mut().zip(hi.iter_mut()) {
                        let mut v = *l;
                        v.mul_assign(&c);
                        *h = v;
                        l.mul_assign(&om);
                    }
                });
            }
        });
    }
    table
}

// Domain equality polys
fn make_domain_eq_poly_impl<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    const FULL: bool,
>(
    challenges: &[E],
) -> Vec<Box<[E]>> {
    // See WHIR comments: our equality poly is special here as we choose not the 0/1 hypercube, but 1/omega one.
    // So our equality is eq(X, Y) = 1 / (omega - 1) ^ 2 * (X - 1)(Y - 1) + (1 - (X - 1)/(omega - 1))(1 - (Y - 1)/(omega - 1))

    assert!(challenges.len() > 0);
    // challenges[0] is the challenge used to fold a variable, that is encoded as MSB in the values enumeration,
    // and we will produce the outputs in a same form. We also keep all intermediate forms for simplicity
    let mut result = Vec::with_capacity(challenges.len() + 1);
    result.push(vec![E::ONE].into_boxed_slice());

    let mut size = 1;
    let mut idx = challenges.len();

    let bound = if FULL {
        challenges.len() + 1
    } else {
        challenges.len()
    };

    for _ in 1..bound {
        size *= 2;
        idx -= 1;

        let omega = F::TWO_ADICITY_GENERATORS[idx + 1];
        let mut omega_minus_one = omega;
        omega_minus_one.sub_assign(&F::ONE);
        let omega_minus_one_inverse = omega_minus_one.inverse().expect("not 1-sized domain");

        let mut layer = Box::new_uninit_slice(size);
        let previous_layer = result.last().expect("is present");

        // eq(X, challenge)
        let challenge = challenges[idx];

        let mut eq_at_1 = E::ONE;
        eq_at_1.sub_assign(&challenge);
        eq_at_1.mul_assign_by_base(&omega_minus_one_inverse);
        eq_at_1.add_assign(&E::ONE);

        let mut eq_at_omega = challenge;
        eq_at_omega.sub_assign(&E::ONE);
        eq_at_omega.mul_assign_by_base(&omega_minus_one_inverse);

        dbg!(eq_at_1);
        dbg!(eq_at_omega);

        let half_size = size / 2;

        assert_eq!(previous_layer.len(), half_size);

        for index in 0..half_size {
            let mut left = previous_layer[index];
            let mut right = left;
            left.mul_assign(&eq_at_1);
            right.mul_assign(&eq_at_omega);
            layer[index].write(left);
            layer[index + half_size].write(right);
        }

        let layer = unsafe { layer.assume_init() };
        dbg!(&layer);
        result.push(layer);
    }

    result
}

pub fn make_domain_eq_poly_reduced<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field>(
    challenges: &[E],
) -> Vec<Box<[E]>> {
    make_domain_eq_poly_impl::<F, E, false>(challenges)
}

pub fn make_domain_eq_poly_in_full<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field>(
    challenges: &[E],
) -> Vec<Box<[E]>> {
    make_domain_eq_poly_impl::<F, E, true>(challenges)
}

/// LSB-first single-table variant of the domain (1/omega hypercube) eq poly:
/// index bit `b` pairs with `challenges[b]` and the per-variable generator
/// `F::TWO_ADICITY_GENERATORS[b + 1]` (same weight pair as
/// [`make_domain_eq_poly_impl`], different index orientation). Serial: the
/// consumers are the per-round in-domain claim evaluations.
pub fn make_domain_eq_table_lsb_first<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field>(
    challenges: &[E],
) -> Vec<E> {
    let mut table = vec![E::ONE; 1usize << challenges.len()];
    for (b, challenge) in challenges.iter().enumerate() {
        let omega = F::TWO_ADICITY_GENERATORS[b + 1];
        let mut omega_minus_one = omega;
        omega_minus_one.sub_assign(&F::ONE);
        let omega_minus_one_inverse = omega_minus_one.inverse().expect("not 1-sized domain");

        let mut eq_at_1 = E::ONE;
        eq_at_1.sub_assign(challenge);
        eq_at_1.mul_assign_by_base(&omega_minus_one_inverse);
        eq_at_1.add_assign(&E::ONE);

        let mut eq_at_omega = *challenge;
        eq_at_omega.sub_assign(&E::ONE);
        eq_at_omega.mul_assign_by_base(&omega_minus_one_inverse);

        let half = 1usize << b;
        for i in 0..half {
            let prev = table[i];
            let mut left = prev;
            left.mul_assign(&eq_at_1);
            let mut right = prev;
            right.mul_assign(&eq_at_omega);
            table[i] = left;
            table[i + half] = right;
        }
    }
    table
}

pub(crate) fn evaluate_with_precomputed_eq<F: PrimeField, E: FieldExtension<F> + Field>(
    base_field_values: &[F],
    eq: &[E],
) -> E {
    assert_eq!(base_field_values.len(), eq.len());
    let mut result = E::ZERO;
    for (a, b) in base_field_values.iter().zip(eq.iter()) {
        let mut t = *b;
        t.mul_assign_by_base(a);
        result.add_assign(&t);
    }

    result
}

#[track_caller]
pub(crate) fn evaluate_with_precomputed_eq_ext<E: Field>(ext_field_values: &[E], eq: &[E]) -> E {
    assert_eq!(ext_field_values.len(), eq.len());
    let mut result = E::ZERO;
    for (a, b) in ext_field_values.iter().zip(eq.iter()) {
        let mut t = *b;
        t.mul_assign(a);
        result.add_assign(&t);
    }

    result
}

pub(crate) fn evaluate_constant_and_quadratic_coeffs_with_precomputed_eq<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    values: &[[E; 2]],
    eq: &[E],
    worker: &Worker,
) -> [E; 2] {
    let work_size = values.len();

    assert_eq!(work_size, eq.len());

    if work_size == 0 {
        return [E::ZERO; 2];
    }

    let mut partial_results = vec![
        [E::ZERO; 2];
        worker
            .get_geometry_with_threshold(work_size, PAR_THRESHOLD)
            .len()
    ];

    worker.scope_with_threshold(work_size, PAR_THRESHOLD, |scope, geometry| {
        let values_chunks = values.chunks_for_geometry(geometry);
        let eq_chunks = eq.chunks_for_geometry(geometry);

        partial_results
            .iter_mut()
            .enumerate()
            .zip(values_chunks.zip(eq_chunks))
            .for_each(|((idx, partial), (v_chunk, e_chunk))| {
                Worker::smart_spawn(scope, idx == geometry.len() - 1, |_| {
                    let mut res0 = E::ZERO;
                    let mut res1 = E::ZERO;

                    for (a, b) in v_chunk.iter().zip(e_chunk.iter()) {
                        let mut t0 = *b;
                        t0.mul_assign(&a[0]);
                        res0.add_assign(&t0);

                        let mut t1 = *b;
                        t1.mul_assign(&a[1]);
                        res1.add_assign(&t1);
                    }

                    *partial = [res0, res1];
                })
            });
    });

    partial_results
        .iter()
        .fold([E::ZERO; 2], |mut acc, [a, b]| {
            acc[0].add_assign(a);
            acc[1].add_assign(b);
            acc
        })
}

#[cfg(test)]
pub(crate) fn evaluate_constant_and_quadratic_coeffs_with_precomputed_eq_serial<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    values: &[[E; 2]],
    eq: &[E],
) -> [E; 2] {
    assert_eq!(values.len(), eq.len());
    let mut result_0 = E::ZERO;
    let mut result_1 = E::ZERO;
    for (a, b) in values.iter().zip(eq.iter()) {
        let [a0, a1] = a;

        let mut t0 = *b;
        t0.mul_assign(a0);
        result_0.add_assign(&t0);

        let mut t1 = *b;
        t1.mul_assign(a1);
        result_1.add_assign(&t1);
    }

    [result_0, result_1]
}




/// Serial variant of [`make_eq_poly_in_full_lsb`] (same table semantics:
/// `result[k]` covers the LAST k coordinates in variable order).
pub fn make_eq_poly_in_full_lsb_serial<E: Field>(challenges: &[E]) -> Vec<Box<[E]>> {
    assert!(!challenges.is_empty());
    let mut result: Vec<Box<[E]>> = Vec::with_capacity(challenges.len() + 1);
    result.push(vec![E::ONE].into_boxed_slice());
    let mut idx = challenges.len();
    for _ in 1..challenges.len() + 1 {
        idx -= 1;
        let c = challenges[idx];
        let prev = result.last().expect("is present");
        let mut layer = Box::new_uninit_slice(prev.len() * 2);
        for (p, dst) in prev.iter().zip(layer.chunks_exact_mut(2)) {
            let mut one = *p;
            one.mul_assign(&c);
            let mut zero = *p;
            zero.sub_assign(&one);
            dst[0].write(zero);
            dst[1].write(one);
        }
        result.push(unsafe { layer.assume_init() });
    }
    result
}

#[cfg(test)]
mod eq_nested_lsb_tests {
    use super::*;
    use field::baby_bear::ext4::BabyBearExt4 as E;
    use field::Field;

    #[test]
    fn nested_lsb_tables_match_single_builder() {
        let worker = crate::worker::Worker::new_with_num_threads(2);
        let n = 5usize;
        let challenges: Vec<E> = (0..n)
            .map(|i| {
                let base = field::baby_bear::base::BabyBearField::from_u32_with_reduction(
                    77 + 31 * i as u32,
                );
                let mut v = E::from_base(base);
                v.mul_assign(&E::from_base(
                    field::baby_bear::base::BabyBearField::from_u32_with_reduction(1013),
                ));
                v
            })
            .collect();
        let tables = make_eq_poly_in_full_lsb::<E>(&challenges, &worker);
        assert_eq!(tables.len(), n + 1);
        for k in 0..=n {
            assert_eq!(tables[k].len(), 1 << k);
            if k == 0 {
                assert_eq!(tables[0][0], E::ONE);
                continue;
            }
            // tables[k] covers the LAST k coordinates, bit b <-> challenges[n - k + b]
            let expected = make_eq_table_lsb_first::<E>(&challenges[n - k..], &worker);
            assert_eq!(&tables[k][..], &expected[..], "table {k}");
        }
    }
}

#[cfg(test)]
mod eq_lsb_orientation_tests {
    use super::*;
    use field::baby_bear::ext4::BabyBearExt4 as E;
    use field::baby_bear::base::BabyBearField as F;
    use field::{Field, PrimeField, FieldExtension};

    /// `make_eq_table_lsb_first` (index bit b <-> challenges[b]) must match
    /// the explicit product formula for every size.
    #[test]
    fn lsb_first_matches_reference() {
        let worker = crate::worker::Worker::new_with_num_threads(3);
        for n in 1..=6usize {
            let challenges: Vec<E> = (0..n)
                .map(|i| E::from_base(F::from_nonreduced_u32((i * i * 31 + i * 7 + 3) as u32)))
                .collect();
            let lsb = make_eq_table_lsb_first::<E>(&challenges, &worker);
            for j in 0..(1usize << n) {
                let mut expect = E::ONE;
                for (b, c) in challenges.iter().enumerate() {
                    let mut f = *c;
                    if (j >> b) & 1 == 0 {
                        let mut om = E::ONE;
                        om.sub_assign(c);
                        f = om;
                    }
                    expect.mul_assign(&f);
                }
                assert_eq!(lsb[j], expect, "n = {n}, j = {j}");
            }
            // DR layout: bit 0 <-> last entry, bit b >= 1 <-> entry b-1
            let dr = make_eq_table_dim_reducing_point::<E>(&challenges, &worker);
            let var_order: Vec<E> = core::iter::once(challenges[n - 1])
                .chain(challenges[..n - 1].iter().copied())
                .collect();
            let reference3 = make_eq_table_lsb_first::<E>(&var_order, &worker);
            assert_eq!(&dr[..], &reference3[..], "dr n = {n}");
        }
    }

    /// Block-tensor builder with 2-blocks must equal the LSB-first table;
    /// with a mixed 8-block it must equal the manual tensor.
    #[test]
    fn weight_block_tensor_matches() {
        let worker = crate::worker::Worker::new_with_num_threads(2);
        let ch: Vec<E> = (0..4usize)
            .map(|i| E::from_base(F::from_nonreduced_u32((i * 5 + 2) as u32)))
            .collect();
        let two_blocks: Vec<Vec<E>> = ch
            .iter()
            .map(|c| {
                let mut om = E::ONE;
                om.sub_assign(c);
                vec![om, *c]
            })
            .collect();
        let refs: Vec<&[E]> = two_blocks.iter().map(|b| &b[..]).collect();
        let via_blocks = make_eq_table_from_weight_blocks::<E>(&refs, &worker);
        let direct = make_eq_table_lsb_first::<E>(&ch, &worker);
        assert_eq!(via_blocks, direct);

        // mixed: an 8-weight block over vars 0..3, one coordinate at var 3
        let block8: Vec<E> = (0..8u32)
            .map(|j| E::from_base(F::from_nonreduced_u32(j * j + 1)))
            .collect();
        let coord = ch[0];
        let mut om = E::ONE;
        om.sub_assign(&coord);
        let c2 = vec![om, coord];
        let mixed = make_eq_table_from_weight_blocks::<E>(&[&block8[..], &c2[..]], &worker);
        assert_eq!(mixed.len(), 16);
        for j in 0..8usize {
            for k in 0..2usize {
                let mut expect = block8[j];
                expect.mul_assign(&c2[k]);
                assert_eq!(mixed[j + 8 * k], expect, "cell ({j},{k})");
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
    use rand::{rngs::ThreadRng, RngCore};

    type F = BabyBearField;
    type E = BabyBearExt4;

    fn random_in_ext(rng: &mut ThreadRng) -> E
    where
        [(); <E as FieldExtension<F>>::DEGREE]: Sized,
    {
        let coefs = [(); <E as FieldExtension<F>>::DEGREE]
            .map(|_| F::from_u32_with_reduction(rng.next_u32()));
        <E as FieldExtension<F>>::from_coeffs(coefs)
    }

    #[test]
    fn test_evaluate_constant_and_quadratic_coeffs_with_precomputed_eq() {
        let mut rng = rand::rng();

        let size = 1 << 10;
        let eq: Vec<E> = (0..size).map(|_| random_in_ext(&mut rng)).collect();
        let values: Vec<[E; 2]> = (0..size)
            .map(|_| [random_in_ext(&mut rng), random_in_ext(&mut rng)])
            .collect();

        let expected =
            evaluate_constant_and_quadratic_coeffs_with_precomputed_eq_serial::<F, E>(&values, &eq);

        for i in 1..=10 {
            let worker = Worker::new_with_num_threads(i);
            assert_eq!(
                evaluate_constant_and_quadratic_coeffs_with_precomputed_eq::<F, E>(
                    &values, &eq, &worker
                ),
                expected
            );
        }
    }

}
