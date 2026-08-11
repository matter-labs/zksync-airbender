//! Higher-radix (radix-4 / radix-8) variants of the GS DIT NTT
//! (bit-reversed input → natural output). Proth120 has no cheap `·i` rotation,
//! so — unlike small-prime radix-4 FFTs — the multiplication COUNT is unchanged;
//! the win is purely structural: 2 (radix-4) or 3 (radix-8) butterfly levels are
//! fused per pass, so every element is loaded/stored once per pass instead of
//! once per level (2–3× less load/store traffic) and the 4/8 working values live
//! in registers across the fused levels.
//!
//! Stage pairing: levels are fused from the SMALL-`ppg` end; when the level
//! count doesn't divide evenly the leftovers run at the LARGE-`ppg` end, where
//! the last multiplying level is fused with the final twiddle-free level.
//! Outputs are exactly equal to `serial_ct_ntt_bitreversed_to_natural` (same
//! twiddle table, same arithmetic, only the loop structure differs).

use ::field::*;

/// Fused tail: `num_groups == 2` → last multiplying level + final twiddle-free
/// level in one pass; `num_groups == 1` → final level only.
#[inline(always)]
fn radix2_tail<F: Field, E: Field + FieldExtension<F>>(
    a: &mut [E],
    num_groups: usize,
    twiddles_bit_reversed: &[F],
) {
    let n = a.len();
    match num_groups {
        2 => {
            // groups 0 (tw[0]) and 1 (tw[1]), then the final level fused.
            let q = n / 4;
            let s_a = twiddles_bit_reversed[0];
            let s_b = twiddles_bit_reversed[1];
            for j in 0..q {
                unsafe {
                    let x0 = *a.get_unchecked(j);
                    let x1 = *a.get_unchecked(j + q);
                    let x2 = *a.get_unchecked(j + 2 * q);
                    let x3 = *a.get_unchecked(j + 3 * q);
                    let mut y0 = x0;
                    y0.add_assign(&x1);
                    let mut y1 = x0;
                    y1.sub_assign(&x1);
                    y1.mul_assign_by_base(&s_a);
                    let mut y2 = x2;
                    y2.add_assign(&x3);
                    let mut y3 = x2;
                    y3.sub_assign(&x3);
                    y3.mul_assign_by_base(&s_b);
                    let mut z0 = y0;
                    z0.add_assign(&y2);
                    let mut z2 = y0;
                    z2.sub_assign(&y2);
                    let mut z1 = y1;
                    z1.add_assign(&y3);
                    let mut z3 = y1;
                    z3.sub_assign(&y3);
                    *a.get_unchecked_mut(j) = z0;
                    *a.get_unchecked_mut(j + q) = z1;
                    *a.get_unchecked_mut(j + 2 * q) = z2;
                    *a.get_unchecked_mut(j + 3 * q) = z3;
                }
            }
        }
        1 => {
            let half = n / 2;
            for j in 0..half {
                unsafe {
                    let u = *a.get_unchecked(j);
                    let v = *a.get_unchecked(j + half);
                    let mut s = u;
                    s.add_assign(&v);
                    let mut d = u;
                    d.sub_assign(&v);
                    *a.get_unchecked_mut(j) = s;
                    *a.get_unchecked_mut(j + half) = d;
                }
            }
        }
        _ => unreachable!("tail called with num_groups > 2"),
    }
}

/// One radix-4 sweep phase: fuse level pairs while `num_groups >= 4`; returns
/// the updated `(ppg, num_groups)`.
#[inline(always)]
fn radix4_levels<F: Field, E: Field + FieldExtension<F>>(
    a: &mut [E],
    mut ppg: usize,
    mut num_groups: usize,
    twiddles_bit_reversed: &[F],
) -> (usize, usize) {
    while num_groups >= 4 {
        let ng_outer = num_groups / 2;
        for k2 in 0..ng_outer {
            let s_a = twiddles_bit_reversed[2 * k2];
            let s_b = twiddles_bit_reversed[2 * k2 + 1];
            let s_o = twiddles_bit_reversed[k2];
            let base = k2 * ppg * 4;
            for j in base..base + ppg {
                unsafe {
                    let x0 = *a.get_unchecked(j);
                    let x1 = *a.get_unchecked(j + ppg);
                    let x2 = *a.get_unchecked(j + 2 * ppg);
                    let x3 = *a.get_unchecked(j + 3 * ppg);
                    // inner level: groups 2k2 (tw s_a) and 2k2+1 (tw s_b)
                    let mut y0 = x0;
                    y0.add_assign(&x1);
                    let mut y1 = x0;
                    y1.sub_assign(&x1);
                    y1.mul_assign_by_base(&s_a);
                    let mut y2 = x2;
                    y2.add_assign(&x3);
                    let mut y3 = x2;
                    y3.sub_assign(&x3);
                    y3.mul_assign_by_base(&s_b);
                    // outer level: group k2 (tw s_o), pairs (y0,y2) and (y1,y3)
                    let mut z0 = y0;
                    z0.add_assign(&y2);
                    let mut z2 = y0;
                    z2.sub_assign(&y2);
                    z2.mul_assign_by_base(&s_o);
                    let mut z1 = y1;
                    z1.add_assign(&y3);
                    let mut z3 = y1;
                    z3.sub_assign(&y3);
                    z3.mul_assign_by_base(&s_o);
                    *a.get_unchecked_mut(j) = z0;
                    *a.get_unchecked_mut(j + ppg) = z1;
                    *a.get_unchecked_mut(j + 2 * ppg) = z2;
                    *a.get_unchecked_mut(j + 3 * ppg) = z3;
                }
            }
        }
        ppg *= 4;
        num_groups /= 4;
    }
    (ppg, num_groups)
}

/// Radix-4 GS DIT NTT, bit-reversed input → natural output. Exact drop-in for
/// `serial_ct_ntt_bitreversed_to_natural`.
pub fn serial_ct_ntt_bitreversed_to_natural_radix4<F: Field, E: Field + FieldExtension<F>>(
    a: &mut [E],
    log_n: u32,
    twiddles_bit_reversed: &[F],
) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    debug_assert_eq!(n, 1usize << log_n);
    let (_, num_groups) = radix4_levels(a, 1, n / 2, twiddles_bit_reversed);
    radix2_tail(a, num_groups, twiddles_bit_reversed);
}

/// Radix-8 GS DIT NTT, bit-reversed input → natural output: three levels fused
/// per pass, remainder handled by one radix-4 pass and/or the fused tail.
pub fn serial_ct_ntt_bitreversed_to_natural_radix8<F: Field, E: Field + FieldExtension<F>>(
    a: &mut [E],
    log_n: u32,
    twiddles_bit_reversed: &[F],
) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    debug_assert_eq!(n, 1usize << log_n);
    let mut ppg = 1usize;
    let mut num_groups = n / 2;
    while num_groups >= 8 {
        let ng_outer = num_groups / 4;
        for k3 in 0..ng_outer {
            let t_a = twiddles_bit_reversed[4 * k3];
            let t_b = twiddles_bit_reversed[4 * k3 + 1];
            let t_c = twiddles_bit_reversed[4 * k3 + 2];
            let t_d = twiddles_bit_reversed[4 * k3 + 3];
            let t_e = twiddles_bit_reversed[2 * k3];
            let t_f = twiddles_bit_reversed[2 * k3 + 1];
            let t_o = twiddles_bit_reversed[k3];
            let base = k3 * ppg * 8;
            for j in base..base + ppg {
                unsafe {
                    let x0 = *a.get_unchecked(j);
                    let x1 = *a.get_unchecked(j + ppg);
                    let x2 = *a.get_unchecked(j + 2 * ppg);
                    let x3 = *a.get_unchecked(j + 3 * ppg);
                    let x4 = *a.get_unchecked(j + 4 * ppg);
                    let x5 = *a.get_unchecked(j + 5 * ppg);
                    let x6 = *a.get_unchecked(j + 6 * ppg);
                    let x7 = *a.get_unchecked(j + 7 * ppg);
                    // level 1: pairs at stride ppg, twiddles t_a..t_d
                    let mut y0 = x0;
                    y0.add_assign(&x1);
                    let mut y1 = x0;
                    y1.sub_assign(&x1);
                    y1.mul_assign_by_base(&t_a);
                    let mut y2 = x2;
                    y2.add_assign(&x3);
                    let mut y3 = x2;
                    y3.sub_assign(&x3);
                    y3.mul_assign_by_base(&t_b);
                    let mut y4 = x4;
                    y4.add_assign(&x5);
                    let mut y5 = x4;
                    y5.sub_assign(&x5);
                    y5.mul_assign_by_base(&t_c);
                    let mut y6 = x6;
                    y6.add_assign(&x7);
                    let mut y7 = x6;
                    y7.sub_assign(&x7);
                    y7.mul_assign_by_base(&t_d);
                    // level 2: pairs at stride 2ppg, groups 2k3 (t_e) / 2k3+1 (t_f)
                    let mut z0 = y0;
                    z0.add_assign(&y2);
                    let mut z2 = y0;
                    z2.sub_assign(&y2);
                    z2.mul_assign_by_base(&t_e);
                    let mut z1 = y1;
                    z1.add_assign(&y3);
                    let mut z3 = y1;
                    z3.sub_assign(&y3);
                    z3.mul_assign_by_base(&t_e);
                    let mut z4 = y4;
                    z4.add_assign(&y6);
                    let mut z6 = y4;
                    z6.sub_assign(&y6);
                    z6.mul_assign_by_base(&t_f);
                    let mut z5 = y5;
                    z5.add_assign(&y7);
                    let mut z7 = y5;
                    z7.sub_assign(&y7);
                    z7.mul_assign_by_base(&t_f);
                    // level 3: pairs at stride 4ppg, group k3 (t_o)
                    let mut w0 = z0;
                    w0.add_assign(&z4);
                    let mut w4 = z0;
                    w4.sub_assign(&z4);
                    w4.mul_assign_by_base(&t_o);
                    let mut w1 = z1;
                    w1.add_assign(&z5);
                    let mut w5 = z1;
                    w5.sub_assign(&z5);
                    w5.mul_assign_by_base(&t_o);
                    let mut w2 = z2;
                    w2.add_assign(&z6);
                    let mut w6 = z2;
                    w6.sub_assign(&z6);
                    w6.mul_assign_by_base(&t_o);
                    let mut w3 = z3;
                    w3.add_assign(&z7);
                    let mut w7 = z3;
                    w7.sub_assign(&z7);
                    w7.mul_assign_by_base(&t_o);
                    *a.get_unchecked_mut(j) = w0;
                    *a.get_unchecked_mut(j + ppg) = w1;
                    *a.get_unchecked_mut(j + 2 * ppg) = w2;
                    *a.get_unchecked_mut(j + 3 * ppg) = w3;
                    *a.get_unchecked_mut(j + 4 * ppg) = w4;
                    *a.get_unchecked_mut(j + 5 * ppg) = w5;
                    *a.get_unchecked_mut(j + 6 * ppg) = w6;
                    *a.get_unchecked_mut(j + 7 * ppg) = w7;
                }
            }
        }
        ppg *= 8;
        num_groups /= 8;
    }
    let (_, num_groups) = radix4_levels(a, ppg, num_groups, twiddles_bit_reversed);
    radix2_tail(a, num_groups, twiddles_bit_reversed);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::column_major::naive::serial_ct_ntt_bitreversed_to_natural;
    use crate::twiddles::precompute_all_twiddles_for_fft_serial;
    use ::field::baby_bear::base::BabyBearField;
    use ::field::Proth120;
    use std::alloc::Global;

    fn check<F: PrimeField + TwoAdicField + Rand>(log_n: u32) {
        let n = 1usize << log_n;
        let mut rng = rand::rng();
        let x: Vec<F> = (0..n).map(|_| F::random_element(&mut rng)).collect();
        let tw: Vec<F, Global> = precompute_all_twiddles_for_fft_serial::<F, Global, false>(n);

        let mut expected = x.clone();
        serial_ct_ntt_bitreversed_to_natural(&mut expected, log_n, &tw[..(n / 2).max(1)]);

        let mut got = x.clone();
        serial_ct_ntt_bitreversed_to_natural_radix4(&mut got, log_n, &tw[..(n / 2).max(1)]);
        assert_eq!(got, expected, "radix-4 diverged at log_n={log_n}");

        let mut got = x.clone();
        serial_ct_ntt_bitreversed_to_natural_radix8(&mut got, log_n, &tw[..(n / 2).max(1)]);
        assert_eq!(got, expected, "radix-8 diverged at log_n={log_n}");
    }

    #[test]
    fn higher_radix_matches_reference() {
        // cover every (levels mod 2, levels mod 3) residue class
        for log_n in [1u32, 2, 3, 4, 5, 6, 7, 8, 11, 12, 13] {
            check::<BabyBearField>(log_n);
            check::<Proth120>(log_n);
        }
    }
}
