//! Host-side domain math for the uniskip pass: the size-16 subgroup `H`, its odd
//! coset `gamma * H`, the coset LDE matrix and the Lagrange fold weights.

use crate::abi::{UNISKIP_LOG_TAPS, UNISKIP_NTT_TABLES, UNISKIP_TAPS};
use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use field::{Field, FieldExtension};

pub type F = BabyBearField;
pub type E4 = BabyBearExt4;

/// Generator of `H`, the multiplicative subgroup of order 16.
pub fn omega16() -> F {
    F::TWO_ADICITY_GENERATORS[4]
}

/// Coset shift: a generator of the order-32 subgroup, so `gamma^16 = -1` and
/// `gamma * H` is the odd coset disjoint from `H`.
pub fn gamma() -> F {
    F::TWO_ADICITY_GENERATORS[5]
}

fn lift(x: F) -> E4 {
    <E4 as FieldExtension<F>>::from_base(x)
}

fn mul(a: F, b: F) -> F {
    let mut r = a;
    r.mul_assign(&b);
    r
}

fn e4_mul(a: E4, b: E4) -> E4 {
    let mut r = a;
    r.mul_assign(&b);
    r
}

fn e4_sub(a: E4, b: E4) -> E4 {
    let mut r = a;
    r.sub_assign(&b);
    r
}

// L_t(X) on H: prod(X - omega^s) = X^16 - 1, derivative at omega^t = 16*omega^{-t}
//   => L_t(X) = (X^16 - 1) * omega^t * inv16 / (X - omega^t)
// On the odd coset X_c^16 = gamma^16 = -1, so (X_c^16 - 1) = -2 for every c.
/// `M[c][t] = L_t(gamma * omega^c)`: extends the taps on `H` to the coset cells.
/// Row `c` is device cell `abi::cell_for_coset_row(c)`.
pub fn lde_matrix() -> [[F; UNISKIP_TAPS]; UNISKIP_TAPS] {
    let omega = omega16();
    let gamma = gamma();
    let inv16 = F::new(16).inverse().unwrap();
    let mut scale = F::TWO;
    scale.negate();
    scale.mul_assign(&inv16);
    core::array::from_fn(|c| {
        let x = mul(gamma, omega.pow(c as u32));
        core::array::from_fn(|t| {
            let wt = omega.pow(t as u32);
            mul(mul(scale, wt), (x - wt).inverse().unwrap())
        })
    })
}

/// `bitrev` of a `UNISKIP_LOG_TAPS`-bit index.
pub const fn bitrev_tap(i: usize) -> usize {
    let mut out = 0;
    let mut b = 0;
    while b < UNISKIP_LOG_TAPS as usize {
        out |= ((i >> b) & 1) << (UNISKIP_LOG_TAPS as usize - 1 - b);
        b += 1;
    }
    out
}

/// Lane-indexed twiddles of the FACTORIZED coset transform — the host mirror of the
/// device shuffle-NTT's `__constant__` tables, in stage order:
///
/// | table | stage | multiplier at lane `l` |
/// | --- | --- | --- |
/// | 0..2 | iDIF, butterfly distance 8 / 4 / 2 | `omega^-((l & (d-1)) * 16/(2d))` on the lower lanes, `1` on the upper |
/// | 3 | normalize + twist, folded | `inv16 * gamma^bitrev(l)` |
/// | 4..6 | DIT, butterfly distance 2 / 4 / 8 | `omega^((l & (d-1)) * 16/(2d))` on the lower lanes, `1` on the upper |
///
/// The two distance-1 stages carry only unity (their exponent is `0 * 8`) and are
/// elided on both sides, which is why there are 7 tables and not 9.
pub fn ntt_twiddles() -> [[F; UNISKIP_TAPS]; UNISKIP_NTT_TABLES] {
    let omega = omega16();
    let omega_inv = omega.inverse().unwrap();
    let inv16 = F::new(UNISKIP_TAPS as u32).inverse().unwrap();
    let mut tables = [[F::ONE; UNISKIP_TAPS]; UNISKIP_NTT_TABLES];
    let mut stage = |table: usize, d: usize, root: F| {
        for lane in 0..UNISKIP_TAPS {
            if lane & d != 0 {
                let exponent = (lane & (d - 1)) * (UNISKIP_TAPS / (2 * d));
                tables[table][lane] = root.pow(exponent as u32);
            }
        }
    };
    for (table, d) in [8usize, 4, 2].into_iter().enumerate() {
        stage(table, d, omega_inv);
    }
    for (table, d) in [2usize, 4, 8].into_iter().enumerate() {
        stage(UNISKIP_NTT_TABLES - 3 + table, d, omega);
    }
    let gamma = gamma();
    for lane in 0..UNISKIP_TAPS {
        tables[3][lane] = mul(inv16, gamma.pow(bitrev_tap(lane) as u32));
    }
    tables
}

/// One radix-2 butterfly layer at distance `d`: the upper lane of a pair keeps
/// `u + v`, the lower `u - v`. Identical for iDIF and DIT — only where the stage's
/// twiddle is applied differs (iDIF after, DIT before).
fn butterfly(x: &mut [F; UNISKIP_TAPS], d: usize) {
    for lane in 0..UNISKIP_TAPS {
        if lane & d == 0 {
            let u = x[lane];
            let v = x[lane | d];
            let mut sum = u;
            sum.add_assign(&v);
            let mut diff = u;
            diff.sub_assign(&v);
            x[lane] = sum;
            x[lane | d] = diff;
        }
    }
}

/// The FACTORIZED coset transform, exactly as the device shuffle-NTT sequences it:
/// natural-order taps on `H` -> iDIF with `omega^-1` (distances 8, 4, 2, 1) ->
/// folded normalize+twist -> DIT with `omega` (distances 1, 2, 4, 8) -> the 16 cells
/// of `gamma * H` in natural order, so entry `c` is `P(gamma * omega^c)` = row `c` of
/// [`lde_matrix`]. `cpu_factorized_coset_matches_matrix` pins the equality.
pub fn coset_from_taps(taps: &[F; UNISKIP_TAPS]) -> [F; UNISKIP_TAPS] {
    let tw = ntt_twiddles();
    let mut x = *taps;
    for (table, d) in [8usize, 4, 2].into_iter().enumerate() {
        butterfly(&mut x, d);
        for lane in 0..UNISKIP_TAPS {
            x[lane] = mul(x[lane], tw[table][lane]);
        }
    }
    butterfly(&mut x, 1);
    for lane in 0..UNISKIP_TAPS {
        x[lane] = mul(x[lane], tw[3][lane]);
    }
    butterfly(&mut x, 1);
    for (table, d) in [2usize, 4, 8].into_iter().enumerate() {
        for lane in 0..UNISKIP_TAPS {
            x[lane] = mul(x[lane], tw[UNISKIP_NTT_TABLES - 3 + table][lane]);
        }
        butterfly(&mut x, d);
    }
    x
}

/// `[L_t(r)]_t`: the weights that fold the taps on `H` into the evaluation at `r`.
pub fn fold_weights(r: E4) -> [E4; UNISKIP_TAPS] {
    let omega = omega16();
    // On H the barycentric form divides by zero; the weights are the Kronecker delta.
    if let Some(t) = (0..UNISKIP_TAPS).find(|&t| r == lift(omega.pow(t as u32))) {
        return core::array::from_fn(|s| if s == t { E4::ONE } else { E4::ZERO });
    }
    let inv16 = lift(F::new(16).inverse().unwrap());
    let lead = e4_mul(e4_sub(r.pow(16), E4::ONE), inv16);
    core::array::from_fn(|t| {
        let wt = lift(omega.pow(t as u32));
        e4_mul(e4_mul(lead, wt), e4_sub(r, wt).inverse().unwrap())
    })
}

#[cfg(test)]
mod cpu_tests {
    use super::*;

    fn seeded_coeffs() -> Vec<F> {
        (0..16u32)
            .map(|i| F::new(0x1234_5678u32.wrapping_mul(i + 1) % F::ORDER))
            .collect()
    }

    fn horner_bf(coeffs: &[F], x: F) -> F {
        coeffs.iter().rev().fold(F::ZERO, |acc, c| {
            let mut t = acc;
            t.mul_assign(&x);
            t.add_assign(c);
            t
        })
    }

    fn horner_e4(coeffs: &[F], x: E4) -> E4 {
        coeffs.iter().rev().fold(E4::ZERO, |acc, c| {
            let mut t = acc;
            t.mul_assign(&x);
            <E4 as FieldExtension<F>>::add_assign_base(&mut t, c);
            t
        })
    }

    fn taps(coeffs: &[F]) -> Vec<F> {
        let omega = omega16();
        (0..16)
            .map(|t| horner_bf(coeffs, omega.pow(t as u32)))
            .collect()
    }

    #[test]
    fn cpu_lde_matrix_extends_polynomials() {
        let coeffs = seeded_coeffs();
        let taps = taps(&coeffs);
        let omega = omega16();
        let m = lde_matrix();
        for c in 0..16 {
            let mut x = gamma();
            x.mul_assign(&omega.pow(c as u32));
            let mut got = F::ZERO;
            for t in 0..16 {
                got.add_assign_product(&m[c][t], &taps[t]);
            }
            assert_eq!(got, horner_bf(&coeffs, x), "coset cell {c}");
        }
    }

    /// Adversarial tap sets: the canonical extremes and near-`p` values, where a
    /// missing conditional subtract in the lazy chain would show up first.
    fn adversarial_taps() -> Vec<[F; UNISKIP_TAPS]> {
        let edge = [
            0u32,
            1,
            2,
            F::ORDER - 1,
            F::ORDER - 2,
            F::ORDER / 2,
            F::ORDER / 2 + 1,
            1 << 30,
        ];
        let mut sets = vec![
            [F::new(F::ORDER - 1); UNISKIP_TAPS],
            [F::ZERO; UNISKIP_TAPS],
            core::array::from_fn(|t| F::new(edge[t % edge.len()])),
            core::array::from_fn(|t| {
                if t % 2 == 0 {
                    F::new(F::ORDER - 1)
                } else {
                    F::ONE
                }
            }),
        ];
        // Every single-tap impulse: the chain's column `t` against the matrix's.
        for t in 0..UNISKIP_TAPS {
            let mut taps = [F::ZERO; UNISKIP_TAPS];
            taps[t] = F::new(F::ORDER - 1);
            sets.push(taps);
        }
        sets
    }

    /// Flat `bf` limb `i` of an `E4`, in the order `reference::e4_words` uploads.
    fn e4_limb(x: E4, i: usize) -> F {
        [x.c0.c0, x.c0.c1, x.c1.c0, x.c1.c1][i]
    }

    fn pseudorandom_taps(seed: u32) -> [F; UNISKIP_TAPS] {
        core::array::from_fn(|t| {
            let x = seed
                .wrapping_mul(0x9e37_79b9)
                .wrapping_add((t as u32).wrapping_mul(0x85eb_ca6b));
            F::new(x % F::ORDER)
        })
    }

    /// G0's arithmetic core: the factorized iDIF -> twist -> DIT chain the device
    /// shuffle-NTT runs must agree with the dense 16x16 apply for EVERY input, or the
    /// LSB producer is wrong in a way no timing can reveal.
    #[test]
    fn cpu_factorized_coset_matches_matrix() {
        let matrix = lde_matrix();
        let dense = |taps: &[F; UNISKIP_TAPS]| -> [F; UNISKIP_TAPS] {
            core::array::from_fn(|c| {
                let mut acc = F::ZERO;
                for t in 0..UNISKIP_TAPS {
                    acc.add_assign_product(&matrix[c][t], &taps[t]);
                }
                acc
            })
        };
        let mut cases = adversarial_taps();
        cases.extend((0..64u32).map(pseudorandom_taps));
        for (i, taps) in cases.iter().enumerate() {
            assert_eq!(coset_from_taps(taps), dense(taps), "tap set {i}");
        }
    }

    /// The transform is `bf`-linear per limb, which is what lets an `e4` source run
    /// the identical device code path limb-sequentially. Pinned against the dense
    /// apply on the `e4` itself, for every limb position.
    #[test]
    fn cpu_factorized_coset_e4_limbs() {
        let matrix = lde_matrix();
        for seed in [1u32, 7, 0x1234_5678, 0xdead_beef] {
            let taps: [E4; UNISKIP_TAPS] = core::array::from_fn(|t| {
                E4::from_array_of_base(core::array::from_fn(|l| {
                    pseudorandom_taps(seed.wrapping_add(l as u32 * 0x1000_0001))[t]
                }))
            });
            let dense: [E4; UNISKIP_TAPS] = core::array::from_fn(|c| {
                let mut acc = E4::ZERO;
                for t in 0..UNISKIP_TAPS {
                    <E4 as FieldExtension<F>>::add_assign_product_with_base(
                        &mut acc,
                        &taps[t],
                        &matrix[c][t],
                    );
                }
                acc
            });
            for limb in 0..4 {
                let limb_taps: [F; UNISKIP_TAPS] = core::array::from_fn(|t| e4_limb(taps[t], limb));
                let got = coset_from_taps(&limb_taps);
                for c in 0..UNISKIP_TAPS {
                    assert_eq!(
                        got[c],
                        e4_limb(dense[c], limb),
                        "seed {seed} limb {limb} cell {c}"
                    );
                }
            }
        }
    }

    /// The static counts the design is priced on: 8 exchange stages per component
    /// pass and 50 non-unity multiplies over the whole chain (17 + 16 + 17).
    #[test]
    fn cpu_ntt_twiddle_census() {
        let tables = ntt_twiddles();
        let generic = |table: usize| tables[table].iter().filter(|&&x| x != F::ONE).count();
        assert_eq!([generic(0), generic(1), generic(2)], [7, 6, 4]); // iDIF, 17
        assert_eq!(generic(3), UNISKIP_TAPS); // twist, 16 (inv16 at lane 0)
        assert_eq!([generic(4), generic(5), generic(6)], [4, 6, 7]); // DIT, 17
        let total: usize = (0..UNISKIP_NTT_TABLES).map(generic).sum();
        assert_eq!(total, 50);

        // bitrev is an involution and a permutation.
        let mut seen = [false; UNISKIP_TAPS];
        for i in 0..UNISKIP_TAPS {
            assert_eq!(bitrev_tap(bitrev_tap(i)), i);
            seen[bitrev_tap(i)] = true;
        }
        assert!(seen.iter().all(|&s| s));
    }

    #[test]
    fn cpu_fold_weights_evaluate_at_point() {
        let coeffs = seeded_coeffs();
        let taps = taps(&coeffs);
        let r = E4::from_array_of_base(core::array::from_fn(|j| {
            F::new(0x0bad_f00du32.wrapping_mul(j as u32 + 1) % F::ORDER)
        }));
        let w = fold_weights(r);
        let mut got = E4::ZERO;
        for t in 0..16 {
            <E4 as FieldExtension<F>>::add_assign_product_with_base(&mut got, &w[t], &taps[t]);
        }
        assert_eq!(got, horner_e4(&coeffs, r));
    }

    #[test]
    fn cpu_fold_weights_kronecker_on_h() {
        let omega = omega16();
        for t in 0..16 {
            let w = fold_weights(lift(omega.pow(t as u32)));
            for s in 0..16 {
                let expected = if s == t { E4::ONE } else { E4::ZERO };
                assert_eq!(w[s], expected, "t={t} s={s}");
            }
        }
    }
}
