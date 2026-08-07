//! Host-side domain math for the uniskip pass: the size-16 subgroup `H`, its odd
//! coset `gamma * H`, the coset LDE matrix and the Lagrange fold weights.

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
/// `M[c][t] = L_t(gamma * omega^c)`: extends 16 taps on `H` to the 16 coset cells.
pub fn lde_matrix() -> [[F; 16]; 16] {
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

/// `[L_t(r)]_t`: the weights that fold 16 taps on `H` into the evaluation at `r`.
pub fn fold_weights(r: E4) -> [E4; 16] {
    let omega = omega16();
    // On H the barycentric form divides by zero; the weights are the Kronecker delta.
    if let Some(t) = (0..16).find(|&t| r == lift(omega.pow(t as u32))) {
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
