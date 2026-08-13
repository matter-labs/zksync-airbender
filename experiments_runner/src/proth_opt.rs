//! Experimental Proth120 Montgomery multiplication exploiting the special form
//! of the modulus.
//!
//! `p = 7·2^120 + 1`, so as two 64-bit limbs `p = [1, 7·2^56]` and
//! `-p^{-1} mod 2^64 = 2^64 - 1`. In the CIOS reduction pass this collapses:
//!
//! * `m = t0 · (2^64-1) mod 2^64 = (-t0) mod 2^64` — no multiply;
//! * `m · p = m + (7m)·2^120`, and `7m = (m<<3) - m` — the whole `m·p`
//!   contribution costs shifts/adds instead of two 64×64 multiplies.
//!
//! The multiplication pass keeps its 4 real 64×64→128 multiplies (the full
//! `a·b` product), so a full field mul drops from 8 wide multiplies to 4.
//! Values and layout are identical to the reference (`canonical < p`,
//! Montgomery radix `R = 2^128`), verified by [`self_check`].

use field::{Field, Proth120, Rand};

const P_LO: u64 = 1;
const P_HI: u64 = 7u64 << 56;
const ORDER: u128 = (7u128 << 120) + 1;

/// Raw Montgomery-form value (same representation as `Proth120`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OptProth(pub u128);

#[inline(always)]
const fn mac(a: u64, b: u64, c: u64, carry: u64) -> (u64, u64) {
    let t = a as u128 + (b as u128) * (c as u128) + carry as u128;
    (t as u64, (t >> 64) as u64)
}

#[inline(always)]
const fn adc(a: u64, b: u64, carry: u64) -> (u64, u64) {
    let t = a as u128 + b as u128 + carry as u128;
    (t as u64, (t >> 64) as u64)
}

#[inline(always)]
const fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
    let (d, b0) = a.overflowing_sub(b);
    let (d, b1) = d.overflowing_sub(borrow);
    (d, (b0 || b1) as u64)
}

/// `a·b·R^{-1} mod p` with the special-form reduction. Canonical output.
#[inline(always)]
pub const fn mont_mul_opt(a: u128, b: u128) -> u128 {
    let a = [a as u64, (a >> 64) as u64];
    let b = [b as u64, (b >> 64) as u64];

    let mut t = [0u64; 4];

    let mut i = 0;
    while i < 2 {
        // multiplication pass: t += a * b[i]
        let (s, c) = mac(t[0], a[0], b[i], 0);
        t[0] = s;
        let (s, c) = mac(t[1], a[1], b[i], c);
        t[1] = s;
        let (s, c) = adc(t[2], c, 0);
        t[2] = s;
        t[3] = c;

        // reduction pass with p = [1, 7<<56], -p^{-1} = -1:
        //   m = -t0 mod 2^64;  t = (t + m + (7m)<<120) >> 64
        let m = t[0].wrapping_neg();
        // t0 + m·1: zero low limb, carry out = (t0 != 0)
        let carry0 = (t[0] != 0) as u64;
        // (7m) << 56 split into limbs: low = (7m << 56) mod 2^64,
        // high = 7m >> 8. 7m fits in 67 bits, keep it as u128.
        let m7 = (m as u128) * 7;
        let mp_lo = (m7 as u64) << 56;
        let mp_hi = (m7 >> 8) as u64;

        let (s, c) = adc(t[1], mp_lo, carry0);
        t[0] = s;
        let (s, c2) = adc(t[2], mp_hi, c);
        t[1] = s;
        t[2] = t[3].wrapping_add(c2);

        i += 1;
    }

    // t < 2p: subtract p once if needed (t[2] is the overflow bit).
    let (r0, brw) = sbb(t[0], P_LO, 0);
    let (r1, brw) = sbb(t[1], P_HI, brw);

    if t[2] < brw {
        (t[0] as u128) | ((t[1] as u128) << 64)
    } else {
        (r0 as u128) | ((r1 as u128) << 64)
    }
}

impl OptProth {
    #[inline(always)]
    pub fn mul_assign_opt(&mut self, other: &Self) -> &mut Self {
        self.0 = mont_mul_opt(self.0, other.0);
        self
    }
}

/// The optimized multiplication must agree with the reference `Proth120` mul on
/// random inputs (both operate on the same Montgomery representation).
pub fn self_check() {
    let mut rng = rand::rng();
    for _ in 0..100_000 {
        let a = Proth120::random_element(&mut rng);
        let b = Proth120::random_element(&mut rng);
        let mut r = a;
        r.mul_assign(&b);
        let got = mont_mul_opt(a.raw_u128_value(), b.raw_u128_value());
        assert_eq!(
            got,
            r.raw_u128_value(),
            "opt mont mul diverged: a={:?} b={:?}",
            a,
            b
        );
        assert!(got < ORDER);
    }
}
