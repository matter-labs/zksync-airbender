//! DRAFT: Proth120 Montgomery multiplication in x86-64 inline assembly using
//! BMI2 `mulx` (flag-free widening multiply) and ADX `adcx`/`adox` (two
//! independent carry chains), combined with the special-form reduction
//! (`-p^{-1} = -1`, `m·p = m + (7m)·2^120`).
//!
//! Rationale: LLVM already emits `mulx` at x86-64-v3, but it never emits
//! `adcx`/`adox`, so the dual-carry-chain layout — the classic bigint win on
//! Intel — can only be tested with hand-written asm. Total wide multiplies per
//! field mul: 4 for `a·b` plus 2 cheap `m·7` (vs 8 in the generic CIOS).
//!
//! Same Montgomery representation (`R = 2^128`, canonical `< p`) as the
//! reference `Proth120`; validated by [`self_check`].

#![allow(dead_code)]

#[cfg(target_arch = "x86_64")]
pub mod imp {
    use core::arch::asm;

    const P_LO: u64 = 1;
    const P_HI: u64 = 7u64 << 56;
    const ORDER: u128 = (7u128 << 120) + 1;

    /// `a·b·R^{-1} mod p`, canonical output. mulx + adcx/adox + special-form
    /// reduction.
    #[inline]
    pub fn mont_mul_adx(a: u128, b: u128) -> u128 {
        let a0 = a as u64;
        let a1 = (a >> 64) as u64;
        let b0 = b as u64;
        let b1 = (b >> 64) as u64;

        let mut r0: u64;
        let mut r1: u64;

        unsafe {
            asm!(
                // ---------------- round 0: t = a·b0 (b0 pre-loaded in rdx) --
                "mulx {t1}, {t0}, {a0}",       // t1:t0 = a0·b0
                "mulx {t2}, {sc}, {a1}",       // t2:sc = a1·b0
                "add {t1}, {sc}",
                "adc {t2}, 0",
                // m = -t0 mod 2^64, carry0 = (t0 != 0)
                "mov {m}, {t0}",
                "neg {m}",                      // CF = (t0 != 0)
                "mov {c0}, 0",
                "adc {c0}, 0",                  // c0 = carry0
                // (7m) << 56 into hi:lo (mulx is flag-free)
                "mov rdx, 7",
                "mulx {mh}, {ml}, {m}",         // mh:ml = 7m
                "shld {mh}, {ml}, 56",
                "shl {ml}, 56",
                // t = (t1 + c0 + ml, t2 + mh + cf, cf2)   [dropped low limb]
                "add {t1}, {c0}",
                "adc {t2}, {mh}",
                "mov {t3}, 0",
                "adc {t3}, 0",
                "add {t1}, {ml}",
                "adc {t2}, 0",
                "adc {t3}, 0",
                // rename: t0 <- t1, t1 <- t2, t2 <- t3
                // ---------------- round 1: t += a·b1 (dual chains) --
                "mov rdx, {b1}",
                "mulx {sc}, {c0}, {a0}",        // sc:c0 = a0·b1  (c0 reused as lo)
                "mulx {m}, {ml}, {a1}",         // m:ml = a1·b1   (m reused as hi)
                "xor {mh}, {mh}",               // clear CF and OF; mh = 0
                // chain CF (adcx): t1 += lo0, t2 += hi0
                "adcx {t1}, {c0}",
                "adcx {t2}, {sc}",
                "adcx {t3}, {mh}",              // absorb CF into t3
                // chain OF (adox): t2 += lo1, t3 += hi1
                "adox {t2}, {ml}",
                "adox {t3}, {m}",
                // (no further OF propagation: t3 cannot overflow, sum < 2^64)
                // m = -t0' mod 2^64 with t0' = t1
                "mov {m}, {t1}",
                "neg {m}",
                "mov {c0}, 0",
                "adc {c0}, 0",
                "mov rdx, 7",
                "mulx {mh}, {ml}, {m}",
                "shld {mh}, {ml}, 56",
                "shl {ml}, 56",
                "add {t2}, {c0}",
                "adc {t3}, {mh}",
                "add {t2}, {ml}",
                "adc {t3}, 0",
                // result limbs: (t2, t3) + possible >= p correction below
                b1 = in(reg) b1,
                a0 = in(reg) a0,
                a1 = in(reg) a1,
                t0 = out(reg) _,
                t1 = out(reg) _,
                t2 = out(reg) r0,
                t3 = out(reg) r1,
                sc = out(reg) _,
                m = out(reg) _,
                mh = out(reg) _,
                ml = out(reg) _,
                c0 = out(reg) _,
                inout("rdx") b0 => _,
                options(pure, nomem, nostack),
            );
        }

        // t < 2p here (t2 overflow folded into the top limb r1; p_hi = 7<<56 so
        // r1 can exceed P_HI by at most the carry). Conditional subtract p.
        let t = (r0 as u128) | ((r1 as u128) << 64);
        if t >= ORDER {
            t - ORDER
        } else {
            t
        }
    }
}

/// Compare against the reference `Proth120` multiplication on random inputs.
#[cfg(target_arch = "x86_64")]
pub fn self_check() {
    use field::{Field, PrimeField, Proth120, Rand};
    let mut rng = rand::rng();
    for _ in 0..200_000 {
        let a = Proth120::random_element(&mut rng);
        let b = Proth120::random_element(&mut rng);
        let mut r = a;
        r.mul_assign(&b);
        let got = imp::mont_mul_adx(a.raw_u128_value(), b.raw_u128_value());
        assert_eq!(
            got,
            r.raw_u128_value(),
            "adx mont mul diverged: a={a:?} b={b:?}"
        );
    }
}

#[cfg(not(target_arch = "x86_64"))]
pub fn self_check() {}
