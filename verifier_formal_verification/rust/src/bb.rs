//! BabyBear (p = 2^31 - 2^27 + 1, Montgomery form) and its extensions Ext2 = F[v]/(v^2 - 11),
//! Ext4 = Ext2[w]/(w^2 - v), as in zksync-airbender `field/src/baby_bear` (riscv32 code paths).
//! Ext4 mul is `mul_assign_flat_impl_fma` in both variants. Feature `mop`: the base ops are Airbender's field
//! opcodes `mop.rr.N` (`ops/riscv32.rs`, `modular_ops` + `modular_fma`). Default: the same ops in plain Rust
//! (`ops/basic.rs`'s `add_mod` / `mul_mod`, and `fma_mod = add_mod(c, mul_mod(a, b))` as `ops/riscv32.rs` without
//! `modular_fma`), as separate functions; this variant does not trust the field opcodes.

pub const ORDER: u32 = 0x78000001;
const MONT_K: u32 = 0x77ffffff;
const MONT_R2: u32 = {
    let r = (1u64 << 32) % (ORDER as u64);
    ((r * r) % (ORDER as u64)) as u32
};

/// Montgomery product `a b 2^-32 mod p` (`ops/basic.rs` `mul_mod`, `ops/riscv32.rs` `mul_mod_ct`).
pub const fn mul_mod_ct(a: u32, b: u32) -> u32 {
    let product = (a as u64).wrapping_mul(b as u64);
    let m = (product as u32).wrapping_mul(MONT_K);
    let adjusted = product.wrapping_add((m as u64).wrapping_mul(ORDER as u64));
    let result = (adjusted >> 32) as u32;
    if result >= ORDER { result - ORDER } else { result }
}

/// `BabyBearField::new` at compile time: canonical `v < p` to Montgomery form.
pub const fn new_ct(v: u32) -> u32 {
    mul_mod_ct(v, MONT_R2)
}

const NON_RES: u32 = new_ct(11);

#[cfg(not(feature = "mop"))]
mod ops {
    use super::ORDER;

    /// `ops/basic.rs` `add_mod`.
    #[inline(always)]
    fn add_mod(a: u32, b: u32) -> u32 {
        let mut sum = a.wrapping_add(b);
        if sum >= ORDER {
            sum -= ORDER;
        }
        sum
    }

    #[unsafe(no_mangle)]
    #[inline(never)]
    pub extern "C" fn bb_add(a: u32, b: u32) -> u32 {
        add_mod(a, b)
    }

    #[unsafe(no_mangle)]
    #[inline(never)]
    pub extern "C" fn bb_mul(a: u32, b: u32) -> u32 {
        super::mul_mod_ct(a, b)
    }

    /// `c + a b 2^-32` (`fma_mod` without `modular_fma`).
    #[unsafe(no_mangle)]
    #[inline(never)]
    pub extern "C" fn bb_fma(a: u32, b: u32, c: u32) -> u32 {
        add_mod(c, super::mul_mod_ct(a, b))
    }

    pub use bb_add as add;
    pub use bb_fma as fma;
    pub use bb_mul as mul;
}

#[cfg(feature = "mop")]
mod ops {
    macro_rules! mop {
        ($name:ident, $idx:literal) => {
            #[inline(always)]
            pub fn $name(a: u32, b: u32) -> u32 {
                let mut output;
                unsafe {
                    core::arch::asm!(
                        concat!("mop.rr.", $idx, " {rd}, {a}, {b}"),
                        a = in(reg) a,
                        b = in(reg) b,
                        rd = lateout(reg) output,
                        options(nomem, nostack, preserves_flags)
                    );
                }
                output
            }
        };
    }
    mop!(add, 0);
    mop!(mul, 2);

    /// `c + a b 2^-32` (`fma_mod_rt_riscv`).
    #[inline(always)]
    pub fn fma(a: u32, b: u32, mut c: u32) -> u32 {
        unsafe {
            core::arch::asm!(
                "mop.rr.3 {c}, {a}, {b}",
                a = in(reg) a,
                b = in(reg) b,
                c = inlateout(reg) c,
                options(nomem, nostack, preserves_flags)
            );
        }
        c
    }
}

pub use ops::{add, mul};

/// `BabyBearField::new` at run time.
#[inline(always)]
pub fn new(v: u32) -> u32 {
    mul(v, MONT_R2)
}

/// `BabyBearField::to_u32`: back from Montgomery form.
#[inline(always)]
pub fn to_u32(x: u32) -> u32 {
    mul(x, 1)
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Ext2 {
    pub c0: u32,
    pub c1: u32,
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Ext4 {
    pub c0: Ext2,
    pub c1: Ext2,
}

mod ext {
    use super::ops::{fma, mul};
    use super::{Ext2, Ext4, NON_RES};

    /// `BabyBearExt4::mul_assign_flat_impl_fma`.
    #[inline(always)]
    pub fn ext4_mul_assign(a: &mut Ext4, b: &Ext4) {
        let (a0, a1, a2, a3) = (a.c0.c0, a.c0.c1, a.c1.c0, a.c1.c1);
        let b0 = b.c0.c0;
        let mut o0 = mul(a0, b0);
        let mut o1 = mul(a1, b0);
        let mut o2 = mul(a2, b0);
        let mut o3 = mul(a3, b0);
        let a1n = mul(a1, NON_RES);
        let a3n = mul(a3, NON_RES);
        let b1 = b.c0.c1;
        o0 = fma(a1n, b1, o0);
        o1 = fma(a0, b1, o1);
        o2 = fma(a3n, b1, o2);
        o3 = fma(a2, b1, o3);
        let b2 = b.c1.c0;
        o0 = fma(a3n, b2, o0);
        o1 = fma(a2, b2, o1);
        o2 = fma(a0, b2, o2);
        o3 = fma(a1, b2, o3);
        let b3 = b.c1.c1;
        let a2n = mul(a2, NON_RES);
        o0 = fma(a2n, b3, o0);
        o1 = fma(a3n, b3, o1);
        o2 = fma(a1n, b3, o2);
        o3 = fma(a0, b3, o3);
        a.c0 = Ext2 { c0: o0, c1: o1 };
        a.c1 = Ext2 { c0: o2, c1: o3 };
    }
}

pub use ext::ext4_mul_assign;

/// `BabyBearExt4::add_assign`.
#[inline(always)]
pub fn ext4_add_assign(a: &mut Ext4, b: &Ext4) {
    a.c0.c0 = add(a.c0.c0, b.c0.c0);
    a.c0.c1 = add(a.c0.c1, b.c0.c1);
    a.c1.c0 = add(a.c1.c0, b.c1.c0);
    a.c1.c1 = add(a.c1.c1, b.c1.c1);
}

/// `acc = acc x + c`: one Horner step (the only call in `ext4_horner`, so its code is the same in both variants).
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ext4_mul_add(acc: &mut Ext4, x: &Ext4, c: &Ext4) {
    ext4_mul_assign(acc, x);
    ext4_add_assign(acc, c);
}

/// Horner over Ext4: `acc = ((c[n-1] x + c[n-2]) x + ...) x + c[0]`.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ext4_horner(out: &mut Ext4, coeffs: *const Ext4, n: u32, x: &Ext4) {
    let mut acc = Ext4 { c0: Ext2 { c0: 0, c1: 0 }, c1: Ext2 { c0: 0, c1: 0 } };
    let mut i = n;
    while i != 0 {
        i -= 1;
        ext4_mul_add(&mut acc, x, unsafe { &*coeffs.add(i as usize) });
    }
    *out = acc;
}
