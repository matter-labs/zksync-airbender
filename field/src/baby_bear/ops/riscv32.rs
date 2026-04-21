// risc-v target specific implementation

#[cfg_attr(not(feature = "no_inline"), inline(always))]
const fn reduce_with_division_ct(value: u32) -> u32 {
    value % crate::baby_bear::base::BabyBearField::ORDER
}

#[cfg_attr(not(feature = "no_inline"), inline(always))]
pub(crate) const fn add_mod(a: u32, b: u32) -> u32 {
    core::intrinsics::const_eval_select((a, b), add_mod_ct, add_mod_rt_riscv)
}

#[cfg_attr(not(feature = "no_inline"), inline(always))]
const fn add_mod_ct(a: u32, b: u32) -> u32 {
    reduce_with_division_ct(a.wrapping_add(b))
}

#[cfg(feature = "modular_ops")]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
fn add_mod_rt_riscv(a: u32, b: u32) -> u32 {
    let mut output;
    unsafe {
        core::arch::asm!(
            "mop.rr.0 {rd}, {a}, {b}",
            a = in(reg) a,
            b = in(reg) b,
            rd = lateout(reg) output,
            options(nomem, nostack, preserves_flags)
        );
    }

    output
}

#[cfg_attr(not(feature = "no_inline"), inline(always))]
pub(crate) const fn sub_mod(a: u32, b: u32) -> u32 {
    core::intrinsics::const_eval_select((a, b), sub_mod_ct, sub_mod_rt_riscv)
}

#[cfg_attr(not(feature = "no_inline"), inline(always))]
const fn sub_mod_ct(a: u32, b: u32) -> u32 {
    reduce_with_division_ct(
        crate::baby_bear::base::BabyBearField::ORDER
            .wrapping_add(a)
            .wrapping_sub(b),
    )
}

#[cfg(feature = "modular_ops")]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
fn sub_mod_rt_riscv(a: u32, b: u32) -> u32 {
    let mut output;
    unsafe {
        core::arch::asm!(
            "mop.rr.1 {rd}, {a}, {b}",
            a = in(reg) a,
            b = in(reg) b,
            rd = lateout(reg) output,
            options(nomem, nostack, preserves_flags)
        );
    }

    output
}

#[cfg(target_arch = "riscv32")]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
pub(crate) const fn mul_mod(a: u32, b: u32) -> u32 {
    core::intrinsics::const_eval_select((a, b), mul_mod_ct, mul_mod_rt_riscv)
}

#[cfg_attr(not(feature = "no_inline"), inline(always))]
const fn mul_mod_ct(a: u32, b: u32) -> u32 {
    use crate::baby_bear::base::BabyBearField;
    let product = (a as u64).wrapping_mul(b as u64);
    let m = (product as u32).wrapping_mul(BabyBearField::MONT_K);
    let adjusted = product.wrapping_add((m as u64).wrapping_mul(BabyBearField::ORDER as u64));
    let result = (adjusted >> 32) as u32;
    if result >= BabyBearField::ORDER {
        result - BabyBearField::ORDER
    } else {
        result
    }
}

#[cfg(feature = "modular_ops")]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
fn mul_mod_rt_riscv(a: u32, b: u32) -> u32 {
    let mut output;
    unsafe {
        core::arch::asm!(
            "mop.rr.2 {rd}, {a}, {b}",
            a = in(reg) a,
            b = in(reg) b,
            rd = lateout(reg) output,
            options(nomem, nostack, preserves_flags)
        );
    }

    output
}

#[cfg_attr(not(feature = "no_inline"), inline(always))]
pub(crate) const fn fma_mod(a: u32, b: u32, c: u32) -> u32 {
    let t = mul_mod(a, b);
    add_mod(c, t)
}
