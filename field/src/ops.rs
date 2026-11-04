// Here we will define planform-specific implementation of basic ops for the base field.
// Platform-specific implementation for extension (if any) will be in the separate files

#[cfg(all(not(target_arch = "riscv32"), feature = "use_division"))]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
pub(crate) const fn reduce_with_division(value: u32) -> u32 {
    reduce_with_division_ct(value)
}

#[cfg(all(target_arch = "riscv32", feature = "use_division"))]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
pub(crate) const fn reduce_with_division(value: u32) -> u32 {
    core::intrinsics::const_eval_select(
        (value,),
        reduce_with_division_ct,
        reduce_with_division_rt_riscv,
    )
}

#[cfg(target_arch = "riscv32")]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
const fn reduce_with_division_ct(value: u32) -> u32 {
    value % crate::Mersenne31Field::ORDER
}

#[cfg(all(
    target_arch = "riscv32",
    feature = "use_division",
    not(feature = "modular_ops")
))]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
fn reduce_with_division_rt_riscv(value: u32) -> u32 {
    // LLVM is a clever beast that does transform operation `a % MODULUS` into multiplication
    // for the fixed modulus. We want to inhibit such behavior, and will need assembly tricks for it
    let modulus = crate::Mersenne31Field::ORDER;
    let mut output;
    unsafe {
        core::arch::asm!(
            "remu {rd}, {inp}, {ch}",
            ch = in(reg) modulus,
            inp = in(reg) value,
            rd = lateout(reg) output,
            options(nomem, nostack, preserves_flags)
        );
    }

    output
}

#[cfg(all(
    target_arch = "riscv32",
    feature = "use_division",
    feature = "modular_ops"
))]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
fn reduce_with_division_rt_riscv(value: u32) -> u32 {
    // here we add with 0 to get reduction
    add_mod(value, 0)
}

// we will also fully define addmod/submod/mulmod, that can have different implementation strategies on different platforms,
// especially on circuit-bound ones

// generic implementation

#[cfg(not(target_arch = "riscv32"))]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
pub(crate) const fn add_mod(a: u32, b: u32) -> u32 {
    let mut sum = a.wrapping_add(b);
    let msb = sum & (1 << 31);
    sum ^= msb;
    sum += (msb != 0) as u32;

    sum
}

#[cfg(not(target_arch = "riscv32"))]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
pub(crate) const fn sub_mod(a: u32, b: u32) -> u32 {
    let mut sum = a.wrapping_sub(b);
    let msb = sum & (1 << 31);
    sum ^= msb;
    sum -= (msb != 0) as u32;

    sum
}

#[cfg(not(target_arch = "riscv32"))]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
pub(crate) const fn mul_mod(a: u32, b: u32) -> u32 {
    let product = (a as u64) * (b as u64);
    let product_low = (product as u32) & ((1 << 31) - 1);
    let product_high = (product >> 31) as u32;
    add_mod(product_low, product_high)
}

#[cfg(not(target_arch = "riscv32"))]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
/// a * b + c
pub(crate) const fn fma_mod(a: u32, b: u32, c: u32) -> u32 {
    // we can "save" on reduction, by using a fact that for N bit integer one can do multiplication + 2 additions
    // without overflowing 2N bits, so we will have our high and low parts in the same ranges as normally expected
    // by add_mod
    let product = (a as u64) * (b as u64) + (c as u64);
    let product_low = (product as u32) & ((1 << 31) - 1);
    let product_high = (product >> 31) as u32;
    add_mod(product_low, product_high)
}

#[cfg(target_arch = "riscv32")]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
pub(crate) const fn fma_mod(a: u32, b: u32, c: u32) -> u32 {
    let t = mul_mod(a, b);
    add_mod(c, t)
}

// risc-v target specific implementation

#[cfg(target_arch = "riscv32")]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
pub(crate) const fn add_mod(a: u32, b: u32) -> u32 {
    core::intrinsics::const_eval_select((a, b), add_mod_ct, add_mod_rt_riscv)
}

#[cfg(target_arch = "riscv32")]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
const fn add_mod_ct(a: u32, b: u32) -> u32 {
    reduce_with_division_ct(a.wrapping_add(b))
}

#[cfg(all(
    target_arch = "riscv32",
    feature = "use_division",
    not(feature = "modular_ops")
))]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
fn add_mod_rt_riscv(a: u32, b: u32) -> u32 {
    reduce_with_division_rt_riscv(a.wrapping_add(b))
}

#[cfg(all(target_arch = "riscv32", feature = "modular_ops"))]
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

#[cfg(target_arch = "riscv32")]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
pub(crate) const fn sub_mod(a: u32, b: u32) -> u32 {
    core::intrinsics::const_eval_select((a, b), sub_mod_ct, sub_mod_rt_riscv)
}

#[cfg(target_arch = "riscv32")]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
const fn sub_mod_ct(a: u32, b: u32) -> u32 {
    reduce_with_division_ct(
        crate::Mersenne31Field::ORDER
            .wrapping_add(a)
            .wrapping_sub(b),
    )
}

#[cfg(all(
    target_arch = "riscv32",
    feature = "use_division",
    not(feature = "modular_ops")
))]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
fn sub_mod_rt_riscv(a: u32, b: u32) -> u32 {
    reduce_with_division_rt_riscv(
        crate::Mersenne31Field::ORDER
            .wrapping_add(a)
            .wrapping_sub(b),
    )
}

#[cfg(all(target_arch = "riscv32", feature = "modular_ops"))]
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

#[cfg(target_arch = "riscv32")]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
const fn mul_mod_ct(a: u32, b: u32) -> u32 {
    let product = (a as u64) * (b as u64);
    let product_low = (product as u32) & ((1 << 31) - 1);
    let product_high = (product >> 31) as u32;
    reduce_with_division_ct(product_low.wrapping_add(product_high))
}

#[cfg(all(
    target_arch = "riscv32",
    feature = "use_division",
    not(feature = "modular_ops")
))]
#[cfg_attr(not(feature = "no_inline"), inline(always))]
fn mul_mod_rt_riscv(a: u32, b: u32) -> u32 {
    let product = (a as u64) * (b as u64);
    let product_low = (product as u32) & ((1 << 31) - 1);
    let product_high = (product >> 31) as u32;
    reduce_with_division_rt_riscv(product_low.wrapping_add(product_high))
}

#[cfg(all(target_arch = "riscv32", feature = "modular_ops"))]
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
