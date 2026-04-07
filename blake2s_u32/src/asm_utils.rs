#[inline(always)]
#[cfg(all(
    target_arch = "riscv32",
    target_feature = "zbb",
    not(feature = "mop_extension")
))]
pub fn rotate_right<const AMT: u32>(value: u32) -> u32 {
    let mut output;
    unsafe {
        core::arch::asm!(
            "rori {rd}, {rs1}, {amt}",
            rs1 = in(reg) value,
            rd = lateout(reg) output,
            amt = const AMT,
            options(nomem, nostack, preserves_flags)
        );
    }

    output
}

#[inline(always)]
#[cfg(not(all(
    target_arch = "riscv32",
    target_feature = "zimop",
    feature = "mop_extension"
)))]
pub fn rotate_right<const AMT: u32>(value: u32) -> u32 {
    value.rotate_right(AMT)
}

#[inline(always)]
#[cfg(all(
    target_arch = "riscv32",
    target_feature = "zimop",
    feature = "mop_extension"
))]
pub fn rotate_right<const AMT: u32>(value: u32) -> u32 {
    let mut output;
    unsafe {
        core::arch::asm!(
            "mop.r.{amt} {rd}, {rs1}",
            rs1 = in(reg) value,
            rd = lateout(reg) output,
            amt = const AMT,
            options(nomem, nostack, preserves_flags)
        );
    }

    output
}
