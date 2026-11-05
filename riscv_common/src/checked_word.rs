//! Refusal of the checked word-memory runtime: the reduced machine's deliberate trap on the guest,
//! reached by a direct call without formatting or a memory routine; a panic in host tests.

#[cfg(target_arch = "riscv32")]
#[inline(always)]
pub(crate) fn refuse() -> ! {
    crate::zksync_os_finish_error()
}

#[cfg(not(target_arch = "riscv32"))]
pub(crate) fn refuse() -> ! {
    panic!("checked_word_memory: invalid arguments")
}
