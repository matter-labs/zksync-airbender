#![no_std]

#[cfg(feature = "verifier_stats")]
pub mod stats;

pub trait NonDeterminismSource: Send + Sync {
    fn read_word(&mut self) -> u32;
    fn read_reduced_field_element(&mut self, modulus: u32) -> u32;
}

impl NonDeterminismSource for () {
    #[inline(always)]
    fn read_word(&mut self) -> u32 {
        0
    }
    #[inline(always)]
    fn read_reduced_field_element(&mut self, _modulus: u32) -> u32 {
        0
    }
}

impl<T: core::iter::Iterator<Item = u32>> NonDeterminismSource for T {
    #[inline(always)]
    fn read_word(&mut self) -> u32 {
        self.next().expect("next word")
    }

    #[inline(always)]
    fn read_reduced_field_element(&mut self, modulus: u32) -> u32 {
        let value = self.next().expect("next word");
        assert!(value < modulus, "by default we expect reduced field elements everywhere");

        value
    }
}

#[cfg(target_arch = "riscv32")]
#[derive(Clone, Copy, Debug)]
pub struct CSRBasedSource;

#[cfg(target_arch = "riscv32")]
impl NonDeterminismSource for CSRBasedSource {
    #[inline(always)]
    fn read_word(&mut self) -> u32 {
        #[cfg(feature = "verifier_stats")]
        stats::NDS_STATS.with_borrow_mut(|s| s.read_bytes += core::mem::size_of::<u32>());
        csr_read_word()
    }
    #[inline(always)]
    fn read_reduced_field_element(&mut self, modulus: u32) -> u32 {
        #[cfg(feature = "verifier_stats")]
        stats::NDS_STATS.with_borrow_mut(|s| s.read_bytes += core::mem::size_of::<u32>());
        csr_read_field_element(modulus)
    }
}

#[inline(always)]
#[cfg(target_arch = "riscv32")]
fn csr_read_word() -> u32 {
    let mut output;
    unsafe {
        core::arch::asm!(
            "csrrw {rd}, 0x7c0, x0",
            rd = out(reg) output,
            options(nomem, nostack, preserves_flags)
        );
    }

    output
}

#[inline(always)]
#[cfg(target_arch = "riscv32")]
fn csr_read_field_element(_modulus: u32) -> u32 {
    let mut output;
    unsafe {
        core::arch::asm!(
            "csrrw {tmp}, 0x7c0, x0",
            "mop.rr.0 {rd}, {tmp}, x0",
            tmp = out(reg) _,
            rd = lateout(reg) output,
            options(nomem, nostack, preserves_flags)
        );
    }

    output
}
