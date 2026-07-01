#![no_std]

#[cfg(feature = "verifier_stats")]
pub mod stats;

pub trait NonDeterminismSource<F: ::field::PrimeField>: Send + Sync {
    fn read_word(&mut self) -> u32;
    fn read_field_element(&mut self) -> F;
}

impl<T: core::iter::Iterator<Item = u32> + Send + Sync + ?Sized> NonDeterminismSource<::field::baby_bear::base::BabyBearField> for T {
    #[inline(always)]
    fn read_word(&mut self) -> u32 {
        self.next().expect("next word")
    }

    #[inline(always)]
    fn read_field_element(&mut self) -> ::field::baby_bear::base::BabyBearField {
        let value = self.next().expect("next word");
        use ::field::PrimeField;
        ::field::baby_bear::base::BabyBearField::from_raw_repr_with_reduction(value)
    }
}

#[cfg(target_arch = "riscv32")]
#[derive(Clone, Copy, Debug)]
pub struct CSRBasedSource;

#[cfg(target_arch = "riscv32")]
impl NonDeterminismSource<::field::baby_bear::base::BabyBearField> for CSRBasedSource {
    #[inline(always)]
    fn read_word(&mut self) -> u32 {
        #[cfg(feature = "verifier_stats")]
        stats::NDS_STATS.with_borrow_mut(|s| s.read_bytes += core::mem::size_of::<u32>());
        csr_read_word()
    }
    #[inline(always)]
    fn read_reduced_field_element(&mut self) -> ::field::baby_bear::base::BabyBearField {
        #[cfg(feature = "verifier_stats")]
        stats::NDS_STATS.with_borrow_mut(|s| s.read_bytes += core::mem::size_of::<u32>());
        let repr = csr_read_field_element();
        use ::field::PrimeField;
        ::field::baby_bear::base::BabyBearField::from_reduced_raw_repr(value)
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
fn csr_read_field_element() -> u32 {
    use common_constants::mops::MOP_ADD_MOD;
    let mut output;
    unsafe {
        core::arch::asm!(
            "csrrw {tmp}, 0x7c0, x0",
            "mop.rr.{idx} {rd}, {tmp}, x0",
            tmp = out(reg) _,
            rd = lateout(reg) output,
            idx = const MOP_ADD_MOD,
            options(nomem, nostack, preserves_flags)
        );
    }

    output
}
