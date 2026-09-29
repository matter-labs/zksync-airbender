#![no_std]

#[cfg(feature = "verifier_stats")]
pub mod stats;

pub trait U32WordNonDeterminismSource: Send + Sync {
    fn read_word(&mut self) -> u32;
}

pub trait NonDeterminismSource<F: ::field::PrimeField>: U32WordNonDeterminismSource {
    /// Reads a field element in its raw representation.
    ///
    /// SAFETY (simulation): it may ONLY be used for the values that an honest prover provides
    /// as canonical field elements (proof values such as evaluations, sumcheck coefficients,
    /// leaf openings, etc). The RISC-V implementation reduces the word via a field operation
    /// opcode (addition of zero), and the simulator can run in a mode that assumes the inputs
    /// of such opcodes to be canonical (`MopField::BabyBearAssumeCanonical` of the
    /// `riscv_transpiler`'s JIT), where that addition is just a move. So a word that is not
    /// canonical makes such simulation diverge from the circuits (that do reduce), and proving
    /// of this execution fails - that is acceptable for a malformed proof, but not for honest
    /// data. Anything that is a full-range `u32` a-priori (words drawn from the transcript,
    /// hash outputs, timestamps, etc) must be read via `read_word` and converted using
    /// `PrimeField::from_raw_repr_with_reduction` / `from_u32_with_reduction`, that reduce
    /// without the field operation opcodes.
    fn read_field_element(&mut self) -> F;
}

impl<T: core::iter::Iterator<Item = u32> + Send + Sync + ?Sized> U32WordNonDeterminismSource for T {
    #[inline(always)]
    fn read_word(&mut self) -> u32 {
        self.next().expect("next word")
    }
}

impl<T: core::iter::Iterator<Item = u32> + Send + Sync + ?Sized>
    NonDeterminismSource<::field::baby_bear::base::BabyBearField> for T
{
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
impl U32WordNonDeterminismSource for CSRBasedSource {
    #[inline(always)]
    fn read_word(&mut self) -> u32 {
        #[cfg(feature = "verifier_stats")]
        stats::NDS_STATS.with_borrow_mut(|s| s.read_bytes += core::mem::size_of::<u32>());
        csr_read_word()
    }
}

#[cfg(target_arch = "riscv32")]
impl NonDeterminismSource<::field::baby_bear::base::BabyBearField> for CSRBasedSource {
    #[inline(always)]
    fn read_field_element(&mut self) -> ::field::baby_bear::base::BabyBearField {
        #[cfg(feature = "verifier_stats")]
        stats::NDS_STATS.with_borrow_mut(|s| s.read_bytes += core::mem::size_of::<u32>());
        // NOTE: see the safety comment at `NonDeterminismSource::read_field_element` - the
        // reduction inside is a field addition of zero, a NOP for a simulator that assumes
        // canonical inputs
        let repr = csr_read_field_element();
        use ::field::PrimeField;
        ::field::baby_bear::base::BabyBearField::from_reduced_raw_repr(repr)
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
