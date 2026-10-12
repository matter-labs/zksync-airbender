use super::*;
use verifier_common::non_determinism_source::U32WordNonDeterminismSource;

/// # Safety
///
/// No extra caller obligations: `read_caps_into` writes every word of the cap from
/// `nd_source` before it is assumed initialized.
#[allow(invalid_value)]
#[inline(always)]
pub unsafe fn read_setup_cap<I: U32WordNonDeterminismSource, const SIZE: usize>(
    nd_source: &mut I,
) -> MerkleTreeCap<SIZE> {
    let mut result: MaybeUninit<MerkleTreeCap<SIZE>> = core::mem::MaybeUninit::uninit();

    MerkleTreeCap::<SIZE>::read_caps_into::<I, 1>(result.as_mut_ptr().cast(), nd_source);

    result.assume_init()
}

pub const FINAL_PC_BUFFER_PC_IDX: usize = 0;
pub const FINAL_PC_BUFFER_TS_LOW_IDX: usize = 1;
pub const FINAL_PC_BUFFER_TS_HIGH_IDX: usize = 2;
