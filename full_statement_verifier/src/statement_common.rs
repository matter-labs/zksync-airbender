use super::*;
use verifier_common::non_determinism_source::U32WordNonDeterminismSource;

/// Reads a single `SIZE`-wide Merkle cap off the non-determinism stream.
///
/// # Safety
///
/// `MerkleTreeCap<SIZE>` must be a plain `#[repr]`-transparent block of `u32`s (it is), so
/// that `read_caps_into` fully initializes the `MaybeUninit` before `assume_init`. The caller
/// must also be at a cap boundary in the stream — reading elsewhere yields a well-formed but
/// meaningless cap.
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
