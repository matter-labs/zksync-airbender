use super::*;

#[allow(invalid_value)]
#[inline(always)]
pub unsafe fn read_setups<I: NonDeterminismSource, const N: usize>(
) -> [[MerkleTreeCap<CAP_SIZE>; NUM_COSETS]; N] {
    let mut result: [[MaybeUninit<MerkleTreeCap<CAP_SIZE>>; 2]; N] =
        [[const { core::mem::MaybeUninit::uninit() }; NUM_COSETS]; N];

    for dst in result.iter_mut() {
        MerkleTreeCap::<CAP_SIZE>::read_caps_into::<I, NUM_COSETS>(dst.as_mut_ptr().cast());
    }

    result.map(|el| el.map(|el| el.assume_init()))
}

pub const FINAL_PC_BUFFER_PC_IDX: usize = 0;
pub const FINAL_PC_BUFFER_TS_LOW_IDX: usize = 1;
pub const FINAL_PC_BUFFER_TS_HIGH_IDX: usize = 2;
