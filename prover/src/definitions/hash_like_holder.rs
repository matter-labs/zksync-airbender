use core::mem::MaybeUninit;
use non_determinism_source::NonDeterminismSource;

pub const DIGEST_SIZE_U32_WORDS: usize = 8;

const _: () = const {
    assert!(DIGEST_SIZE_U32_WORDS == blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS);
    assert!(DIGEST_SIZE_U32_WORDS == poseidon2::m31::HASH_SIZE_U32_WORDS);

    ()
};

// Simple structure to hold root or cap of the Merkle tree. Almost a proxy for a bag of bytes. If used with
// algebrai hashes, it's caller's responsibility to either expect some reduction behavior,
// or provide separate function for comparison
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize, Hash)]
pub struct MerkleTreeCap<const N: usize> {
    #[serde(with = "serde_big_array::BigArray")]
    // #[serde(bound(deserialize = "[[u32; DIGEST_SIZE_U32_WORDS]; N]: serde::Deserialize<'de>"))]
    // #[serde(bound(serialize = "[[u32; DIGEST_SIZE_U32_WORDS]; N]: serde::Serialize"))]
    pub cap: [[u32; DIGEST_SIZE_U32_WORDS]; N],
}

const _: () = const {
    assert!(
        core::mem::size_of::<MerkleTreeCap::<1>>()
            == core::mem::size_of::<[u32; DIGEST_SIZE_U32_WORDS]>() * 1
    );
    assert!(
        core::mem::size_of::<MerkleTreeCap::<16>>()
            == core::mem::size_of::<[u32; DIGEST_SIZE_U32_WORDS]>() * 16
    );

    assert!(core::mem::align_of::<MerkleTreeCap::<1>>() == core::mem::align_of::<u32>());
    assert!(core::mem::align_of::<MerkleTreeCap::<16>>() == core::mem::align_of::<u32>());

    ()
};

impl<const N: usize> MerkleTreeCap<N> {
    pub fn dummy() -> Self {
        Self {
            cap: [[0u32; DIGEST_SIZE_U32_WORDS]; N],
        }
    }

    pub fn new<I: NonDeterminismSource>() -> Self {
        unsafe {
            let mut new = Self {
                cap: [MaybeUninit::uninit(); N].map(|el| el.assume_init()),
            };

            for dst in new.cap.iter_mut() {
                for dst in dst.iter_mut() {
                    *dst = I::read_word();
                }
            }

            new
        }
    }

    pub unsafe fn read_caps_into<I: NonDeterminismSource, const M: usize>(dst: *mut [Self; M]) {
        let mut ptr: *mut u32 = dst.cast();
        let end = ptr.add(DIGEST_SIZE_U32_WORDS * N * M);
        while ptr < end {
            ptr.write(I::read_word());
            ptr = ptr.add(1);
        }
    }

    pub fn flatten<const M: usize>(input: &'_ [Self; M]) -> &'_ [u32] {
        // layouts are the same
        unsafe {
            core::slice::from_ptr_range(
                input.as_ptr_range().start.cast::<u32>()..input.as_ptr_range().end.cast::<u32>(),
            )
        }
    }

    pub fn compare<const M: usize>(a: &[Self; M], b: &[Self; M]) -> bool {
        let mut equal = true;
        unsafe {
            for i in 0..M {
                let a = a.get_unchecked(i);
                let b = b.get_unchecked(i);
                for j in 0..N {
                    let a = a.cap.get_unchecked(j);
                    let b = b.cap.get_unchecked(j);
                    for k in 0..DIGEST_SIZE_U32_WORDS {
                        equal &= *a.get_unchecked(k) == *b.get_unchecked(k);
                    }
                }
            }
        }

        equal
    }
}
