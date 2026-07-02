//! Keccak256 leaf hashing over the `Proth120` field, matching the leaf format
//! expected by the EVM (Solidity) WHIR verifier.
//!
//! Each `Proth120` value is encoded as the 16-byte big-endian representation of
//! its normal (non-Montgomery) `u128` form. A leaf's preimage is the
//! concatenation of these 16-byte encodings for every field element in the
//! leaf, and the leaf hash is `keccak256` of that preimage. This is exactly the
//! byte string the EVM verifier hashes (it packs two 128-bit values per 32-byte
//! word and takes `keccak256` over the packed words).

use super::*;
use crate::gkr::whir::offsets_vec_for_leaf_construction;
use crate::utils::extension_field_into_base_coeffs;
use fft::bitreverse_enumeration_inplace;
use field::Proth120;
use sha3::{Digest, Keccak256};

/// A Keccak256 digest is 256 bits == 8 `u32` words (same width as the Blake2s
/// digest used elsewhere, so it fits the shared `DIGEST_SIZE_U32_WORDS`).
pub const KECCAK256_DIGEST_SIZE_U32_WORDS: usize = 8;

const _: () = assert!(KECCAK256_DIGEST_SIZE_U32_WORDS == DIGEST_SIZE_U32_WORDS);

/// Pack a raw 32-byte Keccak digest into 8 `u32` words, word `i` holding the
/// big-endian value of digest bytes `[4i, 4i+4)`. This mirrors the EVM
/// `bytes32` view of the digest (`to_be_bytes` of the words, concatenated,
/// reproduces the raw digest), so serialized proofs match the Solidity verifier.
#[inline(always)]
pub(crate) fn keccak_digest_from_bytes(bytes: [u8; 32]) -> [u32; KECCAK256_DIGEST_SIZE_U32_WORDS] {
    core::array::from_fn(|i| {
        u32::from_be_bytes([bytes[4 * i], bytes[4 * i + 1], bytes[4 * i + 2], bytes[4 * i + 3]])
    })
}

/// Inverse of [`keccak_digest_from_bytes`].
#[inline(always)]
pub(crate) fn keccak_digest_to_bytes(words: &[u32; KECCAK256_DIGEST_SIZE_U32_WORDS]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut i = 0;
    while i < KECCAK256_DIGEST_SIZE_U32_WORDS {
        out[4 * i..4 * i + 4].copy_from_slice(&words[i].to_be_bytes());
        i += 1;
    }
    out
}

/// Encode a single `Proth120` element into its 16-byte big-endian normal form
/// and append it to `dst`.
#[inline(always)]
pub(crate) fn encode_proth120_be_into(el: &Proth120, dst: &mut Vec<u8>) {
    dst.extend_from_slice(&el.to_u128().to_be_bytes());
}

pub fn keccak256_leaf_hashes_from_cosets<E, A, B>(
    trace: &[&[&[E]]],
    combine_by: usize,
    bitreverse_evaluations: bool,
    bitreverse_cosets: bool,
    bitreverse_leaf_hashes: bool,
    worker: &Worker,
) -> Vec<[u32; KECCAK256_DIGEST_SIZE_U32_WORDS], B>
where
    E: FieldExtension<Proth120>,
    A: GoodAllocator,
    B: GoodAllocator,
    [(); E::DEGREE]: Sized,
{
    let num_cosets = trace.len();
    let num_columns = trace[0].len();
    let trace_len = trace[0][0].len();
    assert!(combine_by.is_power_of_two());
    assert_eq!(trace_len % combine_by, 0);

    for coset in trace.iter() {
        assert_eq!(coset.len(), num_columns);
        for column in coset.iter() {
            assert_eq!(column.len(), trace_len);
        }
    }

    let coset_tree_size = trace_len / combine_by;
    assert!(coset_tree_size.is_power_of_two());
    let tree_size = num_cosets * coset_tree_size;
    assert!(tree_size.is_power_of_two());

    if bitreverse_evaluations == false {
        // The Blake2s variant only implements the bit-reversed evaluation
        // layout; mirror that here.
        todo!("non-bit-reversed evaluation layout is not implemented");
    }

    // Physical coset `k` in the flat tree is sourced from `trace[coset_indexes[k]]`.
    let mut coset_indexes: Vec<usize> = (0..num_cosets).collect();
    if bitreverse_cosets {
        bitreverse_enumeration_inplace(&mut coset_indexes);
    }
    // Offsets of the `combine_by` evaluations that make up one leaf, in the
    // bit-reversed layout.
    let offsets = offsets_vec_for_leaf_construction(trace_len, combine_by);

    let leaf_width_bytes = num_columns * offsets.len() * E::DEGREE * 16;

    let mut leaf_hashes: Vec<[u32; KECCAK256_DIGEST_SIZE_U32_WORDS], B> =
        Vec::with_capacity_in(tree_size, B::default());

    let offsets_ref = &offsets[..];
    let coset_indexes_ref = &coset_indexes[..];

    unsafe {
        worker.scope(tree_size, |scope, geometry| {
            let mut dst = &mut leaf_hashes.spare_capacity_mut()[..tree_size];
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                let (dst_chunk, rest) = dst.split_at_mut_unchecked(chunk_size);
                dst = rest;

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let mut preimage: Vec<u8> = Vec::with_capacity(leaf_width_bytes);
                    for (local, slot) in dst_chunk.iter_mut().enumerate() {
                        let flat_index = chunk_start + local;
                        let coset_slot = flat_index / coset_tree_size;
                        let row = flat_index % coset_tree_size;
                        let coset = &trace[coset_indexes_ref[coset_slot]];

                        preimage.clear();
                        for column in coset.iter() {
                            for offset in offsets_ref.iter() {
                                let el = column[row + *offset];
                                let coeffs = extension_field_into_base_coeffs::<Proth120, E>(el);
                                for c in coeffs.iter() {
                                    encode_proth120_be_into(c, &mut preimage);
                                }
                            }
                        }
                        debug_assert_eq!(preimage.len(), leaf_width_bytes);

                        let mut digest = [0u8; 32];
                        digest.copy_from_slice(Keccak256::digest(&preimage).as_slice());
                        slot.write(keccak_digest_from_bytes(digest));
                    }
                });
            }
        });

        leaf_hashes.set_len(tree_size);
    }

    if bitreverse_leaf_hashes {
        bitreverse_enumeration_inplace(&mut leaf_hashes);
    }

    leaf_hashes
}
