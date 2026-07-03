//! Keccak256 column-major Merkle tree over the `Proth120` field.
//!
//! This is a sibling of [`Blake2sU32MerkleTreeWithCap`](super::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap)
//! that hashes with `keccak256` instead of Blake2s and packs leaf values the
//! way the EVM (Solidity) WHIR verifier expects: each field element is the
//! 16-byte big-endian normal (`u128`) form, a leaf is `keccak256` of the
//! concatenation, and each internal node is `keccak256(left || right)` over the
//! two 32-byte child digests.

use super::keccak256_hash_leafs::{
    keccak256_leaf_hashes_from_cosets, keccak_digest_to_bytes, KECCAK256_DIGEST_SIZE_U32_WORDS,
};
use super::*;
use crate::definitions::{LeafInclusionVerifier, MerkleTreeCap};
use blake2s_u32::AlignedSlice64;
use field::Proth120;
use non_determinism_source::U32WordNonDeterminismSource;
use sha3::{Digest, Keccak256};
use std::alloc::Global;

pub type Digest32 = [u32; KECCAK256_DIGEST_SIZE_U32_WORDS];

#[derive(Clone, Debug)]
pub struct Keccak256MerkleTreeWithCap<A: GoodAllocator = Global> {
    pub cap_size: usize,
    pub leaf_hashes: Vec<Digest32, A>,
    pub node_hashes_enumerated_from_leafs: Vec<Vec<Digest32, A>>,
}

/// `keccak256(left || right)` over the two 32-byte child digests.
#[inline(always)]
fn compress_two_to_one(left: &Digest32, right: &Digest32) -> Digest32 {
    let mut input = [0u8; 64];
    input[..32].copy_from_slice(&keccak_digest_to_bytes(left));
    input[32..].copy_from_slice(&keccak_digest_to_bytes(right));
    let mut out = [0u8; 32];
    out.copy_from_slice(Keccak256::digest(&input).as_slice());
    super::keccak256_hash_leafs::keccak_digest_from_bytes(out)
}

impl<A: GoodAllocator> Keccak256MerkleTreeWithCap<A> {
    /// Build the tree above a set of leaf hashes up to `cap_size` top nodes.
    /// Exposed for the coset-by-coset commitment, which builds each coset's
    /// subtree (cap_size 1) and then a top tree over the per-coset roots.
    pub(crate) fn continue_from_leaf_hashes(
        leaf_hashes: Vec<Digest32, A>,
        cap_size: usize,
        worker: &Worker,
    ) -> Self {
        assert!(leaf_hashes.len().is_power_of_two());
        assert!(cap_size.is_power_of_two());
        debug_assert!(leaf_hashes.len() >= cap_size);

        let tree_depth = leaf_hashes.len().trailing_zeros();
        let layers_to_skip = cap_size.trailing_zeros();
        let num_layers_to_construct = tree_depth - layers_to_skip;

        if num_layers_to_construct == 0 {
            assert_eq!(cap_size, leaf_hashes.len());
            return Self {
                cap_size,
                leaf_hashes,
                node_hashes_enumerated_from_leafs: Vec::new(),
            };
        }

        let mut previous = &leaf_hashes[..];
        let mut node_hashes_enumerated_from_leafs =
            Vec::with_capacity(num_layers_to_construct as usize);
        for _ in 0..num_layers_to_construct {
            let next_layer_len = previous.len() / 2;
            debug_assert!(next_layer_len > 0);
            debug_assert!(next_layer_len.is_power_of_two());
            let mut new_layer_node_hashes: Vec<Digest32, A> =
                Vec::with_capacity_in(next_layer_len, A::default());

            unsafe {
                worker.scope(next_layer_len, |scope, geometry| {
                    let mut dst = &mut new_layer_node_hashes.spare_capacity_mut()[..next_layer_len];
                    let mut src = previous;
                    for thread_idx in 0..geometry.len() {
                        let chunk_size = geometry.get_chunk_size(thread_idx);

                        let (dst_chunk, rest) = dst.split_at_mut_unchecked(chunk_size);
                        dst = rest;
                        let (src_chunk, rest) = src.split_at_unchecked(chunk_size * 2);
                        src = rest;

                        Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                            for (i, slot) in dst_chunk.iter_mut().enumerate() {
                                let left = &src_chunk[2 * i];
                                let right = &src_chunk[2 * i + 1];
                                slot.write(compress_two_to_one(left, right));
                            }
                        });
                    }
                });

                new_layer_node_hashes.set_len(next_layer_len)
            };

            node_hashes_enumerated_from_leafs.push(new_layer_node_hashes);
            previous = node_hashes_enumerated_from_leafs.last().unwrap();
        }

        debug_assert_eq!(previous.len(), cap_size);

        Self {
            cap_size,
            leaf_hashes,
            node_hashes_enumerated_from_leafs,
        }
    }
}

impl<B: GoodAllocator> ColumnMajorMerkleTreeConstructor<Proth120>
    for Keccak256MerkleTreeWithCap<B>
{
    type Verifier = Keccak256LeafInclusionVerifier;

    fn dummy() -> Self {
        Keccak256MerkleTreeWithCap {
            cap_size: 0,
            leaf_hashes: Vec::new_in(B::default()),
            node_hashes_enumerated_from_leafs: vec![],
        }
    }

    fn get_cap(&self) -> MerkleTreeCapVarLength {
        let output = if let Some(cap) = self.node_hashes_enumerated_from_leafs.last() {
            let mut result = Vec::new();
            result.extend_from_slice(cap);
            result
        } else {
            let mut result = Vec::new();
            result.extend_from_slice(&self.leaf_hashes);
            result
        };

        MerkleTreeCapVarLength { cap: output }
    }

    fn get_proof<C: GoodAllocator>(
        &self,
        idx: usize,
    ) -> (
        [u32; DIGEST_SIZE_U32_WORDS],
        Vec<[u32; DIGEST_SIZE_U32_WORDS], C>,
    ) {
        let depth = self.node_hashes_enumerated_from_leafs.len();
        let mut result = Vec::with_capacity_in(depth, C::default());
        let mut idx = idx;
        let this_el_leaf_hash = self.leaf_hashes[idx];
        for i in 0..depth {
            let pair_idx = idx ^ 1;
            let proof_element = if i == 0 {
                self.leaf_hashes[pair_idx]
            } else {
                self.node_hashes_enumerated_from_leafs[i - 1][pair_idx]
            };

            result.push(proof_element);
            idx >>= 1;
        }

        (this_el_leaf_hash, result)
    }

    fn construct_from_cosets<E: FieldExtension<Proth120>, A: GoodAllocator>(
        trace: &[&[&[E]]],
        combine_by: usize,
        cap_size: usize,
        bitreverse_evaluations: bool,
        bitreverse_cosets: bool,
        bitreverse_leaf_hashes: bool,
        worker: &Worker,
    ) -> Self
    where
        [(); E::DEGREE]: Sized,
    {
        let leaf_hashes = keccak256_leaf_hashes_from_cosets::<E, A, B>(
            trace,
            combine_by,
            bitreverse_evaluations,
            bitreverse_cosets,
            bitreverse_leaf_hashes,
            worker,
        );

        Self::continue_from_leaf_hashes(leaf_hashes, cap_size, worker)
    }

    fn build_over_leaf_hashes(
        leaf_hashes: Vec<[u32; DIGEST_SIZE_U32_WORDS]>,
        cap_size: usize,
        worker: &Worker,
    ) -> Self {
        let mut v: Vec<Digest32, B> = Vec::with_capacity_in(leaf_hashes.len(), B::default());
        v.extend(leaf_hashes);
        Self::continue_from_leaf_hashes(v, cap_size, worker)
    }
}

/// `keccak256` of a byte slice.
#[inline(always)]
fn keccak256_bytes(input: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    out.copy_from_slice(Keccak256::digest(input).as_slice());
    out
}

/// Encode `Proth120` leaf values into the `u32`-word `leaf_encoding` format
/// consumed by [`Keccak256LeafInclusionVerifier::verify_leaf_inclusion`].
///
/// Each value contributes the four big-endian `u32` words of its 16-byte
/// big-endian `u128` normal form, so that reconstructing the bytes
/// (`u32::to_be_bytes` per word) yields exactly the leaf preimage that the tree
/// (and the EVM verifier) hashes.
pub fn keccak_leaf_encoding_words(values: &[Proth120]) -> Vec<u32> {
    let mut words = Vec::with_capacity(values.len() * 4);
    for v in values.iter() {
        let be16 = v.to_u128().to_be_bytes();
        for chunk in be16.chunks_exact(4) {
            words.push(u32::from_be_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]));
        }
    }
    words
}

/// [`LeafInclusionVerifier`] for the Keccak256 tree.
///
/// Merkle-path verification for this tree ultimately runs in the EVM (Solidity)
/// WHIR verifier; the in-circuit RISC-V verifier is Blake2s-only. This host-side
/// implementation reproduces the EVM's Keccak256 path check so the tree can be
/// exercised and validated locally:
/// - the leaf hash is `keccak256` of the leaf preimage (the concatenated 16-byte
///   big-endian `u128` values, supplied via `leaf_encoding`),
/// - each level compresses `keccak256(left || right)` over two 32-byte digests,
///   ordered by the index bit,
/// - the reconstructed digest is compared against `merkle_cap[coset][index]`.
///
/// It allocates and uses `sha3`, so it is only compiled with the `prover`
/// feature (host builds), never in the `no_std` in-circuit verifier.
#[derive(Debug)]
pub struct Keccak256LeafInclusionVerifier;

impl LeafInclusionVerifier for Keccak256LeafInclusionVerifier {
    #[inline(always)]
    fn new() -> Self {
        Self
    }

    unsafe fn verify_leaf_inclusion<
        I: U32WordNonDeterminismSource,
        const CAP_SIZE: usize,
        const NUM_COSETS: usize,
    >(
        &mut self,
        coset_index: u32,
        leaf_index: u32,
        depth: usize,
        leaf_encoding: &AlignedSlice64<u32>,
        merkle_cap: &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
        nd_source: &mut I,
    ) -> bool {
        // Leaf hash: keccak256 over the preimage bytes. Every `u32` word
        // contributes its four big-endian bytes, so the preimage equals the
        // concatenated 16-byte big-endian `u128` encodings the tree hashes.
        let words = core::slice::from_raw_parts(leaf_encoding.as_ptr(), leaf_encoding.len());
        let mut preimage = Vec::with_capacity(words.len() * 4);
        for w in words.iter() {
            preimage.extend_from_slice(&w.to_be_bytes());
        }
        let mut h =
            super::keccak256_hash_leafs::keccak_digest_from_bytes(keccak256_bytes(&preimage));

        let mut index = leaf_index as usize;
        for _ in 0..depth {
            // Read the sibling digest: 8 unstructured `u32` words.
            let mut sibling: Digest32 = [0u32; KECCAK256_DIGEST_SIZE_U32_WORDS];
            for s in sibling.iter_mut() {
                *s = nd_source.read_word();
            }

            let mut input = [0u8; 64];
            if index & 1 == 0 {
                // current node is the left child
                input[..32].copy_from_slice(&keccak_digest_to_bytes(&h));
                input[32..].copy_from_slice(&keccak_digest_to_bytes(&sibling));
            } else {
                input[..32].copy_from_slice(&keccak_digest_to_bytes(&sibling));
                input[32..].copy_from_slice(&keccak_digest_to_bytes(&h));
            }
            h = super::keccak256_hash_leafs::keccak_digest_from_bytes(keccak256_bytes(&input));
            index >>= 1;
        }

        // `index` now selects the cap entry (the top `log2(CAP_SIZE)` bits).
        let cap_entry = merkle_cap
            .get_unchecked(coset_index as usize)
            .cap
            .get_unchecked(index);
        h == *cap_entry
    }
}

#[cfg(test)]
mod test {
    use super::super::keccak256_hash_leafs::{keccak_digest_from_bytes, keccak_digest_to_bytes};
    use super::*;
    use field::PrimeField;

    fn keccak(bytes: &[u8]) -> [u8; 32] {
        let mut out = [0u8; 32];
        out.copy_from_slice(Keccak256::digest(bytes).as_slice());
        out
    }

    #[test]
    fn digest_byte_convention_is_be_and_roundtrips() {
        // keccak256("") is a known vector.
        let empty = keccak(&[]);
        assert_eq!(
            hex_lower(&empty),
            "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
        );
        // words -> bytes -> words round-trips, and to_be_bytes reproduces the raw digest.
        let words = keccak_digest_from_bytes(empty);
        assert_eq!(keccak_digest_to_bytes(&words), empty);
    }

    fn hex_lower(bytes: &[u8]) -> String {
        let mut s = String::with_capacity(bytes.len() * 2);
        for b in bytes {
            s.push_str(&format!("{:02x}", b));
        }
        s
    }

    #[test]
    fn leaf_format_and_path_match_evm_expectations() {
        let worker = Worker::new_with_num_threads(1);
        const NUM_COLUMNS: usize = 3;
        const TRACE_LEN: usize = 8;
        const COMBINE_BY: usize = 1;
        const CAP_SIZE: usize = 1;

        // Column-major data; use some large values to exercise full 16-byte BE.
        let cols: Vec<Vec<Proth120>> = (0..NUM_COLUMNS)
            .map(|c| {
                (0..TRACE_LEN)
                    .map(|r| {
                        let v =
                            (Proth120::ORDER - 1 - ((c * TRACE_LEN + r) as u128)) % Proth120::ORDER;
                        Proth120::new(v)
                    })
                    .collect()
            })
            .collect();
        let col_refs: Vec<&[Proth120]> = cols.iter().map(|c| c.as_slice()).collect();
        let coset: &[&[Proth120]] = &col_refs;
        let trace: &[&[&[Proth120]]] = &[coset];

        let tree = <Keccak256MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<
            Proth120,
        >>::construct_from_cosets::<Proth120, Global>(
            trace, COMBINE_BY, CAP_SIZE, /* bitreverse_evaluations */ true,
            /* bitreverse_cosets */ false, /* bitreverse_leaf_hashes */ false, &worker,
        );

        // --- EVM leaf format: leaf[row] = keccak256( concat_c BE16(col_c[row]) ) ---
        assert_eq!(tree.leaf_hashes.len(), TRACE_LEN);
        for row in 0..TRACE_LEN {
            let mut preimage = Vec::new();
            for c in 0..NUM_COLUMNS {
                preimage.extend_from_slice(&cols[c][row].to_u128().to_be_bytes());
            }
            // preimage is NUM_COLUMNS * 16 bytes, exactly the EVM packing.
            assert_eq!(preimage.len(), NUM_COLUMNS * 16);
            let expected = keccak(&preimage);
            assert_eq!(
                keccak_digest_to_bytes(&tree.leaf_hashes[row]),
                expected,
                "leaf {row} does not match keccak256 of BE-packed u128 values"
            );
        }

        // --- Merkle path reconstruction matches the cap (node = keccak(left||right)) ---
        let cap = tree.get_cap();
        assert_eq!(cap.cap.len(), CAP_SIZE);
        let root = cap.cap[0];

        for idx in 0..TRACE_LEN {
            let (leaf_hash, path) = tree.get_proof::<Global>(idx);
            let mut h = leaf_hash;
            let mut i = idx;
            for sibling in path.iter() {
                let mut input = [0u8; 64];
                if i & 1 == 0 {
                    // current is the left child
                    input[..32].copy_from_slice(&keccak_digest_to_bytes(&h));
                    input[32..].copy_from_slice(&keccak_digest_to_bytes(sibling));
                } else {
                    input[..32].copy_from_slice(&keccak_digest_to_bytes(sibling));
                    input[32..].copy_from_slice(&keccak_digest_to_bytes(&h));
                }
                h = keccak_digest_from_bytes(keccak(&input));
                i >>= 1;
            }
            assert_eq!(h, root, "reconstructed root for leaf {idx} != cap");
        }
    }

    #[test]
    fn keccak256_leaf_inclusion_verifier_matches_tree() {
        use blake2s_u32::{AlignedArray64, AlignedSlice64};

        let worker = Worker::new_with_num_threads(1);
        const NUM_COLUMNS: usize = 3;
        const TRACE_LEN: usize = 8;
        const COMBINE_BY: usize = 1;
        const CAP_SIZE: usize = 2;
        // combine_by == 1 => one value per column per leaf, 4 words per value.
        const LEAF_WORDS: usize = NUM_COLUMNS * 4;

        let cols: Vec<Vec<Proth120>> = (0..NUM_COLUMNS)
            .map(|c| {
                (0..TRACE_LEN)
                    .map(|r| Proth120::new((7 * (c * TRACE_LEN + r) as u128 + 1) % Proth120::ORDER))
                    .collect()
            })
            .collect();
        let col_refs: Vec<&[Proth120]> = cols.iter().map(|c| c.as_slice()).collect();
        let coset: &[&[Proth120]] = &col_refs;
        let trace: &[&[&[Proth120]]] = &[coset];

        let tree = <Keccak256MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<
            Proth120,
        >>::construct_from_cosets::<Proth120, Global>(
            trace, COMBINE_BY, CAP_SIZE, true, false, false, &worker,
        );

        let merkle_cap: [MerkleTreeCap<CAP_SIZE>; 1] =
            [tree.get_cap().into_fixed_holder::<CAP_SIZE>()];
        let depth = tree.node_hashes_enumerated_from_leafs.len();

        let build_leaf_encoding = |words: &[u32]| -> AlignedArray64<u32, LEAF_WORDS> {
            let mut aligned = AlignedArray64::<u32, LEAF_WORDS>::from_value(0u32);
            aligned.deref_mut_impl().copy_from_slice(words);
            aligned
        };

        for idx in 0..TRACE_LEN {
            // For combine_by == 1 (offsets == [0]) leaf `idx` is exactly the
            // `idx`-th row across all columns.
            let leaf_values: Vec<Proth120> = (0..NUM_COLUMNS).map(|c| cols[c][idx]).collect();
            let words = keccak_leaf_encoding_words(&leaf_values);
            assert_eq!(words.len(), LEAF_WORDS);
            let aligned = build_leaf_encoding(&words);
            let leaf_encoding: &AlignedSlice64<u32> =
                unsafe { AlignedSlice64::from_raw_parts(aligned.as_ptr(), LEAF_WORDS) };

            // Feed the proof's sibling digests as the non-determinism source.
            let (_leaf_hash, path) = tree.get_proof::<Global>(idx);
            let mut sibling_words: Vec<u32> = Vec::with_capacity(path.len() * 8);
            for sib in path.iter() {
                sibling_words.extend_from_slice(sib);
            }
            let mut nd = sibling_words.into_iter();

            let mut verifier = Keccak256LeafInclusionVerifier::new();
            let ok = unsafe {
                verifier.verify_leaf_inclusion::<_, CAP_SIZE, 1>(
                    0,
                    idx as u32,
                    depth,
                    leaf_encoding,
                    &merkle_cap,
                    &mut nd,
                )
            };
            assert!(
                ok,
                "verify_leaf_inclusion should accept the correct leaf {idx}"
            );

            // Negative: a corrupted leaf value must be rejected.
            let mut bad_values = leaf_values.clone();
            bad_values[0] = Proth120::new((bad_values[0].to_u128() + 1) % Proth120::ORDER);
            let bad_words = keccak_leaf_encoding_words(&bad_values);
            let bad_aligned = build_leaf_encoding(&bad_words);
            let bad_leaf_encoding: &AlignedSlice64<u32> =
                unsafe { AlignedSlice64::from_raw_parts(bad_aligned.as_ptr(), LEAF_WORDS) };
            let mut nd_bad = {
                let mut v: Vec<u32> = Vec::with_capacity(path.len() * 8);
                for sib in path.iter() {
                    v.extend_from_slice(sib);
                }
                v.into_iter()
            };
            let bad_ok = unsafe {
                verifier.verify_leaf_inclusion::<_, CAP_SIZE, 1>(
                    0,
                    idx as u32,
                    depth,
                    bad_leaf_encoding,
                    &merkle_cap,
                    &mut nd_bad,
                )
            };
            assert!(
                !bad_ok,
                "verify_leaf_inclusion must reject a corrupted leaf {idx}"
            );
        }
    }
}
