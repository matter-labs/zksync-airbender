//! A very simple on-disk / mmap format for the column-major Merkle trees
//! ([`Blake2sU32MerkleTreeWithCap`](super::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap),
//! [`Keccak256MerkleTreeWithCap`](super::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap)).
//!
//! Both trees share the same shape — a leaf-hash layer plus internal node layers
//! of `[u32; DIGEST_SIZE_U32_WORDS]` digests — and their [`PathQueriable`] logic
//! only ever *reads* stored digests (it never re-hashes). So one field-agnostic
//! reader, [`MmapMerkleTreePath`], serves inclusion proofs for either tree.
//!
//! ## Format
//!
//! A small fixed header, then a concatenation of digests: the cap (root) block,
//! then the leaf hashes, then the internal layer hashes bottom-up:
//!
//! ```text
//! [ header (24 bytes) ]
//! [ cap:      cap_size            digests ]   // get_cap()
//! [ leaves:   num_leaves          digests ]   // depth-0 siblings
//! [ layer 1:  num_leaves / 2      digests ]   // depth-1 siblings
//! [ layer 2:  num_leaves / 4      digests ]
//! ...
//! [ layer k-1: 2 * cap_size       digests ]   // top internal siblings below cap
//! ```
//!
//! `k = log2(num_leaves) - log2(cap_size)` is the tree depth. The cap layer
//! (`layer k`) is stored once, up front, and is never needed as a sibling, so the
//! internal blocks stop at `layer k-1`. Each digest is written as
//! `DIGEST_SIZE_U32_WORDS` little-endian `u32` words (deterministic across hosts).
//!
//! The layout is intentionally minimal; a richer, self-describing variant can be
//! added later without touching the trait surface.

use super::{MerkleTreeCapVarLength, PathQueriable};
use crate::definitions::DIGEST_SIZE_U32_WORDS;
use fft::{bitreverse_index, GoodAllocator};
use field::PrimeField;
use std::io::Write;
use std::path::PathBuf;

/// Magic marker ("MTR1") identifying the format.
pub const MERKLE_DISK_MAGIC: u32 = u32::from_le_bytes(*b"MTR1");

/// Header size in bytes: magic(4) + digest_words(4) + num_leaves(8) + cap_size(8).
pub const HEADER_BYTES: usize = 24;

/// Bytes occupied by a single digest.
pub const DIGEST_BYTES: usize = DIGEST_SIZE_U32_WORDS * core::mem::size_of::<u32>();

pub type Digest = [u32; DIGEST_SIZE_U32_WORDS];

#[inline]
fn write_digest<W: Write>(out: &mut W, d: &Digest) -> std::io::Result<()> {
    let mut buf = [0u8; DIGEST_BYTES];
    for (i, w) in d.iter().enumerate() {
        buf[i * 4..i * 4 + 4].copy_from_slice(&w.to_le_bytes());
    }
    out.write_all(&buf)
}

#[inline]
fn digest_from_le_bytes(bytes: &[u8]) -> Digest {
    debug_assert_eq!(bytes.len(), DIGEST_BYTES);
    core::array::from_fn(|i| {
        let b = &bytes[i * 4..i * 4 + 4];
        u32::from_le_bytes([b[0], b[1], b[2], b[3]])
    })
}

/// Number of internal node layers below the cap that are stored as sibling blocks.
/// Equals `depth - 1` for `depth >= 1`, and `0` for a cap-only tree.
#[inline]
fn num_internal_layers(num_leaves: usize, cap_size: usize) -> usize {
    let depth = num_leaves.trailing_zeros() - cap_size.trailing_zeros();
    depth.saturating_sub(1) as usize
}

/// Serialize a tree given its layers into `out` (any [`std::io::Write`] — an
/// in-memory `Vec<u8>`, a `BufWriter<File>`, etc.). `cap` is `get_cap().cap`;
/// `leaf_hashes` is the leaf layer; `internal_layers` are the node layers strictly
/// BELOW the cap (`L1 .. L_{depth-1}`, bottom-up), i.e.
/// `node_hashes_enumerated_from_leafs` without its last (cap) layer. Writes the
/// byte image described in the module docs.
pub fn serialize_layers<W: Write>(
    out: &mut W,
    num_leaves: usize,
    cap_size: usize,
    cap: &[Digest],
    leaf_hashes: &[Digest],
    internal_layers: &[&[Digest]],
) -> std::io::Result<()> {
    assert!(num_leaves.is_power_of_two());
    assert!(cap_size.is_power_of_two());
    assert_eq!(cap.len(), cap_size, "cap block size mismatch");
    assert_eq!(leaf_hashes.len(), num_leaves, "leaf block size mismatch");
    assert_eq!(
        internal_layers.len(),
        num_internal_layers(num_leaves, cap_size),
        "internal layer count mismatch"
    );

    out.write_all(&MERKLE_DISK_MAGIC.to_le_bytes())?;
    out.write_all(&(DIGEST_SIZE_U32_WORDS as u32).to_le_bytes())?;
    out.write_all(&(num_leaves as u64).to_le_bytes())?;
    out.write_all(&(cap_size as u64).to_le_bytes())?;

    for d in cap.iter() {
        write_digest(out, d)?;
    }
    for d in leaf_hashes.iter() {
        write_digest(out, d)?;
    }
    for (i, layer) in internal_layers.iter().enumerate() {
        assert_eq!(
            layer.len(),
            num_leaves >> (i + 1),
            "internal layer {i} has unexpected length"
        );
        for d in layer.iter() {
            write_digest(out, d)?;
        }
    }

    Ok(())
}

/// Byte length of the serialized image for a tree of the given dimensions (header
/// + cap + leaves + internal layers). Handy for pre-sizing a `Vec<u8>` sink.
pub fn serialized_len(num_leaves: usize, cap_size: usize) -> usize {
    let internal: usize = (1..=num_internal_layers(num_leaves, cap_size))
        .map(|i| num_leaves >> i)
        .sum();
    HEADER_BYTES + (cap_size + num_leaves + internal) * DIGEST_BYTES
}

/// Serialize a tree from its in-memory fields (as held by both
/// `Blake2sU32MerkleTreeWithCap` and `Keccak256MerkleTreeWithCap`) into `out`:
/// `node_layers` is `node_hashes_enumerated_from_leafs` (bottom-up, last layer =
/// cap). Handles the cap-only tree (`node_layers` empty ⇒ cap == leaves).
pub fn serialize_tree<A: GoodAllocator, W: Write>(
    out: &mut W,
    cap_size: usize,
    leaf_hashes: &[Digest],
    node_layers: &[Vec<Digest, A>],
) -> std::io::Result<()> {
    let num_leaves = leaf_hashes.len();
    let cap: Vec<Digest> = match node_layers.last() {
        Some(last) => last.to_vec(),
        None => leaf_hashes.to_vec(),
    };
    let internal: Vec<&[Digest]> = if node_layers.is_empty() {
        Vec::new()
    } else {
        node_layers[..node_layers.len() - 1]
            .iter()
            .map(|v| &v[..])
            .collect()
    };
    serialize_layers(out, num_leaves, cap_size, &cap, leaf_hashes, &internal)
}

/// A [`PathQueriable`] backed by an mmap'd (or otherwise borrowed) byte image in the
/// [`serialize_layers`] format. Reads digests directly out of `bytes`; holds no
/// owned digest data of its own.
#[derive(Clone, Debug)]
pub struct MmapMerkleTreePath<'a> {
    bytes: &'a [u8],
    num_leaves: usize,
    cap_size: usize,
    /// Tree depth `k = log2(num_leaves) - log2(cap_size)`.
    depth: usize,
    /// Byte offset of the cap block.
    cap_offset: usize,
    /// Byte offset of the leaf-hash block.
    leaf_offset: usize,
    /// Byte offset of each internal layer `L1 .. L_{depth-1}` (index `i` = `L_{i+1}`).
    internal_offsets: Vec<usize>,
}

impl<'a> MmapMerkleTreePath<'a> {
    /// Parse the header and index the digest blocks. Panics if the header is
    /// malformed, the digest width differs, or `bytes` is too short for the
    /// declared dimensions.
    pub fn from_bytes(bytes: &'a [u8]) -> Self {
        assert!(
            bytes.len() >= HEADER_BYTES,
            "on-disk merkle image shorter than header"
        );
        let magic = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        assert_eq!(magic, MERKLE_DISK_MAGIC, "bad on-disk merkle magic");
        let digest_words = u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]) as usize;
        assert_eq!(
            digest_words, DIGEST_SIZE_U32_WORDS,
            "on-disk digest width mismatch"
        );
        let num_leaves =
            u64::from_le_bytes(bytes[8..16].try_into().unwrap()) as usize;
        let cap_size = u64::from_le_bytes(bytes[16..24].try_into().unwrap()) as usize;
        assert!(num_leaves.is_power_of_two());
        assert!(cap_size.is_power_of_two());
        assert!(cap_size <= num_leaves);

        let depth = (num_leaves.trailing_zeros() - cap_size.trailing_zeros()) as usize;

        let cap_offset = HEADER_BYTES;
        let leaf_offset = cap_offset + cap_size * DIGEST_BYTES;
        let mut internal_offsets = Vec::with_capacity(num_internal_layers(num_leaves, cap_size));
        let mut off = leaf_offset + num_leaves * DIGEST_BYTES;
        for i in 0..num_internal_layers(num_leaves, cap_size) {
            internal_offsets.push(off);
            off += (num_leaves >> (i + 1)) * DIGEST_BYTES;
        }
        assert!(
            bytes.len() >= off,
            "on-disk merkle image truncated: need {off} bytes, have {}",
            bytes.len()
        );

        Self {
            bytes,
            num_leaves,
            cap_size,
            depth,
            cap_offset,
            leaf_offset,
            internal_offsets,
        }
    }

    #[inline]
    fn digest_at(&self, block_offset: usize, index: usize) -> Digest {
        let start = block_offset + index * DIGEST_BYTES;
        digest_from_le_bytes(&self.bytes[start..start + DIGEST_BYTES])
    }

    #[inline]
    fn leaf(&self, index: usize) -> Digest {
        debug_assert!(index < self.num_leaves);
        self.digest_at(self.leaf_offset, index)
    }

    /// Sibling on internal layer `L_{layer+1}` (0-based `layer` in `[0, depth-2]`).
    #[inline]
    fn internal(&self, layer: usize, index: usize) -> Digest {
        self.digest_at(self.internal_offsets[layer], index)
    }
}

impl<'a> MmapMerkleTreePath<'a> {
    /// The borrowed byte image this reader was built over.
    #[inline]
    pub fn as_bytes(&self) -> &'a [u8] {
        self.bytes
    }
}

impl<'a, F: PrimeField> PathQueriable<F> for MmapMerkleTreePath<'a> {
    fn get_cap(&self) -> MerkleTreeCapVarLength {
        let cap = (0..self.cap_size)
            .map(|i| self.digest_at(self.cap_offset, i))
            .collect();
        MerkleTreeCapVarLength { cap }
    }

    fn get_proof<C: GoodAllocator>(
        &self,
        idx: usize,
    ) -> (
        [u32; DIGEST_SIZE_U32_WORDS],
        Vec<[u32; DIGEST_SIZE_U32_WORDS], C>,
    ) {
        // Mirrors the in-memory trees' `get_proof`: for level 0 the sibling comes
        // from the leaf layer, for level `i > 0` from internal layer `L_i`.
        let mut result = Vec::with_capacity_in(self.depth, C::default());
        let mut idx = idx;
        let this_el_leaf_hash = self.leaf(idx);
        for i in 0..self.depth {
            let pair_idx = idx ^ 1;
            let proof_element = if i == 0 {
                self.leaf(pair_idx)
            } else {
                self.internal(i - 1, pair_idx)
            };
            result.push(proof_element);
            idx >>= 1;
        }
        (this_el_leaf_hash, result)
    }
}

// ============================================================================
// Second on-disk tree layout: per-coset subtrees + a top-tree over their roots.
// ============================================================================

/// File path for the per-coset subtree of NATURAL coset `i` (coset 0 = main domain).
pub fn subtree_file_path(prefix: &str, coset_index: usize) -> PathBuf {
    PathBuf::from(format!("{prefix}.subtree_{coset_index:04}.tree"))
}

/// File path for the top-tree over the per-coset subtree roots.
pub fn top_tree_file_path(prefix: &str) -> PathBuf {
    PathBuf::from(format!("{prefix}.toptree.tree"))
}

/// A [`PathQueriable`] assembled from one subtree file per coset plus a small
/// top-tree over their roots — the "second" on-disk tree layout. It serves an
/// inclusion path as the within-coset subtree path stitched to the top-tree path,
/// which is byte-identical to the monolithic tree's `get_proof` (the same
/// equivalence the coset-by-coset commitment relies on), but the subtrees can be
/// prepared and stored one coset at a time, so a large packed setup's tree never
/// has to be materialized whole.
pub struct OnDiskCosetTreePath<'a> {
    /// One subtree per NATURAL coset (each built with cap_size 1).
    subtrees: Vec<MmapMerkleTreePath<'a>>,
    /// Top tree over the per-coset roots (leaves in physical, bit-reversed order).
    top_tree: MmapMerkleTreePath<'a>,
    /// Leaves per coset subtree (`2^coset_size_log2 / values_per_leaf`).
    coset_tree_size: usize,
    cosets_log2: u32,
}

impl<'a> OnDiskCosetTreePath<'a> {
    /// Assemble from already-mapped subtree images (NATURAL coset order) and the
    /// top-tree image. `coset_tree_size` is the number of leaves in each subtree.
    pub fn from_parts(
        subtree_bytes: Vec<&'a [u8]>,
        top_tree_bytes: &'a [u8],
        coset_tree_size: usize,
    ) -> Self {
        assert!(!subtree_bytes.is_empty());
        assert!(subtree_bytes.len().is_power_of_two());
        let cosets_log2 = subtree_bytes.len().trailing_zeros();
        let subtrees = subtree_bytes
            .into_iter()
            .map(MmapMerkleTreePath::from_bytes)
            .collect();
        let top_tree = MmapMerkleTreePath::from_bytes(top_tree_bytes);
        Self {
            subtrees,
            top_tree,
            coset_tree_size,
            cosets_log2,
        }
    }
}

impl<'a, F: PrimeField> PathQueriable<F> for OnDiskCosetTreePath<'a> {
    fn get_cap(&self) -> MerkleTreeCapVarLength {
        PathQueriable::<F>::get_cap(&self.top_tree)
    }

    fn get_proof<C: GoodAllocator>(
        &self,
        idx: usize,
    ) -> (
        [u32; DIGEST_SIZE_U32_WORDS],
        Vec<[u32; DIGEST_SIZE_U32_WORDS], C>,
    ) {
        // The monolithic tree lays cosets out in physical (bit-reversed) order; a
        // leaf index decomposes into (physical coset slot, index within the coset).
        let physical_slot = idx / self.coset_tree_size;
        let internal_index = idx % self.coset_tree_size;
        let natural_coset = bitreverse_index(physical_slot, self.cosets_log2);
        // within-coset path (leaf -> coset root) from that coset's subtree,
        let (leaf, mut path) =
            PathQueriable::<F>::get_proof::<C>(&self.subtrees[natural_coset], internal_index);
        // then coset root -> cap from the top tree.
        let (_root, top_path) = PathQueriable::<F>::get_proof::<C>(&self.top_tree, physical_slot);
        path.extend_from_slice(&top_path);
        (leaf, path)
    }
}

/// The on-disk tree layout backing an on-disk setup commitment: either one
/// monolithic tree file ([`MmapMerkleTreePath`]) or per-coset subtree files plus a
/// top-tree ([`OnDiskCosetTreePath`]). Both serve identical inclusion paths.
pub enum OnDiskTree<'a> {
    Monolithic(MmapMerkleTreePath<'a>),
    CosetSubtrees(OnDiskCosetTreePath<'a>),
}

impl<'a, F: PrimeField> PathQueriable<F> for OnDiskTree<'a> {
    fn get_cap(&self) -> MerkleTreeCapVarLength {
        match self {
            OnDiskTree::Monolithic(t) => PathQueriable::<F>::get_cap(t),
            OnDiskTree::CosetSubtrees(t) => PathQueriable::<F>::get_cap(t),
        }
    }

    fn get_proof<C: GoodAllocator>(
        &self,
        idx: usize,
    ) -> (
        [u32; DIGEST_SIZE_U32_WORDS],
        Vec<[u32; DIGEST_SIZE_U32_WORDS], C>,
    ) {
        match self {
            OnDiskTree::Monolithic(t) => PathQueriable::<F>::get_proof::<C>(t, idx),
            OnDiskTree::CosetSubtrees(t) => PathQueriable::<F>::get_proof::<C>(t, idx),
        }
    }
}

#[cfg(all(test, feature = "prover"))]
mod test {
    use super::*;
    use crate::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
    use crate::merkle_trees::ColumnMajorMerkleTreeConstructor;
    use field::{PrimeField, Proth120};
    use std::alloc::Global;
    use worker::Worker;

    /// Serialize a keccak tree, reparse it from the byte image, and require the
    /// mmap-backed `PathQueriable` to reproduce the in-memory tree's `get_cap` and,
    /// for every leaf, `get_proof` (leaf hash + full sibling path) exactly.
    fn roundtrip(num_columns: usize, trace_len_log2: usize, cap_size: usize) {
        let worker = Worker::new_with_num_threads(2);
        let trace_len = 1usize << trace_len_log2;

        let cols: Vec<Vec<Proth120>> = (0..num_columns)
            .map(|c| {
                (0..trace_len)
                    .map(|r| Proth120::new(((7 * (c * trace_len + r) + 1) as u128) % Proth120::ORDER))
                    .collect()
            })
            .collect();
        let col_refs: Vec<&[Proth120]> = cols.iter().map(|c| c.as_slice()).collect();
        let coset: &[&[Proth120]] = &col_refs;
        let trace: &[&[&[Proth120]]] = &[coset];

        let tree = <Keccak256MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<
            Proth120,
        >>::construct_from_cosets::<Proth120, Global>(
            trace, 1, cap_size, true, false, false, &worker,
        );

        let mut bytes = Vec::new();
        tree.serialize_to_disk_format(&mut bytes).unwrap();
        let disk = <Keccak256MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<
            Proth120,
        >>::disk_path(&bytes);

        assert_eq!(
            PathQueriable::<Proth120>::get_cap(&disk),
            ColumnMajorMerkleTreeConstructor::<Proth120>::get_cap(&tree),
            "cap mismatch (cols={num_columns}, tl={trace_len_log2}, cap={cap_size})"
        );

        for idx in 0..trace_len {
            let (want_leaf, want_path) =
                ColumnMajorMerkleTreeConstructor::<Proth120>::get_proof::<Global>(&tree, idx);
            let (got_leaf, got_path) =
                PathQueriable::<Proth120>::get_proof::<Global>(&disk, idx);
            assert_eq!(got_leaf, want_leaf, "leaf hash @ {idx}");
            assert_eq!(got_path, want_path, "path @ {idx}");
        }
    }

    #[test]
    fn mmap_path_matches_in_memory_tree() {
        roundtrip(3, 8, 1);
        roundtrip(3, 8, 4);
        roundtrip(1, 6, 8);
        roundtrip(5, 10, 2);
    }

    #[test]
    fn mmap_path_cap_equals_all_leaves() {
        // cap_size == num_leaves: depth 0, no internal layers, cap == leaves.
        roundtrip(2, 3, 8);
    }
}
