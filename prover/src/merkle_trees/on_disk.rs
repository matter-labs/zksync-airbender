//! A very simple on-disk / mmap format for the column-major Merkle trees
//! ([`Blake2sU32MerkleTreeWithCap`](super::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap),
//! [`Keccak256MerkleTreeWithCap`](super::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap)).
//!
//! Both trees share the same shape — a leaf-hash layer plus internal node layers
//! of `[u32; DIGEST_SIZE_U32_WORDS]` digests — and their [`PathQueryable`] logic
//! only ever *reads* stored digests (it never re-hashes). So one field-agnostic
//! reader, [`MmapMerkleTree`], serves inclusion proofs for either tree.
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

use super::{
    ColumnMajorMerkleTreeConstructor, CosetColumnsProducer, MerkleTreeCapVarLength, PathQueryable,
};
use crate::definitions::DIGEST_SIZE_U32_WORDS;
use fft::bitreverse_index;
use field::{FieldExtension, PrimeField};
use mmap_io::MemoryMappedFile;
use std::io::Write;
use std::marker::PhantomData;
use std::path::{Path, PathBuf};
use worker::Worker;

fn mmap_io_err(e: impl core::fmt::Debug) -> std::io::Error {
    std::io::Error::other(format!("mmap-io: {e:?}"))
}

/// Which on-disk tree layout an artifact uses: a single monolithic tree file, or
/// per-coset subtree files plus a top-tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OnDiskTreeLayout {
    Monolithic,
    CosetSubtrees,
}

/// Path of the single monolithic tree file under a shared prefix.
pub fn monolithic_tree_file_path(prefix: &str) -> PathBuf {
    PathBuf::from(format!("{prefix}.tree"))
}

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

/// A built tree's digest layers, borrowed and ready for on-disk serialization —
/// the value a [`ColumnMajorMerkleTreeConstructor`](super::ColumnMajorMerkleTreeConstructor)
/// exposes to the (crate-internal) writer used by `write_disk_artifacts`. It is a
/// pure data view: `leaf_hashes` and `internal_layers` borrow the tree, only the
/// small `cap` is owned. There is no standalone public serializer — writing a tree
/// to disk happens only through `write_disk_artifacts`.
pub struct SerializableTreeLayers<'a> {
    num_leaves: usize,
    cap_size: usize,
    cap: Vec<Digest>,
    leaf_hashes: &'a [Digest],
    internal_layers: Vec<&'a [Digest]>,
}

impl<'a> SerializableTreeLayers<'a> {
    /// Write these layers into `out` in the on-disk format. Crate-internal on
    /// purpose: `write_disk_artifacts` is the only intended caller.
    pub(crate) fn write_to<W: Write>(&self, out: &mut W) -> std::io::Result<()> {
        serialize_layers(
            out,
            self.num_leaves,
            self.cap_size,
            &self.cap,
            self.leaf_hashes,
            &self.internal_layers,
        )
    }
}

/// Build a [`SerializableTreeLayers`] from a tree's in-memory fields (as held by
/// both `Blake2sU32MerkleTreeWithCap` and `Keccak256MerkleTreeWithCap`):
/// `node_layers` is `node_hashes_enumerated_from_leafs` as allocator-erased slices
/// (bottom-up, last layer = cap). Handles the cap-only tree (`node_layers` empty ⇒
/// cap == leaves). Taking `&[&[Digest]]` keeps any tree allocator out of the trait
/// surface without this helper being generic over it.
pub fn tree_layers<'a>(
    cap_size: usize,
    leaf_hashes: &'a [Digest],
    node_layers: &[&'a [Digest]],
) -> SerializableTreeLayers<'a> {
    let cap: Vec<Digest> = match node_layers.last() {
        Some(last) => last.to_vec(),
        None => leaf_hashes.to_vec(),
    };
    let internal_layers: Vec<&'a [Digest]> = if node_layers.is_empty() {
        Vec::new()
    } else {
        node_layers[..node_layers.len() - 1].to_vec()
    };
    SerializableTreeLayers {
        num_leaves: leaf_hashes.len(),
        cap_size,
        cap,
        leaf_hashes,
        internal_layers,
    }
}

/// Byte-offset layout of a serialized single-tree image (see module docs), parsed
/// from the 24-byte header. Kept separate from the mapping so a reader can own its
/// `MemoryMappedFile` and re-derive a zero-copy view per access.
#[derive(Clone, Debug)]
struct TreeLayout {
    num_leaves: usize,
    cap_size: usize,
    depth: usize,
    cap_offset: usize,
    leaf_offset: usize,
    /// Byte offset of each internal layer `L1 .. L_{depth-1}` (index `i` = `L_{i+1}`).
    internal_offsets: Vec<usize>,
}

impl TreeLayout {
    fn parse(header: &[u8]) -> Self {
        assert!(
            header.len() >= HEADER_BYTES,
            "on-disk merkle image shorter than header"
        );
        let magic = u32::from_le_bytes([header[0], header[1], header[2], header[3]]);
        assert_eq!(magic, MERKLE_DISK_MAGIC, "bad on-disk merkle magic");
        let digest_words =
            u32::from_le_bytes([header[4], header[5], header[6], header[7]]) as usize;
        assert_eq!(
            digest_words, DIGEST_SIZE_U32_WORDS,
            "on-disk digest width mismatch"
        );
        let num_leaves = u64::from_le_bytes(header[8..16].try_into().unwrap()) as usize;
        let cap_size = u64::from_le_bytes(header[16..24].try_into().unwrap()) as usize;
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
        Self {
            num_leaves,
            cap_size,
            depth,
            cap_offset,
            leaf_offset,
            internal_offsets,
        }
    }

    #[inline]
    fn digest_at(bytes: &[u8], byte_offset: usize) -> Digest {
        digest_from_le_bytes(&bytes[byte_offset..byte_offset + DIGEST_BYTES])
    }

    fn get_cap(&self, bytes: &[u8]) -> MerkleTreeCapVarLength {
        let cap = (0..self.cap_size)
            .map(|i| Self::digest_at(bytes, self.cap_offset + i * DIGEST_BYTES))
            .collect();
        MerkleTreeCapVarLength { cap }
    }

    fn get_proof(&self, bytes: &[u8], idx: usize) -> (Digest, Vec<Digest>) {
        // Mirrors the in-memory trees' `get_proof`: level 0 sibling from the leaf
        // layer, level `i > 0` from internal layer `L_i`.
        let mut result = Vec::with_capacity(self.depth);
        let mut idx = idx;
        let this_leaf = Self::digest_at(bytes, self.leaf_offset + idx * DIGEST_BYTES);
        for i in 0..self.depth {
            let pair = idx ^ 1;
            let el = if i == 0 {
                Self::digest_at(bytes, self.leaf_offset + pair * DIGEST_BYTES)
            } else {
                Self::digest_at(bytes, self.internal_offsets[i - 1] + pair * DIGEST_BYTES)
            };
            result.push(el);
            idx >>= 1;
        }
        (this_leaf, result)
    }
}

/// A single serialized merkle tree, memory-mapped and OWNING its mapping — a
/// self-contained [`PathQueryable`] (no borrows). Digests are read lazily through
/// the OS page cache; nothing is loaded eagerly.
pub struct MmapMerkleTree {
    mmap: MemoryMappedFile,
    layout: TreeLayout,
}

impl MmapMerkleTree {
    /// Memory-map a serialized tree file (as written by `write_disk_artifacts`).
    pub fn open<P: AsRef<Path>>(path: P) -> std::io::Result<Self> {
        let mmap = MemoryMappedFile::open_ro(path).map_err(mmap_io_err)?;
        let header = mmap
            .as_slice_bytes(0, HEADER_BYTES as u64)
            .map_err(mmap_io_err)?;
        let layout = TreeLayout::parse(header);
        Ok(Self { mmap, layout })
    }

    /// Number of leaves in this tree.
    #[inline]
    pub fn num_leaves(&self) -> usize {
        self.layout.num_leaves
    }

    /// Zero-copy whole-file view (lazily paged; no allocation).
    #[inline]
    fn bytes(&self) -> &[u8] {
        self.mmap
            .as_slice_bytes(0, self.mmap.len())
            .expect("merkle tree mmap slice")
    }
}

impl core::fmt::Debug for MmapMerkleTree {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("MmapMerkleTree")
            .field("num_leaves", &self.layout.num_leaves)
            .field("cap_size", &self.layout.cap_size)
            .finish()
    }
}

impl PathQueryable for MmapMerkleTree {
    fn get_cap(&self) -> MerkleTreeCapVarLength {
        self.layout.get_cap(self.bytes())
    }

    fn get_proof(
        &self,
        idx: usize,
    ) -> (
        [u32; DIGEST_SIZE_U32_WORDS],
        Vec<[u32; DIGEST_SIZE_U32_WORDS]>,
    ) {
        self.layout.get_proof(self.bytes(), idx)
    }
}

/// File path for the per-coset subtree of NATURAL coset `i` (coset 0 = main domain).
pub fn subtree_file_path(prefix: &str, coset_index: usize) -> PathBuf {
    PathBuf::from(format!("{prefix}.subtree_{coset_index:04}.tree"))
}

/// File path for the top-tree over the per-coset subtree roots.
pub fn top_tree_file_path(prefix: &str) -> PathBuf {
    PathBuf::from(format!("{prefix}.toptree.tree"))
}

/// A [`PathQueryable`] assembled from one memory-mapped subtree file per coset plus
/// a small top-tree over their roots (the "second" on-disk tree layout). Owns all
/// its mappings. It serves an inclusion path as the within-coset subtree path
/// stitched to the top-tree path, which is byte-identical to a monolithic tree's
/// `get_proof` — but the subtrees can be prepared and stored one coset at a time.
pub struct OnDiskCosetTree {
    /// One subtree per NATURAL coset (each built with cap_size 1).
    subtrees: Vec<MmapMerkleTree>,
    /// Top tree over the per-coset roots (leaves in physical, bit-reversed order).
    top_tree: MmapMerkleTree,
    /// Leaves per coset subtree.
    coset_tree_size: usize,
    cosets_log2: u32,
}

impl OnDiskCosetTree {
    /// Open `num_cosets` subtree files (NATURAL coset order) + the top-tree file
    /// under a shared `prefix`.
    pub fn open(prefix: &str, num_cosets: usize) -> std::io::Result<Self> {
        assert!(num_cosets.is_power_of_two());
        let mut subtrees = Vec::with_capacity(num_cosets);
        for i in 0..num_cosets {
            subtrees.push(MmapMerkleTree::open(subtree_file_path(prefix, i))?);
        }
        let top_tree = MmapMerkleTree::open(top_tree_file_path(prefix))?;
        let coset_tree_size = subtrees[0].num_leaves();
        Ok(Self {
            subtrees,
            top_tree,
            coset_tree_size,
            cosets_log2: num_cosets.trailing_zeros(),
        })
    }
}

impl core::fmt::Debug for OnDiskCosetTree {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("OnDiskCosetTree")
            .field("num_cosets", &self.subtrees.len())
            .field("coset_tree_size", &self.coset_tree_size)
            .finish()
    }
}

impl PathQueryable for OnDiskCosetTree {
    fn get_cap(&self) -> MerkleTreeCapVarLength {
        PathQueryable::get_cap(&self.top_tree)
    }

    fn get_proof(
        &self,
        idx: usize,
    ) -> (
        [u32; DIGEST_SIZE_U32_WORDS],
        Vec<[u32; DIGEST_SIZE_U32_WORDS]>,
    ) {
        // Monolithic layout puts cosets in physical (bit-reversed) order; a leaf
        // index decomposes into (physical coset slot, index within the coset).
        let physical_slot = idx / self.coset_tree_size;
        let internal_index = idx % self.coset_tree_size;
        let natural_coset = bitreverse_index(physical_slot, self.cosets_log2);
        let (leaf, mut path) =
            PathQueryable::get_proof(&self.subtrees[natural_coset], internal_index);
        let (_root, top_path) = PathQueryable::get_proof(&self.top_tree, physical_slot);
        path.extend_from_slice(&top_path);
        (leaf, path)
    }
}

/// The on-disk tree layout backing an on-disk commitment: either one monolithic
/// tree file ([`MmapMerkleTree`]) or per-coset subtree files plus a top-tree
/// ([`OnDiskCosetTree`]). Owns all its mappings and is a self-contained
/// [`PathQueryable`]. Covariant over the tree constructor `T` it was produced by.
pub enum OnDiskTree<T> {
    Monolithic {
        tree: MmapMerkleTree,
        _marker: PhantomData<fn() -> T>,
    },
    CosetSubtrees {
        tree: OnDiskCosetTree,
        _marker: PhantomData<fn() -> T>,
    },
}

impl<T> OnDiskTree<T> {
    #[inline]
    pub fn monolithic(tree: MmapMerkleTree) -> Self {
        OnDiskTree::Monolithic {
            tree,
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn coset_subtrees(tree: OnDiskCosetTree) -> Self {
        OnDiskTree::CosetSubtrees {
            tree,
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn layout(&self) -> OnDiskTreeLayout {
        match self {
            OnDiskTree::Monolithic { .. } => OnDiskTreeLayout::Monolithic,
            OnDiskTree::CosetSubtrees { .. } => OnDiskTreeLayout::CosetSubtrees,
        }
    }
}

impl<T> core::fmt::Debug for OnDiskTree<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            OnDiskTree::Monolithic { tree, .. } => {
                f.debug_tuple("OnDiskTree::Monolithic").field(tree).finish()
            }
            OnDiskTree::CosetSubtrees { tree, .. } => f
                .debug_tuple("OnDiskTree::CosetSubtrees")
                .field(tree)
                .finish(),
        }
    }
}

impl<T> PathQueryable for OnDiskTree<T> {
    fn get_cap(&self) -> MerkleTreeCapVarLength {
        match self {
            OnDiskTree::Monolithic { tree, .. } => PathQueryable::get_cap(tree),
            OnDiskTree::CosetSubtrees { tree, .. } => PathQueryable::get_cap(tree),
        }
    }

    fn get_proof(
        &self,
        idx: usize,
    ) -> (
        [u32; DIGEST_SIZE_U32_WORDS],
        Vec<[u32; DIGEST_SIZE_U32_WORDS]>,
    ) {
        match self {
            OnDiskTree::Monolithic { tree, .. } => PathQueryable::get_proof(tree, idx),
            OnDiskTree::CosetSubtrees { tree, .. } => PathQueryable::get_proof(tree, idx),
        }
    }
}

/// Shared orchestration for `ColumnMajorMerkleTreeConstructor::write_disk_artifacts`.
///
/// Concrete tree types delegate here, passing `layers_of` — an accessor that
/// exposes a built tree's [`SerializableTreeLayers`] (the one piece that needs the
/// concrete type's fields). This keeps the Monolithic/CosetSubtrees layout logic in
/// one place instead of duplicating it across each tree impl.
///
/// [`OnDiskTreeLayout::Monolithic`] writes one tree file (`<base_path>.tree`);
/// [`OnDiskTreeLayout::CosetSubtrees`] writes one cap-size-1 subtree file per coset
/// (`<base_path>.subtree_NNNN.tree`) plus a top-tree (`<base_path>.toptree.tree`),
/// processing ONE coset at a time (memory-light). Read back with [`open_disk_artifacts`].
#[allow(clippy::too_many_arguments)]
pub fn write_disk_artifacts<'a, F, T, E, LayersFn>(
    base_path: &str,
    layout: OnDiskTreeLayout,
    num_cosets: usize,
    mut producer: CosetColumnsProducer<'a, E>,
    combine_by: usize,
    cap_size: usize,
    bitreverse_evaluations: bool,
    bitreverse_cosets: bool,
    bitreverse_leaf_hashes: bool,
    worker: &Worker,
    layers_of: LayersFn,
) -> std::io::Result<()>
where
    F: PrimeField,
    T: ColumnMajorMerkleTreeConstructor<F>,
    E: FieldExtension<F> + 'a,
    LayersFn: for<'b> Fn(&'b T) -> SerializableTreeLayers<'b>,
    [(); E::DEGREE]: Sized,
{
    use std::io::BufWriter;
    match layout {
        OnDiskTreeLayout::Monolithic => {
            let tree = T::construct_from_coset_producer::<E>(
                num_cosets,
                producer,
                combine_by,
                cap_size,
                bitreverse_evaluations,
                bitreverse_cosets,
                bitreverse_leaf_hashes,
                worker,
            );
            let mut f =
                BufWriter::new(std::fs::File::create(monolithic_tree_file_path(base_path))?);
            layers_of(&tree).write_to(&mut f)?;
            f.flush()?;
        }
        OnDiskTreeLayout::CosetSubtrees => {
            assert!(num_cosets.is_power_of_two());
            assert!(
                cap_size <= num_cosets,
                "split layout requires cap_size ({cap_size}) <= num_cosets ({num_cosets})"
            );
            let cosets_log2 = num_cosets.trailing_zeros();
            let mut natural_roots: Vec<[u32; DIGEST_SIZE_U32_WORDS]> =
                Vec::with_capacity(num_cosets);
            for coset_index in 0..num_cosets {
                let columns = producer(coset_index);
                let col_refs: Vec<&[E]> = columns.iter().map(|c| c.as_ref()).collect();
                let coset_refs: &[&[E]] = &col_refs[..];
                let trace: &[&[&[E]]] = std::slice::from_ref(&coset_refs);
                // cap-1 subtree over just this coset (bitreverse_cosets is a no-op
                // for a single coset; the top-tree carries the coset ordering).
                let subtree = T::construct_from_cosets::<E>(
                    trace,
                    combine_by,
                    1,
                    bitreverse_evaluations,
                    false,
                    bitreverse_leaf_hashes,
                    worker,
                );
                let mut f = BufWriter::new(std::fs::File::create(subtree_file_path(
                    base_path,
                    coset_index,
                ))?);
                layers_of(&subtree).write_to(&mut f)?;
                f.flush()?;
                natural_roots.push(subtree.get_cap().cap[0]);
            }
            let physical_roots: Vec<[u32; DIGEST_SIZE_U32_WORDS]> = (0..num_cosets)
                .map(|k| natural_roots[bitreverse_index(k, cosets_log2)])
                .collect();
            let top_tree = T::build_over_leaf_hashes(physical_roots, cap_size, worker);
            let mut f = BufWriter::new(std::fs::File::create(top_tree_file_path(base_path))?);
            layers_of(&top_tree).write_to(&mut f)?;
            f.flush()?;
        }
    }
    Ok(())
}

/// Shared orchestration for `ColumnMajorMerkleTreeConstructor::open_disk_artifacts`.
///
/// Memory-maps the on-disk tree artifacts previously written by
/// [`write_disk_artifacts`] at `base_path`, producing an [`OnDiskTree`]. `layout` is
/// the layout the caller expects; this PANICS if the artifacts on disk are of a
/// different layout. `num_cosets` is used only for the split layout. Needs no
/// concrete-tree accessor — the reader types are field-agnostic.
pub fn open_disk_artifacts<T>(
    base_path: &str,
    layout: OnDiskTreeLayout,
    num_cosets: usize,
) -> OnDiskTree<T> {
    let mono_present = monolithic_tree_file_path(base_path).exists();
    let split_present =
        top_tree_file_path(base_path).exists() && subtree_file_path(base_path, 0).exists();
    let on_disk_layout = match (mono_present, split_present) {
        (true, false) => OnDiskTreeLayout::Monolithic,
        (false, true) => OnDiskTreeLayout::CosetSubtrees,
        (true, true) => {
            panic!("both monolithic and split tree artifacts present at {base_path}")
        }
        (false, false) => panic!("no tree artifacts present at {base_path}"),
    };
    assert_eq!(
        on_disk_layout, layout,
        "on-disk tree layout ({on_disk_layout:?}) != caller-provided layout ({layout:?})"
    );
    match layout {
        OnDiskTreeLayout::Monolithic => OnDiskTree::monolithic(
            MmapMerkleTree::open(monolithic_tree_file_path(base_path))
                .expect("open monolithic tree artifact"),
        ),
        OnDiskTreeLayout::CosetSubtrees => OnDiskTree::coset_subtrees(
            OnDiskCosetTree::open(base_path, num_cosets).expect("open split tree artifacts"),
        ),
    }
}

#[cfg(all(test, feature = "prover"))]
mod test {
    use super::*;
    use crate::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
    use crate::merkle_trees::ColumnMajorMerkleTreeConstructor;
    use field::Proth120;
    use std::alloc::Global;
    use worker::Worker;

    /// Serialize a keccak tree, reparse it from the byte image, and require the
    /// mmap-backed `PathQueryable` to reproduce the in-memory tree's `get_cap` and,
    /// for every leaf, `get_proof` (leaf hash + full sibling path) exactly.
    fn roundtrip(num_columns: usize, trace_len_log2: usize, cap_size: usize) {
        let worker = Worker::new_with_num_threads(2);
        let trace_len = 1usize << trace_len_log2;

        let cols: Vec<Vec<Proth120>> = (0..num_columns)
            .map(|c| {
                (0..trace_len)
                    .map(|r| {
                        Proth120::new(((7 * (c * trace_len + r) + 1) as u128) % Proth120::ORDER)
                    })
                    .collect()
            })
            .collect();
        let col_refs: Vec<&[Proth120]> = cols.iter().map(|c| c.as_slice()).collect();
        let coset: &[&[Proth120]] = &col_refs;
        let trace: &[&[&[Proth120]]] = &[coset];

        // Reference tree built in memory.
        let tree = <Keccak256MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<
            Proth120,
        >>::construct_from_cosets::<Proth120>(
            trace, 1, cap_size, true, false, false, &worker
        );

        // Write + read back the monolithic artifact through the public disk API.
        let prefix = format!(
            "{}/on_disk_mono_roundtrip_{num_columns}_{trace_len_log2}_{cap_size}",
            std::env::temp_dir().display()
        );
        let producer: crate::merkle_trees::CosetColumnsProducer<Proth120> = {
            let col_refs = col_refs.clone();
            Box::new(move |_coset: usize| {
                col_refs
                    .iter()
                    .map(|c| std::borrow::Cow::Borrowed(*c))
                    .collect()
            })
        };
        <Keccak256MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<Proth120>>::write_disk_artifacts::<
            Proth120,
        >(
            &prefix,
            OnDiskTreeLayout::Monolithic,
            1,
            producer,
            1,
            cap_size,
            true,
            false,
            false,
            &worker,
        )
        .unwrap();
        let disk = <Keccak256MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<
            Proth120,
        >>::open_disk_artifacts(&prefix, OnDiskTreeLayout::Monolithic, 1);

        assert_eq!(
            PathQueryable::get_cap(&disk),
            PathQueryable::get_cap(&tree),
            "cap mismatch (cols={num_columns}, tl={trace_len_log2}, cap={cap_size})"
        );

        for idx in 0..trace_len {
            let (want_leaf, want_path) = PathQueryable::get_proof(&tree, idx);
            let (got_leaf, got_path) = PathQueryable::get_proof(&disk, idx);
            assert_eq!(got_leaf, want_leaf, "leaf hash @ {idx}");
            assert_eq!(got_path, want_path, "path @ {idx}");
        }
        drop(disk);
        let _ = std::fs::remove_file(monolithic_tree_file_path(&prefix));
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
