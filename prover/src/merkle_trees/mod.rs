use crate::definitions::{LeafInclusionVerifier, MerkleTreeCap, DIGEST_SIZE_U32_WORDS};
use field::PrimeField;
use std::borrow::Cow;

use fft::GoodAllocator;
use field::FieldExtension;
use worker::Worker;

pub mod blake2s_for_everything_tree;
pub mod blake2s_hash_leafs;
pub mod keccak256_for_everything_tree;
pub mod keccak256_hash_leafs;
pub mod on_disk;

pub type DefaultTreeConstructor =
    crate::merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap<
        std::alloc::Global,
    >;

#[derive(Clone, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize)]
pub struct MerkleTreeCapVarLength {
    pub cap: Vec<[u32; DIGEST_SIZE_U32_WORDS]>,
}

impl MerkleTreeCapVarLength {
    pub fn into_fixed_holder<const N: usize>(self) -> MerkleTreeCap<N> {
        MerkleTreeCap {
            cap: self.cap.try_into().unwrap(),
        }
    }

    pub fn add_into_buffer(&self, buffer: &mut Vec<u32>) {
        for el in self.cap.iter() {
            buffer.extend_from_slice(el);
        }
    }

    pub fn estimate_size(&self) -> usize {
        self.cap.len() * DIGEST_SIZE_U32_WORDS * core::mem::size_of::<u32>()
    }
}

/// The RS-codeword values of a SINGLE LDE coset: serves the packed leaf values
/// for a folded-domain index within that coset (offset-major `[offset][column]`,
/// exactly as WHIR builds a Merkle leaf).
pub trait SingleCosetRSQueryable<T: 'static + Sized> {
    fn values_for_folded_index(&self, index: usize, values_per_leaf: usize) -> Vec<Vec<T>>;
}

/// A main-domain (LDE coset 0) column as served by an [`RSQueryable`] source, in
/// whichever representation that source holds cheaply.
///
/// `whir_fold` batches these columns down to the monomial (multilinear
/// coefficient) form it folds, so a source that already stores monomials — e.g.
/// the coset-recomputing commitment — can return them directly via
/// [`MainDomainColumn::Monomials`] and skip the evaluations→coefficients inverse
/// transform. Materialized cosets, which hold evaluations, return
/// [`MainDomainColumn::Evals`]. Each variant is a `Cow`, so the data is borrowed
/// when the source owns it and owned when it had to be recomputed.
pub enum MainDomainColumn<'a, T: Clone> {
    /// Evaluations on the main evaluation domain (coset 0, offset 1).
    Evals(Cow<'a, [T]>),
    /// Evaluations in the block-padded storage layout of the AVX-512 base LDE.
    EvalsPadded(PaddedBlocksView<'a, T>),
    /// Multilinear monomial coefficients (the form WHIR folds).
    Monomials(Cow<'a, [T]>),
}

impl<'a, T: Copy + Sync> MainDomainColumn<'a, T> {
    /// The underlying column data in natural order (compacted when padded).
    #[inline]
    pub fn as_slice(&self) -> Cow<'_, [T]> {
        match self {
            MainDomainColumn::Evals(c) | MainDomainColumn::Monomials(c) => {
                Cow::Borrowed(c.as_ref())
            }
            MainDomainColumn::EvalsPadded(p) => Cow::Owned(p.to_vec()),
        }
    }

    /// Take ownership of the underlying column data (natural order).
    #[inline]
    pub fn into_owned(self) -> Vec<T> {
        match self {
            MainDomainColumn::Evals(c) | MainDomainColumn::Monomials(c) => c.into_owned(),
            MainDomainColumn::EvalsPadded(p) => p.to_vec(),
        }
    }

    /// Natural length.
    #[inline]
    pub fn len(&self) -> usize {
        match self {
            MainDomainColumn::Evals(c) | MainDomainColumn::Monomials(c) => c.len(),
            MainDomainColumn::EvalsPadded(p) => p.len(),
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Index-addressed view of the data (no copy in either layout).
    #[inline]
    pub fn view(&self) -> ColumnView<'_, T> {
        match self {
            MainDomainColumn::Evals(c) | MainDomainColumn::Monomials(c) => {
                ColumnView::Contiguous(c.as_ref())
            }
            MainDomainColumn::EvalsPadded(p) => ColumnView::Padded(*p),
        }
    }

    /// `true` if this column is already in monomial-coefficient form.
    #[inline]
    pub fn is_monomials(&self) -> bool {
        matches!(self, MainDomainColumn::Monomials(_))
    }
}

/// A full RS codeword (all LDE cosets) viewed as a value source, decoupled from
/// how the accompanying Merkle tree/paths are stored (see [`PathQueryable`]).
///
/// Implementors may hold every coset materialized in RAM
/// ([`MaterializedCosets`](crate::gkr::whir::MaterializedCosets)) or keep only a
/// compact form and recompute the coset a query lands in
/// (`CosetByCosetBaseCommitment`). Later prover configurations pick the policy per
/// oracle; call sites talk to this trait rather than a concrete owner.
pub trait RSQueryable<T: 'static + Sized + Clone>: core::fmt::Debug + Send + Sync {
    /// Number of committed columns.
    fn num_columns(&self) -> usize;
    /// Number of LDE cosets (= LDE factor).
    fn num_cosets(&self) -> usize;
    /// log2 of the size of a single LDE coset (the per-coset polynomial length).
    /// Exposed for future self-checks (verifying a source's coset dimensions
    /// against the schedule/trace length).
    fn coset_size_log2(&self) -> usize;
    /// Packed leaf values (offset-major `[offset][column]`) for folded index
    /// `index` inside the natural-order coset `coset_in_natural_enumeration`.
    fn values_for_coset_and_index(
        &self,
        coset_in_natural_enumeration: usize,
        index: usize,
        values_per_leaf: usize,
    ) -> Vec<Vec<T>>;
    /// Column `column_index` on the MAIN evaluation domain, in whichever form the
    /// source holds cheaply (evaluations for materialized cosets, monomial
    /// coefficients for a monomial-storing recompute source). The only coset
    /// `whir_fold` reads in full, for the batched proximity poly.
    fn main_domain_column(&self, column_index: usize) -> MainDomainColumn<'_, T>;
    /// Downcast bridge: lets a boxed source recover its concrete type (e.g. to reach
    /// `MaterializedCosets::serialize_to_disk` through a `Box<dyn RSQueryable>`).
    fn as_any(&self) -> &dyn std::any::Any;
}

/// The Merkle-tree side of an oracle: the cap and inclusion paths, decoupled from
/// where the tree lives (fully in RAM, a top-tree over recomputed subtrees, or an
/// mmap'd on-disk file — see [`on_disk`]).
/// A single Merkle digest (`DIGEST_SIZE_U32_WORDS` u32 words).
pub type Digest = [u32; DIGEST_SIZE_U32_WORDS];

pub trait PathQueryable: core::fmt::Debug + Send + Sync {
    fn get_cap(&self) -> MerkleTreeCapVarLength;
    fn get_proof(&self, idx: usize) -> (Digest, Vec<Digest>);
}

/// One column of one LDE coset, addressed by its natural (evaluation-order)
/// index. The storage behind it need not be contiguous: the AVX-512 base LDE
/// writes block-padded codewords (see [`PaddedBlocksView`]), a recomputing
/// producer hands out owned columns, materialized cosets plain slices. The
/// leaf hashers are generic over it, so the in-memory paths inline `get`.
pub trait CosetIndexedAccessor<T>: Sync {
    /// Natural length of the column.
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Value at natural index `index`.
    fn get(&self, index: usize) -> T;
}

impl<T: Copy + Sync> CosetIndexedAccessor<T> for [T] {
    #[inline(always)]
    fn len(&self) -> usize {
        <[T]>::len(self)
    }
    #[inline(always)]
    fn get(&self, index: usize) -> T {
        self[index]
    }
}

impl<T: Copy + Sync> CosetIndexedAccessor<T> for Vec<T> {
    #[inline(always)]
    fn len(&self) -> usize {
        <[T]>::len(self)
    }
    #[inline(always)]
    fn get(&self, index: usize) -> T {
        self[index]
    }
}

impl<T, A: CosetIndexedAccessor<T> + ?Sized> CosetIndexedAccessor<T> for &A {
    #[inline(always)]
    fn len(&self) -> usize {
        (**self).len()
    }
    #[inline(always)]
    fn get(&self, index: usize) -> T {
        (**self).get(index)
    }
}

impl<T, A: CosetIndexedAccessor<T> + ?Sized> CosetIndexedAccessor<T> for Box<A> {
    #[inline(always)]
    fn len(&self) -> usize {
        (**self).len()
    }
    #[inline(always)]
    fn get(&self, index: usize) -> T {
        (**self).get(index)
    }
}

/// Leaf-level view of one coset column for tree construction: every leaf's
/// `values_per_leaf` COMMITTED values in the tree's leaf order (the
/// bit-reversed stride gather of [`crate::gkr::whir::offsets_vec_for_leaf_construction`]),
/// produced by the accessor itself — so an encoding such as the WHIR
/// evaluations -> multilinear-coefficient leaf conversion happens while the
/// leaves are hashed, and the column stays in evaluation form.
pub trait CosetLeafAccessor<T>: Sync {
    fn num_leaves(&self) -> usize;
    fn values_per_leaf(&self) -> usize;
    /// Write leaf `leaf_index` into `out` (`values_per_leaf` entries).
    fn leaf_into(&self, leaf_index: usize, out: &mut [T]);
    /// Leaves `first_leaf .. first_leaf + count` into `out` (leaf-major,
    /// `count * values_per_leaf` entries); accessors that convert can batch
    /// the conversion here.
    fn leaves_into(&self, first_leaf: usize, count: usize, out: &mut [T]) {
        let vpl = self.values_per_leaf();
        for (w, chunk) in out[..count * vpl].chunks_exact_mut(vpl).enumerate() {
            self.leaf_into(first_leaf + w, chunk);
        }
    }
    /// Leaves `first_leaf .. first_leaf + count` SLOT-MAJOR into `out`
    /// (`out[k * count + w]` = slot `k` of leaf `w`) when the accessor can
    /// produce that layout directly (`true`); `false` leaves `out` untouched
    /// and the caller falls back to [`Self::leaves_into`].
    fn leaves_into_slot_major(&self, _first_leaf: usize, _count: usize, _out: &mut [T]) -> bool {
        false
    }
}

/// The plain (no conversion) leaf accessor over a contiguous column.
pub struct PlainCosetLeaves<'a, T> {
    column: &'a [T],
    offsets: Vec<usize>,
}

impl<'a, T> PlainCosetLeaves<'a, T> {
    pub fn new(column: &'a [T], values_per_leaf: usize) -> Self {
        Self {
            column,
            offsets: crate::gkr::whir::offsets_vec_for_leaf_construction(
                column.len(),
                values_per_leaf,
            ),
        }
    }
}

impl<'a, T: Copy + Sync> CosetLeafAccessor<T> for PlainCosetLeaves<'a, T> {
    fn num_leaves(&self) -> usize {
        self.column.len() / self.offsets.len()
    }
    fn values_per_leaf(&self) -> usize {
        self.offsets.len()
    }
    #[inline(always)]
    fn leaf_into(&self, leaf_index: usize, out: &mut [T]) {
        for (o, off) in out.iter_mut().zip(self.offsets.iter()) {
            *o = self.column[off + leaf_index];
        }
    }
}

/// A column stored in a block-padded FFT output layout
/// ([`crate::allocation_pool::PaddedBlocks`]): `data` holds
/// `geo.padded_len(len)` elements, the gaps between blocks are never read.
#[derive(Clone, Copy)]
pub struct PaddedBlocksView<'a, T> {
    data: &'a [T],
    len: usize,
    geo: crate::allocation_pool::PaddedBlocks,
}

impl<'a, T> PaddedBlocksView<'a, T> {
    pub fn new(data: &'a [T], len: usize, geo: crate::allocation_pool::PaddedBlocks) -> Self {
        assert!(data.len() >= geo.padded_len(len));
        Self { data, len, geo }
    }
    pub fn padded_data(&self) -> &'a [T] {
        self.data
    }
    pub fn geometry(&self) -> crate::allocation_pool::PaddedBlocks {
        self.geo
    }
}

impl<'a, T: Copy + Sync> CosetIndexedAccessor<T> for PaddedBlocksView<'a, T> {
    #[inline(always)]
    fn len(&self) -> usize {
        self.len
    }
    #[inline(always)]
    fn get(&self, index: usize) -> T {
        debug_assert!(index < self.len);
        unsafe { *self.data.get_unchecked(self.geo.index(index)) }
    }
}

impl<'a, T: Copy> PaddedBlocksView<'a, T> {
    /// The column compacted into natural order.
    pub fn to_vec(&self) -> Vec<T> {
        (0..self.len)
            .map(|i| self.data[self.geo.index(i)])
            .collect()
    }
}

/// A borrowed coset column in either storage layout; the two variants let a
/// hot loop dispatch once and inline the contiguous case.
#[derive(Clone, Copy)]
pub enum ColumnView<'a, T> {
    Contiguous(&'a [T]),
    Padded(PaddedBlocksView<'a, T>),
}

impl<'a, T: Copy + Sync> CosetIndexedAccessor<T> for ColumnView<'a, T> {
    #[inline(always)]
    fn len(&self) -> usize {
        match self {
            Self::Contiguous(s) => s.len(),
            Self::Padded(p) => p.len(),
        }
    }
    #[inline(always)]
    fn get(&self, index: usize) -> T {
        match self {
            Self::Contiguous(s) => s[index],
            Self::Padded(p) => p.get(index),
        }
    }
}

impl<'a, T: Copy> ColumnView<'a, T> {
    /// The natural-order data, borrowed when contiguous.
    pub fn to_cow(&self) -> Cow<'a, [T]> {
        match self {
            Self::Contiguous(s) => Cow::Borrowed(s),
            Self::Padded(p) => Cow::Owned(p.to_vec()),
        }
    }
}

/// A producer of one LDE coset's columns, driving the closure-based constructors on
/// [`ColumnMajorMerkleTreeConstructor`]. `producer(coset_index)` returns that
/// coset's columns as boxed accessors — borrowing the materialized data or owning
/// a recomputed column. The lifetime `'a` ties any borrowed column data; owned
/// columns let a recomputing producer keep only one coset alive at a time.
pub type CosetColumnsProducer<'a, E> =
    Box<dyn FnMut(usize) -> Vec<Box<dyn CosetIndexedAccessor<E> + 'a>> + 'a>;

/// Geometry of a Merkle tree SPLIT into `num_units` equal subtrees (one per LDE
/// coset, or per group of physically adjacent cosets) plus a top tree, for a
/// commitment with `cap_size` top nodes. Both the coset-by-coset commitments
/// and the on-disk split layout use it, and it is what makes the split
/// commitment equal to the monolithic tree for EVERY `cap_size`:
///
/// * `cap_size <= num_units`: every unit subtree is reduced to its single root
///   and the cap is read from the top tree over the `num_units` roots.
/// * `cap_size > num_units`: the cap lives INSIDE the unit subtrees — each is
///   capped at `subtree_cap = cap_size / num_units` nodes, the top "tree" is
///   just those `num_units * subtree_cap = cap_size` nodes in physical order
///   (depth 0, no top path), and the within-unit path stops at the sub-cap.
///
/// Leaves are laid out unit-major in physical (bit-reversed coset) order, so
/// in both cases the cap and every inclusion path match the monolithic tree
/// built by [`ColumnMajorMerkleTreeConstructor::construct_from_cosets`] over
/// the same leaves with the same `cap_size`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SplitTreeGeometry {
    /// Number of unit subtrees (cosets or coset groups).
    pub num_units: usize,
    /// Leaves per unit subtree.
    pub unit_tree_size: usize,
    /// The commitment's cap size.
    pub cap_size: usize,
    /// Cap size each unit subtree is built with: `1` when `cap_size <=
    /// num_units` (the top tree over the unit roots carries the cap), else
    /// `cap_size / num_units` (the cap lives inside the units).
    pub subtree_cap: usize,
}

impl SplitTreeGeometry {
    pub fn new(num_units: usize, unit_tree_size: usize, cap_size: usize) -> Self {
        assert!(num_units.is_power_of_two());
        assert!(unit_tree_size.is_power_of_two());
        assert!(cap_size.is_power_of_two());
        assert!(
            cap_size <= num_units * unit_tree_size,
            "cap_size ({cap_size}) exceeds the number of leaves ({num_units} x {unit_tree_size})"
        );
        // Two regimes, split at `cap_size == num_units`:
        //  * `cap_size <= num_units` (e.g. cap 8 over 32 cosets): every unit is
        //    reduced to its single root; the TOP tree over the `num_units` roots
        //    is what gets capped at `cap_size`.
        //  * `cap_size > num_units` (e.g. cap 16 over 2 cosets): the cap lives
        //    inside the units, `cap_size / num_units` nodes per unit; the top
        //    tree is then exactly the cap (depth 0).
        let subtree_cap = if cap_size <= num_units {
            1
        } else {
            cap_size / num_units
        };
        Self {
            num_units,
            unit_tree_size,
            cap_size,
            subtree_cap,
        }
    }

    /// Number of leaves of the top tree: one per unit sub-cap node.
    #[inline]
    pub fn num_top_leaves(&self) -> usize {
        self.num_units * self.subtree_cap
    }

    /// Top-tree leaf holding the sub-cap node that is the ancestor of leaf
    /// `leaf_in_unit` of the unit at physical slot `physical_unit`.
    #[inline]
    pub fn top_leaf_index(&self, physical_unit: usize, leaf_in_unit: usize) -> usize {
        debug_assert!(physical_unit < self.num_units);
        debug_assert!(leaf_in_unit < self.unit_tree_size);
        let levels_below_sub_cap =
            self.unit_tree_size.trailing_zeros() - self.subtree_cap.trailing_zeros();
        physical_unit * self.subtree_cap + (leaf_in_unit >> levels_below_sub_cap)
    }

    /// The top-tree leaves: the unit sub-caps (`unit_caps[natural unit]`,
    /// each `subtree_cap` long) concatenated in PHYSICAL unit order, where
    /// physical slot `k` holds natural unit `bitreverse(k)`.
    pub fn top_leaves_from_natural_unit_caps(
        &self,
        unit_caps: &[Vec<[u32; DIGEST_SIZE_U32_WORDS]>],
    ) -> Vec<[u32; DIGEST_SIZE_U32_WORDS]> {
        assert_eq!(unit_caps.len(), self.num_units);
        let units_log2 = self.num_units.trailing_zeros();
        let mut leaves = Vec::with_capacity(self.num_top_leaves());
        for k in 0..self.num_units {
            let natural = fft::bitreverse_index(k, units_log2);
            assert_eq!(unit_caps[natural].len(), self.subtree_cap);
            leaves.extend_from_slice(&unit_caps[natural]);
        }
        leaves
    }
}

pub trait ColumnMajorMerkleTreeConstructor<F: PrimeField>:
    Sized + Send + Sync + core::fmt::Debug + PathQueryable + 'static
{
    type Verifier: LeafInclusionVerifier;

    /// Bytes of each `[u32; DIGEST_SIZE_U32_WORDS]` digest that carry hash output;
    /// the rest of the slot is zero.
    const DIGEST_BYTES: usize;

    fn dummy() -> Self;

    /// Build a tree whose leaves ARE the given digests (e.g. per-coset subtree roots),
    /// up to `cap_size` top nodes. Lets the coset-by-coset commitment assemble its top
    /// tree over per-coset roots without re-hashing field data.
    fn build_over_leaf_hashes(
        leaf_hashes: Vec<[u32; DIGEST_SIZE_U32_WORDS]>,
        cap_size: usize,
        worker: &Worker,
    ) -> Self;

    /// The primitive: every coset in memory, each coset a slice of column
    /// accessors (`&[E]` for contiguous columns, [`PaddedBlocksView`] for the
    /// block-padded FFT layout). Generic over the accessor, so the leaf gather
    /// inlines to plain indexing on the in-memory paths.
    fn construct_from_cosets<E: FieldExtension<F>, A: CosetIndexedAccessor<E>>(
        trace: &[&[A]], // slice of cosets, each coset - is a slice of column accessors
        combine_by: usize,
        cap_size: usize,
        bitreverse_evaluations: bool,
        bitreverse_cosets: bool,
        bitreverse_leaf_hashes: bool,
        worker: &Worker,
    ) -> Self;

    /// Closure-driven entry: collects every coset's columns from a
    /// [`CosetColumnsProducer`] (called once per coset in order) and hashes them
    /// through [`Self::construct_from_cosets`] with boxed (dynamic) accessors.
    /// Byte-identical to the materialized path; the one-coset-at-a-time memory
    /// profile only holds on the disk-writing paths, which call the producer
    /// themselves.
    /// Tree over leaf-level accessors (`cosets[c]` = the columns of coset
    /// `c`); the bit-reversed evaluation layout is implied by the accessors.
    fn construct_from_leaf_accessors<E: FieldExtension<F> + field::Field, L: CosetLeafAccessor<E>>(
        cosets: &[&[L]],
        cap_size: usize,
        bitreverse_cosets: bool,
        bitreverse_leaf_hashes: bool,
        worker: &Worker,
    ) -> Self;

    fn construct_from_coset_producer<'a, E: FieldExtension<F> + 'a>(
        num_cosets: usize,
        mut producer: CosetColumnsProducer<'a, E>,
        combine_by: usize,
        cap_size: usize,
        bitreverse_evaluations: bool,
        bitreverse_cosets: bool,
        bitreverse_leaf_hashes: bool,
        worker: &Worker,
    ) -> Self {
        let cosets: Vec<Vec<Box<dyn CosetIndexedAccessor<E> + 'a>>> =
            (0..num_cosets).map(&mut producer).collect();
        let trace: Vec<&[Box<dyn CosetIndexedAccessor<E> + 'a>]> =
            cosets.iter().map(|c| &c[..]).collect();
        Self::construct_from_cosets::<E, _>(
            &trace,
            combine_by,
            cap_size,
            bitreverse_evaluations,
            bitreverse_cosets,
            bitreverse_leaf_hashes,
            worker,
        )
    }

    /// Produce on-disk tree artifacts for the given `layout`, driven by the coset
    /// `producer` (the RS-codeword source). [`OnDiskTreeLayout::Monolithic`](on_disk::OnDiskTreeLayout::Monolithic)
    /// writes one tree file (`<base_path>.tree`);
    /// [`OnDiskTreeLayout::CosetSubtrees`](on_disk::OnDiskTreeLayout::CosetSubtrees)
    /// writes one subtree file per coset (capped at the per-coset sub-cap, see `SplitTreeGeometry`) (`<base_path>.subtree_NNNN.tree`)
    /// plus a top-tree (`<base_path>.toptree.tree`), processing ONE coset at a time
    /// (memory-light). Read back with [`Self::open_disk_artifacts`].
    ///
    /// Implementations delegate to [`on_disk::write_disk_artifacts`], supplying an
    /// accessor for their concrete [`SerializableTreeLayers`](on_disk::SerializableTreeLayers);
    /// that free function holds the shared layout orchestration.
    fn write_disk_artifacts<'a, E: FieldExtension<F> + 'a>(
        base_path: &str,
        layout: on_disk::OnDiskTreeLayout,
        num_cosets: usize,
        producer: CosetColumnsProducer<'a, E>,
        combine_by: usize,
        cap_size: usize,
        bitreverse_evaluations: bool,
        bitreverse_cosets: bool,
        bitreverse_leaf_hashes: bool,
        worker: &Worker,
    ) -> std::io::Result<()>;

    /// Memory-map the on-disk tree artifacts previously written by
    /// [`Self::write_disk_artifacts`] at `base_path`, producing an
    /// [`OnDiskTree`](on_disk::OnDiskTree). `layout` is the layout the caller
    /// expects; this PANICS if the artifacts on disk are of a different layout.
    /// `num_cosets` is used only for the split layout. Implementations delegate to
    /// [`on_disk::open_disk_artifacts`].
    fn open_disk_artifacts(
        base_path: &str,
        layout: on_disk::OnDiskTreeLayout,
        num_cosets: usize,
    ) -> on_disk::OnDiskTree<Self>;
}

#[cfg(test)]
mod split_tree_geometry_tests {
    use super::SplitTreeGeometry;

    #[test]
    fn cap_at_or_above_unit_roots() {
        // production shape: 32 cosets, cap 8 -> unit roots, top tree capped at 8
        let g = SplitTreeGeometry::new(32, 1 << 10, 8);
        assert_eq!(g.subtree_cap, 1);
        assert_eq!(g.num_top_leaves(), 32);
        assert_eq!(g.top_leaf_index(5, 0), 5);
        assert_eq!(g.top_leaf_index(5, (1 << 10) - 1), 5);
        // cap == number of units: still one root per unit, top tree of depth 0
        let g = SplitTreeGeometry::new(16, 1 << 4, 16);
        assert_eq!(g.subtree_cap, 1);
        assert_eq!(g.num_top_leaves(), 16);
        assert_eq!(g.top_leaf_index(3, 7), 3);
    }

    #[test]
    fn cap_inside_units() {
        // 2 cosets, cap 16 -> 8 sub-cap nodes per coset, top tree == cap
        let g = SplitTreeGeometry::new(2, 1 << 6, 16);
        assert_eq!(g.subtree_cap, 8);
        assert_eq!(g.num_top_leaves(), 16);
        // leaf `l` of a unit with 64 leaves sits under sub-cap node `l >> 3`
        assert_eq!(g.top_leaf_index(0, 0), 0);
        assert_eq!(g.top_leaf_index(0, 7), 0);
        assert_eq!(g.top_leaf_index(0, 8), 1);
        assert_eq!(g.top_leaf_index(1, 63), 15);
        // cap == all leaves: every leaf hash is a cap node
        let g = SplitTreeGeometry::new(4, 4, 16);
        assert_eq!(g.subtree_cap, 4);
        assert_eq!(g.top_leaf_index(2, 3), 11);
    }

    #[test]
    #[should_panic]
    fn cap_larger_than_tree_is_rejected() {
        let _ = SplitTreeGeometry::new(2, 4, 16);
    }
}
