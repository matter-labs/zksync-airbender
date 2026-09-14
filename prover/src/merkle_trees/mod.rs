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

impl<'a, T, A: CosetIndexedAccessor<T> + ?Sized> CosetIndexedAccessor<T> for &'a A {
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

pub trait ColumnMajorMerkleTreeConstructor<F: PrimeField>:
    Sized + Send + Sync + core::fmt::Debug + PathQueryable + 'static
{
    type Verifier: LeafInclusionVerifier;

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
    ) -> Self
    where
        [(); E::DEGREE]: Sized;

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
    ) -> Self
    where
        [(); E::DEGREE]: Sized;

    fn construct_from_coset_producer<'a, E: FieldExtension<F> + 'a>(
        num_cosets: usize,
        mut producer: CosetColumnsProducer<'a, E>,
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
        let cosets: Vec<Vec<Box<dyn CosetIndexedAccessor<E> + 'a>>> =
            (0..num_cosets).map(|c| producer(c)).collect();
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
    /// writes one cap-size-1 subtree file per coset (`<base_path>.subtree_NNNN.tree`)
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
    ) -> std::io::Result<()>
    where
        [(); E::DEGREE]: Sized;

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
