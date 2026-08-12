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
pub trait SingleCosetRSQueriable<T: 'static + Sized> {
    fn values_for_folded_index(&self, index: usize, values_per_leaf: usize) -> Vec<Vec<T>>;
}

/// A main-domain (LDE coset 0) column as served by an [`RSQueriable`] source, in
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
    /// Multilinear monomial coefficients (the form WHIR folds).
    Monomials(Cow<'a, [T]>),
}

impl<'a, T: Clone> MainDomainColumn<'a, T> {
    /// The underlying column data, regardless of representation.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        match self {
            MainDomainColumn::Evals(c) | MainDomainColumn::Monomials(c) => c.as_ref(),
        }
    }

    /// Take ownership of the underlying column data.
    #[inline]
    pub fn into_owned(self) -> Vec<T> {
        match self {
            MainDomainColumn::Evals(c) | MainDomainColumn::Monomials(c) => c.into_owned(),
        }
    }

    /// `true` if this column is already in monomial-coefficient form.
    #[inline]
    pub fn is_monomials(&self) -> bool {
        matches!(self, MainDomainColumn::Monomials(_))
    }
}

/// A full RS codeword (all LDE cosets) viewed as a value source, decoupled from
/// how the accompanying Merkle tree/paths are stored (see [`PathQueriable`]).
///
/// Implementors may hold every coset materialized in RAM
/// ([`MaterializedCosets`](crate::gkr::whir::MaterializedCosets)) or keep only a
/// compact form and recompute the coset a query lands in
/// (`CosetByCosetBaseCommitment`). Later prover configurations pick the policy per
/// oracle; call sites talk to this trait rather than a concrete owner.
pub trait RSQueriable<T: 'static + Sized + Clone>: core::fmt::Debug + Send + Sync {
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
    /// `MaterializedCosets::serialize_to_disk` through a `Box<dyn RSQueriable>`).
    fn as_any(&self) -> &dyn std::any::Any;
}

/// The Merkle-tree side of an oracle: the cap and inclusion paths, decoupled from
/// where the tree lives (fully in RAM, a top-tree over recomputed subtrees, or an
/// mmap'd on-disk file — see [`on_disk`]).
/// A single Merkle digest (`DIGEST_SIZE_U32_WORDS` u32 words).
pub type Digest = [u32; DIGEST_SIZE_U32_WORDS];

pub trait PathQueriable: core::fmt::Debug + Send + Sync {
    fn get_cap(&self) -> MerkleTreeCapVarLength;
    fn get_proof(&self, idx: usize) -> (Digest, Vec<Digest>);
}

/// A producer of one LDE coset's columns, driving the closure-based constructors on
/// [`ColumnMajorMerkleTreeConstructor`]. `producer(coset_index)` returns that
/// coset's columns — each borrowed (when the coset is materialized) or owned (when
/// recomputed). The lifetime `'a` ties any borrowed column data; owned columns
/// (`Cow::Owned`) let a recomputing producer keep only one coset alive at a time.
pub type CosetColumnsProducer<'a, E>
    = Box<dyn FnMut(usize) -> Vec<Cow<'a, [E]>> + 'a>
where
    E: Clone;

pub trait ColumnMajorMerkleTreeConstructor<F: PrimeField>:
    Sized + Send + Sync + core::fmt::Debug + PathQueriable + 'static
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

    /// Materialized sibling of [`Self::construct_from_coset_producer`]: wraps the
    /// fully-materialized `trace` in a borrowing [`CosetColumnsProducer`] and
    /// delegates to the producer-driven primitive, hence byte-identical. This is the
    /// convenience entry for callers that already hold every coset in memory.
    fn construct_from_cosets<E: FieldExtension<F>>(
        trace: &[&[&[E]]], // slice of cosets, each coset - is a slice of column evaluations
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
        let num_cosets = trace.len();
        let producer: CosetColumnsProducer<'_, E> = Box::new(move |coset_index| {
            trace[coset_index]
                .iter()
                .map(|column| Cow::Borrowed(*column))
                .collect()
        });
        Self::construct_from_coset_producer::<E>(
            num_cosets,
            producer,
            combine_by,
            cap_size,
            bitreverse_evaluations,
            bitreverse_cosets,
            bitreverse_leaf_hashes,
            worker,
        )
    }

    /// Closure-driven primitive: builds the tree from a [`CosetColumnsProducer`],
    /// calling the producer once per coset in order; each coset's columns are used and
    /// then dropped, so a recomputing producer keeps only one coset in memory. Each
    /// concrete tree implements this (the per-field leaf hashing lives here);
    /// [`Self::construct_from_cosets`] is a materialized-input wrapper over it.
    fn construct_from_coset_producer<'a, E: FieldExtension<F> + 'a>(
        num_cosets: usize,
        producer: CosetColumnsProducer<'a, E>,
        combine_by: usize,
        cap_size: usize,
        bitreverse_evaluations: bool,
        bitreverse_cosets: bool,
        bitreverse_leaf_hashes: bool,
        worker: &Worker,
    ) -> Self
    where
        [(); E::DEGREE]: Sized;

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
