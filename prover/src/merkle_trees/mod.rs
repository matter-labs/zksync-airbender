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
pub trait PathQueriable<F: PrimeField> {
    fn get_cap(&self) -> MerkleTreeCapVarLength;
    fn get_proof<C: GoodAllocator>(
        &self,
        idx: usize,
    ) -> (
        [u32; DIGEST_SIZE_U32_WORDS],
        Vec<[u32; DIGEST_SIZE_U32_WORDS], C>,
    );
}

pub trait ColumnMajorMerkleTreeConstructor<F: PrimeField>:
    Sized + Send + Sync + core::fmt::Debug
{
    type Verifier: LeafInclusionVerifier;

    /// Disk/mmap-backed [`PathQueriable`] view of a serialized instance of this
    /// tree. Constructed by [`Self::disk_path`] over bytes previously produced by
    /// [`Self::serialize_to_disk_format`]. Serving inclusion proofs from an mmap'd
    /// file lets the prover keep only the compact RS-codeword form in RAM.
    type DiskPath<'a>: PathQueriable<F>;

    fn dummy() -> Self;

    /// Serialize the built tree into the simple on-disk format consumed by
    /// [`Self::disk_path`] (a small header followed by the cap digests, the leaf
    /// hashes, and the internal layer hashes — see [`on_disk`]), streaming it into
    /// any [`std::io::Write`] sink (a file, a `Vec<u8>`, …).
    fn serialize_to_disk_format<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()>;

    /// Build a [`PathQueriable`] over mmap'd (or otherwise borrowed) bytes that were
    /// produced by [`Self::serialize_to_disk_format`].
    fn disk_path<'a>(bytes: &'a [u8]) -> Self::DiskPath<'a>;

    fn construct_from_cosets<E: FieldExtension<F>, A: GoodAllocator>(
        trace: &[&[&[E]]], // slice of cosets, each coset - is a slice of column evaluations
        combine_by: usize,
        cap_size: usize,
        bitreverse_evaluations: bool,
        bitreverse_cosets: bool,
        bitreverse_leaf_hashes: bool,
        worker: &Worker,
    ) -> Self
    where
        [(); E::DEGREE]: Sized;

    fn get_cap(&self) -> MerkleTreeCapVarLength;

    fn get_proof<C: GoodAllocator>(
        &self,
        idx: usize,
    ) -> (
        [u32; DIGEST_SIZE_U32_WORDS],
        Vec<[u32; DIGEST_SIZE_U32_WORDS], C>,
    );

    /// Build a tree whose leaves ARE the given digests (e.g. per-coset subtree
    /// roots), up to `cap_size` top nodes. Lets the coset-by-coset commitment
    /// assemble the top tree over per-coset roots without re-hashing field data.
    fn build_over_leaf_hashes(
        leaf_hashes: Vec<[u32; DIGEST_SIZE_U32_WORDS]>,
        cap_size: usize,
        worker: &Worker,
    ) -> Self;
}
