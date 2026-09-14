// The original paper is overly complicated in it's notations, so here is a description.
// We will use capital letter for univariate polys, and small one for multivatiate, and same letter
// of different capitalization is just reinterpretation of one for another
// - Prover starts with oracle of evaluations F0 of the original poly F(X) at some smooth domain L0
// - also we assume that we have an original claim that F(Y) = Z, that can also we rewritten as sumcheck claim
// F(Y) = Z = f(y^0, y^1, y^2, ...) = \sum_{x} eq(x, y^0, y^1, y^2, ...) f(x) - our original sumcheck claim.
// If we sum over all the {x} in the right-hand side, but one, we can view it as a univariate f0(Y), and f0(0) + f0(1) == Z -
// all the standard sumcheck staff
// - Note that in the same manner we can express in-domain value F(omega^k) = \sum_{x} eq(x, omega^k decomposition over powers) f(x)
// - Prover and verifier can engage in more than 1 sumcheck steps (here the tradeoff is less steps later, but more accesses to F0 oracle)
// ---- Steps below are recursive, but we only use indexes 0/1 for clarity. Each step NUM_QUERIES also differs
// - At this moment we would have something like
// claim_0 = \sum_{x/folded coordinates} eq(r1, r2, r3, x4, x5, ... y^0, y^1, y^2, y^4, ...) f(r1, r2, r3, x4, x5, ...)
// - Now prover sends an oracle F1 to f1(x4, x5, ...) = f(r1, r2, r3, x4, x5, ...) at domain L1. Note that "degree" of f1(x4, x5, ...)
// is smaller that of original f(x), but prover can decrease the rate for further iterations of the protocol
// - As in STIR, we want to perform out of domain sampling. So, we draw OOD point y1 and prover sends evaluation of f1(y1^0, y1^1, ...) = z1
// - Now prover also samples NUM_QUERIES indexes in the 3 (in our example) times folded image of L0. Those indexes trivially map
// into the |L0|/2^3 roots of unity. We will use notations Q_i for such indexes and corresponding roots of unity interchangeably
// - As in FRI, verifier has oracle access to f1(Q_i) by accessing 2^3 corresponding elements in F0 (at L0) and folding them.
// - We denote those values as G_i and in the original paper we do not need those values from prover YET, and instead they update our sumcheck claim formally at first,
// but it doesn't affect the protocol, and we will show that verification can be performed right away
// - start with the old one (prefactors aside)
// claim_0 = \sum_{x} eq(x, y^4, y^8, ...) f1(x)
// - add a contribution about f1(y1) = z1
// claim_0 + gamma^1 * z1 = \sum_{x} eq(x, y^4, y^8, ...) f1(x) + gamma^1 * \sum_{x} eq(x, y1^0, y1^1, ...) f1(x)
// - add NUM_QUERIES contribution about Q_i
// claim_0 + gamma^1 * z1 + \sum_{i = 0..NUM_QUERIES} gamma^{i + 1} G_i =
// = \sum_{x} eq(x, y^4, y^8, ...) f1(x) +
// + gamma^1 * \sum_{x} eq(x, y1^0, y1^1, ...) f1(x) +
// + \sum_{i = 0..NUM_QUERIES} gamma^{1+i} * \sum_{x} eq(x, Q_i) f1(x)
// - Those terms re-arrange nicely over f1(x)
// - To continue the sumcheck prover would send some univariate poly f2(Y), but as usual
// f2(0) + f2(1) == claim_0 + gamma^1 * z1 + \sum_{i = 0..NUM_QUERIES} gamma^{i + 1} G_i
// and verifier already has all the values to perform this check and forget about anything that happened before:
// - claim_0 comes from the previous work
// - z1 was sent by the prover
// - G_i are available via oracle access to F0 at L0 (in our example verifier needs 8 elements to fold 3 times and get those values)
// ---- Steps above are recursive until f_i(x) becomes "small-ish"
// - prover and verifier can engate in folding f1(x) few times until it becomes "small"
// - prover sends explicit form of the corresponding f_final(x)
// - same as above, we choose NUM_QUERIES_FINAL indexes, access previous step's oracle to get NUM_QUERIES_FINAL f1(x) values
// - Those values are checked to correspond to the explicit f_final(x) form
// - evaluate the last sumcheck explicitly
// - Due to complexity of such sumcheck (that drags various prefactors from previous rounds), most likely size of the final polynomial
// should be very small (much smaller compared to FRI case)

// NOTE: as we can choose rates somewhat independently from folding parameters, then for 100 bits of conjectured security we can do like
// let's say initially poly is 2^24
// - initial rate 1/2, and fold once - 100 queries, size 2^23
// - we discard all other polys from memory - RAM is no longer a problem, and next computations are cheap
// - rate 1/8, we do 33 queries and fold 4 times. Next step is 2^20
// - rate 1/64, we do 18 queries and fold 4 times. Next step is 2^16
// - rate 1/256, 13 queries, fold 4 times. Next step 2^12
// - rate 1/1024, 10 queries, fold 4 times. Next step 2^8
// - rate 1/4096, 8 queries, fold 4 times, output final 2^4 values

// NOTE: dealing with weight polys (that are EQ in our case only), and mixing it:
// - initially our kernel is claim0 = \sum_{X} eq(r1, r2, r3, ..., X) f(X)
// - prover sends a univariate poly of degree 3 such that p(0) = \sum_{X'} eq(r1, ..., 0, X') f(0, X'), p(1) = \sum_{X'} eq(r1, ..., 1, X') f(1, X'),
// and p(0) + p(1) = claim0
// - then we draw a challenge and evaluate p(alpha) = \sum_{X'} eq(r1, ...., alpha, X') f(alpha, X') =
// = \sum_{X''} eq(r1, ...., alpha, 0, X'') f(alpha, 0, X'') + eq(r1, ...., alpha, 1, X'') f(alpha, 1, X'')

use crate::allocation_pool::{AllocationPool, GenericAllocationPool};
use crate::gkr::prover::backend::LeafConversionHandle;
use crate::gkr::prover::backend::TwiddleSetOps;
use crate::gkr::prover::gkr_backend::BatchedBaseColumn;
use crate::gkr::prover::stages::commitment_utils::{
    compute_column_major_lde_from_monomial_form, ColumnMajorCosetBoundTracePart,
};
use crate::gkr::prover::transcript_utils::{
    add_whir_commitment_to_transcript, commit_field_els, draw_query_bits, draw_random_field_els,
};
use crate::gkr::prover::WhirSchedule;
use crate::gkr::sumcheck::access_and_fold::GKRStorage;
use crate::gkr::sumcheck::*;
use crate::gkr::whir::coset_commit::CosetByCosetBaseCommitment;
use crate::gkr::whir::hypercube_to_monomial::multivariate_coeffs_into_hypercube_evals;
use crate::gkr::PAR_THRESHOLD;
use crate::merkle_trees::{
    ColumnMajorMerkleTreeConstructor, CosetIndexedAccessor, MainDomainColumn,
    MerkleTreeCapVarLength, PathQueryable, RSQueryable, SingleCosetRSQueryable,
};
use crate::query_utils::assemble_query_index;
use cs::definitions::GKRAddress;
use fft::{
    batch_inverse_inplace, bitreverse_enumeration_inplace, bitreverse_index,
    domain_generator_for_size, materialize_powers_serial_starting_with_one, Twiddles,
};
use field::{Field, FieldExtension, PrimeField, TwoAdicField};
use std::alloc::Global;
use std::borrow::Cow;
use std::sync::Arc;
use transcript::Transcript;
use worker::{IterableWithGeometry, Worker};

pub mod by_coefficient;
pub mod coset_commit;
pub mod hypercube_to_monomial;
pub mod in_domain;
pub mod ping_pong;
use in_domain::InDomainTerms;
use ping_pong::PingPongPoly;
pub mod proximity_testing_modes;
pub mod queries;
pub mod rs_on_disk;
pub mod whir_proof;

#[cfg(test)]
mod monomial_basis_self_check;

#[cfg(all(test, feature = "prover"))]
mod proth120_evm_gen;

pub use self::queries::*;
pub use self::whir_proof::*;

#[derive(Debug)]
pub struct ColumnMajorBaseOracleForCoset<F: PrimeField + TwoAdicField> {
    pub original_values_normal_order: Vec<ColumnMajorCosetBoundTracePart<F, F>>, // num_columns
    pub offset: F,
    pub coset_size_log2: usize,
}

impl<F: PrimeField + TwoAdicField> SingleCosetRSQueryable<F> for ColumnMajorBaseOracleForCoset<F> {
    fn values_for_folded_index(&self, index: usize, values_per_leaf: usize) -> Vec<Vec<F>> {
        assert!(values_per_leaf.is_power_of_two());
        assert!(index < (1 << self.coset_size_log2) / values_per_leaf);
        let trace_len = 1 << self.coset_size_log2;

        let mut result: Vec<Vec<F>> = (0..values_per_leaf)
            .into_iter()
            .map(|_| Vec::with_capacity(self.original_values_normal_order.len()))
            .collect();

        match values_per_leaf {
            2 => {
                let offsets = offsets_for_leaf_construction::<2>(trace_len);
                for src_poly in self.original_values_normal_order.iter() {
                    for (j, offset) in offsets.iter().enumerate() {
                        let i = *offset + index;
                        let value = src_poly.get(i);
                        result[j].push(value);
                    }
                }
            }
            4 => {
                let offsets = offsets_for_leaf_construction::<4>(trace_len);
                for src_poly in self.original_values_normal_order.iter() {
                    for (j, offset) in offsets.iter().enumerate() {
                        let i = *offset + index;
                        let value = src_poly.get(i);
                        result[j].push(value);
                    }
                }
            }
            8 => {
                let offsets = offsets_for_leaf_construction::<8>(trace_len);
                for src_poly in self.original_values_normal_order.iter() {
                    for (j, offset) in offsets.iter().enumerate() {
                        let i = *offset + index;
                        let value = src_poly.get(i);
                        result[j].push(value);
                    }
                }
            }
            16 => {
                let offsets = offsets_for_leaf_construction::<16>(trace_len);
                for src_poly in self.original_values_normal_order.iter() {
                    for (j, offset) in offsets.iter().enumerate() {
                        let i = *offset + index;
                        let value = src_poly.get(i);
                        result[j].push(value);
                    }
                }
            }
            32 => {
                let offsets = offsets_for_leaf_construction::<32>(trace_len);
                for src_poly in self.original_values_normal_order.iter() {
                    for (j, offset) in offsets.iter().enumerate() {
                        let i = *offset + index;
                        let value = src_poly.get(i);
                        result[j].push(value);
                    }
                }
            }
            a @ _ => {
                panic!("unsupported: {} values per leaf", a);
            }
        }

        result
    }
}

/// A full RS codeword held fully materialized in RAM: every LDE coset's
/// evaluations for every column. Implements [`RSQueryable`] so a base oracle can
/// talk to it (or to a recompute-on-demand source such as
/// `CosetByCosetBaseCommitment`) behind the same trait object.
#[derive(Debug)]
pub struct MaterializedCosets<F: PrimeField + TwoAdicField> {
    pub cosets: Vec<ColumnMajorBaseOracleForCoset<F>>,
}

impl<F: PrimeField + TwoAdicField> RSQueryable<F> for MaterializedCosets<F> {
    fn num_columns(&self) -> usize {
        self.cosets[0].original_values_normal_order.len()
    }

    fn num_cosets(&self) -> usize {
        self.cosets.len()
    }

    fn coset_size_log2(&self) -> usize {
        self.cosets[0].coset_size_log2
    }

    fn values_for_coset_and_index(
        &self,
        coset_in_natural_enumeration: usize,
        index: usize,
        values_per_leaf: usize,
    ) -> Vec<Vec<F>> {
        self.cosets[coset_in_natural_enumeration].values_for_folded_index(index, values_per_leaf)
    }

    fn main_domain_column(&self, column_index: usize) -> MainDomainColumn<'_, F> {
        // Materialized cosets hold main-domain EVALUATIONS.
        self.cosets[0].original_values_normal_order[column_index].main_domain_column()
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}

/// Boxed [`RSQueryable`] value source (used by the on-disk setup commitment). The
/// trait object is `Send + Sync + Debug` via the trait's supertraits, so it can
/// cross the worker boundary.
pub type BoxedBaseRSSource<F> = Box<dyn RSQueryable<F>>;

/// The fully materialized base oracle: every LDE coset's evaluations in RAM plus
/// the full (concretely typed) Merkle tree. Serves main-domain columns in
/// EVALUATION form and answers queries directly from the stored data.
#[derive(Debug)]
pub struct InMemoryBaseOracle<F: PrimeField + TwoAdicField, T: ColumnMajorMerkleTreeConstructor<F>>
{
    pub cosets: MaterializedCosets<F>,
    pub tree: T,
    pub values_per_leaf: usize,
    pub coset_size_log2: usize,
}

impl<F: PrimeField + TwoAdicField, T: ColumnMajorMerkleTreeConstructor<F>>
    InMemoryBaseOracle<F, T>
{
    /// An oracle with no columns (used when a commitment set is absent): empty
    /// cosets with the right offsets and a dummy tree.
    pub fn empty(values_per_leaf: usize, coset_size_log2: usize, lde_factor: usize) -> Self {
        let generators: Vec<F> =
            crate::gkr::prover::backend::coset_offsets::<F>(1 << coset_size_log2, lde_factor);
        let mut cosets = Vec::with_capacity(lde_factor);
        for i in 0..lde_factor {
            let offset = generators[i];
            let coset = ColumnMajorBaseOracleForCoset {
                original_values_normal_order: Vec::new(),
                offset,
                coset_size_log2,
            };
            cosets.push(coset);
        }

        Self {
            cosets: MaterializedCosets { cosets },
            tree: T::dummy(),
            values_per_leaf,
            coset_size_log2,
        }
    }

    pub fn num_columns(&self) -> usize {
        self.cosets.cosets[0].original_values_normal_order.len()
    }

    pub fn num_cosets(&self) -> usize {
        self.cosets.cosets.len()
    }

    pub fn get_cap(&self) -> MerkleTreeCapVarLength {
        self.tree.get_cap()
    }

    /// Column `c` on the MAIN evaluation domain (LDE coset 0), as evaluations.
    pub fn main_domain_column(&self, column_index: usize) -> MainDomainColumn<'_, F> {
        self.cosets.cosets[0].original_values_normal_order[column_index].main_domain_column()
    }

    pub fn query_for_folded_index(
        &self,
        index: usize,
    ) -> (usize, Vec<Vec<F>>, BaseFieldQuery<F, T>) {
        let num_cosets = self.num_cosets();
        let coset_index = index & (num_cosets - 1);
        let internal_index = index / num_cosets;
        let coset_tree_size = (1 << self.coset_size_log2) / self.values_per_leaf;
        assert!(internal_index < coset_tree_size);
        let values = self.cosets.cosets[coset_index]
            .values_for_folded_index(internal_index, self.values_per_leaf);

        // Tree leaves are laid out sequentially by coset (with bit-reversed coset
        // order)
        let coset_dest_index = bitreverse_index(coset_index, num_cosets.trailing_zeros());
        let tree_index = coset_dest_index * coset_tree_size + internal_index;

        let (_leaf_hash, path) = self.tree.get_proof(tree_index);

        #[cfg(feature = "gkr_self_checks")]
        {
            // This recomputation is blake2s + u32-field (BabyBear) specific. Skip it for
            // larger fields (e.g. Proth120, committed with a keccak tree): the field has
            // no `as_u32_raw_repr_reduced` and the hash algorithm would not match anyway;
            // the coset-by-coset tests already validate that leaf hashing against the
            // monolithic tree.
            if core::mem::size_of::<F>() <= core::mem::size_of::<u32>() {
                let recomputed = Self::compute_base_field_leaf_hash(&values, self.values_per_leaf);
                assert_eq!(
                    recomputed, _leaf_hash,
                    "Leaf hash mismatch at query_index={index}, tree_index={tree_index}"
                );
            }
        }

        let query = BaseFieldQuery::<F, T> {
            index: tree_index,
            leaf_values_concatenated: values.iter().flatten().copied().collect(),
            path,
            _marker: core::marker::PhantomData,
        };
        (coset_index, values, query)
    }

    /// Hash leaf data the same way `blake2s_leaf_hashes_from_cosets` does:
    /// column-major with bit-reversed offsets. `values_offset_major` is the
    /// `[offset][column]` leaf produced by [`RSQueryable::values_for_coset_and_index`];
    /// the tree hashes it column-major (column outer, offset inner), so we transpose.
    #[cfg(feature = "gkr_self_checks")]
    fn compute_base_field_leaf_hash(
        values_offset_major: &[Vec<F>],
        values_per_leaf: usize,
    ) -> [u32; 8] {
        use blake2s_u32::{Blake2sState, BLAKE2S_BLOCK_SIZE_U32_WORDS};

        debug_assert_eq!(values_offset_major.len(), values_per_leaf);
        let num_columns = values_offset_major[0].len();

        let mut buffer = Vec::new();
        for c in 0..num_columns {
            for o in 0..values_per_leaf {
                buffer.push(values_offset_major[o][c].as_u32_raw_repr_reduced());
            }
        }

        let mut h = Blake2sState::new();
        let num_words = buffer.len();
        let num_full_blocks = num_words / BLAKE2S_BLOCK_SIZE_U32_WORDS;
        let remainder = num_words % BLAKE2S_BLOCK_SIZE_U32_WORDS;
        let mut output = [0u32; 8];

        for block_idx in 0..num_full_blocks {
            let block_start = block_idx * BLAKE2S_BLOCK_SIZE_U32_WORDS;
            let block: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS] = unsafe {
                &*(buffer.as_ptr().add(block_start) as *const [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS])
            };
            if block_idx == num_full_blocks - 1 && remainder == 0 {
                h.absorb_final_block::<true>(block, BLAKE2S_BLOCK_SIZE_U32_WORDS, &mut output);
                return output;
            }
            h.absorb::<true>(block);
        }

        let mut last_block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
        let tail_start = num_full_blocks * BLAKE2S_BLOCK_SIZE_U32_WORDS;
        last_block[..remainder].copy_from_slice(&buffer[tail_start..]);
        h.absorb_final_block::<true>(&last_block, remainder, &mut output);
        output
    }
}

/// A base (round-0) WHIR oracle: the RS codeword + Merkle tree of one committed
/// column set (memory, witness, or setup). Storage policy is explicit in the
/// variant; each variant is a standalone type carrying its own implementation:
///
/// * [`Self::InMemory`] ([`InMemoryBaseOracle`]) — every LDE coset materialized
///   in RAM plus the full Merkle tree; main-domain columns come back as
///   EVALUATIONS and queries are read directly from the stored data.
/// * [`Self::CosetRecompute`] ([`CosetByCosetBaseCommitment`]) — only the
///   compact per-column monomial forms plus the small top tree over per-coset
///   subtree roots; main-domain columns come back as MONOMIAL coefficients
///   (whir_fold's batching consumes them with no transform) and query batches
///   are served by grouping over cosets, recomputing each touched coset's RS
///   codeword + subtree exactly once.
///
/// Both variants produce byte-identical commitments and proofs; only memory/time
/// trade-offs differ.
#[derive(Debug)]
pub enum ColumnMajorBaseOracleForLDE<
    F: PrimeField + TwoAdicField,
    T: ColumnMajorMerkleTreeConstructor<F>,
> {
    InMemory(InMemoryBaseOracle<F, T>),
    CosetRecompute(CosetByCosetBaseCommitment<F, T>),
}

impl<F: PrimeField + TwoAdicField, T: ColumnMajorMerkleTreeConstructor<F>>
    ColumnMajorBaseOracleForLDE<F, T>
{
    /// Tear the oracle down, handing every uniquely owned pooled codeword
    /// column back to `pool` (owned columns and the tree are dropped).
    pub fn release_into<E>(self, pool: &dyn AllocationPool<F, E>) {
        match self {
            Self::InMemory(oracle) => {
                let InMemoryBaseOracle { cosets, tree, .. } = oracle;
                drop(tree);
                for coset in cosets.cosets.into_iter() {
                    for part in coset.original_values_normal_order.into_iter() {
                        if let Ok(column) = Arc::try_unwrap(part.column) {
                            column.release_base(pool);
                        }
                    }
                }
            }
            Self::CosetRecompute(c) => drop(c),
        }
    }
}

impl<F: PrimeField + TwoAdicField, T: ColumnMajorMerkleTreeConstructor<F>>
    ColumnMajorBaseOracleForLDE<F, T>
{
    /// An in-memory oracle with no columns (used when a commitment set is absent).
    pub fn empty(values_per_leaf: usize, coset_size_log2: usize, lde_factor: usize) -> Self {
        Self::InMemory(InMemoryBaseOracle::empty(
            values_per_leaf,
            coset_size_log2,
            lde_factor,
        ))
    }

    pub fn num_columns(&self) -> usize {
        match self {
            Self::InMemory(o) => o.num_columns(),
            Self::CosetRecompute(c) => c.monomial_forms.len(),
        }
    }

    pub fn num_cosets(&self) -> usize {
        match self {
            Self::InMemory(o) => o.num_cosets(),
            Self::CosetRecompute(c) => c.lde_factor,
        }
    }

    pub fn values_per_leaf(&self) -> usize {
        match self {
            Self::InMemory(o) => o.values_per_leaf,
            Self::CosetRecompute(c) => c.values_per_leaf,
        }
    }

    pub fn coset_size_log2(&self) -> usize {
        match self {
            Self::InMemory(o) => o.coset_size_log2,
            Self::CosetRecompute(c) => c.trace_len_log2,
        }
    }

    /// The commitment cap (goes into the transcript).
    pub fn get_cap(&self) -> MerkleTreeCapVarLength {
        match self {
            Self::InMemory(o) => o.get_cap(),
            Self::CosetRecompute(c) => c.top_tree.get_cap(),
        }
    }

    /// Column `c` on the MAIN evaluation domain, in whichever form this variant
    /// holds cheaply: evaluations for the materialized oracle, monomial
    /// coefficients for the recompute one. whir_fold's batching accepts both.
    pub fn main_domain_column(&self, column_index: usize) -> MainDomainColumn<'_, F> {
        match self {
            Self::InMemory(o) => o.main_domain_column(column_index),
            Self::CosetRecompute(c) => {
                MainDomainColumn::Monomials(Cow::Borrowed(&c.monomial_forms[column_index][..]))
            }
        }
    }

    /// Serve a batch of round-0 queries at once. Results are in input order (one
    /// entry per query index, duplicates included), each the offset-major
    /// `[offset][column]` leaf values plus the Merkle inclusion query.
    ///
    /// `InMemory` reads each query from the stored cosets/tree; `CosetRecompute`
    /// groups the indices by the LDE coset they land in and recomputes each
    /// touched coset's RS codeword + subtree once for all its queries (`twiddles`
    /// and `worker` exist for that recomputation).
    pub fn query_many(
        &self,
        query_indices: &[usize],
        twiddles: &Twiddles<F, Global>,
        worker: &Worker,
    ) -> Vec<(Vec<Vec<F>>, BaseFieldQuery<F, T>)>
    where
        [(); F::DEGREE]: Sized,
    {
        match self {
            Self::InMemory(o) => query_indices
                .iter()
                .map(|&index| {
                    let (_coset_index, values, query) = o.query_for_folded_index(index);
                    (values, query)
                })
                .collect(),
            Self::CosetRecompute(c) => c.query_many_structured(query_indices, twiddles, worker),
        }
    }

    /// Single-query entry for the `InMemory` variant (tests and self-checks). The
    /// `CosetRecompute` variant panics here: batched serving via
    /// [`Self::query_many`] is the only sensible access pattern for it (a single
    /// query would recompute a whole coset).
    pub fn query_for_folded_index(
        &self,
        index: usize,
    ) -> (usize, Vec<Vec<F>>, BaseFieldQuery<F, T>) {
        match self {
            Self::InMemory(o) => o.query_for_folded_index(index),
            Self::CosetRecompute(_) => {
                panic!(
                    "query_for_folded_index is only served by the InMemory variant; use query_many"
                )
            }
        }
    }
}

#[derive(Debug)]
pub struct ColumnMajorExtensionOracleForCoset<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
> {
    pub values_normal_order: ColumnMajorCosetBoundTracePart<F, E>, // single column
}

fn offsets_for_leaf_construction<const N: usize>(trace_len: usize) -> [usize; N] {
    assert!(trace_len.is_power_of_two());
    assert!(N.is_power_of_two());
    let mut result = [0; N];
    let stride = trace_len / N;
    for i in 0..N {
        result[i] = stride * i;
    }
    bitreverse_enumeration_inplace(&mut result);

    result
}

pub(crate) fn offsets_vec_for_leaf_construction(trace_len: usize, combine_by: usize) -> Vec<usize> {
    assert!(trace_len.is_power_of_two());
    assert!(combine_by.is_power_of_two());
    let mut result = Vec::with_capacity(combine_by);
    let stride = trace_len / combine_by;
    for i in 0..combine_by {
        result.push(stride * i);
    }
    bitreverse_enumeration_inplace(&mut result);

    result
}

impl<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field>
    ColumnMajorExtensionOracleForCoset<F, E>
{
    pub fn values_for_folded_index(&self, index: usize, values_per_leaf: usize) -> Vec<E> {
        let trace_len = self.values_normal_order.len();
        assert!(values_per_leaf.is_power_of_two());
        assert!(
            index < trace_len / values_per_leaf,
            "folded index {} is too large for a coset of size 2^{} and {} values packed per leaf",
            index,
            trace_len.trailing_zeros(),
            values_per_leaf
        );

        let mut result: Vec<E> = Vec::with_capacity(values_per_leaf);

        match values_per_leaf {
            2 => {
                let offsets = offsets_for_leaf_construction::<2>(trace_len);
                for offset in offsets.iter() {
                    let i = *offset + index;
                    let value = self.values_normal_order.get(i);
                    result.push(value);
                }
            }
            4 => {
                let offsets = offsets_for_leaf_construction::<4>(trace_len);
                for offset in offsets.iter() {
                    let i = *offset + index;
                    let value = self.values_normal_order.get(i);
                    result.push(value);
                }
            }
            8 => {
                let offsets = offsets_for_leaf_construction::<8>(trace_len);
                for offset in offsets.iter() {
                    let i = *offset + index;
                    let value = self.values_normal_order.get(i);
                    result.push(value);
                }
            }
            16 => {
                let offsets = offsets_for_leaf_construction::<16>(trace_len);
                for offset in offsets.iter() {
                    let i = *offset + index;
                    let value = self.values_normal_order.get(i);
                    result.push(value);
                }
            }
            32 => {
                let offsets = offsets_for_leaf_construction::<32>(trace_len);
                for offset in offsets.iter() {
                    let i = *offset + index;
                    let value = self.values_normal_order.get(i);
                    result.push(value);
                }
            }
            a @ _ => {
                panic!("unsupported: {} values per leaf", a);
            }
        }

        result
    }
}

#[derive(Debug)]
pub struct ColumnMajorExtensionOracleForLDE<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
> {
    /// The cosets in EVALUATION form; leaves are converted at query time.
    pub cosets: Vec<ColumnMajorExtensionOracleForCoset<F, E>>,
    pub tree: T,
    pub values_per_leaf: usize,
    pub trace_len_log2: usize,
    /// The leaf encoding the tree committed to.
    pub conv: LeafConversionHandle<F, E>,
    /// Inverses of the cosets' LDE offsets (natural coset order).
    pub coset_offsets_inv: Vec<F>,
    /// `true` when the stored cosets were converted in place (small leaves):
    /// they then hold the committed coefficient leaves and `conv` is the
    /// identity; `false` keeps evaluations and converts at query time.
    pub leaves_in_coefficient_form: bool,
}

impl<
        F: PrimeField + TwoAdicField,
        E: FieldExtension<F> + Field,
        T: ColumnMajorMerkleTreeConstructor<F>,
    > ColumnMajorExtensionOracleForLDE<F, E, T>
{
    /// The leaf at folded index `index` as stored: EVALUATIONS in leaf order
    /// (no conversion, no Merkle proof).
    pub(crate) fn leaf_evaluations(&self, index: usize) -> Vec<E> {
        let num_cosets = self.cosets.len();
        let coset_index = index & (num_cosets - 1);
        let internal_index = index / num_cosets;
        self.cosets[coset_index].values_for_folded_index(internal_index, self.values_per_leaf)
    }

    pub fn query_for_folded_index(
        &self,
        index: usize,
    ) -> (usize, Vec<E>, ExtensionFieldQuery<F, E, T>) {
        let num_cosets = self.cosets.len();
        let coset_index = index & (num_cosets - 1);
        let internal_index = index / num_cosets;
        let coset_tree_size = (1 << self.trace_len_log2) / self.values_per_leaf;
        // the committed (converted) leaf
        let mut values = vec![E::ZERO; self.values_per_leaf];
        self.conv.convert_leaf(
            self.cosets[coset_index]
                .values_normal_order
                .as_contiguous()
                .expect("contiguous ext oracle column"),
            self.coset_offsets_inv[coset_index],
            internal_index,
            &mut values,
        );

        let coset_dest_index = bitreverse_index(coset_index, num_cosets.trailing_zeros());
        let tree_index = coset_dest_index * coset_tree_size + internal_index;

        let (_leaf_hash, path) = self.tree.get_proof(tree_index);
        let query = ExtensionFieldQuery {
            index: tree_index,
            leaf_values_concatenated: values.clone(),
            path,
            _marker: core::marker::PhantomData,
        };
        (coset_index, values, query)
    }
}

/// Selects how `whir_fold` materializes each intermediate (folded) RS oracle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WhirIntermediateOracleMode {
    /// Build the whole `ColumnMajorExtensionOracleForLDE` (the entire RS codeword,
    /// one boxed allocation per coset).
    Monolithic,
    /// Coset-by-coset: keep only the folded monomial form and recompute the coset a
    /// query lands in (memory-light; see `coset_commit::CosetByCosetExtCommitment`).
    CosetByCoset,
    /// The whole RS codeword in ONE contiguous buffer
    /// ([`ContinuousExtensionOracleForLDE`]): same data and byte-identical
    /// commitment as [`Self::Monolithic`], but a single allocation and a
    /// bounded task grid — the per-coset boxing of `Monolithic` dominates the
    /// LDE wall time for huge-LDE oracles (a tiny polynomial across millions
    /// of cosets).
    InMemoryContinuous,
}

/// The buffer-continuous twin of [`ColumnMajorExtensionOracleForLDE`]: all
/// LDE cosets live in ONE contiguous allocation (coset-major, each coset in
/// natural order, leaf coeff-conversion applied), with the per-coset
/// multiplicative offsets alongside. Serves the same accesses — coset slices,
/// tree construction, folded-index queries — with byte-identical results.
#[derive(Debug)]
pub struct ContinuousExtensionOracleForLDE<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
> {
    /// `lde_factor * 2^trace_len_log2` elements, coset-major, EVALUATION
    /// form (leaves are converted at query time).
    pub buffer: Box<[E]>,
    /// Per-coset multiplicative offsets, natural coset order.
    pub coset_offsets: Vec<F>,
    /// log2 of one coset (the folded polynomial size).
    pub trace_len_log2: usize,
    pub tree: T,
    pub values_per_leaf: usize,
    /// The leaf encoding the tree committed to.
    pub conv: LeafConversionHandle<F, E>,
    /// Inverses of `coset_offsets`.
    pub coset_offsets_inv: Vec<F>,
    /// `true` when the buffer was converted in place (small leaves): it then
    /// holds the committed coefficient leaves and `conv` is the identity.
    pub leaves_in_coefficient_form: bool,
}

impl<
        F: PrimeField + TwoAdicField,
        E: FieldExtension<F> + Field,
        T: ColumnMajorMerkleTreeConstructor<F>,
    > ContinuousExtensionOracleForLDE<F, E, T>
{
    pub fn num_cosets(&self) -> usize {
        self.coset_offsets.len()
    }

    /// The `coset_index`-th coset's values (natural order within the coset).
    pub fn coset(&self, coset_index: usize) -> &[E] {
        let n = 1usize << self.trace_len_log2;
        &self.buffer[coset_index * n..(coset_index + 1) * n]
    }

    /// Same leaf gathering as
    /// [`ColumnMajorExtensionOracleForCoset::values_for_folded_index`], over a
    /// coset slice.
    fn values_for_folded_index(coset: &[E], index: usize, values_per_leaf: usize) -> Vec<E> {
        let trace_len = coset.len();
        assert!(values_per_leaf.is_power_of_two());
        assert!(
            index < trace_len / values_per_leaf,
            "folded index {} is too large for a coset of size 2^{} and {} values packed per leaf",
            index,
            trace_len.trailing_zeros(),
            values_per_leaf
        );
        let offsets = offsets_vec_for_leaf_construction(trace_len, values_per_leaf);
        offsets.iter().map(|offset| coset[offset + index]).collect()
    }

    /// The leaf at folded index `index` as stored: EVALUATIONS in leaf order
    /// (no conversion, no Merkle proof).
    pub(crate) fn leaf_evaluations(&self, index: usize) -> Vec<E> {
        let num_cosets = self.num_cosets();
        let coset_index = index & (num_cosets - 1);
        let internal_index = index / num_cosets;
        Self::values_for_folded_index(
            self.coset(coset_index),
            internal_index,
            self.values_per_leaf,
        )
    }

    /// Identical to [`ColumnMajorExtensionOracleForLDE::query_for_folded_index`].
    pub fn query_for_folded_index(
        &self,
        index: usize,
    ) -> (usize, Vec<E>, ExtensionFieldQuery<F, E, T>) {
        let num_cosets = self.num_cosets();
        let coset_index = index & (num_cosets - 1);
        let internal_index = index / num_cosets;
        let coset_tree_size = (1 << self.trace_len_log2) / self.values_per_leaf;
        // the committed (converted) leaf
        let mut values = vec![E::ZERO; self.values_per_leaf];
        self.conv.convert_leaf(
            self.coset(coset_index),
            self.coset_offsets_inv[coset_index],
            internal_index,
            &mut values,
        );

        let coset_dest_index = bitreverse_index(coset_index, num_cosets.trailing_zeros());
        let tree_index = coset_dest_index * coset_tree_size + internal_index;

        let (_leaf_hash, path) = self.tree.get_proof(tree_index);
        let query = ExtensionFieldQuery {
            index: tree_index,
            leaf_values_concatenated: values.clone(),
            path,
            _marker: core::marker::PhantomData,
        };
        (coset_index, values, query)
    }
}

/// Intermediate (folded) WHIR oracle. Like [`ColumnMajorBaseOracleForLDE`], the
/// storage policy is explicit in the variant and each variant is a standalone
/// type:
///
/// * [`Self::Monolithic`] ([`ColumnMajorExtensionOracleForLDE`]) — the whole RS
///   codeword + tree materialized; queries are read from the stored data.
/// * [`Self::CosetRecompute`] ([`CosetByCosetExtCommitment`]) — only the folded
///   monomial form + the small top tree; query batches are served by grouping
///   over coset groups, recomputing each touched group's LDE + subtree exactly
///   once.
///
/// Both variants produce byte-identical commitments and proofs.
enum IntermediateOracle<F, E, T>
where
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
{
    Monolithic(ColumnMajorExtensionOracleForLDE<F, E, T>),
    InMemoryContinuous(ContinuousExtensionOracleForLDE<F, E, T>),
    /// The limb columns LDE'd through the base-column pipeline, leaves
    /// assembled on access (same tree as the in-memory variants).
    ByCoefficient(by_coefficient::ByCoefficientExtOracle<F, E, T>),
    CosetRecompute(coset_commit::CosetByCosetExtCommitment<F, E, T>),
}

impl<F, E, T> IntermediateOracle<F, E, T>
where
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
    [(); E::DEGREE]: Sized,
{
    /// Number of LDE cosets (sizes the next round's query domain).
    fn num_cosets(&self) -> usize {
        match self {
            Self::Monolithic(oracle) => oracle.cosets.len(),
            Self::InMemoryContinuous(oracle) => oracle.num_cosets(),
            Self::ByCoefficient(oracle) => oracle.num_cosets(),
            Self::CosetRecompute(c) => c.lde_factor,
        }
    }

    /// Done with this oracle: pooled storage goes back to `pool`.
    fn release_into(self, pool: &dyn AllocationPool<F, E>) {
        match self {
            Self::ByCoefficient(oracle) => oracle.release_into(pool),
            other => drop(other),
        }
    }

    /// The leaf at folded index `index` without a Merkle proof, for the
    /// symbolic in-domain terms (they read the CURRENT oracle only): the
    /// in-memory oracles hand out their EVALUATIONS (`false`), the recompute
    /// variant its coefficient-form leaf (`true`). `twiddles`/`worker` serve
    /// the recompute variant only.
    fn leaf_evaluations(
        &self,
        index: usize,
        twiddles: &Twiddles<F, Global>,
        worker: &Worker,
    ) -> (Vec<E>, bool) {
        match self {
            Self::Monolithic(oracle) => (
                oracle.leaf_evaluations(index),
                oracle.leaves_in_coefficient_form,
            ),
            Self::InMemoryContinuous(oracle) => (
                oracle.leaf_evaluations(index),
                oracle.leaves_in_coefficient_form,
            ),
            Self::ByCoefficient(oracle) => (oracle.leaf_evaluations(index), false),
            Self::CosetRecompute(c) => (c.query(index, twiddles, worker).1, true),
        }
    }

    /// Serve a batch of this round's queries at once (per query the same tuple as
    /// [`ColumnMajorExtensionOracleForLDE::query_for_folded_index`]), results in
    /// input order. `twiddles`/`worker` are used by the recompute variant only.
    fn query_many(
        &self,
        query_indices: &[usize],
        twiddles: &Twiddles<F, Global>,
        worker: &Worker,
    ) -> Vec<(usize, Vec<E>, ExtensionFieldQuery<F, E, T>)> {
        match self {
            Self::Monolithic(oracle) => query_indices
                .iter()
                .map(|&qi| oracle.query_for_folded_index(qi))
                .collect(),
            Self::InMemoryContinuous(oracle) => query_indices
                .iter()
                .map(|&qi| oracle.query_for_folded_index(qi))
                .collect(),
            Self::ByCoefficient(oracle) => query_indices
                .iter()
                .map(|&qi| oracle.query_for_folded_index(qi))
                .collect(),
            Self::CosetRecompute(c) => c.query_many(query_indices, twiddles, worker),
        }
    }
}

/// (LDE, tree) wall times of an in-memory oracle build.
type OracleBuildSplit = Option<(std::time::Duration, std::time::Duration)>;

fn format_build_split(split: OracleBuildSplit) -> String {
    match split {
        Some((lde, tree)) => format!("LDE {:.3?}, tree {:.3?}, ", lde, tree),
        None => String::new(),
    }
}

/// Build the intermediate oracle for a folded polynomial (`monomial_form` and
/// `evaluation_form` are the same polynomial: the by-coefficient path LDEs the
/// evaluations, the others the monomials), returning its Merkle cap (to
/// commit), the oracle and the LDE/tree time split (in-memory modes).
fn build_intermediate_oracle<F, E, T, B: crate::gkr::prover::backend::Backend<F, E>>(
    backend: &B,
    monomial_form: &[E],
    evaluation_form: &[E],
    lde_factor: usize,
    values_per_leaf: usize,
    tree_cap_size: usize,
    mode: WhirIntermediateOracleMode,
    twiddles: &B::TwiddleSet,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) -> (
    MerkleTreeCapVarLength,
    IntermediateOracle<F, E, T>,
    OracleBuildSplit,
)
where
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
    [(); E::DEGREE]: Sized,
{
    assert_eq!(monomial_form.len(), evaluation_form.len());
    match mode {
        WhirIntermediateOracleMode::Monolithic => {
            let t_lde = std::time::Instant::now();
            let rs = backend.lde_ext_poly_from_monomial_form(
                monomial_form,
                twiddles,
                lde_factor,
                pool,
                worker,
            );
            let t_lde = t_lde.elapsed();
            let t_tree = std::time::Instant::now();
            let oracle = commit_single_ext_poly::<F, E, T, B>(
                rs,
                values_per_leaf,
                tree_cap_size,
                backend,
                worker,
            );
            let t_tree = t_tree.elapsed();
            let cap = oracle.tree.get_cap();
            (
                cap,
                IntermediateOracle::Monolithic(oracle),
                Some((t_lde, t_tree)),
            )
        }
        WhirIntermediateOracleMode::InMemoryContinuous => {
            // the by-coefficient path: the backend's fast base-column LDE
            // length is twice this polynomial, and the leaves are large
            // enough for the fused (hash-time) conversion
            if let Some(len) = backend.by_coefficient_lde_len() {
                if 2 * evaluation_form.len() == len
                    && lde_factor >= 2
                    && values_per_leaf >= FUSED_LEAF_CONVERSION_MIN_VALUES_PER_LEAF
                {
                    let (oracle, t_lde, t_tree) = by_coefficient::commit_by_coefficient::<F, E, T, B>(
                        evaluation_form,
                        lde_factor,
                        values_per_leaf,
                        tree_cap_size,
                        backend,
                        twiddles,
                        pool,
                        worker,
                    );
                    let cap = oracle.tree.get_cap();
                    return (
                        cap,
                        IntermediateOracle::ByCoefficient(oracle),
                        Some((t_lde, t_tree)),
                    );
                }
            }
            let t_lde = std::time::Instant::now();
            let (buffer, coset_offsets) = backend.lde_ext_poly_from_monomial_form_continuous(
                monomial_form,
                twiddles,
                lde_factor,
                pool,
                worker,
            );
            let t_lde = t_lde.elapsed();
            let t_tree = std::time::Instant::now();
            let oracle = commit_single_ext_poly_continuous::<F, E, T, B>(
                buffer,
                coset_offsets,
                values_per_leaf,
                tree_cap_size,
                backend,
                worker,
            );
            let t_tree = t_tree.elapsed();
            let cap = oracle.tree.get_cap();
            (
                cap,
                IntermediateOracle::InMemoryContinuous(oracle),
                Some((t_lde, t_tree)),
            )
        }
        WhirIntermediateOracleMode::CosetByCoset => {
            let commitment = coset_commit::CosetByCosetExtCommitment::<F, E, T>::commit(
                monomial_form,
                twiddles.plain(),
                lde_factor,
                values_per_leaf,
                tree_cap_size,
                worker,
            );
            let cap = commitment.get_cap();
            (cap, IntermediateOracle::CosetRecompute(commitment), None)
        }
    }
}

pub fn whir_fold<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
    TR: Transcript<F, E>,
    B: crate::gkr::prover::backend::Backend<F, E>,
    GB: crate::gkr::prover::gkr_backend::GKRBackend<F, E>,
>(
    mem_oracle: ColumnMajorBaseOracleForLDE<F, T>,
    mem_polys_claims: Vec<E>,
    wit_oracle: ColumnMajorBaseOracleForLDE<F, T>,
    wit_polys_claims: Vec<E>,
    setup: &crate::gkr::prover::SetupCommitment<F, T>,
    setup_polys_claims: Vec<E>,
    // The GKR storage, CONSUMED: its base layer holds the committed columns'
    // hypercube evaluations the batched proximity polynomial is accumulated
    // from; it is released to `pool` right after.
    gkr_storage: GKRStorage<F, E>,
    // log2 of the packing factor of the base commitments (0 = unpacked):
    // `trace_len_log2 - pack_log2` is the base-layer column length.
    pack_log2: usize,
    original_evaluation_point: Vec<E>,
    batching_challenge: E,
    whir_schedule: &WhirSchedule,
    twiddles: &B::TwiddleSet,
    mut transcript_seed: TR::Seed,
    tree_cap_size: usize,
    trace_len_log2: usize,
    // Compute backend for the in-memory-path heavy ops (intermediate-oracle LDEs,
    // the batched poly's hypercube -> monomial transform). The backend must not
    // change any produced values.
    backend: &B,
    // The GKR backend's vector kernels for the WHIR-side passes: the base
    // column accumulation and the LSB folds (the eq poly and the batched
    // poly's evaluation form).
    gkr_backend: &GB,
    // How to materialize each intermediate (folded) RS oracle. Independent from the
    // storage policy of the base oracles: the base oracles carry their own policy in
    // their `ColumnMajorBaseOracleForLDE` variant, so e.g. recompute-based base
    // oracles can be combined with fully materialized intermediate oracles.
    intermediate_oracle_mode: WhirIntermediateOracleMode,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) -> WhirPolyCommitProof<F, E, T>
where
    [(); F::DEGREE]: Sized,
    [(); E::DEGREE]: Sized,
{
    let two_inv = F::TWO.inverse().unwrap();

    let evals_refs = [&mem_polys_claims, &wit_polys_claims, &setup_polys_claims];
    // Per-set accessors (0 = memory, 1 = witness, 2 = setup). The setup set is served
    // through `SetupCommitment` (in-memory oracle enum, or the on-disk source); the
    // memory/witness sets carry their storage policy in their oracle enum variant.
    let set_num_columns = [
        mem_oracle.num_columns(),
        wit_oracle.num_columns(),
        setup.num_columns(),
    ];
    let set_caps = [mem_oracle.get_cap(), wit_oracle.get_cap(), setup.get_cap()];

    let t_eq_init = std::time::Instant::now();
    let mut eq_pp = {
        assert_eq!(
            original_evaluation_point.len(),
            trace_len_log2,
            "claim coordinate must have one entry per variable"
        );
        // scalar points are stored in VARIABLE order (LSB round order); the
        // table lives in a pooled ping-pong buffer pair and every fold writes
        // the other buffer (no in-place compaction), see `ping_pong`
        PingPongPoly::<E>::new_ext::<F>(1usize << trace_len_log2, pool, |dst| {
            crate::gkr::sumcheck::eq_poly::fill_eq_table_lsb_first_uninit::<E>(
                &original_evaluation_point[..],
                dst,
                worker,
            )
        })
    };
    // in-domain query terms, kept symbolically (see `in_domain`)
    let mut in_domain = InDomainTerms::<F, E>::new();
    println!(
        "  [timing] initial eq-poly build: {:.3?}",
        t_eq_init.elapsed()
    );

    let mut commitments = Vec::with_capacity(3);
    for (i, cap) in set_caps.into_iter().enumerate() {
        let t = WhirBaseLayerCommitmentAndQueries {
            commitment: WhirCommitment {
                cap,
                _marker: core::marker::PhantomData,
            },
            num_columns: set_num_columns[i],
            evals: evals_refs[i].clone(),
            queries: vec![],
        };
        commitments.push(t);
    }

    let [memory_commitment, witness_commitment, setup_commitment] = commitments.try_into().unwrap();

    let mut proof = WhirPolyCommitProof {
        witness_commitment,
        memory_commitment,
        setup_commitment,
        sumcheck_polys: vec![],
        intermediate_whir_oracles: Vec::with_capacity(whir_schedule.whir_steps_lde_factors.len()),
        ood_samples: vec![],
        pow_nonces: vec![],
        final_monomials: vec![],
        whir_schedule: whir_schedule.clone(),
        // GKR->WHIR handoff values (see WhirPolyCommitProof). `batched_opening` is filled once
        // `batched_claim` is computed below.
        batching_challenge: Some(batching_challenge),
        original_evaluation_point: Some(original_evaluation_point.clone()),
        batched_opening: None,
    };

    let mut final_poly_log2 = trace_len_log2;
    for el in whir_schedule.whir_steps_schedule.iter() {
        assert!(*el <= final_poly_log2);
        final_poly_log2 -= *el;
    }

    assert!(whir_schedule.base_lde_factor.is_power_of_two());
    let num_whir_steps = whir_schedule.whir_steps_lde_factors.len();
    assert_eq!(
        whir_schedule.whir_steps_schedule.len(),
        whir_schedule.whir_steps_lde_factors.len() + 1
    );
    assert_eq!(
        whir_schedule.whir_steps_schedule.len(),
        whir_schedule.whir_queries_schedule.len()
    );
    assert_eq!(
        whir_schedule.whir_steps_schedule.len(),
        whir_schedule.whir_pow_schedule.len()
    );

    let mut rs_oracle;

    // first compute batched poly. We do compute it on main domain only, and then FFT,
    // especially if we are going to offload cosets from the original commitment to disk instead of keeping in RAM

    let total_base_oracles: usize = set_num_columns.iter().sum();
    assert_eq!(
        total_base_oracles,
        evals_refs.iter().map(|el| el.len()).sum::<usize>()
    );
    for (a, b) in set_num_columns.iter().zip(evals_refs.iter()) {
        assert_eq!(*a, b.len());
    }

    let challenge_powers = materialize_powers_serial_starting_with_one::<E, Global>(
        batching_challenge,
        total_base_oracles,
    );

    let (base_mem_powers, rest) = challenge_powers.split_at(evals_refs[0].len());
    let (base_witness_powers, base_setup_powers) = rest.split_at(evals_refs[1].len());
    assert_eq!(base_setup_powers.len(), evals_refs[2].len());

    let batch_challenges = [
        base_mem_powers.to_vec(),
        base_witness_powers.to_vec(),
        base_setup_powers.to_vec(),
    ];

    println!("Computing batched poly for proximity testing");
    let t_batching = std::time::Instant::now();
    // The batched proximity polynomial straight from the base layer: the
    // committed columns' hypercube evaluations weighted by the powers of the
    // batching challenge (no codeword batching / IFFT round trip). The
    // columns come in commitment order — memory then witness (one committed
    // set when the commitment merged them, two otherwise: the same sequence
    // either way), then setup; virtual setup polys are not committed. Each
    // set is packed by `2^pack_log2` consecutive columns into one committed
    // column (sub-poly `y` of a pack is block `y` of the packed poly) and the
    // batching powers run over the COMMITTED columns.
    let base_len = 1usize << (trace_len_log2 - pack_log2);
    let pack = 1usize << pack_log2;
    let base_columns = |key: fn(usize) -> GKRAddress| -> Vec<&[F]> {
        (0..)
            .map_while(|i| gkr_storage.try_get_base_poly(key(i)))
            .collect()
    };
    let mut mem_wit_columns = base_columns(GKRAddress::BaseLayerMemory);
    mem_wit_columns.extend(base_columns(GKRAddress::BaseLayerWitness));
    let setup_columns = base_columns(GKRAddress::Setup);
    let mut terms: Vec<BatchedBaseColumn<'_, F, E>> =
        Vec::with_capacity(mem_wit_columns.len() + setup_columns.len());
    let mut committed = 0usize;
    for set in [&mem_wit_columns, &setup_columns] {
        for (c, column) in set.iter().enumerate() {
            assert_eq!(column.len(), base_len, "base-layer column length");
            terms.push(BatchedBaseColumn {
                column,
                power: challenge_powers[committed + c / pack],
                dst_offset: (c % pack) * base_len,
            });
        }
        committed += set.len().div_ceil(pack);
    }
    assert_eq!(
        committed, total_base_oracles,
        "one committed (packed) column per group of base-layer columns"
    );

    #[cfg(feature = "gkr_self_checks")]
    if pack_log2 == 0 {
        use crate::gkr::sumcheck::eq_poly::evaluate_with_precomputed_eq;
        // every claim is its base column's multilinear evaluation at the claim point
        let claims: Vec<E> = evals_refs.iter().flat_map(|c| c.iter().copied()).collect();
        assert_eq!(claims.len(), terms.len());
        for (i, (term, claim)) in terms.iter().zip(claims.iter()).enumerate() {
            let recomputed = evaluate_with_precomputed_eq::<F, E>(term.column, eq_pp.as_slice());
            assert_eq!(
                recomputed, *claim,
                "claim recomputation diverged for base column {i}"
            );
        }
    }

    // the evaluation form lives in a pooled ping-pong buffer pair: every LSB
    // fold writes the other buffer through the backend's kernel
    let mut evals_pp = PingPongPoly::<E>::new_ext::<F>(1usize << trace_len_log2, pool, |dst| {
        gkr_backend.accumulate_base_columns_into(dst, &terms, worker)
    });
    drop(terms);
    drop(mem_wit_columns);
    drop(setup_columns);
    let t_release = std::time::Instant::now();
    gkr_storage.release_into(pool);
    println!(
        "  [timing] gkr_storage release: {:.3?}",
        t_release.elapsed()
    );
    let mut sumchecked_poly_monomial_form =
        backend.monomial_form_from_hypercube_evals(evals_pp.as_slice(), worker);
    assert_eq!(sumchecked_poly_monomial_form.len(), 1 << trace_len_log2);
    println!(
        "  [timing] batching stage (base columns -> hypercube evals -> monomials): {:.3?}",
        t_batching.elapsed()
    );
    let t_round = std::time::Instant::now();

    let mut batched_claim = E::ZERO;
    for (challenges_set, values_set) in [base_mem_powers, base_witness_powers, base_setup_powers]
        .into_iter()
        .zip(evals_refs.into_iter())
    {
        assert_eq!(challenges_set.len(), values_set.len());
        for (a, b) in challenges_set.iter().zip(values_set.into_iter()) {
            let mut result = *b;
            result.mul_assign(&a);
            batched_claim.add_assign(&result);
        }
    }
    // Record the initial batched opening (= the committed-state `batched_opening`) so a
    // verifier-calldata serializer needn't recompute it from the transcript replay.
    proof.batched_opening = Some(batched_claim);
    drop(mem_polys_claims);
    drop(wit_polys_claims);
    drop(setup_polys_claims);

    let mut query_references = vec![];

    // our initial sumcheck claim is `batched_claim` = \sum_{hypercube} eq(x, `original_evaluation_point`) batched_poly(x)

    let num_rounds = whir_schedule.whir_steps_schedule.len();
    assert!(num_rounds >= 2);

    let mut whir_steps_schedule = whir_schedule.whir_steps_schedule.iter().peekable();
    let mut whir_queries_schedule = whir_schedule.whir_queries_schedule.iter();
    let mut whir_steps_lde_factors = whir_schedule.whir_steps_lde_factors.iter();
    let mut whir_pow_schedule = whir_schedule.whir_pow_schedule.iter();

    // as we will eventually continue to mix-in additional equality polys into sumcheck kernel,
    // so we can NOT easily use the same trick with splitting out eq poly highest coordinate in sumcheck.
    // So we make EQ poly explicitly, and then we will update it after every step, and use naively

    let mut monomial_form_buffer = Vec::with_capacity(sumchecked_poly_monomial_form.len());

    let mut claim = batched_claim;

    #[cfg(feature = "gkr_self_checks")]
    {
        let recomputed_claim = dot_product(evals_pp.as_slice(), eq_pp.as_slice(), worker);
        assert_eq!(recomputed_claim, claim);
    }

    assert_eq!(eq_pp.len(), evals_pp.len());
    assert_eq!(eq_pp.len(), sumchecked_poly_monomial_form.len());

    let mut folding_challenges = vec![];
    let mut delinearization_challenges_per_round = vec![];

    let mut poly_size_log2 = trace_len_log2;

    // initial round where we fold and query existing oracles
    {
        let num_initial_folding_rounds = *whir_steps_schedule.next().unwrap();
        let num_queries = *whir_queries_schedule.next().unwrap();
        let pow_bits = *whir_pow_schedule.next().unwrap();
        println!("Initial round: fold by {}", 1 << num_initial_folding_rounds);

        assert!(num_initial_folding_rounds <= poly_size_log2);
        let rs_domain_log2 =
            trace_len_log2 + (whir_schedule.base_lde_factor.trailing_zeros() as usize);
        let query_domain_log2 = rs_domain_log2 - num_initial_folding_rounds;

        // Even though we can do all the same trick as in our GKR kernels and only evaluate sum of half-size,
        // instead we naively evaluate at 0 and 1, and use input claim to get the monomial form via Lagrange interpolation

        assert_eq!(
            mem_oracle.values_per_leaf(),
            1 << num_initial_folding_rounds
        );
        assert_eq!(
            wit_oracle.values_per_leaf(),
            1 << num_initial_folding_rounds
        );
        assert_eq!(setup.values_per_leaf(), 1 << num_initial_folding_rounds);
        let mut folding_challenges_in_round = vec![];
        println!(
            "  running sumcheck for {} rounds...",
            num_initial_folding_rounds
        );
        let t_sumcheck = std::time::Instant::now();
        // the in-domain terms only appear with this round's queries, after
        // this sumcheck; none exist yet
        assert_eq!(in_domain.len(), 0);
        for _ in 0..num_initial_folding_rounds {
            let (f0, f1, f_half) =
                special_three_point_eval(evals_pp.as_slice(), eq_pp.as_slice(), worker);
            let evaluation_point = E::from_base(two_inv);
            let univariate_coeffs = special_lagrange_interpolate(f0, f1, f_half, evaluation_point);
            // commit
            proof.sumcheck_polys.push(univariate_coeffs);
            commit_field_els::<F, E, TR>(&mut transcript_seed, &univariate_coeffs);

            #[cfg(feature = "gkr_self_checks")]
            {
                let s0 = evaluate_small_univariate_poly(&univariate_coeffs, &E::ZERO);
                assert_eq!(s0, f0);
                let s1 = evaluate_small_univariate_poly(&univariate_coeffs, &E::ONE);
                assert_eq!(s1, f1);
                let s_half = evaluate_small_univariate_poly(&univariate_coeffs, &evaluation_point);
                assert_eq!(s_half, f_half);
                let mut v = s0;
                v.add_assign(&s1);
                assert_eq!(v, claim);
            }

            // draw folding challenge
            let folding_challenges = draw_random_field_els::<F, E, TR>(&mut transcript_seed, 1);
            let folding_challenge = folding_challenges[0];
            folding_challenges_in_round.push(folding_challenge);

            let next_claim = evaluate_small_univariate_poly(&univariate_coeffs, &folding_challenge);
            claim = next_claim;
            // and fold the poly itself - both multivariate evals mapping, and monomial form

            fold_monomial_form(
                &mut sumchecked_poly_monomial_form,
                &mut monomial_form_buffer,
                &folding_challenge,
                worker,
            );

            evals_pp.fold::<F, GB>(&folding_challenge, gkr_backend, worker);

            assert_eq!(sumchecked_poly_monomial_form.len(), evals_pp.len());

            #[cfg(feature = "gkr_self_checks")]
            {
                let mut source = sumchecked_poly_monomial_form.clone();
                multivariate_coeffs_into_hypercube_evals(
                    &mut source,
                    sumchecked_poly_monomial_form.len().trailing_zeros(),
                );
                assert_eq!(&source[..], evals_pp.as_slice());
            }

            // and so we fold equality poly too
            eq_pp.fold::<F, GB>(&folding_challenge, gkr_backend, worker);
            assert_eq!(evals_pp.len(), eq_pp.len());
        }
        println!(
            "  [timing] round sumcheck+eq folds: {:.3?}",
            t_sumcheck.elapsed()
        );
        poly_size_log2 -= num_initial_folding_rounds;

        assert_eq!(evals_pp.len(), 1 << poly_size_log2);
        assert_eq!(sumchecked_poly_monomial_form.len(), 1 << poly_size_log2);
        assert_eq!(eq_pp.len(), 1 << poly_size_log2);

        #[cfg(feature = "gkr_self_checks")]
        {
            let mut full_sum = dot_product(evals_pp.as_slice(), eq_pp.as_slice(), worker);
            full_sum.add_assign(&in_domain.sum_at_current());
            assert_eq!(full_sum, claim);
        }

        folding_challenges.push(folding_challenges_in_round.clone());

        // compute RS for folded one (we will NOT query it this round)
        println!("  computing next RS code word oracle...");
        {
            let lde_factor = *whir_steps_lde_factors.next().unwrap();
            let next_folding_steps = *whir_steps_schedule.peek().unwrap();
            let t_build = std::time::Instant::now();
            let (cap, next_oracle, split) = build_intermediate_oracle::<F, E, T, B>(
                backend,
                &sumchecked_poly_monomial_form,
                evals_pp.as_slice(),
                lde_factor,
                1 << next_folding_steps,
                tree_cap_size,
                intermediate_oracle_mode,
                twiddles,
                pool,
                worker,
            );
            println!(
                "  [timing] intermediate oracle 0: poly 2^{}, lde {} -> {}built in {:.3?}",
                poly_size_log2,
                lde_factor,
                format_build_split(split),
                t_build.elapsed()
            );
            let c = WhirIntermediateCommitmentAndQueries {
                commitment: WhirCommitment {
                    cap,
                    _marker: core::marker::PhantomData,
                },
                queries: vec![],
            };
            add_whir_commitment_to_transcript::<F, E, TR, T>(&mut transcript_seed, &c.commitment);
            proof.intermediate_whir_oracles.push(c);
            rs_oracle = next_oracle;
        }

        let mut contributions_to_eq_poly = vec![];

        // draw OOD sample
        let ood_points: Vec<E> = draw_random_field_els::<F, E, TR>(&mut transcript_seed, 1);
        let ood_point = ood_points[0];
        // compute OOD value
        let ood_value = {
            let t_ood = std::time::Instant::now();
            let v = evaluate_monomial_form(&sumchecked_poly_monomial_form[..], &ood_point, worker);
            println!("  [timing] OOD evaluation: {:.3?}", t_ood.elapsed());
            v
        };
        commit_field_els::<F, E, TR>(&mut transcript_seed, &[ood_value]);
        #[cfg(feature = "gkr_self_checks")]
        {
            let pows = make_pows(ood_point, evals_pp.len().trailing_zeros() as usize);
            let value = evaluate_multivariate(evals_pp.as_slice(), &pows, worker);
            assert_eq!(value, ood_value);
        }

        proof.ood_samples.push(ood_value);

        // now can draw challenges

        // and we can immediately query all the original oracles, and drop them. For that we need to draw indexes
        let query_domain_size = 1u64 << query_domain_log2;

        let query_domain_generator = domain_generator_for_size::<F>(query_domain_size);
        let input_domain_size = 1u64 << rs_domain_log2;
        let extended_generator = domain_generator_for_size::<F>(input_domain_size);

        // Leaf folding for this round's base-oracle queries: encoding choice,
        // tables and scratch all live inside the folder.
        let mut round0_folder =
            QueryFolder::<F, E>::new(num_initial_folding_rounds, &folding_challenges_in_round);

        let query_index_bits = query_domain_size.trailing_zeros() as usize;
        let num_bits_for_queries = num_queries * query_index_bits;
        if pow_bits > 0 {
            println!("  grinding {pow_bits}-bit PoW ({num_queries} queries)...");
        }
        let t_pow = std::time::Instant::now();
        let (nonce, mut bit_source) = draw_query_bits::<F, E, TR>(
            &mut transcript_seed,
            num_bits_for_queries,
            pow_bits,
            worker,
        );
        println!(
            "  [timing] PoW grind ({pow_bits} bits): {:.3?}",
            t_pow.elapsed()
        );
        proof.pow_nonces.push(nonce);
        println!("  generating {num_queries} query indexes...");
        let mut query_indexes = vec![];
        for _ in 0..num_queries {
            // query index is power for omega^k expression, where omega^{`input_domain_size`} == 1
            let query_index = assemble_query_index(query_index_bits, &mut bit_source);
            query_indexes.push(query_index);
        }

        // and delinearization challenge
        let delinearization_challenges: Vec<E> =
            draw_random_field_els::<F, E, TR>(&mut transcript_seed, 1);
        let delinearization_challenge = delinearization_challenges[0];
        delinearization_challenges_per_round.push(delinearization_challenge);

        // we will have OOD sample contribution
        contributions_to_eq_poly.push((ood_point, delinearization_challenge));

        let mut claim_correction = E::ZERO;
        {
            let mut t = ood_value;
            t.mul_assign(&delinearization_challenge);
            claim_correction.add_assign(&t);
        }
        let mut current_delinearization_challenge = delinearization_challenge;
        current_delinearization_challenge.square();

        // Request ALL round-0 queries from every base oracle at once. A recompute
        // oracle groups them by the coset they land in and rebuilds each touched
        // coset (RS codeword + subtree) exactly once; results come back in query
        // order. The per-query loop below then consumes them in the same unsorted
        // query-index order as before, so proof layout and transcript are
        // unchanged.
        println!("  drawing {num_queries} queries...");
        let t_queries = std::time::Instant::now();
        let mut set_query_iters: [Option<std::vec::IntoIter<(Vec<Vec<F>>, BaseFieldQuery<F, T>)>>;
            3] = [
            (set_num_columns[0] > 0).then(|| {
                mem_oracle
                    .query_many(&query_indexes, twiddles.plain(), worker)
                    .into_iter()
            }),
            (set_num_columns[1] > 0).then(|| {
                wit_oracle
                    .query_many(&query_indexes, twiddles.plain(), worker)
                    .into_iter()
            }),
            (set_num_columns[2] > 0).then(|| {
                setup
                    .query_many(&query_indexes, twiddles.plain(), worker)
                    .into_iter()
            }),
        ];

        println!(
            "  [timing] round-0 base queries ({num_queries}) served in {:.3?}",
            t_queries.elapsed()
        );

        // Every round-0 query has been served: the (potentially large) base
        // oracles can be dropped before the memory-heavy folding rounds. For
        // fully in-memory base oracles this deallocates hundreds of GB —
        // seconds of page-table teardown — so the drop runs on a DETACHED
        // thread and overlaps the folding rounds instead of stalling them.
        // Pooled codeword buffers go back to the pool (a shared handle, so
        // the release can run on the detached thread too).
        let release_pool = pool.share();
        std::thread::spawn(move || {
            mem_oracle.release_into(&*release_pool);
            wit_oracle.release_into(&*release_pool);
        });
        println!("  [timing] base oracle drop offloaded to background thread");

        for &query_index in query_indexes.iter() {
            assert!(query_index < query_domain_size as usize);
            let query_point = query_domain_generator.pow(query_index as u32);

            // we have a query point, and now we need to understand "preimages" for it
            // assume that we have a query point omega_q ^ i, and we fold K times.
            // Then what we need is a set of points omega^{0 << (log(query_domain)) || i }, omega^{1 << (log(query_domain)) || i}, etc
            // where omega = root(omega_q, 2^K)

            // So for "base root" we take omega^i from the notations above, and when we fold we multiply it by root(1, 2^K)

            // get original leaf, compute batched, and then folded value
            let base_root = extended_generator.pow(query_index as u32);
            let base_root_inv = base_root.inverse().unwrap();
            let mut batched_evals = vec![E::ZERO; 1 << num_initial_folding_rounds];
            for (set_idx, batching_challenges) in batch_challenges.iter().enumerate() {
                if let Some(set_queries) = set_query_iters[set_idx].as_mut() {
                    let (leaf, query) = set_queries.next().unwrap();
                    match set_idx {
                        0 => {
                            proof.memory_commitment.queries.push(query);
                        }
                        1 => {
                            proof.witness_commitment.queries.push(query);
                        }
                        2 => {
                            proof.setup_commitment.queries.push(query);
                        }
                        _ => {
                            unreachable!()
                        }
                    }
                    assert_eq!(batched_evals.len(), leaf.len());
                    for (dst, src) in batched_evals.iter_mut().zip(leaf.iter()) {
                        assert_eq!(src.len(), batching_challenges.len());
                        for (a, b) in src.iter().zip(batching_challenges.iter()) {
                            let mut t = *b;
                            t.mul_assign_by_base(a);
                            dst.add_assign(&t);
                        }
                    }
                }
            }

            let folded = round0_folder.fold_eval_leaf(batched_evals, &base_root_inv);

            query_references.push((query_index, query_point, folded));

            // and add into sumcheck claim
            in_domain.add(
                query_point,
                query_index,
                query_domain_log2,
                current_delinearization_challenge,
            );
            {
                let mut t = folded;
                t.mul_assign(&current_delinearization_challenge);
                claim_correction.add_assign(&t);
            }
            current_delinearization_challenge.mul_assign(&delinearization_challenge);
        }

        #[cfg(feature = "gkr_self_checks")]
        {
            let omega = domain_generator_for_size::<F>(query_domain_size);
            for (i, &query_index) in query_indexes.iter().enumerate() {
                let root = omega.pow(query_index as u32);
                let eval_from_monomial = evaluate_monomial_form(
                    &sumchecked_poly_monomial_form,
                    &E::from_base(root),
                    worker,
                );
                assert_eq!(
                    (query_index, root, eval_from_monomial),
                    query_references[i],
                    "diverged at query {}",
                    i
                );
                let pows = make_pows(root, evals_pp.len().trailing_zeros() as usize);
                let eval_from_multivariate =
                    evaluate_multivariate_at_base(evals_pp.as_slice(), &pows, worker);
                assert_eq!(eval_from_monomial, eval_from_multivariate);
            }
            query_references.clear();
        }
        #[cfg(not(feature = "gkr_self_checks"))]
        query_references.clear();

        // we now update the equality poly - initially we had eq(X, original_evaluation_point), from which we folded few coordinates.
        // Now we should add more terms there to reflect OOD and in-domain samples
        {
            let t_upd = std::time::Instant::now();
            backend.update_eq_poly(eq_pp.as_mut_slice(), &contributions_to_eq_poly, &[], worker);
            println!("  [timing] eq-poly update: {:.3?}", t_upd.elapsed());
        }

        // and remember new sumcheck claim
        claim.add_assign(&claim_correction);
    }

    println!("  [timing] initial round total: {:.3?}", t_round.elapsed());

    let num_internal_whir_steps = num_whir_steps - 1;
    println!(
        "Initial queries and folding are complete, now can proceed into {} internal rounds",
        num_internal_whir_steps
    );

    // now we step into recursive procedure over one batched polynomial and it's evals. Our sequence is
    // - fold
    // - RS code word computation and commit
    // - query previous(!) RS oracle
    // - update claim and eq poly
    for internal_round in 0..num_internal_whir_steps {
        let t_round = std::time::Instant::now();
        // commit
        let num_folding_steps = *whir_steps_schedule.next().unwrap();
        let num_queries = *whir_queries_schedule.next().unwrap();
        let pow_bits = *whir_pow_schedule.next().unwrap();
        assert!(num_folding_steps <= poly_size_log2);

        println!(
            "Internal round {}: fold by {}, {} queries, pow {}",
            internal_round,
            1 << num_folding_steps,
            num_queries,
            pow_bits
        );

        let rs_domain_log2 = poly_size_log2 + (rs_oracle.num_cosets().trailing_zeros() as usize);
        let query_domain_log2 = rs_domain_log2 - num_folding_steps;
        // the symbolic in-domain terms read their leaves of the CURRENT oracle
        in_domain.start_round(num_folding_steps, rs_domain_log2, |i| {
            rs_oracle.leaf_evaluations(i, twiddles.plain(), worker)
        });
        #[cfg(feature = "gkr_self_checks")]
        in_domain.assert_matches_monomial_form(&sumchecked_poly_monomial_form, worker);

        // fold

        // NOTE: we can no longer use the fact that sumcheck kernel is simple as \sum_X eq(r, X) p(X),
        // and so to send degree 2 poly to the verifier we need to compute such kernel at 3 points and interpolate.
        // As our hypercube is 0/1, then we choose to compute at 0, 1 and 1/2

        // eval(1/2) = \sum_{X} multilinear(1/2, X) * p(1/2, X) = 1/4 \sum_{X} (multilinear(1, X) + multilinear(0, X)) * (P(1, X) + P(0, X))

        let mut folding_challenges_in_round = Vec::with_capacity(num_folding_steps);
        println!("  running sumcheck for {} rounds...", num_folding_steps);
        let t_sumcheck = std::time::Instant::now();
        for _ in 0..num_folding_steps {
            let (f0, f1, f_half) =
                special_three_point_eval(evals_pp.as_slice(), eq_pp.as_slice(), worker);
            let evaluation_point = E::from_base(two_inv);
            let mut univariate_coeffs =
                special_lagrange_interpolate(f0, f1, f_half, evaluation_point);
            // the symbolic in-domain terms' degree-2 polynomial, added to the
            // coefficients (the three-point sums above cover the eq table only)
            let in_domain_coeffs = in_domain.univariate_coeffs();
            for (c, d) in univariate_coeffs.iter_mut().zip(in_domain_coeffs.iter()) {
                c.add_assign(d);
            }
            // commit
            proof.sumcheck_polys.push(univariate_coeffs);
            commit_field_els::<F, E, TR>(&mut transcript_seed, &univariate_coeffs);

            #[cfg(feature = "gkr_self_checks")]
            {
                let with_terms = |v: E, t: E| {
                    let mut v = v;
                    v.add_assign(&evaluate_small_univariate_poly(&in_domain_coeffs, &t));
                    v
                };
                let s0 = evaluate_small_univariate_poly(&univariate_coeffs, &E::ZERO);
                assert_eq!(s0, with_terms(f0, E::ZERO));
                let s1 = evaluate_small_univariate_poly(&univariate_coeffs, &E::ONE);
                assert_eq!(s1, with_terms(f1, E::ONE));
                let s_half = evaluate_small_univariate_poly(&univariate_coeffs, &evaluation_point);
                assert_eq!(s_half, with_terms(f_half, evaluation_point));
                let mut v = s0;
                v.add_assign(&s1);
                assert_eq!(v, claim);
            }

            let folding_challenges = draw_random_field_els::<F, E, TR>(&mut transcript_seed, 1);
            let folding_challenge = folding_challenges[0];
            folding_challenges_in_round.push(folding_challenge);

            let next_claim = evaluate_small_univariate_poly(&univariate_coeffs, &folding_challenge);
            claim = next_claim;
            // and fold the poly itself - both multivariate evals mapping, and monomial form

            fold_monomial_form(
                &mut sumchecked_poly_monomial_form,
                &mut monomial_form_buffer,
                &folding_challenge,
                worker,
            );

            evals_pp.fold::<F, GB>(&folding_challenge, gkr_backend, worker);

            assert_eq!(sumchecked_poly_monomial_form.len(), evals_pp.len());
            eq_pp.fold::<F, GB>(&folding_challenge, gkr_backend, worker);
            in_domain.fold(&folding_challenge);
            assert_eq!(evals_pp.len(), eq_pp.len());
        }

        println!(
            "  [timing] round sumcheck+eq folds: {:.3?}",
            t_sumcheck.elapsed()
        );
        poly_size_log2 -= num_folding_steps;

        assert_eq!(evals_pp.len(), 1 << poly_size_log2);
        assert_eq!(sumchecked_poly_monomial_form.len(), 1 << poly_size_log2);
        assert_eq!(eq_pp.len(), 1 << poly_size_log2);

        #[cfg(feature = "gkr_self_checks")]
        {
            let mut full_sum = dot_product(evals_pp.as_slice(), eq_pp.as_slice(), worker);
            full_sum.add_assign(&in_domain.sum_at_current());
            assert_eq!(full_sum, claim);
        }

        // query
        folding_challenges.push(folding_challenges_in_round.clone());

        println!("  computing next RS code word oracle...");
        let rs_oracle_to_query = {
            let lde_factor = *whir_steps_lde_factors.next().unwrap();
            let next_folding_steps = *whir_steps_schedule.peek().unwrap();
            let t_build = std::time::Instant::now();
            let (cap, next_oracle, split) = build_intermediate_oracle::<F, E, T, B>(
                backend,
                &sumchecked_poly_monomial_form,
                evals_pp.as_slice(),
                lde_factor,
                1 << next_folding_steps,
                tree_cap_size,
                intermediate_oracle_mode,
                twiddles,
                pool,
                worker,
            );
            println!(
                "  [timing] intermediate oracle {}: poly 2^{}, lde {} -> {}built in {:.3?}",
                internal_round + 1,
                poly_size_log2,
                lde_factor,
                format_build_split(split),
                t_build.elapsed()
            );
            let c = WhirIntermediateCommitmentAndQueries {
                commitment: WhirCommitment {
                    cap,
                    _marker: core::marker::PhantomData,
                },
                queries: vec![],
            };
            add_whir_commitment_to_transcript::<F, E, TR, T>(&mut transcript_seed, &c.commitment);
            proof.intermediate_whir_oracles.push(c);
            core::mem::replace(&mut rs_oracle, next_oracle)
        };

        // draw OOD sample
        let ood_points: Vec<E> = draw_random_field_els::<F, E, TR>(&mut transcript_seed, 1);
        let ood_point = ood_points[0];
        // compute OOD value
        let ood_value = {
            let t_ood = std::time::Instant::now();
            let v = evaluate_monomial_form(&sumchecked_poly_monomial_form[..], &ood_point, worker);
            println!("  [timing] OOD evaluation: {:.3?}", t_ood.elapsed());
            v
        };
        commit_field_els::<F, E, TR>(&mut transcript_seed, &[ood_value]);
        #[cfg(feature = "gkr_self_checks")]
        {
            let pows = make_pows(ood_point, evals_pp.len().trailing_zeros() as usize);
            let value = evaluate_multivariate(evals_pp.as_slice(), &pows, worker);
            assert_eq!(value, ood_value);
        }

        proof.ood_samples.push(ood_value);

        let mut contributions_to_eq_poly = vec![];

        let query_domain_size = 1u64 << query_domain_log2;

        let query_domain_generator = domain_generator_for_size::<F>(query_domain_size);

        // Committed-leaf folding for this round's intermediate-oracle queries.
        let mut round_folder =
            QueryFolder::<F, E>::new(num_folding_steps, &folding_challenges_in_round);

        let query_index_bits = query_domain_size.trailing_zeros() as usize;
        let num_bits_for_queries = num_queries * query_index_bits;
        if pow_bits > 0 {
            println!("  grinding {pow_bits}-bit PoW ({num_queries} queries)...");
        }
        let t_pow = std::time::Instant::now();
        let (nonce, mut bit_source) = draw_query_bits::<F, E, TR>(
            &mut transcript_seed,
            num_bits_for_queries,
            pow_bits,
            worker,
        );
        println!(
            "  [timing] PoW grind ({pow_bits} bits): {:.3?}",
            t_pow.elapsed()
        );
        proof.pow_nonces.push(nonce);
        println!("  generating {num_queries} query indexes...");
        let mut query_indexes = vec![];
        for _ in 0..num_queries {
            // query index is power for omega^k expression, where omega^{`input_domain_size`} == 1
            let query_index = assemble_query_index(query_index_bits, &mut bit_source);
            query_indexes.push(query_index);
        }

        // and delinearization challenge
        let delinearization_challenges: Vec<E> =
            draw_random_field_els::<F, E, TR>(&mut transcript_seed, 1);
        let delinearization_challenge = delinearization_challenges[0];
        delinearization_challenges_per_round.push(delinearization_challenge);

        // we will have OOD sample contribution
        contributions_to_eq_poly.push((ood_point, delinearization_challenge));

        let mut claim_correction = E::ZERO;
        {
            let mut t = ood_value;
            t.mul_assign(&delinearization_challenge);
            claim_correction.add_assign(&t);
        }
        let mut current_delinearization_challenge = delinearization_challenge;
        current_delinearization_challenge.square();

        // Batch-serve all of this round's queries from the previous oracle (a
        // coset-by-coset oracle recomputes each touched coset group once), then
        // consume them in the original unsorted query order.
        println!("  drawing {num_queries} queries...");
        let t_queries = std::time::Instant::now();
        let mut round_queries = rs_oracle_to_query
            .query_many(&query_indexes, twiddles.plain(), worker)
            .into_iter();
        println!(
            "  [timing] round {} queries ({num_queries}) served in {:.3?}",
            internal_round + 1,
            t_queries.elapsed()
        );
        rs_oracle_to_query.release_into(pool);
        for &query_index in query_indexes.iter() {
            assert!(query_index < query_domain_size as usize);
            let query_point = query_domain_generator.pow(query_index as u32);

            let (_coset_idx, coeffs, query) = round_queries.next().unwrap();
            let num_intermediate_oracles = proof.intermediate_whir_oracles.len();
            assert!(num_intermediate_oracles >= 2);
            let intermediate_oracle =
                &mut proof.intermediate_whir_oracles[num_intermediate_oracles - 2];
            intermediate_oracle.queries.push(query);

            let folded = round_folder.fold_committed_leaf(coeffs);

            query_references.push((query_index, query_point, folded));

            // and add into sumcheck claim
            in_domain.add(
                query_point,
                query_index,
                query_domain_log2,
                current_delinearization_challenge,
            );
            {
                let mut t = folded;
                t.mul_assign(&current_delinearization_challenge);
                claim_correction.add_assign(&t);
            }
            current_delinearization_challenge.mul_assign(&delinearization_challenge);
        }

        #[cfg(feature = "gkr_self_checks")]
        {
            let omega = domain_generator_for_size::<F>(query_domain_size);
            for (i, &query_index) in query_indexes.iter().enumerate() {
                let root = omega.pow(query_index as u32);
                let eval_from_monomial = evaluate_monomial_form(
                    &sumchecked_poly_monomial_form,
                    &E::from_base(root),
                    worker,
                );
                assert_eq!(
                    (query_index, root, eval_from_monomial),
                    query_references[i],
                    "diverged at query {}",
                    i
                );
                let pows = make_pows(root, evals_pp.len().trailing_zeros() as usize);
                let eval_from_multivariate =
                    evaluate_multivariate_at_base(evals_pp.as_slice(), &pows, worker);
                assert_eq!(eval_from_monomial, eval_from_multivariate);
            }
            query_references.clear();
        }
        #[cfg(not(feature = "gkr_self_checks"))]
        query_references.clear();

        // we now update the equality poly - initially we had eq(X, original_evaluation_point), from which we folded few coordinates.
        // Now we should add more terms there to reflect OOD and in-domain samples
        {
            let t_upd = std::time::Instant::now();
            backend.update_eq_poly(eq_pp.as_mut_slice(), &contributions_to_eq_poly, &[], worker);
            println!("  [timing] eq-poly update: {:.3?}", t_upd.elapsed());
        }

        // and remember new sumcheck claim
        claim.add_assign(&claim_correction);

        println!(
            "  [timing] internal round {internal_round} total: {:.3?}",
            t_round.elapsed()
        );
    }

    // and final step is almost the same as the first one - we can fold few times, output evaluation form, and draw final query indexes,
    // check consistency between them, and perform final explicit sumcheck
    let t_round = std::time::Instant::now();
    {
        let num_folding_steps = *whir_steps_schedule.next().unwrap();
        let num_queries = *whir_queries_schedule.next().unwrap();
        let pow_bits = *whir_pow_schedule.next().unwrap();
        assert!(num_folding_steps <= poly_size_log2);

        println!("Final round: fold by {}", 1 << num_folding_steps);

        let rs_domain_log2 = poly_size_log2 + (rs_oracle.num_cosets().trailing_zeros() as usize);
        let query_domain_log2 = rs_domain_log2 - num_folding_steps;
        // the symbolic in-domain terms read their leaves of the CURRENT oracle
        in_domain.start_round(num_folding_steps, rs_domain_log2, |i| {
            rs_oracle.leaf_evaluations(i, twiddles.plain(), worker)
        });
        #[cfg(feature = "gkr_self_checks")]
        in_domain.assert_matches_monomial_form(&sumchecked_poly_monomial_form, worker);

        // fold and send explicit form

        let mut folding_challenges_in_round = Vec::with_capacity(num_folding_steps);
        println!("  running sumcheck for {} rounds...", num_folding_steps);
        let t_sumcheck = std::time::Instant::now();
        for _folding_round in 0..num_folding_steps {
            let (f0, f1, f_half) =
                special_three_point_eval(evals_pp.as_slice(), eq_pp.as_slice(), worker);
            let evaluation_point = E::from_base(two_inv);
            let mut univariate_coeffs =
                special_lagrange_interpolate(f0, f1, f_half, evaluation_point);
            // the symbolic in-domain terms' degree-2 polynomial, added to the
            // coefficients (the three-point sums above cover the eq table only)
            let in_domain_coeffs = in_domain.univariate_coeffs();
            for (c, d) in univariate_coeffs.iter_mut().zip(in_domain_coeffs.iter()) {
                c.add_assign(d);
            }
            // commit
            proof.sumcheck_polys.push(univariate_coeffs);
            commit_field_els::<F, E, TR>(&mut transcript_seed, &univariate_coeffs);

            #[cfg(feature = "gkr_self_checks")]
            {
                let with_terms = |v: E, t: E| {
                    let mut v = v;
                    v.add_assign(&evaluate_small_univariate_poly(&in_domain_coeffs, &t));
                    v
                };
                let s0 = evaluate_small_univariate_poly(&univariate_coeffs, &E::ZERO);
                assert_eq!(s0, with_terms(f0, E::ZERO));
                let s1 = evaluate_small_univariate_poly(&univariate_coeffs, &E::ONE);
                assert_eq!(s1, with_terms(f1, E::ONE));
                let s_half = evaluate_small_univariate_poly(&univariate_coeffs, &evaluation_point);
                assert_eq!(s_half, with_terms(f_half, evaluation_point));
                let mut v = s0;
                v.add_assign(&s1);
                assert_eq!(v, claim, "diverged at round {}", _folding_round);
            }

            let folding_challenges = draw_random_field_els::<F, E, TR>(&mut transcript_seed, 1);
            let folding_challenge = folding_challenges[0];
            folding_challenges_in_round.push(folding_challenge);

            let next_claim = evaluate_small_univariate_poly(&univariate_coeffs, &folding_challenge);
            claim = next_claim;
            // and fold the poly itself - both multivariate evals mapping, and monomial form

            fold_monomial_form(
                &mut sumchecked_poly_monomial_form,
                &mut monomial_form_buffer,
                &folding_challenge,
                worker,
            );

            evals_pp.fold::<F, GB>(&folding_challenge, gkr_backend, worker);

            assert_eq!(sumchecked_poly_monomial_form.len(), evals_pp.len());

            eq_pp.fold::<F, GB>(&folding_challenge, gkr_backend, worker);
            in_domain.fold(&folding_challenge);
            assert_eq!(evals_pp.len(), eq_pp.len());
        }

        println!(
            "  [timing] round sumcheck+eq folds: {:.3?}",
            t_sumcheck.elapsed()
        );
        poly_size_log2 -= num_folding_steps;

        assert_eq!(evals_pp.len(), 1 << poly_size_log2);
        assert_eq!(sumchecked_poly_monomial_form.len(), 1 << poly_size_log2);
        assert_eq!(eq_pp.len(), 1 << poly_size_log2);

        #[cfg(feature = "gkr_self_checks")]
        {
            let mut full_sum = dot_product(evals_pp.as_slice(), eq_pp.as_slice(), worker);
            full_sum.add_assign(&in_domain.sum_at_current());
            assert_eq!(full_sum, claim);
        }

        // commit final-round monomials before drawing queries
        commit_field_els::<F, E, TR>(&mut transcript_seed, &sumchecked_poly_monomial_form);

        // query
        println!("Querying last RS code word oracle");
        let rs_oracle_to_query = rs_oracle;
        let query_domain_size = 1u64 << query_domain_log2;

        let query_domain_generator = domain_generator_for_size::<F>(query_domain_size);

        // Committed-leaf folding for this round's intermediate-oracle queries.
        let mut round_folder =
            QueryFolder::<F, E>::new(num_folding_steps, &folding_challenges_in_round);

        let query_index_bits = query_domain_size.trailing_zeros() as usize;
        let num_bits_for_queries = num_queries * query_index_bits;
        if pow_bits > 0 {
            println!("  grinding {pow_bits}-bit PoW ({num_queries} queries)...");
        }
        let t_pow = std::time::Instant::now();
        let (nonce, mut bit_source) = draw_query_bits::<F, E, TR>(
            &mut transcript_seed,
            num_bits_for_queries,
            pow_bits,
            worker,
        );
        println!(
            "  [timing] PoW grind ({pow_bits} bits): {:.3?}",
            t_pow.elapsed()
        );
        proof.pow_nonces.push(nonce);
        println!("  generating {num_queries} query indexes...");
        let mut query_indexes = vec![];
        for _ in 0..num_queries {
            // query index is power for omega^k expression, where omega^{`input_domain_size`} == 1
            let query_index = assemble_query_index(query_index_bits, &mut bit_source);
            query_indexes.push(query_index);
        }

        // Same batched-then-ordered serving as the internal rounds.
        println!("  drawing {num_queries} queries...");
        let t_queries = std::time::Instant::now();
        let mut round_queries = rs_oracle_to_query
            .query_many(&query_indexes, twiddles.plain(), worker)
            .into_iter();
        println!(
            "  [timing] final-round queries ({num_queries}) served in {:.3?}",
            t_queries.elapsed()
        );
        rs_oracle_to_query.release_into(pool);
        for &query_index in query_indexes.iter() {
            assert!(query_index < query_domain_size as usize);
            let query_point = query_domain_generator.pow(query_index as u32);

            let (_coset_idx, coeffs, query) = round_queries.next().unwrap();
            let intermediate_oracle = proof.intermediate_whir_oracles.last_mut().unwrap();
            intermediate_oracle.queries.push(query);

            let folded = round_folder.fold_committed_leaf(coeffs);

            query_references.push((query_index, query_point, folded));
        }

        #[cfg(feature = "gkr_self_checks")]
        if evals_pp.len() > 1 {
            let omega = domain_generator_for_size::<F>(query_domain_size);
            for (i, &query_index) in query_indexes.iter().enumerate() {
                let root = omega.pow(query_index as u32);
                let eval_from_monomial = evaluate_monomial_form(
                    &sumchecked_poly_monomial_form,
                    &E::from_base(root),
                    worker,
                );
                assert_eq!(
                    (query_index, root, eval_from_monomial),
                    query_references[i],
                    "diverged at query {}",
                    i
                );
                let pows = make_pows(root, evals_pp.len().trailing_zeros() as usize);
                let eval_from_multivariate =
                    evaluate_multivariate_at_base(evals_pp.as_slice(), &pows, worker);
                assert_eq!(eval_from_monomial, eval_from_multivariate);
            }
            query_references.clear();
        }

        #[cfg(feature = "gkr_self_checks")]
        {
            let mut value = dot_product(evals_pp.as_slice(), eq_pp.as_slice(), worker);
            value.add_assign(&in_domain.sum_at_current());
            assert_eq!(value, claim);
        }
    }

    assert!(whir_steps_lde_factors.next().is_none());
    assert!(whir_steps_schedule.next().is_none());
    assert!(whir_queries_schedule.next().is_none());
    assert!(whir_pow_schedule.next().is_none());

    println!("  [timing] final round total: {:.3?}", t_round.elapsed());

    proof.final_monomials = sumchecked_poly_monomial_form;
    eq_pp.release::<F>(pool);

    #[cfg(feature = "gkr_self_checks")]
    {
        let final_len = 1usize << final_poly_log2;
        let mut hypercube_evals = proof.final_monomials.clone();
        multivariate_coeffs_into_hypercube_evals(&mut hypercube_evals, final_poly_log2 as u32);
        assert_eq!(evals_pp.len(), final_len);
        assert_eq!(
            &hypercube_evals[..],
            evals_pp.as_slice(),
            "final monomials → hypercube evals mismatch"
        );
    }
    evals_pp.release::<F>(pool);

    proof
}

/// Per-round query-leaf folding (coefficient leaves + monomial-tensor
/// evaluation), its precomputed tables AND its scratch buffers all hidden
/// inside — so query sites carry no loose scratch vectors.
pub(crate) struct QueryFolder<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field> {
    num_folding_rounds: usize,
    high_powers_offsets: Vec<F>,
    two_inv: F,
    monomial_weights: Vec<E>,
    scratch_a: Vec<E>,
    scratch_b: Vec<E>,
}

impl<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field> QueryFolder<F, E> {
    pub(crate) fn new(num_folding_rounds: usize, folding_challenges_in_round: &[E]) -> Self {
        let two_inv = F::TWO.inverse().unwrap();
        let high_powers_offsets = if num_folding_rounds > 0 {
            let set_generator = domain_generator_for_size::<F>(1u64 << num_folding_rounds);
            let mut hp = materialize_powers_serial_starting_with_one::<F, Global>(
                set_generator.inverse().unwrap(),
                1 << (num_folding_rounds - 1),
            );
            bitreverse_enumeration_inplace(&mut hp);
            hp
        } else {
            vec![]
        };
        let monomial_weights = if !folding_challenges_in_round.is_empty() {
            precompute_monomial_tensor(folding_challenges_in_round)
        } else {
            vec![E::ONE]
        };
        let scratch_len = 1usize << num_folding_rounds;
        Self {
            num_folding_rounds,
            high_powers_offsets,
            two_inv,
            monomial_weights,
            scratch_a: vec![E::ZERO; scratch_len],
            scratch_b: vec![E::ZERO; scratch_len],
        }
    }

    /// Fold a leaf that is in EVALUATION form (the round-0 base-oracle
    /// leaves), given the query's base root inverse.
    pub(crate) fn fold_eval_leaf(&mut self, mut evals: Vec<E>, base_root_inv: &F) -> E {
        evals_to_multilinear_coeffs(
            &mut evals,
            base_root_inv,
            &self.high_powers_offsets,
            &self.two_inv,
            self.num_folding_rounds,
            &mut self.scratch_a,
            &mut self.scratch_b,
        );
        eval_multilinear_with_monomial_tensor(&evals, &self.monomial_weights)
    }

    /// Fold a leaf that is in the PRODUCTION committed encoding (intermediate
    /// oracles: multilinear coefficients).
    pub(crate) fn fold_committed_leaf(&mut self, leaf: Vec<E>) -> E {
        eval_multilinear_with_monomial_tensor(&leaf, &self.monomial_weights)
    }
}

/// Coset-independent precomputes for the extension leaf coeff-conversion, so a
/// caller iterating many cosets builds them ONCE (the `coset_gen_inv_powers` table
/// alone is `num_leaves` field elements).
pub(crate) struct ExtCoeffConvCtx<F: PrimeField + TwoAdicField> {
    pub(crate) values_per_leaf: usize,
    pub(crate) num_folding_rounds: usize,
    pub(crate) two_inv: F,
    pub(crate) high_powers_offsets: Vec<F>,
    pub(crate) offsets: Vec<usize>,
    /// `coset_generator_inv^leaf_idx`, `num_leaves` entries (coset-independent).
    pub(crate) coset_gen_inv_powers: Vec<F>,
}

impl<F: PrimeField + TwoAdicField> ExtCoeffConvCtx<F> {
    pub(crate) fn new(trace_len: usize, values_per_leaf: usize) -> Self {
        let num_folding_rounds = values_per_leaf.trailing_zeros() as usize;
        let two_inv = F::TWO.inverse().unwrap();
        let set_generator = domain_generator_for_size::<F>(values_per_leaf as u64);
        let mut high_powers_offsets = materialize_powers_serial_starting_with_one::<F, Global>(
            set_generator.inverse().unwrap(),
            values_per_leaf / 2,
        );
        bitreverse_enumeration_inplace(&mut high_powers_offsets);
        let offsets = offsets_vec_for_leaf_construction(trace_len, values_per_leaf);
        let num_leaves = trace_len / values_per_leaf;
        let coset_generator = domain_generator_for_size::<F>(trace_len as u64);
        let coset_gen_inv_powers = materialize_powers_serial_starting_with_one::<F, Global>(
            coset_generator.inverse().unwrap(),
            num_leaves,
        );
        Self {
            values_per_leaf,
            num_folding_rounds,
            two_inv,
            high_powers_offsets,
            offsets,
            coset_gen_inv_powers,
        }
    }

    /// Rewrite one coset (with LDE `offset`) from evaluation to multilinear-coeff
    /// form, in place. `base_root_invs[i] = coset_gen_inv^i * offset^-1`.
    pub(crate) fn apply<E: FieldExtension<F> + Field>(
        &self,
        column: &mut [E],
        offset: F,
        worker: &Worker,
    ) {
        if self.num_folding_rounds == 0 {
            return;
        }
        let num_leaves = self.coset_gen_inv_powers.len();
        let values_per_leaf = self.values_per_leaf;
        let num_folding_rounds = self.num_folding_rounds;
        let two_inv = self.two_inv;

        let offset_inv = offset.inverse().unwrap();
        let base_root_invs: Vec<F> = self
            .coset_gen_inv_powers
            .iter()
            .map(|&p| {
                let mut x = p;
                x.mul_assign(&offset_inv);
                x
            })
            .collect();

        debug_assert!(self
            .offsets
            .iter()
            .all(|&o| o % num_leaves == 0 && o < column.len()));
        let base_ptr = column.as_mut_ptr() as usize;
        worker.scope(num_leaves, |scope, geometry| {
            for chunk_idx in 0..geometry.len() {
                let chunk_start = geometry.get_chunk_start_pos(chunk_idx);
                let chunk_size = geometry.get_chunk_size(chunk_idx);
                let base_ptr = base_ptr;
                let offsets = &self.offsets;
                let base_root_invs = &base_root_invs;
                let high_powers_offsets = &self.high_powers_offsets;
                let is_last = chunk_idx == geometry.len() - 1;

                Worker::smart_spawn(scope, is_last, move |_| {
                    let ptr = base_ptr as *mut E;
                    let mut leaf_buf = vec![E::ZERO; values_per_leaf];
                    let mut scratch_a = vec![E::ZERO; values_per_leaf];
                    let mut scratch_b = vec![E::ZERO; values_per_leaf];
                    for leaf_idx in chunk_start..(chunk_start + chunk_size) {
                        for (k, &off) in offsets.iter().enumerate() {
                            leaf_buf[k] = unsafe { *ptr.add(off + leaf_idx) };
                        }
                        evals_to_multilinear_coeffs(
                            &mut leaf_buf,
                            &base_root_invs[leaf_idx],
                            high_powers_offsets,
                            &two_inv,
                            num_folding_rounds,
                            &mut scratch_a,
                            &mut scratch_b,
                        );
                        for (k, &off) in offsets.iter().enumerate() {
                            unsafe { *ptr.add(off + leaf_idx) = leaf_buf[k] };
                        }
                    }
                });
            }
        });
    }

    /// ONE leaf of an evaluation-form column (`offset_inv` = the coset
    /// offset's inverse), gathered in leaf order and converted into `out`;
    /// bit-identical to the leaf [`apply`](Self::apply) leaves in the column.
    #[inline(always)]
    pub(crate) fn convert_leaf<E: FieldExtension<F> + Field>(
        &self,
        column: &[E],
        offset_inv: F,
        leaf_index: usize,
        out: &mut [E],
    ) {
        debug_assert_eq!(out.len(), self.values_per_leaf);
        for (o, &off) in out.iter_mut().zip(self.offsets.iter()) {
            *o = column[off + leaf_index];
        }
        self.convert_gathered_leaf(offset_inv, leaf_index, out);
    }

    /// The conversion half of [`convert_leaf`](Self::convert_leaf): `leaf`
    /// already holds leaf `leaf_index`'s evaluations in leaf order.
    #[inline(always)]
    pub(crate) fn convert_gathered_leaf<E: FieldExtension<F> + Field>(
        &self,
        offset_inv: F,
        leaf_index: usize,
        leaf: &mut [E],
    ) {
        let n = self.values_per_leaf;
        debug_assert_eq!(leaf.len(), n);
        if self.num_folding_rounds == 0 {
            return;
        }
        let mut root_inv = self.coset_gen_inv_powers[leaf_index];
        root_inv.mul_assign(&offset_inv);
        if n <= 64 {
            let mut a = [E::ZERO; 64];
            let mut b = [E::ZERO; 64];
            evals_to_multilinear_coeffs(
                leaf,
                &root_inv,
                &self.high_powers_offsets,
                &self.two_inv,
                self.num_folding_rounds,
                &mut a[..n],
                &mut b[..n],
            );
        } else {
            let mut a = vec![E::ZERO; n];
            let mut b = vec![E::ZERO; n];
            evals_to_multilinear_coeffs(
                leaf,
                &root_inv,
                &self.high_powers_offsets,
                &self.two_inv,
                self.num_folding_rounds,
                &mut a,
                &mut b,
            );
        }
    }

    /// Fully-serial (no worker) variant of [`apply`](Self::apply). Used when many
    /// small cosets are converted concurrently (one per worker thread), so the
    /// per-coset conversion must not spawn its own worker scope. Bit-identical to
    /// `apply` for the same `column`/`offset`.
    pub(crate) fn apply_serial<E: FieldExtension<F> + Field>(&self, column: &mut [E], offset: F) {
        if self.num_folding_rounds == 0 {
            return;
        }
        let num_leaves = self.coset_gen_inv_powers.len();
        let offset_inv = offset.inverse().unwrap();
        let mut leaf_buf = vec![E::ZERO; self.values_per_leaf];
        let mut scratch_a = vec![E::ZERO; self.values_per_leaf];
        let mut scratch_b = vec![E::ZERO; self.values_per_leaf];
        for leaf_idx in 0..num_leaves {
            let mut base_root_inv = self.coset_gen_inv_powers[leaf_idx];
            base_root_inv.mul_assign(&offset_inv);
            for (k, &off) in self.offsets.iter().enumerate() {
                leaf_buf[k] = column[off + leaf_idx];
            }
            evals_to_multilinear_coeffs(
                &mut leaf_buf,
                &base_root_inv,
                &self.high_powers_offsets,
                &self.two_inv,
                self.num_folding_rounds,
                &mut scratch_a,
                &mut scratch_b,
            );
            for (k, &off) in self.offsets.iter().enumerate() {
                column[off + leaf_idx] = leaf_buf[k];
            }
        }
    }
}

/// Leaves of at least this many values are converted WHILE the tree hashes
/// them (the cosets stay in evaluation form, queries convert on the way
/// out); smaller leaves are converted by the in-place pass first. Measured
/// on the box (solo 16 threads, tree = conversion + hashing): 32-value
/// leaves 186-188 ms fused vs 186-187 in place, 16-value 335 vs 234,
/// 8-value 127 vs 68 — the per-leaf-batch overhead of the fused gather only
/// amortizes over wide leaves, while the in-place AVX2 pass streams tiny
/// leaves at ~1 ns each.
const FUSED_LEAF_CONVERSION_MIN_VALUES_PER_LEAF: usize = 32;

/// In-place leaf conversion of every coset (the small-leaf path), scheduled
/// like the backend's coset grids: with at least as many cosets as threads
/// the cosets are converted in parallel with the serial per-coset kernel,
/// otherwise sequentially with the worker-parallel one.
fn convert_leaves_in_place<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field>(
    columns: &mut [&mut [E]],
    offsets: &[F],
    conv: &impl crate::gkr::prover::backend::ExtCoeffConversion<F, E>,
    worker: &Worker,
) {
    if columns.len() >= worker.get_num_cores() {
        use worker::rayon::prelude::*;
        worker.pool.install(|| {
            columns
                .par_iter_mut()
                .zip(offsets.par_iter())
                .for_each(|(column, offset)| conv.apply_serial(column, *offset))
        });
    } else {
        for (column, offset) in columns.iter_mut().zip(offsets.iter()) {
            conv.apply(column, *offset, worker);
        }
    }
}

/// Commit one extension polynomial's RS cosets: the tree hashes the
/// backend's committed leaf encoding (evaluations -> multilinear coefficients)
/// THROUGH the leaf accessors
/// while it hashes, so the cosets stay in evaluation form and no separate
/// conversion pass touches the codeword; queries convert their leaf on the
/// way out. Small leaves take the in-place conversion pass instead (see
/// [`FUSED_LEAF_CONVERSION_MIN_VALUES_PER_LEAF`]).
fn commit_single_ext_poly<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
    B: crate::gkr::prover::backend::Backend<F, E>,
>(
    cosets: Vec<(Box<[E]>, F)>,
    values_per_leaf: usize,
    tree_cap_size: usize,
    backend: &B,
    worker: &Worker,
) -> ColumnMajorExtensionOracleForLDE<F, E, T>
where
    [(); E::DEGREE]: Sized,
{
    let trace_len_log2 = cosets[0].0.len().trailing_zeros() as usize;
    let trace_len = 1usize << trace_len_log2;
    let conv = backend.ext_coeff_conv(trace_len, values_per_leaf);
    let fused = values_per_leaf >= FUSED_LEAF_CONVERSION_MIN_VALUES_PER_LEAF;
    let mut cosets = cosets;
    if !fused {
        let offsets: Vec<F> = cosets.iter().map(|(_, o)| *o).collect();
        let mut columns: Vec<&mut [E]> = cosets.iter_mut().map(|(c, _)| &mut c[..]).collect();
        convert_leaves_in_place(&mut columns, &offsets, &conv, worker);
    }
    let mut t = Vec::with_capacity(cosets.len());
    for (column, offset) in cosets.into_iter() {
        assert_eq!(column.len(), trace_len);
        t.push(ColumnMajorExtensionOracleForCoset {
            values_normal_order: ColumnMajorCosetBoundTracePart::owned(column, offset),
        });
    }
    let mut coset_offsets_inv: Vec<F> = t.iter().map(|el| el.values_normal_order.offset).collect();
    let mut inv_scratch = vec![F::ZERO; coset_offsets_inv.len()];
    batch_inverse_inplace(&mut coset_offsets_inv, &mut inv_scratch);
    let tree = if fused {
        let leaves: Vec<[B::CosetLeaves<'_>; 1]> = t
            .iter()
            .map(|el| {
                [backend.coset_leaves(
                    &conv,
                    el.values_normal_order
                        .as_contiguous()
                        .expect("contiguous ext oracle column"),
                    el.values_normal_order.offset,
                )]
            })
            .collect();
        let leaves_ref: Vec<&[B::CosetLeaves<'_>]> = leaves.iter().map(|el| &el[..]).collect();
        T::construct_from_leaf_accessors::<E, _>(
            &leaves_ref[..],
            tree_cap_size,
            true,
            false,
            worker,
        )
    } else {
        let source: Vec<Vec<&[E]>> = t
            .iter()
            .map(|el| {
                vec![el
                    .values_normal_order
                    .as_contiguous()
                    .expect("contiguous ext oracle column")]
            })
            .collect();
        let source_ref: Vec<&[&[E]]> = source.iter().map(|el| &el[..]).collect();
        T::construct_from_cosets::<E, _>(
            &source_ref[..],
            values_per_leaf,
            tree_cap_size,
            true,
            true,
            false,
            worker,
        )
    };
    let conv: LeafConversionHandle<F, E> = if fused {
        LeafConversionHandle(Arc::new(conv))
    } else {
        LeafConversionHandle(Arc::new(
            crate::gkr::prover::backend::NoLeafConversion::<F>::new(trace_len, values_per_leaf),
        ))
    };
    ColumnMajorExtensionOracleForLDE {
        cosets: t,
        tree,
        values_per_leaf,
        trace_len_log2,
        conv,
        coset_offsets_inv,
        leaves_in_coefficient_form: !fused,
    }
}

/// [`commit_single_ext_poly`] over one contiguous coset-major buffer.
fn commit_single_ext_poly_continuous<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
    B: crate::gkr::prover::backend::Backend<F, E>,
>(
    buffer: Box<[E]>,
    coset_offsets: Vec<F>,
    values_per_leaf: usize,
    tree_cap_size: usize,
    backend: &B,
    worker: &Worker,
) -> ContinuousExtensionOracleForLDE<F, E, T>
where
    [(); E::DEGREE]: Sized,
{
    let num_cosets = coset_offsets.len();
    assert!(num_cosets.is_power_of_two());
    assert_eq!(buffer.len() % num_cosets, 0);
    let trace_len = buffer.len() / num_cosets;
    assert!(trace_len.is_power_of_two());
    let trace_len_log2 = trace_len.trailing_zeros() as usize;
    let conv = backend.ext_coeff_conv(trace_len, values_per_leaf);
    let mut coset_offsets_inv: Vec<F> = coset_offsets.clone();
    let mut inv_scratch = vec![F::ZERO; coset_offsets_inv.len()];
    batch_inverse_inplace(&mut coset_offsets_inv, &mut inv_scratch);
    let fused = values_per_leaf >= FUSED_LEAF_CONVERSION_MIN_VALUES_PER_LEAF;
    let mut buffer = buffer;
    if !fused {
        let mut columns: Vec<&mut [E]> = buffer.chunks_mut(trace_len).collect();
        convert_leaves_in_place(&mut columns, &coset_offsets, &conv, worker);
    }
    let tree = if fused {
        let leaves: Vec<[B::CosetLeaves<'_>; 1]> = buffer
            .chunks(trace_len)
            .zip(coset_offsets.iter())
            .map(|(column, offset)| [backend.coset_leaves(&conv, column, *offset)])
            .collect();
        let leaves_ref: Vec<&[B::CosetLeaves<'_>]> = leaves.iter().map(|el| &el[..]).collect();
        T::construct_from_leaf_accessors::<E, _>(
            &leaves_ref[..],
            tree_cap_size,
            true,
            false,
            worker,
        )
    } else {
        let source: Vec<Vec<&[E]>> = buffer.chunks(trace_len).map(|coset| vec![coset]).collect();
        let source_ref: Vec<&[&[E]]> = source.iter().map(|el| &el[..]).collect();
        T::construct_from_cosets::<E, _>(
            &source_ref[..],
            values_per_leaf,
            tree_cap_size,
            true,
            true,
            false,
            worker,
        )
    };
    let conv: LeafConversionHandle<F, E> = if fused {
        LeafConversionHandle(Arc::new(conv))
    } else {
        LeafConversionHandle(Arc::new(
            crate::gkr::prover::backend::NoLeafConversion::<F>::new(trace_len, values_per_leaf),
        ))
    };
    ContinuousExtensionOracleForLDE {
        buffer,
        coset_offsets,
        trace_len_log2,
        tree,
        values_per_leaf,
        conv,
        coset_offsets_inv,
        leaves_in_coefficient_form: !fused,
    }
}

/// Test-only public shim over the private [`commit_single_ext_poly`], so
/// downstream crates' tests can build a reference recursive-WHIR oracle with the
/// exact production leaf encoding (coefficient form). Gated behind `test-utils`;
/// not part of the normal library API.
#[cfg(any(test, feature = "test-utils"))]
pub fn commit_single_ext_poly_for_test<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    cosets: Vec<(Box<[E]>, F)>,
    values_per_leaf: usize,
    tree_cap_size: usize,
    worker: &Worker,
) -> ColumnMajorExtensionOracleForLDE<F, E, T>
where
    [(); E::DEGREE]: Sized,
{
    commit_single_ext_poly::<F, E, T, _>(
        cosets,
        values_per_leaf,
        tree_cap_size,
        &crate::gkr::prover::backend::NaiveBackend,
        worker,
    )
}

/// Eval-form (no leaf transform) single-poly commit for tests that validate the
/// `transform_leaves_to_multilinear_coeffs == false` path against a GPU oracle.
/// `commit_single_ext_poly` is coefficient-form (#279); this helper provides the
/// eval-form reference (raw evaluations committed).
#[cfg(any(test, feature = "test-utils"))]
pub fn commit_single_ext_poly_no_transform_for_test<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    cosets: Vec<(Box<[E]>, F)>,
    values_per_leaf: usize,
    tree_cap_size: usize,
    worker: &Worker,
) -> ColumnMajorExtensionOracleForLDE<F, E, T>
where
    [(); E::DEGREE]: Sized,
{
    let mut t = Vec::with_capacity(cosets.len());
    let trace_len_log2 = cosets[0].0.len().trailing_zeros() as usize;
    for (column, offset) in cosets.into_iter() {
        assert!(!column.is_empty());
        let el = ColumnMajorExtensionOracleForCoset {
            values_normal_order: ColumnMajorCosetBoundTracePart::owned(column, offset),
        };
        t.push(el);
    }

    let source: Vec<_> = t
        .iter()
        .map(|el| {
            vec![el
                .values_normal_order
                .as_contiguous()
                .expect("contiguous ext oracle column")]
        })
        .collect();
    let source_ref: Vec<_> = source.iter().map(|el| &el[..]).collect();

    let tree = T::construct_from_cosets::<E, _>(
        &source_ref[..],
        values_per_leaf,
        tree_cap_size,
        true,
        true,
        false,
        worker,
    );

    let coset_offsets_inv: Vec<F> = t
        .iter()
        .map(|el| el.values_normal_order.offset.inverse().unwrap())
        .collect();
    ColumnMajorExtensionOracleForLDE {
        cosets: t,
        tree,
        values_per_leaf,
        trace_len_log2,
        // the buffers already hold the committed values: queries gather as is
        conv: LeafConversionHandle(Arc::new(
            crate::gkr::prover::backend::NoLeafConversion::<F>::new(
                1usize << trace_len_log2,
                values_per_leaf,
            ),
        )),
        coset_offsets_inv,
        leaves_in_coefficient_form: true,
    }
}

#[cfg(any(test, feature = "test-utils"))]
pub fn commit_single_ext_poly_with_transform_for_test<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    cosets: Vec<(Box<[E]>, F)>,
    values_per_leaf: usize,
    tree_cap_size: usize,
    worker: &Worker,
) -> ColumnMajorExtensionOracleForLDE<F, E, T>
where
    [(); E::DEGREE]: Sized,
{
    let num_folding_rounds = values_per_leaf.trailing_zeros() as usize;
    let mut t = Vec::with_capacity(cosets.len());
    let trace_len_log2 = cosets[0].0.len().trailing_zeros() as usize;
    let trace_len = 1usize << trace_len_log2;
    let num_cosets = cosets.len();

    let two_inv = F::from_u32_unchecked(2).inverse().unwrap();
    let set_generator = domain_generator_for_size::<F>(values_per_leaf as u64);
    let mut high_powers_offsets = materialize_powers_serial_starting_with_one::<F, Global>(
        set_generator.inverse().unwrap(),
        values_per_leaf / 2,
    );
    bitreverse_enumeration_inplace(&mut high_powers_offsets);

    let offsets = offsets_vec_for_leaf_construction(trace_len, values_per_leaf);
    let num_leaves = trace_len / values_per_leaf;

    let extended_generator = domain_generator_for_size::<F>((trace_len * num_cosets) as u64);
    let coset_generator = extended_generator.pow(num_cosets as u32);
    let coset_generator_inv = coset_generator.inverse().unwrap();

    for (mut column, offset) in cosets.into_iter() {
        assert!(column.len() > 0);

        if num_folding_rounds > 0 {
            let offset_inv = offset.inverse().unwrap();
            let base_root_invs = {
                let mut v = materialize_powers_serial_starting_with_one::<F, Global>(
                    coset_generator_inv,
                    num_leaves,
                );
                for r in v.iter_mut() {
                    r.mul_assign(&offset_inv);
                }
                v
            };

            // SAFETY: each thread writes to disjoint leaf indices; offsets stride
            // across the column so no two threads touch the same element.
            let base_ptr = column.as_mut_ptr() as usize;
            worker.scope(num_leaves, |scope, geometry| {
                for chunk_idx in 0..geometry.len() {
                    let chunk_start = geometry.get_chunk_start_pos(chunk_idx);
                    let chunk_size = geometry.get_chunk_size(chunk_idx);
                    let base_ptr = base_ptr;
                    let offsets = &offsets;
                    let base_root_invs = &base_root_invs;
                    let high_powers_offsets = &high_powers_offsets;
                    let is_last = chunk_idx == geometry.len() - 1;

                    Worker::smart_spawn(scope, is_last, move |_| {
                        let ptr = base_ptr as *mut E;
                        let mut leaf_buf = vec![E::ZERO; values_per_leaf];
                        let mut scratch_a = vec![E::ZERO; values_per_leaf];
                        let mut scratch_b = vec![E::ZERO; values_per_leaf];
                        for leaf_idx in chunk_start..(chunk_start + chunk_size) {
                            for (k, &off) in offsets.iter().enumerate() {
                                leaf_buf[k] = unsafe { *ptr.add(off + leaf_idx) };
                            }
                            evals_to_multilinear_coeffs(
                                &mut leaf_buf,
                                &base_root_invs[leaf_idx],
                                high_powers_offsets,
                                &two_inv,
                                num_folding_rounds,
                                &mut scratch_a,
                                &mut scratch_b,
                            );
                            for (k, &off) in offsets.iter().enumerate() {
                                unsafe { *ptr.add(off + leaf_idx) = leaf_buf[k] };
                            }
                        }
                    });
                }
            });
        }

        let el = ColumnMajorExtensionOracleForCoset {
            values_normal_order: ColumnMajorCosetBoundTracePart::owned(column, offset),
        };
        t.push(el);
    }

    let source: Vec<_> = t
        .iter()
        .map(|el| {
            vec![el
                .values_normal_order
                .as_contiguous()
                .expect("contiguous ext oracle column")]
        })
        .collect();
    let source_ref: Vec<_> = source.iter().map(|el| &el[..]).collect();

    let tree = T::construct_from_cosets::<E, _>(
        &source_ref[..],
        values_per_leaf,
        tree_cap_size,
        true,
        true,
        false,
        worker,
    );

    let coset_offsets_inv: Vec<F> = t
        .iter()
        .map(|el| el.values_normal_order.offset.inverse().unwrap())
        .collect();
    ColumnMajorExtensionOracleForLDE {
        cosets: t,
        tree,
        values_per_leaf,
        trace_len_log2,
        // the buffers already hold the committed values: queries gather as is
        conv: LeafConversionHandle(Arc::new(
            crate::gkr::prover::backend::NoLeafConversion::<F>::new(
                1usize << trace_len_log2,
                values_per_leaf,
            ),
        )),
        coset_offsets_inv,
        leaves_in_coefficient_form: true,
    }
}

pub fn fold_monomial_form<E: Field>(
    input: &mut Vec<E>,
    buffer: &mut Vec<E>,
    challenge: &E,
    worker: &Worker,
) {
    assert!(input.len().is_power_of_two());
    assert!(buffer.capacity() >= input.len() / 2);
    assert!(buffer.is_empty());

    let work_size = input.len() / 2;
    if work_size == 0 {
        return;
    }

    let input_pairs = input.as_chunks::<2>().0;
    let dst_uninit = &mut buffer.spare_capacity_mut()[..work_size];

    worker.scope_with_threshold(work_size, PAR_THRESHOLD, |scope, geometry| {
        input_pairs
            .chunks_for_geometry(geometry)
            .enumerate()
            .zip(dst_uninit.chunks_for_geometry_mut(geometry))
            .for_each(|((idx, src_chunk), dst_chunk)| {
                Worker::smart_spawn(scope, idx == geometry.len() - 1, |_| {
                    for ([c0, c1], d) in src_chunk.iter().zip(dst_chunk.iter_mut()) {
                        let mut result = *c1;
                        result.mul_assign(challenge);
                        result.add_assign(c0);
                        d.write(result);
                    }
                });
            })
    });

    unsafe {
        buffer.set_len(work_size);
    }

    core::mem::swap(input, buffer);
    buffer.clear();
}

#[cfg(test)]
fn fold_monomial_form_serial<E: Field>(input: &mut Vec<E>, buffer: &mut Vec<E>, challenge: &E) {
    assert!(input.len().is_power_of_two());
    assert!(buffer.capacity() >= input.len() / 2);
    assert!(buffer.is_empty());

    for ([c0, c1], dst) in input
        .as_chunks::<2>()
        .0
        .iter()
        .zip(buffer.spare_capacity_mut()[..input.len() / 2].iter_mut())
    {
        let mut result = *c1;
        result.mul_assign(challenge);
        result.add_assign(c0);
        dst.write(result);
    }
    unsafe {
        buffer.set_len(input.len() / 2);
    }

    core::mem::swap(input, buffer);
    buffer.clear();
}

#[cfg(test)]
fn fold_evaluation_form_serial<'a, F: PrimeField, E: FieldExtension<F> + Field>(
    input: &'a mut [E],
    challenge: &E,
) -> &'a mut [E] {
    assert!(input.len().is_power_of_two());
    let half_len = input.len() / 2;
    let f1_coeff = *challenge;

    // LSB binding: fold ADJACENT pairs (2i, 2i+1); serial in-place
    // left-to-right is safe (writes trail reads)
    for i in 0..half_len {
        let a = input[2 * i];
        let mut t = input[2 * i + 1];
        t.sub_assign(&a);
        t.mul_assign(&f1_coeff);
        let mut v = a;
        v.add_assign(&t);
        input[i] = v;
    }

    &mut input[..half_len]
}

pub fn fold_evaluation_form<'a, F: PrimeField, E: FieldExtension<F> + Field>(
    input: &'a mut [E],
    challenge: &E,
    worker: &Worker,
) -> &'a mut [E] {
    assert!(input.len().is_power_of_two());
    let half_len = input.len() / 2;
    if half_len == 0 {
        return &mut input[..0];
    }

    let f1_coeff = *challenge;

    // LSB binding folds ADJACENT pairs (2i, 2i+1). Phase 1 (parallel): each
    // pair's result overwrites its own pair slots -- per-pair independent, so
    // any chunking is race-free (pair chunks never split a pair). Phase 2
    // (parallel): compact pair-heads to the front by disjoint chunk copies
    // using a whole-struct pointer (each chunk writes [a, b) and reads
    // [2a, 2b); write ranges are pairwise disjoint from OTHER chunks' reads
    // only in phase-separated form, so phase 2 reads what phase 1 finished).
    let pairs = input.as_chunks_mut::<2>().0;
    worker.scope_with_threshold(half_len, PAR_THRESHOLD, |scope, geometry| {
        pairs
            .chunks_for_geometry_mut(geometry)
            .enumerate()
            .for_each(|(idx, chunk)| {
                Worker::smart_spawn(scope, idx == geometry.len() - 1, |_| {
                    for pair in chunk.iter_mut() {
                        let [a, b] = *pair;
                        let mut t = b;
                        t.sub_assign(&a);
                        t.mul_assign(&f1_coeff);
                        let mut v = a;
                        v.add_assign(&t);
                        pair[0] = v;
                    }
                });
            })
    });
    // serial compaction: input[i] = input[2i]; writes trail reads
    for i in 1..half_len {
        input[i] = input[2 * i];
    }

    &mut input[..half_len]
}

#[cfg(test)]
fn fold_eq_poly_serial<'a, F: PrimeField, E: FieldExtension<F> + Field>(
    eq_poly: &'a mut [E],
    challenge: &E,
) -> &'a mut [E] {
    assert!(eq_poly.len().is_power_of_two());
    assert!(eq_poly.len() >= 2);
    let half_len = eq_poly.len() / 2;
    let f1_coeff = *challenge;

    for i in 0..half_len {
        let a = eq_poly[2 * i];
        let mut t = eq_poly[2 * i + 1];
        t.sub_assign(&a);
        t.mul_assign(&f1_coeff);
        let mut v = a;
        v.add_assign(&t);
        eq_poly[i] = v;
    }

    &mut eq_poly[..half_len]
}

pub fn fold_eq_poly<'a, F: PrimeField, E: FieldExtension<F> + Field>(
    eq_poly: &'a mut [E],
    challenge: &E,
    worker: &Worker,
) -> &'a mut [E] {
    assert!(eq_poly.len().is_power_of_two());
    assert!(eq_poly.len() >= 2);
    let half_len = eq_poly.len() / 2;

    let f1_coeff = *challenge;

    // LSB binding: same two-phase adjacent-pair scheme as
    // [`fold_evaluation_form`] (identical linear-interpolation formula)
    let pairs = eq_poly.as_chunks_mut::<2>().0;
    worker.scope_with_threshold(half_len, PAR_THRESHOLD, |scope, geometry| {
        pairs
            .chunks_for_geometry_mut(geometry)
            .enumerate()
            .for_each(|(idx, chunk)| {
                Worker::smart_spawn(scope, idx == geometry.len() - 1, |_| {
                    for pair in chunk.iter_mut() {
                        let [a, b] = *pair;
                        let mut t = b;
                        t.sub_assign(&a);
                        t.mul_assign(&f1_coeff);
                        let mut v = a;
                        v.add_assign(&t);
                        pair[0] = v;
                    }
                });
            })
    });
    for i in 1..half_len {
        eq_poly[i] = eq_poly[2 * i];
    }

    &mut eq_poly[..half_len]
}

#[cfg(test)]
fn dot_product_serial<F: PrimeField, E: FieldExtension<F> + Field>(a: &[E], b: &[E]) -> E {
    assert!(a.len() > 0);
    assert_eq!(a.len(), b.len());
    let mut result = E::ZERO;
    for (a, b) in a.iter().zip(b.iter()) {
        let mut t = *a;
        t.mul_assign(b);
        result.add_assign(&t);
    }
    result
}

fn dot_product<F: PrimeField, E: FieldExtension<F> + Field>(
    a: &[E],
    b: &[E],
    worker: &Worker,
) -> E {
    assert!(a.len() > 0);
    assert_eq!(a.len(), b.len());

    let geometry = worker.get_geometry_with_threshold(a.len(), PAR_THRESHOLD);
    let mut partial_results = vec![E::ZERO; geometry.len()];

    worker.scope_with_threshold(a.len(), PAR_THRESHOLD, |scope, geometry| {
        a.chunks_for_geometry(geometry)
            .enumerate()
            .zip(b.chunks_for_geometry(geometry))
            .zip(partial_results.iter_mut())
            .for_each(|(((idx, a_chunk), b_chunk), partial)| {
                Worker::smart_spawn(scope, idx == geometry.len() - 1, |_| {
                    let mut acc = E::ZERO;
                    for (a, b) in a_chunk.iter().zip(b_chunk.iter()) {
                        let mut t = *a;
                        t.mul_assign(b);
                        acc.add_assign(&t);
                    }
                    *partial = acc;
                });
            });
    });

    partial_results.iter().fold(E::ZERO, |mut acc, p| {
        acc.add_assign(p);
        acc
    })
}

// Accumulate partial [f0, f1, f_half] sums over aligned quadruples of slice elements.
// LSB pairing: the round binds variable 0, so a pair is the ADJACENT
// (a[2i], a[2i+1]) (natural monomial/eval order).  quart scaling is NOT
// applied here.
#[inline(always)]
fn three_point_partial<E: Field>(a_pairs: &[[E; 2]], b_pairs: &[[E; 2]]) -> [E; 3] {
    let mut f0 = E::ZERO;
    let mut f1 = E::ZERO;
    let mut f_half = E::ZERO;
    for ([a0, a1], [b0, b1]) in a_pairs.iter().zip(b_pairs.iter()) {
        let mut t0 = *a0;
        t0.mul_assign(b0);
        f0.add_assign(&t0);

        let mut t1 = *a1;
        t1.mul_assign(b1);
        f1.add_assign(&t1);

        let mut tt = *a1;
        tt.add_assign(a0);
        let mut t_half = *b1;
        t_half.add_assign(b0);
        t_half.mul_assign(&tt);
        f_half.add_assign(&t_half);
    }
    [f0, f1, f_half]
}

#[cfg(test)]
fn special_three_point_eval_serial<F: PrimeField, E: FieldExtension<F> + Field>(
    a: &[E],
    b: &[E],
) -> (E, E, E) {
    assert!(a.len() > 0);
    assert_eq!(a.len(), b.len());
    let quart = F::from_u32_unchecked(4).inverse().unwrap();
    let [f0, f1, mut f_half] = three_point_partial(a.as_chunks::<2>().0, b.as_chunks::<2>().0);
    f_half.mul_assign_by_base(&quart);
    (f0, f1, f_half)
}

pub fn special_three_point_eval<F: PrimeField, E: FieldExtension<F> + Field>(
    a: &[E],
    b: &[E],
    worker: &Worker,
) -> (E, E, E) {
    assert!(a.len() > 0);
    assert_eq!(a.len(), b.len());

    let quart = F::from_u32_unchecked(4).inverse().unwrap();
    let half = a.len() / 2;
    let a_pairs = a.as_chunks::<2>().0;
    let b_pairs = b.as_chunks::<2>().0;

    // Each thread accumulates partial [f0, f1, f_half] over its chunk of
    // ADJACENT pairs (LSB binding), then we reduce across threads.  When half
    // < PAR_THRESHOLD the geometry has one chunk and smart_spawn runs on the
    // calling thread.
    let mut partial_results = vec![
        [E::ZERO; 3];
        worker
            .get_geometry_with_threshold(half, PAR_THRESHOLD)
            .len()
    ];

    let [f0, f1, mut f_half] = {
        worker.scope_with_threshold(half, PAR_THRESHOLD, |scope, geometry| {
            a_pairs
                .chunks_for_geometry(geometry)
                .enumerate()
                .zip(b_pairs.chunks_for_geometry(geometry))
                .zip(partial_results.iter_mut())
                .for_each(|(((idx, ap), bp), partial)| {
                    Worker::smart_spawn(scope, idx == geometry.len() - 1, |_| {
                        *partial = three_point_partial(ap, bp);
                    });
                });
        });

        partial_results
            .iter()
            .fold([E::ZERO; 3], |mut acc, partial| {
                acc[0].add_assign(&partial[0]);
                acc[1].add_assign(&partial[1]);
                acc[2].add_assign(&partial[2]);
                acc
            })
    };

    // quart scaling is applied once after the full reduction, not per-thread
    f_half.mul_assign_by_base(&quart);
    (f0, f1, f_half)
}

#[cfg(test)]
fn evaluate_monomial_form_serial<E: Field>(coeffs: &[E], point: &E) -> E {
    let mut result = E::ZERO;
    let mut c = E::ONE;
    for a in coeffs.iter() {
        let mut t = *a;
        t.mul_assign(&c);
        c.mul_assign(point);
        result.add_assign(&t);
    }
    result
}

pub fn evaluate_monomial_form<E: Field>(coeffs: &[E], point: &E, worker: &Worker) -> E {
    if coeffs.is_empty() {
        return E::ZERO;
    }

    let geometry = worker.get_geometry_with_threshold(coeffs.len(), PAR_THRESHOLD);
    let num_chunks = geometry.len();

    // offset_powers[j] = point^(start of chunk j), advanced by point^(size of chunk j)
    let pow = |exp: usize| {
        let mut result = E::ONE;
        let mut base = *point;
        let mut exp = exp;
        while exp > 0 {
            if exp & 1 == 1 {
                result.mul_assign(&base);
            }
            base.square();
            exp >>= 1;
        }
        result
    };
    let mut offset_powers = Vec::with_capacity(num_chunks);
    let mut current = E::ONE;
    for j in 0..num_chunks {
        offset_powers.push(current);
        current.mul_assign(&pow(geometry.get_chunk_size(j)));
    }

    let mut partial_results = vec![E::ZERO; num_chunks];

    worker.scope_with_threshold(coeffs.len(), PAR_THRESHOLD, |scope, geometry| {
        coeffs
            .chunks_for_geometry(geometry)
            .enumerate()
            .zip(partial_results.iter_mut())
            .for_each(|((idx, chunk), partial)| {
                Worker::smart_spawn(scope, idx == geometry.len() - 1, |_| {
                    // Horner within chunk, starting at relative power point^0
                    let mut acc = E::ZERO;
                    let mut c = E::ONE;
                    for a in chunk.iter() {
                        let mut t = *a;
                        t.mul_assign(&c);
                        c.mul_assign(point);
                        acc.add_assign(&t);
                    }
                    *partial = acc;
                });
            });
    });

    // result = sum_j offset_powers[j] * partial_results[j]
    let mut result = E::ZERO;
    for (offset, partial) in offset_powers.iter().zip(partial_results.iter()) {
        let mut t = *partial;
        t.mul_assign(offset);
        result.add_assign(&t);
    }
    result
}

fn special_lagrange_interpolate<E: Field>(
    eval_at_0: E,
    eval_at_1: E,
    eval_at_random: E,
    random_point: E,
) -> [E; 3] {
    // easier to compute special case than generic
    let mut coeffs_for_0 = [E::ZERO, E::ZERO, E::ONE];
    coeffs_for_0[1] = E::ONE;
    coeffs_for_0[1].add_assign(&random_point);
    coeffs_for_0[1].negate();

    coeffs_for_0[0] = E::ONE;
    coeffs_for_0[0].mul_assign(&random_point);

    let mut coeffs_for_1 = [E::ZERO, E::ZERO, E::ONE];
    coeffs_for_1[1] = E::ZERO;
    coeffs_for_1[1].add_assign(&random_point);
    coeffs_for_1[1].negate();

    coeffs_for_1[0] = E::ZERO;
    coeffs_for_1[0].mul_assign(&random_point);

    let mut coeffs_for_random_point = [E::ZERO, E::ZERO, E::ONE];
    coeffs_for_random_point[1] = E::ZERO;
    coeffs_for_random_point[1].add_assign(&E::ONE);
    coeffs_for_random_point[1].negate();

    coeffs_for_random_point[0] = E::ZERO;
    coeffs_for_random_point[0].mul_assign(&E::ONE);

    let mut dens = [E::ONE, E::ONE, E::ONE];

    let mut t = E::ZERO;
    t.sub_assign(&E::ONE);
    dens[0].mul_assign(&t);
    let mut t = E::ZERO;
    t.sub_assign(&random_point);
    dens[0].mul_assign(&t);

    let mut t = E::ONE;
    t.sub_assign(&E::ZERO);
    dens[1].mul_assign(&t);
    let mut t = E::ONE;
    t.sub_assign(&random_point);
    dens[1].mul_assign(&t);

    let mut t = random_point;
    t.sub_assign(&E::ZERO);
    dens[2].mul_assign(&t);
    let mut t = random_point;
    t.sub_assign(&E::ONE);
    dens[2].mul_assign(&t);

    let mut buffer = [E::ZERO; 3];
    batch_inverse_inplace(&mut dens, &mut buffer);

    let mut result = [E::ZERO; 3];
    for (eval, den, coeffs) in [
        (eval_at_0, dens[0], coeffs_for_0),
        (eval_at_1, dens[1], coeffs_for_1),
        (eval_at_random, dens[2], coeffs_for_random_point),
    ]
    .into_iter()
    {
        for (i, c) in coeffs.into_iter().enumerate() {
            let mut t = c;
            t.mul_assign(&den);
            t.mul_assign(&eval);
            result[i].add_assign(&t);
        }
    }

    result
}

pub(crate) use crate::gkr::sumcheck::eq_poly::make_pows;

pub(crate) fn update_eq_poly_reference<F: PrimeField, E: FieldExtension<F> + Field>(
    eq_poly: &mut [E],
    ood_samples: &[(E, E)],
    in_domain_samples: &[(F, E)],
    worker: &Worker,
) {
    assert!(eq_poly.len().is_power_of_two());
    assert_eq!(ood_samples.len(), 1);
    for (point, challenge) in ood_samples.iter() {
        let pows = make_pows(*point, eq_poly.len().trailing_zeros() as usize);
        let eq_table = crate::gkr::sumcheck::eq_poly::make_eq_table_lsb_first::<E>(&pows, worker);
        for (dst, src) in eq_poly.iter_mut().zip(eq_table.iter()) {
            let mut t = *challenge;
            t.mul_assign(src);
            dst.add_assign(&t);
        }
    }
    for (point, challenge) in in_domain_samples.iter() {
        let pows = make_pows(*point, eq_poly.len().trailing_zeros() as usize);
        let eq_table = crate::gkr::sumcheck::eq_poly::make_eq_table_lsb_first::<F>(&pows, worker);
        for (dst, src) in eq_poly.iter_mut().zip(eq_table.iter()) {
            let mut t = *challenge;
            t.mul_assign_by_base(src);
            dst.add_assign(&t);
        }
    }
}

fn evaluate_base_multivariate<F: PrimeField, E: FieldExtension<F> + Field>(
    evals: &[F],
    point: &[E],
    worker: &Worker,
) -> E {
    let eq = crate::gkr::sumcheck::eq_poly::make_eq_table_lsb_first::<E>(point, worker);
    assert_eq!(eq.len(), evals.len());
    let mut result = E::ZERO;
    for (a, b) in eq.iter().zip(evals.iter()) {
        let mut t = *a;
        t.mul_assign_by_base(b);
        result.add_assign(&t);
    }
    result
}

pub fn evaluate_multivariate<E: Field>(evals: &[E], point: &[E], worker: &Worker) -> E {
    let eq = crate::gkr::sumcheck::eq_poly::make_eq_table_lsb_first::<E>(point, worker);
    assert_eq!(eq.len(), evals.len());
    let mut result = E::ZERO;
    for (a, b) in eq.iter().zip(evals.iter()) {
        let mut t = *a;
        t.mul_assign(b);
        result.add_assign(&t);
    }
    result
}

fn evaluate_multivariate_at_base<F: PrimeField, E: FieldExtension<F> + Field>(
    evals: &[E],
    point: &[F],
    worker: &Worker,
) -> E {
    let eq = crate::gkr::sumcheck::eq_poly::make_eq_table_lsb_first::<F>(point, worker);
    assert_eq!(eq.len(), evals.len());
    let mut result = E::ZERO;
    for (a, b) in eq.iter().zip(evals.iter()) {
        let mut t = *b;
        t.mul_assign_by_base(a);
        result.add_assign(&t);
    }
    result
}

fn evaluate_multivariate_at_base_for_domain_hypercube<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
>(
    evals: &[E],
    point: &[F],
) -> E {
    let eq = crate::gkr::sumcheck::eq_poly::make_domain_eq_table_lsb_first::<F, F>(point);
    assert_eq!(eq.len(), evals.len());
    let mut result = E::ZERO;
    for (a, b) in eq.iter().zip(evals.iter()) {
        let mut t = *b;
        t.mul_assign_by_base(a);
        result.add_assign(&t);
    }
    result
}

fn evals_to_multilinear_coeffs<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field>(
    data: &mut [E],
    base_root_inv: &F,
    high_powers_offsets: &[F],
    two_inv: &F,
    num_folding_rounds: usize,
    buf_a: &mut [E],
    buf_b: &mut [E],
) {
    let n = 1usize << num_folding_rounds;
    assert_eq!(data.len(), n);
    if num_folding_rounds == 0 {
        return;
    }
    assert!(buf_a.len() >= n);
    assert!(buf_b.len() >= n);

    let mut root_inv = *base_root_inv;

    // stage reads from `src` and writes `dst`. At stage 0 we read
    // from `data`; afterwards we alternate between buf_a and buf_b.
    for stage in 0..num_folding_rounds {
        let src: &[E] = if stage == 0 {
            &*data
        } else if stage % 2 == 1 {
            unsafe { core::slice::from_raw_parts(buf_a.as_ptr(), n) }
        } else {
            unsafe { core::slice::from_raw_parts(buf_b.as_ptr(), n) }
        };
        let dst: &mut [E] = if stage % 2 == 0 {
            unsafe { core::slice::from_raw_parts_mut(buf_a.as_mut_ptr(), n) }
        } else {
            unsafe { core::slice::from_raw_parts_mut(buf_b.as_mut_ptr(), n) }
        };

        let num_existing = 1usize << stage;
        let bit = 1usize << stage;
        let block_len = n >> stage;
        let half = block_len / 2;

        for idx in 0..num_existing {
            let base = idx * block_len;
            let out_base = idx * half;
            let linear_base = (idx | bit) * half;
            for set_idx in 0..half {
                let a = src[base + 2 * set_idx];
                let b = src[base + 2 * set_idx + 1];

                let mut root = root_inv;
                root.mul_assign(&high_powers_offsets[set_idx]);

                let mut c_even = a;
                c_even.add_assign(&b);
                c_even.mul_assign_by_base(two_inv);

                let mut c_odd = a;
                c_odd.sub_assign(&b);
                c_odd.mul_assign_by_base(&root);
                c_odd.mul_assign_by_base(two_inv);

                dst[out_base + set_idx] = c_even;
                dst[linear_base + set_idx] = c_odd;
            }
        }

        root_inv.square();
    }

    let final_buf: &[E] = if num_folding_rounds % 2 == 1 {
        unsafe { core::slice::from_raw_parts(buf_a.as_ptr(), n) }
    } else {
        unsafe { core::slice::from_raw_parts(buf_b.as_ptr(), n) }
    };
    data.copy_from_slice(&final_buf[..n]);
}

#[cfg(test)]
fn eval_multilinear_from_coeffs<E: Field>(coeffs: &[E], challenges: &[E]) -> E {
    let eq_weights = precompute_monomial_tensor(challenges);
    eval_multilinear_with_monomial_tensor(coeffs, &eq_weights)
}

fn precompute_monomial_tensor<E: Field>(challenges: &[E]) -> Vec<E> {
    let k = challenges.len();
    let mut weights = vec![E::ZERO; 1 << k];
    weights[0] = E::ONE;
    for (j, alpha) in challenges.iter().enumerate() {
        for i in (0..(1 << j)).rev() {
            let w = weights[i];
            let mut w_alpha = w;
            w_alpha.mul_assign(alpha);
            weights[i + (1 << j)] = w_alpha;
        }
    }
    weights
}

fn eval_multilinear_with_monomial_tensor<E: Field>(coeffs: &[E], eq_weights: &[E]) -> E {
    assert_eq!(coeffs.len(), eq_weights.len());
    let mut result = E::ZERO;
    for (c, w) in coeffs.iter().zip(eq_weights.iter()) {
        let mut t = *c;
        t.mul_assign(w);
        result.add_assign(&t);
    }
    result
}

#[cfg(test)]
fn fold_coset<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field>(
    mut flattened_evals: Vec<E>,
    num_folding_rounds: usize,
    folding_challenges: &[E],
    base_root_inv: &F,
    high_powers_offsets: &[F],
    two_inv: &F,
) -> E {
    assert_eq!(num_folding_rounds, folding_challenges.len());
    debug_assert_eq!(high_powers_offsets[0], F::ONE);
    let mut root_inv = *base_root_inv;
    // Now we can fold queries values, in a normal FRI style
    let mut buffer = Vec::with_capacity(flattened_evals.len());
    for folding_step in 0..num_folding_rounds {
        let (src, dst) = if folding_step % 2 == 0 {
            (&flattened_evals[..], &mut buffer)
        } else {
            (&buffer[..], &mut flattened_evals)
        };
        assert!(dst.is_empty());
        assert!(src.is_empty() == false);
        assert!(src.len().is_power_of_two());
        assert_eq!(src.len(), 1 << (num_folding_rounds - folding_step));
        let folding_challenge = folding_challenges[folding_step];
        for (set_idx, [a, b]) in src.as_chunks::<2>().0.iter().enumerate() {
            let mut t = *a;
            t.sub_assign(b);
            t.mul_assign(&folding_challenge);

            let mut root = root_inv;
            root.mul_assign(&high_powers_offsets[set_idx]);

            t.mul_assign_by_base(&root);

            t.add_assign(a);
            t.add_assign(b);
            t.mul_assign_by_base(two_inv);
            dst.push(t);
        }
        if folding_step % 2 == 0 {
            flattened_evals.clear();
        } else {
            buffer.clear();
        };
        root_inv.square();
    }

    let folded = if num_folding_rounds % 2 == 1 {
        &buffer[..]
    } else {
        &flattened_evals[..]
    };
    assert_eq!(folded.len(), 1);

    folded[0]
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4},
        merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap,
    };
    use field::FieldExtension;
    use rand::{rngs::ThreadRng, RngCore};

    type F = BabyBearField;
    type E = BabyBearExt4;

    fn random_e(rng: &mut ThreadRng) -> E
    where
        [(); <E as FieldExtension<F>>::DEGREE]: Sized,
    {
        let coefs = [(); <E as FieldExtension<F>>::DEGREE]
            .map(|_| F::from_u32_with_reduction(rng.next_u32()));

        <E as FieldExtension<F>>::from_coeffs(coefs)
    }

    use proptest::prelude::*;
    use proptest::prop_assert_eq;

    fn arb_base() -> impl Strategy<Value = F> {
        any::<u32>().prop_map(F::from_u32_with_reduction)
    }

    fn arb_ext() -> impl Strategy<Value = E> {
        [any::<u32>(); 4].prop_map(|raw| {
            let coefs = raw.map(F::from_u32_with_reduction);
            <E as FieldExtension<F>>::from_coeffs(coefs)
        })
    }

    fn arb_ext_vec(len: usize) -> impl Strategy<Value = Vec<E>> {
        proptest::collection::vec(arb_ext(), len)
    }

    fn coeffs_based_folding_matches_fold_coset(
        num_folding_rounds: usize,
        evals: Vec<E>,
        challenges: Vec<E>,
        base_root_raw: F,
    ) -> Result<(), proptest::prelude::TestCaseError> {
        use fft::{
            bitreverse_enumeration_inplace, domain_generator_for_size,
            materialize_powers_serial_starting_with_one,
        };

        let values_per_leaf = 1usize << num_folding_rounds;

        let base_root = if base_root_raw == F::ZERO {
            F::ONE
        } else {
            base_root_raw
        };
        let base_root_inv = base_root.inverse().unwrap();

        let set_generator = domain_generator_for_size::<F>(values_per_leaf as u64);
        let mut high_powers_offsets = materialize_powers_serial_starting_with_one::<F, Global>(
            set_generator.inverse().unwrap(),
            1 << (num_folding_rounds - 1),
        );
        bitreverse_enumeration_inplace(&mut high_powers_offsets);

        let folded_old = fold_coset(
            evals.clone(),
            num_folding_rounds,
            &challenges,
            &base_root_inv,
            &high_powers_offsets,
            &F::HALF,
        );

        let mut coeffs = evals;
        let mut scratch_a = vec![E::ZERO; values_per_leaf];
        let mut scratch_b = vec![E::ZERO; values_per_leaf];
        evals_to_multilinear_coeffs(
            &mut coeffs,
            &base_root_inv,
            &high_powers_offsets,
            &F::HALF,
            num_folding_rounds,
            &mut scratch_a,
            &mut scratch_b,
        );
        let folded_new = eval_multilinear_from_coeffs(&coeffs, &challenges);

        prop_assert_eq!(folded_old, folded_new);
        Ok(())
    }

    proptest::proptest! {
        #[test]
        fn test_coeffs_folding_k1(
            evals in arb_ext_vec(2),
            challenges in arb_ext_vec(1),
            base_root in arb_base(),
        ) {
            coeffs_based_folding_matches_fold_coset(1, evals, challenges, base_root)?;
        }
        #[test]
        fn test_coeffs_folding_k2(
            evals in arb_ext_vec(4),
            challenges in arb_ext_vec(2),
            base_root in arb_base(),
        ) {
            coeffs_based_folding_matches_fold_coset(2, evals, challenges, base_root)?;
        }
        #[test]
        fn test_coeffs_folding_k3(
            evals in arb_ext_vec(8),
            challenges in arb_ext_vec(3),
            base_root in arb_base(),
        ) {
            coeffs_based_folding_matches_fold_coset(3, evals, challenges, base_root)?;
        }
        #[test]
        fn test_coeffs_folding_k4(
            evals in arb_ext_vec(16),
            challenges in arb_ext_vec(4),
            base_root in arb_base(),
        ) {
            coeffs_based_folding_matches_fold_coset(4, evals, challenges, base_root)?;
        }
    }

    /// The fused leaf conversion (evaluation-form cosets, leaves converted
    /// while the tree hashes them and at query time) must produce the same
    /// tree and the same query leaves as the in-place conversion pass.
    #[test]
    fn fused_leaf_conversion_matches_in_place() {
        use crate::gkr::prover::stages::commitment_utils::compute_column_major_lde_from_monomial_form;
        use fft::Twiddles;
        use field::Rand;
        let worker = Worker::new_with_num_threads(4);
        let mut rng = rand::thread_rng();
        for (poly_log2, lde_factor, values_per_leaf) in
            [(10usize, 8usize, 16usize), (12, 4, 32), (9, 16, 4)]
        {
            let poly_size = 1usize << poly_log2;
            let monomial: Vec<E> = (0..poly_size)
                .map(|_| E::random_element(&mut rng))
                .collect();
            let twiddles = Twiddles::<F, Global>::new(poly_size, &worker);
            let cosets = compute_column_major_lde_from_monomial_form(
                &monomial,
                &twiddles,
                lde_factor,
                Some(&worker),
            );
            let make = || -> Vec<(Box<[E]>, F)> {
                cosets
                    .iter()
                    .map(|(col, off)| (col.to_vec().into_boxed_slice(), *off))
                    .collect()
            };
            let reference = commit_single_ext_poly_with_transform_for_test::<
                F,
                E,
                Blake2sU32MerkleTreeWithCap,
            >(make(), values_per_leaf, 4, &worker);
            let fused = commit_single_ext_poly::<F, E, Blake2sU32MerkleTreeWithCap, _>(
                make(),
                values_per_leaf,
                4,
                &crate::gkr::prover::backend::NaiveBackend,
                &worker,
            );
            assert_eq!(
                reference.tree.get_cap(),
                fused.tree.get_cap(),
                "cap {poly_log2}/{lde_factor}/{values_per_leaf}"
            );
            let num_leaves = lde_factor * poly_size / values_per_leaf;
            for index in [0usize, 1, 7, num_leaves / 3, num_leaves - 1] {
                let (_, a, qa) = reference.query_for_folded_index(index);
                let (_, b, qb) = fused.query_for_folded_index(index);
                assert_eq!(a, b, "leaf {index}");
                assert_eq!(qa.leaf_values_concatenated, qb.leaf_values_concatenated);
                assert_eq!(qa.path, qb.path);
            }
            #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
            {
                let avx2 = commit_single_ext_poly::<F, E, Blake2sU32MerkleTreeWithCap, _>(
                    make(),
                    values_per_leaf,
                    4,
                    &crate::gkr::prover::DefaultBabyBearBackend::default(),
                    &worker,
                );
                assert_eq!(reference.tree.get_cap(), avx2.tree.get_cap(), "avx2 cap");
                for index in [0usize, 3, num_leaves - 1] {
                    assert_eq!(
                        reference.query_for_folded_index(index).1,
                        avx2.query_for_folded_index(index).1
                    );
                }
            }
        }
    }

    fn commit_ext_poly_coeffs_match_fold_coset(
        monomial: Vec<E>,
        challenges: Vec<E>,
        query_index_frac: f64,
    ) -> Result<(), proptest::prelude::TestCaseError> {
        use crate::gkr::prover::stages::commitment_utils::compute_column_major_lde_from_monomial_form;
        use fft::Twiddles;

        let worker = Worker::new_with_num_threads(4);
        let poly_size = monomial.len();
        let lde_factor = 8usize;
        let values_per_leaf = 16usize;
        let num_folding_rounds = values_per_leaf.trailing_zeros() as usize;
        assert_eq!(challenges.len(), num_folding_rounds);

        let twiddles = Twiddles::<F, Global>::new(poly_size, &worker);

        let cosets = compute_column_major_lde_from_monomial_form(
            &monomial,
            &twiddles,
            lde_factor,
            Some(&worker),
        );
        let raw_cosets: Vec<(Vec<E>, F)> = cosets
            .iter()
            .map(|(col, off)| (col.to_vec(), *off))
            .collect();

        let oracle = commit_single_ext_poly::<F, E, Blake2sU32MerkleTreeWithCap, _>(
            cosets,
            values_per_leaf,
            16,
            &crate::gkr::prover::backend::NaiveBackend,
            &worker,
        );

        let set_generator = domain_generator_for_size::<F>(values_per_leaf as u64);
        let mut high_powers_offsets = materialize_powers_serial_starting_with_one::<F, Global>(
            set_generator.inverse().unwrap(),
            values_per_leaf / 2,
        );
        bitreverse_enumeration_inplace(&mut high_powers_offsets);

        let rs_domain_size = poly_size * lde_factor;
        let extended_generator = domain_generator_for_size::<F>(rs_domain_size as u64);
        let offsets_vec = offsets_vec_for_leaf_construction(poly_size, values_per_leaf);
        let num_cosets = lde_factor;
        let monomial_weights = precompute_monomial_tensor(&challenges);

        let num_leaves_per_coset = poly_size / values_per_leaf;
        let query_domain_size = num_leaves_per_coset * num_cosets;
        let query_index = ((query_index_frac.abs() % 1.0) * query_domain_size as f64) as usize;
        let query_index = query_index.min(query_domain_size - 1);

        let coset_index = query_index % num_cosets;
        let internal_index = query_index / num_cosets;

        let (_ci, coeffs, _query) = oracle.query_for_folded_index(query_index);
        let result_new = eval_multilinear_with_monomial_tensor(&coeffs, &monomial_weights);

        let mut raw_leaf = Vec::with_capacity(values_per_leaf);
        for &off in offsets_vec.iter() {
            raw_leaf.push(raw_cosets[coset_index].0[off + internal_index]);
        }
        let base_root = extended_generator.pow(query_index as u32);
        let base_root_inv = base_root.inverse().unwrap();
        let result_old = fold_coset(
            raw_leaf,
            num_folding_rounds,
            &challenges,
            &base_root_inv,
            &high_powers_offsets,
            &F::HALF,
        );

        prop_assert_eq!(result_new, result_old);
        Ok(())
    }

    proptest::proptest! {
        #![proptest_config(proptest::prelude::ProptestConfig::with_cases(32))]
        #[test]
        fn test_commit_ext_poly_stores_coefficients(
            monomial in arb_ext_vec(256),
            challenges in arb_ext_vec(4),
            query_frac in 0.0f64..1.0,
        ) {
            commit_ext_poly_coeffs_match_fold_coset(monomial, challenges, query_frac)?;
        }
    }

    #[test]
    fn test_fold_monomial_form() {
        let mut rng = rand::rng();
        let size = 1 << 13;
        let input: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();
        let challenge = random_e(&mut rng);

        let mut input_ser = input.clone();
        let mut buffer_ser: Vec<E> = Vec::with_capacity(size / 2);
        fold_monomial_form_serial(&mut input_ser, &mut buffer_ser, &challenge);

        for num_threads in [1, 2, 4, 8] {
            let worker = Worker::new_with_num_threads(num_threads);
            let mut input_par = input.clone();
            let mut buffer_par: Vec<E> = Vec::with_capacity(size / 2);
            fold_monomial_form(&mut input_par, &mut buffer_par, &challenge, &worker);
            assert_eq!(
                input_par, input_ser,
                "fold_monomial_form mismatch with {} threads",
                num_threads
            );
        }
    }

    // fn make_base_oracle(
    //     size: usize,
    //     worker: &Worker,
    // ) -> ColumnMajorBaseOracleForLDE<F, Blake2sU32MerkleTreeWithCap> {
    //     let main_domain: Vec<F> = (1..=size).map(|el| {
    //         F::from_u32_unchecked(el as u32)
    //     }).collect();
    //     let twiddles = Twiddles::<F, Global>::new(size, worker);
    //     let main_domain = Arc::new(main_domain.into_boxed_slice());

    //     let other_domains =
    //         compute_column_major_lde_from_main_domain(main_domain.clone(), &twiddles, 2);
    //     let original_values_normal_order = ColumnMajorCosetBoundTracePart {
    //         column: main_domain,
    //         offset: F::ONE,
    //     };
    //     let source = Some(original_values_normal_order)
    //         .into_iter()
    //         .chain(other_domains.into_iter());

    //     let mut result = ColumnMajorBaseOracleForLDE { cosets: vec![] };
    //     for coset in source {
    //         let el = ColumnMajorBaseOracleForCoset {
    //             original_values_normal_order: vec![coset],
    //             tree: <Blake2sU32MerkleTreeWithCap as ColumnMajorMerkleTreeConstructor<F>>::dummy(),
    //             values_per_leaf: 2,
    //             trace_len_log2: size.trailing_zeros() as usize,
    //         };
    //         result.cosets.push(el);
    //     }

    //     result
    // }

    fn make_base_oracle(
        size: usize,
        worker: &Worker,
        offset: usize,
    ) -> (
        ColumnMajorBaseOracleForLDE<F, Blake2sU32MerkleTreeWithCap>,
        Vec<F>,
    ) {
        todo!();

        // let coeffs: Vec<F> = (1..=size)
        //     .map(|el| F::from_u32_with_reduction((el + offset) as u32))
        //     .collect();
        // let twiddles = Twiddles::<F, Global>::new(size, worker);

        // let cosets = compute_column_major_lde_from_monomial_form(&coeffs, &twiddles, 2);

        // let mut result = ColumnMajorBaseOracleForLDE { cosets: vec![] };
        // for (column, offset) in cosets.into_iter() {
        //     let tree = <Blake2sU32MerkleTreeWithCap as ColumnMajorMerkleTreeConstructor<F>>::construct_for_column_major_coset::<F, Global>(
        //         &[&column[..]],
        //         2,
        //         1,
        //         true,
        //         false,
        //         worker
        //     );
        //     let el = ColumnMajorBaseOracleForCoset {
        //         original_values_normal_order: vec![ColumnMajorCosetBoundTracePart {
        //             column: Arc::new(column),
        //             offset,
        //         }],
        //         tree,
        //         values_per_leaf: 2,
        //         trace_len_log2: size.trailing_zeros() as usize,
        //     };
        //     result.cosets.push(el);
        // }

        // (result, coeffs)
    }

    #[test]
    fn test_fold_evaluation_form() {
        let mut rng = rand::rng();
        let size = 1 << 13;
        let input: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();
        let challenge = random_e(&mut rng);

        let mut input_ser = input.clone();
        let expected = fold_evaluation_form_serial::<F, E>(&mut input_ser, &challenge);
        let expected = expected.to_vec();

        for num_threads in [1, 2, 4, 8] {
            let worker = Worker::new_with_num_threads(num_threads);
            let mut input_par = input.clone();
            let got = fold_evaluation_form::<F, E>(&mut input_par, &challenge, &worker);
            assert_eq!(
                got,
                expected.as_slice(),
                "fold_evaluation_form mismatch with {} threads",
                num_threads
            );
        }
    }

    #[test]
    fn ping_pong_fold_matches_fold_eq_poly() {
        use crate::allocation_pool::GenericAllocationPool;
        use crate::gkr::prover::gkr_backend::NaiveGKRBackend;
        use field::Rand;
        let worker = Worker::new_with_num_threads(4);
        let mut rng = rand::thread_rng();
        let n = 1usize << 12;
        let table: Vec<E> = (0..n).map(|_| E::random_element(&mut rng)).collect();
        let challenges: Vec<E> = (0..5).map(|_| E::random_element(&mut rng)).collect();
        let pool = GenericAllocationPool::<F, E>::new();
        let mut pp = PingPongPoly::<E>::new_ext::<F>(n, &pool, |dst| {
            for (d, v) in dst.iter_mut().zip(table.iter()) {
                d.write(*v);
            }
        });
        let mut reference = table.clone();
        let mut reference_slice: &mut [E] = &mut reference[..];
        for ch in challenges.iter() {
            reference_slice = fold_eq_poly::<F, E>(reference_slice, ch, &worker);
            pp.fold::<F, NaiveGKRBackend>(ch, &NaiveGKRBackend, &worker);
            assert_eq!(pp.len(), reference_slice.len());
            assert_eq!(pp.as_slice(), &*reference_slice);
        }
        pp.release::<F>(&pool);
        assert_eq!(
            pool.stats().retained_bytes,
            (n + n / 2) * core::mem::size_of::<E>()
        );
    }

    #[test]
    fn test_fold_eq_poly() {
        let mut rng = rand::rng();
        let size = 1 << 13;
        let eq: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();
        let challenge = random_e(&mut rng);

        let mut eq_ser = eq.clone();
        let expected = fold_eq_poly_serial::<F, E>(&mut eq_ser, &challenge);
        let expected = expected.to_vec();

        for num_threads in [1, 2, 4, 8] {
            let worker = Worker::new_with_num_threads(num_threads);
            let mut eq_par = eq.clone();
            let got = fold_eq_poly::<F, E>(&mut eq_par, &challenge, &worker);
            assert_eq!(
                got,
                expected.as_slice(),
                "fold_eq_poly mismatch with {} threads",
                num_threads
            );
        }
    }

    #[test]
    fn test_special_three_point_eval() {
        let mut rng = rand::rng();
        let size = 1 << 12;
        let a: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();
        let b: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();

        let (e_f0, e_f1, e_fh) = special_three_point_eval_serial::<F, E>(&a, &b);

        for num_threads in [1, 2, 4, 8] {
            let worker = Worker::new_with_num_threads(num_threads);
            let (f0, f1, fh) = special_three_point_eval::<F, E>(&a, &b, &worker);
            assert_eq!(
                (f0, f1, fh),
                (e_f0, e_f1, e_fh),
                "special_three_point_eval mismatch with {} threads",
                num_threads
            );
        }
    }

    #[test]
    fn test_dot_product() {
        let mut rng = rand::rng();
        let size = 1 << 13;
        let a: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();
        let b: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();

        let expected = dot_product_serial::<F, E>(&a, &b);

        for num_threads in [1, 2, 4, 8] {
            let worker = Worker::new_with_num_threads(num_threads);
            let got = dot_product::<F, E>(&a, &b, &worker);
            assert_eq!(
                got, expected,
                "dot_product mismatch with {} threads",
                num_threads
            );
        }
    }

    #[test]
    fn test_evaluate_monomial_form() {
        let mut rng = rand::rng();
        let size = 1 << 13;
        let coeffs: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();
        let point = random_e(&mut rng);

        let expected = evaluate_monomial_form_serial(&coeffs, &point);

        for num_threads in [1, 2, 4, 8] {
            let worker = Worker::new_with_num_threads(num_threads);
            let got = evaluate_monomial_form(&coeffs, &point, &worker);
            assert_eq!(
                got, expected,
                "evaluate_monomial_form mismatch with {} threads",
                num_threads
            );
        }
    }

    #[test]
    fn test_special_three_point_eval_correctness() {
        let mut rng = rand::rng();
        let worker = Worker::new_with_num_threads(8);
        let quart_inv = F::from_u32_unchecked(4).inverse().unwrap();

        for size_log2 in [3u32, 13] {
            let size = 1 << size_log2;
            let a: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();
            let b: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();
            let half = size / 2;

            // f(0) = dot(a[0..half], b[0..half])
            let expected_f0 = (0..half).fold(E::ZERO, |mut acc, i| {
                let mut t = a[i];
                t.mul_assign(&b[i]);
                acc.add_assign(&t);
                acc
            });
            // f(1) = dot(a[half..], b[half..])
            let expected_f1 = (0..half).fold(E::ZERO, |mut acc, i| {
                let mut t = a[i + half];
                t.mul_assign(&b[i + half]);
                acc.add_assign(&t);
                acc
            });
            // f(1/2) = 1/4 * sum_i (a[i]+a[i+half]) * (b[i]+b[i+half])
            let mut expected_fh = (0..half).fold(E::ZERO, |mut acc, i| {
                let mut ta = a[i];
                ta.add_assign(&a[i + half]);
                let mut tb = b[i];
                tb.add_assign(&b[i + half]);
                ta.mul_assign(&tb);
                acc.add_assign(&ta);
                acc
            });
            expected_fh.mul_assign_by_base(&quart_inv);

            let full_dot = (0..size).fold(E::ZERO, |mut acc, i| {
                let mut t = a[i];
                t.mul_assign(&b[i]);
                acc.add_assign(&t);
                acc
            });
            let mut f0_plus_f1 = expected_f0;
            f0_plus_f1.add_assign(&expected_f1);
            assert_eq!(f0_plus_f1, full_dot, "sanity: f(0)+f(1) == dot(a,b)");

            let (f0, f1, fh) = special_three_point_eval::<F, E>(&a, &b, &worker);
            assert_eq!(f0, expected_f0, "f(0) wrong at size 2^{}", size_log2);
            assert_eq!(f1, expected_f1, "f(1) wrong at size 2^{}", size_log2);
            assert_eq!(fh, expected_fh, "f(1/2) wrong at size 2^{}", size_log2);
        }
    }
    #[test]
    fn test_evaluate_monomial_form_correctness() {
        let mut rng = rand::rng();
        let worker = Worker::new_with_num_threads(8);

        // f(x) = 3 + 5x  at  x = 2  →  3 + 10 = 13
        {
            let c0 = E::from_base(F::from_u32_unchecked(3));
            let c1 = E::from_base(F::from_u32_unchecked(5));
            let x = E::from_base(F::from_u32_unchecked(2));
            let mut expected = c1;
            expected.mul_assign(&x);
            expected.add_assign(&c0);
            assert_eq!(evaluate_monomial_form(&[c0, c1], &x, &worker), expected);
        }

        {
            let n = 2048usize;
            let p = E::from_base(F::from_u32_unchecked(3));
            let mut coeffs = vec![E::ZERO; n];
            *coeffs.last_mut().unwrap() = E::ONE;
            let expected = (0..n - 1).fold(E::ONE, |mut acc, _| {
                acc.mul_assign(&p);
                acc
            });
            assert_eq!(evaluate_monomial_form(&coeffs, &p, &worker), expected);
        }

        for size_log2 in [3u32, 13] {
            let size = 1 << size_log2;
            let coeffs: Vec<E> = (0..size).map(|_| random_e(&mut rng)).collect();
            let p = random_e(&mut rng);

            let expected = {
                let mut acc = E::ZERO;
                let mut pow = E::ONE;
                for c in coeffs.iter() {
                    let mut t = *c;
                    t.mul_assign(&pow);
                    acc.add_assign(&t);
                    pow.mul_assign(&p);
                }
                acc
            };

            let got = evaluate_monomial_form(&coeffs, &p, &worker);
            assert_eq!(
                got, expected,
                "evaluate_monomial_form wrong at size 2^{}",
                size_log2
            );
        }
    }

    #[test]
    fn test_domain_hypercube_evals() {
        let worker = Worker::new_with_num_threads(1);
        let size: usize = 4;

        let main_domain: Vec<F> = (1..=size)
            .map(|el| F::from_u32_unchecked(el as u32))
            .collect();
        dbg!(&main_domain);

        let root = domain_generator_for_size::<F>(size as u64);
        let domain = materialize_powers_serial_starting_with_one::<F, Global>(root, size);
        dbg!(&domain);
        for i in 0..size {
            dbg!(i);
            let domain_point = root.pow(i as u32);
            let pows = make_pows(domain_point, size.trailing_zeros() as usize);
            dbg!(&pows);
            let value = evaluate_multivariate_at_base_for_domain_hypercube(&main_domain, &pows);
            dbg!(value);
        }
    }

    #[test]
    fn test_whir() {
        let worker = Worker::new_with_num_threads(1);
        let size = 128;

        let mut inputs = vec![];
        let mut monomial_forms = vec![];
        for i in 0..3 {
            let (input, monomial) = make_base_oracle(size, &worker, i * 32);
            inputs.push(input);
            monomial_forms.push(monomial);
        }

        let [mem, wit, setup] = inputs.try_into().unwrap();

        let original_evaluation_point: Vec<_> = (0..size.trailing_zeros())
            .map(|el| E::from_base(F::from_u32_unchecked(4 << el)))
            .collect();
        let twiddles = Twiddles::<F, Global>::new(size, &worker);

        let original_claims: Vec<_> = monomial_forms
            .iter()
            .map(|el| {
                // compute on hypercube
                let mut t = el.to_vec();
                bitreverse_enumeration_inplace(&mut t);
                multivariate_coeffs_into_hypercube_evals(&mut t, size.trailing_zeros());
                let eval = evaluate_base_multivariate(&t, &original_evaluation_point, &worker);

                vec![eval]
            })
            .collect::<Vec<_>>();

        let [a, b, c] = original_claims.try_into().unwrap();

        let whir_schedule = WhirSchedule {
            base_lde_factor: 2,
            cap_size: 1,
            whir_steps_schedule: vec![1, 2, 3],
            whir_queries_schedule: vec![4, 4, 4],
            whir_steps_lde_factors: vec![8, 16],
            whir_pow_schedule: vec![10, 10, 10],
        };

        let setup_commitment = crate::gkr::prover::SetupCommitment::InMemory(setup);
        let mut gkr_storage = GKRStorage::<F, E>::default();
        for (key, monomial) in [
            GKRAddress::BaseLayerMemory(0),
            GKRAddress::BaseLayerWitness(0),
            GKRAddress::Setup(0),
        ]
        .into_iter()
        .zip(monomial_forms.iter())
        {
            let mut t = monomial.to_vec();
            bitreverse_enumeration_inplace(&mut t);
            multivariate_coeffs_into_hypercube_evals(&mut t, size.trailing_zeros());
            gkr_storage.insert_base_field_at_layer(
                0,
                key,
                crate::gkr::sumcheck::access_and_fold::BaseFieldPoly::new(t.into_boxed_slice()),
            );
        }
        let proof = whir_fold::<F, E, _, ::transcript::Blake2sTranscript, _, _>(
            mem,
            a,
            wit,
            b,
            &setup_commitment,
            c,
            gkr_storage,
            0,
            original_evaluation_point,
            E::from_base(F::from_u32_with_reduction(7)),
            &whir_schedule,
            &twiddles,
            ::transcript::Seed::default(),
            1,
            size.trailing_zeros() as usize,
            &crate::gkr::prover::backend::NaiveBackend,
            &crate::gkr::prover::gkr_backend::NaiveGKRBackend,
            WhirIntermediateOracleMode::Monolithic,
            &GenericAllocationPool::proxy(),
            &worker,
        );
    }
}
