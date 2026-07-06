//! Coset-by-coset commitment for production-sized WHIR base oracles (8 witness
//! polys of 2^26, 1 setup poly of 2^26).
//!
//! The monolithic [`commit_trace_part`](crate::gkr::prover::stages::stage1::commit_trace_part)
//! materializes the entire RS codeword (message x LDE factor, e.g. 2^26 x 32 =
//! 2^31 per column) and one Merkle tree over all of it. For 8+1 columns that is
//! hundreds of GB. Instead, this commitment:
//!
//!   * keeps only the per-column monomial forms (message-sized), and
//!   * processes ONE LDE coset at a time: compute its evaluations, hash its
//!     leaves, build its subtree, keep only the subtree root, then drop the
//!     coset data. Peak memory is ~one coset instead of the whole codeword.
//!
//! A small top tree over the per-coset roots yields the commitment cap. The full
//! tree's cap equals this top-tree cap because each coset's leaves occupy a
//! contiguous, power-of-two block whose subtree root is a single node.
//!
//! WHIR's initial queries recompute the single coset a query lands in, produce
//! the within-coset Merkle path there, and stitch it to the top-tree path. The
//! result is byte-identical to `ColumnMajorBaseOracleForLDE::tree.get_proof`.

use super::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs;
use super::offsets_vec_for_leaf_construction;
use super::queries::{BaseFieldQuery, ExtensionFieldQuery};
use crate::definitions::DIGEST_SIZE_U32_WORDS;
use crate::gkr::prover::stages::stage1::{
    compute_column_major_lde_single_coset, compute_column_major_lde_single_coset_with_offset,
    compute_column_major_lde_single_coset_with_offset_serial,
};
use crate::merkle_trees::keccak256_for_everything_tree::{Digest32, Keccak256MerkleTreeWithCap};
use crate::merkle_trees::keccak256_hash_leafs::keccak256_leaf_hashes_from_cosets;
use crate::merkle_trees::{ColumnMajorMerkleTreeConstructor, MerkleTreeCapVarLength};
use core::marker::PhantomData;
use fft::{
    bitreverse_enumeration_inplace, bitreverse_index, domain_generator_for_size,
    materialize_powers_serial_starting_with_one, Twiddles,
};
use field::{Field, FieldExtension, PrimeField, Proth120, TwoAdicField};
use std::alloc::Global;
use worker::Worker;

pub type Tree = Keccak256MerkleTreeWithCap<Global>;

/// Run `f(0..len)` across the worker's threads, collecting the results in order.
/// (Small helper mirroring the `spare_capacity_mut` + `split_at_mut_unchecked`
/// pattern used by the Merkle-tree builder, so per-column work runs in parallel.)
fn parallel_collect<T: Send, F: Fn(usize) -> T + Sync>(
    worker: &Worker,
    len: usize,
    f: F,
) -> Vec<T> {
    let mut result: Vec<T> = Vec::with_capacity(len);
    if len == 0 {
        return result;
    }
    unsafe {
        worker.scope(len, |scope, geometry| {
            let mut dst = &mut result.spare_capacity_mut()[..len];
            let f = &f;
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                let (dst_chunk, rest) = dst.split_at_mut_unchecked(chunk_size);
                dst = rest;
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    for (j, slot) in dst_chunk.iter_mut().enumerate() {
                        slot.write(f(chunk_start + j));
                    }
                });
            }
        });
        result.set_len(len);
    }
    result
}

/// Compute one coset's LDE evaluations for every column. Columns are done one at a
/// time because each `compute_column_major_lde_single_coset` is itself worker-parallel
/// (parallelizing over columns on top would only oversubscribe the pool).
fn coset_columns(
    monomial_forms: &[Vec<Proth120>],
    twiddles: &Twiddles<Proth120, Global>,
    lde_factor: usize,
    coset_index: usize,
    worker: &Worker,
) -> Vec<Box<[Proth120]>> {
    monomial_forms
        .iter()
        .map(|m| {
            compute_column_major_lde_single_coset(m, twiddles, lde_factor, coset_index, worker)
        })
        .collect()
}

/// A base-oracle commitment (witness = 8 columns, or setup = 1 column) built
/// coset-by-coset. Holds the message monomial forms (needed to recompute cosets
/// for queries) and the small top tree over the per-coset subtree roots.
#[derive(Clone, Debug)]
pub struct CosetByCosetBaseCommitment {
    /// Per-column multilinear monomial coefficients (message-sized, normal order).
    pub monomial_forms: Vec<Vec<Proth120>>,
    /// log2 of the message (per-coset) length.
    pub trace_len_log2: usize,
    /// Number of LDE cosets (= LDE factor).
    pub lde_factor: usize,
    /// Values packed per Merkle leaf (2^whir_first_fold_step_log2).
    pub values_per_leaf: usize,
    /// Merkle cap size (number of top nodes).
    pub cap_size: usize,
    /// Top tree over the per-coset roots (its leaves are the roots in physical,
    /// i.e. bit-reversed-coset, order). Provides the cap and the top-tree paths.
    pub top_tree: Tree,
}

impl CosetByCosetBaseCommitment {
    /// Number of leaves in one coset's subtree.
    #[inline]
    pub fn coset_tree_size(&self) -> usize {
        (1usize << self.trace_len_log2) / self.values_per_leaf
    }

    /// The commitment cap (identical to the monolithic tree's cap).
    #[inline]
    pub fn get_cap(&self) -> MerkleTreeCapVarLength {
        self.top_tree.get_cap()
    }

    /// Per-column values on the MAIN evaluation domain (LDE coset 0, offset 1) — the
    /// only coset `whir_fold` reads for the batched-polynomial computation. This is
    /// the memory the base oracle must still hold during folding (~num_cols * 2^N).
    pub fn main_domain_columns(
        &self,
        twiddles: &Twiddles<Proth120, Global>,
        worker: &Worker,
    ) -> Vec<Box<[Proth120]>> {
        coset_columns(&self.monomial_forms, twiddles, self.lde_factor, 0, worker)
    }

    /// Commit a batch of columns given on the boolean hypercube (same inputs as
    /// `commit_trace_part`: `input_on_hypercube[col]` is a message-sized column).
    pub fn commit(
        input_on_hypercube: &[&[Proth120]],
        twiddles: &Twiddles<Proth120, Global>,
        lde_factor: usize,
        whir_first_fold_step_log2: usize,
        cap_size: usize,
        trace_len_log2: usize,
        worker: &Worker,
    ) -> Self {
        assert!(!input_on_hypercube.is_empty());
        assert!(lde_factor.is_power_of_two());
        assert!(cap_size.is_power_of_two());
        // The cap must sit at or above the per-coset subtree roots so it can be built
        // from them (cap 8, lde_factor 32 in production). If cap_size > lde_factor the
        // cap would live *inside* the cosets and this split no longer applies.
        assert!(
            cap_size <= lde_factor,
            "coset-by-coset commitment requires cap_size ({cap_size}) <= lde_factor ({lde_factor})"
        );
        let values_per_leaf = 1usize << whir_first_fold_step_log2;

        // hypercube evals -> multilinear monomial coefficients (per column, in
        // parallel), same transform the monolithic path applies before the RS
        // encoding.
        let monomial_forms: Vec<Vec<Proth120>> =
            parallel_collect(worker, input_on_hypercube.len(), |i| {
                let col = input_on_hypercube[i];
                assert_eq!(col.len(), 1usize << trace_len_log2);
                let mut v = col.to_vec();
                bitreverse_enumeration_inplace(&mut v);
                multivariate_hypercube_evals_into_coeffs(&mut v, trace_len_log2 as u32);
                v
            });

        // Per natural-order coset: root of that coset's leaf subtree. Cosets are
        // processed sequentially so peak memory stays ~one coset; the work inside a
        // coset (per-column LDE, leaf hashing, subtree) is what runs in parallel.
        // For production-sized commits (big cosets) log per-coset progress.
        let verbose = trace_len_log2 >= 20;
        let t0 = std::time::Instant::now();
        let mut natural_roots: Vec<Digest32> = Vec::with_capacity(lde_factor);
        for coset_index in 0..lde_factor {
            let root = coset_subtree_root(
                &monomial_forms,
                twiddles,
                lde_factor,
                values_per_leaf,
                coset_index,
                worker,
            );
            natural_roots.push(root);
            if verbose {
                println!(
                    "[coset-commit +{:6.1}s] coset {}/{} done ({} cols of 2^{})",
                    t0.elapsed().as_secs_f64(),
                    coset_index + 1,
                    lde_factor,
                    monomial_forms.len(),
                    trace_len_log2,
                );
            }
        }

        // Physical tree slot `k` sources from coset `bitreverse(k)` (the tree is
        // built with bit-reversed coset order), so reorder the roots accordingly.
        let cosets_log2 = lde_factor.trailing_zeros();
        let physical_roots: Vec<Digest32> = (0..lde_factor)
            .map(|k| natural_roots[bitreverse_index(k, cosets_log2)])
            .collect();

        // Top tree over the per-coset roots -> the commitment cap.
        let top_tree = Tree::continue_from_leaf_hashes(physical_roots, cap_size, worker);

        Self {
            monomial_forms,
            trace_len_log2,
            lde_factor,
            values_per_leaf,
            cap_size,
            top_tree,
        }
    }

    /// Produce the query for a WHIR folded-domain `query_index` (in `[0, tree_size)`):
    /// leaf values (offset-major, matching `query_for_folded_index`) and the full
    /// Merkle path = within-coset path ++ top-tree path.
    pub fn query(
        &self,
        query_index: usize,
        twiddles: &Twiddles<Proth120, Global>,
        worker: &Worker,
    ) -> BaseFieldQuery<Proth120, Tree> {
        self.query_many(&[query_index], twiddles, worker)
            .pop()
            .unwrap()
    }

    /// Like [`query`](Self::query) but also returns the leaf values reshaped into
    /// offset-major `[offset][column]` form (matching `query_for_folded_index`), as
    /// needed by `whir_fold`'s base-layer batching hook.
    pub fn query_structured(
        &self,
        query_index: usize,
        twiddles: &Twiddles<Proth120, Global>,
        worker: &Worker,
    ) -> (Vec<Vec<Proth120>>, BaseFieldQuery<Proth120, Tree>) {
        let q = self.query(query_index, twiddles, worker);
        let num_cols = self.monomial_forms.len();
        let leaf: Vec<Vec<Proth120>> = (0..self.values_per_leaf)
            .map(|o| q.leaf_values_concatenated[o * num_cols..(o + 1) * num_cols].to_vec())
            .collect();
        (leaf, q)
    }

    /// Produce queries for many folded-domain indices, recomputing each distinct
    /// coset only once (a coset's LDE is 2^trace_len_log2 per column, so recomputing
    /// it per query would be wasteful). Returned queries are in input order.
    pub fn query_many(
        &self,
        query_indices: &[usize],
        twiddles: &Twiddles<Proth120, Global>,
        worker: &Worker,
    ) -> Vec<BaseFieldQuery<Proth120, Tree>> {
        let num_cosets = self.lde_factor;
        let cosets_log2 = num_cosets.trailing_zeros();
        let coset_tree_size = self.coset_tree_size();
        let offsets =
            offsets_vec_for_leaf_construction(1usize << self.trace_len_log2, self.values_per_leaf);

        // Group input positions by natural coset index.
        let mut by_coset: std::collections::BTreeMap<usize, Vec<usize>> =
            std::collections::BTreeMap::new();
        for (pos, &qi) in query_indices.iter().enumerate() {
            by_coset.entry(qi & (num_cosets - 1)).or_default().push(pos);
        }

        let mut out: Vec<Option<BaseFieldQuery<Proth120, Tree>>> =
            (0..query_indices.len()).map(|_| None).collect();

        for (coset_index, positions) in by_coset.into_iter() {
            // Recompute this coset once: LDE evaluations (parallel across columns),
            // leaf hashes, subtree.
            let coset_columns = coset_columns(
                &self.monomial_forms,
                twiddles,
                self.lde_factor,
                coset_index,
                worker,
            );

            let col_refs: Vec<&[Proth120]> = coset_columns.iter().map(|c| &c[..]).collect();
            let coset_refs: &[&[Proth120]] = &col_refs[..];
            let trace: &[&[&[Proth120]]] = std::slice::from_ref(&coset_refs);
            let leaf_hashes = keccak256_leaf_hashes_from_cosets::<Proth120, Global, Global>(
                trace,
                self.values_per_leaf,
                true,
                false,
                false,
                worker,
            );
            let subtree = Tree::continue_from_leaf_hashes(leaf_hashes, 1, worker);

            let physical_slot = bitreverse_index(coset_index, cosets_log2);
            let (_root, top_path) = self.top_tree.get_proof::<Global>(physical_slot);

            for pos in positions {
                let internal_index = query_indices[pos] >> cosets_log2;
                assert!(internal_index < coset_tree_size);
                let tree_index = physical_slot * coset_tree_size + internal_index;

                // Leaf values in offset-major order (result[offset][column]), exactly
                // like `ColumnMajorBaseOracleForCoset::values_for_folded_index`.
                let mut leaf_values_concatenated: Vec<Proth120> =
                    Vec::with_capacity(self.values_per_leaf * coset_columns.len());
                for off in offsets.iter() {
                    for col in coset_columns.iter() {
                        leaf_values_concatenated.push(col[*off + internal_index]);
                    }
                }

                let (_leaf_hash, mut path) = subtree.get_proof::<Global>(internal_index);
                path.extend_from_slice(&top_path);

                out[pos] = Some(BaseFieldQuery {
                    index: tree_index,
                    leaf_values_concatenated,
                    path,
                    _marker: core::marker::PhantomData,
                });
            }
        }

        out.into_iter().map(|q| q.unwrap()).collect()
    }
}

/// Compute one coset's leaf hashes and build its subtree, returning only the root.
fn coset_subtree_root(
    monomial_forms: &[Vec<Proth120>],
    twiddles: &Twiddles<Proth120, Global>,
    lde_factor: usize,
    values_per_leaf: usize,
    coset_index: usize,
    worker: &Worker,
) -> Digest32 {
    let coset_columns = coset_columns(monomial_forms, twiddles, lde_factor, coset_index, worker);

    let col_refs: Vec<&[Proth120]> = coset_columns.iter().map(|c| &c[..]).collect();
    let coset_refs: &[&[Proth120]] = &col_refs[..];
    let trace: &[&[&[Proth120]]] = std::slice::from_ref(&coset_refs);

    let leaf_hashes = keccak256_leaf_hashes_from_cosets::<Proth120, Global, Global>(
        trace,
        values_per_leaf,
        true,
        false,
        false,
        worker,
    );
    let subtree =
        Keccak256MerkleTreeWithCap::<Global>::continue_from_leaf_hashes(leaf_hashes, 1, worker);
    subtree.get_cap().cap[0]
}

// ============================================================================
// Coset-by-coset commitment for a SINGLE extension-field oracle (the WHIR
// intermediate/folded RS oracles). Analogous to `CosetByCosetBaseCommitment` but:
//   * one column, given already in monomial form (the folded polynomial),
//   * DEFAULT: each leaf is converted to multilinear-coefficient form (as the
//     monolithic `commit_single_ext_poly` does). Under the `eval_leaves` feature the
//     raw evaluations are committed instead (mirroring the `eval_leaves` monolithic
//     path; the EVM verifier folds those with `fold_coset`, see whir.sol EVAL_LEAVES),
//   * generic over the tree `T` (uses `construct_from_cosets` for per-coset
//     subtrees and `build_over_leaf_hashes` for the top tree).
// ============================================================================

/// Coset-independent factors hoisted out of the per-coset loop in `commit`: the LDE
/// coset offsets, and (default) the coeff-conversion context whose `num_leaves`-long
/// power table would otherwise be rebuilt for every coset.
struct ExtCommonCtx<F: PrimeField + TwoAdicField> {
    root_powers: Vec<F>,
    values_per_leaf: usize,
    #[cfg(not(feature = "eval_leaves"))]
    conv: super::ExtCoeffConvCtx<F>,
}

impl<F: PrimeField + TwoAdicField> ExtCommonCtx<F> {
    fn new(trace_len: usize, lde_factor: usize, values_per_leaf: usize) -> Self {
        let next_root = domain_generator_for_size::<F>((trace_len * lde_factor) as u64);
        let root_powers =
            materialize_powers_serial_starting_with_one::<F, Global>(next_root, lde_factor);
        Self {
            root_powers,
            values_per_leaf,
            #[cfg(not(feature = "eval_leaves"))]
            conv: super::ExtCoeffConvCtx::new(trace_len, values_per_leaf),
        }
    }
}

/// One coset's leaf column: LDE of the monomial form at `root_powers[coset_index]`,
/// then (default) rewritten to coeff form. Under `eval_leaves` the raw evals stand.
fn ext_coset_column<F, E>(
    monomial_form: &[E],
    twiddles: &Twiddles<F, Global>,
    ctx: &ExtCommonCtx<F>,
    coset_index: usize,
    worker: &Worker,
) -> Box<[E]>
where
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
{
    let offset = ctx.root_powers[coset_index];
    #[allow(unused_mut)]
    let mut column =
        compute_column_major_lde_single_coset_with_offset(monomial_form, twiddles, offset, worker);
    #[cfg(not(feature = "eval_leaves"))]
    ctx.conv.apply(&mut column, offset, worker);
    column
}

/// Fully-serial (no worker) variant of [`ext_coset_column`], for computing many
/// small cosets concurrently (one per worker thread).
fn ext_coset_column_serial<F, E>(
    monomial_form: &[E],
    twiddles: &Twiddles<F, Global>,
    ctx: &ExtCommonCtx<F>,
    coset_index: usize,
) -> Box<[E]>
where
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
{
    let offset = ctx.root_powers[coset_index];
    #[allow(unused_mut)]
    let mut column =
        compute_column_major_lde_single_coset_with_offset_serial(monomial_form, twiddles, offset);
    #[cfg(not(feature = "eval_leaves"))]
    ctx.conv.apply_serial(&mut column, offset);
    column
}

/// Compute the `group_size` LDE cosets that occupy top-tree physical slots
/// `[group_index*group_size, +group_size)` and return the root of ONE shared
/// subtree over them (cap size 1). The G cosets are laid out in physical order,
/// so this root equals the corresponding ancestor node of the monolithic tree.
///
/// When `group_size == 1` this is the original single-coset path (the coset's own
/// subtree root), computed with the worker-parallel LDE. When `group_size > 1`
/// (chosen only when each coset's FFT is below the parallel threshold) the G coset
/// columns are computed CONCURRENTLY — one per worker thread, each internally
/// serial — and share a single subtree build.
fn ext_group_subtree_root<F, E, T>(
    monomial_form: &[E],
    twiddles: &Twiddles<F, Global>,
    ctx: &ExtCommonCtx<F>,
    group_index: usize,
    group_log2: u32,
    cosets_log2: u32,
    worker: &Worker,
) -> [u32; DIGEST_SIZE_U32_WORDS]
where
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
    [(); E::DEGREE]: Sized,
{
    let group_size = 1usize << group_log2;
    // Natural coset for physical slot `group_index*group_size + j`.
    let nat = |j: usize| bitreverse_index((group_index << group_log2) + j, cosets_log2);

    let columns: Vec<Box<[E]>> = if group_size == 1 {
        vec![ext_coset_column::<F, E>(monomial_form, twiddles, ctx, nat(0), worker)]
    } else {
        parallel_collect(worker, group_size, |j| {
            ext_coset_column_serial::<F, E>(monomial_form, twiddles, ctx, nat(j))
        })
    };

    ext_group_root_from_columns::<F, E, T>(&columns, ctx.values_per_leaf, worker)
}

/// Build the shared subtree (cap 1) over `columns` (one extension column per coset,
/// in physical order) and return its single root node.
fn ext_group_root_from_columns<F, E, T>(
    columns: &[Box<[E]>],
    values_per_leaf: usize,
    worker: &Worker,
) -> [u32; DIGEST_SIZE_U32_WORDS]
where
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
    [(); E::DEGREE]: Sized,
{
    // trace shape is [coset][column][values]; one column per coset here.
    let per_coset: Vec<[&[E]; 1]> = columns.iter().map(|c| [&c[..]]).collect();
    let coset_slices: Vec<&[&[E]]> = per_coset.iter().map(|a| &a[..]).collect();
    let trace: &[&[&[E]]] = &coset_slices;
    let subtree =
        T::construct_from_cosets::<E, Global>(trace, values_per_leaf, 1, true, false, false, worker);
    subtree.get_cap().cap[0]
}

/// Choose the coset grouping (log2). Returns 0 (no grouping, per-coset roots)
/// unless each coset's FFT is below the parallel-NTT serial cutoff — in which case
/// grouping lets several cosets run concurrently. Group size is `floor_pow2(cores)`,
/// capped so the top tree keeps `>= cap_size` leaves (`num_groups >= cap_size`).
fn grouping_log2<E: Field>(
    trace_len: usize,
    cosets_log2: u32,
    cap_size: usize,
    worker: &Worker,
) -> u32 {
    // Mirrors `parallel_ct_ntt_bitreversed_to_natural`'s serial fallback cutoff.
    const NTT_PAR_THRESHOLD: usize = 1 << 12;
    let words = (core::mem::size_of::<E>() / core::mem::size_of::<u32>()).max(1);
    let eff_threshold = NTT_PAR_THRESHOLD / words;
    if trace_len >= eff_threshold {
        return 0; // per-coset FFT is already worker-parallel; grouping would not help.
    }
    let threads_log2 = worker.get_num_cores().max(1).ilog2();
    // num_groups = 2^(cosets_log2 - group_log2) must stay >= cap_size = 2^cap_log2.
    let max_group_log2 = cosets_log2.saturating_sub(cap_size.trailing_zeros());
    threads_log2.min(max_group_log2)
}

/// Coset-by-coset commitment of a single extension-field poly (given in monomial
/// form). Keeps only the monomial form + top tree; recomputes cosets on query.
#[derive(Debug)]
pub struct CosetByCosetExtCommitment<F, E, T>
where
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
{
    pub monomial_form: Vec<E>,
    pub trace_len_log2: usize,
    pub lde_factor: usize,
    pub values_per_leaf: usize,
    /// log2 of the coset grouping: each top-tree leaf is a shared subtree over
    /// `2^group_log2` physically-adjacent cosets (0 = one coset per top leaf, the
    /// original layout). > 0 only when the per-coset FFT runs serially.
    pub group_log2: u32,
    pub top_tree: T,
    _marker: PhantomData<F>,
}

impl<F, E, T> CosetByCosetExtCommitment<F, E, T>
where
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
    [(); E::DEGREE]: Sized,
{
    #[inline]
    pub fn get_cap(&self) -> MerkleTreeCapVarLength {
        self.top_tree.get_cap()
    }

    pub fn commit(
        monomial_form: &[E],
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        values_per_leaf: usize,
        cap_size: usize,
        worker: &Worker,
    ) -> Self {
        assert!(lde_factor.is_power_of_two());
        assert!(cap_size <= lde_factor, "cap_size must be <= lde_factor");
        assert!(cap_size.is_power_of_two());
        let trace_len_log2 = monomial_form.len().trailing_zeros() as usize;
        let trace_len = 1usize << trace_len_log2;
        let cosets_log2 = lde_factor.trailing_zeros();

        // Coset grouping: when each coset's FFT is below the parallel-NTT threshold it
        // runs serially, leaving the worker's threads idle. In that regime, process
        // `2^group_log2` cosets CONCURRENTLY (one serial FFT per thread) and build one
        // shared subtree per group. `group_log2 = 0` reproduces the original layout.
        let group_log2 = grouping_log2::<E>(trace_len, cosets_log2, cap_size, worker);
        let group_size = 1usize << group_log2;
        let num_groups = lde_factor >> group_log2;

        let step = if trace_len_log2 >= 20 {
            1
        } else {
            (num_groups.max(1) * group_size * trace_len) >> 20
        }
        .max(1);
        let t0 = std::time::Instant::now();
        // Hoist coset-independent factors (root_powers + coeff-conversion table).
        let ctx = ExtCommonCtx::<F>::new(trace_len, lde_factor, values_per_leaf);
        // Physical top-tree leaf `g` = root of the shared subtree over physical coset
        // slots `[g*group_size, +group_size)`. (group_size == 1 -> per-coset roots.)
        let mut physical_roots: Vec<[u32; DIGEST_SIZE_U32_WORDS]> = Vec::with_capacity(num_groups);
        for group_index in 0..num_groups {
            physical_roots.push(ext_group_subtree_root::<F, E, T>(
                monomial_form,
                twiddles,
                &ctx,
                group_index,
                group_log2,
                cosets_log2,
                worker,
            ));
            if (group_index + 1) % step == 0 {
                println!(
                    "[ext-coset-commit +{:6.1}s] group {}/{} done ({} cosets/group, 1 col of 2^{})",
                    t0.elapsed().as_secs_f64(),
                    group_index + 1,
                    num_groups,
                    group_size,
                    trace_len_log2,
                );
            }
        }
        let top_tree = T::build_over_leaf_hashes(physical_roots, cap_size, worker);

        Self {
            monomial_form: monomial_form.to_vec(),
            trace_len_log2,
            lde_factor,
            values_per_leaf,
            group_log2,
            top_tree,
            _marker: PhantomData,
        }
    }

    /// Same shape as `ColumnMajorExtensionOracleForLDE::query_for_folded_index`:
    /// `(coset_index, leaf coeff values, ExtensionFieldQuery)`.
    pub fn query(
        &self,
        query_index: usize,
        twiddles: &Twiddles<F, Global>,
        worker: &Worker,
    ) -> (usize, Vec<E>, ExtensionFieldQuery<F, E, T>) {
        let num_cosets = self.lde_factor;
        let cosets_log2 = num_cosets.trailing_zeros();
        let coset_tree_size = (1usize << self.trace_len_log2) / self.values_per_leaf;
        let coset_index = query_index & (num_cosets - 1);
        let internal_index = query_index >> cosets_log2;
        assert!(internal_index < coset_tree_size);
        let physical_slot = bitreverse_index(coset_index, cosets_log2);
        let tree_index = physical_slot * coset_tree_size + internal_index;

        // The query's coset lives at position `slot_in_group` inside top-tree leaf
        // `group_index`'s shared subtree. Recompute that whole group (grouping only
        // activates for small cosets, so this is a handful of tiny FFTs), then read the
        // leaf->group-root path from the group subtree and stitch the top-tree path.
        let group_log2 = self.group_log2;
        let group_size = 1usize << group_log2;
        let group_index = physical_slot >> group_log2;
        let slot_in_group = physical_slot & (group_size - 1);

        let ctx =
            ExtCommonCtx::<F>::new(1usize << self.trace_len_log2, num_cosets, self.values_per_leaf);
        let columns: Vec<Box<[E]>> = if group_size == 1 {
            vec![ext_coset_column::<F, E>(
                &self.monomial_form,
                twiddles,
                &ctx,
                coset_index,
                worker,
            )]
        } else {
            parallel_collect(worker, group_size, |j| {
                let nat = bitreverse_index((group_index << group_log2) + j, cosets_log2);
                ext_coset_column_serial::<F, E>(&self.monomial_form, twiddles, &ctx, nat)
            })
        };

        let my_column = &columns[slot_in_group];
        let offsets =
            offsets_vec_for_leaf_construction(1usize << self.trace_len_log2, self.values_per_leaf);
        let values: Vec<E> = offsets
            .iter()
            .map(|&off| my_column[off + internal_index])
            .collect();

        // shared subtree over the group -> path from this leaf up to the group root.
        let per_coset: Vec<[&[E]; 1]> = columns.iter().map(|c| [&c[..]]).collect();
        let coset_slices: Vec<&[&[E]]> = per_coset.iter().map(|a| &a[..]).collect();
        let trace: &[&[&[E]]] = &coset_slices;
        let subtree = T::construct_from_cosets::<E, Global>(
            trace,
            self.values_per_leaf,
            1,
            true,
            false,
            false,
            worker,
        );
        let group_leaf_index = slot_in_group * coset_tree_size + internal_index;
        let (_leaf, mut path) = subtree.get_proof::<Global>(group_leaf_index);

        // top-tree path (group root -> cap)
        let (_root, top_path) = self.top_tree.get_proof::<Global>(group_index);
        path.extend_from_slice(&top_path);

        let query = ExtensionFieldQuery {
            index: tree_index,
            leaf_values_concatenated: values.clone(),
            path,
            _marker: PhantomData,
        };
        (coset_index, values, query)
    }
}

#[cfg(all(test, feature = "prover"))]
mod test {
    use super::*;
    use crate::gkr::prover::stages::stage1::commit_trace_part;
    use crate::gkr::whir::ColumnMajorBaseOracleForLDE;
    use field::PrimeField;
    use rand::{Rng, SeedableRng};

    fn rand_proth<R: Rng>(rng: &mut R) -> Proth120 {
        let lo: u64 = rng.random();
        let hi: u64 = rng.random();
        Proth120::new((((hi as u128) << 64) | lo as u128) % Proth120::ORDER)
    }

    /// The coset-by-coset commitment must produce the exact same cap and, for each
    /// checked folded-domain index, the exact same tree index / leaf values / Merkle
    /// path as the monolithic `commit_trace_part` + `query_for_folded_index`. When
    /// `indices` is `None`, every index is checked; otherwise only the given sample
    /// (used for large sizes where checking all would be too slow).
    fn check(
        num_columns: usize,
        trace_len_log2: usize,
        lde_log2: usize,
        first_fold_log2: usize,
        cap_size: usize,
        indices: Option<&[usize]>,
    ) {
        let worker = Worker::new_with_num_threads(4);
        let trace_len = 1usize << trace_len_log2;
        let lde_factor = 1usize << lde_log2;
        let mut rng = rand::rngs::StdRng::seed_from_u64(0xC0DE_C0DE);

        let cols: Vec<Vec<Proth120>> = (0..num_columns)
            .map(|_| (0..trace_len).map(|_| rand_proth(&mut rng)).collect())
            .collect();
        let col_refs: Vec<&[Proth120]> = cols.iter().map(|c| &c[..]).collect();

        let twiddles = Twiddles::<Proth120, Global>::new(trace_len, &worker);

        let mono: ColumnMajorBaseOracleForLDE<Proth120, Tree> = commit_trace_part(
            &col_refs,
            &twiddles,
            lde_factor,
            first_fold_log2,
            cap_size,
            trace_len_log2,
            &worker,
        );
        let coset = CosetByCosetBaseCommitment::commit(
            &col_refs,
            &twiddles,
            lde_factor,
            first_fold_log2,
            cap_size,
            trace_len_log2,
            &worker,
        );

        assert_eq!(mono.tree.get_cap(), coset.get_cap(), "cap mismatch");

        let vpl = 1usize << first_fold_log2;
        let tree_size = lde_factor * (trace_len / vpl);
        let all: Vec<usize> = (0..tree_size).collect();
        let sample: &[usize] = indices.unwrap_or(&all);

        // exercise the batched path too (dedups by coset)
        let got_batch = coset.query_many(sample, &twiddles, &worker);
        for (pos, &qi) in sample.iter().enumerate() {
            let (_c, _v, expected) = mono.query_for_folded_index(qi);
            let got = &got_batch[pos];
            assert_eq!(got.index, expected.index, "tree_index @ q={qi}");
            assert_eq!(
                got.leaf_values_concatenated, expected.leaf_values_concatenated,
                "leaf values @ q={qi}"
            );
            assert_eq!(got.path, expected.path, "merkle path @ q={qi}");
        }
    }

    #[test]
    fn matches_monolithic_8col_lde8_fold1() {
        check(8, 6, 3, 1, 2, None);
    }

    #[test]
    fn matches_monolithic_1col_lde4_fold1() {
        // setup-oracle shape (1 column), and identity coset bit-reversal edge.
        check(1, 7, 2, 1, 4, None);
    }

    #[test]
    fn matches_monolithic_test_schedule() {
        // Same shape as the working EVM fixture: message 2^8, LDE 32, 8 cols.
        check(8, 8, 5, 1, 8, None);
    }

    #[test]
    fn matches_monolithic_large_parallel_ntt() {
        // message 2^14 (> the NTT parallel threshold 2^12) so `commit`/`query` run the
        // worker-parallel LDE, distribute_powers and bit-reversal. LDE 16 cosets, cap 8
        // (cap_size <= lde_factor). tree_size = 16 * 2^13 = 2^17. Sample of indices.
        let sample = [
            0usize, 1, 3, 255, 1024, 65535, 65536, 99999, 131071, 100000, 42,
        ];
        check(8, 14, 4, 1, 8, Some(&sample));
    }

    /// VARIANT-4 uses round-0 fold 2 => 4 values per leaf. The monolithic base
    /// `query_for_folded_index` only supports vp==2, so instead validate the cap and,
    /// per query, the Merkle path against the monolithic tree plus the leaf hash
    /// (proving the recomputed leaf VALUES are correct).
    #[test]
    fn matches_monolithic_vp4() {
        use sha3::{Digest, Keccak256};
        let worker = Worker::new_with_num_threads(4);
        let (num_columns, trace_len_log2, lde_log2, first_fold_log2, cap_size) = (8, 8, 5, 2, 8);
        let trace_len = 1usize << trace_len_log2;
        let lde_factor = 1usize << lde_log2;
        let vpl = 1usize << first_fold_log2;
        let mut rng = rand::rngs::StdRng::seed_from_u64(0xABCD_1234);

        let cols: Vec<Vec<Proth120>> = (0..num_columns)
            .map(|_| (0..trace_len).map(|_| rand_proth(&mut rng)).collect())
            .collect();
        let col_refs: Vec<&[Proth120]> = cols.iter().map(|c| &c[..]).collect();
        let twiddles = Twiddles::<Proth120, Global>::new(trace_len, &worker);

        let mono: crate::gkr::whir::ColumnMajorBaseOracleForLDE<Proth120, Tree> =
            crate::gkr::prover::stages::stage1::commit_trace_part(
                &col_refs,
                &twiddles,
                lde_factor,
                first_fold_log2,
                cap_size,
                trace_len_log2,
                &worker,
            );
        let coset = CosetByCosetBaseCommitment::commit(
            &col_refs,
            &twiddles,
            lde_factor,
            first_fold_log2,
            cap_size,
            trace_len_log2,
            &worker,
        );
        assert_eq!(mono.tree.get_cap(), coset.get_cap(), "cap mismatch");

        // leaf hash = keccak256 of the column-major BE16 values (as the tree hashes).
        let leaf_hash = |vals: &[Proth120]| -> [u32; 8] {
            let mut pre = Vec::new();
            for c in 0..num_columns {
                for o in 0..vpl {
                    pre.extend_from_slice(&vals[o * num_columns + c].to_u128().to_be_bytes());
                }
            }
            let mut out = [0u8; 32];
            out.copy_from_slice(Keccak256::digest(&pre).as_slice());
            core::array::from_fn(|i| {
                u32::from_be_bytes([out[4 * i], out[4 * i + 1], out[4 * i + 2], out[4 * i + 3]])
            })
        };

        let tree_size = lde_factor * (trace_len / vpl);
        for qi in 0..tree_size {
            let q = coset.query(qi, &twiddles, &worker);
            let (leaf_h, expected_path) = mono.tree.get_proof::<Global>(q.index);
            assert_eq!(q.path, expected_path, "path @ q={qi}");
            assert_eq!(
                leaf_hash(&q.leaf_values_concatenated),
                leaf_h,
                "leaf hash @ q={qi}"
            );
        }
    }

    /// Coset grouping (computing several small cosets in parallel under one shared
    /// subtree) is a pure implementation detail: the commitment/queries must be
    /// byte-identical regardless of the worker's thread count. Uses a small trace
    /// (2^7 < the NTT parallel threshold) so grouping activates when cores allow.
    #[test]
    fn ext_grouping_matches_across_thread_counts() {
        let (tl, ld, vp, cap) = (7usize, 4usize, 1usize, 2usize);
        let trace_len = 1usize << tl;
        let lde_factor = 1usize << ld;
        let vpl = 1usize << vp;
        let mut rng = rand::rngs::StdRng::seed_from_u64(0x9A9A_5C5C);
        let monomial: Vec<Proth120> = (0..trace_len).map(|_| rand_proth(&mut rng)).collect();

        // reference: single thread => no grouping (group_log2 == 0, original layout).
        let w1 = Worker::new_with_num_threads(1);
        let tw1 = Twiddles::<Proth120, Global>::new(trace_len, &w1);
        let reference = CosetByCosetExtCommitment::<Proth120, Proth120, Tree>::commit(
            &monomial, &tw1, lde_factor, vpl, cap, &w1,
        );
        assert_eq!(reference.group_log2, 0, "single thread should not group");

        let tree_size = lde_factor * (trace_len / vpl);
        for nthreads in [2usize, 4, 8] {
            let w = Worker::new_with_num_threads(nthreads);
            let tw = Twiddles::<Proth120, Global>::new(trace_len, &w);
            let grouped = CosetByCosetExtCommitment::<Proth120, Proth120, Tree>::commit(
                &monomial, &tw, lde_factor, vpl, cap, &w,
            );
            assert!(
                grouped.group_log2 >= 1,
                "grouping should activate with {nthreads} threads"
            );
            assert_eq!(reference.get_cap(), grouped.get_cap(), "cap @ {nthreads} threads");
            for qi in 0..tree_size {
                let (_rc, rv, rq) = reference.query(qi, &tw1, &w1);
                let (_gc, gv, gq) = grouped.query(qi, &tw, &w);
                assert_eq!(rv, gv, "values @ q={qi} nthreads={nthreads}");
                assert_eq!(rq.index, gq.index, "index @ q={qi} nthreads={nthreads}");
                assert_eq!(rq.path, gq.path, "path @ q={qi} nthreads={nthreads}");
            }
        }
    }

    /// The coset-by-coset EXTENSION commitment must match the monolithic
    /// `commit_single_ext_poly` + `query_for_folded_index` exactly (cap, coset index,
    /// coeff-form leaf values, tree index, Merkle path).
    #[test]
    fn ext_matches_monolithic() {
        use crate::gkr::prover::stages::stage1::compute_column_major_lde_from_monomial_form;
        let worker = Worker::new_with_num_threads(4);
        // (trace_len_log2, lde_log2, vpl_log2, cap_size)
        for (tl, ld, vp, cap) in [(6usize, 3usize, 1usize, 2usize), (8, 4, 2, 8), (8, 5, 2, 8)] {
            let trace_len = 1usize << tl;
            let lde_factor = 1usize << ld;
            let vpl = 1usize << vp;
            let mut rng = rand::rngs::StdRng::seed_from_u64(0xE47_0000 + tl as u64);
            let monomial: Vec<Proth120> = (0..trace_len).map(|_| rand_proth(&mut rng)).collect();
            let twiddles = Twiddles::<Proth120, Global>::new(trace_len, &worker);

            let rs = compute_column_major_lde_from_monomial_form(
                &monomial,
                &twiddles,
                lde_factor,
                Some(&worker),
            );
            let mono = super::super::commit_single_ext_poly::<Proth120, Proth120, Tree>(
                rs, vpl, cap, &worker,
            );
            let coset = CosetByCosetExtCommitment::<Proth120, Proth120, Tree>::commit(
                &monomial, &twiddles, lde_factor, vpl, cap, &worker,
            );
            assert_eq!(
                mono.tree.get_cap(),
                coset.get_cap(),
                "ext cap mismatch (tl={tl})"
            );

            let tree_size = lde_factor * (trace_len / vpl);
            for qi in 0..tree_size {
                let (mci, mvals, mq) = mono.query_for_folded_index(qi);
                let (cci, cvals, cq) = coset.query(qi, &twiddles, &worker);
                assert_eq!(mci, cci, "coset_index @ q={qi}");
                assert_eq!(mvals, cvals, "coeff values @ q={qi}");
                assert_eq!(mq.index, cq.index, "tree_index @ q={qi}");
                assert_eq!(
                    mq.leaf_values_concatenated, cq.leaf_values_concatenated,
                    "leaf @ q={qi}"
                );
                assert_eq!(mq.path, cq.path, "path @ q={qi}");
            }
        }
    }
}
