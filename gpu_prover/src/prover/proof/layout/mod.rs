//! Device-resident proof image — single `u8` slab layout.
//!
//! See `docs/gpu_scheduling_contract.md`. Every proof field produced on device
//! lands in one contiguous device allocation (the proof slab); one terminal
//! D2H copies the slab to pinned host memory; a single host parse over the
//! slab emits the final `GKRProof`.
//!
//! ## Layout policy
//!
//! Each field range starts at an offset rounded up to `FIELD_ALIGN` (16). This
//! is a superset of the alignment of every proof element type we store (`E4`,
//! `BF`, `u32`, `u64`, digest words), so casting the raw pointer + the field's
//! `Range::start` as a typed `*mut T` is always well-aligned. The cost is a
//! handful of padding bytes per field; the benefit is that the layout math is
//! trivially correct and reviewable in one place.
//!
//! ## Host alignment invariant
//!
//! The host-side proof slab is allocated from the stream-ordered host pool,
//! whose block size is configured by `ProverContextConfig::host_allocator_block_log_size`.
//! `ProverContext::new` asserts `host_allocator_block_log_size >= 4` (16-byte
//! blocks) so block addresses meet the `FIELD_ALIGN` requirement above.

use std::collections::BTreeMap;
use std::mem::size_of;
use std::ops::Range;

use std::collections::BTreeSet;

use crate::primitives::field::{BF, E4};
use crate::prover::gkr::stage1::GpuGKRTraceGeometry;
use crate::upstream::{
    DefaultTreeConstructor, ExtensionFieldQuery, GKRAddress, GKRCircuitArtifact,
    MerkleTreeCapVarLength, OutputType, SumcheckIntermediateProofValues,
    WhirBaseLayerCommitmentAndQueries, WhirCommitment, WhirIntermediateCommitmentAndQueries,
    WhirPolyCommitProof, WhirSchedule,
};

/// Slab field-start alignment, in bytes. See module-level doc.
pub(crate) const FIELD_ALIGN: usize = 16;

/// Number of `u32` words per Merkle digest (Blake2s cap entry size).
pub(crate) const DIGEST_U32_WORDS: usize = 8;

#[inline]
fn align_up(offset: usize, align: usize) -> usize {
    debug_assert!(align.is_power_of_two());
    (offset + align - 1) & !(align - 1)
}

/// Per-backward-layer shape.
#[derive(Debug, Clone)]
pub(crate) struct BackwardLayerDims {
    pub(crate) layer_idx: usize,
    /// Total sumcheck rounds for this layer; `internal_round_coefficients` has
    /// length `sumcheck_num_rounds - 1`, each element `[E4; 4]`.
    pub(crate) sumcheck_num_rounds: usize,
    /// Addresses for `final_step_evaluations`, in a stable order. Each entry
    /// contributes `final_step_eval_degree` `E4` values.
    pub(crate) final_step_eval_addresses: Vec<GKRAddress>,
    /// Elements per `final_step_evaluations` entry (typically equal to the
    /// extension-field degree of the reduced output polynomial). Kept per-layer
    /// because it may vary between dim-reducing and main layers.
    pub(crate) final_step_eval_degree: usize,
    /// Addresses for `extra_evaluations_from_caching_relations` — the per-layer
    /// orphan kernel outputs that are not consumed as inputs by any parent-layer
    /// kernel and therefore not part of `final_step_evaluations`. Each entry
    /// contributes a single `E4` (the explicit evaluation at the random folding
    /// point). Empty for dim-reducing slots and for main layers without
    /// orphans. Mirrors the CPU proof's
    /// `SumcheckIntermediateProofValues::extra_evaluations_from_caching_relations`
    /// field.
    pub(crate) extra_evaluations_addresses: Vec<GKRAddress>,
}

/// Per-base-layer (setup/memory/witness) WHIR dimensions.
#[derive(Debug, Clone)]
pub(crate) struct WhirBaseLayerDims {
    /// Number of trace columns (= `evals.len()`).
    pub(crate) num_columns: usize,
    /// Number of digests in the Merkle cap for this base layer.
    pub(crate) cap_digest_count: usize,
    /// Number of queries against this base layer.
    pub(crate) query_count: usize,
    /// `leaf_values_concatenated.len()` per query (= `num_columns *
    /// values_per_leaf`).
    pub(crate) leaf_values_len: usize,
    /// Merkle path length per query, in digests.
    pub(crate) path_len: usize,
}

/// Per-intermediate-WHIR-oracle dimensions.
#[derive(Debug, Clone)]
pub(crate) struct WhirIntermediateDims {
    pub(crate) cap_digest_count: usize,
    pub(crate) query_count: usize,
    /// `leaf_values_concatenated.len()` per query (extension-field values,
    /// = `values_per_leaf`).
    pub(crate) leaf_values_len: usize,
    pub(crate) path_len: usize,
}

/// WHIR-side dimensions for the proof image.
#[derive(Debug, Clone)]
pub(crate) struct WhirDims {
    pub(crate) setup: WhirBaseLayerDims,
    pub(crate) memory: WhirBaseLayerDims,
    pub(crate) witness: WhirBaseLayerDims,
    pub(crate) intermediate: Vec<WhirIntermediateDims>,
    /// Number of `ood_samples` (one per intermediate oracle round).
    pub(crate) num_ood_samples: usize,
    /// Total `sumcheck_polys` entries across all WHIR folding rounds.
    pub(crate) total_sumcheck_polys: usize,
    /// `pow_nonces.len()` — equal to `whir_pow_schedule.len()`.
    pub(crate) pow_rounds: usize,
    /// `final_monomials.len()`. Must be derivable from the WHIR schedule at
    /// `prove()` start — see the iterative-knitting-bumblebee plan.
    pub(crate) final_monomials_len: usize,
}

/// Full proof-image shape. Consumed by `ProofLayout::new`.
#[derive(Debug, Clone)]
pub(crate) struct ProofLayoutInputs {
    /// Per `OutputType`, the lengths of the two `Vec<E4>` entries
    /// (`[read_set_len, write_set_len]`) in
    /// `GKRProof::final_explicit_evaluations`.
    pub(crate) output_evaluations: BTreeMap<OutputType, [usize; 2]>,
    /// Backward layers in layer-index order. Parse rebuilds the
    /// `sumcheck_intermediate_values` `BTreeMap` using `layer_idx`.
    pub(crate) backward_layers: Vec<BackwardLayerDims>,
    pub(crate) whir: WhirDims,
}

// ---------------------------------------------------------------------------
// Per-field layout sub-types
// ---------------------------------------------------------------------------

/// Layout for one entry in `final_explicit_evaluations` (two `Vec<E4>`).
#[derive(Debug, Clone)]
pub(crate) struct OutputEvaluationsLayout {
    pub(crate) read_set: Range<usize>,
    pub(crate) write_set: Range<usize>,
}

/// Layout for one backward layer's sumcheck contribution.
#[derive(Debug, Clone)]
pub(crate) struct BackwardLayerLayout {
    pub(crate) layer_idx: usize,
    /// `internal_round_coefficients` — flat array of `[E4; 4]`,
    /// length `sumcheck_num_rounds - 1`.
    pub(crate) internal_round_coefficients: Range<usize>,
    /// `final_step_evaluations` flat array — `addresses.len() *
    /// final_step_eval_degree` `E4` values, address order matches
    /// `final_step_eval_addresses`.
    pub(crate) final_step_evaluations: Range<usize>,
    /// Copy of the address ordering, retained for parse-time `BTreeMap`
    /// reconstruction.
    pub(crate) final_step_eval_addresses: Vec<GKRAddress>,
    /// `extra_evaluations_from_caching_relations` flat array — one `E4` per
    /// orphan address, in `extra_evaluations_addresses` order. Empty for
    /// dim-reducing slots and main layers without orphans.
    pub(crate) extra_evaluations: Range<usize>,
    /// Copy of the orphan address ordering, retained for parse-time
    /// `BTreeMap` reconstruction.
    pub(crate) extra_evaluations_addresses: Vec<GKRAddress>,
    pub(crate) sumcheck_num_rounds: usize,
    pub(crate) final_step_eval_degree: usize,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub(crate) struct WhirBaseLayerByteLayout {
    pub(crate) num_columns: usize,
    /// `cap` flat bytes — `cap_digest_count * DIGEST_U32_WORDS` `u32`s.
    pub(crate) cap: Range<usize>,
    /// `evals` — `num_columns` `E4` values.
    pub(crate) evals: Range<usize>,
    /// `queries[i].index` — `query_count` `u32` values (narrowed from `usize`;
    /// index < 2^32 is safe for all realistic trace lengths).
    pub(crate) query_indices: Range<usize>,
    /// `queries[i].leaf_values_concatenated` — `query_count * leaf_values_len`
    /// `BF` values, flat.
    pub(crate) query_leaves: Range<usize>,
    /// `queries[i].path` — `query_count * path_len` digest words (each digest
    /// is `DIGEST_U32_WORDS` `u32`), flat.
    pub(crate) query_paths: Range<usize>,
    pub(crate) query_count: usize,
    pub(crate) leaf_values_len: usize,
    pub(crate) path_len: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct WhirIntermediateByteLayout {
    pub(crate) cap: Range<usize>,
    pub(crate) query_indices: Range<usize>,
    /// Flat `E4` values — `query_count * leaf_values_len`.
    pub(crate) query_leaves: Range<usize>,
    pub(crate) query_paths: Range<usize>,
    pub(crate) query_count: usize,
    pub(crate) leaf_values_len: usize,
    pub(crate) path_len: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct WhirLayout {
    pub(crate) setup: WhirBaseLayerByteLayout,
    pub(crate) memory: WhirBaseLayerByteLayout,
    pub(crate) witness: WhirBaseLayerByteLayout,
    pub(crate) intermediate: Vec<WhirIntermediateByteLayout>,
    /// `ood_samples` — `num_ood_samples` `E4` values.
    pub(crate) ood_samples: Range<usize>,
    /// `sumcheck_polys` — flat array of `[E4; 3]`, length `total_sumcheck_polys`.
    pub(crate) sumcheck_polys: Range<usize>,
    /// `pow_nonces` — `pow_rounds` `u64` values.
    pub(crate) pow_nonces: Range<usize>,
    /// `final_monomials` — `final_monomials_len` `E4` values.
    pub(crate) final_monomials: Range<usize>,
}

/// Complete slab byte layout.
#[derive(Debug, Clone)]
pub(crate) struct ProofLayout {
    pub(crate) output_evaluations: BTreeMap<OutputType, OutputEvaluationsLayout>,
    pub(crate) backward: Vec<BackwardLayerLayout>,
    pub(crate) whir: WhirLayout,
    pub(crate) total_bytes: usize,
}

#[cfg(test)]
pub(crate) use tests::placeholder_inputs_for_prove;

mod accessors;
mod build_inputs;
pub(crate) use accessors::WhirBaseLayerKind;
pub(crate) use build_inputs::build_proof_layout_inputs;

/// Trace-holder geometry subset needed to size WHIR base-layer fields in the
/// slab. See [`build_proof_layout_inputs`].
#[derive(Clone, Copy, Debug)]
pub(crate) struct ProofLayoutBaseLayerGeometry {
    pub(crate) columns_count: usize,
    pub(crate) log_domain_size: u32,
    pub(crate) log_lde_factor: u32,
    pub(crate) log_rows_per_leaf: u32,
    pub(crate) log_tree_cap_size: u32,
}

impl ProofLayoutBaseLayerGeometry {
    pub(crate) fn from_geometry(geometry: GpuGKRTraceGeometry, columns_count: usize) -> Self {
        Self {
            columns_count,
            log_domain_size: geometry.log_domain_size,
            log_lde_factor: geometry.log_lde_factor,
            log_rows_per_leaf: geometry.log_rows_per_leaf,
            log_tree_cap_size: geometry.log_tree_cap_size,
        }
    }
}

/// Build [`ProofLayoutInputs`] for one `prove()` invocation. Derives every
/// input from the compiled circuit + WHIR schedule + base-layer geometries —
/// no forward-pass output required. Called by `prove()` to size the proof
/// slab before `schedule_forward_pass` runs.
///
/// Field-by-field sourcing:
///
/// * `backward_layers`: `initial_layer_for_sumcheck` down through main layer 0
///   in scheduler (high-to-low) order. `sumcheck_num_rounds` follows the
///   dim-reducing chain starting at `final_trace_size_log_2` and incrementing
///   by one per dim-reducing layer, then saturates at
///   `initial_trace_size_log_2` for every main layer. `final_step_eval_degree`
///   is 4 for dim-reducing (see backward.rs:5188) and 2 for main
///   (backward.rs:6646). Dim-reducing `final_step_eval_addresses` come from
///   [`crate::prover::gkr::backward::derive_dimension_reducing_inputs`]
///   (address-assignment rules match `schedule_dimension_reduction_forward`).
///   Main-layer `final_step_eval_addresses` come from
///   [`crate::prover::gkr::backward::collect_main_layer_input_addresses_per_layer`]
///   (storage-aware kernel-kind branch is invariant in the collected address set
///   — see that function's doc).
///
/// Note: `extra_evaluations_from_caching_relations` (main layer 0 only) is
/// not a separate slab range. Its values are sparse references into the
/// slab-resident WHIR base eval ranges; Phase 4 reconstructs the map from
/// `base_layer_claims_shared_state` metadata plus the terminal slab mirror.
/// * `whir`: derivation mirrors `whir_fold.rs:1742-1792`. `final_monomials_len`
///   is 0 because the current GPU prover leaves `proof.final_monomials =
///   vec![]` (whir_fold.rs:1870); revisit if that changes.
impl ProofLayout {
    pub(crate) fn new(inputs: &ProofLayoutInputs) -> Self {
        let mut cur = 0usize;

        let alloc = |cur: &mut usize, count: usize, elem_size: usize| -> Range<usize> {
            let start = align_up(*cur, FIELD_ALIGN);
            let end = start + count * elem_size;
            *cur = end;
            start..end
        };

        // output_evaluations are laid out first as a single contiguous E4
        // block in BTreeMap key order × {read, write}. This matches the
        // packing order produced by the forward dim-reduction pass, allowing
        // the final forward outputs to write directly into this slab prefix.
        let mut output_evaluations = BTreeMap::new();
        for (&output_type, &[read_len, write_len]) in inputs.output_evaluations.iter() {
            let read_set = alloc(&mut cur, read_len, size_of::<E4>());
            let write_set = alloc(&mut cur, write_len, size_of::<E4>());
            output_evaluations.insert(
                output_type,
                OutputEvaluationsLayout {
                    read_set,
                    write_set,
                },
            );
        }

        // Backward layers, in the order given.
        let mut backward = Vec::with_capacity(inputs.backward_layers.len());
        for layer in inputs.backward_layers.iter() {
            let internal_count = layer.sumcheck_num_rounds.saturating_sub(1);
            let internal_round_coefficients = alloc(&mut cur, internal_count * 4, size_of::<E4>());
            let final_evals_count =
                layer.final_step_eval_addresses.len() * layer.final_step_eval_degree;
            let final_step_evaluations = alloc(&mut cur, final_evals_count, size_of::<E4>());
            // One `E4` per orphan address — single explicit evaluation at
            // the layer's random folding point. Empty range when there are
            // no orphans (zero-width allocations are fine; the start offset
            // remains aligned).
            let extra_evaluations = alloc(
                &mut cur,
                layer.extra_evaluations_addresses.len(),
                size_of::<E4>(),
            );
            backward.push(BackwardLayerLayout {
                layer_idx: layer.layer_idx,
                internal_round_coefficients,
                final_step_evaluations,
                final_step_eval_addresses: layer.final_step_eval_addresses.clone(),
                extra_evaluations,
                extra_evaluations_addresses: layer.extra_evaluations_addresses.clone(),
                sumcheck_num_rounds: layer.sumcheck_num_rounds,
                final_step_eval_degree: layer.final_step_eval_degree,
            });
        }

        // WHIR base layers + intermediates + flat arrays.
        let whir = Self::lay_whir(&mut cur, &inputs.whir);

        let total_bytes = align_up(cur, FIELD_ALIGN);
        ProofLayout {
            output_evaluations,
            backward,
            whir,
            total_bytes,
        }
    }

    /// Returns the byte range covering the full `output_evaluations` block —
    /// concatenation of every `{read_set, write_set}` in BTreeMap iteration
    /// order. The block is contiguous (every entry's element size equals
    /// `FIELD_ALIGN`) and is the direct-write target for the final forward
    /// dim-reduction outputs in the proof path.
    pub(crate) fn output_evaluations_block(&self) -> Option<Range<usize>> {
        let first = self.output_evaluations.values().next()?;
        let last = self
            .output_evaluations
            .values()
            .next_back()
            .expect("non-empty map has a last entry");
        let start = first.read_set.start;
        let end = last.write_set.end;
        debug_assert_eq!(
            (end - start) % size_of::<E4>(),
            0,
            "output_evaluations block byte span must be a multiple of E4 size",
        );
        Some(start..end)
    }

    fn lay_whir(cur: &mut usize, dims: &WhirDims) -> WhirLayout {
        let alloc = |cur: &mut usize, count: usize, elem_size: usize| -> Range<usize> {
            let start = align_up(*cur, FIELD_ALIGN);
            let end = start + count * elem_size;
            *cur = end;
            start..end
        };

        let lay_base = |cur: &mut usize, d: &WhirBaseLayerDims| -> WhirBaseLayerByteLayout {
            let cap = alloc(cur, d.cap_digest_count * DIGEST_U32_WORDS, size_of::<u32>());
            let evals = alloc(cur, d.num_columns, size_of::<E4>());
            let query_indices = alloc(cur, d.query_count, size_of::<u32>());
            let query_leaves = alloc(cur, d.query_count * d.leaf_values_len, size_of::<BF>());
            let query_paths = alloc(
                cur,
                d.query_count * d.path_len * DIGEST_U32_WORDS,
                size_of::<u32>(),
            );
            WhirBaseLayerByteLayout {
                num_columns: d.num_columns,
                cap,
                evals,
                query_indices,
                query_leaves,
                query_paths,
                query_count: d.query_count,
                leaf_values_len: d.leaf_values_len,
                path_len: d.path_len,
            }
        };

        let lay_intermediate =
            |cur: &mut usize, d: &WhirIntermediateDims| -> WhirIntermediateByteLayout {
                let cap = alloc(cur, d.cap_digest_count * DIGEST_U32_WORDS, size_of::<u32>());
                let query_indices = alloc(cur, d.query_count, size_of::<u32>());
                let query_leaves = alloc(cur, d.query_count * d.leaf_values_len, size_of::<E4>());
                let query_paths = alloc(
                    cur,
                    d.query_count * d.path_len * DIGEST_U32_WORDS,
                    size_of::<u32>(),
                );
                WhirIntermediateByteLayout {
                    cap,
                    query_indices,
                    query_leaves,
                    query_paths,
                    query_count: d.query_count,
                    leaf_values_len: d.leaf_values_len,
                    path_len: d.path_len,
                }
            };

        let setup = lay_base(cur, &dims.setup);
        let memory = lay_base(cur, &dims.memory);
        let witness = lay_base(cur, &dims.witness);
        let intermediate = dims
            .intermediate
            .iter()
            .map(|d| lay_intermediate(cur, d))
            .collect();
        let ood_samples = alloc(cur, dims.num_ood_samples, size_of::<E4>());
        // sumcheck_polys entries are `[E4; 3]` = 3 * E4.
        let sumcheck_polys = alloc(cur, dims.total_sumcheck_polys * 3, size_of::<E4>());
        let pow_nonces = alloc(cur, dims.pow_rounds, size_of::<u64>());
        let final_monomials = alloc(cur, dims.final_monomials_len, size_of::<E4>());

        WhirLayout {
            setup,
            memory,
            witness,
            intermediate,
            ood_samples,
            sumcheck_polys,
            pow_nonces,
            final_monomials,
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
