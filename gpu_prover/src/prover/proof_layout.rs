//! Device-resident proof image — single `u8` slab layout.
//!
//! See `docs/gpu_scheduling_contract.md` and the iterative-knitting-bumblebee
//! plan. The intent is that every proof field produced on device lands in one
//! contiguous device allocation (the proof slab); one terminal D2H copies the
//! slab to pinned host memory; a single host parse over the slab emits the final
//! `GKRProof`.
//!
//! This module is dead code in Phase 1 — the slab is allocated at `prove()`
//! start but no kernels write to it yet. Phases 2-4 wire kernel writes into
//! slab offsets.
//!
//! ## Layout policy
//!
//! Each field range starts at an offset rounded up to `FIELD_ALIGN` (16). This
//! is a superset of the alignment of every proof element type we store (`E4`,
//! `BF`, `u32`, `u64`, digest words), so casting the raw pointer + the field's
//! `Range::start` as a typed `*mut T` is always well-aligned. The cost is a
//! handful of padding bytes per field; the benefit is that the layout math is
//! trivially correct and reviewable in one place.

use std::collections::BTreeMap;
use std::marker::PhantomData;
use std::mem::size_of;
use std::ops::Range;

use std::collections::BTreeSet;

use cs::definitions::GKRAddress;
use cs::gkr_compiler::{GKRCircuitArtifact, OutputType};
use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
use prover::gkr::prover::{SumcheckIntermediateProofValues, WhirSchedule};
use prover::gkr::whir::{
    BaseFieldQuery, ExtensionFieldQuery, WhirBaseLayerCommitmentAndQueries, WhirCommitment,
    WhirIntermediateCommitmentAndQueries, WhirPolyCommitProof,
};
use prover::merkle_trees::{DefaultTreeConstructor, MerkleTreeCapVarLength};

use crate::field::{BF, E4};
use crate::prover::gkr::stage1::GpuGKRTraceGeometry;

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

/// Phase 2a placeholder — returns empty dims for every section. Retained for
/// unit-test coverage of the empty-slab edge case. Real `prove()` uses
/// [`build_proof_layout_inputs`].
#[cfg(test)]
pub(crate) fn placeholder_inputs_for_prove() -> ProofLayoutInputs {
    ProofLayoutInputs {
        output_evaluations: BTreeMap::new(),
        backward_layers: Vec::new(),
        whir: WhirDims {
            setup: empty_base_layer_dims(),
            memory: empty_base_layer_dims(),
            witness: empty_base_layer_dims(),
            intermediate: Vec::new(),
            num_ood_samples: 0,
            total_sumcheck_polys: 0,
            pow_rounds: 0,
            final_monomials_len: 0,
        },
    }
}

#[cfg(test)]
fn empty_base_layer_dims() -> WhirBaseLayerDims {
    WhirBaseLayerDims {
        num_columns: 0,
        cap_digest_count: 0,
        query_count: 0,
        leaf_values_len: 0,
        path_len: 0,
    }
}

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

/// Build real [`ProofLayoutInputs`] for one `prove()` invocation.
///
/// All dimensions are derivable from the WHIR schedule + circuit artifact +
/// final-trace size + the forward pass's `dimension_reducing_inputs` +
/// per-main-layer input address sets (from
/// `collect_main_layer_input_addresses_per_layer`). All of these are
/// available once `schedule_forward_pass` returns.
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
///   `dimension_reducing_inputs[layer_idx].values().flat_map(.inputs)`
///   deduplicated and sorted (matching the BTreeMap-keyed iteration order in
///   `final_evaluation_sources_for_last_step`, backward.rs:4945-4980). Main
///   layer `final_step_eval_addresses` come from
///   `main_layer_input_addresses_per_layer[layer_idx]` (same underlying
///   source: the union of `kernel.inputs.inputs_in_base` +
///   `inputs_in_extension` per blueprint, matching main-layer
///   `final_evaluation_sources_for_last_step`).
///
/// Note: `extra_evaluations_from_caching_relations` (main layer 0 only) is
/// not a separate slab range. Its values are sparse references into the
/// slab-resident WHIR base eval ranges; Phase 4 reconstructs the map from
/// `base_layer_claims_shared_state` metadata plus the terminal slab mirror.
/// * `whir`: derivation mirrors `whir_fold.rs:1742-1792`. `final_monomials_len`
///   is 0 because the current GPU prover leaves `proof.final_monomials =
///   vec![]` (whir_fold.rs:1870); revisit if that changes.
pub(crate) fn build_proof_layout_inputs(
    compiled_circuit: &GKRCircuitArtifact<BF>,
    whir_schedule: &WhirSchedule,
    final_trace_size_log_2: usize,
    dimension_reducing_inputs: &BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
    main_layer_input_addresses_per_layer: &[Vec<GKRAddress>],
    main_layer_orphan_output_addresses_per_layer: &[Vec<GKRAddress>],
    memory_geometry: ProofLayoutBaseLayerGeometry,
    witness_geometry: ProofLayoutBaseLayerGeometry,
    setup_geometry: ProofLayoutBaseLayerGeometry,
) -> ProofLayoutInputs {
    let initial_trace_size_log_2 = compiled_circuit.trace_len.trailing_zeros() as usize;
    assert!(initial_trace_size_log_2 >= final_trace_size_log_2);
    let num_dim_reducing_layers = initial_trace_size_log_2 - final_trace_size_log_2;
    let num_main_layers = compiled_circuit.layers.len();
    assert_eq!(
        dimension_reducing_inputs.len(),
        num_dim_reducing_layers,
        "dimension_reducing_inputs must have one entry per dim-reducing layer",
    );
    assert_eq!(
        main_layer_input_addresses_per_layer.len(),
        num_main_layers,
        "main_layer_input_addresses_per_layer must have one entry per main layer",
    );
    assert_eq!(
        main_layer_orphan_output_addresses_per_layer.len(),
        num_main_layers,
        "main_layer_orphan_output_addresses_per_layer must have one entry per main layer",
    );

    // ------------------------------------------------------------------
    // output_evaluations: one (read_set, write_set) entry per OutputType.
    // Both halves have length `1 << final_trace_size_log_2` (the reduced-
    // output polynomial size at the initial sumcheck layer).
    // ------------------------------------------------------------------
    let reduced_poly_len = 1usize << final_trace_size_log_2;
    let mut output_evaluations = BTreeMap::new();
    for (&output_type, addresses) in compiled_circuit.global_output_map.iter() {
        assert_eq!(
            addresses.len(),
            2,
            "global_output_map[{:?}] must have exactly 2 entries (read + write set)",
            output_type,
        );
        output_evaluations.insert(output_type, [reduced_poly_len, reduced_poly_len]);
    }

    // ------------------------------------------------------------------
    // backward_layers (scheduler high-to-low order)
    // ------------------------------------------------------------------
    //
    // Dim-reducing slot 0 is the highest layer_idx = `num_main_layers +
    // num_dim_reducing_layers - 1` (= `initial_layer_for_sumcheck`), with
    // sumcheck_num_rounds = final_trace_size_log_2. Each subsequent
    // dim-reducing slot covers one lower layer_idx and one more folding step
    // (see backward.rs:3251-3253 + backward.rs:3387). Main layers follow in
    // `compiled_circuit.layers.into_iter().enumerate().rev()` order — index
    // `num_main_layers - 1` down to 0 — each with
    // `sumcheck_num_rounds = initial_trace_size_log_2` (backward.rs:3503).
    let mut backward_layers = Vec::with_capacity(num_dim_reducing_layers + num_main_layers);
    for slot in 0..num_dim_reducing_layers {
        let layer_idx = num_main_layers + num_dim_reducing_layers - 1 - slot;
        let sumcheck_num_rounds = final_trace_size_log_2 + slot;
        let io_map = dimension_reducing_inputs
            .get(&layer_idx)
            .unwrap_or_else(|| {
                panic!("dimension_reducing_inputs missing entry for layer_idx {layer_idx}")
            });
        let mut addresses: BTreeSet<GKRAddress> = BTreeSet::new();
        for io in io_map.values() {
            for addr in io.inputs.iter() {
                addresses.insert(*addr);
            }
        }
        backward_layers.push(BackwardLayerDims {
            layer_idx,
            sumcheck_num_rounds,
            final_step_eval_addresses: addresses.into_iter().collect(),
            final_step_eval_degree: 4,
            // Dim-reducing layers don't host the kind of orphan-output
            // pattern that main-layer `MaxQuadratic` produces; the
            // forward dim-reduction pass wires every output from one
            // round directly into the next round's inputs.
            extra_evaluations_addresses: Vec::new(),
        });
    }
    for layer_idx in (0..num_main_layers).rev() {
        backward_layers.push(BackwardLayerDims {
            layer_idx,
            sumcheck_num_rounds: initial_trace_size_log_2,
            final_step_eval_addresses: main_layer_input_addresses_per_layer[layer_idx].clone(),
            final_step_eval_degree: 2,
            extra_evaluations_addresses: main_layer_orphan_output_addresses_per_layer[layer_idx]
                .clone(),
        });
    }

    // ------------------------------------------------------------------
    // whir
    // ------------------------------------------------------------------
    assert_eq!(
        whir_schedule.whir_steps_schedule.len(),
        whir_schedule.whir_queries_schedule.len(),
    );
    assert_eq!(
        whir_schedule.whir_steps_schedule.len(),
        whir_schedule.whir_pow_schedule.len(),
    );
    assert_eq!(
        whir_schedule.whir_steps_schedule.len(),
        whir_schedule.whir_steps_lde_factors.len() + 1,
    );
    let initial_values_per_leaf = 1usize << whir_schedule.whir_steps_schedule[0];
    let tree_cap_size = whir_schedule.cap_size;
    let tree_cap_log2 = tree_cap_size.trailing_zeros() as usize;
    let initial_query_count = whir_schedule.whir_queries_schedule[0];

    let base_layer_dims = |g: ProofLayoutBaseLayerGeometry| -> WhirBaseLayerDims {
        // `cap_digest_count`: total digests across all LDE cosets for this
        // base layer. `allocate_tree_caps` sizes each coset at
        // `1 << (log_tree_cap_size - log_lde_factor)` digests (trace_holder.rs)
        // so the sum over `lde_factor` cosets is `1 << log_tree_cap_size`.
        let cap_digest_count = 1usize << g.log_tree_cap_size;
        let leaf_values_len = g.columns_count * initial_values_per_leaf;
        // Matches whir_fold.rs:1765-1776 and the setup_columns_count==0
        // branch at 1846.
        let path_len = if g.columns_count == 0 {
            0
        } else {
            (g.log_domain_size - g.log_rows_per_leaf - (g.log_tree_cap_size - g.log_lde_factor))
                as usize
        };
        WhirBaseLayerDims {
            num_columns: g.columns_count,
            cap_digest_count,
            query_count: initial_query_count,
            leaf_values_len,
            path_len,
        }
    };

    let mut folded_trace_len_log2 = initial_trace_size_log_2;
    let mut intermediate = Vec::with_capacity(whir_schedule.whir_steps_lde_factors.len());
    for (oracle_idx, &lde_factor) in whir_schedule.whir_steps_lde_factors.iter().enumerate() {
        folded_trace_len_log2 -= whir_schedule.whir_steps_schedule[oracle_idx];
        let values_per_leaf_log2 = whir_schedule.whir_steps_schedule[oracle_idx + 1];
        let path_len = folded_trace_len_log2 + lde_factor.trailing_zeros() as usize
            - values_per_leaf_log2
            - tree_cap_log2;
        intermediate.push(WhirIntermediateDims {
            cap_digest_count: tree_cap_size,
            query_count: whir_schedule.whir_queries_schedule[oracle_idx + 1],
            leaf_values_len: 1usize << values_per_leaf_log2,
            path_len,
        });
    }

    let whir = WhirDims {
        setup: base_layer_dims(setup_geometry),
        memory: base_layer_dims(memory_geometry),
        witness: base_layer_dims(witness_geometry),
        intermediate,
        num_ood_samples: whir_schedule.whir_steps_lde_factors.len(),
        total_sumcheck_polys: whir_schedule.whir_steps_schedule.iter().sum::<usize>(),
        pow_rounds: whir_schedule.whir_pow_schedule.len(),
        // GPU prover currently leaves `WhirPolyCommitProof::final_monomials`
        // as `vec![]` (whir_fold.rs:1870). If a future commit teaches WHIR
        // to emit the final monomial basis, lift this from the schedule via
        // `initial_trace_size_log_2 - sum(whir_steps_schedule)`.
        final_monomials_len: 0,
    };

    ProofLayoutInputs {
        output_evaluations,
        backward_layers,
        whir,
    }
}

/// Structural variant of [`build_proof_layout_inputs`] that derives every input
/// from the compiled circuit + WHIR schedule + base-layer geometries — no
/// forward-pass output required. Used by `prove()` to size the proof slab
/// before `schedule_forward_pass` runs.
///
/// Internally:
/// * `dimension_reducing_inputs` is reproduced by
///   [`crate::prover::gkr::backward::derive_dimension_reducing_inputs_structural`]
///   (address-assignment rules match `schedule_dimension_reduction_forward`).
/// * `main_layer_input_addresses_per_layer` is reproduced by
///   [`crate::prover::gkr::backward::collect_main_layer_input_addresses_per_layer_structural`]
///   (storage-aware version's address set is invariant of which kernel-kind
///   branch is taken — see that function's doc).
pub(crate) fn build_proof_layout_inputs_structural<E>(
    compiled_circuit: &GKRCircuitArtifact<BF>,
    external_challenges: &prover::gkr::prover::GKRExternalChallenges<BF, E>,
    whir_schedule: &WhirSchedule,
    final_trace_size_log_2: usize,
    memory_geometry: ProofLayoutBaseLayerGeometry,
    witness_geometry: ProofLayoutBaseLayerGeometry,
    setup_geometry: ProofLayoutBaseLayerGeometry,
) -> ProofLayoutInputs
where
    E: field::Field + field::FieldExtension<BF>,
{
    // Normalize-once for the address-derivation helpers so they see the
    // same `(MaxQuadratic { output: ScratchSpace(K) })` shape that the
    // backward main-layer scheduler operates on. Without this, orphan
    // addresses derived structurally would still carry `InnerLayer { ..
    // }` for scratch-mapped MaxQuadratic outputs, while runtime kernel
    // outputs (post-normalize) carry `ScratchSpace(K)` — and the
    // resulting `next_claim_layout` augmentation would never match
    // L-1's `claim_idx` lookup. The clone is paid once per proof.
    let normalized_compiled_circuit =
        crate::prover::gkr::transform::normalize_compiled_circuit_for_gpu(compiled_circuit.clone());
    let initial_trace_size_log_2 = normalized_compiled_circuit.trace_len.trailing_zeros() as usize;
    let dim_reducing_inputs =
        crate::prover::gkr::backward::derive_dimension_reducing_inputs_structural(
            normalized_compiled_circuit.layers.len(),
            &normalized_compiled_circuit.global_output_map,
            initial_trace_size_log_2,
            final_trace_size_log_2,
        );
    let main_layer_addresses =
        crate::prover::gkr::backward::collect_main_layer_input_addresses_per_layer_structural::<E>(
            &normalized_compiled_circuit,
            external_challenges,
        );
    let main_layer_outputs =
        crate::prover::gkr::backward::collect_main_layer_kernel_output_addresses_per_layer_structural::<E>(
            &normalized_compiled_circuit,
            external_challenges,
        );
    let main_layer_orphans =
        crate::prover::gkr::backward::compute_main_layer_orphan_output_addresses_per_layer::<E>(
            &main_layer_addresses,
            &main_layer_outputs,
        );
    build_proof_layout_inputs(
        &normalized_compiled_circuit,
        whir_schedule,
        final_trace_size_log_2,
        &dim_reducing_inputs,
        &main_layer_addresses,
        &main_layer_orphans,
        memory_geometry,
        witness_geometry,
        setup_geometry,
    )
}

impl ProofLayout {
    pub(crate) fn new(inputs: &ProofLayoutInputs) -> Self {
        let mut cur = 0usize;

        let mut alloc = |cur: &mut usize, count: usize, elem_size: usize| -> Range<usize> {
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
        let mut alloc = |cur: &mut usize, count: usize, elem_size: usize| -> Range<usize> {
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
// Typed accessors — device side (raw pointer + count)
// ---------------------------------------------------------------------------
//
// Each method takes a `*mut u8` pointer to the slab base (produced from a
// `DeviceAllocation<u8>`) and returns `(*mut T, usize)`: a typed pointer into
// the slab at the field's offset and the element count. Used at kernel-launch
// sites to wire slab offsets as kernel output pointers.
//
// Safety: the returned pointer is valid only as long as the underlying device
// allocation is live, and the caller must not dereference it from host code.
// The slab pointer is assumed to be 16-byte aligned; `ProofLayout::new`
// guarantees every range's start is also 16-byte aligned so typed casts to any
// proof element type are valid.

impl ProofLayout {
    #[inline]
    unsafe fn device_typed<T>(slab_base: *mut u8, range: &Range<usize>) -> (*mut T, usize) {
        let ptr = slab_base.add(range.start) as *mut T;
        let bytes = range.end - range.start;
        debug_assert_eq!(
            bytes % size_of::<T>(),
            0,
            "slab range size must be a multiple of element size"
        );
        (ptr, bytes / size_of::<T>())
    }

    pub(crate) unsafe fn backward_internal_coeffs_device_mut(
        &self,
        slab_base: *mut u8,
        layer_slot: usize,
    ) -> (*mut E4, usize) {
        Self::device_typed::<E4>(
            slab_base,
            &self.backward[layer_slot].internal_round_coefficients,
        )
    }

    pub(crate) unsafe fn backward_final_step_evals_device_mut(
        &self,
        slab_base: *mut u8,
        layer_slot: usize,
    ) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.backward[layer_slot].final_step_evaluations)
    }

    /// Per-layer-slot `extra_evaluations` range. Returns `(ptr, addresses_len)`
    /// — one `E4` per orphan address. Length is 0 for dim-reducing slots and
    /// for main layers without orphan outputs.
    pub(crate) unsafe fn backward_extra_evaluations_device_mut(
        &self,
        slab_base: *mut u8,
        layer_slot: usize,
    ) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.backward[layer_slot].extra_evaluations)
    }

    pub(crate) unsafe fn output_evaluations_device_mut(
        &self,
        slab_base: *mut u8,
    ) -> Option<(*mut E4, usize)> {
        let block = self.output_evaluations_block()?;
        Some(Self::device_typed::<E4>(slab_base, &block))
    }

    pub(crate) unsafe fn whir_base_cap_device_mut(
        &self,
        slab_base: *mut u8,
        which: WhirBaseLayerKind,
    ) -> (*mut u32, usize) {
        Self::device_typed::<u32>(slab_base, &self.whir_base(which).cap)
    }

    pub(crate) unsafe fn whir_base_evals_device_mut(
        &self,
        slab_base: *mut u8,
        which: WhirBaseLayerKind,
    ) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.whir_base(which).evals)
    }

    pub(crate) unsafe fn whir_base_query_indices_device_mut(
        &self,
        slab_base: *mut u8,
        which: WhirBaseLayerKind,
    ) -> (*mut u32, usize) {
        Self::device_typed::<u32>(slab_base, &self.whir_base(which).query_indices)
    }

    pub(crate) unsafe fn whir_base_query_leaves_device_mut(
        &self,
        slab_base: *mut u8,
        which: WhirBaseLayerKind,
    ) -> (*mut BF, usize) {
        Self::device_typed::<BF>(slab_base, &self.whir_base(which).query_leaves)
    }

    pub(crate) unsafe fn whir_base_query_paths_device_mut(
        &self,
        slab_base: *mut u8,
        which: WhirBaseLayerKind,
    ) -> (*mut u32, usize) {
        Self::device_typed::<u32>(slab_base, &self.whir_base(which).query_paths)
    }

    pub(crate) unsafe fn whir_intermediate_cap_device_mut(
        &self,
        slab_base: *mut u8,
        round: usize,
    ) -> (*mut u32, usize) {
        Self::device_typed::<u32>(slab_base, &self.whir.intermediate[round].cap)
    }

    pub(crate) unsafe fn whir_intermediate_query_indices_device_mut(
        &self,
        slab_base: *mut u8,
        round: usize,
    ) -> (*mut u32, usize) {
        Self::device_typed::<u32>(slab_base, &self.whir.intermediate[round].query_indices)
    }

    pub(crate) unsafe fn whir_intermediate_query_leaves_device_mut(
        &self,
        slab_base: *mut u8,
        round: usize,
    ) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.whir.intermediate[round].query_leaves)
    }

    pub(crate) unsafe fn whir_intermediate_query_paths_device_mut(
        &self,
        slab_base: *mut u8,
        round: usize,
    ) -> (*mut u32, usize) {
        Self::device_typed::<u32>(slab_base, &self.whir.intermediate[round].query_paths)
    }

    pub(crate) unsafe fn whir_ood_samples_device_mut(
        &self,
        slab_base: *mut u8,
    ) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.whir.ood_samples)
    }

    pub(crate) unsafe fn whir_sumcheck_polys_device_mut(
        &self,
        slab_base: *mut u8,
    ) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.whir.sumcheck_polys)
    }

    pub(crate) unsafe fn whir_pow_nonces_device_mut(
        &self,
        slab_base: *mut u8,
    ) -> (*mut u64, usize) {
        Self::device_typed::<u64>(slab_base, &self.whir.pow_nonces)
    }

    pub(crate) unsafe fn whir_final_monomials_device_mut(
        &self,
        slab_base: *mut u8,
    ) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.whir.final_monomials)
    }

    fn whir_base(&self, which: WhirBaseLayerKind) -> &WhirBaseLayerByteLayout {
        match which {
            WhirBaseLayerKind::Setup => &self.whir.setup,
            WhirBaseLayerKind::Memory => &self.whir.memory,
            WhirBaseLayerKind::Witness => &self.whir.witness,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum WhirBaseLayerKind {
    Setup,
    Memory,
    Witness,
}

// ---------------------------------------------------------------------------
// Typed accessors — host side (slice views over the D2H'd blob)
// ---------------------------------------------------------------------------
//
// Used at proof-parse time after the terminal D2H has copied the slab into a
// pinned host buffer. Each method returns a typed slice into that buffer.

impl ProofLayout {
    fn host_typed<'a, T>(slab: &'a [u8], range: &Range<usize>) -> &'a [T] {
        let bytes = &slab[range.clone()];
        debug_assert_eq!(
            bytes.as_ptr() as usize % std::mem::align_of::<T>(),
            0,
            "slab range start must be aligned for T"
        );
        debug_assert_eq!(
            bytes.len() % size_of::<T>(),
            0,
            "slab range size must be a multiple of element size"
        );
        // SAFETY: the slab is allocated as pinned pinned host bytes populated
        // via `memory_copy_async`; element alignment is asserted above and
        // guaranteed by the layout policy (field-start aligned to FIELD_ALIGN,
        // which is ≥ align_of::<T>() for every element type used here).
        unsafe {
            std::slice::from_raw_parts(bytes.as_ptr() as *const T, bytes.len() / size_of::<T>())
        }
    }

    pub(crate) fn backward_internal_coeffs_host<'a>(
        &self,
        slab: &'a [u8],
        layer_slot: usize,
    ) -> &'a [E4] {
        Self::host_typed::<E4>(slab, &self.backward[layer_slot].internal_round_coefficients)
    }

    pub(crate) fn backward_final_step_evals_host<'a>(
        &self,
        slab: &'a [u8],
        layer_slot: usize,
    ) -> &'a [E4] {
        Self::host_typed::<E4>(slab, &self.backward[layer_slot].final_step_evaluations)
    }

    pub(crate) fn backward_extra_evaluations_host<'a>(
        &self,
        slab: &'a [u8],
        layer_slot: usize,
    ) -> &'a [E4] {
        Self::host_typed::<E4>(slab, &self.backward[layer_slot].extra_evaluations)
    }

    pub(crate) fn output_evaluations_read_host<'a>(
        &self,
        slab: &'a [u8],
        output_type: OutputType,
    ) -> &'a [E4] {
        let layout = self
            .output_evaluations
            .get(&output_type)
            .expect("unknown OutputType in slab layout");
        Self::host_typed::<E4>(slab, &layout.read_set)
    }

    pub(crate) fn output_evaluations_write_host<'a>(
        &self,
        slab: &'a [u8],
        output_type: OutputType,
    ) -> &'a [E4] {
        let layout = self
            .output_evaluations
            .get(&output_type)
            .expect("unknown OutputType in slab layout");
        Self::host_typed::<E4>(slab, &layout.write_set)
    }

    /// Parse `final_explicit_evaluations: BTreeMap<OutputType, [Vec<E4>; 2]>`
    /// from the D2H'd slab. The forward dim-reduction pass writes every
    /// reduced-output poly into a single contiguous block in BTreeMap key
    /// order × {read, write}; this parse re-emits the BTreeMap by slicing the
    /// host-mirrored slab byte-for-byte.
    pub(crate) fn parse_final_explicit_evaluations(
        &self,
        slab: &[u8],
    ) -> BTreeMap<OutputType, [Vec<E4>; 2]> {
        self.output_evaluations
            .keys()
            .map(|&output_type| {
                let read = self
                    .output_evaluations_read_host(slab, output_type)
                    .to_vec();
                let write = self
                    .output_evaluations_write_host(slab, output_type)
                    .to_vec();
                (output_type, [read, write])
            })
            .collect()
    }

    /// Phase 4: parse every slab-resident WHIR proof field into a fresh
    /// `WhirPolyCommitProof`. Base-layer `queries` are left as `Vec::new()`
    /// (the caller is expected to overwrite from the host-side callback
    /// path — base-layer queries stay on host per the approved plan);
    /// `final_monomials` is `vec![]` (GPU prover leaves this empty today,
    /// matching the layout's `final_monomials_len: 0`).
    pub(crate) fn parse_whir_proof(
        &self,
        slab: &[u8],
    ) -> WhirPolyCommitProof<BF, E4, DefaultTreeConstructor> {
        let digest_bytes_of = |bytes: &[u32]| -> Vec<[u32; DIGEST_U32_WORDS]> {
            bytes
                .chunks_exact(DIGEST_U32_WORDS)
                .map(|c| {
                    let mut d = [0u32; DIGEST_U32_WORDS];
                    d.copy_from_slice(c);
                    d
                })
                .collect()
        };
        let base = |which: WhirBaseLayerKind| -> WhirBaseLayerCommitmentAndQueries<
            BF,
            E4,
            DefaultTreeConstructor,
        > {
            let base_layout = self.whir_base(which);
            let cap_flat = self.whir_base_cap_host(slab, which);
            let cap = digest_bytes_of(cap_flat);
            let evals = self.whir_base_evals_host(slab, which).to_vec();
            WhirBaseLayerCommitmentAndQueries {
                commitment: WhirCommitment {
                    cap: MerkleTreeCapVarLength { cap },
                    _marker: PhantomData,
                },
                num_columns: base_layout.num_columns,
                evals,
                queries: Vec::new(),
            }
        };
        let setup_commitment = base(WhirBaseLayerKind::Setup);
        let memory_commitment = base(WhirBaseLayerKind::Memory);
        let witness_commitment = base(WhirBaseLayerKind::Witness);
        let intermediate_whir_oracles: Vec<
            WhirIntermediateCommitmentAndQueries<BF, E4, DefaultTreeConstructor>,
        > = self
            .whir
            .intermediate
            .iter()
            .enumerate()
            .map(|(round, inter)| {
                let cap_flat = self.whir_intermediate_cap_host(slab, round);
                let cap = digest_bytes_of(cap_flat);
                let indices = self.whir_intermediate_query_indices_host(slab, round);
                let leaves = self.whir_intermediate_query_leaves_host(slab, round);
                let paths_flat = self.whir_intermediate_query_paths_host(slab, round);
                let query_count = inter.query_count;
                let leaf_values_len = inter.leaf_values_len;
                let path_len = inter.path_len;
                let queries: Vec<ExtensionFieldQuery<BF, E4, DefaultTreeConstructor>> = (0
                    ..query_count)
                    .map(|q| {
                        let leaf_start = q * leaf_values_len;
                        let leaf_end = leaf_start + leaf_values_len;
                        let path_start_u32 = q * path_len * DIGEST_U32_WORDS;
                        let path_end_u32 = path_start_u32 + path_len * DIGEST_U32_WORDS;
                        ExtensionFieldQuery {
                            index: indices[q] as usize,
                            leaf_values_concatenated: leaves[leaf_start..leaf_end].to_vec(),
                            path: digest_bytes_of(&paths_flat[path_start_u32..path_end_u32]),
                            _marker: PhantomData,
                        }
                    })
                    .collect();
                WhirIntermediateCommitmentAndQueries {
                    commitment: WhirCommitment {
                        cap: MerkleTreeCapVarLength { cap },
                        _marker: PhantomData,
                    },
                    queries,
                }
            })
            .collect();
        let ood_samples = self.whir_ood_samples_host(slab).to_vec();
        let sumcheck_polys: Vec<[E4; 3]> = self
            .whir_sumcheck_polys_host(slab)
            .chunks_exact(3)
            .map(|c| [c[0], c[1], c[2]])
            .collect();
        let pow_nonces = self.whir_pow_nonces_host(slab).to_vec();
        let final_monomials = self.whir_final_monomials_host(slab).to_vec();
        WhirPolyCommitProof {
            setup_commitment,
            memory_commitment,
            witness_commitment,
            intermediate_whir_oracles,
            ood_samples,
            sumcheck_polys,
            pow_nonces,
            final_monomials,
        }
    }

    /// Phase 4: parse `sumcheck_intermediate_values: BTreeMap<layer_idx, _>`
    /// from the D2H'd slab.
    ///
    /// `extra_evaluations_by_layer` is the caller-provided sparse map for
    /// layer 0 only — its values are sparse references into the slab-resident
    /// WHIR base eval ranges (`DenseSource::read_from_slab`). For every other
    /// layer-slot we read the dedicated `extra_evaluations` slab range
    /// directly: each entry is one `E4` per orphan address, in
    /// `extra_evaluations_addresses` order. Both sources are merged into the
    /// same `extra_evaluations_from_caching_relations` BTreeMap on the
    /// resulting `SumcheckIntermediateProofValues`.
    pub(crate) fn parse_sumcheck_intermediate_values(
        &self,
        slab: &[u8],
        mut extra_evaluations_by_layer: BTreeMap<usize, BTreeMap<GKRAddress, E4>>,
    ) -> BTreeMap<usize, SumcheckIntermediateProofValues<BF, E4>> {
        let mut result = BTreeMap::new();
        for (layer_slot, bw) in self.backward.iter().enumerate() {
            let coeffs_flat = self.backward_internal_coeffs_host(slab, layer_slot);
            debug_assert_eq!(
                coeffs_flat.len(),
                bw.sumcheck_num_rounds.saturating_sub(1) * 4
            );
            let internal_round_coefficients: Vec<[E4; 4]> = coeffs_flat
                .chunks_exact(4)
                .map(|c| [c[0], c[1], c[2], c[3]])
                .collect();
            let finals_flat = self.backward_final_step_evals_host(slab, layer_slot);
            debug_assert_eq!(
                finals_flat.len(),
                bw.final_step_eval_addresses.len() * bw.final_step_eval_degree
            );
            let final_step_evaluations: BTreeMap<GKRAddress, Vec<E4>> = bw
                .final_step_eval_addresses
                .iter()
                .enumerate()
                .map(|(i, addr)| {
                    let start = i * bw.final_step_eval_degree;
                    let end = start + bw.final_step_eval_degree;
                    (*addr, finals_flat[start..end].to_vec())
                })
                .collect();
            let mut extra_evaluations_from_caching_relations = extra_evaluations_by_layer
                .remove(&bw.layer_idx)
                .unwrap_or_default();
            if !bw.extra_evaluations_addresses.is_empty() {
                let extras_flat = self.backward_extra_evaluations_host(slab, layer_slot);
                debug_assert_eq!(
                    extras_flat.len(),
                    bw.extra_evaluations_addresses.len(),
                    "slab extra_evaluations length must match address ordering",
                );
                for (addr, value) in bw
                    .extra_evaluations_addresses
                    .iter()
                    .zip(extras_flat.iter())
                {
                    let prev = extra_evaluations_from_caching_relations.insert(*addr, *value);
                    debug_assert!(
                        prev.is_none(),
                        "duplicate extra-evaluation address across slab range and caller map: {addr:?}",
                    );
                }
            }
            result.insert(
                bw.layer_idx,
                SumcheckIntermediateProofValues {
                    sumcheck_num_rounds: bw.sumcheck_num_rounds,
                    internal_round_coefficients,
                    final_step_evaluations,
                    extra_evaluations_from_caching_relations,
                    _marker: PhantomData,
                },
            );
        }
        result
    }

    pub(crate) fn whir_base_cap_host<'a>(
        &self,
        slab: &'a [u8],
        which: WhirBaseLayerKind,
    ) -> &'a [u32] {
        Self::host_typed::<u32>(slab, &self.whir_base(which).cap)
    }

    pub(crate) fn whir_base_evals_host<'a>(
        &self,
        slab: &'a [u8],
        which: WhirBaseLayerKind,
    ) -> &'a [E4] {
        Self::host_typed::<E4>(slab, &self.whir_base(which).evals)
    }

    pub(crate) fn whir_base_query_indices_host<'a>(
        &self,
        slab: &'a [u8],
        which: WhirBaseLayerKind,
    ) -> &'a [u32] {
        Self::host_typed::<u32>(slab, &self.whir_base(which).query_indices)
    }

    pub(crate) fn whir_base_query_leaves_host<'a>(
        &self,
        slab: &'a [u8],
        which: WhirBaseLayerKind,
    ) -> &'a [BF] {
        Self::host_typed::<BF>(slab, &self.whir_base(which).query_leaves)
    }

    pub(crate) fn whir_base_query_paths_host<'a>(
        &self,
        slab: &'a [u8],
        which: WhirBaseLayerKind,
    ) -> &'a [u32] {
        Self::host_typed::<u32>(slab, &self.whir_base(which).query_paths)
    }

    pub(crate) fn whir_intermediate_cap_host<'a>(&self, slab: &'a [u8], round: usize) -> &'a [u32] {
        Self::host_typed::<u32>(slab, &self.whir.intermediate[round].cap)
    }

    pub(crate) fn whir_intermediate_query_indices_host<'a>(
        &self,
        slab: &'a [u8],
        round: usize,
    ) -> &'a [u32] {
        Self::host_typed::<u32>(slab, &self.whir.intermediate[round].query_indices)
    }

    pub(crate) fn whir_intermediate_query_leaves_host<'a>(
        &self,
        slab: &'a [u8],
        round: usize,
    ) -> &'a [E4] {
        Self::host_typed::<E4>(slab, &self.whir.intermediate[round].query_leaves)
    }

    pub(crate) fn whir_intermediate_query_paths_host<'a>(
        &self,
        slab: &'a [u8],
        round: usize,
    ) -> &'a [u32] {
        Self::host_typed::<u32>(slab, &self.whir.intermediate[round].query_paths)
    }

    pub(crate) fn whir_ood_samples_host<'a>(&self, slab: &'a [u8]) -> &'a [E4] {
        Self::host_typed::<E4>(slab, &self.whir.ood_samples)
    }

    pub(crate) fn whir_sumcheck_polys_host<'a>(&self, slab: &'a [u8]) -> &'a [E4] {
        Self::host_typed::<E4>(slab, &self.whir.sumcheck_polys)
    }

    pub(crate) fn whir_pow_nonces_host<'a>(&self, slab: &'a [u8]) -> &'a [u64] {
        Self::host_typed::<u64>(slab, &self.whir.pow_nonces)
    }

    pub(crate) fn whir_final_monomials_host<'a>(&self, slab: &'a [u8]) -> &'a [E4] {
        Self::host_typed::<E4>(slab, &self.whir.final_monomials)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use field::{Field, FieldExtension, PrimeField};

    fn sample_inputs() -> ProofLayoutInputs {
        let backward_layers = vec![
            BackwardLayerDims {
                layer_idx: 8,
                sumcheck_num_rounds: 3,
                final_step_eval_addresses: vec![GKRAddress::BaseLayerWitness(0); 2],
                final_step_eval_degree: 4,
                // Dim-reducing slot: never has orphans.
                extra_evaluations_addresses: Vec::new(),
            },
            BackwardLayerDims {
                layer_idx: 0,
                sumcheck_num_rounds: 5,
                final_step_eval_addresses: vec![GKRAddress::BaseLayerWitness(0); 3],
                final_step_eval_degree: 2,
                // Exercise non-empty orphans to validate the extra
                // range's sizing + parser round-trip in this slot.
                // Production code derives this list via a BTreeSet
                // (`compute_main_layer_orphan_output_addresses_per_layer`),
                // so the ordering matches `GKRAddress`'s `Ord` impl —
                // `InnerLayer` < `ScratchSpace` per the enum-variant
                // declaration order.
                extra_evaluations_addresses: vec![
                    GKRAddress::InnerLayer {
                        layer: 1,
                        offset: 0,
                    },
                    GKRAddress::ScratchSpace(7),
                ],
            },
        ];

        let whir = WhirDims {
            setup: WhirBaseLayerDims {
                num_columns: 4,
                cap_digest_count: 8,
                query_count: 16,
                leaf_values_len: 32,
                path_len: 12,
            },
            memory: WhirBaseLayerDims {
                num_columns: 32,
                cap_digest_count: 8,
                query_count: 16,
                leaf_values_len: 128,
                path_len: 12,
            },
            witness: WhirBaseLayerDims {
                num_columns: 64,
                cap_digest_count: 8,
                query_count: 16,
                leaf_values_len: 256,
                path_len: 12,
            },
            intermediate: vec![
                WhirIntermediateDims {
                    cap_digest_count: 8,
                    query_count: 12,
                    leaf_values_len: 16,
                    path_len: 10,
                },
                WhirIntermediateDims {
                    cap_digest_count: 8,
                    query_count: 10,
                    leaf_values_len: 16,
                    path_len: 8,
                },
            ],
            num_ood_samples: 2,
            total_sumcheck_polys: 8,
            pow_rounds: 3,
            final_monomials_len: 4,
        };

        let mut output_evaluations = BTreeMap::new();
        output_evaluations.insert(OutputType::PermutationProduct, [2usize, 2usize]);
        output_evaluations.insert(OutputType::Lookup16Bits, [1usize, 1usize]);

        ProofLayoutInputs {
            output_evaluations,
            backward_layers,
            whir,
        }
    }

    #[test]
    fn layout_is_16_byte_aligned_and_nonoverlapping() {
        let inputs = sample_inputs();
        let layout = ProofLayout::new(&inputs);

        let mut ranges: Vec<(String, Range<usize>)> = Vec::new();
        for (&output_type, r) in layout.output_evaluations.iter() {
            ranges.push((format!("{output_type:?}.read"), r.read_set.clone()));
            ranges.push((format!("{output_type:?}.write"), r.write_set.clone()));
        }
        for bw in &layout.backward {
            ranges.push((
                format!("backward[{}].internal", bw.layer_idx),
                bw.internal_round_coefficients.clone(),
            ));
            ranges.push((
                format!("backward[{}].final", bw.layer_idx),
                bw.final_step_evaluations.clone(),
            ));
            if !bw.extra_evaluations_addresses.is_empty() {
                ranges.push((
                    format!("backward[{}].extra", bw.layer_idx),
                    bw.extra_evaluations.clone(),
                ));
            }
        }
        for (name, base) in [
            ("setup", &layout.whir.setup),
            ("memory", &layout.whir.memory),
            ("witness", &layout.whir.witness),
        ] {
            ranges.push((format!("whir.{name}.cap"), base.cap.clone()));
            ranges.push((format!("whir.{name}.evals"), base.evals.clone()));
            ranges.push((format!("whir.{name}.qi"), base.query_indices.clone()));
            ranges.push((format!("whir.{name}.ql"), base.query_leaves.clone()));
            ranges.push((format!("whir.{name}.qp"), base.query_paths.clone()));
        }
        for (i, im) in layout.whir.intermediate.iter().enumerate() {
            ranges.push((format!("whir.intermediate[{i}].cap"), im.cap.clone()));
            ranges.push((
                format!("whir.intermediate[{i}].qi"),
                im.query_indices.clone(),
            ));
            ranges.push((
                format!("whir.intermediate[{i}].ql"),
                im.query_leaves.clone(),
            ));
            ranges.push((format!("whir.intermediate[{i}].qp"), im.query_paths.clone()));
        }
        ranges.push(("whir.ood".to_string(), layout.whir.ood_samples.clone()));
        ranges.push((
            "whir.sumcheck_polys".to_string(),
            layout.whir.sumcheck_polys.clone(),
        ));
        ranges.push((
            "whir.pow_nonces".to_string(),
            layout.whir.pow_nonces.clone(),
        ));
        ranges.push((
            "whir.final_monomials".to_string(),
            layout.whir.final_monomials.clone(),
        ));

        // Every field start is FIELD_ALIGN-aligned.
        for (name, r) in &ranges {
            assert_eq!(r.start % FIELD_ALIGN, 0, "field `{name}` start not aligned");
            assert!(r.end <= layout.total_bytes);
        }
        // Non-overlap (sort by start, ensure no previous end > current start).
        let mut sorted = ranges.clone();
        sorted.sort_by_key(|(_, r)| r.start);
        for pair in sorted.windows(2) {
            let (a_name, a_r) = &pair[0];
            let (b_name, b_r) = &pair[1];
            assert!(
                a_r.end <= b_r.start,
                "overlap: `{a_name}` ends at {}, `{b_name}` starts at {}",
                a_r.end,
                b_r.start
            );
        }

        // Total bytes is itself FIELD_ALIGN-aligned.
        assert_eq!(layout.total_bytes % FIELD_ALIGN, 0);
        assert!(layout.total_bytes > 0);
    }

    #[test]
    fn backward_range_sizes_match_inputs() {
        let inputs = sample_inputs();
        let layout = ProofLayout::new(&inputs);

        for (dims, laid) in inputs.backward_layers.iter().zip(layout.backward.iter()) {
            assert_eq!(laid.layer_idx, dims.layer_idx);
            assert_eq!(laid.sumcheck_num_rounds, dims.sumcheck_num_rounds);
            let internal_len = dims.sumcheck_num_rounds.saturating_sub(1) * 4;
            assert_eq!(
                laid.internal_round_coefficients.end - laid.internal_round_coefficients.start,
                internal_len * size_of::<E4>()
            );
            let final_len = dims.final_step_eval_addresses.len() * dims.final_step_eval_degree;
            assert_eq!(
                laid.final_step_evaluations.end - laid.final_step_evaluations.start,
                final_len * size_of::<E4>()
            );
            // 1 E4 per orphan address.
            let extra_len = dims.extra_evaluations_addresses.len();
            assert_eq!(
                laid.extra_evaluations.end - laid.extra_evaluations.start,
                extra_len * size_of::<E4>()
            );
            assert_eq!(
                laid.extra_evaluations_addresses,
                dims.extra_evaluations_addresses,
            );
        }
    }

    #[test]
    fn whir_range_sizes_match_inputs() {
        let inputs = sample_inputs();
        let layout = ProofLayout::new(&inputs);

        let check_base = |dims: &WhirBaseLayerDims, laid: &WhirBaseLayerByteLayout| {
            assert_eq!(
                laid.cap.end - laid.cap.start,
                dims.cap_digest_count * DIGEST_U32_WORDS * size_of::<u32>()
            );
            assert_eq!(
                laid.evals.end - laid.evals.start,
                dims.num_columns * size_of::<E4>()
            );
            assert_eq!(
                laid.query_indices.end - laid.query_indices.start,
                dims.query_count * size_of::<u32>()
            );
            assert_eq!(
                laid.query_leaves.end - laid.query_leaves.start,
                dims.query_count * dims.leaf_values_len * size_of::<BF>()
            );
            assert_eq!(
                laid.query_paths.end - laid.query_paths.start,
                dims.query_count * dims.path_len * DIGEST_U32_WORDS * size_of::<u32>()
            );
        };
        check_base(&inputs.whir.setup, &layout.whir.setup);
        check_base(&inputs.whir.memory, &layout.whir.memory);
        check_base(&inputs.whir.witness, &layout.whir.witness);

        for (dims, laid) in inputs
            .whir
            .intermediate
            .iter()
            .zip(layout.whir.intermediate.iter())
        {
            assert_eq!(
                laid.cap.end - laid.cap.start,
                dims.cap_digest_count * DIGEST_U32_WORDS * size_of::<u32>()
            );
            assert_eq!(
                laid.query_indices.end - laid.query_indices.start,
                dims.query_count * size_of::<u32>()
            );
            assert_eq!(
                laid.query_leaves.end - laid.query_leaves.start,
                dims.query_count * dims.leaf_values_len * size_of::<E4>()
            );
            assert_eq!(
                laid.query_paths.end - laid.query_paths.start,
                dims.query_count * dims.path_len * DIGEST_U32_WORDS * size_of::<u32>()
            );
        }

        assert_eq!(
            layout.whir.ood_samples.end - layout.whir.ood_samples.start,
            inputs.whir.num_ood_samples * size_of::<E4>()
        );
        assert_eq!(
            layout.whir.sumcheck_polys.end - layout.whir.sumcheck_polys.start,
            inputs.whir.total_sumcheck_polys * 3 * size_of::<E4>()
        );
        assert_eq!(
            layout.whir.pow_nonces.end - layout.whir.pow_nonces.start,
            inputs.whir.pow_rounds * size_of::<u64>()
        );
        assert_eq!(
            layout.whir.final_monomials.end - layout.whir.final_monomials.start,
            inputs.whir.final_monomials_len * size_of::<E4>()
        );
    }

    #[test]
    fn typed_accessors_match_ranges() {
        let inputs = sample_inputs();
        let layout = ProofLayout::new(&inputs);
        let mut slab = vec![0u8; layout.total_bytes];
        // align the test buffer to 16B by taking the offset into a larger Vec —
        // in production the device allocator guarantees alignment.
        let (_, typed, _) = unsafe { slab.align_to::<u128>() };
        assert!(!typed.is_empty(), "test buffer must be 16-byte aligned");

        // Round-trip: write via device pointer view, read via host slice view.
        let slab_ptr = slab.as_mut_ptr();
        for (i, bw_layout) in layout.backward.iter().enumerate() {
            unsafe {
                let (ptr, len) = layout.backward_final_step_evals_device_mut(slab_ptr, i);
                assert_eq!(
                    ptr as *const u8 as usize,
                    slab_ptr as usize + bw_layout.final_step_evaluations.start
                );
                assert_eq!(
                    len * size_of::<E4>(),
                    bw_layout.final_step_evaluations.end - bw_layout.final_step_evaluations.start
                );
                let (extra_ptr, extra_len) =
                    layout.backward_extra_evaluations_device_mut(slab_ptr, i);
                assert_eq!(
                    extra_ptr as *const u8 as usize,
                    slab_ptr as usize + bw_layout.extra_evaluations.start
                );
                assert_eq!(
                    extra_len * size_of::<E4>(),
                    bw_layout.extra_evaluations.end - bw_layout.extra_evaluations.start
                );
                assert_eq!(extra_len, bw_layout.extra_evaluations_addresses.len());
            }
            let host = layout.backward_final_step_evals_host(&slab, i);
            assert_eq!(
                host.len() * size_of::<E4>(),
                bw_layout.final_step_evaluations.end - bw_layout.final_step_evaluations.start
            );
            let extra_host = layout.backward_extra_evaluations_host(&slab, i);
            assert_eq!(
                extra_host.len() * size_of::<E4>(),
                bw_layout.extra_evaluations.end - bw_layout.extra_evaluations.start,
            );
        }
    }

    #[test]
    fn parser_round_trips_extra_evaluations() {
        let inputs = sample_inputs();
        let layout = ProofLayout::new(&inputs);

        // Layer 0 has 2 orphan addresses (per `sample_inputs`). Write
        // recognizable values into the slab's `extra_evaluations` range
        // for layer-slot 1 (= main layer, the second slot here), then
        // run the parser and assert the BTreeMap has the expected keys
        // and values.
        let mut slab = vec![0u8; layout.total_bytes];
        let layer_slot = 1usize;
        let bw = &layout.backward[layer_slot];
        assert_eq!(bw.extra_evaluations_addresses.len(), 2);

        // Write `[E4::from_limbs([1,0,0,0]), E4::from_limbs([2,0,0,0])]`
        // into the slab via the device-side accessor (we have a host
        // pointer here but the call shape matches production usage).
        let slab_ptr = slab.as_mut_ptr();
        unsafe {
            let (ptr, len) = layout.backward_extra_evaluations_device_mut(slab_ptr, layer_slot);
            assert_eq!(len, 2);
            let written: [E4; 2] = [
                E4::from_base(BF::from_u32_unchecked(1)),
                E4::from_base(BF::from_u32_unchecked(2)),
            ];
            std::ptr::copy_nonoverlapping(written.as_ptr(), ptr, 2);
        }

        let parsed = layout.parse_sumcheck_intermediate_values(&slab, BTreeMap::new());
        let layer_idx = inputs.backward_layers[layer_slot].layer_idx;
        let intermediate = parsed.get(&layer_idx).expect("layer slot in parsed map");
        assert_eq!(
            intermediate.extra_evaluations_from_caching_relations.len(),
            2,
        );
        let by_addr: Vec<_> = intermediate
            .extra_evaluations_from_caching_relations
            .iter()
            .collect();
        // BTreeMap iteration follows GKRAddress's `Ord`: InnerLayer < ScratchSpace.
        assert_eq!(
            *by_addr[0].0,
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 0,
            }
        );
        assert_eq!(*by_addr[1].0, GKRAddress::ScratchSpace(7));
        // `extras_flat[0] = 1` was written under the address at slab
        // index 0 = InnerLayer{1, 0}, `extras_flat[1] = 2` under
        // ScratchSpace(7). The map preserves those associations.
        assert_eq!(*by_addr[0].1, E4::from_base(BF::from_u32_unchecked(1)));
        assert_eq!(*by_addr[1].1, E4::from_base(BF::from_u32_unchecked(2)));
    }
}
