//! Device-resident proof image — single `u8` slab layout.
//!
//! See `docs/gpu_scheduling_contract.md` and the iterative-knitting-bumblebee
//! plan. The intent is that every proof field produced on device lands in one
//! contiguous `DeviceAllocation<u8>` (the proof slab); one terminal D2H copies
//! the slab to pinned host memory; a single host parse over the slab emits the
//! final `GKRProof`.
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
use std::mem::size_of;
use std::ops::Range;

use cs::definitions::GKRAddress;
use cs::gkr_compiler::OutputType;

use crate::field::{BF, E4};

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
    /// Addresses for `extra_evaluations_from_caching_relations`, stable order.
    /// Each entry contributes one `E4`. Empty for dim-reducing layers.
    pub(crate) extra_eval_addresses: Vec<GKRAddress>,
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
    /// `extra_evaluations_from_caching_relations` flat array — one `E4` per
    /// entry in `extra_eval_addresses`.
    pub(crate) extra_evaluations: Range<usize>,
    /// Copies of the address ordering, retained for parse-time `BTreeMap`
    /// reconstruction.
    pub(crate) final_step_eval_addresses: Vec<GKRAddress>,
    pub(crate) extra_eval_addresses: Vec<GKRAddress>,
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

impl ProofLayout {
    pub(crate) fn new(inputs: &ProofLayoutInputs) -> Self {
        let mut cur = 0usize;

        let mut alloc = |cur: &mut usize, count: usize, elem_size: usize| -> Range<usize> {
            let start = align_up(*cur, FIELD_ALIGN);
            let end = start + count * elem_size;
            *cur = end;
            start..end
        };

        // final_explicit_evaluations, BTreeMap key order (BTreeMap iterates in
        // key order, matching what the parse will emit).
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
            let internal_round_coefficients =
                alloc(&mut cur, internal_count * 4, size_of::<E4>());
            let final_evals_count =
                layer.final_step_eval_addresses.len() * layer.final_step_eval_degree;
            let final_step_evaluations = alloc(&mut cur, final_evals_count, size_of::<E4>());
            let extra_count = layer.extra_eval_addresses.len();
            let extra_evaluations = alloc(&mut cur, extra_count, size_of::<E4>());
            backward.push(BackwardLayerLayout {
                layer_idx: layer.layer_idx,
                internal_round_coefficients,
                final_step_evaluations,
                extra_evaluations,
                final_step_eval_addresses: layer.final_step_eval_addresses.clone(),
                extra_eval_addresses: layer.extra_eval_addresses.clone(),
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
            let query_leaves =
                alloc(cur, d.query_count * d.leaf_values_len, size_of::<BF>());
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

        let lay_intermediate = |cur: &mut usize, d: &WhirIntermediateDims| -> WhirIntermediateByteLayout {
            let cap = alloc(cur, d.cap_digest_count * DIGEST_U32_WORDS, size_of::<u32>());
            let query_indices = alloc(cur, d.query_count, size_of::<u32>());
            let query_leaves =
                alloc(cur, d.query_count * d.leaf_values_len, size_of::<E4>());
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

    pub(crate) unsafe fn output_evaluations_read_device_mut(
        &self,
        slab_base: *mut u8,
        output_type: OutputType,
    ) -> (*mut E4, usize) {
        let layout = self
            .output_evaluations
            .get(&output_type)
            .expect("unknown OutputType in slab layout");
        Self::device_typed::<E4>(slab_base, &layout.read_set)
    }

    pub(crate) unsafe fn output_evaluations_write_device_mut(
        &self,
        slab_base: *mut u8,
        output_type: OutputType,
    ) -> (*mut E4, usize) {
        let layout = self
            .output_evaluations
            .get(&output_type)
            .expect("unknown OutputType in slab layout");
        Self::device_typed::<E4>(slab_base, &layout.write_set)
    }

    pub(crate) unsafe fn backward_internal_coeffs_device_mut(
        &self,
        slab_base: *mut u8,
        layer_slot: usize,
    ) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.backward[layer_slot].internal_round_coefficients)
    }

    pub(crate) unsafe fn backward_final_step_evals_device_mut(
        &self,
        slab_base: *mut u8,
        layer_slot: usize,
    ) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.backward[layer_slot].final_step_evaluations)
    }

    pub(crate) unsafe fn backward_extra_evals_device_mut(
        &self,
        slab_base: *mut u8,
        layer_slot: usize,
    ) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.backward[layer_slot].extra_evaluations)
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

    pub(crate) fn backward_extra_evals_host<'a>(
        &self,
        slab: &'a [u8],
        layer_slot: usize,
    ) -> &'a [E4] {
        Self::host_typed::<E4>(slab, &self.backward[layer_slot].extra_evaluations)
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

    pub(crate) fn whir_intermediate_cap_host<'a>(
        &self,
        slab: &'a [u8],
        round: usize,
    ) -> &'a [u32] {
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

    fn sample_inputs() -> ProofLayoutInputs {
        let mut output_evaluations = BTreeMap::new();
        output_evaluations.insert(OutputType::PermutationProduct, [2usize, 2usize]);
        output_evaluations.insert(OutputType::Lookup16Bits, [1usize, 1usize]);

        let backward_layers = vec![
            BackwardLayerDims {
                layer_idx: 8,
                sumcheck_num_rounds: 3,
                final_step_eval_addresses: vec![GKRAddress::BaseLayerWitness(0); 2],
                final_step_eval_degree: 4,
                extra_eval_addresses: vec![],
            },
            BackwardLayerDims {
                layer_idx: 0,
                sumcheck_num_rounds: 5,
                final_step_eval_addresses: vec![GKRAddress::BaseLayerWitness(0); 3],
                final_step_eval_degree: 2,
                extra_eval_addresses: vec![GKRAddress::BaseLayerWitness(1); 1],
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
            ranges.push((
                format!("backward[{}].extra", bw.layer_idx),
                bw.extra_evaluations.clone(),
            ));
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
            ranges.push((format!("whir.intermediate[{i}].qi"), im.query_indices.clone()));
            ranges.push((format!("whir.intermediate[{i}].ql"), im.query_leaves.clone()));
            ranges.push((format!("whir.intermediate[{i}].qp"), im.query_paths.clone()));
        }
        ranges.push(("whir.ood".to_string(), layout.whir.ood_samples.clone()));
        ranges.push((
            "whir.sumcheck_polys".to_string(),
            layout.whir.sumcheck_polys.clone(),
        ));
        ranges.push(("whir.pow_nonces".to_string(), layout.whir.pow_nonces.clone()));
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
            let extra_len = dims.extra_eval_addresses.len();
            assert_eq!(
                laid.extra_evaluations.end - laid.extra_evaluations.start,
                extra_len * size_of::<E4>()
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
                assert_eq!(ptr as *const u8 as usize, slab_ptr as usize + bw_layout.final_step_evaluations.start);
                assert_eq!(len * size_of::<E4>(), bw_layout.final_step_evaluations.end - bw_layout.final_step_evaluations.start);
            }
            let host = layout.backward_final_step_evals_host(&slab, i);
            assert_eq!(host.len() * size_of::<E4>(), bw_layout.final_step_evaluations.end - bw_layout.final_step_evaluations.start);
        }
    }
}
