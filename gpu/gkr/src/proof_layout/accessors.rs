use std::collections::BTreeMap;
use std::marker::PhantomData;
use std::mem::size_of;
use std::ops::Range;

use super::*;
use crate::upstream::Field;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WhirBaseLayerKind {
    Setup,
    Memory,
    Witness,
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
// The slab pointer is assumed to be 32-byte aligned; `ProofLayout::new`
// guarantees every range's start is also 32-byte aligned so typed casts to any
// proof element type (including digest-typed regions consumed by 256-bit
// st.global.cs.v4.b64 stores) are valid.

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

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn backward_internal_coeffs_device_mut(
        &self,
        slab_base: *mut u8,
        layer_slot: usize,
    ) -> (*mut E4, usize) {
        Self::device_typed::<E4>(
            slab_base,
            &self.backward[layer_slot].internal_round_coefficients,
        )
    }

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn backward_final_step_evals_device_mut(
        &self,
        slab_base: *mut u8,
        layer_slot: usize,
    ) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.backward[layer_slot].final_step_evaluations)
    }

    /// Per-layer-slot `extra_evaluations` range. Returns `(ptr, addresses_len)`
    /// — one `E4` per missing cached dependency. Length is 0 for
    /// dim-reducing slots and main layers without extras.
    ///
    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn backward_extra_evaluations_device_mut(
        &self,
        slab_base: *mut u8,
        layer_slot: usize,
    ) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.backward[layer_slot].extra_evaluations)
    }

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn output_evaluations_device_mut(
        &self,
        slab_base: *mut u8,
    ) -> Option<(*mut E4, usize)> {
        let block = self.output_evaluations_block()?;
        Some(Self::device_typed::<E4>(slab_base, &block))
    }

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn whir_original_evaluation_point_device_mut(
        &self,
        slab_base: *mut u8,
    ) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.whir.original_evaluation_point)
    }

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn whir_batching_challenge_device_mut(
        &self,
        slab_base: *mut u8,
    ) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.whir.batching_challenge)
    }

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn whir_base_cap_device_mut(
        &self,
        slab_base: *mut u8,
        which: WhirBaseLayerKind,
    ) -> (*mut u32, usize) {
        Self::device_typed::<u32>(slab_base, &self.whir_base(which).cap)
    }

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn whir_base_evals_device_mut(
        &self,
        slab_base: *mut u8,
        which: WhirBaseLayerKind,
    ) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.whir_base(which).evals)
    }

    /// Shared base-oracle `query_indices` range. The three base oracles
    /// (setup/memory/witness) reuse a single slab range — see
    /// `WhirLayout::base_query_indices`.
    ///
    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn whir_base_query_indices_device_mut(
        &self,
        slab_base: *mut u8,
    ) -> (*mut u32, usize) {
        Self::device_typed::<u32>(slab_base, &self.whir.base_query_indices)
    }

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn whir_base_query_leaves_device_mut(
        &self,
        slab_base: *mut u8,
        which: WhirBaseLayerKind,
    ) -> (*mut BF, usize) {
        Self::device_typed::<BF>(slab_base, &self.whir_base(which).query_leaves)
    }

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn whir_base_query_paths_device_mut(
        &self,
        slab_base: *mut u8,
        which: WhirBaseLayerKind,
    ) -> (*mut u32, usize) {
        Self::device_typed::<u32>(slab_base, &self.whir_base(which).query_paths)
    }

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn whir_intermediate_cap_device_mut(
        &self,
        slab_base: *mut u8,
        round: usize,
    ) -> (*mut u32, usize) {
        Self::device_typed::<u32>(slab_base, &self.whir.intermediate[round].cap)
    }

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn whir_intermediate_query_indices_device_mut(
        &self,
        slab_base: *mut u8,
        round: usize,
    ) -> (*mut u32, usize) {
        Self::device_typed::<u32>(slab_base, &self.whir.intermediate[round].query_indices)
    }

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn whir_intermediate_query_leaves_device_mut(
        &self,
        slab_base: *mut u8,
        round: usize,
    ) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.whir.intermediate[round].query_leaves)
    }

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn whir_intermediate_query_paths_device_mut(
        &self,
        slab_base: *mut u8,
        round: usize,
    ) -> (*mut u32, usize) {
        Self::device_typed::<u32>(slab_base, &self.whir.intermediate[round].query_paths)
    }

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn whir_ood_samples_device_mut(&self, slab_base: *mut u8) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.whir.ood_samples)
    }

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn whir_sumcheck_polys_device_mut(&self, slab_base: *mut u8) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.whir.sumcheck_polys)
    }

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn whir_pow_nonces_device_mut(&self, slab_base: *mut u8) -> (*mut u64, usize) {
        Self::device_typed::<u64>(slab_base, &self.whir.pow_nonces)
    }

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn whir_final_monomials_device_mut(&self, slab_base: *mut u8) -> (*mut E4, usize) {
        Self::device_typed::<E4>(slab_base, &self.whir.final_monomials)
    }

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn lookup_pow_nonce_device_mut(&self, slab_base: *mut u8) -> (*mut u64, usize) {
        Self::device_typed::<u64>(slab_base, &self.lookup_pow_nonce)
    }

    /// # Safety
    /// `slab_base` must point into a live device allocation big enough for
    /// this layout (see the module-level safety note above); the returned
    /// pointer must not be dereferenced from host code.
    pub unsafe fn batched_proximity_pow_nonce_device_mut(
        &self,
        slab_base: *mut u8,
    ) -> (*mut u64, usize) {
        Self::device_typed::<u64>(slab_base, &self.batched_proximity_pow_nonce)
    }

    fn whir_base(&self, which: WhirBaseLayerKind) -> &WhirBaseLayerByteLayout {
        match which {
            WhirBaseLayerKind::Setup => &self.whir.setup,
            WhirBaseLayerKind::Memory => &self.whir.memory,
            WhirBaseLayerKind::Witness => &self.whir.witness,
        }
    }
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
    pub fn parse_final_explicit_evaluations(
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

    /// Parse every slab-resident WHIR proof field into a fresh
    /// `WhirPolyCommitProof`. Base-layer `queries` are populated directly
    /// from the slab — the gather kernels write `query_indices` /
    /// `query_leaves` / `query_paths` for each base oracle in
    /// row-major-per-query layout matching what the verifier consumes.
    pub fn parse_whir_proof(
        &self,
        slab: &[u8],
    ) -> WhirPolyCommitProof<BF, E4, DefaultTreeConstructor> {
        let digest_bytes_of = |bytes: &[u32]| -> Vec<[u32; DIGEST_U32_WORDS]> {
            bytes.as_chunks::<DIGEST_U32_WORDS>().0.to_vec()
        };
        // Shared across all three base oracles — the setup/memory/witness
        // oracles sample the same tree-space indices, so the slab stores one
        // copy. See `WhirLayout::base_query_indices`.
        let base_indices = self.whir_base_query_indices_host(slab);
        let base = |which: WhirBaseLayerKind,
                    indices: &[u32]|
         -> WhirBaseLayerCommitmentAndQueries<BF, E4, DefaultTreeConstructor> {
            let base_layout = self.whir_base(which);
            let cap = if base_layout.num_columns == 0 {
                Vec::new()
            } else {
                digest_bytes_of(self.whir_base_cap_host(slab, which))
            };
            let evals = self.whir_base_evals_host(slab, which).to_vec();
            let query_count = base_layout.query_count;
            let leaf_values_len = base_layout.leaf_values_len;
            let path_len = base_layout.path_len;
            let queries: Vec<BaseFieldQuery<BF, DefaultTreeConstructor>> =
                if query_count == 0 || base_layout.num_columns == 0 {
                    Vec::new()
                } else {
                    let leaves = self.whir_base_query_leaves_host(slab, which);
                    let paths_flat = self.whir_base_query_paths_host(slab, which);
                    (0..query_count)
                        .map(|q| {
                            let leaf_start = q * leaf_values_len;
                            let leaf_end = leaf_start + leaf_values_len;
                            let path_start_u32 = q * path_len * DIGEST_U32_WORDS;
                            let path_end_u32 = path_start_u32 + path_len * DIGEST_U32_WORDS;
                            BaseFieldQuery {
                                index: indices[q] as usize,
                                leaf_values_concatenated: leaves[leaf_start..leaf_end].to_vec(),
                                path: digest_bytes_of(&paths_flat[path_start_u32..path_end_u32]),
                                _marker: PhantomData,
                            }
                        })
                        .collect()
                };
            WhirBaseLayerCommitmentAndQueries {
                commitment: WhirCommitment {
                    cap: MerkleTreeCapVarLength { cap },
                    _marker: PhantomData,
                },
                num_columns: base_layout.num_columns,
                evals,
                queries,
            }
        };
        let setup_commitment = base(WhirBaseLayerKind::Setup, base_indices);
        let memory_commitment = base(WhirBaseLayerKind::Memory, base_indices);
        let witness_commitment = base(WhirBaseLayerKind::Witness, base_indices);
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
            .as_chunks::<3>()
            .0
            .to_vec();
        let original_evaluation_point = self.whir_original_evaluation_point_host(slab).to_vec();
        let batching_challenge = self.whir_batching_challenge_host(slab)[0];
        let [c0, c1, c2] = sumcheck_polys[0];
        let mut p_at_one = c0;
        p_at_one.add_assign(&c1);
        p_at_one.add_assign(&c2);
        let mut batched_opening = c0;
        batched_opening.add_assign(&p_at_one);
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
            whir_schedule: WhirSchedule::default(),
            batching_challenge: Some(batching_challenge),
            original_evaluation_point: Some(original_evaluation_point),
            batched_opening: Some(batched_opening),
        }
    }

    /// Parse `sumcheck_intermediate_values: BTreeMap<layer_idx, _>`
    /// from the D2H'd slab.
    ///
    /// `extra_evaluations_by_layer` is a sparse source whose
    /// values may come from slab-resident WHIR base-evaluation ranges
    /// (`DenseSource::read_from_slab`). For every layer-slot, the dedicated
    /// `extra_evaluations` slab range is also read when present: each entry is
    /// one `E4` per address, in `extra_evaluations_addresses` order. Both
    /// sources are merged into the same
    /// `extra_evaluations_from_caching_relations` BTreeMap on the resulting
    /// `SumcheckIntermediateProofValues`.
    pub fn parse_sumcheck_intermediate_values(
        &self,
        slab: &[u8],
        mut extra_evaluations_by_layer: BTreeMap<usize, BTreeMap<GKRAddress, E4>>,
    ) -> BTreeMap<usize, SumcheckIntermediateProofValues<BF, E4>> {
        let mut result = BTreeMap::new();
        for (layer_slot, bw) in self.backward.iter().enumerate() {
            let coeffs_flat = self.backward_internal_coeffs_host(slab, layer_slot);
            // `sumcheck_num_rounds` monomials.
            debug_assert_eq!(coeffs_flat.len(), bw.sumcheck_num_rounds * 4);
            let internal_round_coefficients: Vec<[E4; 4]> = coeffs_flat.as_chunks::<4>().0.to_vec();
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

    pub fn whir_original_evaluation_point_host<'a>(&self, slab: &'a [u8]) -> &'a [E4] {
        Self::host_typed::<E4>(slab, &self.whir.original_evaluation_point)
    }

    pub fn whir_batching_challenge_host<'a>(&self, slab: &'a [u8]) -> &'a [E4] {
        Self::host_typed::<E4>(slab, &self.whir.batching_challenge)
    }

    pub fn whir_base_cap_host<'a>(&self, slab: &'a [u8], which: WhirBaseLayerKind) -> &'a [u32] {
        Self::host_typed::<u32>(slab, &self.whir_base(which).cap)
    }

    pub fn whir_base_evals_host<'a>(&self, slab: &'a [u8], which: WhirBaseLayerKind) -> &'a [E4] {
        Self::host_typed::<E4>(slab, &self.whir_base(which).evals)
    }

    /// Shared base-oracle `query_indices` slice. The three base oracles
    /// (setup/memory/witness) reuse a single slab range — see
    /// `WhirLayout::base_query_indices`.
    pub fn whir_base_query_indices_host<'a>(&self, slab: &'a [u8]) -> &'a [u32] {
        Self::host_typed::<u32>(slab, &self.whir.base_query_indices)
    }

    pub fn whir_base_query_leaves_host<'a>(
        &self,
        slab: &'a [u8],
        which: WhirBaseLayerKind,
    ) -> &'a [BF] {
        Self::host_typed::<BF>(slab, &self.whir_base(which).query_leaves)
    }

    pub fn whir_base_query_paths_host<'a>(
        &self,
        slab: &'a [u8],
        which: WhirBaseLayerKind,
    ) -> &'a [u32] {
        Self::host_typed::<u32>(slab, &self.whir_base(which).query_paths)
    }

    pub fn whir_intermediate_cap_host<'a>(&self, slab: &'a [u8], round: usize) -> &'a [u32] {
        Self::host_typed::<u32>(slab, &self.whir.intermediate[round].cap)
    }

    pub fn whir_intermediate_query_indices_host<'a>(
        &self,
        slab: &'a [u8],
        round: usize,
    ) -> &'a [u32] {
        Self::host_typed::<u32>(slab, &self.whir.intermediate[round].query_indices)
    }

    pub fn whir_intermediate_query_leaves_host<'a>(
        &self,
        slab: &'a [u8],
        round: usize,
    ) -> &'a [E4] {
        Self::host_typed::<E4>(slab, &self.whir.intermediate[round].query_leaves)
    }

    pub fn whir_intermediate_query_paths_host<'a>(
        &self,
        slab: &'a [u8],
        round: usize,
    ) -> &'a [u32] {
        Self::host_typed::<u32>(slab, &self.whir.intermediate[round].query_paths)
    }

    pub fn whir_ood_samples_host<'a>(&self, slab: &'a [u8]) -> &'a [E4] {
        Self::host_typed::<E4>(slab, &self.whir.ood_samples)
    }

    pub fn whir_sumcheck_polys_host<'a>(&self, slab: &'a [u8]) -> &'a [E4] {
        Self::host_typed::<E4>(slab, &self.whir.sumcheck_polys)
    }

    pub fn whir_pow_nonces_host<'a>(&self, slab: &'a [u8]) -> &'a [u64] {
        Self::host_typed::<u64>(slab, &self.whir.pow_nonces)
    }

    pub fn whir_final_monomials_host<'a>(&self, slab: &'a [u8]) -> &'a [E4] {
        Self::host_typed::<E4>(slab, &self.whir.final_monomials)
    }

    pub fn lookup_pow_nonce_host(&self, slab: &[u8]) -> u64 {
        Self::host_typed::<u64>(slab, &self.lookup_pow_nonce)[0]
    }

    pub fn batched_proximity_pow_nonce_host(&self, slab: &[u8]) -> u64 {
        Self::host_typed::<u64>(slab, &self.batched_proximity_pow_nonce)[0]
    }
}
