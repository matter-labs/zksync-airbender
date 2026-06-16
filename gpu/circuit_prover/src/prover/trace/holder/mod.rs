use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
#[cfg(test)]
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use crate::allocator::tracker::AllocationPlacement;
#[cfg(test)]
use crate::ops::blake2s::build_merkle_tree;
use crate::ops::blake2s::{
    build_merkle_tree_multi_coset, build_merkle_tree_nodes_multi_coset_from_external_src,
    gather_tree_caps_inline, Digest,
};
#[cfg(test)]
use crate::ops::blake2s::{
    gather_leaf_rows, gather_merkle_paths_device, gather_merkle_paths_from_rows,
};
use crate::ops::ntt::{
    bitreversed_monomials_to_natural_evals_multi_coset,
    bitreversed_monomials_to_natural_evals_multi_coset_with_coset_range,
    hypercube_x1_msb_evals_to_x1_msb_monomials, log_size_supports_transposed_monomials,
    transform_whir_leaves_from_ntt_in_place_multi_coset,
};
use crate::primitives::context::DeviceAllocation;
#[cfg(test)]
use crate::primitives::context::HostAllocation;
#[cfg(test)]
use crate::primitives::device_structures::DeviceMatrix;
use crate::primitives::device_structures::{
    DeviceMatrixChunk, DeviceMatrixImpl, DeviceMatrixMut, DeviceMatrixMutImpl,
};
use crate::primitives::field::{BF, E4};
use crate::prover::ProverContext;
use crate::upstream::FieldExtension;

pub(crate) const PARTIAL_TREE_REDUCTION_LAYERS: u32 = crate::primitives::utils::LOG_WARP_SIZE;

const EXT4_DEGREE: usize = <E4 as FieldExtension<BF>>::DEGREE;

#[derive(Copy, Clone)]
pub(crate) enum TreesCacheMode {
    CacheNone,
    CachePartial,
    CacheFull,
}

pub(crate) enum CosetsHolder<T> {
    Full(DeviceAllocation<T>),
    None(std::marker::PhantomData<T>),
}

pub(crate) enum TreesHolder {
    Full(DeviceAllocation<Digest>),
    Partial(DeviceAllocation<Digest>),
    None,
}

#[cfg(test)]
pub(crate) struct LeafsAndMerklePaths {
    pub leafs: HostAllocation<[BF]>,
    pub merkle_paths: HostAllocation<[Digest]>,
}

pub(crate) struct TraceHolder<T> {
    pub(crate) log_domain_size: u32,
    pub(crate) log_lde_factor: u32,
    pub(crate) log_rows_per_leaf: u32,
    pub(crate) log_tree_cap_size: u32,
    pub(crate) columns_count: usize,
    raw_hypercube_evals: std::sync::Arc<DeviceAllocation<T>>,
    cosets_materialized: bool,
    pub(crate) cosets: CosetsHolder<T>,
    pub(crate) trees: TreesHolder,
    /// Device-resident, contiguous Merkle cap of length `1 << log_tree_cap_size`,
    /// laid out in canonical bit-reversed coset order (`stage1_pos = 0..lde_factor`,
    /// reading from `coset[bitreverse(stage1_pos)]`). Populated by `commit_all`
    /// (or by a pre-prove H2D from a precomputed host source for the setup/memory
    /// holders that bypass `commit_all`).
    pub(crate) unified_device_cap: Option<DeviceAllocation<Digest>>,
}

impl<T> TraceHolder<T> {
    pub(crate) fn new(
        log_domain_size: u32,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
        columns_count: usize,
        trees_cache_mode: TreesCacheMode,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let instances_count = 1usize << log_lde_factor;
        let raw_hypercube_evals = std::sync::Arc::new(context.alloc(
            columns_count << log_domain_size,
            AllocationPlacement::Bottom,
        )?);
        let cosets = CosetsHolder::Full(allocate_cosets(
            instances_count,
            log_domain_size,
            columns_count,
            context,
        )?);
        let trees = match trees_cache_mode {
            TreesCacheMode::CacheNone => TreesHolder::None,
            TreesCacheMode::CachePartial => TreesHolder::Partial(allocate_trees(
                instances_count,
                log_domain_size - PARTIAL_TREE_REDUCTION_LAYERS,
                log_rows_per_leaf,
                context,
            )?),
            TreesCacheMode::CacheFull => TreesHolder::Full(allocate_trees(
                instances_count,
                log_domain_size,
                log_rows_per_leaf,
                context,
            )?),
        };
        Ok(Self {
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            raw_hypercube_evals,
            cosets_materialized: false,
            cosets,
            trees,
            unified_device_cap: None,
        })
    }

    /// Creates a trace holder that allocates only the hypercube evaluation buffer and
    /// (optionally) tree storage, but defers coset allocation until `ensure_cosets_materialized`.
    pub(crate) fn new_without_cosets(
        log_domain_size: u32,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
        columns_count: usize,
        trees_cache_mode: TreesCacheMode,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let instances_count = 1usize << log_lde_factor;
        let raw_hypercube_evals = std::sync::Arc::new(context.alloc(
            columns_count << log_domain_size,
            AllocationPlacement::Bottom,
        )?);
        let trees = match trees_cache_mode {
            TreesCacheMode::CacheNone => TreesHolder::None,
            TreesCacheMode::CachePartial => TreesHolder::Partial(allocate_trees(
                instances_count,
                log_domain_size - PARTIAL_TREE_REDUCTION_LAYERS,
                log_rows_per_leaf,
                context,
            )?),
            TreesCacheMode::CacheFull => TreesHolder::Full(allocate_trees(
                instances_count,
                log_domain_size,
                log_rows_per_leaf,
                context,
            )?),
        };
        Ok(Self {
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            raw_hypercube_evals,
            cosets_materialized: false,
            cosets: CosetsHolder::None(std::marker::PhantomData),
            trees,
            unified_device_cap: None,
        })
    }

    /// Returns the device-resident unified Merkle cap. Populated by `commit_all`
    /// or by a pre-prove H2D from a precomputed host source.
    pub(crate) fn unified_device_cap(&self) -> &DeviceAllocation<Digest> {
        self.unified_device_cap
            .as_ref()
            .expect("unified device cap must be materialized before access")
    }

    pub(crate) fn get_hypercube_evals(&self) -> &DeviceSlice<T> {
        self.raw_hypercube_evals.as_ref()
    }

    pub(crate) fn get_uninit_hypercube_evals_mut(&mut self) -> &mut DeviceSlice<T> {
        self.cosets_materialized = false;
        std::sync::Arc::get_mut(&mut self.raw_hypercube_evals)
            .expect("raw hypercube allocation must not be shared while being initialized")
    }

    pub(crate) fn raw_hypercube_backing(&self) -> std::sync::Arc<DeviceAllocation<T>> {
        std::sync::Arc::clone(&self.raw_hypercube_evals)
    }

    pub(crate) fn are_cosets_materialized(&self) -> bool {
        self.cosets_materialized
    }

    pub(crate) fn mark_cosets_materialized(&mut self) {
        self.cosets_materialized = true;
    }

    pub(crate) fn get_coset_evaluations(&self, coset_index: usize) -> &DeviceSlice<T> {
        assert!(coset_index < (1usize << self.log_lde_factor));
        assert!(
            self.cosets_materialized,
            "coset evaluations must be materialized before access"
        );
        match &self.cosets {
            CosetsHolder::Full(backing) => {
                let stride = self.columns_count << self.log_domain_size;
                &backing[coset_index * stride..(coset_index + 1) * stride]
            }
            CosetsHolder::None(_) => {
                panic!("cosets not allocated — call ensure_cosets_materialized first")
            }
        }
    }

    // /// Mutable shared-borrow of the full `CosetsHolder::Full` backing, intended
    // /// for callers that fill all cosets in one shot (multi-coset NTT writing
    // /// directly into the cosets backing). Asserts `!self.cosets_materialized`;
    // /// the caller is responsible for calling `mark_cosets_materialized` once the
    // /// fill completes.
    // pub(crate) fn get_uninit_consolidated_cosets_mut(&mut self) -> &mut DeviceSlice<T> {
    //     assert!(
    //         !self.cosets_materialized,
    //         "get_uninit_consolidated_cosets_mut: cosets already materialized"
    //     );
    //     match &mut self.cosets {
    //         CosetsHolder::Full(backing) => backing,
    //         CosetsHolder::None(_) => {
    //             panic!("cosets not allocated — call ensure_cosets_materialized first")
    //         }
    //     }
    // }

    pub(crate) fn get_evaluations(&self) -> &DeviceSlice<T> {
        self.get_coset_evaluations(0)
    }

    /// Returns the single consolidated cosets backing as one device slice in
    /// coset-major order: `backing[coset_index * stride .. (coset_index + 1) * stride]`
    /// is the slice for coset `coset_index`, where `stride = columns_count << log_domain_size`.
    pub(crate) fn get_consolidated_cosets(&self) -> &DeviceSlice<T> {
        match &self.cosets {
            CosetsHolder::Full(backing) => backing,
            CosetsHolder::None(_) => {
                panic!("cosets not allocated — call ensure_cosets_materialized first")
            }
        }
    }

    /// Returns per-coset segment length in digests for the current trees variant.
    /// `None` if no trees are allocated.
    fn per_coset_tree_len(&self) -> Option<usize> {
        match &self.trees {
            TreesHolder::Full(_) => {
                Some(1usize << (self.log_domain_size + 1 - self.log_rows_per_leaf))
            }
            TreesHolder::Partial(_) => {
                let partial_log_domain = self.log_domain_size - PARTIAL_TREE_REDUCTION_LAYERS;
                Some(1usize << (partial_log_domain + 1 - self.log_rows_per_leaf))
            }
            TreesHolder::None => None,
        }
    }

    pub(crate) fn get_uninit_tree_mut(
        &mut self,
        coset_index: usize,
    ) -> Option<&mut DeviceSlice<Digest>> {
        assert!(coset_index < (1usize << self.log_lde_factor));
        let per_coset = self.per_coset_tree_len()?;
        match &mut self.trees {
            TreesHolder::Full(backing) | TreesHolder::Partial(backing) => {
                Some(&mut backing[coset_index * per_coset..(coset_index + 1) * per_coset])
            }
            TreesHolder::None => None,
        }
    }

    /// Shared-borrow per-coset tree slice. Returns the subrange of the
    /// consolidated tree backing belonging to `coset_index`, or `None` if
    /// trees aren't allocated.
    #[cfg(test)]
    pub(crate) fn get_tree_slice(&self, coset_index: usize) -> Option<&DeviceSlice<Digest>> {
        assert!(coset_index < (1usize << self.log_lde_factor));
        let per_coset = self.per_coset_tree_len()?;
        match &self.trees {
            TreesHolder::Full(backing) | TreesHolder::Partial(backing) => {
                Some(&backing[coset_index * per_coset..(coset_index + 1) * per_coset])
            }
            TreesHolder::None => None,
        }
    }

    /// Returns the single consolidated tree backing as one device slice in
    /// coset-major order. `None` if trees aren't allocated.
    pub(crate) fn get_consolidated_tree(&self) -> Option<&DeviceSlice<Digest>> {
        match &self.trees {
            TreesHolder::Full(backing) | TreesHolder::Partial(backing) => Some(backing),
            TreesHolder::None => None,
        }
    }
}

impl TraceHolder<BF> {
    pub(crate) fn materialize_cosets_from_owned_hypercube(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let source = self.raw_hypercube_backing();
        let domain_size = 1usize << self.log_domain_size;

        let mut coeff_scratch = context.alloc(domain_size, AllocationPlacement::BestFit)?;
        let stream = context.get_exec_stream();
        let ntt_ctx = context.ntt_device_context();
        // The base-trace LDE log_domain_size is typically > 13 (→ compact /
        // two-pass-compact, NO DIT, scratch unused), but allocate a pooled
        // d-table scratch (len >= N) for the in-range case to keep the DIT path
        // enqueue-only per the GPU scheduling contract. Avoid a multi-MB unused
        // buffer for the large-log_n compact path by allocating only when in
        // range; the handle outlives all per-column launches below.
        let mut d_scratch;
        let mut scratch_opt = if (self.log_domain_size as usize) <= 13 {
            d_scratch = context.alloc::<BF>(domain_size, AllocationPlacement::BestFit)?;
            Some(&mut d_scratch[..])
        } else {
            None
        };
        let use_transposed_monomials =
            log_size_supports_transposed_monomials(self.log_domain_size as usize);
        for column in 0..self.columns_count {
            let offset = column * domain_size;
            let source_column = &source[offset..offset + domain_size];
            hypercube_x1_msb_evals_to_x1_msb_monomials(
                source_column,
                &mut coeff_scratch[0..domain_size],
                self.log_domain_size as usize,
                use_transposed_monomials,
                stream,
                context.get_device_properties(),
            )?;

            match &mut self.cosets {
                CosetsHolder::Full(backing) => {
                    // CosetsHolder::Full layout: [coset][col][trace_len], stride
                    // between cosets = columns_count * domain_size. The
                    // multi-coset NTT slices the backing at the current
                    // column's position and uses num_cols_per_coset_stride =
                    // columns_count to write each coset's slab in one launch,
                    // replacing the per-coset NTT loop.
                    let monomials = DeviceMatrixChunk::new(
                        &coeff_scratch[0..domain_size],
                        domain_size,
                        0,
                        domain_size,
                    );
                    let backing_from_col = &mut backing[offset..];
                    bitreversed_monomials_to_natural_evals_multi_coset(
                        &monomials,
                        backing_from_col,
                        self.log_domain_size as usize,
                        self.log_lde_factor as usize,
                        self.columns_count,
                        use_transposed_monomials,
                        ntt_ctx,
                        scratch_opt.as_deref_mut(),
                        stream,
                        context.get_device_properties(),
                    )?;
                }
                CosetsHolder::None(_) => {
                    panic!("cosets not allocated — call ensure_cosets_materialized first")
                }
            }
        }
        self.cosets_materialized = true;
        Ok(())
    }

    pub(crate) fn ensure_cosets_materialized(&mut self, context: &ProverContext) -> CudaResult<()> {
        if !self.cosets_materialized {
            if matches!(&self.cosets, CosetsHolder::None(_)) {
                let instances_count = 1usize << self.log_lde_factor;
                self.cosets = CosetsHolder::Full(allocate_cosets(
                    instances_count,
                    self.log_domain_size,
                    self.columns_count,
                    context,
                )?);
            }
            self.materialize_cosets_from_owned_hypercube(context)?;
        }
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn materialize_from_hypercube_evals(
        &mut self,
        source: &DeviceSlice<BF>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let domain_size = 1usize << self.log_domain_size;
        assert_eq!(source.len(), self.columns_count * domain_size);
        memory_copy_async(
            self.get_uninit_hypercube_evals_mut(),
            source,
            context.get_exec_stream(),
        )?;
        self.materialize_cosets_from_owned_hypercube(context)
    }

    /// Schedules the per-coset Merkle commits and the inline gather kernel,
    /// writing the unified Merkle cap (in canonical bit-reversed coset order)
    /// directly into a caller-supplied `dst_u32` device slice. No allocation
    /// of `self.unified_device_cap` is performed here — callers that still
    /// own a private cap buffer should use `commit_all`, which wraps this
    /// function with the legacy allocation behavior.
    pub(crate) fn commit_all_into(
        &mut self,
        dst_u32: &mut DeviceSlice<u32>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        self.ensure_cosets_materialized(context)?;
        let lde_factor = 1usize << self.log_lde_factor;
        let log_subtree_cap_size = self.log_tree_cap_size - self.log_lde_factor;
        let per_coset_cap_size = 1usize << log_subtree_cap_size;
        let cap_size = 1usize << self.log_tree_cap_size;
        let cap_words_per_coset = (per_coset_cap_size * BLAKE2S_DIGEST_SIZE_U32_WORDS) as u32;
        assert_eq!(
            dst_u32.len(),
            cap_size * BLAKE2S_DIGEST_SIZE_U32_WORDS,
            "commit_all_into dst_u32 length must match cap_size * DIGEST_U32_WORDS",
        );

        let log_domain_size = self.log_domain_size;
        let log_lde_factor = self.log_lde_factor;
        let log_rows_per_leaf = self.log_rows_per_leaf;
        let log_tree_cap_size = self.log_tree_cap_size;
        let columns_count = self.columns_count;
        let stream = context.get_exec_stream();

        let per_coset_tree_full_len = 1usize << (log_domain_size + 1 - log_rows_per_leaf);
        let per_coset_tree_partial_len =
            self.per_coset_tree_len().unwrap_or(per_coset_tree_full_len);

        // Snapshot the cosets backing as a raw pointer to dodge the
        // simultaneous `&self.cosets` + `&mut self.trees` borrow inside the
        // per-coset commit loop. SAFETY: cosets and trees backings are
        // disjoint device allocations; evaluations are only read.
        let evals_stride = columns_count << log_domain_size;
        let evals_ptr = match &self.cosets {
            CosetsHolder::Full(backing) => backing.as_ptr(),
            CosetsHolder::None(_) => {
                panic!("cosets not allocated — call ensure_cosets_materialized first")
            }
        };

        // Multi-coset commit: every coset's Merkle tree is built layer-by-layer
        // across all cosets in one launch per layer (was `lde_factor * layers`
        // launches in a per-coset loop). For `Partial`/`None` modes we
        // allocate one transient `tree_tops` slab covering all cosets;
        // `lde_factor * tree_top_per_coset` is bounded by ~`2^(OMEGA_LOG_ORDER
        // + 1) * sizeof(Digest)` ≈ 8 GB since `log_n + log_lde_factor <=
        // OMEGA_LOG_ORDER` constrains the worst case across all schedules.
        let evals_total_len = lde_factor * evals_stride;
        // SAFETY: cosets backing remains alive for `&self`; evals range is
        // disjoint from the trees backing.
        let evals_backing: &DeviceSlice<BF> =
            unsafe { DeviceSlice::from_raw_parts(evals_ptr, evals_total_len) };

        // Holds a transient tree_tops slab for Partial/None modes through the
        // cap gather. Full mode commits directly into the consolidated trees
        // backing and leaves this `None`.
        let mut transient_tree_tops: Option<DeviceAllocation<Digest>> = None;

        match &mut self.trees {
            TreesHolder::Full(backing) => {
                commit_trace_multi_coset(
                    evals_backing,
                    backing,
                    log_domain_size,
                    log_lde_factor,
                    log_rows_per_leaf,
                    log_tree_cap_size,
                    columns_count,
                    lde_factor,
                    stream,
                )?;
            }
            TreesHolder::Partial(backing) => {
                let mut tree_tops =
                    allocate_trees(lde_factor, log_domain_size, log_rows_per_leaf, context)?;
                commit_trace_with_partial_tree_multi_coset(
                    evals_backing,
                    &mut tree_tops,
                    backing,
                    log_domain_size,
                    log_lde_factor,
                    log_rows_per_leaf,
                    log_tree_cap_size,
                    columns_count,
                    lde_factor,
                    stream,
                )?;
                // tree_tops is dropped after the cap gather completes; the
                // bottom (in `backing`) is what queries read.
                let _ = tree_tops;
            }
            TreesHolder::None => {
                let mut tree_tops =
                    allocate_trees(lde_factor, log_domain_size, log_rows_per_leaf, context)?;
                commit_trace_multi_coset(
                    evals_backing,
                    &mut tree_tops,
                    log_domain_size,
                    log_lde_factor,
                    log_rows_per_leaf,
                    log_tree_cap_size,
                    columns_count,
                    lde_factor,
                    stream,
                )?;
                transient_tree_tops = Some(tree_tops);
            }
        }

        // Single kernel launch over the consolidated tree backing: each
        // block gathers one natural-coset cap region into the bit-reversed
        // (stage1) destination slot.
        match &self.trees {
            TreesHolder::Full(backing) | TreesHolder::Partial(backing) => {
                let per_coset_segment_len = match &self.trees {
                    TreesHolder::Full(_) => per_coset_tree_full_len,
                    TreesHolder::Partial(_) => per_coset_tree_partial_len,
                    _ => unreachable!(),
                };
                // Cap region sits at the tail of each per-coset segment.
                // Matches `merkle_tree_cap`'s offset computation at
                // `ops/blake2s/mod.rs` (`len - 2 * cap_size`).
                let cap_offset_in_digests =
                    per_coset_segment_len - (1usize << (log_subtree_cap_size + 1));
                let cap_offset_in_u32_words = cap_offset_in_digests * BLAKE2S_DIGEST_SIZE_U32_WORDS;
                let stride_in_u32_words =
                    (per_coset_segment_len * BLAKE2S_DIGEST_SIZE_U32_WORDS) as u32;
                let base_u32 = backing.as_ptr() as *const u32;
                // SAFETY: cap_offset_in_u32_words is within per_coset_segment_len.
                let cap_base = unsafe { base_u32.add(cap_offset_in_u32_words) };
                gather_tree_caps_inline(
                    cap_base,
                    lde_factor as u32,
                    cap_words_per_coset,
                    stride_in_u32_words,
                    log_lde_factor,
                    dst_u32,
                    stream,
                )?;
            }
            TreesHolder::None => {
                // None mode now also uses one consolidated tree_tops slab
                // (same layout as Full/Partial backing), so gather_tree_caps
                // works directly across it.
                let backing = transient_tree_tops
                    .as_ref()
                    .expect("None mode allocates transient_tree_tops above");
                let cap_offset_in_digests =
                    per_coset_tree_full_len - (1usize << (log_subtree_cap_size + 1));
                let cap_offset_in_u32_words = cap_offset_in_digests * BLAKE2S_DIGEST_SIZE_U32_WORDS;
                let stride_in_u32_words =
                    (per_coset_tree_full_len * BLAKE2S_DIGEST_SIZE_U32_WORDS) as u32;
                let base_u32 = backing.as_ptr() as *const u32;
                // SAFETY: cap_offset_in_u32_words is within per_coset_tree_full_len.
                let cap_base = unsafe { base_u32.add(cap_offset_in_u32_words) };
                gather_tree_caps_inline(
                    cap_base,
                    lde_factor as u32,
                    cap_words_per_coset,
                    stride_in_u32_words,
                    log_lde_factor,
                    dst_u32,
                    stream,
                )?;
            }
        }

        // `transient_tree_tops` drops at end of scope — its pool free is
        // exec-stream-ordered after the gather, so it is safe to drop here.
        drop(transient_tree_tops);
        Ok(())
    }

    pub(crate) fn commit_all(&mut self, context: &ProverContext) -> CudaResult<()> {
        let cap_size = 1usize << self.log_tree_cap_size;
        let unified_cap: DeviceAllocation<Digest> =
            context.alloc(cap_size, AllocationPlacement::BestFit)?;
        assert!(self.unified_device_cap.replace(unified_cap).is_none());
        let unified_cap_mut = self
            .unified_device_cap
            .as_mut()
            .expect("unified_device_cap was just placed above");
        // SAFETY: `unified_cap_mut` owns a `[Digest]` allocation of length
        // `cap_size`; reinterpreting the same bytes as a `u32` slice of length
        // `cap_size * BLAKE2S_DIGEST_SIZE_U32_WORDS` is layout-compatible
        // (`Digest == [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]`). The raw pointer
        // is rebuilt into a disjoint `&mut DeviceSlice<u32>` so the borrow
        // checker doesn't conflate it with other `&mut self` reborrows below.
        let dst_ptr = unified_cap_mut.as_mut_ptr() as *mut u32;
        let dst_len = cap_size * BLAKE2S_DIGEST_SIZE_U32_WORDS;
        let dst_u32 = unsafe { DeviceSlice::from_raw_parts_mut(dst_ptr, dst_len) };
        self.commit_all_into(dst_u32, context)
    }

    /// Natural-NTT variant of `commit_all_into`: the caller has populated the
    /// cosets backing with `lde_factor * trace_len * src_cols_per_coset` BFs in
    /// the natural multi-coset NTT layout (coset-major outer, column-major
    /// inner). Builds a single flat merkle tree using
    /// `commit_trace_from_ntt_single_tree`, then gathers the cap via the same
    /// `gather_tree_caps_inline` path `commit_all_into` uses.
    ///
    /// Asserted shape: `self.log_lde_factor == 0`, `self.log_rows_per_leaf == 0`
    /// (the WHIR oracle's TraceHolder shape). The natural lde factor and
    /// per-leaf size are passed as arguments — they live outside the TraceHolder
    /// abstraction.
    pub(crate) fn whir_lde_and_commit_all_into(
        &mut self,
        inputs_matrix: &DeviceMatrixChunk<BF>,
        dst_u32: &mut DeviceSlice<u32>,
        log_trace_len: u32,
        natural_log_lde_factor: u32,
        log_values_per_leaf: u32,
        src_cols_per_coset: usize,
        transform_leaves_to_multilinear_coeffs: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert_eq!(
            self.log_lde_factor, 0,
            "whir_lde_and_commit_all_into: TraceHolder must be the WHIR-oracle shape (log_lde_factor = 0)"
        );
        assert_eq!(
            self.log_rows_per_leaf, 0,
            "whir_lde_and_commit_all_into: TraceHolder must be the WHIR-oracle shape (log_rows_per_leaf = 0)"
        );
        assert!(
            !self.cosets_materialized,
            "whir_lde_and_commit_all_into: cosets already materialized"
        );
        let stream = context.get_exec_stream();
        let cap_size = 1usize << self.log_tree_cap_size;
        assert_eq!(
            dst_u32.len(),
            cap_size * BLAKE2S_DIGEST_SIZE_U32_WORDS,
            "whir_lde_and_commit_all_into dst_u32 length must match cap_size * DIGEST_U32_WORDS",
        );

        // Snapshot the cosets backing as a raw const slice so we can borrow
        // `self.cosets` shared and `self.trees` mutable in the same scope.
        let evals_ptr = match &mut self.cosets {
            CosetsHolder::Full(backing) => backing.as_mut_ptr(),
            CosetsHolder::None(_) => {
                panic!("cosets not allocated — call ensure_cosets_materialized first")
            }
        };
        let lde_factor = 1usize << natural_log_lde_factor;
        let trace_len = 1usize << log_trace_len;
        let evals_total_len = lde_factor * trace_len * src_cols_per_coset;
        // SAFETY: cosets backing remains alive for `&self`; evals range is
        // disjoint from the trees backing.
        let ntt_output: &mut DeviceSlice<BF> =
            unsafe { DeviceSlice::from_raw_parts_mut(evals_ptr, evals_total_len) };

        let total_leaf_count_log2 = (log_trace_len - log_values_per_leaf) + natural_log_lde_factor;
        let total_leaf_count = 1usize << total_leaf_count_log2;
        let per_coset_tree_full_len = total_leaf_count << 1;
        let log_subtree_cap_size = self.log_tree_cap_size; // log_lde_factor == 0
        let cap_words_per_coset =
            ((1usize << log_subtree_cap_size) * BLAKE2S_DIGEST_SIZE_U32_WORDS) as u32;

        let mut transient_tree_tops: Option<DeviceAllocation<Digest>> = None;
        match &mut self.trees {
            TreesHolder::Full(backing) => {
                commit_trace_from_ntt_single_tree(
                    inputs_matrix,
                    ntt_output,
                    backing,
                    log_trace_len,
                    natural_log_lde_factor,
                    log_values_per_leaf,
                    self.log_tree_cap_size,
                    src_cols_per_coset,
                    transform_leaves_to_multilinear_coeffs,
                    context,
                )?;
            }
            TreesHolder::Partial(backing) => {
                // Partial mode: the single flat tree's top
                // (leaves + PARTIAL_TREE_REDUCTION_LAYERS-1 layers) lives in a
                // transient slab; the bottom (the rest of the layers) lives in
                // `backing`. Same shape as `commit_trace_with_partial_tree` but
                // single-tree.
                let tree_top_len = per_coset_tree_full_len;
                let mut tree_top =
                    context.alloc::<Digest>(tree_top_len, AllocationPlacement::BestFit)?;
                // Build top: leaves + (PARTIAL_TREE_REDUCTION_LAYERS - 1) layers.
                // commit_trace_from_ntt_single_tree builds leaves + (layers_count
                // - 1) node layers; pass log_tree_cap_size such that layers_count
                // = PARTIAL_TREE_REDUCTION_LAYERS.
                let top_log_cap = total_leaf_count_log2 + 1 - PARTIAL_TREE_REDUCTION_LAYERS;
                commit_trace_from_ntt_single_tree(
                    inputs_matrix,
                    ntt_output,
                    &mut tree_top[..],
                    log_trace_len,
                    natural_log_lde_factor,
                    log_values_per_leaf,
                    top_log_cap,
                    src_cols_per_coset,
                    transform_leaves_to_multilinear_coeffs,
                    context,
                )?;
                // Bottom: read the "top layer" digests out of `tree_top` and
                // continue the merkle tree into `backing` for the remaining
                // layers. Mirrors `commit_trace_with_partial_tree`.
                let bottom_layers_count = total_leaf_count_log2 + 1
                    - PARTIAL_TREE_REDUCTION_LAYERS
                    - self.log_tree_cap_size;
                let tree_bottom_len = tree_top_len >> PARTIAL_TREE_REDUCTION_LAYERS;
                assert_eq!(backing.len(), tree_bottom_len);
                let values = &tree_top[tree_top_len - 2 * tree_bottom_len..][..tree_bottom_len];
                crate::ops::blake2s::build_merkle_tree_nodes(
                    values,
                    backing,
                    bottom_layers_count,
                    stream,
                )?;
                let _ = tree_top; // dropped after cap gather completes via the snapshot below
                transient_tree_tops = None; // partial path doesn't reuse via gather
            }
            TreesHolder::None => {
                panic!("whir_lde_and_commit_all_into: TreesCacheMode::CacheNone is not supported; use CachePartial or CacheFull");
            }
        }

        // Cap gather: the WHIR oracle has log_lde_factor == 0, so the cap lives
        // at the tail of the single tree (no per-coset slabs to merge). Cap
        // region offset is `tree_len - 2 * cap_size`.
        match &self.trees {
            TreesHolder::Full(backing) => {
                let cap_offset_in_digests =
                    per_coset_tree_full_len - (1usize << (log_subtree_cap_size + 1));
                let cap_offset_in_u32_words = cap_offset_in_digests * BLAKE2S_DIGEST_SIZE_U32_WORDS;
                let stride_in_u32_words =
                    (per_coset_tree_full_len * BLAKE2S_DIGEST_SIZE_U32_WORDS) as u32;
                let base_u32 = backing.as_ptr() as *const u32;
                // SAFETY: cap_offset_in_u32_words is within per_coset_tree_full_len.
                let cap_base = unsafe { base_u32.add(cap_offset_in_u32_words) };
                gather_tree_caps_inline(
                    cap_base,
                    /*num_cosets=*/ 1,
                    cap_words_per_coset,
                    stride_in_u32_words,
                    /*log_lde_factor=*/ 0,
                    dst_u32,
                    stream,
                )?;
            }
            TreesHolder::Partial(backing) => {
                // Partial: cap lives in the bottom slab now. The bottom slab is
                // `tree_bottom_len = per_coset_tree_full_len >>
                // PARTIAL_TREE_REDUCTION_LAYERS` digests; the cap is the tail
                // `2 * cap_size`.
                let tree_bottom_len = per_coset_tree_full_len >> PARTIAL_TREE_REDUCTION_LAYERS;
                let cap_offset_in_digests =
                    tree_bottom_len - (1usize << (log_subtree_cap_size + 1));
                let cap_offset_in_u32_words = cap_offset_in_digests * BLAKE2S_DIGEST_SIZE_U32_WORDS;
                let stride_in_u32_words = (tree_bottom_len * BLAKE2S_DIGEST_SIZE_U32_WORDS) as u32;
                let base_u32 = backing.as_ptr() as *const u32;
                let cap_base = unsafe { base_u32.add(cap_offset_in_u32_words) };
                gather_tree_caps_inline(
                    cap_base,
                    /*num_cosets=*/ 1,
                    cap_words_per_coset,
                    stride_in_u32_words,
                    /*log_lde_factor=*/ 0,
                    dst_u32,
                    stream,
                )?;
            }
            TreesHolder::None => unreachable!(),
        }

        let _ = transient_tree_tops;
        Ok(())
    }

    /// Wrapper around `whir_lde_and_commit_all_into` that allocates a private
    /// `unified_device_cap` (mirrors `commit_all`'s relationship to
    /// `commit_all_into`). Used by `#[cfg(test)]` callers that don't have a slab
    /// destination handy.
    pub(crate) fn whir_lde_and_commit_all(
        &mut self,
        inputs_matrix: &DeviceMatrixChunk<BF>,
        log_trace_len: u32,
        natural_log_lde_factor: u32,
        log_values_per_leaf: u32,
        src_cols_per_coset: usize,
        transform_leaves_to_multilinear_coeffs: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let cap_size = 1usize << self.log_tree_cap_size;
        let unified_cap: DeviceAllocation<Digest> =
            context.alloc(cap_size, AllocationPlacement::BestFit)?;
        assert!(self.unified_device_cap.replace(unified_cap).is_none());
        let unified_cap_mut = self
            .unified_device_cap
            .as_mut()
            .expect("unified_device_cap was just placed above");
        // SAFETY: identical reborrow to `commit_all`; see that function's SAFETY
        // comment.
        let dst_ptr = unified_cap_mut.as_mut_ptr() as *mut u32;
        let dst_len = cap_size * BLAKE2S_DIGEST_SIZE_U32_WORDS;
        let dst_u32 = unsafe { DeviceSlice::from_raw_parts_mut(dst_ptr, dst_len) };
        self.whir_lde_and_commit_all_into(
            inputs_matrix,
            dst_u32,
            log_trace_len,
            natural_log_lde_factor,
            log_values_per_leaf,
            src_cols_per_coset,
            transform_leaves_to_multilinear_coeffs,
            context,
        )
    }

    /// Builds and caches partial trees from already-materialized coset evaluations.
    /// The caller must set `self.trees` to `TreesHolder::Partial(...)` with allocated
    /// storage before calling this method.
    pub(crate) fn build_and_cache_partial_trees(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(
            self.cosets_materialized,
            "cosets must be materialized before building partial trees"
        );
        let log_domain_size = self.log_domain_size;
        let log_lde_factor = self.log_lde_factor;
        let log_rows_per_leaf = self.log_rows_per_leaf;
        let log_tree_cap_size = self.log_tree_cap_size;
        let columns_count = self.columns_count;
        let instances_count = 1usize << log_lde_factor;
        let stream = context.get_exec_stream();
        let _per_coset_partial_len = self
            .per_coset_tree_len()
            .expect("build_and_cache_partial_trees requires allocated trees");
        // Snapshot cosets backing as raw pointer to dodge the simultaneous
        // &self.cosets + &mut self.trees borrow inside the loop.
        let evals_stride = columns_count << log_domain_size;
        let evals_ptr = match &self.cosets {
            CosetsHolder::Full(backing) => backing.as_ptr(),
            CosetsHolder::None(_) => {
                panic!("cosets not allocated — call ensure_cosets_materialized first")
            }
        };
        // SAFETY: cosets backing remains alive for `&self`; evals range is
        // disjoint from the trees backing.
        let evals_total_len = instances_count * evals_stride;
        let evals_backing: &DeviceSlice<BF> =
            unsafe { DeviceSlice::from_raw_parts(evals_ptr, evals_total_len) };
        let mut tree_tops =
            allocate_trees(instances_count, log_domain_size, log_rows_per_leaf, context)?;
        let trees_backing = match &mut self.trees {
            TreesHolder::Partial(backing) => backing,
            _ => panic!("build_and_cache_partial_trees requires TreesHolder::Partial"),
        };
        commit_trace_with_partial_tree_multi_coset(
            evals_backing,
            &mut tree_tops,
            trees_backing,
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            instances_count,
            stream,
        )?;
        // tree_tops drops here — frees the transient full-tree allocation.
        drop(tree_tops);
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn materialize_and_commit_from_hypercube_evals(
        &mut self,
        source: &DeviceSlice<BF>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        self.materialize_from_hypercube_evals(source, context)?;
        self.commit_all(context)
    }

    #[cfg(test)]
    fn query_leafs_layout(&self, queries_count: usize) -> (usize, usize) {
        let domain_size = 1usize << self.log_domain_size;
        let values_per_column_count = queries_count << self.log_rows_per_leaf;
        let leafs_len = values_per_column_count * self.columns_count;
        (domain_size, leafs_len)
    }

    fn query_merkle_path_layout(&self, queries_count: usize) -> (u32, usize) {
        let layers_count = self.log_domain_size
            - self.log_rows_per_leaf
            - (self.log_tree_cap_size - self.log_lde_factor);
        let digests_len = queries_count * layers_count as usize;
        (layers_count, digests_len)
    }

    /// Natural-NTT variant of `schedule_query_leaves_into`: the cosets backing
    /// holds the natural multi-coset NTT output (not the packed layout); the
    /// gather kernel applies the full pack-inverse to read it.
    ///
    /// `natural_log_lde_factor` and `log_values_per_leaf` are the actual NTT
    /// parameters (NOT the TraceHolder's stored values).
    pub(crate) fn schedule_query_leaves_into_from_ntt(
        &mut self,
        query_indexes: &DeviceSlice<u32>,
        dst: &mut DeviceSlice<BF>,
        log_trace_len: u32,
        natural_log_lde_factor: u32,
        log_values_per_leaf: u32,
        log_src_cols_per_coset: u32,
        context: &ProverContext,
    ) -> CudaResult<()> {
        self.ensure_cosets_materialized(context)?;
        let cosets = self.get_consolidated_cosets();
        let stream = context.get_exec_stream();
        let log_packed_leaf_count = log_trace_len - log_values_per_leaf;
        let trace_len = 1u32 << log_trace_len;
        crate::ops::blake2s::launch_gather_leaves_for_queries_from_ntt(
            cosets,
            dst,
            natural_log_lde_factor,
            log_packed_leaf_count,
            log_values_per_leaf,
            log_src_cols_per_coset,
            trace_len,
            query_indexes,
            stream,
        )
    }

    /// Natural-NTT variant of `schedule_query_merkle_paths_into` for the WHIR
    /// oracle: the cosets backing holds the natural multi-coset NTT output
    /// (not the packed layout), so the bottom-layer re-hash inside the gather
    /// kernel uses the pack-inverse address translation. Partial mode only —
    /// Full mode walks the consolidated tree without touching cosets and is
    /// unchanged. Asserts `log_lde_factor == 0` and `log_rows_per_leaf == 0`
    /// (the WHIR-oracle TraceHolder shape).
    pub(crate) fn schedule_query_merkle_paths_into_from_ntt(
        &mut self,
        query_indexes: &DeviceSlice<u32>,
        dst: &mut DeviceSlice<u32>,
        log_trace_len: u32,
        natural_log_lde_factor: u32,
        log_values_per_leaf: u32,
        log_src_cols_per_coset: u32,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert_eq!(
            self.log_lde_factor, 0,
            "schedule_query_merkle_paths_into_from_ntt: requires the WHIR-oracle TraceHolder shape (log_lde_factor = 0)"
        );
        assert_eq!(
            self.log_rows_per_leaf, 0,
            "schedule_query_merkle_paths_into_from_ntt: requires the WHIR-oracle TraceHolder shape (log_rows_per_leaf = 0)"
        );
        self.ensure_cosets_materialized(context)?;
        let queries_count = query_indexes.len();
        let (layers_count, _) = self.query_merkle_path_layout(queries_count);
        let stream = context.get_exec_stream();
        let log_packed_leaf_count = log_trace_len - log_values_per_leaf;
        let trace_len = 1u32 << log_trace_len;
        let log_total_leaves_count = self.log_domain_size - self.log_rows_per_leaf;
        match &self.trees {
            TreesHolder::Full(_) => {
                let consolidated_tree = self
                    .get_consolidated_tree()
                    .expect("Full mode has a tree backing");
                let lde_factor = 1usize << self.log_lde_factor;
                let stride_per_coset = consolidated_tree.len() / lde_factor;
                crate::ops::blake2s::gather_merkle_paths_full_for_queries(
                    query_indexes,
                    self.log_lde_factor,
                    stride_per_coset as u32,
                    consolidated_tree,
                    dst,
                    layers_count,
                    stream,
                )
            }
            TreesHolder::Partial(_) => {
                let cosets = self.get_consolidated_cosets();
                let consolidated_tree = self
                    .get_consolidated_tree()
                    .expect("Partial mode has a tree backing");
                // SAFETY: `consolidated_tree` is a `&DeviceSlice<Digest>` covering
                // `lde_factor * stride_per_coset_in_digests * STATE_SIZE` u32 words.
                // We reinterpret as u32 only for the kernel's interface.
                let partial_tree_ptr = consolidated_tree.as_ptr() as *const u32;
                let partial_tree_words =
                    consolidated_tree.len() * (crate::ops::blake2s::STATE_SIZE);
                let partial_tree_u32 =
                    unsafe { DeviceSlice::from_raw_parts(partial_tree_ptr, partial_tree_words) };
                crate::ops::blake2s::gather_merkle_paths_partial_for_queries_from_ntt(
                    cosets,
                    partial_tree_u32,
                    dst,
                    natural_log_lde_factor,
                    log_values_per_leaf,
                    log_src_cols_per_coset,
                    log_packed_leaf_count,
                    trace_len,
                    log_total_leaves_count,
                    layers_count,
                    query_indexes,
                    stream,
                )
            }
            TreesHolder::None => {
                panic!(
                    "schedule_query_merkle_paths_into_from_ntt: TreesCacheMode::CacheNone is not supported \
                     (no consolidated tree backing). Use CachePartial or CacheFull."
                );
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn get_query_leafs(
        &mut self,
        coset_index: usize,
        indexes: &DeviceSlice<u32>,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[BF]>> {
        self.ensure_cosets_materialized(context)?;
        let queries_count = indexes.len();
        let (domain_size, leafs_len) = self.query_leafs_layout(queries_count);
        let values = self.get_coset_evaluations(coset_index);
        let values_matrix = DeviceMatrix::new(values, domain_size);
        let stream = context.get_exec_stream();
        let mut d_leafs = context.alloc(leafs_len, AllocationPlacement::BestFit)?;
        let mut leafs_matrix =
            DeviceMatrixMut::new(&mut d_leafs, queries_count << self.log_rows_per_leaf);
        gather_leaf_rows(
            indexes,
            false,
            self.log_rows_per_leaf,
            &values_matrix,
            &mut leafs_matrix,
            stream,
        )?;
        let mut leafs = unsafe { context.alloc_host_uninit_slice(leafs_len) };
        memory_copy_async(&mut leafs, &d_leafs, stream)?;
        Ok(leafs)
    }

    #[cfg(test)]
    pub(crate) fn get_query_merkle_paths(
        &mut self,
        coset_index: usize,
        indexes: &DeviceSlice<u32>,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[Digest]>> {
        self.ensure_cosets_materialized(context)?;
        let queries_count = indexes.len();
        let (_, digests_len) = self.query_merkle_path_layout(queries_count);
        let stream = context.get_exec_stream();
        let mut d_merkle_paths = context.alloc(digests_len, AllocationPlacement::BestFit)?;
        let (layers_count, _) = self.query_merkle_path_layout(queries_count);
        match &self.trees {
            TreesHolder::Full(_) => {
                let tree = self
                    .get_tree_slice(coset_index)
                    .expect("Full mode has a tree slot");
                gather_merkle_paths_device(
                    indexes,
                    tree,
                    &mut d_merkle_paths,
                    layers_count,
                    stream,
                )?;
            }
            TreesHolder::Partial(_) => {
                let tree_bottom = self
                    .get_tree_slice(coset_index)
                    .expect("Partial mode has a tree slot");
                gather_merkle_paths_from_rows(
                    indexes,
                    false,
                    self.get_coset_evaluations(coset_index),
                    self.log_rows_per_leaf,
                    self.columns_count,
                    tree_bottom,
                    &mut d_merkle_paths,
                    layers_count,
                    stream,
                )?;
            }
            TreesHolder::None => {
                let values = self.get_coset_evaluations(coset_index);
                let mut tree =
                    allocate_tree(self.log_domain_size, self.log_rows_per_leaf, context)?;
                build_merkle_tree(
                    values,
                    &mut tree,
                    self.log_rows_per_leaf,
                    stream,
                    layers_count,
                    false,
                )?;
                gather_merkle_paths_device(
                    indexes,
                    &tree,
                    &mut d_merkle_paths,
                    layers_count,
                    stream,
                )?;
            }
        };
        let mut merkle_paths = unsafe { context.alloc_host_uninit_slice(digests_len) };
        memory_copy_async(&mut merkle_paths, &d_merkle_paths, stream)?;
        Ok(merkle_paths)
    }

    /// Test-only sibling of `get_query_merkle_paths` for the WHIR oracle's
    /// natural-NTT cosets backing. Allocates a device path slab + invokes
    /// `schedule_query_merkle_paths_into_from_ntt`, then copies asynchronously
    /// to host. Caller is responsible for stream synchronization.
    #[cfg(test)]
    pub(crate) fn get_query_merkle_paths_from_ntt(
        &mut self,
        indexes: &DeviceSlice<u32>,
        log_trace_len: u32,
        natural_log_lde_factor: u32,
        log_values_per_leaf: u32,
        log_src_cols_per_coset: u32,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[Digest]>> {
        let queries_count = indexes.len();
        let (_, digests_len) = self.query_merkle_path_layout(queries_count);
        let mut d_merkle_paths: DeviceAllocation<Digest> =
            context.alloc(digests_len, AllocationPlacement::BestFit)?;
        // Reinterpret the Digest slab as u32 for the kernel's signature. SAFETY:
        // `Digest = [u32; STATE_SIZE]` has the same byte layout; both views
        // alias the same exclusive allocation for the duration of the call.
        let words_len = digests_len * crate::ops::blake2s::STATE_SIZE;
        let d_merkle_paths_u32 = unsafe {
            DeviceSlice::from_raw_parts_mut(d_merkle_paths.as_mut_ptr() as *mut u32, words_len)
        };
        self.schedule_query_merkle_paths_into_from_ntt(
            indexes,
            d_merkle_paths_u32,
            log_trace_len,
            natural_log_lde_factor,
            log_values_per_leaf,
            log_src_cols_per_coset,
            context,
        )?;
        let mut merkle_paths = unsafe { context.alloc_host_uninit_slice(digests_len) };
        memory_copy_async(
            &mut merkle_paths,
            &d_merkle_paths,
            context.get_exec_stream(),
        )?;
        Ok(merkle_paths)
    }

    #[cfg(test)]
    pub fn get_leafs_and_merkle_paths(
        &mut self,
        coset_index: usize,
        indexes: &DeviceSlice<u32>,
        context: &ProverContext,
    ) -> CudaResult<LeafsAndMerklePaths> {
        let leafs = self.get_query_leafs(coset_index, indexes, context)?;
        let merkle_paths = self.get_query_merkle_paths(coset_index, indexes, context)?;
        Ok(LeafsAndMerklePaths {
            leafs,
            merkle_paths,
        })
    }
}

fn allocate_cosets<T>(
    instances_count: usize,
    log_domain_size: u32,
    columns_count: usize,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<T>> {
    let per_coset_len = columns_count << log_domain_size;
    let total = instances_count * per_coset_len;
    context.alloc(total, AllocationPlacement::Bottom)
}

#[cfg(test)]
fn allocate_tree(
    log_domain_size: u32,
    log_rows_per_leaf: u32,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<Digest>> {
    let size = 1 << (log_domain_size + 1 - log_rows_per_leaf);
    context.alloc(size, AllocationPlacement::Bottom)
}

pub(crate) fn allocate_trees(
    instances_count: usize,
    log_domain_size: u32,
    log_rows_per_leaf: u32,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<Digest>> {
    let per_coset_len = 1usize << (log_domain_size + 1 - log_rows_per_leaf);
    let total = instances_count * per_coset_len;
    context.alloc(total, AllocationPlacement::Bottom)
}

/// Multi-coset variant of `commit_trace`: builds all `cosets_in_tile` per-
/// coset Merkle trees in one launch per layer. `evals_backing` holds
/// `[coset0_evals | coset1_evals | ...]` (each coset's evals span
/// `columns_count << log_domain_size` BFs); `trees_backing` holds the same
/// shape with `tree_len = 2 << (log_domain_size - log_rows_per_leaf)` digests
/// per coset.
pub(crate) fn commit_trace_multi_coset(
    evals_backing: &DeviceSlice<BF>,
    trees_backing: &mut DeviceSlice<Digest>,
    log_domain_size: u32,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_tree_cap_size: u32,
    columns_count: usize,
    cosets_in_tile: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(log_tree_cap_size >= log_lde_factor);
    let log_coset_tree_cap_size = log_tree_cap_size - log_lde_factor;
    assert!(log_domain_size >= log_rows_per_leaf + log_coset_tree_cap_size);
    let per_coset_evals_stride = columns_count << log_domain_size;
    let per_coset_leaves_count = 1usize << (log_domain_size - log_rows_per_leaf);
    let per_coset_tree_stride = per_coset_leaves_count << 1;
    assert_eq!(evals_backing.len(), per_coset_evals_stride * cosets_in_tile);
    assert_eq!(trees_backing.len(), per_coset_tree_stride * cosets_in_tile);
    let layers_count = log_domain_size + 1 - log_rows_per_leaf - log_coset_tree_cap_size;
    build_merkle_tree_multi_coset(
        evals_backing,
        trees_backing,
        log_rows_per_leaf,
        stream,
        layers_count,
        cosets_in_tile,
        per_coset_leaves_count,
        per_coset_evals_stride,
        per_coset_tree_stride,
        columns_count,
    )
}

/// Mirror of `commit_trace_multi_coset` for the WHIR oracle path: builds a
/// single flat merkle tree across all `cosets_in_tile = 1 <<
/// natural_log_lde_factor` cosets, reading the natural-NTT cosets layout via
/// `launch_leaves_kernel_from_ntt_multi_coset` and constructing node layers
/// with the single-tree `build_merkle_tree_nodes` (NOT the multi-coset
/// variant, because the WHIR oracle's `TraceHolder` has `log_lde_factor = 0`
/// and thus owns ONE flat tree across all natural cosets).
///
/// `natural_log_lde_factor` is the actual coset count of the NTT output
/// (typically `whir_steps_lde_factors[i].trailing_zeros()`), NOT the
/// `TraceHolder`'s `log_lde_factor`.
pub(crate) fn commit_trace_from_ntt_single_tree(
    inputs_matrix: &DeviceMatrixChunk<BF>,
    ntt_output: &mut DeviceSlice<BF>,
    trees_backing: &mut DeviceSlice<Digest>,
    log_trace_len: u32,
    natural_log_lde_factor: u32,
    log_values_per_leaf: u32,
    log_tree_cap_size: u32,
    src_cols_per_coset: usize,
    transform_leaves_to_multilinear_coeffs: bool,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(natural_log_lde_factor >= 1);
    assert!(log_trace_len >= log_values_per_leaf);
    let trace_len = 1 << log_trace_len;
    let packed_leaf_count = 1usize << (log_trace_len - log_values_per_leaf);
    let total_leaf_count = packed_leaf_count
        .checked_mul(1 << natural_log_lde_factor)
        .expect("total_leaf_count overflow");
    assert_eq!(trees_backing.len(), total_leaf_count << 1);
    let total_leaf_count_log2 = (log_trace_len - log_values_per_leaf) + natural_log_lde_factor;
    assert!(log_tree_cap_size <= total_leaf_count_log2);
    let layers_count = total_leaf_count_log2 + 1 - log_tree_cap_size;
    let (leaves, nodes) = trees_backing.split_at_mut(total_leaf_count);
    let stream = context.get_exec_stream();

    let device_properties = context.get_device_properties();
    let ntt_ctx = context.ntt_device_context();
    // Recursive WHIR folds to a small trace (trace_len_log2 <= 13), the DIT
    // forward-NTT range, which needs a pooled d-table scratch (len >= N).
    // Allocate from the stream-ordered pool so this stays enqueue-only per
    // the GPU scheduling contract; the handle outlives the launches below.
    // Outside the DIT range the compact path ignores the scratch, so the
    // allocation is skipped entirely.
    let mut d_scratch = if log_trace_len <= 13 {
        Some(context.alloc::<BF>(trace_len, AllocationPlacement::BestFit)?)
    } else {
        None
    };

    let l2_bytes = device_properties.l2_cache_size_bytes;
    let single_bf_col_bytes = std::mem::size_of::<BF>() << log_trace_len;
    let single_coset_bytes = src_cols_per_coset * single_bf_col_bytes;
    let cosets_in_tile_chunk = if l2_bytes >= single_coset_bytes {
        let nearest = l2_bytes / single_coset_bytes;
        if nearest.is_power_of_two() {
            nearest
        } else {
            nearest.next_power_of_two() >> 1
        }
    } else {
        1
    };
    let total_cosets = 1 << natural_log_lde_factor;
    if total_cosets > cosets_in_tile_chunk {
        assert_eq!(total_cosets % cosets_in_tile_chunk, 0);
    }
    let mut ntt_output_matrix = DeviceMatrixMut::new(ntt_output, trace_len);
    for coset_index_base in (0..total_cosets).step_by(cosets_in_tile_chunk) {
        let cosets_in_tile =
            std::cmp::min(cosets_in_tile_chunk, total_cosets - coset_index_base);
        let scratch_opt = d_scratch.as_mut().map(|s| &mut s[..]);
        // The NTT API does not internally apply an offset for coset_index_base.
        let offset = EXT4_DEGREE * trace_len * coset_index_base;
        bitreversed_monomials_to_natural_evals_multi_coset_with_coset_range(
            inputs_matrix,
            &mut (ntt_output_matrix.slice_mut())[offset..],
            log_trace_len as usize,
            natural_log_lde_factor as usize,
            cosets_in_tile,
            coset_index_base,
            EXT4_DEGREE,
            false,
            ntt_ctx,
            scratch_opt,
            stream,
            device_properties,
        )?;
        if transform_leaves_to_multilinear_coeffs {
            transform_whir_leaves_from_ntt_in_place_multi_coset(
                &mut ntt_output_matrix,
                log_trace_len,
                natural_log_lde_factor,
                log_values_per_leaf,
                coset_index_base as u32,
                cosets_in_tile as u32,
                src_cols_per_coset as u32,
                stream,
            )?;
        }
        crate::ops::blake2s::launch_leaves_kernel_from_ntt_multi_coset(
            ntt_output_matrix.slice(),
            leaves,
            log_values_per_leaf,
            src_cols_per_coset as u32,
            natural_log_lde_factor,
            coset_index_base as u32,
            cosets_in_tile,
            packed_leaf_count,
            trace_len as u32,
            stream,
        )?;
    }
    // } else {
    //     let coset_index_base = 0;
    //     let cosets_in_tile = 1usize << natural_log_lde_factor;
    //     crate::ops::blake2s::launch_leaves_kernel_from_ntt_multi_coset(
    //         ntt_output,
    //         leaves,
    //         log_values_per_leaf,
    //         src_cols_per_coset as u32,
    //         natural_log_lde_factor,
    //         coset_index_base,
    //         cosets_in_tile,
    //         packed_leaf_count,
    //         trace_len as u32,
    //         stream,
    //     )?;
    // }

    // Single-tree node layers: build_merkle_tree_nodes operates on a flat
    // `[leaves | nodes]` slab. `layers_count - 1` because the leaf layer is
    // already written; the function builds the remaining `layers_count - 1`
    // node layers.
    crate::ops::blake2s::build_merkle_tree_nodes(leaves, nodes, layers_count - 1, stream)
}

/// Multi-coset variant of `commit_trace_with_partial_tree`: takes one big
/// `tree_tops_backing` slab sized for all cosets' tops, plus the existing
/// shared `tree_bottoms_backing`. Builds top layers (leaves +
/// PARTIAL_TREE_REDUCTION_LAYERS-1 layers of nodes) into every coset's top
/// slab in one launch per layer, then runs the bottom layers across all
/// cosets in one launch per layer.
pub(crate) fn commit_trace_with_partial_tree_multi_coset(
    evals_backing: &DeviceSlice<BF>,
    tree_tops_backing: &mut DeviceSlice<Digest>,
    tree_bottoms_backing: &mut DeviceSlice<Digest>,
    log_domain_size: u32,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_tree_cap_size: u32,
    columns_count: usize,
    cosets_in_tile: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(log_tree_cap_size >= log_lde_factor);
    let log_coset_tree_cap_size = log_tree_cap_size - log_lde_factor;
    assert!(
        log_domain_size
            > log_rows_per_leaf + PARTIAL_TREE_REDUCTION_LAYERS + log_coset_tree_cap_size
    );
    let per_coset_evals_stride = columns_count << log_domain_size;
    let per_coset_top_stride = 1usize << (log_domain_size + 1 - log_rows_per_leaf);
    let per_coset_top_leaves_count = per_coset_top_stride >> 1;
    let per_coset_bottom_stride = per_coset_top_stride >> PARTIAL_TREE_REDUCTION_LAYERS;
    assert_eq!(evals_backing.len(), per_coset_evals_stride * cosets_in_tile);
    assert_eq!(
        tree_tops_backing.len(),
        per_coset_top_stride * cosets_in_tile
    );
    assert_eq!(
        tree_bottoms_backing.len(),
        per_coset_bottom_stride * cosets_in_tile
    );
    // Top: leaves + (PARTIAL_TREE_REDUCTION_LAYERS - 1) node layers, all
    // built inside each coset's tree_top slab.
    build_merkle_tree_multi_coset(
        evals_backing,
        tree_tops_backing,
        log_rows_per_leaf,
        stream,
        PARTIAL_TREE_REDUCTION_LAYERS,
        cosets_in_tile,
        per_coset_top_leaves_count,
        per_coset_evals_stride,
        per_coset_top_stride,
        columns_count,
    )?;
    // Bottom: each coset's "top layer" within tree_tops has
    // `per_coset_bottom_stride` digests sitting at offset
    // `per_coset_top_stride - 2 * per_coset_bottom_stride` (mirroring
    // `tree_top[tree_top_len - 2 * tree_bottom_len..][..tree_bottom_len]` in
    // the single-coset path). The first bottom layer hashes pairs of those
    // top-layer digests into tree_bottoms_backing[0..bottom_stride/2] across
    // every coset; subsequent layers hash up in-place inside the bottoms
    // slab. tree_bottoms is sized for OUTPUTS only, not for re-storing the
    // input, so we never copy the top layer into the bottoms slab.
    let top_layer_src_offset = per_coset_top_stride - 2 * per_coset_bottom_stride;
    let bottom_layers_count = log_domain_size + 1
        - log_rows_per_leaf
        - PARTIAL_TREE_REDUCTION_LAYERS
        - log_coset_tree_cap_size;
    build_merkle_tree_nodes_multi_coset_from_external_src(
        tree_tops_backing,
        tree_bottoms_backing,
        bottom_layers_count,
        cosets_in_tile,
        per_coset_top_stride,
        per_coset_bottom_stride,
        top_layer_src_offset,
        per_coset_bottom_stride,
        stream,
    )
}

pub(crate) fn bitreverse_index(index: usize, num_bits: u32) -> usize {
    if num_bits == 0 {
        0
    } else {
        index.reverse_bits() >> (usize::BITS - num_bits)
    }
}

#[cfg(test)]
mod tests;
