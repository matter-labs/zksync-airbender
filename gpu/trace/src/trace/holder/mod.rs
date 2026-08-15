use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use crate::upstream::MerkleTreeCapVarLength;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::context::HostAllocation;
use gpu_core::primitives::device_structures::DeviceMatrix;
use gpu_core::primitives::device_structures::{
    DeviceMatrixChunk, DeviceMatrixImpl, DeviceMatrixMut, DeviceMatrixMutImpl,
};
use gpu_core::primitives::field::BF;
use gpu_hash::blake2s::build_merkle_tree;
use gpu_hash::blake2s::{
    build_merkle_tree_multi_coset, build_partial_merkle_tree_multi_coset, gather_tree_caps_inline,
    Digest,
};
use gpu_hash::blake2s::{
    gather_leaf_rows, gather_merkle_paths_device, gather_merkle_paths_from_rows,
};
use gpu_ntt::ntt::{
    bitreversed_monomials_to_natural_evals_multi_coset, hypercube_to_multi_coset_evals_fused,
    hypercube_x1_msb_evals_to_x1_msb_monomials, log_size_supports_transposed_monomials,
};
use gpu_prover_context::ProverContext;

// test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
#[doc(hidden)]
pub const PARTIAL_TREE_REDUCTION_LAYERS: u32 = gpu_core::primitives::utils::LOG_WARP_SIZE;

// test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
#[doc(hidden)]
#[derive(Copy, Clone)]
pub enum TreesCacheMode {
    CacheNone,
    CachePartial,
    CacheFull,
}

pub(crate) enum CosetsHolder<T> {
    Full(DeviceAllocation<T>),
    None(std::marker::PhantomData<T>),
}

// test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
#[doc(hidden)]
pub enum TreesHolder {
    Full(DeviceAllocation<Digest>),
    Partial(DeviceAllocation<Digest>),
    None,
}

// test-reference readers: return type of the doc-hidden pub `get_leafs_and_merkle_paths`.
#[doc(hidden)]
pub struct LeafsAndMerklePaths {
    pub leafs: HostAllocation<[BF]>,
    pub merkle_paths: HostAllocation<[Digest]>,
}

// test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
#[doc(hidden)]
pub struct TraceHolder<T> {
    pub log_domain_size: u32,
    pub log_lde_factor: u32,
    pub log_rows_per_leaf: u32,
    pub log_tree_cap_size: u32,
    pub columns_count: usize,
    raw_hypercube_evals: std::sync::Arc<DeviceAllocation<T>>,
    cosets_materialized: bool,
    // `pub(crate)`, not `pub`: unlike `trees`/`unified_device_cap`, nothing
    // outside `gpu_trace` reads `cosets` directly (confirmed by grep across
    // `gpu_gkr`/`gpu_whir`/`gpu_circuit_prover`), so this stays no wider than
    // its `pub(crate)` `CosetsHolder<T>` type.
    pub(crate) cosets: CosetsHolder<T>,
    pub trees: TreesHolder,
    /// Device-resident, contiguous Merkle cap of length `1 << log_tree_cap_size`,
    /// laid out in canonical bit-reversed coset order (`stage1_pos = 0..lde_factor`,
    /// reading from `coset[bitreverse(stage1_pos)]`). Populated by `commit_all`
    /// (or by a pre-prove H2D from a precomputed host source for the setup/memory
    /// holders that bypass `commit_all`).
    pub unified_device_cap: Option<DeviceAllocation<Digest>>,
}

// Public methods are cross-crate production APIs; `#[doc(hidden)]` methods are test seams.
impl<T> TraceHolder<T> {
    pub fn new(
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
    // test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
    #[doc(hidden)]
    pub fn new_without_cosets(
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
    // test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
    #[doc(hidden)]
    pub fn unified_device_cap(&self) -> &DeviceAllocation<Digest> {
        self.unified_device_cap
            .as_ref()
            .expect("unified device cap must be materialized before access")
    }

    /// Installs a private unified cap after an external scheduler has filled it.
    #[doc(hidden)]
    pub fn install_unified_device_cap(&mut self, cap: DeviceAllocation<Digest>) {
        assert_eq!(cap.len(), 1usize << self.log_tree_cap_size);
        assert!(
            self.unified_device_cap.is_none(),
            "unified device cap was already installed",
        );
        self.unified_device_cap = Some(cap);
    }

    // test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
    #[doc(hidden)]
    pub fn get_hypercube_evals(&self) -> &DeviceSlice<T> {
        self.raw_hypercube_evals.as_ref()
    }

    pub fn get_uninit_hypercube_evals_mut(&mut self) -> &mut DeviceSlice<T> {
        self.cosets_materialized = false;
        std::sync::Arc::get_mut(&mut self.raw_hypercube_evals)
            .expect("raw hypercube allocation must not be shared while being initialized")
    }

    pub fn raw_hypercube_backing(&self) -> std::sync::Arc<DeviceAllocation<T>> {
        std::sync::Arc::clone(&self.raw_hypercube_evals)
    }

    pub fn are_cosets_materialized(&self) -> bool {
        self.cosets_materialized
    }

    /// Release the materialized LDE cosets, returning the holder to its
    /// pre-`ensure_cosets_materialized` state (`raw_hypercube_evals`, cached
    /// partial trees, and the unified cap are kept). The cosets are a transient
    /// expansion needed only while committing / WHIR-opening this trace; once
    /// those reads have been scheduled the reservation is freed stream-ordered
    /// (same basis as the other prove-end device releases). A subsequent
    /// `ensure_cosets_materialized` re-allocates them on demand.
    pub fn release_cosets(&mut self) {
        self.cosets = CosetsHolder::None(std::marker::PhantomData);
        self.cosets_materialized = false;
    }

    pub fn mark_cosets_materialized(&mut self) {
        self.cosets_materialized = true;
    }

    // test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
    #[doc(hidden)]
    pub fn get_coset_evaluations(&self, coset_index: usize) -> &DeviceSlice<T> {
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

    pub fn get_evaluations(&self) -> &DeviceSlice<T> {
        self.get_coset_evaluations(0)
    }

    /// Returns the single consolidated cosets backing as one device slice in
    /// coset-major order: `backing[coset_index * stride .. (coset_index + 1) * stride]`
    /// is the slice for coset `coset_index`, where `stride = columns_count << log_domain_size`.
    pub fn get_consolidated_cosets(&self) -> &DeviceSlice<T> {
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

    pub fn get_uninit_tree_mut(&mut self, coset_index: usize) -> Option<&mut DeviceSlice<Digest>> {
        assert!(coset_index < (1usize << self.log_lde_factor));
        let per_coset = self.per_coset_tree_len()?;
        match &mut self.trees {
            TreesHolder::Full(backing) | TreesHolder::Partial(backing) => {
                Some(&mut backing[coset_index * per_coset..(coset_index + 1) * per_coset])
            }
            TreesHolder::None => None,
        }
    }

    /// Returns disjoint mutable views of the unmaterialized consolidated
    /// coset storage and tree storage for an external commit scheduler.
    pub fn get_uninit_cosets_and_tree_mut(&mut self) -> (&mut DeviceSlice<T>, &mut TreesHolder) {
        assert!(
            !self.cosets_materialized,
            "cosets are already marked materialized",
        );
        let cosets = match &mut self.cosets {
            CosetsHolder::Full(backing) => &mut backing[..],
            CosetsHolder::None(_) => panic!("cosets storage is not allocated"),
        };
        (cosets, &mut self.trees)
    }

    /// Shared-borrow per-coset tree slice. Returns the subrange of the
    /// consolidated tree backing belonging to `coset_index`, or `None` if
    /// trees aren't allocated.
    // un-gated (was cfg(test)): internal helper of the doc-hidden pub query methods below.
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
    pub fn get_consolidated_tree(&self) -> Option<&DeviceSlice<Digest>> {
        match &self.trees {
            TreesHolder::Full(backing) | TreesHolder::Partial(backing) => Some(backing),
            TreesHolder::None => None,
        }
    }
}

impl TraceHolder<BF> {
    // test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
    #[doc(hidden)]
    pub fn materialize_cosets_from_owned_hypercube(
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

            match &mut self.cosets {
                CosetsHolder::Full(backing) => {
                    // CosetsHolder::Full layout: [coset][col][trace_len], stride
                    // between cosets = columns_count * domain_size. The
                    // multi-coset NTT slices the backing at the current
                    // column's position and uses num_cols_per_coset_stride =
                    // columns_count to write each coset's slab in one launch,
                    // replacing the per-coset NTT loop.
                    let backing_from_col = &mut backing[offset..];
                    // Hybrid fused-boundary path: the hypercube final pass runs
                    // once, fused with coset 0's forward initial + in-place
                    // monomial writeback (transposed 3-pass regime only; falls
                    // back below).
                    let fused = hypercube_to_multi_coset_evals_fused(
                        source_column,
                        &mut coeff_scratch[0..domain_size],
                        backing_from_col,
                        self.log_domain_size as usize,
                        self.log_lde_factor as usize,
                        self.columns_count,
                        stream,
                        context.get_device_properties(),
                    )?;
                    if !fused {
                        hypercube_x1_msb_evals_to_x1_msb_monomials(
                            source_column,
                            &mut coeff_scratch[0..domain_size],
                            self.log_domain_size as usize,
                            use_transposed_monomials,
                            stream,
                            context.get_device_properties(),
                        )?;
                        let monomials = DeviceMatrixChunk::new(
                            &coeff_scratch[0..domain_size],
                            domain_size,
                            0,
                            domain_size,
                        );
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
                }
                CosetsHolder::None(_) => {
                    panic!("cosets not allocated — call ensure_cosets_materialized first")
                }
            }
        }
        self.cosets_materialized = true;
        Ok(())
    }

    // test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
    #[doc(hidden)]
    pub fn ensure_cosets_materialized(&mut self, context: &ProverContext) -> CudaResult<()> {
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

    // un-gated (was cfg(test)): internal helper of the doc-hidden pub commit/query methods.
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
    /// function and allocates a private cap buffer.
    pub fn commit_all_into(
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

        let evals_total_len = lde_factor * evals_stride;
        // SAFETY: cosets backing remains alive for `&self`; evals range is
        // disjoint from the trees backing.
        let evals_backing: &DeviceSlice<BF> =
            unsafe { DeviceSlice::from_raw_parts(evals_ptr, evals_total_len) };

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
                commit_trace_with_partial_tree_multi_coset(
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
                    cap_words_per_coset,
                    stride_in_u32_words,
                    log_lde_factor,
                    dst_u32,
                    stream,
                )?;
            }
            TreesHolder::None => {
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

    // test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
    #[doc(hidden)]
    pub fn commit_all(&mut self, context: &ProverContext) -> CudaResult<()> {
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

    /// Builds and caches partial trees from already-materialized coset evaluations.
    /// The caller must set `self.trees` to `TreesHolder::Partial(...)` with allocated
    /// storage before calling this method.
    // test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
    #[doc(hidden)]
    pub fn build_and_cache_partial_trees(&mut self, context: &ProverContext) -> CudaResult<()> {
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
        let trees_backing = match &mut self.trees {
            TreesHolder::Partial(backing) => backing,
            _ => panic!("build_and_cache_partial_trees requires TreesHolder::Partial"),
        };
        commit_trace_with_partial_tree_multi_coset(
            evals_backing,
            trees_backing,
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            instances_count,
            stream,
        )?;
        Ok(())
    }

    // test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
    #[doc(hidden)]
    pub fn materialize_and_commit_from_hypercube_evals(
        &mut self,
        source: &DeviceSlice<BF>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        self.materialize_from_hypercube_evals(source, context)?;
        self.commit_all(context)
    }

    // un-gated (was cfg(test)): internal helper of the doc-hidden pub query methods.
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
    pub fn schedule_query_leaves_into_from_ntt(
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
        gpu_hash::blake2s::gather_leaves_for_queries_from_ntt(
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
    pub fn schedule_query_merkle_paths_into_from_ntt(
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
                gpu_hash::blake2s::gather_merkle_paths_full_for_queries(
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
                let partial_tree_words = consolidated_tree.len() * (gpu_hash::blake2s::STATE_SIZE);
                let partial_tree_u32 =
                    unsafe { DeviceSlice::from_raw_parts(partial_tree_ptr, partial_tree_words) };
                gpu_hash::blake2s::gather_merkle_paths_partial_for_queries_from_ntt(
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

    // test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
    #[doc(hidden)]
    pub fn get_query_leafs(
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

    // test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
    #[doc(hidden)]
    pub fn get_query_merkle_paths(
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

    // test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
    #[doc(hidden)]
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

// un-gated (was cfg(test)): internal helper of the doc-hidden pub commit/query methods.
fn allocate_tree(
    log_domain_size: u32,
    log_rows_per_leaf: u32,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<Digest>> {
    let size = 1 << (log_domain_size + 1 - log_rows_per_leaf);
    context.alloc(size, AllocationPlacement::Bottom)
}

// test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
#[doc(hidden)]
pub fn allocate_trees(
    instances_count: usize,
    log_domain_size: u32,
    log_rows_per_leaf: u32,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<Digest>> {
    let per_coset_len = 1usize << (log_domain_size + 1 - log_rows_per_leaf);
    let total = instances_count * per_coset_len;
    context.alloc(total, AllocationPlacement::Bottom)
}

/// Builds all `cosets_in_tile` per-
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
        layers_count,
        cosets_in_tile,
        per_coset_leaves_count,
        per_coset_evals_stride,
        per_coset_tree_stride,
        columns_count,
        stream,
    )
}

pub(crate) fn commit_trace_with_partial_tree_multi_coset(
    evals_backing: &DeviceSlice<BF>,
    tree_backing: &mut DeviceSlice<Digest>,
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
    let per_coset_leaves_count = 1usize << (log_domain_size - log_rows_per_leaf);
    let per_coset_tree_stride = (per_coset_leaves_count << 1) >> PARTIAL_TREE_REDUCTION_LAYERS;
    assert_eq!(evals_backing.len(), per_coset_evals_stride * cosets_in_tile);
    assert_eq!(tree_backing.len(), per_coset_tree_stride * cosets_in_tile);
    let layers_count = log_domain_size + 1
        - log_rows_per_leaf
        - PARTIAL_TREE_REDUCTION_LAYERS
        - log_coset_tree_cap_size;
    build_partial_merkle_tree_multi_coset(
        evals_backing,
        tree_backing,
        log_rows_per_leaf,
        layers_count,
        cosets_in_tile,
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

// General-purpose host-readback helpers for the unified Merkle cap. Relocated
// out of the `#[cfg(test)]`-gated `tests` module (they have no test-framework
// dependency) so apex test suites can reach them across the crate boundary.
impl<T> TraceHolder<T> {
    /// Reads the unified device cap back to host and returns it as a single
    /// `MerkleTreeCapVarLength`. Performs an exec-stream synchronize, so it is
    /// only meant for tests / one-shot helpers, not for the `prove()` hot path.
    // test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
    #[doc(hidden)]
    pub fn read_full_cap_synchronously(
        &self,
        context: &ProverContext,
    ) -> CudaResult<MerkleTreeCapVarLength> {
        let device_cap = self.unified_device_cap();
        let cap_size = device_cap.len();
        debug_assert_eq!(cap_size, 1usize << self.log_tree_cap_size);
        let stream = context.get_exec_stream();
        let mut host = vec![Digest::default(); cap_size];
        memory_copy_async(host.as_mut_slice(), device_cap, stream)?;
        stream.synchronize()?;
        Ok(MerkleTreeCapVarLength { cap: host })
    }

    /// Reads the unified device cap back to host and chops it into the
    /// per-coset `MerkleTreeCapVarLength` shape. Used by tests that compare
    /// against CPU caps produced per-coset. Performs a host synchronize.
    // test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
    #[doc(hidden)]
    pub fn read_per_coset_caps_synchronously(
        &self,
        context: &ProverContext,
    ) -> CudaResult<Vec<MerkleTreeCapVarLength>> {
        let lde_factor = 1usize << self.log_lde_factor;
        let full = self.read_full_cap_synchronously(context)?.cap;
        debug_assert_eq!(full.len() % lde_factor, 0);
        let per_coset = full.len() / lde_factor;
        Ok((0..lde_factor)
            .map(|stage1_pos| MerkleTreeCapVarLength {
                cap: full[stage1_pos * per_coset..(stage1_pos + 1) * per_coset].to_vec(),
            })
            .collect())
    }
}

#[cfg(test)]
mod tests;
