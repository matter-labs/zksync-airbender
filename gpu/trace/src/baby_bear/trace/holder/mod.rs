mod openings;

use crate::trace::holder::*;
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use crate::upstream::{BaseCommitmentGeometry, BaseOracleRole};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::context::HostAllocation;
use gpu_core::primitives::device_structures::DeviceMatrix;
use gpu_core::primitives::device_structures::{
    DeviceMatrixChunk, DeviceMatrixChunkMut, DeviceMatrixMut,
};
use gpu_core::primitives::field::BF;
use gpu_hash::blake2s::{
    build_merkle_tree_nodes_multi_coset_over_existing_layer,
    build_partial_merkle_tree_multi_coset_physical, gather_tree_caps_inline,
    hash_leaves_multi_coset_physical, Digest,
};
use gpu_hash::blake2s::{
    gather_leaf_rows_physical, gather_merkle_paths_device, gather_merkle_paths_from_rows_physical,
};
use gpu_ntt::baby_bear::{
    hypercube_evals_to_monomials, hypercube_to_bitreversed_multi_coset_evals_fused_log_n_20,
    hypercube_to_multi_coset_bitrev_evals_fused, log_size_supports_natural_to_bitrev_lde,
    natural_monomials_to_bitreversed_evals_multi_coset,
};
use gpu_ops::bit_reverse::bit_reverse_in_place;
use gpu_prover_context::ProverContext;

#[doc(hidden)]
pub struct LeafsAndMerklePaths {
    pub leafs: HostAllocation<[BF]>,
    pub merkle_paths: HostAllocation<[Digest]>,
}

impl TraceHolder<BF> {
    pub fn new_base_without_cosets(
        geometry: BaseCommitmentGeometry,
        role: BaseOracleRole,
        trees_mode: TreesCacheMode,
        partial_tree_reduction_layers: u32,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        assert_partial_tree_reduction_layers(partial_tree_reduction_layers);
        let mut holder = Self::new_without_cosets_padded(
            u32::try_from(geometry.trace_len_log2()).expect("trace log2 exceeds u32"),
            geometry.lde_factor().trailing_zeros(),
            geometry.values_per_leaf().trailing_zeros(),
            geometry.cap_size().trailing_zeros(),
            geometry.oracle(role).logical_columns(),
            u32::try_from(geometry.pack_log2()).expect("packing log2 exceeds u32"),
            TreesCacheMode::CacheNone,
            partial_tree_reduction_layers,
            context,
        )?;
        holder.base_geometry = Some((geometry, role));
        if !holder.is_empty_base_oracle() {
            holder.trees = match trees_mode {
                TreesCacheMode::CacheNone => TreesHolder::None,
                TreesCacheMode::CachePartial => TreesHolder::Partial(allocate_trees(
                    1usize << holder.log_lde_factor,
                    holder.commitment_log_domain_size() - holder.partial_tree_reduction_layers(),
                    holder.log_rows_per_leaf,
                    context,
                )?),
                TreesCacheMode::CacheFull => TreesHolder::Full(allocate_trees(
                    1usize << holder.log_lde_factor,
                    holder.commitment_log_domain_size(),
                    holder.log_rows_per_leaf,
                    context,
                )?),
            };
        }
        Ok(holder)
    }

    pub fn new_base(
        geometry: BaseCommitmentGeometry,
        role: BaseOracleRole,
        trees_mode: TreesCacheMode,
        partial_tree_reduction_layers: u32,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let mut holder = Self::new_base_without_cosets(
            geometry,
            role,
            trees_mode,
            partial_tree_reduction_layers,
            context,
        )?;
        holder.cosets = CosetsHolder::Full(allocate_cosets(
            1usize << holder.log_lde_factor,
            holder.commitment_log_domain_size(),
            holder.committed_columns_count(),
            context,
        )?);
        Ok(holder)
    }
}

impl TraceHolder<BF> {
    #[doc(hidden)]
    pub fn materialize_cosets_from_owned_hypercube(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let source = self.raw_hypercube_backing();
        self.materialize_cosets_from_source(&source, context)
    }

    fn materialize_cosets_from_source(
        &mut self,
        source: &DeviceSlice<BF>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let log_domain_size = self.commitment_log_domain_size();
        let columns_count = self.committed_columns_count();
        let domain_size = 1usize << log_domain_size;

        let log_n = log_domain_size as usize;
        // The committed backing is the BITREVERSED-order codeword the Merkle
        // builders and query gathers consume; the natural->bitrev LDE produces
        // it directly.
        assert!(
            log_size_supports_natural_to_bitrev_lde(log_n),
            "log_n {log_n} is outside the natural->bitrev LDE range",
        );

        let mut coeff_scratch = context.alloc(domain_size, AllocationPlacement::BestFit)?;
        let stream = context.get_exec_stream();
        let ntt_ctx = context.ntt_device_context();
        let mut current_finest_already_computed = false;
        for column in 0..columns_count {
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
                    if log_n == 20 {
                        hypercube_to_bitreversed_multi_coset_evals_fused_log_n_20(
                            source_column,
                            &mut coeff_scratch[0..domain_size],
                            backing_from_col,
                            self.log_lde_factor as usize,
                            columns_count,
                            stream,
                            context.get_device_properties(),
                        )?;
                        current_finest_already_computed = false;
                        continue;
                    }
                    // Fused boundary first: the hypercube coarse tail, monomial
                    // writeback, coset scale, and the first coset's initial
                    // stages run as one launch. The last tail launch also
                    // performs the NEXT column's hypercube finest pass, so the
                    // next iteration starts at the in-place middle pass.
                    let next_column_hypercube = (column + 1 < columns_count)
                        .then(|| source[offset + domain_size..].as_ptr());
                    let fused = hypercube_to_multi_coset_bitrev_evals_fused(
                        source_column,
                        backing_from_col,
                        log_n,
                        self.log_lde_factor as usize,
                        columns_count,
                        current_finest_already_computed,
                        next_column_hypercube,
                        stream,
                        context.get_device_properties(),
                    )?;
                    if fused {
                        current_finest_already_computed = column + 1 < columns_count;
                        continue;
                    }
                    current_finest_already_computed = false;
                    hypercube_evals_to_monomials(
                        source_column,
                        &mut coeff_scratch[0..domain_size],
                        log_n,
                        stream,
                        context.get_device_properties(),
                    )?;
                    let monomials = DeviceMatrixChunk::new(
                        &coeff_scratch[0..domain_size],
                        domain_size,
                        0,
                        domain_size,
                    );
                    natural_monomials_to_bitreversed_evals_multi_coset(
                        &monomials,
                        backing_from_col,
                        log_n,
                        self.log_lde_factor as usize,
                        columns_count,
                        ntt_ctx,
                        None,
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

    #[doc(hidden)]
    pub fn ensure_cosets_materialized(&mut self, context: &ProverContext) -> CudaResult<()> {
        let log_domain_size = self.commitment_log_domain_size();
        let columns_count = self.committed_columns_count();
        if !self.cosets_materialized {
            if columns_count != 0 {
                assert!(
                    self.raw_hypercube_evals.is_some()
                        || self.opening_raw.is_some()
                        || self.opening_monomials.is_some(),
                    "raw hypercube values are unavailable for coset rematerialization",
                );
            }
            if matches!(&self.cosets, CosetsHolder::None(_)) {
                let instances_count = 1usize << self.log_lde_factor;
                self.cosets = CosetsHolder::Full(allocate_cosets(
                    instances_count,
                    log_domain_size,
                    columns_count,
                    context,
                )?);
            }
            if columns_count == 0 {
                self.cosets_materialized = true;
            } else if let Some(monomials) = self.opening_monomials.take() {
                let matrix = DeviceMatrix::new(&monomials, 1usize << log_domain_size);
                let CosetsHolder::Full(backing) = &mut self.cosets else {
                    unreachable!()
                };
                natural_monomials_to_bitreversed_evals_multi_coset(
                    &matrix,
                    backing,
                    log_domain_size as usize,
                    self.log_lde_factor as usize,
                    columns_count,
                    context.ntt_device_context(),
                    None,
                    context.get_exec_stream(),
                    context.get_device_properties(),
                )?;
                self.cosets_materialized = true;
            } else if let Some(source) = self.opening_raw.take() {
                // Every raw reader has been enqueued on exec. Consuming this
                // owner after the transform schedules needs no copy or wait.
                self.materialize_cosets_from_source(&source, context)?;
            } else {
                self.materialize_cosets_from_owned_hypercube(context)?;
            }
        }
        Ok(())
    }

    /// Call after all raw-evaluation readers have been enqueued. Keep the backing
    /// for a deferred opening, or release it when retained monomials or
    /// materialized cosets already supply the opening representation.
    pub fn finish_raw_batching(&mut self, context: &ProverContext) -> CudaResult<()> {
        if self.opening_monomials.is_some() {
            drop(self.take_raw_hypercube_backing());
        } else if self.defer_opening {
            assert!(self.opening_raw.is_none());
            self.opening_raw = Some(self.take_raw_hypercube_backing());
        } else {
            self.ensure_cosets_materialized(context)?;
            drop(self.take_raw_hypercube_backing());
        }
        Ok(())
    }

    /// Materialize all cosets and build partial trees if no trees are cached.
    pub fn prepare_full_opening(&mut self, context: &ProverContext) -> CudaResult<()> {
        self.ensure_cosets_materialized(context)?;
        if self.committed_columns_count() != 0 && matches!(self.trees, TreesHolder::None) {
            self.trees = TreesHolder::Partial(allocate_trees(
                1usize << self.log_lde_factor,
                self.commitment_log_domain_size() - self.partial_tree_reduction_layers(),
                self.log_rows_per_leaf,
                context,
            )?);
            self.build_and_cache_partial_trees(context)?;
        }
        // Empty oracles never enter the transform; retire their empty owner too.
        self.opening_raw = None;
        Ok(())
    }

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
        if self.is_empty_base_oracle() {
            assert!(dst_u32.is_empty(), "empty base oracle has an empty cap");
            return Ok(());
        }
        let lde_factor = 1usize << self.log_lde_factor;
        let cap_size = 1usize << self.log_tree_cap_size;
        assert_eq!(
            dst_u32.len(),
            cap_size * BLAKE2S_DIGEST_SIZE_U32_WORDS,
            "commit_all_into dst_u32 length must match cap_size * DIGEST_U32_WORDS",
        );

        let log_domain_size = self.commitment_log_domain_size();
        let log_lde_factor = self.log_lde_factor;
        let log_rows_per_leaf = self.log_rows_per_leaf;
        let log_tree_cap_size = self.log_tree_cap_size;
        let columns_count = self.committed_columns_count();
        let stream = context.get_exec_stream();

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
        let reduction_layers = match self.trees {
            TreesHolder::Partial(_) => self.partial_tree_reduction_layers(),
            _ => PARTIAL_TREE_REDUCTION_LAYERS,
        };
        let mut boundary_scratch = match self.trees {
            TreesHolder::Partial(_) => self.allocate_partial_tree_scratch(context)?,
            _ => None,
        };

        match &mut self.trees {
            TreesHolder::Full(backing) => {
                build_full_trees_from_physical(
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
                build_partial_trees_from_physical(
                    evals_backing,
                    backing,
                    log_domain_size,
                    log_lde_factor,
                    log_rows_per_leaf,
                    log_tree_cap_size,
                    columns_count,
                    lde_factor,
                    reduction_layers,
                    boundary_scratch.as_deref_mut(),
                    stream,
                )?;
            }
            TreesHolder::None => {
                let mut tree_tops =
                    allocate_trees(lde_factor, log_domain_size, log_rows_per_leaf, context)?;
                build_full_trees_from_physical(
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

        let trees = match &self.trees {
            TreesHolder::Full(backing) | TreesHolder::Partial(backing) => &backing[..],
            TreesHolder::None => transient_tree_tops.as_ref().unwrap(),
        };
        self.gather_cap(trees, dst_u32, context)
    }

    fn gather_cap(
        &self,
        trees: &DeviceSlice<Digest>,
        dst: &mut DeviceSlice<u32>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let stride = trees.len() >> self.log_lde_factor;
        let cap_size = 1usize << (self.log_tree_cap_size - self.log_lde_factor);
        // Each segment ends with the committed cap followed by a cap-sized
        // unused suffix. The gather writes caps in bit-reversed coset order.
        let offset = stride - 2 * cap_size;
        // SAFETY: offset is within the first tree segment; trees remains owned
        // until all cap reads have been enqueued on exec_stream.
        let cap_ptr = unsafe { trees.as_ptr().add(offset).cast::<u32>() };
        gather_tree_caps_inline(
            cap_ptr,
            (cap_size * BLAKE2S_DIGEST_SIZE_U32_WORDS) as u32,
            (stride * BLAKE2S_DIGEST_SIZE_U32_WORDS) as u32,
            self.log_lde_factor,
            dst,
            context.get_exec_stream(),
        )
    }

    #[doc(hidden)]
    pub fn commit_all(&mut self, context: &ProverContext) -> CudaResult<()> {
        let cap_size = if self.is_empty_base_oracle() {
            0
        } else {
            1usize << self.log_tree_cap_size
        };
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
    #[doc(hidden)]
    pub fn build_and_cache_partial_trees(&mut self, context: &ProverContext) -> CudaResult<()> {
        assert!(
            self.cosets_materialized,
            "cosets must be materialized before building partial trees"
        );
        let log_domain_size = self.commitment_log_domain_size();
        let log_lde_factor = self.log_lde_factor;
        let log_rows_per_leaf = self.log_rows_per_leaf;
        let log_tree_cap_size = self.log_tree_cap_size;
        let columns_count = self.committed_columns_count();
        let instances_count = 1usize << log_lde_factor;
        let stream = context.get_exec_stream();
        let _per_coset_partial_len = self
            .per_coset_tree_len()
            .expect("build_and_cache_partial_trees requires allocated trees");
        let reduction_layers = self.partial_tree_reduction_layers();
        let mut boundary_scratch = self.allocate_partial_tree_scratch(context)?;
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
        build_partial_trees_from_physical(
            evals_backing,
            trees_backing,
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            instances_count,
            reduction_layers,
            boundary_scratch.as_deref_mut(),
            stream,
        )?;
        Ok(())
    }

    #[doc(hidden)]
    pub fn materialize_and_commit_from_hypercube_evals(
        &mut self,
        source: &DeviceSlice<BF>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        self.materialize_from_hypercube_evals(source, context)?;
        self.commit_all(context)
    }

    fn query_leafs_layout(&self, queries_count: usize) -> (usize, usize) {
        let domain_size = 1usize << self.commitment_log_domain_size();
        let values_per_column_count = queries_count << self.log_rows_per_leaf;
        let leafs_len = values_per_column_count * self.committed_columns_count();
        (domain_size, leafs_len)
    }

    fn query_merkle_path_layout(&self, queries_count: usize) -> (u32, usize) {
        if self.is_empty_base_oracle() {
            return (0, 0);
        }
        let layers_count = self.commitment_log_domain_size()
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

    /// Natural-NTT variant of `schedule_query_merkle_paths_into`. The coset
    /// backing holds natural multi-coset NTT output; partial-tree gathers use
    /// pack-inverse addressing to re-hash the bottom layers. Full-tree gathers
    /// do not read cosets. Requires `log_lde_factor == 0` and
    /// `log_rows_per_leaf == 0`.
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
        let log_total_leaves_count = self.commitment_log_domain_size() - self.log_rows_per_leaf;
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
                assert_eq!(
                    self.partial_tree_reduction_layers(),
                    PARTIAL_TREE_REDUCTION_LAYERS,
                    "schedule_query_merkle_paths_into_from_ntt: requires {PARTIAL_TREE_REDUCTION_LAYERS} reduction layers"
                );
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

    #[doc(hidden)]
    pub fn get_query_leafs(
        &mut self,
        coset_index: usize,
        indexes: &DeviceSlice<u32>,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[BF]>> {
        if self.is_empty_base_oracle() {
            // SAFETY: an empty allocation has no elements or stream readers.
            return Ok(unsafe { context.alloc_host_uninit_slice(0) });
        }
        self.ensure_cosets_materialized(context)?;
        let queries_count = indexes.len();
        let (domain_size, leafs_len) = self.query_leafs_layout(queries_count);
        let values = self.get_coset_evaluations(coset_index);
        let values_matrix = DeviceMatrix::new(values, domain_size);
        let stream = context.get_exec_stream();
        let mut d_leafs = context.alloc(leafs_len, AllocationPlacement::BestFit)?;
        let mut leafs_matrix =
            DeviceMatrixMut::new(&mut d_leafs, queries_count << self.log_rows_per_leaf);
        gather_leaf_rows_physical(
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

    #[doc(hidden)]
    pub fn get_query_merkle_paths(
        &mut self,
        coset_index: usize,
        indexes: &DeviceSlice<u32>,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[Digest]>> {
        if self.is_empty_base_oracle() {
            // SAFETY: an empty allocation has no elements or stream readers.
            return Ok(unsafe { context.alloc_host_uninit_slice(0) });
        }
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
                gather_merkle_paths_from_rows_physical(
                    indexes,
                    false,
                    self.get_coset_evaluations(coset_index),
                    self.log_rows_per_leaf,
                    self.committed_columns_count(),
                    tree_bottom,
                    &mut d_merkle_paths,
                    layers_count,
                    self.partial_tree_reduction_layers(),
                    stream,
                )?;
            }
            TreesHolder::None => {
                let values = self.get_coset_evaluations(coset_index);
                let mut tree = allocate_tree(
                    self.commitment_log_domain_size(),
                    self.log_rows_per_leaf,
                    context,
                )?;
                build_full_trees_from_physical(
                    values,
                    &mut tree,
                    self.commitment_log_domain_size(),
                    0,
                    self.log_rows_per_leaf,
                    self.log_tree_cap_size - self.log_lde_factor,
                    self.committed_columns_count(),
                    1,
                    stream,
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

/// Builds all `cosets_in_tile` per-coset Merkle trees from BITREVERSED-order codewords: every leaf
/// is one physically contiguous row block and leaf digests land in physical-block order. The
/// strided bit-reverse canonicalizes them, so the trees equal those of the natural-order codeword.
#[doc(hidden)]
pub fn build_full_trees_from_physical(
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
    assert_ne!(layers_count, 0);
    assert!(per_coset_leaves_count >= 1 << (layers_count - 1));
    hash_leaves_multi_coset_physical(
        evals_backing,
        trees_backing,
        log_rows_per_leaf,
        cosets_in_tile,
        per_coset_leaves_count,
        per_coset_evals_stride,
        per_coset_tree_stride,
        columns_count,
        stream,
    )?;
    {
        let mut leaves = DeviceMatrixChunkMut::new(
            trees_backing,
            per_coset_tree_stride,
            0,
            per_coset_leaves_count,
        );
        bit_reverse_in_place(&mut leaves, stream)?;
    }
    build_merkle_tree_nodes_multi_coset_over_existing_layer(
        trees_backing,
        layers_count - 1,
        cosets_in_tile,
        per_coset_tree_stride,
        /*initial_src_offset_in_coset=*/ 0,
        /*initial_src_layer_count_per_coset=*/ per_coset_leaves_count,
        stream,
    )
}

/// Builds the partial per-coset Merkle trees from BITREVERSED-order codewords. The fused
/// bottom-five-level kernel writes logical level-5 roots, folded to the boundary level when it is
/// deeper, then the ordinary node builder materializes every cached level through the cap; the
/// result and cached query subtree equal those of the natural-order codeword.
#[doc(hidden)]
pub fn build_partial_trees_from_physical(
    evals_backing: &DeviceSlice<BF>,
    tree_backing: &mut DeviceSlice<Digest>,
    log_domain_size: u32,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_tree_cap_size: u32,
    columns_count: usize,
    cosets_in_tile: usize,
    reduction_layers: u32,
    boundary_scratch: Option<&mut DeviceSlice<Digest>>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(log_tree_cap_size >= log_lde_factor);
    let log_coset_tree_cap_size = log_tree_cap_size - log_lde_factor;
    // At equality the bottom reduction layers produce the cap directly.
    assert!(log_domain_size >= log_rows_per_leaf + reduction_layers + log_coset_tree_cap_size);
    let per_coset_evals_stride = columns_count << log_domain_size;
    let per_coset_leaves_count = 1usize << (log_domain_size - log_rows_per_leaf);
    let per_coset_tree_stride = (per_coset_leaves_count << 1) >> reduction_layers;
    assert_eq!(evals_backing.len(), per_coset_evals_stride * cosets_in_tile);
    assert_eq!(tree_backing.len(), per_coset_tree_stride * cosets_in_tile);
    let layers_count =
        log_domain_size + 1 - log_rows_per_leaf - reduction_layers - log_coset_tree_cap_size;
    build_partial_merkle_tree_multi_coset_physical(
        evals_backing,
        tree_backing,
        log_rows_per_leaf,
        layers_count,
        cosets_in_tile,
        reduction_layers,
        boundary_scratch,
        stream,
    )
}

#[cfg(test)]
mod tests;
