use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::{
    build_merkle_tree, build_merkle_tree_nodes, gather_leaf_rows, gather_merkle_paths_device,
    gather_merkle_paths_from_rows, gather_tree_caps_inline, merkle_tree_cap, Digest,
};
use crate::ops::ntt::{
    bitreversed_monomials_to_natural_evals, hypercube_x1_msb_evals_to_x1_msb_monomials,
    log_size_supports_transposed_monomials,
};
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor};
use crate::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use crate::primitives::field::BF;

pub(crate) const PARTIAL_TREE_REDUCTION_LAYERS: u32 = crate::primitives::utils::LOG_WARP_SIZE;

#[derive(Copy, Clone)]
pub(crate) enum TreesCacheMode {
    CacheNone,
    CachePartial,
    CacheFull,
}

pub(crate) enum CosetsHolder<T> {
    Full(Vec<DeviceAllocation<T>>),
    None(std::marker::PhantomData<T>),
}

#[allow(unused)]
pub(crate) enum TreesHolder {
    Full(Vec<DeviceAllocation<Digest>>),
    Partial(Vec<DeviceAllocation<Digest>>),
    None,
}

pub(crate) struct LeafsAndMerklePaths {
    pub leafs: HostAllocation<[BF]>,
    pub merkle_paths: HostAllocation<[Digest]>,
}

#[allow(dead_code)] // Used by the old query workflow and will be wired back into the new prover.
pub(crate) struct LeafsAndMerklePathsAccessors {
    pub leafs: UnsafeAccessor<[BF]>,
    pub merkle_paths: UnsafeAccessor<[Digest]>,
}

impl LeafsAndMerklePaths {
    #[allow(dead_code)] // Used by the old query workflow and will be wired back into the new prover.
    pub(crate) fn get_accessor(&self) -> LeafsAndMerklePathsAccessors {
        LeafsAndMerklePathsAccessors {
            leafs: self.leafs.get_accessor(),
            merkle_paths: self.merkle_paths.get_accessor(),
        }
    }
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

    #[cfg(test)]
    pub(crate) fn take_unified_device_cap(&mut self) -> DeviceAllocation<Digest> {
        self.unified_device_cap
            .take()
            .expect("unified device cap must be materialized before keepalive extraction")
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
            CosetsHolder::Full(evaluations) => &evaluations[coset_index],
            CosetsHolder::None(_) => {
                panic!("cosets not allocated — call ensure_cosets_materialized first")
            }
        }
    }

    #[allow(dead_code)] // Preserved for stage-style workflows that treat coset 0 as the active trace.
    pub(crate) fn get_uninit_coset_evaluations_mut(
        &mut self,
        coset_index: usize,
    ) -> &mut DeviceSlice<T> {
        assert!(coset_index < (1usize << self.log_lde_factor));
        match &mut self.cosets {
            CosetsHolder::Full(evaluations) => &mut evaluations[coset_index],
            CosetsHolder::None(_) => {
                panic!("cosets not allocated — call ensure_cosets_materialized first")
            }
        }
    }

    #[allow(dead_code)] // Preserved for stage-style workflows that treat coset 0 as the active trace.
    pub(crate) fn get_evaluations(&self) -> &DeviceSlice<T> {
        self.get_coset_evaluations(0)
    }

    #[allow(dead_code)] // Preserved for stage-style workflows that treat coset 0 as the active trace.
    pub(crate) fn get_uninit_evaluations_mut(&mut self) -> &mut DeviceSlice<T> {
        self.get_uninit_coset_evaluations_mut(0)
    }

    pub(crate) fn get_uninit_tree_mut(
        &mut self,
        coset_index: usize,
    ) -> Option<&mut DeviceSlice<Digest>> {
        assert!(coset_index < (1usize << self.log_lde_factor));
        match &mut self.trees {
            TreesHolder::Full(trees) => Some(&mut trees[coset_index]),
            TreesHolder::Partial(trees) => Some(&mut trees[coset_index]),
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
                CosetsHolder::Full(cosets) => {
                    for (coset_index, coset) in cosets.iter_mut().enumerate() {
                        let dst_column = &mut coset[offset..offset + domain_size];
                        // "&coeff_scratch" won't deref-coerce all the way to DeviceMatrixChunkImpl
                        // expected by the API, so we insert a manual DeviceSlice coercion first
                        let monomials = &coeff_scratch[0..domain_size];
                        bitreversed_monomials_to_natural_evals(
                            monomials,
                            dst_column,
                            self.log_domain_size as usize,
                            self.log_lde_factor as usize,
                            coset_index,
                            use_transposed_monomials,
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

    /// Commits one coset's per-coset Merkle tree and returns the device pointer
    /// (cast to `*const u32`) at this coset's cap region. The per-coset D2D
    /// from cap region into `unified_device_cap` is no longer performed here —
    /// `commit_all` aggregates every coset's cap region in one
    /// `gather_tree_caps` kernel launch after every per-coset commit has been
    /// scheduled.
    ///
    /// `none_mode_trees` collects the temporary `tree_top` allocations for
    /// `TreesHolder::None`, which are otherwise dropped per-coset. Their cap
    /// region pointers must remain valid until the gather kernel reads them,
    /// so the caller (`commit_all`) keeps the Vec alive across all per-coset
    /// commits and through the gather launch. For `Full` and `Partial` modes
    /// the trees are moved back into `self.trees`, so their lifetimes already
    /// extend past the gather.
    fn commit_per_coset_capture_cap_ptr(
        &mut self,
        coset_index: usize,
        none_mode_trees: &mut Vec<DeviceAllocation<Digest>>,
        context: &ProverContext,
    ) -> CudaResult<u64> {
        let log_domain_size = self.log_domain_size;
        let log_lde_factor = self.log_lde_factor;
        let log_rows_per_leaf = self.log_rows_per_leaf;
        let log_tree_cap_size = self.log_tree_cap_size;
        let columns_count = self.columns_count;
        let stream = context.get_exec_stream();
        let (mut tree_top, mut tree_bottom) = match &mut self.trees {
            TreesHolder::Full(trees) => (trees.remove(coset_index), None),
            TreesHolder::Partial(trees) => (
                allocate_tree(log_domain_size, log_rows_per_leaf, context)?,
                Some(trees.remove(coset_index)),
            ),
            TreesHolder::None => (
                allocate_tree(log_domain_size, log_rows_per_leaf, context)?,
                None,
            ),
        };
        let evaluations = self.get_coset_evaluations(coset_index);
        if let Some(tree_bottom) = &mut tree_bottom {
            commit_trace_with_partial_tree(
                evaluations,
                &mut tree_top,
                tree_bottom,
                log_domain_size,
                log_lde_factor,
                log_rows_per_leaf,
                log_tree_cap_size,
                columns_count,
                stream,
            )?;
        } else {
            commit_trace(
                evaluations,
                &mut tree_top,
                log_domain_size,
                log_lde_factor,
                log_rows_per_leaf,
                log_tree_cap_size,
                columns_count,
                stream,
            )?;
        }
        let log_subtree_cap_size = log_tree_cap_size - log_lde_factor;
        // For `Partial`, the cap is in `tree_bottom`; otherwise it's in `tree_top`.
        let cap_slice: &DeviceSlice<Digest> = if let Some(tb) = tree_bottom.as_ref() {
            merkle_tree_cap(tb, log_subtree_cap_size)
        } else {
            merkle_tree_cap(&tree_top, log_subtree_cap_size)
        };
        // SAFETY: `Digest` is `[u32; 8]`; reading the cap region as `u32` words
        // is reinterpreting the same bytes the `gather_tree_caps` kernel will
        // read. The pointer is captured as a numeric value here; lifetime of
        // the underlying allocation is enforced by stashing `tree_top` (None
        // mode) or by `self.trees` (Full / Partial), which outlive the kernel.
        let cap_ptr = unsafe { cap_slice.transmute::<u32>() }.as_ptr() as u64;
        match &mut self.trees {
            TreesHolder::Full(trees) => trees.insert(coset_index, tree_top),
            TreesHolder::Partial(trees) => {
                trees.insert(coset_index, tree_bottom.unwrap());
                // tree_top drops here — temp working buffer in Partial mode.
            }
            TreesHolder::None => {
                // Stash the temp tree_top so its cap region pointer stays
                // valid until the gather kernel reads it. Local-Vec lifetime
                // ≤ caller `commit_all`'s frame, which schedules the gather
                // before returning.
                none_mode_trees.push(tree_top);
            }
        };
        Ok(cap_ptr)
    }

    pub(crate) fn commit_all(&mut self, context: &ProverContext) -> CudaResult<()> {
        self.ensure_cosets_materialized(context)?;
        let cap_size = 1usize << self.log_tree_cap_size;
        let unified_cap: DeviceAllocation<Digest> =
            context.alloc(cap_size, AllocationPlacement::BestFit)?;
        assert!(self.unified_device_cap.replace(unified_cap).is_none());

        let lde_factor = 1usize << self.log_lde_factor;
        let log_subtree_cap_size = self.log_tree_cap_size - self.log_lde_factor;
        let per_coset_cap_size = 1usize << log_subtree_cap_size;

        // Local owned tree allocations for `TreesHolder::None` commits, kept
        // alive across all per-coset commits and through the gather launch.
        // For `Full` and `Partial`, the trees are stored on `self.trees` and
        // outlive the gather automatically.
        let mut none_mode_trees: Vec<DeviceAllocation<Digest>> = Vec::new();
        // Per-coset cap region device pointers, in canonical bit-reversed
        // coset order — `src_ptrs_host[stage1_pos] = cap_ptr_for(coset_index)`
        // where `stage1_pos = bitreverse_index(coset_index)`.
        let mut src_ptrs_host: Vec<u64> = vec![0u64; lde_factor];
        for coset_index in 0..lde_factor {
            let cap_ptr =
                self.commit_per_coset_capture_cap_ptr(coset_index, &mut none_mode_trees, context)?;
            let stage1_pos = bitreverse_index(coset_index, self.log_lde_factor);
            src_ptrs_host[stage1_pos] = cap_ptr;
        }

        // Single inline-descriptor kernel launch replaces the per-coset cap
        // D2Ds. The pointer table rides as `__grid_constant__` kernel-arg
        // data (see `gather_tree_caps_inline`), so no pre-launch H2D is
        // needed — `prove()`-time H2Ds would otherwise serialize against
        // the parallel pre-prove H2Ds uploading the next proof's trace.
        let stream = context.get_exec_stream();
        let cap_words_per_coset = (per_coset_cap_size * BLAKE2S_DIGEST_SIZE_U32_WORDS) as u32;
        let unified_cap = self
            .unified_device_cap
            .as_mut()
            .expect("unified_device_cap was just placed above");
        // SAFETY: `unified_cap` is `[Digest]`; the gather kernel writes
        // `lde_factor * cap_words_per_coset` u32 words = `cap_size *
        // BLAKE2S_DIGEST_SIZE_U32_WORDS` words = the full unified-cap byte
        // range. The `Digest` (== `[u32; 8]`) and `u32` share alignment.
        let dst_u32 = unsafe { unified_cap.transmute_mut::<u32>() };
        gather_tree_caps_inline(&src_ptrs_host, dst_u32, cap_words_per_coset, stream)?;

        // `none_mode_trees` drops at end of scope — its pool free is
        // exec-stream-ordered after the gather, so it is safe to drop here.
        drop(none_mode_trees);
        Ok(())
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
        for coset_index in 0..instances_count {
            let mut tree_top = allocate_tree(log_domain_size, log_rows_per_leaf, context)?;
            let mut tree_bottom = match &mut self.trees {
                TreesHolder::Partial(trees) => trees.remove(coset_index),
                _ => panic!("build_and_cache_partial_trees requires TreesHolder::Partial"),
            };
            let evaluations = self.get_coset_evaluations(coset_index);
            commit_trace_with_partial_tree(
                evaluations,
                &mut tree_top,
                &mut tree_bottom,
                log_domain_size,
                log_lde_factor,
                log_rows_per_leaf,
                log_tree_cap_size,
                columns_count,
                stream,
            )?;
            match &mut self.trees {
                TreesHolder::Partial(trees) => trees.insert(coset_index, tree_bottom),
                _ => unreachable!(),
            };
            // tree_top drops here — frees temporary full-tree allocation
        }
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
        memory_copy_async(
            unsafe { leafs.get_mut_accessor().get_mut() },
            &d_leafs,
            stream,
        )?;
        Ok(leafs)
    }

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
            TreesHolder::Full(trees) => {
                let tree = &trees[coset_index];
                gather_merkle_paths_device(
                    indexes,
                    tree,
                    &mut d_merkle_paths,
                    layers_count,
                    stream,
                )?;
            }
            TreesHolder::Partial(trees) => {
                let tree_bottom = &trees[coset_index];
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
        memory_copy_async(
            unsafe { merkle_paths.get_mut_accessor().get_mut() },
            &d_merkle_paths,
            stream,
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

pub(crate) fn allocate_coset<T>(
    log_domain_size: u32,
    columns_count: usize,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<T>> {
    context.alloc(
        columns_count << log_domain_size,
        AllocationPlacement::Bottom,
    )
}

fn allocate_cosets<T>(
    instances_count: usize,
    log_domain_size: u32,
    columns_count: usize,
    context: &ProverContext,
) -> CudaResult<Vec<DeviceAllocation<T>>> {
    let mut result = Vec::with_capacity(instances_count);
    for _ in 0..instances_count {
        result.push(allocate_coset(log_domain_size, columns_count, context)?);
    }
    Ok(result)
}

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
) -> CudaResult<Vec<DeviceAllocation<Digest>>> {
    let mut result = Vec::with_capacity(instances_count);
    for _ in 0..instances_count {
        result.push(allocate_tree(log_domain_size, log_rows_per_leaf, context)?);
    }
    Ok(result)
}

pub(crate) fn commit_trace(
    lde: &DeviceSlice<BF>,
    tree: &mut DeviceSlice<Digest>,
    log_domain_size: u32,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_tree_cap_size: u32,
    columns_count: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(lde.len() & ((1 << log_domain_size) - 1), 0);
    assert!(log_tree_cap_size >= log_lde_factor);
    let log_coset_tree_cap_size = log_tree_cap_size - log_lde_factor;
    assert!(log_domain_size >= (log_rows_per_leaf + log_coset_tree_cap_size));
    let tree_len = 1 << (log_domain_size + 1 - log_rows_per_leaf);
    assert_eq!(tree.len(), tree_len);
    let layers_count = log_domain_size + 1 - log_rows_per_leaf - log_coset_tree_cap_size;
    build_merkle_tree(
        &lde[..columns_count << log_domain_size],
        tree,
        log_rows_per_leaf,
        stream,
        layers_count,
        false,
    )
}

pub(crate) fn commit_trace_with_partial_tree(
    lde: &DeviceSlice<BF>,
    tree_top: &mut DeviceSlice<Digest>,
    tree_bottom: &mut DeviceSlice<Digest>,
    log_domain_size: u32,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_tree_cap_size: u32,
    columns_count: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(lde.len() & ((1 << log_domain_size) - 1), 0);
    assert!(log_tree_cap_size >= log_lde_factor);
    let log_coset_tree_cap_size = log_tree_cap_size - log_lde_factor;
    assert!(
        log_domain_size
            > (log_rows_per_leaf + PARTIAL_TREE_REDUCTION_LAYERS + log_coset_tree_cap_size)
    );
    let tree_top_len = 1 << (log_domain_size + 1 - log_rows_per_leaf);
    assert_eq!(tree_top.len(), tree_top_len);
    let tree_bottom_len = tree_top_len >> PARTIAL_TREE_REDUCTION_LAYERS;
    assert_eq!(tree_bottom.len(), tree_bottom_len);
    build_merkle_tree(
        &lde[..columns_count << log_domain_size],
        tree_top,
        log_rows_per_leaf,
        stream,
        PARTIAL_TREE_REDUCTION_LAYERS,
        false,
    )?;
    let bottom_layers_count = log_domain_size + 1
        - log_rows_per_leaf
        - PARTIAL_TREE_REDUCTION_LAYERS
        - log_coset_tree_cap_size;
    let values = &tree_top[tree_top_len - 2 * tree_bottom_len..][..tree_bottom_len];
    build_merkle_tree_nodes(values, tree_bottom, bottom_layers_count, stream)
}

pub(crate) fn bitreverse_index(index: usize, num_bits: u32) -> usize {
    if num_bits == 0 {
        0
    } else {
        index.reverse_bits() >> (usize::BITS - num_bits)
    }
}

#[cfg(test)]
mod test;
