//! Per-coset witness commitment and query-time openings with retained monomials
//! or in-place transforms.

use super::*;
use gpu_hash::blake2s::{
    gather_leaves_for_queries_single_coset_physical,
    gather_merkle_paths_partial_for_queries_single_coset_physical,
};
use gpu_ntt::ntt::{
    coset_to_monomials_in_place, hypercube_to_coset_in_place,
    hypercube_to_retained_monomials_and_coset, hypercube_to_retained_monomials_and_coset_in_place,
    monomials_to_coset_in_place, monomials_to_hypercube_in_place, retained_monomials_to_coset,
};

impl TraceHolder<BF> {
    /// All coset readers must be enqueued on exec before reusing the workspace.
    pub fn gather_openings_recomputed(
        &mut self,
        queries: &DeviceSlice<u32>,
        leaves: &mut DeviceSlice<BF>,
        paths: &mut DeviceSlice<u32>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(!self.cosets_materialized);
        assert!(matches!(self.cosets, CosetsHolder::None(_)));
        assert!(matches!(
            self.trees,
            TreesHolder::None | TreesHolder::Partial(_)
        ));
        assert_ne!(self.opening_policy, OpeningPolicy::FullMaterialization);
        if self.columns_count == 0 || queries.is_empty() {
            return Ok(());
        }
        let in_place = self.opening_policy == OpeningPolicy::InPlace;
        let already_monomials = self.opening_monomials.is_some();
        let mut monomials = self
            .opening_monomials
            .take()
            .or_else(|| self.opening_raw.take())
            .expect("initial batching must transfer an opening source");
        let log_n = self.log_domain_size;
        let log_f = self.log_lde_factor;
        let log_subtree_cap = self.log_tree_cap_size - log_f;
        let layers = log_n - self.log_rows_per_leaf - log_subtree_cap;
        let mut workspace = if in_place {
            None
        } else {
            Some(context.alloc(monomials.len(), AllocationPlacement::BestFit)?)
        };
        let mut previous_coset = None;
        let mut temporary_tree = if matches!(self.trees, TreesHolder::None) {
            Some(allocate_trees(
                1,
                log_n - PARTIAL_TREE_REDUCTION_LAYERS,
                self.log_rows_per_leaf,
                context,
            )?)
        } else {
            None
        };
        let stream = context.get_exec_stream();
        let properties = context.get_device_properties();
        let first_coset = usize::from(log_f != 0);
        for (iteration, coset_index) in std::iter::once(first_coset)
            .chain((0..1usize << log_f).filter(|&c| c != first_coset))
            .enumerate()
        {
            if let Some(coset) = workspace.as_mut() {
                if iteration == 0 && !already_monomials {
                    hypercube_to_retained_monomials_and_coset_in_place(
                        &mut monomials,
                        coset,
                        log_n as usize,
                        log_f as usize,
                        coset_index,
                        properties,
                        stream,
                    )?;
                } else {
                    retained_monomials_to_coset(
                        &monomials,
                        coset,
                        log_n as usize,
                        log_f as usize,
                        coset_index,
                        properties,
                        stream,
                    )?;
                }
            } else {
                if let Some(previous) = previous_coset {
                    coset_to_monomials_in_place(
                        &mut monomials,
                        log_n as usize,
                        log_f as usize,
                        previous,
                        properties,
                        stream,
                    )?;
                }
                if iteration == 0 && !already_monomials {
                    hypercube_to_coset_in_place(
                        &mut monomials,
                        log_n as usize,
                        log_f as usize,
                        coset_index,
                        properties,
                        stream,
                    )?;
                } else {
                    monomials_to_coset_in_place(
                        &mut monomials,
                        log_n as usize,
                        log_f as usize,
                        coset_index,
                        properties,
                        stream,
                    )?;
                }
                previous_coset = Some(coset_index);
            }
            let coset = match workspace.as_ref() {
                Some(workspace) => &workspace[..],
                None => &monomials[..],
            };
            let tree = if let Some(tree) = temporary_tree.as_mut() {
                // This buffer contains one coset, whose cap is smaller than
                // the complete oracle cap by the global LDE factor.
                build_partial_trees_from_physical(
                    coset,
                    tree,
                    log_n,
                    0,
                    self.log_rows_per_leaf,
                    log_subtree_cap,
                    self.columns_count,
                    1,
                    stream,
                )?;
                &tree[..]
            } else {
                self.get_tree_slice(coset_index)
                    .expect("cached partial tree")
            };
            gather_leaves_for_queries_single_coset_physical(
                coset,
                coset_index as u32,
                log_f,
                log_n,
                self.log_rows_per_leaf,
                queries,
                leaves,
                stream,
            )?;
            gather_merkle_paths_partial_for_queries_single_coset_physical(
                coset,
                tree,
                coset_index as u32,
                log_f,
                log_n,
                self.log_rows_per_leaf,
                layers,
                queries,
                paths,
                stream,
            )?;
        }
        Ok(())
    }

    /// Commit one coset at a time, preserving raw evaluations for GKR and true
    /// monomials for WHIR. The only coset workspace is released on return.
    pub fn commit_retaining_monomials(
        &mut self,
        cap_dst: Option<&mut DeviceSlice<u32>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        if let Some(dst) = cap_dst {
            return self.commit_retaining_monomials_into(dst, context);
        }
        let mut cap = context.alloc::<Digest>(
            1usize << self.log_tree_cap_size,
            AllocationPlacement::Bottom,
        )?;
        // SAFETY: Digest consists of eight u32 words; this exclusive view spans
        // the live cap allocation and is written only by exec-stream kernels.
        let dst = unsafe { cap[..].transmute_mut::<u32>() };
        self.commit_retaining_monomials_into(dst, context)?;
        self.unified_device_cap = Some(cap);
        Ok(())
    }

    fn commit_retaining_monomials_into(
        &mut self,
        cap_dst: &mut DeviceSlice<u32>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(matches!(self.cosets, CosetsHolder::None(_)));
        assert!(matches!(self.trees, TreesHolder::Partial(_)));
        assert!(self.opening_monomials.is_none());
        let source = self.raw_hypercube_backing();
        let log_n = self.log_domain_size;
        let log_f = self.log_lde_factor;
        let log_rows = self.log_rows_per_leaf;
        let log_subcap = self.log_tree_cap_size - log_f;
        let columns = self.columns_count;
        assert!(columns != 0);
        let mut monomials = context.alloc(source.len(), AllocationPlacement::Bottom)?;
        let mut coset = context.alloc(source.len(), AllocationPlacement::BestFit)?;
        let stream = context.get_exec_stream();
        let properties = context.get_device_properties();
        let first_coset = usize::from(log_f != 0);
        for (iteration, index) in std::iter::once(first_coset)
            .chain((0..1usize << log_f).filter(|&c| c != first_coset))
            .enumerate()
        {
            if iteration == 0 {
                hypercube_to_retained_monomials_and_coset(
                    &source,
                    &mut monomials,
                    &mut coset,
                    log_n as usize,
                    log_f as usize,
                    index,
                    properties,
                    stream,
                )?;
            } else {
                retained_monomials_to_coset(
                    &monomials,
                    &mut coset,
                    log_n as usize,
                    log_f as usize,
                    index,
                    properties,
                    stream,
                )?;
            }
            let tree = self
                .get_uninit_tree_mut(index)
                .expect("partial tree allocated");
            build_partial_trees_from_physical(
                &coset, tree, log_n, 0, log_rows, log_subcap, columns, 1, stream,
            )?;
        }
        self.gather_cached_cap(cap_dst, context)?;
        self.opening_monomials = Some(monomials);
        Ok(())
    }

    fn gather_cached_cap(
        &self,
        cap_dst: &mut DeviceSlice<u32>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let log_f = self.log_lde_factor;
        let log_subcap = self.log_tree_cap_size - log_f;
        let stream = context.get_exec_stream();
        let stride = self.per_coset_tree_len().unwrap();
        let cap_size = 1usize << log_subcap;
        let offset = stride - 2 * cap_size;
        let tree = self.get_consolidated_tree().unwrap();
        // SAFETY: each cap lies in the initialized suffix of its tree segment;
        // the consolidated tree remains owned through the cap gather enqueue.
        let cap_ptr = unsafe { tree.as_ptr().add(offset).cast::<u32>() };
        gather_tree_caps_inline(
            cap_ptr,
            (cap_size * 8) as u32,
            (stride * 8) as u32,
            log_f,
            cap_dst,
            stream,
        )?;
        Ok(())
    }

    /// Commit through the raw allocation, then restore raw evaluations for
    /// GKR. No monomial or coset allocation survives (or supplements) this slab.
    pub fn commit_in_place(
        &mut self,
        cap_dst: Option<&mut DeviceSlice<u32>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        if let Some(dst) = cap_dst {
            return self.commit_in_place_into(dst, context);
        }
        let mut cap = context.alloc::<Digest>(
            1usize << self.log_tree_cap_size,
            AllocationPlacement::Bottom,
        )?;
        // SAFETY: the exclusive u32 view spans exactly the eight words of each
        // Digest; exec-stream cap gather is its only writer.
        let dst = unsafe { cap[..].transmute_mut::<u32>() };
        self.commit_in_place_into(dst, context)?;
        self.unified_device_cap = Some(cap);
        Ok(())
    }

    fn commit_in_place_into(
        &mut self,
        cap_dst: &mut DeviceSlice<u32>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(matches!(self.cosets, CosetsHolder::None(_)));
        assert!(matches!(self.trees, TreesHolder::Partial(_)));
        assert!(self.opening_monomials.is_none());
        let mut values = self.take_raw_hypercube_backing();
        let log_n = self.log_domain_size;
        let log_f = self.log_lde_factor;
        let log_rows = self.log_rows_per_leaf;
        let log_subcap = self.log_tree_cap_size - log_f;
        let columns = self.columns_count;
        assert!(columns != 0);
        let stream = context.get_exec_stream();
        let properties = context.get_device_properties();
        let first_coset = usize::from(log_f != 0);
        let mut previous = first_coset;
        for (iteration, index) in std::iter::once(first_coset)
            .chain((0..1usize << log_f).filter(|&c| c != first_coset))
            .enumerate()
        {
            if iteration == 0 {
                hypercube_to_coset_in_place(
                    &mut values,
                    log_n as usize,
                    log_f as usize,
                    index,
                    properties,
                    stream,
                )?;
            } else {
                coset_to_monomials_in_place(
                    &mut values,
                    log_n as usize,
                    log_f as usize,
                    previous,
                    properties,
                    stream,
                )?;
                monomials_to_coset_in_place(
                    &mut values,
                    log_n as usize,
                    log_f as usize,
                    index,
                    properties,
                    stream,
                )?;
            }
            let tree = self
                .get_uninit_tree_mut(index)
                .expect("partial tree allocated");
            build_partial_trees_from_physical(
                &values, tree, log_n, 0, log_rows, log_subcap, columns, 1, stream,
            )?;
            previous = index;
        }
        self.gather_cached_cap(cap_dst, context)?;
        // The final tree reader is queued before overwriting the last coset.
        coset_to_monomials_in_place(
            &mut values,
            log_n as usize,
            log_f as usize,
            previous,
            properties,
            stream,
        )?;
        monomials_to_hypercube_in_place(&mut values, log_n as usize, properties, stream)?;
        self.raw_hypercube_evals = Some(std::sync::Arc::new(values));
        Ok(())
    }
}
