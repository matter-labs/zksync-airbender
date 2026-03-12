use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use itertools::Itertools;
use prover::merkle_trees::MerkleTreeCapVarLength;
use prover::prover_stages::Transcript;
use prover::transcript::Seed;

use crate::allocator::tracker::AllocationPlacement;
use crate::ntt::{
    bitreversed_coeffs_to_natural_coset, hypercube_evals_natural_to_bitreversed_coeffs,
};
use crate::ops::blake2s::{
    build_merkle_tree, build_merkle_tree_nodes, gather_leaf_rows, gather_merkle_paths_device,
    gather_rows_and_merkle_paths, merkle_tree_cap, Digest,
};
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor};
use crate::primitives::device_structures::{DeviceMatrix, DeviceMatrixImpl, DeviceMatrixMut};
use crate::primitives::field::BF;

pub const PARTIAL_TREE_REDUCTION_LAYERS: u32 = crate::primitives::utils::LOG_WARP_SIZE;

#[derive(Copy, Clone)]
pub enum TreesCacheMode {
    CacheNone,
    CachePartial,
    CacheFull,
}

pub(crate) enum CosetsHolder<T> {
    Full(Vec<DeviceAllocation<T>>),
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
    pub(crate) tree_caps: Option<Vec<HostAllocation<[Digest]>>>,
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
            tree_caps: None,
        })
    }

    pub(crate) fn get_tree_caps_accessors(&self) -> Vec<UnsafeAccessor<[Digest]>> {
        self.tree_caps
            .as_ref()
            .expect("tree caps must be materialized before access")
            .iter()
            .map(HostAllocation::get_accessor)
            .collect_vec()
    }

    pub(crate) fn get_tree_caps(&self) -> Vec<MerkleTreeCapVarLength> {
        let tree_caps_accessors = self.get_tree_caps_accessors();
        get_tree_caps_for_accessors(&tree_caps_accessors, self.log_lde_factor)
    }

    #[allow(dead_code)] // Preserved for transcript-commit flows mirrored from gpu_prover_old.
    fn flatten_tree_caps(&self) -> Vec<u32> {
        let tree_caps_accessors = self.get_tree_caps_accessors();
        flatten_tree_caps_for_accessors(&tree_caps_accessors, self.log_lde_factor)
    }

    #[allow(dead_code)] // Preserved for transcript-commit flows mirrored from gpu_prover_old.
    pub(crate) fn get_update_seed_fn(&self, seed: &mut HostAllocation<Seed>) -> impl Fn() {
        let seed_accessor = seed.get_mut_accessor();
        let input = self.flatten_tree_caps();
        move || unsafe { Transcript::commit_with_seed(seed_accessor.get_mut(), &input) }
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

    pub(crate) fn get_coset_evaluations(&self, coset_index: usize) -> &DeviceSlice<T> {
        assert!(coset_index < (1usize << self.log_lde_factor));
        assert!(
            self.cosets_materialized,
            "coset evaluations must be materialized before access"
        );
        match &self.cosets {
            CosetsHolder::Full(evaluations) => &evaluations[coset_index],
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

    pub(crate) fn clone_tree_caps_from_host(
        &mut self,
        source: &[HostAllocation<[Digest]>],
        context: &ProverContext,
    ) {
        assert_eq!(source.len(), 1usize << self.log_lde_factor);
        let mut caps = allocate_tree_caps(self.log_lde_factor, self.log_tree_cap_size, context);
        for (src, dst) in source.iter().zip(caps.iter_mut()) {
            unsafe {
                dst.get_mut_accessor()
                    .get_mut()
                    .copy_from_slice(src.get_accessor().get());
            }
        }
        assert!(self.tree_caps.replace(caps).is_none());
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
        for column in 0..self.columns_count {
            let offset = column * domain_size;
            let source_column = &source[offset..offset + domain_size];
            hypercube_evals_natural_to_bitreversed_coeffs(
                source_column,
                &mut coeff_scratch,
                self.log_domain_size as usize,
                stream,
            )?;

            match &mut self.cosets {
                CosetsHolder::Full(cosets) => {
                    for (coset_index, coset) in cosets.iter_mut().enumerate() {
                        let dst_column = &mut coset[offset..offset + domain_size];
                        bitreversed_coeffs_to_natural_coset(
                            &coeff_scratch,
                            dst_column,
                            self.log_domain_size as usize,
                            self.log_lde_factor as usize,
                            coset_index,
                            stream,
                        )?;
                    }
                }
            }
        }
        self.cosets_materialized = true;
        Ok(())
    }

    pub(crate) fn ensure_cosets_materialized(&mut self, context: &ProverContext) -> CudaResult<()> {
        if !self.cosets_materialized {
            self.materialize_cosets_from_owned_hypercube(context)?;
        }
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

    fn commit_and_transfer_tree_caps(
        &mut self,
        coset_index: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
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
        let tree = if let Some(tree_bottom) = &mut tree_bottom {
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
            tree_bottom
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
            &mut tree_top
        };
        let caps = &mut self.tree_caps.as_mut().unwrap()[coset_index];
        transfer_tree_cap(tree, caps, log_lde_factor, log_tree_cap_size, stream)?;
        match &mut self.trees {
            TreesHolder::Full(trees) => trees.insert(coset_index, tree_top),
            TreesHolder::Partial(trees) => {
                trees.insert(coset_index, tree_bottom.unwrap());
            }
            TreesHolder::None => {}
        };
        Ok(())
    }

    pub(crate) fn commit_all(&mut self, context: &ProverContext) -> CudaResult<()> {
        self.ensure_cosets_materialized(context)?;
        let tree_caps = allocate_tree_caps(self.log_lde_factor, self.log_tree_cap_size, context);
        assert!(self.tree_caps.replace(tree_caps).is_none());
        for coset_index in 0..(1usize << self.log_lde_factor) {
            self.commit_and_transfer_tree_caps(coset_index, context)?;
        }
        Ok(())
    }

    pub(crate) fn materialize_and_commit_from_hypercube_evals(
        &mut self,
        source: &DeviceSlice<BF>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        self.materialize_from_hypercube_evals(source, context)?;
        self.commit_all(context)
    }

    pub fn get_leafs_and_merkle_paths(
        &mut self,
        coset_index: usize,
        indexes: &DeviceSlice<u32>,
        context: &ProverContext,
    ) -> CudaResult<LeafsAndMerklePaths> {
        self.ensure_cosets_materialized(context)?;
        let queries_count = indexes.len();
        let log_domain_size = self.log_domain_size;
        let log_rows_per_index = self.log_rows_per_leaf;
        let domain_size = 1 << log_domain_size;
        let values = self.get_coset_evaluations(coset_index);
        let values_matrix = DeviceMatrix::new(values, domain_size);
        let columns_count = values_matrix.cols();
        let values_per_column_count = queries_count << log_rows_per_index;
        let leafs_len = values_per_column_count * columns_count;
        let layers_count = log_domain_size
            - self.log_rows_per_leaf
            - (self.log_tree_cap_size - self.log_lde_factor);
        let digests_len = queries_count * layers_count as usize;
        let stream = context.get_exec_stream();
        let mut d_leafs = context.alloc(leafs_len, AllocationPlacement::BestFit)?;
        let mut leafs_matrix = DeviceMatrixMut::new(&mut d_leafs, values_per_column_count);
        let mut d_merkle_paths = context.alloc(digests_len, AllocationPlacement::BestFit)?;
        match &self.trees {
            TreesHolder::Full(trees) => {
                // Full-tree queries work in the natural per-coset leaf index space. They still
                // need leaf-aware row extraction, but can read all Merkle layers directly from the
                // cached tree without the fused partial-tree path.
                gather_leaf_rows(
                    indexes,
                    false,
                    log_rows_per_index,
                    &values_matrix,
                    &mut leafs_matrix,
                    stream,
                )?;
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
                gather_rows_and_merkle_paths(
                    indexes,
                    false,
                    values,
                    log_rows_per_index,
                    &mut leafs_matrix,
                    tree_bottom,
                    &mut d_merkle_paths,
                    layers_count,
                    stream,
                )?;
            }
            TreesHolder::None => {
                gather_leaf_rows(
                    indexes,
                    false,
                    log_rows_per_index,
                    &values_matrix,
                    &mut leafs_matrix,
                    stream,
                )?;
                let mut tree =
                    allocate_tree(self.log_domain_size, self.log_rows_per_leaf, context)?;
                build_merkle_tree(
                    values,
                    &mut tree,
                    log_rows_per_index,
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
        let mut leafs = unsafe { context.alloc_host_uninit_slice(leafs_len) };
        memory_copy_async(
            unsafe { leafs.get_mut_accessor().get_mut() },
            &d_leafs,
            stream,
        )?;
        let mut merkle_paths = unsafe { context.alloc_host_uninit_slice(digests_len) };
        memory_copy_async(
            unsafe { merkle_paths.get_mut_accessor().get_mut() },
            &d_merkle_paths,
            stream,
        )?;
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

fn allocate_trees(
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

pub(crate) fn allocate_tree_caps(
    log_lde_factor: u32,
    log_tree_cap_size: u32,
    context: &ProverContext,
) -> Vec<HostAllocation<[Digest]>> {
    let lde_factor = 1 << log_lde_factor;
    let log_coset_tree_cap_size = log_tree_cap_size - log_lde_factor;
    let coset_tree_cap_size = 1 << log_coset_tree_cap_size;
    let mut result = Vec::with_capacity(lde_factor);
    for _ in 0..lde_factor {
        result.push(unsafe { context.alloc_host_uninit_slice(coset_tree_cap_size) });
    }
    result
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

pub(crate) fn transfer_tree_cap(
    tree: &DeviceSlice<Digest>,
    cap: &mut HostAllocation<[Digest]>,
    log_lde_factor: u32,
    log_tree_cap_size: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let log_subtree_cap_size = log_tree_cap_size - log_lde_factor;
    let d_cap = merkle_tree_cap(tree, log_subtree_cap_size);
    memory_copy_async(unsafe { cap.get_mut_accessor().get_mut() }, d_cap, stream)
}

fn bitreverse_index(index: usize, num_bits: u32) -> usize {
    if num_bits == 0 {
        0
    } else {
        index.reverse_bits() >> (usize::BITS - num_bits)
    }
}

#[allow(dead_code)] // Preserved for transcript-commit flows mirrored from gpu_prover_old.
fn flatten_tree_caps_for_accessors(
    accessors: &[UnsafeAccessor<[Digest]>],
    log_lde_factor: u32,
) -> Vec<u32> {
    let lde_factor = 1usize << log_lde_factor;
    assert_eq!(accessors.len(), lde_factor);
    let mut result = Vec::with_capacity(
        accessors
            .iter()
            .map(|accessor| unsafe {
                accessor.get().len() * core::mem::size_of::<Digest>() / core::mem::size_of::<u32>()
            })
            .sum(),
    );
    for stage1_pos in 0..lde_factor {
        let natural_coset_index = bitreverse_index(stage1_pos, log_lde_factor);
        for digest in unsafe { accessors[natural_coset_index].get() }.iter() {
            result.extend_from_slice(digest);
        }
    }

    result
}

#[allow(dead_code)] // Preserved for transcript-commit flows mirrored from gpu_prover_old.
pub(crate) fn flatten_tree_caps(
    accessors: &[UnsafeAccessor<[Digest]>],
    log_lde_factor: u32,
) -> Vec<u32> {
    flatten_tree_caps_for_accessors(accessors, log_lde_factor)
}

fn get_tree_caps_for_accessors(
    accessors: &[UnsafeAccessor<[Digest]>],
    log_lde_factor: u32,
) -> Vec<MerkleTreeCapVarLength> {
    let lde_factor = 1usize << log_lde_factor;
    assert_eq!(accessors.len(), lde_factor);
    (0..lde_factor)
        .map(|stage1_pos| {
            let natural_coset_index = bitreverse_index(stage1_pos, log_lde_factor);
            let cap = unsafe { accessors[natural_coset_index].get().to_vec() };
            MerkleTreeCapVarLength { cap }
        })
        .collect_vec()
}

#[allow(dead_code)] // Preserved for transcript-commit flows mirrored from gpu_prover_old.
pub(crate) fn get_tree_caps(
    accessors: &[UnsafeAccessor<[Digest]>],
    log_lde_factor: u32,
) -> Vec<MerkleTreeCapVarLength> {
    get_tree_caps_for_accessors(accessors, log_lde_factor)
}

#[cfg(test)]
mod test {
    use std::alloc::Global;

    use blake2s_u32::{Blake2sState, BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS};
    use era_cudart::memory::memory_copy;
    use field::{Field, PrimeField};
    use prover::gkr::whir::hypercube_to_monomial::multivariate_coeffs_into_hypercube_evals;
    use prover::merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap;
    use prover::merkle_trees::ColumnMajorMerkleTreeConstructor;
    use serial_test::serial;
    use worker::Worker;

    use super::*;
    use crate::allocator::tracker::AllocationPlacement;
    use crate::prover::test_utils::make_test_context;

    fn cpu_all_cosets(coeffs: &[BF], log_lde_factor: u32, worker: &Worker) -> Vec<Vec<BF>> {
        let n = coeffs.len();
        let log_n = n.trailing_zeros();
        let twiddles = fft::Twiddles::<BF, Global>::new(n, worker);
        let selected_twiddles = &twiddles.forward_twiddles[..(n >> 1)];
        let tau = fft::domain_generator_for_size::<BF>(1u64 << (log_n + log_lde_factor));
        let mut result = Vec::with_capacity(1 << log_lde_factor);
        for coset_index in 0..(1usize << log_lde_factor) {
            let mut evals = coeffs.to_vec();
            if coset_index != 0 {
                fft::distribute_powers_serial(&mut evals, BF::ONE, tau.pow(coset_index as u32));
            }
            fft::bitreverse_enumeration_inplace(&mut evals);
            fft::naive::serial_ct_ntt_bitreversed_to_natural(&mut evals, log_n, selected_twiddles);
            result.push(evals);
        }
        result
    }

    fn make_source_host_and_cpu_cosets(
        log_domain_size: u32,
        log_lde_factor: u32,
        columns_count: usize,
        worker: &Worker,
    ) -> (Vec<BF>, Vec<Vec<BF>>) {
        let domain_size = 1usize << log_domain_size;
        let lde_factor = 1usize << log_lde_factor;
        let mut cpu_columns = Vec::with_capacity(columns_count);
        let mut source_host = vec![BF::ZERO; columns_count * domain_size];
        for column in 0..columns_count {
            let coeffs = (0..domain_size)
                .map(|idx| BF::new((1 + column * domain_size + idx) as u32))
                .collect_vec();
            let mut source_column = coeffs.clone();
            multivariate_coeffs_into_hypercube_evals(&mut source_column, log_domain_size);
            fft::bitreverse_enumeration_inplace(&mut source_column);
            source_host[column * domain_size..(column + 1) * domain_size]
                .copy_from_slice(&source_column);
            cpu_columns.push(coeffs);
        }

        let mut cpu_cosets = vec![vec![BF::ZERO; columns_count * domain_size]; lde_factor];
        for (column_idx, coeffs) in cpu_columns.iter().enumerate() {
            for (coset_idx, coset) in cpu_all_cosets(coeffs, log_lde_factor, worker)
                .into_iter()
                .enumerate()
            {
                cpu_cosets[coset_idx][column_idx * domain_size..(column_idx + 1) * domain_size]
                    .copy_from_slice(&coset);
            }
        }

        (source_host, cpu_cosets)
    }

    fn stage1_caps_from_cpu_cosets(
        cpu_cosets: &[Vec<BF>],
        domain_size: usize,
        columns_count: usize,
        rows_per_leaf: usize,
        total_cap_size: usize,
        log_lde_factor: u32,
        worker: &Worker,
    ) -> Vec<MerkleTreeCapVarLength> {
        let source_storage: Vec<Vec<&[BF]>> = cpu_cosets
            .iter()
            .map(|coset| {
                (0..columns_count)
                    .map(|column| &coset[column * domain_size..(column + 1) * domain_size])
                    .collect_vec()
            })
            .collect_vec();
        let source_refs = source_storage
            .iter()
            .map(|columns| columns.as_slice())
            .collect_vec();
        let tree = <Blake2sU32MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<
            BF,
        >>::construct_from_cosets::<BF, Global>(
            &source_refs,
            rows_per_leaf,
            total_cap_size,
            true,
            true,
            false,
            worker,
        );
        let subcap_size = total_cap_size >> log_lde_factor;
        <Blake2sU32MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
            &tree,
        )
        .cap
        .chunks_exact(subcap_size)
        .map(|chunk| MerkleTreeCapVarLength {
            cap: chunk.to_vec(),
        })
        .collect_vec()
    }

    fn hash_leaf_words(words: &[u32]) -> Digest {
        let num_full_rounds = words.len() / BLAKE2S_BLOCK_SIZE_U32_WORDS;
        let remainder = words.len() % BLAKE2S_BLOCK_SIZE_U32_WORDS;
        let only_full_rounds = remainder == 0;
        let (chunks, tail) = words.as_chunks::<BLAKE2S_BLOCK_SIZE_U32_WORDS>();
        let mut state = Blake2sState::new();
        let mut digest = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];
        for (round_idx, block) in chunks.iter().enumerate() {
            let is_last_round = round_idx + 1 == num_full_rounds;
            if is_last_round && only_full_rounds {
                state.absorb_final_block::<true>(block, BLAKE2S_BLOCK_SIZE_U32_WORDS, &mut digest);
            } else {
                state.absorb::<true>(block);
            }
        }
        if !only_full_rounds {
            let mut block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
            block[..tail.len()].copy_from_slice(tail);
            state.absorb_final_block::<true>(&block, tail.len(), &mut digest);
        }

        digest
    }

    fn extract_query_leaf_words(
        leafs: &[BF],
        query_index: usize,
        queries_count: usize,
        rows_per_leaf: usize,
    ) -> Vec<u32> {
        let values_per_column_count = queries_count * rows_per_leaf;
        assert_eq!(leafs.len() % values_per_column_count, 0);
        let columns_count = leafs.len() / values_per_column_count;
        let mut result = Vec::with_capacity(columns_count * rows_per_leaf);
        for column in 0..columns_count {
            let start = column * values_per_column_count + query_index * rows_per_leaf;
            result.extend(
                leafs[start..start + rows_per_leaf]
                    .iter()
                    .map(|value| value.as_u32_raw_repr_reduced()),
            );
        }

        result
    }

    fn verify_query_against_stage1_caps(
        leaf_words: &[u32],
        merkle_path: &[Digest],
        natural_leaf_index: usize,
        natural_coset_index: usize,
        stage1_caps: &[MerkleTreeCapVarLength],
        log_lde_factor: u32,
    ) {
        let mut current = hash_leaf_words(leaf_words);
        let mut index = natural_leaf_index;
        for sibling in merkle_path.iter() {
            let mut block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
            if index & 1 == 0 {
                block[..BLAKE2S_DIGEST_SIZE_U32_WORDS].copy_from_slice(&current);
                block[BLAKE2S_DIGEST_SIZE_U32_WORDS..].copy_from_slice(sibling);
            } else {
                block[..BLAKE2S_DIGEST_SIZE_U32_WORDS].copy_from_slice(sibling);
                block[BLAKE2S_DIGEST_SIZE_U32_WORDS..].copy_from_slice(&current);
            }
            Blake2sState::compress_two_to_one::<true>(&block, &mut current);
            index >>= 1;
        }

        let stage1_coset_index = super::bitreverse_index(natural_coset_index, log_lde_factor);
        assert_eq!(current, stage1_caps[stage1_coset_index].cap[index]);
    }

    fn assert_trace_holder_materialization_and_caps_match_cpu(log_rows_per_leaf: u32) {
        let worker = Worker::new();
        let context = make_test_context(256, 32);
        let log_domain_size = PARTIAL_TREE_REDUCTION_LAYERS + 3;
        let log_lde_factor = 2u32;
        let domain_size = 1usize << log_domain_size;
        let columns_count = 3usize;
        let (source_host, cpu_cosets) = make_source_host_and_cpu_cosets(
            log_domain_size,
            log_lde_factor,
            columns_count,
            &worker,
        );

        let mut source_device = context
            .alloc(source_host.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy(&mut source_device, &source_host).unwrap();

        let mut trace_holder = TraceHolder::<BF>::new(
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_lde_factor + 1,
            columns_count,
            TreesCacheMode::CacheFull,
            &context,
        )
        .unwrap();
        trace_holder
            .materialize_from_hypercube_evals(&source_device, &context)
            .unwrap();
        let mut raw_hypercube = vec![BF::ZERO; source_host.len()];
        memory_copy(&mut raw_hypercube, trace_holder.get_hypercube_evals()).unwrap();
        assert_eq!(raw_hypercube, source_host);
        assert!(trace_holder.are_cosets_materialized());

        match &trace_holder.cosets {
            CosetsHolder::Full(cosets) => {
                for (coset_idx, coset) in cosets.iter().enumerate() {
                    let mut gpu = vec![BF::ZERO; coset.len()];
                    memory_copy(&mut gpu, coset).unwrap();
                    assert_eq!(gpu, cpu_cosets[coset_idx], "coset {}", coset_idx);
                }
            }
        }

        trace_holder.commit_all(&context).unwrap();
        context.get_exec_stream().synchronize().unwrap();

        let gpu_caps = trace_holder.get_tree_caps();
        let cpu_caps = stage1_caps_from_cpu_cosets(
            &cpu_cosets,
            domain_size,
            columns_count,
            1 << log_rows_per_leaf,
            1 << trace_holder.log_tree_cap_size,
            log_lde_factor,
            &worker,
        );
        assert_eq!(gpu_caps, cpu_caps);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn trace_holder_lazy_coset_materialization_matches_cpu() {
        let worker = Worker::new();
        let context = make_test_context(256, 32);
        let log_domain_size = PARTIAL_TREE_REDUCTION_LAYERS + 3;
        let log_lde_factor = 2u32;
        let columns_count = 3usize;
        let (source_host, cpu_cosets) = make_source_host_and_cpu_cosets(
            log_domain_size,
            log_lde_factor,
            columns_count,
            &worker,
        );

        let mut trace_holder = TraceHolder::<BF>::new(
            log_domain_size,
            log_lde_factor,
            0,
            log_lde_factor + 1,
            columns_count,
            TreesCacheMode::CachePartial,
            &context,
        )
        .unwrap();
        memory_copy(trace_holder.get_uninit_hypercube_evals_mut(), &source_host).unwrap();

        let mut raw_hypercube = vec![BF::ZERO; source_host.len()];
        memory_copy(&mut raw_hypercube, trace_holder.get_hypercube_evals()).unwrap();
        assert_eq!(raw_hypercube, source_host);
        assert!(!trace_holder.are_cosets_materialized());

        trace_holder.ensure_cosets_materialized(&context).unwrap();
        assert!(trace_holder.are_cosets_materialized());

        match &trace_holder.cosets {
            CosetsHolder::Full(cosets) => {
                for (coset_idx, coset) in cosets.iter().enumerate() {
                    let mut gpu = vec![BF::ZERO; coset.len()];
                    memory_copy(&mut gpu, coset).unwrap();
                    assert_eq!(gpu, cpu_cosets[coset_idx], "coset {}", coset_idx);
                }
            }
        }
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn trace_holder_materialization_matches_cpu_for_single_row_leafs() {
        assert_trace_holder_materialization_and_caps_match_cpu(0);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn trace_holder_materialization_matches_stage1_caps_for_grouped_leafs() {
        assert_trace_holder_materialization_and_caps_match_cpu(2);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn trace_holder_queries_match_across_tree_cache_modes() {
        let worker = Worker::new();
        let context = make_test_context(256, 32);
        let log_domain_size = 9u32;
        let log_lde_factor = 2u32;
        let log_rows_per_leaf = 2u32;
        let log_tree_cap_size = 3u32;
        let domain_size = 1usize << log_domain_size;
        let columns_count = 3usize;
        let rows_per_leaf = 1usize << log_rows_per_leaf;
        let (source_host, cpu_cosets) = make_source_host_and_cpu_cosets(
            log_domain_size,
            log_lde_factor,
            columns_count,
            &worker,
        );

        let mut source_device = context
            .alloc(source_host.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy(&mut source_device, &source_host).unwrap();

        let mut full_holder = TraceHolder::<BF>::new(
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            TreesCacheMode::CacheFull,
            &context,
        )
        .unwrap();
        full_holder
            .materialize_and_commit_from_hypercube_evals(&source_device, &context)
            .unwrap();

        let mut partial_holder = TraceHolder::<BF>::new(
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            TreesCacheMode::CachePartial,
            &context,
        )
        .unwrap();
        partial_holder
            .materialize_and_commit_from_hypercube_evals(&source_device, &context)
            .unwrap();

        let mut none_holder = TraceHolder::<BF>::new(
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            TreesCacheMode::CacheNone,
            &context,
        )
        .unwrap();
        none_holder
            .materialize_and_commit_from_hypercube_evals(&source_device, &context)
            .unwrap();

        let query_indexes = vec![0u32, 1, 7, 13, 42];
        let mut indexes_device = context
            .alloc(query_indexes.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy(&mut indexes_device, &query_indexes).unwrap();

        let full = full_holder
            .get_leafs_and_merkle_paths(1, &indexes_device, &context)
            .unwrap();
        let partial = partial_holder
            .get_leafs_and_merkle_paths(1, &indexes_device, &context)
            .unwrap();
        let none = none_holder
            .get_leafs_and_merkle_paths(1, &indexes_device, &context)
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        let full_leafs = unsafe { full.leafs.get_accessor().get().to_vec() };
        let partial_leafs = unsafe { partial.leafs.get_accessor().get().to_vec() };
        let none_leafs = unsafe { none.leafs.get_accessor().get().to_vec() };
        assert_eq!(partial_leafs, full_leafs);
        assert_eq!(none_leafs, full_leafs);

        let full_paths = unsafe { full.merkle_paths.get_accessor().get().to_vec() };
        let partial_paths = unsafe { partial.merkle_paths.get_accessor().get().to_vec() };
        let none_paths = unsafe { none.merkle_paths.get_accessor().get().to_vec() };
        assert_eq!(partial_paths, full_paths);
        assert_eq!(none_paths, full_paths);

        let stage1_caps = full_holder.get_tree_caps();
        let cpu_caps = stage1_caps_from_cpu_cosets(
            &cpu_cosets,
            domain_size,
            columns_count,
            rows_per_leaf,
            1 << log_tree_cap_size,
            log_lde_factor,
            &worker,
        );
        assert_eq!(stage1_caps, cpu_caps);

        let path_len =
            (log_domain_size - log_rows_per_leaf - (log_tree_cap_size - log_lde_factor)) as usize;
        for (query_slot, &leaf_index) in query_indexes.iter().enumerate() {
            let leaf_words = extract_query_leaf_words(
                &full_leafs,
                query_slot,
                query_indexes.len(),
                rows_per_leaf,
            );
            let merkle_path = (0..path_len)
                .map(|layer| full_paths[query_slot + layer * query_indexes.len()])
                .collect_vec();
            verify_query_against_stage1_caps(
                &leaf_words,
                &merkle_path,
                leaf_index as usize,
                1,
                &stage1_caps,
                log_lde_factor,
            );
        }
    }
}
