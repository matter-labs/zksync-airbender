use super::context::{DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor};
use super::{BF, E4};
use crate::allocator::tracker::AllocationPlacement;
use crate::blake2s::{build_merkle_tree, merkle_tree_cap, Digest};
use crate::device_structures::{DeviceMatrix, DeviceMatrixChunkMut, DeviceMatrixMut};
use crate::ntt::{
    bitrev_Z_to_natural_composition_main_evals, natural_composition_coset_evals_to_bitrev_Z,
    natural_compressed_coset_evals_to_bitrev_Z, natural_main_evals_to_natural_coset_evals,
};
use crate::ops_cub::device_reduce::{
    batch_reduce_with_adaptive_parallelism,
    get_batch_reduce_with_adaptive_parallelism_temp_storage, ReduceOperation,
};
use crate::ops_simple::{neg, set_by_val, set_to_zero};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, DeviceSlice};
use era_cudart::stream::CudaStream;
use field::Field;
use itertools::Itertools;
use prover::merkle_trees::MerkleTreeCapVarLength;
use prover::prover_stages::Transcript;
use prover::transcript::Seed;
use std::mem::size_of;
use std::ops::Deref;

#[derive(Copy, Clone)]
pub enum TreesCacheMode {
    CacheNone,
    CachePatrial,
    CacheFull,
}

pub(crate) enum CosetsHolder<T> {
    Full(Vec<DeviceAllocation<T>>),
    Single {
        current_coset_index: usize,
        evaluations: DeviceAllocation<T>,
    },
}

#[allow(unused)]
pub(crate) enum TreesHolder {
    Full(Vec<DeviceAllocation<Digest>>),
    Partial(Vec<DeviceAllocation<Digest>>),
    None,
}

pub(crate) enum TreeReference<'a> {
    Borrowed(&'a DeviceAllocation<Digest>),
    Owned(DeviceAllocation<Digest>),
}

impl Deref for TreeReference<'_> {
    type Target = DeviceAllocation<Digest>;

    fn deref(&self) -> &Self::Target {
        match self {
            TreeReference::Borrowed(b) => *b,
            TreeReference::Owned(o) => o,
        }
    }
}

pub(crate) trait TraceHolderImpl {
    fn ensure_coset_computed(
        &mut self,
        coset_index: usize,
        context: &ProverContext,
    ) -> CudaResult<()>;
}

pub(crate) struct TraceHolder<T> {
    pub(crate) log_domain_size: u32,
    pub(crate) log_lde_factor: u32,
    pub(crate) log_rows_per_leaf: u32,
    pub(crate) log_tree_cap_size: u32,
    pub(crate) columns_count: usize,
    pub(crate) padded_to_even: bool,
    pub(crate) compressed_coset: bool,
    pub(crate) cosets: CosetsHolder<T>,
    pub(crate) trees: TreesHolder,
    pub(crate) tree_caps: Option<Vec<HostAllocation<[Digest]>>>,
}

impl TraceHolder<BF> {
    pub(crate) fn make_evaluations_sum_to_zero(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let evaluations = match &mut self.cosets {
            CosetsHolder::Full(evaluations) => &mut evaluations[0],
            CosetsHolder::Single {
                current_coset_index,
                evaluations,
            } => {
                assert_eq!(*current_coset_index, 0);
                evaluations
            }
        };
        make_evaluations_sum_to_zero(
            evaluations,
            self.log_domain_size,
            self.columns_count,
            self.padded_to_even,
            context,
        )
    }

    pub(crate) fn extend(
        &mut self,
        source_coset_index: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let log_domain_size = self.log_domain_size;
        let log_lde_factor = self.log_lde_factor;
        let compressed_coset = self.compressed_coset;
        assert_eq!(log_lde_factor, 1);
        match &mut self.cosets {
            CosetsHolder::Full(evaluations) => {
                let (src, dst) = split_evaluations_pair(evaluations, source_coset_index);
                compute_coset_evaluations(
                    src,
                    dst,
                    source_coset_index,
                    log_domain_size,
                    log_lde_factor,
                    compressed_coset,
                    context,
                )?;
            }
            CosetsHolder::Single {
                current_coset_index,
                evaluations,
            } => {
                assert_eq!(source_coset_index, *current_coset_index);
                *current_coset_index = 1 - source_coset_index;
                switch_coset_evaluations_in_place(
                    evaluations,
                    source_coset_index,
                    log_domain_size,
                    log_lde_factor,
                    compressed_coset,
                    context,
                )?;
            }
        }
        Ok(())
    }

    pub(crate) fn make_evaluations_sum_to_zero_and_extend(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<()> {
        self.make_evaluations_sum_to_zero(context)?;
        self.extend(0, context)
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
        let mut tree = match &mut self.trees {
            TreesHolder::Full(trees) => trees.remove(coset_index),
            TreesHolder::Partial(_) => unimplemented!(),
            TreesHolder::None => allocate_tree(log_domain_size, log_rows_per_leaf, context)?,
        };
        let evaluations = self.get_coset_evaluations(coset_index, context)?;
        commit_trace(
            evaluations,
            &mut tree,
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            stream,
        )?;
        let caps = &mut self.tree_caps.as_mut().unwrap()[coset_index];
        transfer_tree_cap(&mut tree, caps, log_lde_factor, log_tree_cap_size, stream)?;
        match &mut self.trees {
            TreesHolder::Full(trees) => trees.insert(coset_index, tree),
            TreesHolder::Partial(_) => unimplemented!(),
            TreesHolder::None => drop(tree),
        };
        Ok(())
    }

    pub(crate) fn extend_and_commit(
        &mut self,
        source_coset_index: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let tree_caps = allocate_tree_caps(self.log_lde_factor, self.log_tree_cap_size, context);
        assert!(self.tree_caps.replace(tree_caps).is_none());
        self.commit_and_transfer_tree_caps(source_coset_index, context)?;
        self.extend(source_coset_index, context)?;
        self.commit_and_transfer_tree_caps(1 - source_coset_index, context)?;
        Ok(())
    }

    pub(crate) fn make_evaluations_sum_to_zero_extend_and_commit(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<()> {
        self.make_evaluations_sum_to_zero(context)?;
        self.extend_and_commit(0, context)
    }

    pub(crate) fn get_coset_evaluations_and_tree(
        &mut self,
        coset_index: usize,
        context: &ProverContext,
    ) -> CudaResult<(&DeviceSlice<BF>, TreeReference<'_>)> {
        self.ensure_coset_computed(coset_index, context)?;
        let evaluations = match &self.cosets {
            CosetsHolder::Full(evaluations) => &evaluations[coset_index],
            CosetsHolder::Single {
                evaluations,
                current_coset_index,
            } => {
                assert_eq!(*current_coset_index, coset_index);
                evaluations
            }
        };
        let evaluations = &evaluations[..self.columns_count << self.log_domain_size];
        let tree = match &self.trees {
            TreesHolder::Full(trees) => TreeReference::Borrowed(&trees[coset_index]),
            TreesHolder::Partial(_) => unimplemented!(),
            TreesHolder::None => {
                let mut tree =
                    allocate_tree(self.log_domain_size, self.log_rows_per_leaf, context)?;
                commit_trace(
                    evaluations,
                    &mut tree,
                    self.log_domain_size,
                    self.log_lde_factor,
                    self.log_rows_per_leaf,
                    self.log_tree_cap_size,
                    self.columns_count,
                    context.get_exec_stream(),
                )?;
                TreeReference::Owned(tree)
            }
        };
        Ok((evaluations, tree))
    }
}

impl TraceHolderImpl for TraceHolder<BF> {
    fn ensure_coset_computed(
        &mut self,
        coset_index: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(coset_index < (1 << self.log_lde_factor));
        match &mut self.cosets {
            CosetsHolder::Full(evaluations) => {
                assert!(evaluations.len() > coset_index);
                Ok(())
            }
            CosetsHolder::Single {
                current_coset_index,
                evaluations,
            } => {
                if *current_coset_index == coset_index {
                    return Ok(());
                }
                switch_coset_evaluations_in_place(
                    evaluations,
                    *current_coset_index,
                    self.log_domain_size,
                    self.log_lde_factor,
                    self.compressed_coset,
                    context,
                )?;
                *current_coset_index = coset_index;
                Ok(())
            }
        }
    }
}

impl<T> TraceHolder<T> {
    pub(crate) fn new(
        log_domain_size: u32,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
        columns_count: usize,
        pad_to_even: bool,
        compressed_coset: bool,
        recompute_cosets: bool,
        trees_cache_mode: TreesCacheMode,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        assert_eq!(log_lde_factor, 1);
        let padded_to_even = pad_to_even && columns_count.next_multiple_of(2) != columns_count;
        let instances_count = 1 << log_lde_factor;
        let cosets = match recompute_cosets {
            true => CosetsHolder::Single {
                current_coset_index: 0,
                evaluations: allocate_coset(log_domain_size, columns_count, pad_to_even, context)?,
            },
            false => CosetsHolder::Full(allocate_cosets(
                instances_count,
                log_domain_size,
                columns_count,
                pad_to_even,
                context,
            )?),
        };
        let trees = match trees_cache_mode {
            TreesCacheMode::CacheNone => TreesHolder::None,
            TreesCacheMode::CachePatrial => unimplemented!(),
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
            padded_to_even,
            compressed_coset,
            cosets,
            trees,
            tree_caps: None,
        })
    }

    pub(crate) fn allocate_only_evaluation(
        log_domain_size: u32,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
        columns_count: usize,
        pad_to_even: bool,
        compressed_coset: bool,
        recompute_cosets: bool,
        trees_cache_mode: TreesCacheMode,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let padded_to_even = pad_to_even && columns_count.next_multiple_of(2) != columns_count;
        let evaluations = allocate_coset(log_domain_size, columns_count, pad_to_even, context)?;
        let cosets = match recompute_cosets {
            true => CosetsHolder::Single {
                current_coset_index: 0,
                evaluations,
            },
            false => CosetsHolder::Full(vec![evaluations]),
        };
        let trees = match trees_cache_mode {
            TreesCacheMode::CacheNone => TreesHolder::Full(vec![]),
            TreesCacheMode::CachePatrial => unimplemented!(),
            TreesCacheMode::CacheFull => TreesHolder::None,
        };
        Ok(Self {
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            padded_to_even,
            compressed_coset,
            cosets,
            trees,
            tree_caps: None,
        })
    }

    pub(crate) fn allocate_to_full(&mut self, context: &ProverContext) -> CudaResult<()> {
        let instances_count = 1 << self.log_lde_factor;
        match &mut self.cosets {
            CosetsHolder::Full(evaluations) => {
                assert_eq!(evaluations.len(), 1);
                let additional_evaluations = allocate_cosets(
                    instances_count - 1,
                    self.log_domain_size,
                    self.columns_count,
                    self.padded_to_even,
                    context,
                )?;
                evaluations.extend(additional_evaluations);
            }
            CosetsHolder::Single { .. } => {}
        }
        match &mut self.trees {
            TreesHolder::Full(trees) => {
                assert!(trees.is_empty());
                let new_trees = allocate_trees(
                    instances_count,
                    self.log_domain_size,
                    self.log_rows_per_leaf,
                    context,
                )?;
                trees.extend(new_trees);
            }
            TreesHolder::Partial(_) => unimplemented!(),
            TreesHolder::None => {}
        }
        Ok(())
    }

    pub(crate) fn get_tree_caps_accessors(&self) -> Vec<UnsafeAccessor<[Digest]>> {
        self.tree_caps
            .as_ref()
            .unwrap()
            .iter()
            .map(HostAllocation::get_accessor)
            .collect_vec()
    }

    pub(crate) fn get_update_seed_fn(&self, seed: &mut HostAllocation<Seed>) -> impl Fn() {
        let tree_caps_accessors = self.get_tree_caps_accessors();
        let seed_accessor = seed.get_mut_accessor();
        move || unsafe {
            let input = flatten_tree_caps(&tree_caps_accessors).collect_vec();
            Transcript::commit_with_seed(seed_accessor.get_mut(), &input);
        }
    }
}

impl TraceHolderImpl for TraceHolder<E4> {
    fn ensure_coset_computed(
        &mut self,
        coset_index: usize,
        _context: &ProverContext,
    ) -> CudaResult<()> {
        assert!(coset_index < (1 << self.log_lde_factor));
        match &mut self.cosets {
            CosetsHolder::Full(evaluations) => {
                assert!(evaluations.len() > coset_index);
                Ok(())
            }
            CosetsHolder::Single { .. } => {
                unimplemented!()
            }
        }
    }
}

impl<T> TraceHolder<T>
where
    TraceHolder<T>: TraceHolderImpl,
{
    pub(crate) fn get_coset_evaluations(
        &mut self,
        coset_index: usize,
        context: &ProverContext,
    ) -> CudaResult<&DeviceSlice<T>> {
        self.ensure_coset_computed(coset_index, context)?;
        let evaluations = match &self.cosets {
            CosetsHolder::Full(evaluations) => &evaluations[coset_index],
            CosetsHolder::Single {
                evaluations,
                current_coset_index,
            } => {
                assert_eq!(*current_coset_index, coset_index);
                evaluations
            }
        };
        Ok(&evaluations[..self.columns_count << self.log_domain_size])
    }

    pub(crate) fn get_uninit_coset_evaluations_mut(
        &mut self,
        coset_index: usize,
    ) -> &mut DeviceSlice<T> {
        let evaluations = match &mut self.cosets {
            CosetsHolder::Full(evaluations) => &mut evaluations[coset_index],
            CosetsHolder::Single {
                evaluations,
                current_coset_index,
            } => {
                *current_coset_index = coset_index;
                evaluations
            }
        };
        &mut evaluations[..self.columns_count << self.log_domain_size]
    }

    pub(crate) fn get_evaluations(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<&DeviceSlice<T>> {
        self.get_coset_evaluations(0, context)
    }

    pub(crate) fn get_uninit_evaluations_mut(&mut self) -> &mut DeviceSlice<T> {
        self.get_uninit_coset_evaluations_mut(0)
    }
}

pub(crate) fn allocate_coset<T>(
    log_domain_size: u32,
    columns_count: usize,
    pad_to_even: bool,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<T>> {
    let columns_count = if pad_to_even {
        columns_count.next_multiple_of(2)
    } else {
        columns_count
    };
    let size = columns_count << log_domain_size;
    context.alloc(size, AllocationPlacement::Bottom)
}

fn allocate_cosets<T>(
    instances_count: usize,
    log_domain_size: u32,
    columns_count: usize,
    pad_to_even: bool,
    context: &ProverContext,
) -> CudaResult<Vec<DeviceAllocation<T>>> {
    let mut result = Vec::with_capacity(instances_count);
    for _ in 0..instances_count {
        result.push(allocate_coset(
            log_domain_size,
            columns_count,
            pad_to_even,
            context,
        )?);
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
        let tree_cap = unsafe { context.alloc_host_uninit_slice(coset_tree_cap_size) };
        result.push(tree_cap);
    }
    result
}

fn make_evaluations_sum_to_zero(
    evaluations: &mut DeviceSlice<BF>,
    log_domain_size: u32,
    columns_count: usize,
    padded_to_even: bool,
    context: &ProverContext,
) -> CudaResult<()> {
    let domain_size = 1 << log_domain_size;
    assert_eq!(
        evaluations.len(),
        domain_size * columns_count.next_multiple_of(2)
    );
    let stream = context.get_exec_stream();
    set_by_val(
        BF::ZERO,
        &mut DeviceMatrixChunkMut::new(
            &mut evaluations[..columns_count << log_domain_size],
            domain_size,
            domain_size - 1,
            1,
        ),
        stream,
    )?;
    let (cub_scratch_bytes, batch_reduce_intermediate_elems) =
        get_batch_reduce_with_adaptive_parallelism_temp_storage::<BF>(
            ReduceOperation::Sum,
            columns_count,
            domain_size,
            context.get_device_properties(),
        )?;
    let mut scratch_bytes_alloc = context.alloc(
        size_of::<BF>() * (batch_reduce_intermediate_elems + columns_count) + cub_scratch_bytes,
        AllocationPlacement::BestFit,
    )?;
    let (batch_reduce_intermediates_scratch, scratch_bytes) =
        scratch_bytes_alloc.split_at_mut(size_of::<BF>() * batch_reduce_intermediate_elems);
    let batch_reduce_intermediates_scratch =
        unsafe { batch_reduce_intermediates_scratch.transmute_mut::<BF>() };
    let maybe_batch_reduce_intermediates: Option<&mut DeviceSlice<BF>> =
        if batch_reduce_intermediate_elems > 0 {
            Some(batch_reduce_intermediates_scratch)
        } else {
            None
        };
    let (reduce_result, cub_scratch) = scratch_bytes.split_at_mut(size_of::<BF>() * columns_count);
    let reduce_result = unsafe { reduce_result.transmute_mut::<BF>() };
    batch_reduce_with_adaptive_parallelism::<BF>(
        ReduceOperation::Sum,
        cub_scratch,
        maybe_batch_reduce_intermediates,
        &DeviceMatrix::new(&evaluations[0..columns_count * domain_size], domain_size),
        reduce_result,
        stream,
        context.get_device_properties(),
    )?;
    neg(
        &DeviceMatrix::new(&reduce_result, 1),
        &mut DeviceMatrixChunkMut::new(
            &mut evaluations[..columns_count << log_domain_size],
            domain_size,
            domain_size - 1,
            1,
        ),
        stream,
    )?;
    scratch_bytes_alloc.free();
    if padded_to_even {
        set_to_zero(&mut evaluations[columns_count << log_domain_size..], stream)?;
    }
    Ok(())
}

pub(crate) fn compute_coset_evaluations(
    src: &DeviceSlice<BF>,
    dst: &mut DeviceSlice<BF>,
    source_coset_index: usize,
    log_domain_size: u32,
    log_lde_factor: u32,
    compressed_coset: bool,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(log_lde_factor, 1);
    let len = src.len();
    assert_eq!(len, dst.len());
    let domain_size = 1 << log_domain_size;
    assert_eq!(len & ((domain_size << 1) - 1), 0);
    let num_bf_cols = len >> log_domain_size;
    let src_matrix = DeviceMatrix::new(src, domain_size);
    let const_dst = unsafe { DeviceSlice::from_raw_parts(dst.as_ptr(), len) };
    let const_dst_matrix = DeviceMatrix::new(const_dst, domain_size);
    let mut dst_matrix = DeviceMatrixMut::new(dst, domain_size);
    let log_n = log_domain_size as usize;
    let stream = context.get_exec_stream();
    if source_coset_index == 0 {
        if compressed_coset {
            natural_main_evals_to_natural_coset_evals(
                &src_matrix,
                &mut dst_matrix,
                log_n,
                num_bf_cols,
                stream,
                context.get_aux_stream(),
                context.get_device_properties(),
            )?;
        } else {
            unimplemented!();
        }
    } else {
        assert_eq!(source_coset_index, 1);
        if compressed_coset {
            natural_compressed_coset_evals_to_bitrev_Z(
                &src_matrix,
                &mut dst_matrix,
                log_n,
                num_bf_cols,
                stream,
            )?;
        } else {
            natural_composition_coset_evals_to_bitrev_Z(
                &src_matrix,
                &mut dst_matrix,
                log_domain_size as usize,
                num_bf_cols,
                stream,
            )?;
        }
        bitrev_Z_to_natural_composition_main_evals(
            &const_dst_matrix,
            &mut dst_matrix,
            log_domain_size as usize,
            num_bf_cols,
            stream,
        )?;
    }
    Ok(())
}

fn switch_coset_evaluations_in_place(
    evals: &mut DeviceSlice<BF>,
    source_coset_index: usize,
    log_domain_size: u32,
    log_lde_factor: u32,
    compressed_coset: bool,
    context: &ProverContext,
) -> CudaResult<()> {
    let const_evals = unsafe { DeviceSlice::from_raw_parts_mut(evals.as_mut_ptr(), evals.len()) };
    compute_coset_evaluations(
        &const_evals,
        evals,
        source_coset_index,
        log_domain_size,
        log_lde_factor,
        compressed_coset,
        context,
    )
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
    let tree_len = 1 << log_domain_size + 1 - log_rows_per_leaf;
    assert_eq!(tree.len(), tree_len);
    let log_coset_tree_cap_size = log_tree_cap_size - log_lde_factor;
    let layers_count = log_domain_size + 1 - log_rows_per_leaf - log_coset_tree_cap_size;
    build_merkle_tree(
        &lde[..columns_count << log_domain_size],
        tree,
        log_rows_per_leaf,
        stream,
        layers_count,
        true,
    )
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

pub(crate) fn flatten_tree_caps(
    accessors: &[UnsafeAccessor<[Digest]>],
) -> impl Iterator<Item = u32> + use<'_> {
    accessors
        .into_iter()
        .flat_map(|accessor| unsafe { accessor.get().to_vec() })
        .flatten()
}

pub(crate) fn get_tree_caps(accessors: &[UnsafeAccessor<[Digest]>]) -> Vec<MerkleTreeCapVarLength> {
    accessors
        .into_iter()
        .map(|accessor| unsafe { accessor.get().to_vec() })
        .map(|cap| MerkleTreeCapVarLength { cap })
        .collect_vec()
}

pub(crate) fn split_evaluations_pair(
    evaluations: &mut [DeviceAllocation<BF>],
    coset_index: usize,
) -> (&DeviceAllocation<BF>, &mut DeviceAllocation<BF>) {
    assert_eq!(evaluations.len(), 2);
    let (src, dst) = evaluations.split_at_mut(1);
    if coset_index == 0 {
        (&src[0], &mut dst[0])
    } else {
        (&dst[0], &mut src[0])
    }
}

#[allow(dead_code)]
#[cfg(test)]
mod test {
    use super::BF;
    use crate::blake2s::Digest;
    use era_cudart::memory::memory_copy;
    use era_cudart::slice::DeviceSlice;
    use fft::GoodAllocator;
    use prover::merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap;
    use prover::merkle_trees::MerkleTreeConstructor;
    use prover::prover_stages::CosetBoundTracePart;
    use std::ops::DerefMut;

    pub(crate) fn compare_row_major_trace_ldes<
        const N: usize,
        A: GoodAllocator,
        L: DerefMut<Target = DeviceSlice<BF>>,
    >(
        cpu_data: &[CosetBoundTracePart<N, A>],
        gpu_data: &[L],
    ) {
        let mut error_count = 0;
        for (coset, (cpu_lde, gpu_lde)) in cpu_data.iter().zip(gpu_data.iter()).enumerate() {
            let trace_len = cpu_lde.trace.len();
            let gpu_lde_len = gpu_lde.len();
            assert_eq!(gpu_lde_len % trace_len, 0);
            let gpu_cols = gpu_lde_len / trace_len;
            let mut h_trace = vec![BF::default(); gpu_lde_len];
            memory_copy(&mut h_trace, gpu_lde.deref()).unwrap();
            let mut gpu_lde = vec![BF::default(); gpu_lde_len];
            assert_eq!(cpu_lde.trace.width().next_multiple_of(2), gpu_cols);
            transpose::transpose(&h_trace, &mut gpu_lde, trace_len, gpu_cols);
            let mut view = cpu_lde.trace.row_view(0..trace_len);
            for (row, gpu_row) in gpu_lde.chunks(gpu_cols).enumerate() {
                let cpu_row = view.current_row_ref();
                let gpu_row = &gpu_row[..cpu_row.len()];
                if cpu_row != gpu_row {
                    dbg!(coset, row, cpu_row, gpu_row);
                    error_count += 1;
                    if error_count > 4 {
                        panic!("too many errors");
                    }
                }
                view.advance_row();
            }
        }
        assert_eq!(error_count, 0);
    }

    pub(crate) fn compare_trace_trees<
        A: GoodAllocator,
        T: DerefMut<Target = DeviceSlice<Digest>>,
    >(
        cpu_trees: &[Blake2sU32MerkleTreeWithCap<A>],
        gpu_trees: &[T],
        log_lde_factor: u32,
        log_tree_cap_size: u32,
    ) {
        let log_coset_tree_cap_size = log_tree_cap_size - log_lde_factor;
        let coset_tree_cap_size = 1 << log_coset_tree_cap_size;
        for (coset, (cpu_tree, gpu_tree)) in cpu_trees.iter().zip(gpu_trees.iter()).enumerate() {
            let cpu_leaf_hashes = &cpu_tree.leaf_hashes;
            let leafs_count = cpu_tree.leaf_hashes.len();
            assert_eq!(gpu_tree.len(), leafs_count << 1);
            let mut h_tree = vec![Digest::default(); leafs_count << 1];
            memory_copy(&mut h_tree, gpu_tree.deref()).unwrap();
            let gpu_leaf_hashes = &h_tree[..leafs_count];
            if cpu_leaf_hashes != gpu_leaf_hashes {
                cpu_leaf_hashes
                    .iter()
                    .zip(gpu_leaf_hashes.iter())
                    .enumerate()
                    .for_each(|(i, (c, g))| {
                        assert_eq!(c, g, "coset: {}, leaf: {}", coset, i);
                    });
            }
            let cpu_cap = cpu_tree.get_cap().cap;
            assert_eq!(cpu_cap.len(), coset_tree_cap_size);
            let offset = (leafs_count - coset_tree_cap_size) << 1;
            assert_eq!(cpu_cap, h_tree[offset..][..coset_tree_cap_size]);
        }
    }
}
