use super::context::{
    DeviceAllocation, DeviceProperties, HostAllocation, ProverContext, UnsafeAccessor,
};
use super::{BF, E4};
use crate::allocator::tracker::AllocationPlacement;
use crate::blake2s::{build_merkle_tree, merkle_tree_cap, Digest};
use crate::device_structures::{DeviceMatrix, DeviceMatrixChunkMut, DeviceMatrixMut};
use crate::ntt::{
    bitrev_Z_to_natural_composition_main_evals, natural_composition_coset_evals_to_bitrev_Z,
    natural_main_evals_to_natural_coset_evals,
};
use crate::ops_cub::device_reduce::{
    batch_reduce_with_adaptive_parallelism,
    get_batch_reduce_with_adaptive_parallelism_temp_storage, ReduceOperation,
};
use crate::ops_simple::{neg, set_by_val, set_to_zero};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use field::Field;
use itertools::Itertools;
use prover::merkle_trees::MerkleTreeCapVarLength;
use prover::prover_stages::Transcript;
use prover::transcript::Seed;
use std::mem::size_of;
use std::ops::{Deref, DerefMut};

pub enum CosetsHolder<T> {
    Full {
        evaluations: Vec<DeviceAllocation<T>>,
    },
    WithRecomputations {
        current_coset_index: usize,
        evaluations: DeviceAllocation<T>,
    },
}

pub trait TraceHolderImpl {
    fn ensure_coset_computed(
        &mut self,
        coset_index: usize,
        context: &ProverContext,
    ) -> CudaResult<()>;
}

pub struct TraceHolder<T> {
    pub(crate) log_domain_size: u32,
    pub(crate) log_lde_factor: u32,
    pub(crate) log_rows_per_leaf: u32,
    pub(crate) log_tree_cap_size: u32,
    pub(crate) columns_count: usize,
    pub(crate) padded_to_even: bool,
    pub(crate) cosets: CosetsHolder<T>,
    pub(crate) trees: Vec<DeviceAllocation<Digest>>,
    pub(crate) tree_caps: Option<Vec<HostAllocation<[Digest]>>>,
}

impl TraceHolder<BF> {
    pub fn make_evaluations_sum_to_zero(&mut self, context: &ProverContext) -> CudaResult<()> {
        let evaluations = match &mut self.cosets {
            CosetsHolder::Full { evaluations } => &mut evaluations[0],
            CosetsHolder::WithRecomputations {
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

    pub fn extend_and_commit(
        &mut self,
        source_coset_index: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let log_domain_size = self.log_domain_size;
        let log_lde_factor = self.log_lde_factor;
        let log_rows_per_leaf = self.log_rows_per_leaf;
        let log_tree_cap_size = self.log_tree_cap_size;
        let columns_count = self.columns_count;
        let lde_factor = 1 << log_lde_factor;
        let stream = context.get_exec_stream();
        match &mut self.cosets {
            CosetsHolder::Full { evaluations } => {
                assert_eq!(evaluations.len(), lde_factor);
                extend_trace(
                    evaluations,
                    source_coset_index,
                    log_domain_size,
                    log_lde_factor,
                    stream,
                    context.get_aux_stream(),
                    context.get_device_properties(),
                )?;
                let trees = &mut self.trees;
                assert_eq!(trees.len(), lde_factor);
                for (lde, tree) in evaluations.iter().zip_eq(trees.iter_mut()) {
                    commit_trace(
                        lde,
                        tree,
                        log_domain_size,
                        log_lde_factor,
                        log_rows_per_leaf,
                        log_tree_cap_size,
                        columns_count,
                        stream,
                    )?;
                }
            }
            CosetsHolder::WithRecomputations {
                current_coset_index,
                evaluations,
            } => {
                assert_eq!(*current_coset_index, source_coset_index);
                commit_trace(
                    evaluations,
                    &mut self.trees[source_coset_index],
                    log_domain_size,
                    log_lde_factor,
                    log_rows_per_leaf,
                    log_tree_cap_size,
                    columns_count,
                    stream,
                )?;
                for i in 0..lde_factor {
                    if i == source_coset_index {
                        continue;
                    }
                    switch_evaluations_coset_in_place(
                        evaluations,
                        source_coset_index,
                        log_domain_size,
                        log_lde_factor,
                        stream,
                        context.get_aux_stream(),
                        context.get_device_properties(),
                    )?;
                    *current_coset_index = i;
                    commit_trace(
                        evaluations,
                        &mut self.trees[i],
                        log_domain_size,
                        log_lde_factor,
                        log_rows_per_leaf,
                        log_tree_cap_size,
                        columns_count,
                        stream,
                    )?;
                }
            }
        }
        Ok(())
    }

    pub fn make_evaluations_sum_to_zero_extend_and_commit(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<()> {
        self.make_evaluations_sum_to_zero(context)?;
        self.extend_and_commit(0, context)
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
            CosetsHolder::Full { evaluations } => {
                assert!(evaluations.len() <= coset_index);
                Ok(())
            }
            CosetsHolder::WithRecomputations {
                current_coset_index,
                evaluations,
            } => {
                if *current_coset_index == coset_index {
                    return Ok(());
                }
                switch_evaluations_coset_in_place(
                    evaluations,
                    *current_coset_index,
                    self.log_domain_size,
                    self.log_lde_factor,
                    context.get_exec_stream(),
                    context.get_aux_stream(),
                    context.get_device_properties(),
                )?;
                *current_coset_index = coset_index;
                Ok(())
            }
        }
    }
}

impl<T> TraceHolder<T> {
    pub fn new(
        log_domain_size: u32,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
        columns_count: usize,
        pad_to_even: bool,
        use_recomputations: bool,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let padded_to_even = pad_to_even && columns_count.next_multiple_of(2) != columns_count;
        let instances_count = 1 << log_lde_factor;
        let cosets = if use_recomputations {
            let evaluations =
                allocate_ldes(log_domain_size, 1, columns_count, pad_to_even, context)?;
            CosetsHolder::WithRecomputations {
                current_coset_index: 0,
                evaluations: evaluations.into_iter().next().unwrap(),
            }
        } else {
            let evaluations = allocate_ldes(
                log_domain_size,
                instances_count,
                columns_count,
                pad_to_even,
                context,
            )?;
            CosetsHolder::Full { evaluations }
        };
        let trees = allocate_trees(log_domain_size, instances_count, log_rows_per_leaf, context)?;
        Ok(Self {
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            padded_to_even,
            cosets,
            trees,
            tree_caps: None,
        })
    }

    pub fn allocate_only_evaluation(
        log_domain_size: u32,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
        columns_count: usize,
        pad_to_even: bool,
        use_recomputations: bool,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let padded_to_even = pad_to_even && columns_count.next_multiple_of(2) != columns_count;
        let evaluations = allocate_ldes(log_domain_size, 1, columns_count, pad_to_even, context)?;
        let cosets = if use_recomputations {
            CosetsHolder::WithRecomputations {
                current_coset_index: 0,
                evaluations: evaluations.into_iter().next().unwrap(),
            }
        } else {
            CosetsHolder::Full { evaluations }
        };
        let trees = vec![];
        Ok(Self {
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            padded_to_even,
            cosets,
            trees,
            tree_caps: None,
        })
    }

    pub fn allocate_to_full(&mut self, context: &ProverContext) -> CudaResult<()> {
        let instances_count = 1 << self.log_lde_factor;
        match &mut self.cosets {
            CosetsHolder::Full { evaluations } => {
                assert_eq!(evaluations.len(), 1);
                let additional_evaluations = allocate_ldes(
                    self.log_domain_size,
                    instances_count - 1,
                    self.columns_count,
                    self.padded_to_even,
                    context,
                )?;
                evaluations.extend(additional_evaluations);
            }
            CosetsHolder::WithRecomputations { .. } => {}
        }
        assert!(self.trees.is_empty());
        let trees = allocate_trees(
            self.log_domain_size,
            instances_count,
            self.log_rows_per_leaf,
            context,
        )?;
        self.trees.extend(trees);
        Ok(())
    }

    pub fn produce_tree_caps(&mut self, context: &ProverContext) -> CudaResult<()> {
        if self.tree_caps.is_some() {
            return Ok(());
        }
        let mut tree_caps =
            allocate_tree_caps(self.log_lde_factor, self.log_tree_cap_size, context);
        transfer_tree_caps(
            &self.trees,
            &mut tree_caps,
            self.log_lde_factor,
            self.log_tree_cap_size,
            context.get_exec_stream(),
        )?;
        self.tree_caps = Some(tree_caps);
        Ok(())
    }

    pub fn get_tree_caps_accessors(&self) -> Vec<UnsafeAccessor<[Digest]>> {
        self.tree_caps
            .as_ref()
            .unwrap()
            .iter()
            .map(HostAllocation::get_accessor)
            .collect_vec()
    }

    pub fn get_update_seed_fn(&self, seed: &mut HostAllocation<Seed>) -> impl Fn() {
        let tree_caps_accessors = self.get_tree_caps_accessors();
        let seed_accessor = seed.get_mut_accessor();
        move || unsafe {
            let tree_caps = tree_caps_accessors
                .iter()
                .map(|cap| cap.get())
                .collect_vec();
            let input = flatten_tree_caps(&tree_caps).collect_vec();
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
            CosetsHolder::Full { evaluations } => {
                assert!(evaluations.len() <= coset_index);
                Ok(())
            }
            CosetsHolder::WithRecomputations { .. } => {
                unimplemented!()
            }
        }
    }
}

impl<T> TraceHolder<T>
where
    TraceHolder<T>: TraceHolderImpl,
{
    pub fn get_coset_evaluations(
        &mut self,
        coset_index: usize,
        context: &ProverContext,
    ) -> CudaResult<&DeviceSlice<T>> {
        self.ensure_coset_computed(coset_index, context)?;
        let evaluations = match &self.cosets {
            CosetsHolder::Full { evaluations } => &evaluations[coset_index],
            CosetsHolder::WithRecomputations {
                evaluations,
                current_coset_index,
            } => {
                assert_eq!(*current_coset_index, coset_index);
                evaluations
            }
        };
        Ok(&evaluations[..self.columns_count << self.log_domain_size])
    }

    pub fn get_uninit_coset_evaluations_mut(&mut self, coset_index: usize) -> &mut DeviceSlice<T> {
        let evaluations = match &mut self.cosets {
            CosetsHolder::Full { evaluations } => &mut evaluations[coset_index],
            CosetsHolder::WithRecomputations {
                evaluations,
                current_coset_index,
            } => {
                *current_coset_index = coset_index;
                evaluations
            }
        };
        &mut evaluations[..self.columns_count << self.log_domain_size]
    }

    pub fn get_evaluations(&mut self, context: &ProverContext) -> CudaResult<&DeviceSlice<T>> {
        self.get_coset_evaluations(0, context)
    }

    pub fn get_uninit_evaluations_mut(&mut self) -> &mut DeviceSlice<T> {
        self.get_uninit_coset_evaluations_mut(0)
    }

    pub fn get_coset_evaluations_and_tree(
        &mut self,
        coset_index: usize,
        context: &ProverContext,
    ) -> CudaResult<(&DeviceSlice<T>, &DeviceSlice<Digest>)> {
        self.ensure_coset_computed(coset_index, context)?;
        let evaluations = match &self.cosets {
            CosetsHolder::Full { evaluations } => &evaluations[coset_index],
            CosetsHolder::WithRecomputations {
                evaluations,
                current_coset_index,
            } => {
                assert_eq!(*current_coset_index, coset_index);
                evaluations
            }
        };
        let evaluations = &evaluations[..self.columns_count << self.log_domain_size];
        let tree = &self.trees[coset_index] as &DeviceSlice<Digest>;
        Ok((evaluations, tree))
    }
}

pub(crate) fn allocate_ldes<T>(
    log_domain_size: u32,
    instances_count: usize,
    columns_count: usize,
    pad_to_even: bool,
    context: &ProverContext,
) -> CudaResult<Vec<DeviceAllocation<T>>> {
    let columns_count = if pad_to_even {
        columns_count.next_multiple_of(2)
    } else {
        columns_count
    };
    let size = columns_count << log_domain_size;
    let mut result = Vec::with_capacity(instances_count);
    for _ in 0..instances_count {
        result.push(context.alloc(size, AllocationPlacement::Bottom)?);
    }
    Ok(result)
}

pub(crate) fn allocate_trees(
    log_domain_size: u32,
    instances_count: usize,
    log_rows_per_leaf: u32,
    context: &ProverContext,
) -> CudaResult<Vec<DeviceAllocation<Digest>>> {
    let size = 1 << (log_domain_size + 1 - log_rows_per_leaf);
    let mut result = Vec::with_capacity(instances_count);
    for _ in 0..instances_count {
        result.push(context.alloc(size, AllocationPlacement::Bottom)?);
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

pub(crate) fn extend_trace<L: DerefMut<Target = DeviceSlice<BF>>>(
    ldes: &mut [L],
    source_coset_index: usize,
    log_domain_size: u32,
    log_lde_factor: u32,
    stream: &CudaStream,
    aux_stream: &CudaStream,
    device_properties: &DeviceProperties,
) -> CudaResult<()> {
    assert_eq!(log_lde_factor, 1);
    let lde_factor = 1 << log_lde_factor;
    assert_eq!(ldes.len(), lde_factor);
    let len = ldes[0].len();
    assert_eq!(len, ldes[1].len());
    let domain_size = 1 << log_domain_size;
    assert_eq!(len & ((domain_size << 1) - 1), 0);
    let num_bf_cols = len >> log_domain_size;
    if source_coset_index == 0 {
        let (src_evals, dst_evals) = ldes.split_at_mut(1);
        let src_evals = &src_evals[0];
        let dst_evals = &mut dst_evals[0];
        let src_evals_matrix = DeviceMatrix::new(src_evals, domain_size);
        let mut dst_matrix = DeviceMatrixMut::new(dst_evals, domain_size);
        natural_main_evals_to_natural_coset_evals(
            &src_evals_matrix,
            &mut dst_matrix,
            log_domain_size as usize,
            num_bf_cols,
            stream,
            aux_stream,
            device_properties,
        )?;
    } else {
        assert_eq!(source_coset_index, 1);
        let (dst_evals, src_evals) = ldes.split_at_mut(1);
        let src_evals = &src_evals[0];
        let const_dst_evals = unsafe { DeviceSlice::from_raw_parts(dst_evals[0].as_ptr(), len) };
        let dst_evals = &mut dst_evals[0];
        let src_evals_matrix = DeviceMatrix::new(src_evals, domain_size);
        let const_dst_matrix = DeviceMatrix::new(const_dst_evals, domain_size);
        let mut dst_matrix = DeviceMatrixMut::new(dst_evals, domain_size);
        natural_composition_coset_evals_to_bitrev_Z(
            &src_evals_matrix,
            &mut dst_matrix,
            log_domain_size as usize,
            num_bf_cols,
            stream,
        )?;
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

fn switch_evaluations_coset_in_place<L: DerefMut<Target = DeviceSlice<BF>>>(
    evals: &mut L,
    source_coset_index: usize,
    log_domain_size: u32,
    log_lde_factor: u32,
    stream: &CudaStream,
    aux_stream: &CudaStream,
    device_properties: &DeviceProperties,
) -> CudaResult<()> {
    assert_eq!(log_lde_factor, 1);
    let len = evals.len();
    let domain_size = 1 << log_domain_size;
    assert_eq!(len & ((domain_size << 1) - 1), 0);
    let num_bf_cols = len >> log_domain_size;
    if source_coset_index == 0 {
        let src_evals = unsafe { DeviceSlice::from_raw_parts(evals.as_ptr(), len) };
        let dst_evals = evals;
        let src_evals_matrix = DeviceMatrix::new(src_evals, domain_size);
        let mut dst_matrix = DeviceMatrixMut::new(dst_evals, domain_size);
        natural_main_evals_to_natural_coset_evals(
            &src_evals_matrix,
            &mut dst_matrix,
            log_domain_size as usize,
            num_bf_cols,
            stream,
            aux_stream,
            device_properties,
        )?;
    } else {
        assert_eq!(source_coset_index, 1);
        let src_evals = unsafe { DeviceSlice::from_raw_parts(evals.as_ptr(), len) };
        let dst_evals = evals;
        let src_evals_matrix = DeviceMatrix::new(src_evals, domain_size);
        let mut dst_matrix = DeviceMatrixMut::new(dst_evals, domain_size);
        natural_composition_coset_evals_to_bitrev_Z(
            &src_evals_matrix,
            &mut dst_matrix,
            log_domain_size as usize,
            num_bf_cols,
            stream,
        )?;
        bitrev_Z_to_natural_composition_main_evals(
            &src_evals_matrix,
            &mut dst_matrix,
            log_domain_size as usize,
            num_bf_cols,
            stream,
        )?;
    }
    Ok(())
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

pub(crate) fn transfer_tree_caps<T: DerefMut<Target = DeviceSlice<Digest>>>(
    trees: &[T],
    caps: &mut [HostAllocation<[Digest]>],
    log_lde_factor: u32,
    log_tree_cap_size: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(trees.len(), 1 << log_lde_factor);
    let log_subtree_cap_size = log_tree_cap_size - log_lde_factor;
    for (subtree, h_cap) in trees.iter().zip(caps.iter_mut()) {
        let d_cap = merkle_tree_cap(subtree, log_subtree_cap_size);
        memory_copy_async(unsafe { h_cap.get_mut_accessor().get_mut() }, d_cap, stream)?;
    }
    Ok(())
}

pub(crate) fn flatten_tree_caps<C: Deref<Target = [Digest]>>(
    caps: &[C],
) -> impl Iterator<Item = u32> + use<'_, C> {
    caps.iter()
        .flat_map(|slice| slice.deref())
        .flatten()
        .copied()
}

pub(crate) fn transform_tree_caps<C: Deref<Target = [Digest]>>(
    caps: &[C],
) -> Vec<MerkleTreeCapVarLength> {
    caps.iter()
        .map(|cap| cap.iter().copied().collect_vec())
        .map(|cap| MerkleTreeCapVarLength { cap })
        .collect_vec()
}

pub(crate) fn get_tree_caps(
    accessors: &Vec<UnsafeAccessor<[Digest]>>,
) -> Vec<MerkleTreeCapVarLength> {
    let tree_caps = accessors
        .iter()
        .map(|accessor| unsafe { accessor.get() })
        .collect_vec();
    transform_tree_caps(&tree_caps)
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
