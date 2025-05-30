use super::context::{DeviceProperties, ProverContext};
use super::BF;
use crate::blake2s::{build_merkle_tree, merkle_tree_cap, Digest};
use crate::device_structures::{DeviceMatrix, DeviceMatrixChunkMut, DeviceMatrixMut};
use crate::ntt::{
    bitrev_Z_to_natural_composition_main_evals, natural_composition_coset_evals_to_bitrev_Z,
    natural_main_evals_to_natural_coset_evals,
};
use crate::ops_cub::device_reduce::{get_reduce_temp_storage_bytes, reduce, ReduceOperation};
use crate::ops_simple::{neg, set_to_zero};
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, DeviceSlice};
use era_cudart::stream::{CudaStream, CudaStreamWaitEventFlags};
use fft::GoodAllocator;
use itertools::Itertools;
use prover::merkle_trees::MerkleTreeCapVarLength;
use std::ops::DerefMut;
use std::sync::Arc;

pub struct TraceHolder<T: Sync, C: ProverContext> {
    pub(crate) log_domain_size: u32,
    pub(crate) log_lde_factor: u32,
    pub(crate) log_rows_per_leaf: u32,
    pub(crate) log_tree_cap_size: u32,
    pub(crate) columns_count: usize,
    pub(crate) padded_to_even: bool,
    pub(crate) ldes: Vec<C::Allocation<T>>,
    pub(crate) trees: Vec<C::Allocation<Digest>>,
    pub(crate) tree_caps: Option<Arc<Vec<Vec<Digest, C::HostAllocator>>>>,
}

impl<C: ProverContext> TraceHolder<BF, C> {
    pub fn make_evaluations_sum_to_zero(&mut self, context: &C) -> CudaResult<()> {
        make_evaluations_sum_to_zero(
            &mut self.ldes[0],
            self.log_domain_size,
            self.columns_count,
            self.padded_to_even,
            context,
        )
    }

    pub fn extend_and_commit(&mut self, source_coset_index: usize, context: &C) -> CudaResult<()> {
        extend_trace(
            &mut self.ldes,
            source_coset_index,
            self.log_domain_size,
            self.log_lde_factor,
            context.get_exec_stream(),
            context.get_aux_stream(),
            context.get_device_properties(),
        )?;
        populate_trees_from_trace_ldes::<C>(
            &self.ldes,
            &mut self.trees,
            self.log_domain_size,
            self.log_lde_factor,
            self.log_rows_per_leaf,
            self.log_tree_cap_size,
            self.columns_count,
            context.get_exec_stream(),
        )
    }

    pub fn make_evaluations_sum_to_zero_extend_and_commit(
        &mut self,
        context: &C,
    ) -> CudaResult<()> {
        self.make_evaluations_sum_to_zero(context)?;
        self.extend_and_commit(0, context)
    }
}
impl<T: Sync, C: ProverContext> TraceHolder<T, C> {
    pub fn new(
        log_domain_size: u32,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
        columns_count: usize,
        pad_to_even: bool,
        context: &C,
    ) -> CudaResult<Self> {
        let padded_to_even = pad_to_even && columns_count.next_multiple_of(2) != columns_count;
        let instances_count = 1 << log_lde_factor;
        let ldes = allocate_ldes(
            log_domain_size,
            instances_count,
            columns_count,
            pad_to_even,
            context,
        )?;
        let trees = allocate_trees(log_domain_size, instances_count, log_rows_per_leaf, context)?;
        Ok(Self {
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            padded_to_even,
            ldes,
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
        context: &C,
    ) -> CudaResult<Self> {
        let padded_to_even = pad_to_even && columns_count.next_multiple_of(2) != columns_count;
        let ldes = allocate_ldes(log_domain_size, 1, columns_count, pad_to_even, context)?;
        let trees = vec![];
        Ok(Self {
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            padded_to_even,
            ldes,
            trees,
            tree_caps: None,
        })
    }

    pub fn allocate_to_full(&mut self, context: &C) -> CudaResult<()> {
        let instances_count = 1 << self.log_lde_factor;
        assert_eq!(self.ldes.len(), 1);
        let ldes = allocate_ldes(
            self.log_domain_size,
            instances_count - 1,
            self.columns_count,
            self.padded_to_even,
            context,
        )?;
        self.ldes.extend(ldes);
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

    pub fn get_coset_evaluations(&self, coset_index: usize) -> &DeviceSlice<T> {
        &self.ldes[coset_index][..self.columns_count << self.log_domain_size]
    }

    pub fn get_coset_evaluations_mut(&mut self, coset_index: usize) -> &mut DeviceSlice<T> {
        &mut self.ldes[coset_index][..self.columns_count << self.log_domain_size]
    }

    pub fn get_evaluations(&self) -> &DeviceSlice<T> {
        self.get_coset_evaluations(0)
    }

    pub fn get_evaluations_mut(&mut self) -> &mut DeviceSlice<T> {
        self.get_coset_evaluations_mut(0)
    }

    pub fn produce_tree_caps(&mut self, context: &C) -> CudaResult<()> {
        if self.tree_caps.is_some() {
            return Ok(());
        }
        let mut tree_caps = allocate_tree_caps::<C>(self.log_lde_factor, self.log_tree_cap_size);
        transfer_tree_caps(
            &self.trees,
            &mut tree_caps,
            self.log_lde_factor,
            self.log_tree_cap_size,
            context.get_exec_stream(),
        )?;
        self.tree_caps = Some(Arc::new(tree_caps));
        Ok(())
    }

    pub fn get_tree_caps(&self) -> Arc<Vec<Vec<Digest, C::HostAllocator>>> {
        self.tree_caps.clone().unwrap()
    }
}

pub(crate) fn allocate_ldes<T: Sync, C: ProverContext>(
    log_domain_size: u32,
    instances_count: usize,
    columns_count: usize,
    pad_to_even: bool,
    context: &C,
) -> CudaResult<Vec<C::Allocation<T>>> {
    let columns_count = if pad_to_even {
        columns_count.next_multiple_of(2)
    } else {
        columns_count
    };
    let size = columns_count << log_domain_size;
    let mut result = Vec::with_capacity(instances_count);
    for _ in 0..instances_count {
        result.push(context.alloc(size)?);
    }
    Ok(result)
}

pub(crate) fn allocate_trees<C: ProverContext>(
    log_domain_size: u32,
    instances_count: usize,
    log_rows_per_leaf: u32,
    context: &C,
) -> CudaResult<Vec<C::Allocation<Digest>>> {
    let size = 1 << (log_domain_size + 1 - log_rows_per_leaf);
    let mut result = Vec::with_capacity(instances_count);
    for _ in 0..instances_count {
        result.push(context.alloc(size)?);
    }
    Ok(result)
}

pub(crate) fn allocate_tree_caps<C: ProverContext>(
    log_lde_factor: u32,
    log_tree_cap_size: u32,
) -> Vec<Vec<Digest, C::HostAllocator>> {
    let lde_factor = 1 << log_lde_factor;
    let log_coset_tree_cap_size = log_tree_cap_size - log_lde_factor;
    let coset_tree_cap_size = 1 << log_coset_tree_cap_size;
    let mut result = Vec::with_capacity(lde_factor);
    for _ in 0..lde_factor {
        let mut tree_cap = Vec::with_capacity_in(coset_tree_cap_size, C::HostAllocator::default());
        unsafe { tree_cap.set_len(coset_tree_cap_size) };
        result.push(tree_cap);
    }
    result
}

pub(crate) fn make_evaluations_sum_to_zero<C: ProverContext>(
    evaluations: &mut DeviceSlice<BF>,
    log_domain_size: u32,
    columns_count: usize,
    padded_to_even: bool,
    context: &C,
) -> CudaResult<()> {
    let domain_size = 1 << log_domain_size;
    let mut reduce_result = context.alloc(columns_count)?;
    let reduce_temp_storage_bytes =
        get_reduce_temp_storage_bytes::<BF>(ReduceOperation::Sum, (domain_size - 1) as i32)?;
    let mut reduce_temp_storage_0 = context.alloc(reduce_temp_storage_bytes)?;
    let mut reduce_temp_storage_1 = context.alloc(reduce_temp_storage_bytes)?;
    let reduce_temp_storage_refs = [&mut reduce_temp_storage_0, &mut reduce_temp_storage_1];
    let exec_stream = context.get_exec_stream();
    let aux_stream = context.get_aux_stream();
    let stream_refs = [exec_stream, aux_stream];
    let start_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    let end_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    start_event.record(exec_stream)?;
    aux_stream.wait_event(&start_event, CudaStreamWaitEventFlags::DEFAULT)?;
    for (i, col) in evaluations
        .chunks(domain_size)
        .take(columns_count)
        .enumerate()
    {
        reduce(
            ReduceOperation::Sum,
            reduce_temp_storage_refs[i & 1],
            &col[..domain_size - 1],
            &mut reduce_result[i],
            stream_refs[i & 1],
        )?;
    }
    end_event.record(aux_stream)?;
    exec_stream.wait_event(&end_event, CudaStreamWaitEventFlags::DEFAULT)?;
    context.free(reduce_temp_storage_0)?;
    context.free(reduce_temp_storage_1)?;
    neg(
        &DeviceMatrix::new(&reduce_result, 1),
        &mut DeviceMatrixChunkMut::new(
            &mut evaluations[..columns_count << log_domain_size],
            domain_size,
            domain_size - 1,
            1,
        ),
        exec_stream,
    )?;
    context.free(reduce_result)?;
    if padded_to_even {
        set_to_zero(
            &mut evaluations[columns_count << log_domain_size..],
            exec_stream,
        )?;
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

pub(crate) fn populate_trees_from_trace_ldes<C: ProverContext>(
    ldes: &[C::Allocation<BF>],
    trees: &mut [C::Allocation<Digest>],
    log_domain_size: u32,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_tree_cap_size: u32,
    columns_count: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    let lde_factor = 1 << log_lde_factor;
    assert_eq!(ldes.len(), lde_factor);
    assert_eq!(trees.len(), lde_factor);
    for (lde, tree) in ldes.iter().zip_eq(trees.iter_mut()) {
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
    Ok(())
}

pub(crate) fn transfer_tree_caps<A: GoodAllocator, T: DerefMut<Target = DeviceSlice<Digest>>>(
    trees: &[T],
    caps: &mut [Vec<Digest, A>],
    log_lde_factor: u32,
    log_tree_cap_size: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(trees.len(), 1 << log_lde_factor);
    let log_subtree_cap_size = log_tree_cap_size - log_lde_factor;
    for (subtree, h_cap) in trees.iter().zip(caps.iter_mut()) {
        let d_cap = merkle_tree_cap(subtree, log_subtree_cap_size);
        memory_copy_async(h_cap, d_cap, stream)?;
    }
    Ok(())
}

pub(crate) fn flatten_tree_caps<A: GoodAllocator>(
    caps: &[Vec<Digest, A>],
) -> impl Iterator<Item = u32> + use<'_, A> {
    caps.iter().flatten().flatten().copied()
}

pub(crate) fn transform_tree_caps(
    caps: &[Vec<Digest, impl GoodAllocator>],
) -> Vec<MerkleTreeCapVarLength> {
    caps.iter()
        .map(|cap| cap.iter().copied().collect_vec())
        .map(|cap| MerkleTreeCapVarLength { cap })
        .collect_vec()
}

#[allow(dead_code)]
#[cfg(test)]
mod test {
    use crate::blake2s::Digest;
    use crate::prover::trace_holder::DerefMut;
    use crate::prover::BF;
    use era_cudart::memory::memory_copy;
    use era_cudart::slice::DeviceSlice;
    use fft::GoodAllocator;
    use prover::merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap;
    use prover::merkle_trees::MerkleTreeConstructor;
    use prover::prover_stages::CosetBoundTracePart;

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
