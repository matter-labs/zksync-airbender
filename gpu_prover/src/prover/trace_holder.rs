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

// pub fn populate_trace_ldes<C: ProverContext>(
//     transfer: TraceTransfer<BF, C>,
//     mut cosets: VecDeque<C::Allocation<BF>>,
//     log_domain_size: u32,
//     log_lde_factor: u32,
//     context: &C,
// ) -> CudaResult<Vec<C::Allocation<BF>>> {
//     let TraceTransfer {
//         trace,
//         log_chunk_size,
//         even_padding,
//         temp_allocation,
//         final_allocation,
//         transferred_events,
//         ..
//     } = transfer;
//     assert!(even_padding);
//     assert_ne!(log_chunk_size, 0);
//     let length = trace.len();
//     let width = trace.width();
//     assert_eq!(length.trailing_zeros(), log_domain_size);
//     assert_eq!(cosets.len(), (1 << log_lde_factor) - 1);
//     let padded_width = width.next_multiple_of(2);
//     let len = length * width;
//     let stream = context.get_exec_stream();
//     let mut evaluations = final_allocation.unwrap();
//     assert_eq!(evaluations.len(), length * padded_width);
//     if padded_width != width {
//         set_to_zero(&mut evaluations[len..], stream)?;
//     }
//     let stream = context.get_exec_stream();
//     let evaluations_ref: &mut DeviceSlice<BF> = evaluations.deref_mut();
//     let mut offset = 0;
//     let target_l2_chunk_len = length * BF_COLS_CHUNK_FOR_L2;
//     for (chunk, event) in evaluations_ref
//         .chunks_mut(length << log_chunk_size)
//         .zip_eq(transferred_events.into_iter())
//     {
//         stream.wait_event(&event, CudaStreamWaitEventFlags::DEFAULT)?;
//         // The logic here should do the right thing for "tail chunks"
//         // if the target_l2_chunk_len does not evenly divide chunk.len(),
//         // even if target_l2_chunk_len happens to be >= chunk.len().
//         for l2_chunk in chunk.chunks_mut(target_l2_chunk_len) {
//             let l2_chunk_len = l2_chunk.len();
//             assert!(offset < len);
//             make_trace_evaluations_sum_to_zero(
//                 &mut l2_chunk[..l2_chunk_len.min(len - offset)],
//                 log_domain_size,
//                 context,
//             )?;
//             let range = offset..offset + l2_chunk_len;
//             let mut ldes = iter::once(l2_chunk)
//                 .chain(cosets.iter_mut().map(|coset| &mut coset[range.clone()]))
//                 .collect_vec();
//             extend_trace(&mut ldes, 0, log_domain_size, log_lde_factor, stream)?;
//             offset += l2_chunk_len;
//         }
//     }
//     drop(temp_allocation);
//     let result = iter::once(evaluations)
//         .chain(cosets.into_iter())
//         .collect_vec();
//     Ok(result)
// }
//
// pub(crate) fn compare_row_major_trace_ldes<
//     const N: usize,
//     A: GoodAllocator,
//     L: DerefMut<Target = DeviceSlice<BF>>,
// >(
//     cpu_data: &[CosetBoundTracePart<N, A>],
//     gpu_data: &[L],
// ) {
//     let mut error_count = 0;
//     for (coset, (cpu_lde, gpu_lde)) in cpu_data.iter().zip(gpu_data.iter()).enumerate() {
//         let trace_len = cpu_lde.trace.len();
//         let gpu_lde_len = gpu_lde.len();
//         assert_eq!(gpu_lde_len % trace_len, 0);
//         let gpu_cols = gpu_lde_len / trace_len;
//         let mut h_trace = vec![BF::default(); gpu_lde_len];
//         memory_copy(&mut h_trace, gpu_lde.deref()).unwrap();
//         let mut gpu_lde = vec![BF::default(); gpu_lde_len];
//         assert_eq!(cpu_lde.trace.width().next_multiple_of(2), gpu_cols);
//         transpose::transpose(&h_trace, &mut gpu_lde, trace_len, gpu_cols);
//         let mut view = cpu_lde.trace.row_view(0..trace_len);
//         for (row, gpu_row) in gpu_lde.chunks(gpu_cols).enumerate() {
//             let cpu_row = view.current_row_ref();
//             let gpu_row = &gpu_row[..cpu_row.len()];
//             if cpu_row != gpu_row {
//                 dbg!(coset, row, cpu_row, gpu_row);
//                 error_count += 1;
//                 if error_count > 4 {
//                     panic!("too many errors");
//                 }
//             }
//             view.advance_row();
//         }
//     }
//     assert_eq!(error_count, 0);
// }
//
// pub(crate) fn compare_column_major_trace_ldes<
//     A: GoodAllocator,
//     L: DerefMut<Target = DeviceSlice<E4>>,
// >(
//     cpu_data: &[CosetBoundColumnMajorTracePart<A>],
//     gpu_data: &[L],
// ) {
//     for (coset, (cpu_lde, gpu_lde)) in cpu_data.iter().zip(gpu_data.iter()).enumerate() {
//         let cpu_trace = &cpu_lde.trace;
//         let trace_len = cpu_trace.len();
//         let cols = cpu_trace.width();
//         let gpu_lde_len = gpu_lde.len();
//         assert_eq!(gpu_lde.len(), trace_len * cols);
//         let mut h_gpu_lde = vec![E4::default(); gpu_lde_len];
//         memory_copy(&mut h_gpu_lde, gpu_lde.deref()).unwrap();
//         for (col, (gpu_col, cpu_col)) in h_gpu_lde
//             .chunks(trace_len)
//             .zip(cpu_trace.columns_iter())
//             .enumerate()
//         {
//             if gpu_col != cpu_col {
//                 for (i, (cpu, gpu)) in cpu_col.iter().zip(gpu_col.iter()).enumerate() {
//                     assert_eq!(cpu, gpu, "coset: {}, col: {}, index: {}", coset, col, i);
//                 }
//             }
//         }
//     }
// }
//
// pub(crate) fn compare_trace_trees<A: GoodAllocator, T: DerefMut<Target = DeviceSlice<Digest>>>(
//     cpu_trees: &[Blake2sU32MerkleTreeWithCap<A>],
//     gpu_trees: &[T],
//     log_lde_factor: u32,
//     log_tree_cap_size: u32,
// ) {
//     let log_coset_tree_cap_size = log_tree_cap_size - log_lde_factor;
//     let coset_tree_cap_size = 1 << log_coset_tree_cap_size;
//     for (coset, (cpu_tree, gpu_tree)) in cpu_trees.iter().zip(gpu_trees.iter()).enumerate() {
//         let cpu_leaf_hashes = &cpu_tree.leaf_hashes;
//         let leafs_count = cpu_tree.leaf_hashes.len();
//         assert_eq!(gpu_tree.len(), leafs_count << 1);
//         let mut h_tree = vec![Digest::default(); leafs_count << 1];
//         memory_copy(&mut h_tree, gpu_tree.deref()).unwrap();
//         let gpu_leaf_hashes = &h_tree[..leafs_count];
//         if cpu_leaf_hashes != gpu_leaf_hashes {
//             cpu_leaf_hashes
//                 .iter()
//                 .zip(gpu_leaf_hashes.iter())
//                 .enumerate()
//                 .for_each(|(i, (c, g))| {
//                     assert_eq!(c, g, "coset: {}, leaf: {}", coset, i);
//                 });
//         }
//         let cpu_cap = cpu_tree.get_cap().cap;
//         assert_eq!(cpu_cap.len(), coset_tree_cap_size);
//         let offset = (leafs_count - coset_tree_cap_size) << 1;
//         assert_eq!(cpu_cap, h_tree[offset..][..coset_tree_cap_size]);
//     }
// }
//
// #[derive(Copy, Clone)]
// pub enum TraceTransferAllocationType {
//     None,
//     Temp(usize),
//     Final,
// }
//
// pub(crate) struct TraceTransfer<'a, T: Copy + Send + Sync + 'static, C: ProverContext> {
//     pub(crate) trace: &'a ColumnMajorTrace<T, C::HostAllocator>,
//     pub(crate) log_chunk_size: u32,
//     pub(crate) allocation_type: TraceTransferAllocationType,
//     pub(crate) even_padding: bool,
//     pub(crate) temp_allocation: Option<C::Allocation<T>>,
//     pub(crate) final_allocation: Option<C::Allocation<T>>,
//     pub(crate) allocated_event: CudaEvent,
//     pub(crate) scheduled_count: usize,
//     pub(crate) transferred_events: VecDeque<CudaEvent>,
// }
//
// impl<'a, T: Copy + Send + Sync + 'static, C: ProverContext> TraceTransfer<'a, T, C> {
//     pub fn new(
//         trace: &'a ColumnMajorTrace<T, C::HostAllocator>,
//         log_chunk_size: u32,
//         allocation_type: TraceTransferAllocationType,
//         even_padding: bool,
//         context: &C,
//     ) -> CudaResult<Self> {
//         let width = trace.width();
//         let padded_width = if even_padding {
//             assert_ne!(log_chunk_size, 0);
//             width.next_multiple_of(2)
//         } else {
//             width
//         };
//         let len = trace.len();
//         let (temp_allocation, final_allocation) = match allocation_type {
//             TraceTransferAllocationType::None => (None, None),
//             TraceTransferAllocationType::Temp(chunks_count) => {
//                 let count = chunks_count << log_chunk_size;
//                 assert!(count < padded_width);
//                 (Some(context.alloc(len * count)?), None)
//             }
//             TraceTransferAllocationType::Final => (None, Some(context.alloc(len * padded_width)?)),
//         };
//         let allocated_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
//         if matches!(allocation_type, TraceTransferAllocationType::None) {
//             allocated_event.record(context.get_exec_stream())?;
//         }
//         let result = Self {
//             trace,
//             log_chunk_size,
//             allocation_type,
//             even_padding,
//             temp_allocation,
//             final_allocation,
//             allocated_event,
//             scheduled_count: 0,
//             transferred_events: VecDeque::new(),
//         };
//         Ok(result)
//     }
//
//     pub fn schedule(&mut self, max_columns_count: Option<usize>, context: &C) -> CudaResult<usize> {
//         let width = match self.allocation_type {
//             TraceTransferAllocationType::None => return Ok(0),
//             TraceTransferAllocationType::Temp(chunks_count) => chunks_count << self.log_chunk_size,
//             TraceTransferAllocationType::Final => self.trace.width(),
//         };
//         let len = self.trace.len();
//         let mut remaining_count = width - self.scheduled_count;
//         if let Some(max_columns_count) = max_columns_count {
//             remaining_count = remaining_count.min(max_columns_count);
//         }
//         if remaining_count == 0 {
//             return Ok(0);
//         }
//         let stream = context.get_h2d_stream();
//         let range = self.scheduled_count * len..(self.scheduled_count + remaining_count) * len;
//         let allocation = self
//             .temp_allocation
//             .as_mut()
//             .or(self.final_allocation.as_mut())
//             .unwrap();
//         if self.scheduled_count == 0 {
//             stream.wait_event(&self.allocated_event, CudaStreamWaitEventFlags::DEFAULT)?;
//         }
//         memory_copy_async(
//             &mut allocation[range.clone()],
//             &self.trace.as_slice()[range],
//             stream,
//         )?;
//         self.scheduled_count += remaining_count;
//         Ok(remaining_count)
//     }
//
//     pub fn final_scheduled_count(&self) -> usize {
//         match self.allocation_type {
//             TraceTransferAllocationType::None => 0,
//             TraceTransferAllocationType::Temp(chunks_count) => chunks_count << self.log_chunk_size,
//             TraceTransferAllocationType::Final => self.trace.width(),
//         }
//     }
//
//     pub fn padded_width(&self) -> usize {
//         let width = self.trace.width();
//         if self.even_padding {
//             width.next_multiple_of(2)
//         } else {
//             width
//         }
//     }
//
//     pub fn allocate_final(&mut self, context: &C) -> CudaResult<()> {
//         assert_eq!(self.scheduled_count, self.final_scheduled_count());
//         if matches!(
//             self.allocation_type,
//             TraceTransferAllocationType::None | TraceTransferAllocationType::Temp(_)
//         ) {
//             self.final_allocation = Some(context.alloc(self.trace.len() * self.padded_width())?);
//             self.allocated_event.record(context.get_exec_stream())?;
//         }
//         Ok(())
//     }
//
//     pub fn transfer_final(&mut self, context: &C) -> CudaResult<()> {
//         assert_eq!(self.scheduled_count, self.final_scheduled_count());
//         assert!(self.final_allocation.is_some());
//         let length = self.trace.len();
//         let width = self.trace.width();
//         let stream = context.get_h2d_stream();
//         stream.wait_event(&self.allocated_event, CudaStreamWaitEventFlags::DEFAULT)?;
//         let final_allocation = self.final_allocation.as_mut().unwrap();
//         let values: &mut DeviceSlice<T> = final_allocation.deref_mut();
//         let chunk_size = length << self.log_chunk_size;
//         for (i, (result_chunk, trace_chunk)) in values
//             .chunks_mut(chunk_size)
//             .zip(self.trace.as_slice().chunks(chunk_size))
//             .enumerate()
//         {
//             let count = i << self.log_chunk_size;
//             let offset = count * length;
//             if self.temp_allocation.is_some() && count < self.scheduled_count {
//                 let range = offset..offset + result_chunk.len();
//                 let src = &self.temp_allocation.as_ref().unwrap()[range];
//                 memory_copy_async(result_chunk, src, stream)?;
//             } else if self.scheduled_count != width {
//                 memory_copy_async(&mut result_chunk[..trace_chunk.len()], trace_chunk, stream)?;
//             }
//             let event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
//             event.record(stream)?;
//             self.transferred_events.push_back(event);
//         }
//         Ok(())
//     }
// }
