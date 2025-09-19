use super::context::ProverContext;
use super::trace_holder::{get_tree_caps, TraceHolder, TreesCacheMode, TreesHolder};
use super::transfer::Transfer;
use super::BF;
use crate::blake2s::Digest;
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use fft::GoodAllocator;
use itertools::Itertools;
use prover::merkle_trees::MerkleTreeCapVarLength;
use std::sync::Arc;

#[derive(Clone)]
pub struct SetupTreesAndCaps {
    pub trees: Vec<Arc<Box<[Digest]>>>,
    pub caps: Arc<Vec<MerkleTreeCapVarLength>>,
}

pub struct SetupPrecomputations<'a> {
    pub(crate) trace_holder: TraceHolder<BF>,
    pub(crate) transfer: Transfer<'a>,
    pub(crate) trees_and_caps: SetupTreesAndCaps,
    pub(crate) is_extended: bool,
}

impl<'a> SetupPrecomputations<'a> {
    pub fn new(
        circuit: &CompiledCircuitArtifact<BF>,
        log_lde_factor: u32,
        log_tree_cap_size: u32,
        recompute_cosets: bool,
        trees_and_caps: SetupTreesAndCaps,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let trace_len = circuit.trace_len;
        assert!(trace_len.is_power_of_two());
        let log_domain_size = trace_len.trailing_zeros();
        let columns_count = circuit.setup_layout.total_width;
        let trace_holder = TraceHolder::new(
            log_domain_size,
            log_lde_factor,
            0,
            log_tree_cap_size,
            columns_count,
            true,
            true,
            recompute_cosets,
            TreesCacheMode::CacheNone,
            context,
        )?;
        let transfer = Transfer::new()?;
        transfer.record_allocated(context)?;
        Ok(Self {
            trace_holder,
            transfer,
            trees_and_caps,
            is_extended: false,
        })
    }

    pub fn schedule_transfer(
        &mut self,
        trace: Arc<Vec<BF, impl GoodAllocator + 'a>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let dst = self.trace_holder.get_uninit_evaluations_mut();
        self.transfer.schedule(trace, dst, context)?;
        self.transfer.record_transferred(context)
    }

    pub fn ensure_is_extended(&mut self, context: &ProverContext) -> CudaResult<()> {
        if self.is_extended {
            return Ok(());
        }
        self.extend(context)
    }

    fn extend(&mut self, context: &ProverContext) -> CudaResult<()> {
        self.transfer.ensure_transferred(context)?;
        self.trace_holder
            .make_evaluations_sum_to_zero_and_extend(context)?;
        self.is_extended = true;
        Ok(())
    }

    pub fn get_trees_and_caps(
        circuit: &CompiledCircuitArtifact<BF>,
        log_lde_factor: u32,
        log_tree_cap_size: u32,
        trace: Arc<Vec<BF, impl GoodAllocator>>,
        context: &ProverContext,
    ) -> CudaResult<SetupTreesAndCaps> {
        let trace_len = circuit.trace_len;
        assert!(trace_len.is_power_of_two());
        let log_domain_size = trace_len.trailing_zeros();
        let columns_count = circuit.setup_layout.total_width;
        let mut trace_holder = TraceHolder::new(
            log_domain_size,
            log_lde_factor,
            0,
            log_tree_cap_size,
            columns_count,
            true,
            true,
            false,
            TreesCacheMode::CacheFull,
            context,
        )?;
        let mut transfer = Transfer::new()?;
        transfer.record_allocated(context)?;
        let dst = trace_holder.get_uninit_evaluations_mut();
        transfer.schedule(trace, dst, context)?;
        transfer.record_transferred(context)?;
        transfer.ensure_transferred(context)?;
        trace_holder.make_evaluations_sum_to_zero_extend_and_commit(context)?;
        let streams = [context.get_exec_stream(), context.get_aux_stream()];
        for stream in streams {
            stream.synchronize()?;
        }
        let caps = get_tree_caps(&trace_holder.get_tree_caps_accessors());
        let d_trees = match &trace_holder.trees {
            TreesHolder::Full(trees) => trees,
            _ => unreachable!(),
        };
        let lde_factor = 1usize << log_lde_factor;
        let tree_len = 1usize << (log_domain_size + 1);
        assert!(tree_len.is_multiple_of(CHUNK_SIZE));
        let mut trees = (0..lde_factor)
            .into_iter()
            .map(|_| unsafe { Box::new_uninit_slice(tree_len).assume_init() })
            .collect_vec();
        const CHUNK_SIZE: usize = 1 << 20; // 32 MB
        let mut chunks = unsafe {
            [
                context.alloc_host_uninit_slice(CHUNK_SIZE),
                context.alloc_host_uninit_slice(CHUNK_SIZE),
            ]
        };
        let mut callbacks = transfer.callbacks;
        let mut i = 0;
        for (coset_index, tree) in trees.iter_mut().enumerate() {
            let d_tree = &d_trees[coset_index];
            assert_eq!(d_tree.len(), tree_len);
            for (src, dst) in d_tree
                .chunks(CHUNK_SIZE)
                .zip_eq(tree.chunks_exact_mut(CHUNK_SIZE))
            {
                let stream = streams[i % 2];
                let chunk = &mut chunks[i % 2];
                i += 1;
                memory_copy_async(chunk, src, stream)?;
                let chunk = chunk.get_accessor();
                let copy_fn = {
                    move || unsafe {
                        let chunk = <[Digest]>::as_ptr(chunk.get());
                        let dst = <[Digest]>::as_ptr(dst) as *mut Digest;
                        std::ptr::copy_nonoverlapping(chunk, dst, CHUNK_SIZE);
                    }
                };
                callbacks.schedule(copy_fn, stream)?;
            }
        }
        for stream in streams {
            stream.synchronize()?;
        }
        drop(callbacks);
        let trees = trees.into_iter().map(Arc::new).collect_vec();
        let caps = Arc::new(caps);
        Ok(SetupTreesAndCaps { trees, caps })
    }
}
