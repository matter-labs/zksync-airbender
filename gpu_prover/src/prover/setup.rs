use super::context::ProverContext;
use super::trace_holder::{
    get_tree_caps, CosetsCacheMode, TraceHolder, TreesCacheMode, TreesHolder,
    PARTIAL_TREE_REDUCTION_LAYERS,
};
use super::transfer::Transfer;
use super::BF;
use crate::allocator::host::ConcurrentStaticHostAllocator;
use crate::blake2s::Digest;
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::memory::{memory_copy, CudaHostAllocFlags, HostAllocation};
use era_cudart::result::CudaResult;
use era_cudart_sys::CudaError;
use fft::GoodAllocator;
use prover::merkle_trees::MerkleTreeCapVarLength;
use std::mem::size_of;
use std::ops::{Deref, DerefMut};
use std::sync::Arc;

pub(crate) type SetupPartialTreeHost = Arc<Vec<Digest, ConcurrentStaticHostAllocator>>;

const SETUP_PARTIAL_TREE_HOST_LOG_CHUNK_SIZE: u32 = 12;

fn allocate_setup_partial_tree_host(
    elements: usize,
) -> CudaResult<Vec<Digest, ConcurrentStaticHostAllocator>> {
    let chunk_bytes = 1usize << SETUP_PARTIAL_TREE_HOST_LOG_CHUNK_SIZE;
    let requested_bytes = elements
        .checked_mul(size_of::<Digest>())
        .ok_or(CudaError::ErrorInvalidValue)?;
    let allocation_bytes = requested_bytes
        .checked_add(chunk_bytes - 1)
        .map(|bytes| bytes / chunk_bytes * chunk_bytes)
        .filter(|bytes| *bytes != 0)
        .ok_or(CudaError::ErrorInvalidValue)?;
    let allocation = HostAllocation::alloc(allocation_bytes, CudaHostAllocFlags::PORTABLE)?;
    let allocator =
        ConcurrentStaticHostAllocator::new([allocation], SETUP_PARTIAL_TREE_HOST_LOG_CHUNK_SIZE);
    let mut tree = Vec::with_capacity_in(elements, allocator);
    unsafe { tree.set_len(elements) };
    Ok(tree)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct SetupTreeCacheMetadata {
    log_domain_size: u32,
    log_lde_factor: u32,
    log_tree_cap_size: u32,
}

impl SetupTreeCacheMetadata {
    fn new(log_domain_size: u32, log_lde_factor: u32, log_tree_cap_size: u32) -> Self {
        Self {
            log_domain_size,
            log_lde_factor,
            log_tree_cap_size,
        }
    }

    fn partial_tree_len(self) -> Option<usize> {
        self.log_domain_size
            .checked_add(1)?
            .checked_sub(PARTIAL_TREE_REDUCTION_LAYERS)
            .and_then(|exponent| 1usize.checked_shl(exponent))
    }
}

#[derive(Clone)]
pub struct SetupTreesAndCaps {
    pub caps: Arc<Vec<MerkleTreeCapVarLength>>,
    pub(crate) partial_trees: Arc<Vec<SetupPartialTreeHost>>,
    pub(crate) metadata: SetupTreeCacheMetadata,
}

pub struct SetupPrecomputations<'a> {
    pub(crate) trace_holder: TraceHolder<BF>,
    pub(crate) transfer: Transfer<'a>,
    pub(crate) trees_and_caps: SetupTreesAndCaps,
    input_is_ready: bool,
    is_extended: bool,
}

impl<'a> SetupPrecomputations<'a> {
    pub fn new(
        circuit: &CompiledCircuitArtifact<BF>,
        log_lde_factor: u32,
        log_tree_cap_size: u32,
        cosets_cache_mode: CosetsCacheMode,
        trees_and_caps: SetupTreesAndCaps,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let trace_len = circuit.trace_len;
        assert!(trace_len.is_power_of_two());
        let log_domain_size = trace_len.trailing_zeros();
        let expected_metadata =
            SetupTreeCacheMetadata::new(log_domain_size, log_lde_factor, log_tree_cap_size);
        if trees_and_caps.metadata != expected_metadata {
            return Err(CudaError::ErrorInvalidValue);
        }
        let expected_tree_count = 1usize << log_lde_factor;
        let expected_tree_len = expected_metadata
            .partial_tree_len()
            .ok_or(CudaError::ErrorInvalidValue)?;
        if trees_and_caps.partial_trees.len() != expected_tree_count
            || trees_and_caps
                .partial_trees
                .iter()
                .any(|tree| tree.len() != expected_tree_len)
        {
            return Err(CudaError::ErrorInvalidValue);
        }

        let columns_count = circuit.setup_layout.total_width;
        let trace_holder = TraceHolder::new_deferred_cosets(
            log_domain_size,
            log_lde_factor,
            0,
            log_tree_cap_size,
            columns_count,
            true,
            true,
            cosets_cache_mode,
            TreesCacheMode::CachePatrial,
            context,
        )?;
        let transfer = Transfer::new()?;
        transfer.record_allocated(context)?;
        Ok(Self {
            trace_holder,
            transfer,
            trees_and_caps,
            input_is_ready: false,
            is_extended: false,
        })
    }

    pub fn schedule_transfer(
        &mut self,
        trace: Arc<Vec<BF, impl GoodAllocator + 'a>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut dst = self.trace_holder.get_uninit_evaluations_mut();
        self.transfer.schedule(trace, dst.deref_mut(), context)?;
        drop(dst);
        let device_trees = self
            .trace_holder
            .partial_trees_mut()
            .expect("setup always uses partial device trees");
        assert_eq!(self.trees_and_caps.partial_trees.len(), device_trees.len());
        for (host_tree, device_tree) in self
            .trees_and_caps
            .partial_trees
            .iter()
            .zip(device_trees.iter_mut())
        {
            self.transfer
                .schedule(host_tree.clone(), device_tree.deref_mut(), context)?;
        }
        self.transfer.record_transferred(context)
    }

    pub(crate) fn ensure_input_is_ready(&mut self, context: &ProverContext) -> CudaResult<()> {
        if !self.input_is_ready {
            self.transfer.ensure_transferred(context)?;
            self.trace_holder.make_evaluations_sum_to_zero(context)?;
            self.input_is_ready = true;
        }
        Ok(())
    }

    pub fn ensure_is_extended(&mut self, context: &ProverContext) -> CudaResult<()> {
        if !self.is_extended {
            self.ensure_input_is_ready(context)?;
            self.trace_holder.materialize_coset(1, context)?;
            self.is_extended = true;
        }
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
            CosetsCacheMode::CacheFull,
            TreesCacheMode::CachePatrial,
            context,
        )?;
        let mut transfer = Transfer::new()?;
        transfer.record_allocated(context)?;
        let mut dst = trace_holder.get_uninit_evaluations_mut();
        transfer.schedule(trace, dst.deref_mut(), context)?;
        drop(dst);
        transfer.record_transferred(context)?;
        transfer.ensure_transferred(context)?;
        trace_holder.make_evaluations_sum_to_zero_extend_and_commit(context)?;
        context.get_exec_stream().synchronize()?;

        let caps = Arc::new(get_tree_caps(&trace_holder.get_tree_caps_accessors()));
        let metadata =
            SetupTreeCacheMetadata::new(log_domain_size, log_lde_factor, log_tree_cap_size);
        let TreesHolder::Partial(device_trees) = &trace_holder.trees else {
            unreachable!("setup cold initialization always builds partial trees");
        };
        let expected_tree_len = metadata
            .partial_tree_len()
            .ok_or(CudaError::ErrorInvalidValue)?;
        let mut partial_trees = Vec::with_capacity(device_trees.len());
        for device_tree in device_trees {
            if device_tree.len() != expected_tree_len {
                return Err(CudaError::ErrorInvalidValue);
            }
            let mut host_tree = allocate_setup_partial_tree_host(device_tree.len())?;
            memory_copy(host_tree.as_mut_slice(), device_tree.deref())?;
            partial_trees.push(Arc::new(host_tree));
        }
        Ok(SetupTreesAndCaps {
            caps,
            partial_trees: Arc::new(partial_trees),
            metadata,
        })
    }
}
