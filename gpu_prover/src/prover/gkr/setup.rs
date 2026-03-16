use std::ops::DerefMut;
use std::sync::Arc;

use cs::definitions::GKRAddress;
use cs::gkr_compiler::GKRCircuitArtifact;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::CudaSlice;
use fft::materialize_powers_serial_starting_with_one;
use field::Field;

use super::stage1::GpuGKRStage1Output;
use super::{GpuBaseFieldPoly, GpuGKRStorage};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::Digest;
use crate::ops::complex::{batch_inv_in_place, BatchInv};
use crate::ops::simple::{add_into_y, mul_into_y, set_by_ref, Add, BinaryOp, Mul, SetByRef};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext};
use crate::primitives::device_structures::DeviceVectorChunk;
use crate::primitives::device_tracing::Range;
use crate::primitives::field::BF;
use crate::primitives::static_host::{
    alloc_static_pinned_vec_from_slice, alloc_static_pinned_vec_uninit, StaticPinnedVec,
};
use crate::primitives::transfer::Transfer;
use crate::prover::trace_holder::{TraceHolder, TreesCacheMode, TreesHolder};
use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;

const SETUP_TREE_STATIC_HOST_LOG_CHUNK_SIZE: u32 = 12;

pub(crate) struct GpuGKRSetupHost {
    pub(crate) raw_hypercube_evals: StaticPinnedVec<BF>,
    pub(crate) partial_trees: Vec<StaticPinnedVec<Digest>>,
    pub(crate) tree_caps: Vec<StaticPinnedVec<Digest>>,
    pub(crate) trace_len: usize,
    pub(crate) log_domain_size: u32,
    pub(crate) columns_count: usize,
    pub(crate) log_lde_factor: u32,
    pub(crate) log_rows_per_leaf: u32,
    pub(crate) log_tree_cap_size: u32,
}

impl GpuGKRSetupHost {
    pub(crate) fn precompute_from_cpu_setup(
        setup: &CpuGKRSetup<BF>,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let columns_count = setup.hypercube_evals.len();
        assert!(columns_count > 0, "setup must contain at least one column");
        let trace_len = setup.hypercube_evals[0].len();
        assert!(
            trace_len.is_power_of_two(),
            "trace len must be a power of two"
        );
        let log_domain_size = trace_len.trailing_zeros();
        for column in setup.hypercube_evals.iter() {
            assert_eq!(column.len(), trace_len, "all setup columns must match");
        }

        let raw_hypercube_evals =
            flatten_setup_columns_into_pinned_buffer(setup, columns_count, trace_len)?;
        let (partial_trees, tree_caps) = precompute_partial_tree_cache(
            &raw_hypercube_evals,
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            context,
        )?;

        Ok(Self {
            raw_hypercube_evals,
            partial_trees,
            tree_caps,
            trace_len,
            log_domain_size,
            columns_count,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
        })
    }

    pub(crate) fn column_offset(&self, column: usize) -> usize {
        assert!(column < self.columns_count);
        column * self.trace_len
    }
}

fn bind_trace_holder_columns_into_storage<E>(
    trace_holder: &TraceHolder<BF>,
    storage: &mut GpuGKRStorage<BF, E>,
    make_address: impl Fn(usize) -> GKRAddress,
) {
    let trace_len = 1usize << trace_holder.log_domain_size;
    assert_eq!(
        trace_holder.get_hypercube_evals().len(),
        trace_holder.columns_count * trace_len,
        "trace holder backing must be laid out as flat column-major hypercube evals",
    );

    let backing = trace_holder.raw_hypercube_backing();
    for column in 0..trace_holder.columns_count {
        storage.insert_base_field_at_layer(
            0,
            make_address(column),
            GpuBaseFieldPoly::from_arc(backing.clone(), column * trace_len, trace_len),
        );
    }
}

pub(crate) struct GpuGKRSetupTransfer<'a> {
    pub(crate) host: Arc<GpuGKRSetupHost>,
    pub(crate) trace_holder: TraceHolder<BF>,
    pub(crate) transfer: Transfer<'a>,
}

pub(crate) struct GpuGKRSetupTransferHostKeepalive<'a> {
    #[allow(dead_code)]
    host: Arc<GpuGKRSetupHost>,
    #[allow(dead_code)]
    transfer_callbacks: Callbacks<'a>,
}

impl<'a> GpuGKRSetupTransfer<'a> {
    pub(crate) fn new(host: Arc<GpuGKRSetupHost>, context: &ProverContext) -> CudaResult<Self> {
        let trace_holder = TraceHolder::<BF>::new(
            host.log_domain_size,
            host.log_lde_factor,
            host.log_rows_per_leaf,
            host.log_tree_cap_size,
            host.columns_count,
            TreesCacheMode::CachePartial,
            context,
        )?;
        let transfer = Transfer::new()?;
        transfer.record_allocated(context)?;
        Ok(Self {
            host,
            trace_holder,
            transfer,
        })
    }

    pub(crate) fn schedule_transfer(&mut self, context: &ProverContext) -> CudaResult<()> {
        self.transfer.ensure_allocated(context)?;
        let stream = context.get_h2d_stream();
        memory_copy_async(
            self.trace_holder.get_uninit_hypercube_evals_mut(),
            self.host.raw_hypercube_evals.as_slice(),
            stream,
        )?;
        assert_eq!(
            self.host.partial_trees.len(),
            1usize << self.host.log_lde_factor,
            "expected one cached partial tree per coset",
        );
        for (coset_index, src_tree) in self.host.partial_trees.iter().enumerate() {
            let dst_tree = self
                .trace_holder
                .get_uninit_tree_mut(coset_index)
                .expect("setup transfers require partial-tree caching");
            memory_copy_async(dst_tree, src_tree.as_slice(), stream)?;
        }
        self.trace_holder
            .clone_tree_caps_from_slices(&self.host.tree_caps, context);
        self.transfer.record_transferred(context)
    }

    pub(crate) fn ensure_transferred(&self, context: &ProverContext) -> CudaResult<()> {
        self.transfer.ensure_transferred(context)
    }

    pub(crate) fn into_host_keepalive(self) -> GpuGKRSetupTransferHostKeepalive<'a> {
        let Self {
            host,
            trace_holder: _,
            transfer,
        } = self;
        GpuGKRSetupTransferHostKeepalive {
            host,
            transfer_callbacks: transfer.into_callbacks(),
        }
    }

    pub(crate) fn bind_setup_columns_into_storage<E>(&self, storage: &mut GpuGKRStorage<BF, E>) {
        assert_eq!(self.trace_holder.columns_count, self.host.columns_count);
        assert_eq!(
            1usize << self.trace_holder.log_domain_size,
            self.host.trace_len
        );
        bind_trace_holder_columns_into_storage(&self.trace_holder, storage, GKRAddress::Setup);
    }

    pub(crate) fn bootstrap_storage<E>(
        &self,
        memory_trace_holder: &TraceHolder<BF>,
        witness_trace_holder: &TraceHolder<BF>,
    ) -> GpuGKRStorage<BF, E> {
        for (label, trace_holder) in [
            ("memory", memory_trace_holder),
            ("witness", witness_trace_holder),
        ] {
            assert_eq!(
                trace_holder.log_domain_size, self.trace_holder.log_domain_size,
                "{label} trace holder must match setup trace length",
            );
            assert_eq!(
                trace_holder.log_lde_factor, self.trace_holder.log_lde_factor,
                "{label} trace holder must match setup LDE factor",
            );
            assert_eq!(
                trace_holder.log_rows_per_leaf, self.trace_holder.log_rows_per_leaf,
                "{label} trace holder must match setup rows per leaf",
            );
            assert_eq!(
                trace_holder.log_tree_cap_size, self.trace_holder.log_tree_cap_size,
                "{label} trace holder must match setup tree cap size",
            );
        }

        let mut storage = GpuGKRStorage::default();
        self.bind_setup_columns_into_storage(&mut storage);
        bind_trace_holder_columns_into_storage(
            memory_trace_holder,
            &mut storage,
            GKRAddress::BaseLayerMemory,
        );
        bind_trace_holder_columns_into_storage(
            witness_trace_holder,
            &mut storage,
            GKRAddress::BaseLayerWitness,
        );

        storage
    }

    pub(crate) fn bootstrap_storage_from_stage1<E>(
        &self,
        stage1: &GpuGKRStage1Output,
    ) -> GpuGKRStorage<BF, E> {
        self.bootstrap_storage(&stage1.memory_trace_holder, &stage1.witness_trace_holder)
    }

    pub(crate) fn schedule_forward_setup<E>(
        &self,
        compiled_circuit: &GKRCircuitArtifact<BF>,
        lookup_challenges: HostAllocation<[E]>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRForwardSetup<E>>
    where
        E: Field + SetByRef + BatchInv + 'static,
        Add: BinaryOp<E, E, E>,
        Add: BinaryOp<BF, E, E>,
        Mul: BinaryOp<BF, E, E>,
    {
        self.ensure_transferred(context)?;
        assert_eq!(compiled_circuit.trace_len, self.host.trace_len);
        assert_eq!(
            compiled_circuit.generic_lookup_tables_width + 2,
            self.host.columns_count
        );

        let generic_lookup_len = compiled_circuit.total_tables_size;
        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let schedule_range = Range::new("gkr.forward_setup.schedule")?;
        schedule_range.start(stream)?;
        let mut host_lookup_additive_part = unsafe { context.alloc_host_uninit_slice(1) };
        let mut device_lookup_additive_part = context.alloc(1, AllocationPlacement::BestFit)?;
        let mut host_lookup_alpha_powers = if self.host.columns_count > 3 && generic_lookup_len > 0
        {
            Some(unsafe { context.alloc_host_uninit_slice(self.host.columns_count - 2) })
        } else {
            None
        };
        let mut generic_lookup = if generic_lookup_len > 0 {
            Some(context.alloc(generic_lookup_len, AllocationPlacement::BestFit)?)
        } else {
            None
        };
        let lookup_challenges_accessor = lookup_challenges.get_accessor();
        let mut callbacks = Callbacks::new();

        let lookup_additive_part_accessor = host_lookup_additive_part.get_mut_accessor();
        let alpha_powers_accessor = host_lookup_alpha_powers
            .as_mut()
            .map(HostAllocation::get_mut_accessor);
        let alpha_powers_len = host_lookup_alpha_powers
            .as_ref()
            .map(HostAllocation::len)
            .unwrap_or(0);
        callbacks.schedule(
            move || unsafe {
                let lookup_challenges = lookup_challenges_accessor.get();
                assert!(
                    lookup_challenges.len() >= 2,
                    "lookup scheduling expects [lookup_alpha, lookup_additive_part, ...]",
                );
                let lookup_alpha = lookup_challenges[0];
                let lookup_additive_part = lookup_challenges[1];
                lookup_additive_part_accessor.get_mut()[0] = lookup_additive_part;
                if let Some(alpha_powers_accessor) = alpha_powers_accessor.as_ref() {
                    let powers = materialize_powers_serial_starting_with_one::<
                        E,
                        std::alloc::Global,
                    >(lookup_alpha, alpha_powers_len);
                    alpha_powers_accessor.get_mut().copy_from_slice(&powers);
                }
            },
            context.get_exec_stream(),
        )?;

        memory_copy_async(
            &mut device_lookup_additive_part,
            &host_lookup_additive_part,
            context.get_exec_stream(),
        )?;
        let mut device_lookup_alpha_powers =
            if let Some(host_alpha_powers) = host_lookup_alpha_powers.as_ref() {
                let mut device =
                    context.alloc(host_alpha_powers.len(), AllocationPlacement::BestFit)?;
                memory_copy_async(&mut device, host_alpha_powers, context.get_exec_stream())?;
                Some(device)
            } else {
                None
            };

        if let Some(generic_lookup) = generic_lookup.as_mut() {
            let generic_lookup_range = Range::new("gkr.forward_setup.build_generic_lookup")?;
            generic_lookup_range.start(stream)?;
            let raw = self.trace_holder.get_hypercube_evals();
            let lookup_additive_part = DeviceVectorChunk::new(&device_lookup_additive_part, 0, 1);

            let mut weighted_column = if self.host.columns_count > 3 {
                Some(context.alloc(generic_lookup.len(), AllocationPlacement::BestFit)?)
            } else {
                None
            };
            set_by_ref(&lookup_additive_part, generic_lookup.deref_mut(), stream)?;
            let base_column =
                DeviceVectorChunk::new(raw, self.host.column_offset(2), generic_lookup.len());
            add_into_y(&base_column, generic_lookup.deref_mut(), stream)?;

            if let (Some(weighted_column), Some(alpha_powers)) = (
                weighted_column.as_mut(),
                device_lookup_alpha_powers.as_ref(),
            ) {
                for setup_column in 3..self.host.columns_count {
                    let source = DeviceVectorChunk::new(
                        raw,
                        self.host.column_offset(setup_column),
                        generic_lookup.len(),
                    );
                    let challenge_power = DeviceVectorChunk::new(alpha_powers, setup_column - 2, 1);
                    set_by_ref(&challenge_power, weighted_column.deref_mut(), stream)?;
                    mul_into_y(&source, weighted_column.deref_mut(), stream)?;
                    let weighted_column_chunk =
                        DeviceVectorChunk::new(&*weighted_column, 0, weighted_column.len());
                    add_into_y(&weighted_column_chunk, generic_lookup.deref_mut(), stream)?;
                }
            }
            batch_inv_in_place(generic_lookup, stream)?;
            generic_lookup_range.end(stream)?;
            tracing_ranges.push(generic_lookup_range);
        }

        drop(device_lookup_alpha_powers);
        schedule_range.end(stream)?;
        tracing_ranges.push(schedule_range);

        Ok(GpuGKRForwardSetup {
            tracing_ranges,
            lookup_challenges,
            callbacks,
            host_lookup_additive_part,
            host_lookup_alpha_powers,
            device_lookup_additive_part,
            generic_lookup,
        })
    }
}

pub(crate) struct GpuGKRForwardSetup<E> {
    #[allow(dead_code)] // Keeps queued NVTX host callbacks alive until the stream consumes them.
    tracing_ranges: Vec<Range>,
    #[allow(dead_code)] // Keeps challenge source alive until queued callbacks consume it.
    lookup_challenges: HostAllocation<[E]>,
    #[allow(dead_code)] // Keeps queued setup callbacks alive until the stream consumes them.
    callbacks: Callbacks<'static>,
    #[allow(dead_code)] // Keeps async H2D sources alive until the queued copies complete.
    host_lookup_additive_part: HostAllocation<[E]>,
    #[allow(dead_code)] // Keeps async H2D sources alive until the queued copies complete.
    host_lookup_alpha_powers: Option<HostAllocation<[E]>>,
    device_lookup_additive_part: DeviceAllocation<E>,
    generic_lookup: Option<DeviceAllocation<E>>,
}

pub(crate) struct GpuGKRForwardSetupHostKeepalive<E> {
    #[allow(dead_code)]
    tracing_ranges: Vec<Range>,
    #[allow(dead_code)]
    lookup_challenges: HostAllocation<[E]>,
    #[allow(dead_code)]
    callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    host_lookup_additive_part: HostAllocation<[E]>,
    #[allow(dead_code)]
    host_lookup_alpha_powers: Option<HostAllocation<[E]>>,
}

impl<E> GpuGKRForwardSetup<E> {
    pub(crate) fn has_generic_lookup(&self) -> bool {
        self.generic_lookup.is_some()
    }

    pub(crate) fn lookup_additive_part_device(&self) -> &DeviceAllocation<E> {
        &self.device_lookup_additive_part
    }

    pub(crate) fn generic_lookup(&self) -> &DeviceAllocation<E> {
        self.generic_lookup
            .as_ref()
            .expect("generic lookup runtime was released")
    }

    pub(crate) fn generic_lookup_len(&self) -> usize {
        self.generic_lookup
            .as_ref()
            .map(DeviceAllocation::len)
            .unwrap_or(0)
    }

    pub(crate) fn release_generic_lookup(&mut self) {
        self.generic_lookup = None;
    }

    pub(crate) fn into_host_keepalive(self) -> GpuGKRForwardSetupHostKeepalive<E> {
        let Self {
            tracing_ranges,
            lookup_challenges,
            callbacks,
            host_lookup_additive_part,
            host_lookup_alpha_powers,
            device_lookup_additive_part: _,
            generic_lookup: _,
        } = self;
        GpuGKRForwardSetupHostKeepalive {
            tracing_ranges,
            lookup_challenges,
            callbacks,
            host_lookup_additive_part,
            host_lookup_alpha_powers,
        }
    }
}

fn flatten_setup_columns_into_pinned_buffer(
    setup: &CpuGKRSetup<BF>,
    columns_count: usize,
    trace_len: usize,
) -> CudaResult<StaticPinnedVec<BF>> {
    let column_bytes = trace_len * core::mem::size_of::<BF>();
    let log_chunk_size = column_bytes.trailing_zeros();
    let mut raw_hypercube_evals =
        alloc_static_pinned_vec_uninit(columns_count * trace_len, log_chunk_size)?;
    for (column_idx, src_column) in setup.hypercube_evals.iter().enumerate() {
        let dst_range = column_idx * trace_len..(column_idx + 1) * trace_len;
        raw_hypercube_evals[dst_range].copy_from_slice(src_column.as_ref());
    }
    Ok(raw_hypercube_evals)
}

fn precompute_partial_tree_cache(
    raw_hypercube_evals: &StaticPinnedVec<BF>,
    log_domain_size: u32,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_tree_cap_size: u32,
    columns_count: usize,
    context: &ProverContext,
) -> CudaResult<(Vec<StaticPinnedVec<Digest>>, Vec<StaticPinnedVec<Digest>>)> {
    let mut trace_holder = TraceHolder::<BF>::new(
        log_domain_size,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        columns_count,
        TreesCacheMode::CachePartial,
        context,
    )?;
    memory_copy_async(
        trace_holder.get_uninit_hypercube_evals_mut(),
        raw_hypercube_evals.as_slice(),
        context.get_exec_stream(),
    )?;
    trace_holder.ensure_cosets_materialized(context)?;
    trace_holder.commit_all(context)?;

    let partial_trees = match &trace_holder.trees {
        TreesHolder::Partial(trees) => copy_partial_trees_to_pinned_host(trees, context)?,
        _ => unreachable!("host setup precomputation always caches partial trees"),
    };

    context.get_exec_stream().synchronize()?;
    let tree_caps = trace_holder
        .tree_caps
        .as_ref()
        .expect("setup commit must populate tree caps")
        .iter()
        .map(|src_cap| copy_host_allocation(src_cap, context))
        .collect();

    Ok((partial_trees, tree_caps))
}

fn copy_partial_trees_to_pinned_host(
    trees: &[DeviceAllocation<Digest>],
    context: &ProverContext,
) -> CudaResult<Vec<StaticPinnedVec<Digest>>> {
    let mut result = Vec::with_capacity(trees.len());
    for tree in trees.iter() {
        let mut host_tree =
            alloc_static_pinned_vec_uninit(tree.len(), SETUP_TREE_STATIC_HOST_LOG_CHUNK_SIZE)?;
        memory_copy_async(host_tree.as_mut_slice(), tree, context.get_exec_stream())?;
        result.push(host_tree);
    }
    Ok(result)
}

fn copy_host_allocation<T: Copy>(
    source: &HostAllocation<[T]>,
    _: &ProverContext,
) -> StaticPinnedVec<T> {
    alloc_static_pinned_vec_from_slice(unsafe { source.get_accessor().get() }, 10)
        .expect("static setup host copies must fit in pinned host memory")
}

#[cfg(test)]
mod tests {
    use std::alloc::Global;
    use std::ops::DerefMut;
    use std::sync::Arc;

    use cs::definitions::TIMESTAMP_COLUMNS_NUM_BITS;
    use era_cudart::memory::memory_copy;
    use field::PrimeField;
    use itertools::Itertools;
    use prover::merkle_trees::{
        ColumnMajorMerkleTreeConstructor, DefaultTreeConstructor, MerkleTreeCapVarLength,
    };
    use serial_test::serial;
    use worker::Worker;

    use super::*;
    use crate::ops::simple::set_by_ref;
    use crate::primitives::field::E4;
    use crate::prover::test_utils::make_test_context;

    fn make_test_cpu_setup(
        trace_len: usize,
        generic_lookup_width: usize,
        total_tables_size: usize,
    ) -> CpuGKRSetup<BF> {
        let total_width = 2 + generic_lookup_width;
        let mut columns = Vec::with_capacity(total_width);
        for _ in 0..total_width {
            columns.push(vec![BF::ZERO; trace_len].into_boxed_slice());
        }

        for idx in 0..trace_len.min(1usize << 16) {
            columns[0][idx] = BF::from_u32_unchecked(idx as u32);
        }
        for idx in 0..trace_len.min(1usize << TIMESTAMP_COLUMNS_NUM_BITS) {
            columns[1][idx] = BF::from_u32_unchecked(idx as u32);
        }
        for row in 0..total_tables_size {
            for column in 0..generic_lookup_width {
                columns[2 + column][row] =
                    BF::from_u32_unchecked(10 * (column as u32 + 1) + row as u32);
            }
        }

        CpuGKRSetup {
            hypercube_evals: columns.into_iter().map(Arc::new).collect(),
        }
    }

    fn flatten_setup(setup: &CpuGKRSetup<BF>) -> Vec<BF> {
        let trace_len = setup.hypercube_evals[0].len();
        let mut result = vec![BF::ZERO; setup.hypercube_evals.len() * trace_len];
        for (column_idx, column) in setup.hypercube_evals.iter().enumerate() {
            let range = column_idx * trace_len..(column_idx + 1) * trace_len;
            result[range].copy_from_slice(column.as_ref());
        }
        result
    }

    fn bitreverse_index(index: usize, num_bits: u32) -> usize {
        if num_bits == 0 {
            0
        } else {
            index.reverse_bits() >> (usize::BITS - num_bits)
        }
    }

    fn stage1_caps_from_host_allocations<S: AsRef<[Digest]>>(
        caps: &[S],
        log_lde_factor: u32,
    ) -> Vec<MerkleTreeCapVarLength> {
        (0..(1usize << log_lde_factor))
            .map(|stage1_pos| {
                let natural_coset_index = bitreverse_index(stage1_pos, log_lde_factor);
                let cap = caps[natural_coset_index].as_ref().to_vec();
                MerkleTreeCapVarLength { cap }
            })
            .collect_vec()
    }

    fn materialize_trace_holder_from_values(
        values: &[BF],
        columns_count: usize,
        trace_len: usize,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
        context: &ProverContext,
    ) -> TraceHolder<BF> {
        let mut source = context
            .alloc(values.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy(&mut source, values).unwrap();
        let mut trace_holder = TraceHolder::<BF>::new(
            trace_len.trailing_zeros(),
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            columns_count,
            TreesCacheMode::CachePartial,
            context,
        )
        .unwrap();
        trace_holder
            .materialize_and_commit_from_hypercube_evals(&source, context)
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        trace_holder
    }

    fn copy_base_poly_from_storage(
        storage: &GpuGKRStorage<BF, E4>,
        address: GKRAddress,
        context: &ProverContext,
    ) -> Vec<BF> {
        let poly = storage.get_base_layer(address);
        let mut tmp = context
            .alloc(poly.len(), AllocationPlacement::BestFit)
            .unwrap();
        set_by_ref(
            &poly.as_device_chunk(),
            tmp.deref_mut(),
            context.get_exec_stream(),
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        let mut host = vec![BF::ZERO; poly.len()];
        memory_copy(&mut host, &tmp).unwrap();
        host
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn setup_host_matches_flattened_cpu_setup_and_caps() {
        let trace_len = 1usize << 16;
        let lde_factor = 2usize;
        let tree_cap_size = 4usize;
        let log_lde_factor = lde_factor.trailing_zeros();
        let log_rows_per_leaf = 1u32;
        let log_tree_cap_size = tree_cap_size.trailing_zeros();
        let setup = make_test_cpu_setup(trace_len, 3, 64);
        let context = make_test_context(256, 64);

        let host = GpuGKRSetupHost::precompute_from_cpu_setup(
            &setup,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            &context,
        )
        .unwrap();

        assert_eq!(host.raw_hypercube_evals.as_slice(), flatten_setup(&setup));

        let worker = Worker::new();
        let twiddles: fft::Twiddles<BF, Global> = fft::Twiddles::new(trace_len, &worker);
        let setup_commitment = setup.commit(
            &twiddles,
            lde_factor,
            log_rows_per_leaf as usize,
            tree_cap_size,
            trace_len.trailing_zeros() as usize,
            &worker,
        );
        let subcap_size = tree_cap_size / lde_factor;
        let setup_caps = <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
            &setup_commitment.tree,
        )
        .cap
        .chunks_exact(subcap_size)
        .map(|chunk| MerkleTreeCapVarLength {
            cap: chunk.to_vec(),
        })
        .collect_vec();
        assert_eq!(
            stage1_caps_from_host_allocations(&host.tree_caps, log_lde_factor),
            setup_caps
        );
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn setup_transfer_reuses_single_raw_backing_and_lazy_queries_match_fresh_commit() {
        let trace_len = 1usize << 10;
        let lde_factor = 2usize;
        let tree_cap_size = 4usize;
        let log_lde_factor = lde_factor.trailing_zeros();
        let log_rows_per_leaf = 1u32;
        let log_tree_cap_size = tree_cap_size.trailing_zeros();
        let setup = make_test_cpu_setup(trace_len, 3, 32);
        let context = make_test_context(256, 64);

        let host = Arc::new(
            GpuGKRSetupHost::precompute_from_cpu_setup(
                &setup,
                log_lde_factor,
                log_rows_per_leaf,
                log_tree_cap_size,
                &context,
            )
            .unwrap(),
        );
        let mut transfer = GpuGKRSetupTransfer::new(host, &context).unwrap();
        transfer.schedule_transfer(&context).unwrap();
        context.get_h2d_stream().synchronize().unwrap();

        let mut raw = vec![BF::ZERO; transfer.trace_holder.get_hypercube_evals().len()];
        memory_copy(&mut raw, transfer.trace_holder.get_hypercube_evals()).unwrap();
        assert_eq!(raw, flatten_setup(&setup));
        assert!(!transfer.trace_holder.are_cosets_materialized());

        let mut storage = GpuGKRStorage::<BF, crate::primitives::field::E4>::default();
        transfer.bind_setup_columns_into_storage(&mut storage);
        let first_poly = storage.get_base_layer(GKRAddress::Setup(0)).clone_shared();
        for column in 0..setup.hypercube_evals.len() {
            let poly = storage.get_base_layer(GKRAddress::Setup(column));
            assert_eq!(poly.offset(), column * trace_len);
            assert_eq!(poly.len(), trace_len);
            assert!(poly.shares_backing_with(&first_poly));
        }

        let mut fresh_source = context
            .alloc(raw.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy(&mut fresh_source, &raw).unwrap();
        let mut fresh_holder = TraceHolder::<BF>::new(
            trace_len.trailing_zeros(),
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            setup.hypercube_evals.len(),
            TreesCacheMode::CachePartial,
            &context,
        )
        .unwrap();
        fresh_holder
            .materialize_and_commit_from_hypercube_evals(&fresh_source, &context)
            .unwrap();

        let query_indexes = vec![0u32, 3, 17, 31];
        let mut indexes_device = context
            .alloc(query_indexes.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy(&mut indexes_device, &query_indexes).unwrap();

        transfer.ensure_transferred(&context).unwrap();
        let transferred_queries = transfer
            .trace_holder
            .get_leafs_and_merkle_paths(1, &indexes_device, &context)
            .unwrap();
        let fresh_queries = fresh_holder
            .get_leafs_and_merkle_paths(1, &indexes_device, &context)
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        assert!(transfer.trace_holder.are_cosets_materialized());
        assert_eq!(
            unsafe { transferred_queries.leafs.get_accessor().get() },
            unsafe { fresh_queries.leafs.get_accessor().get() }
        );
        assert_eq!(
            unsafe { transferred_queries.merkle_paths.get_accessor().get() },
            unsafe { fresh_queries.merkle_paths.get_accessor().get() }
        );
        assert_eq!(
            transfer.trace_holder.get_tree_caps(),
            fresh_holder.get_tree_caps()
        );
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn bootstrap_storage_binds_setup_memory_and_witness_trace_holders() {
        let trace_len = 1usize << 10;
        let lde_factor = 2usize;
        let tree_cap_size = 4usize;
        let log_lde_factor = lde_factor.trailing_zeros();
        let log_rows_per_leaf = 1u32;
        let log_tree_cap_size = tree_cap_size.trailing_zeros();
        let setup = make_test_cpu_setup(trace_len, 2, 32);
        let context = make_test_context(256, 64);

        let host = Arc::new(
            GpuGKRSetupHost::precompute_from_cpu_setup(
                &setup,
                log_lde_factor,
                log_rows_per_leaf,
                log_tree_cap_size,
                &context,
            )
            .unwrap(),
        );
        let mut transfer = GpuGKRSetupTransfer::new(host, &context).unwrap();
        transfer.schedule_transfer(&context).unwrap();
        context.get_h2d_stream().synchronize().unwrap();

        let memory_columns = 2usize;
        let witness_columns = 3usize;
        let memory_values = (0..memory_columns * trace_len)
            .map(|i| BF::from_u32_unchecked(i as u32 + 1))
            .collect_vec();
        let witness_values = (0..witness_columns * trace_len)
            .map(|i| BF::from_u32_unchecked(i as u32 + 1000))
            .collect_vec();
        let memory_trace_holder = materialize_trace_holder_from_values(
            &memory_values,
            memory_columns,
            trace_len,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            &context,
        );
        let witness_trace_holder = materialize_trace_holder_from_values(
            &witness_values,
            witness_columns,
            trace_len,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            &context,
        );

        let storage = transfer.bootstrap_storage::<E4>(&memory_trace_holder, &witness_trace_holder);
        assert_eq!(storage.layers.len(), 1);
        assert!(storage.layers[0].extension_field_inputs.is_empty());

        for column in 0..setup.hypercube_evals.len() {
            let poly = storage.get_base_layer(GKRAddress::Setup(column));
            assert_eq!(poly.offset(), column * trace_len);
            assert_eq!(
                copy_base_poly_from_storage(&storage, GKRAddress::Setup(column), &context),
                &setup.hypercube_evals[column][..]
            );
        }
        for column in 0..memory_columns {
            let expected = &memory_values[column * trace_len..(column + 1) * trace_len];
            assert_eq!(
                copy_base_poly_from_storage(
                    &storage,
                    GKRAddress::BaseLayerMemory(column),
                    &context
                ),
                expected,
            );
        }
        for column in 0..witness_columns {
            let expected = &witness_values[column * trace_len..(column + 1) * trace_len];
            assert_eq!(
                copy_base_poly_from_storage(
                    &storage,
                    GKRAddress::BaseLayerWitness(column),
                    &context
                ),
                expected,
            );
        }
    }
}
