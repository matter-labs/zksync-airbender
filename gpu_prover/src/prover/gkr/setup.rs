use std::ops::DerefMut;
use std::sync::Arc;

use cs::definitions::{GKRAddress, TIMESTAMP_COLUMNS_NUM_BITS};
use cs::gkr_compiler::GKRCircuitArtifact;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::CudaSlice;
use fft::materialize_powers_serial_starting_with_one;
use field::Field;

use super::{GpuBaseFieldPoly, GpuExtensionFieldPoly, GpuGKRStorage};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::Digest;
use crate::ops::complex::{batch_inv_in_place, BatchInv};
use crate::ops::simple::{add_into_y, mul_into_y, set_by_ref, Add, BinaryOp, Mul, SetByRef};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor};
use crate::primitives::device_structures::{DeviceVectorChunk, DeviceVectorChunkMut};
use crate::primitives::field::BF;
use crate::primitives::transfer::Transfer;
use crate::prover::trace_holder::{TraceHolder, TreesCacheMode, TreesHolder};
use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;

pub(crate) struct GpuGKRSetupHost {
    pub(crate) raw_hypercube_evals: HostAllocation<[BF]>,
    pub(crate) partial_trees: Vec<HostAllocation<[Digest]>>,
    pub(crate) tree_caps: Vec<HostAllocation<[Digest]>>,
    pub(crate) trace_len: usize,
    pub(crate) log_domain_size: u32,
    pub(crate) columns_count: usize,
    pub(crate) log_lde_factor: u32,
    pub(crate) log_rows_per_leaf: u32,
    pub(crate) log_tree_cap_size: u32,
}

impl GpuGKRSetupHost {
    pub(crate) fn from_cpu_setup(
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

        let mut raw_hypercube_evals =
            unsafe { context.alloc_host_uninit_slice(columns_count * trace_len) };
        {
            let raw_hypercube_accessor = raw_hypercube_evals.get_mut_accessor();
            let dst = unsafe { raw_hypercube_accessor.get_mut() };
            for (column_idx, src_column) in setup.hypercube_evals.iter().enumerate() {
                let dst_range = column_idx * trace_len..(column_idx + 1) * trace_len;
                dst[dst_range].copy_from_slice(src_column.as_ref());
            }
        }

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
            &raw_hypercube_evals,
            context.get_exec_stream(),
        )?;
        trace_holder.ensure_cosets_materialized(context)?;
        trace_holder.commit_all(context)?;

        let partial_trees = match &trace_holder.trees {
            TreesHolder::Partial(trees) => {
                let mut result = Vec::with_capacity(trees.len());
                for tree in trees.iter() {
                    let mut host_tree = unsafe { context.alloc_host_uninit_slice(tree.len()) };
                    memory_copy_async(&mut host_tree, tree, context.get_exec_stream())?;
                    result.push(host_tree);
                }
                result
            }
            _ => unreachable!("host setup precomputation always caches partial trees"),
        };

        context.get_exec_stream().synchronize()?;

        let mut tree_caps = Vec::with_capacity(1usize << log_lde_factor);
        for src_cap in trace_holder
            .tree_caps
            .as_ref()
            .expect("setup commit must populate tree caps")
            .iter()
        {
            let mut dst_cap = unsafe { context.alloc_host_uninit_slice(src_cap.len()) };
            unsafe {
                dst_cap
                    .get_mut_accessor()
                    .get_mut()
                    .copy_from_slice(src_cap.get_accessor().get());
            }
            tree_caps.push(dst_cap);
        }

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

pub(crate) struct GpuGKRSetupTransfer<'a> {
    pub(crate) host: Arc<GpuGKRSetupHost>,
    pub(crate) trace_holder: TraceHolder<BF>,
    pub(crate) transfer: Transfer<'a>,
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
            &self.host.raw_hypercube_evals,
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
            memory_copy_async(dst_tree, src_tree, stream)?;
        }
        self.trace_holder
            .clone_tree_caps_from_host(&self.host.tree_caps, context);
        self.transfer.record_transferred(context)
    }

    pub(crate) fn ensure_transferred(&self, context: &ProverContext) -> CudaResult<()> {
        self.transfer.ensure_transferred(context)
    }

    pub(crate) fn bind_setup_columns_into_storage<E>(&self, storage: &mut GpuGKRStorage<BF, E>) {
        let backing = self.trace_holder.raw_hypercube_backing();
        for column in 0..self.host.columns_count {
            storage.insert_base_field_at_layer(
                0,
                GKRAddress::Setup(column),
                GpuBaseFieldPoly::from_arc(
                    backing.clone(),
                    self.host.column_offset(column),
                    self.host.trace_len,
                ),
            );
        }
    }

    pub(crate) fn prepare_lookup_precomputations<E>(
        &self,
        compiled_circuit: &GKRCircuitArtifact<BF>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRLookupPrecomputations<E>>
    where
        E: Field,
    {
        assert_eq!(compiled_circuit.trace_len, self.host.trace_len);
        assert_eq!(
            compiled_circuit.generic_lookup_tables_width + 2,
            self.host.columns_count
        );
        let generic_lookup_len = compiled_circuit.total_tables_size;
        let host_lookup_gamma = unsafe { context.alloc_host_uninit_slice(1) };
        let device_lookup_gamma = context.alloc(1, AllocationPlacement::BestFit)?;
        let host_lookup_alpha_powers = if self.host.columns_count > 3 {
            Some(unsafe { context.alloc_host_uninit_slice(self.host.columns_count - 2) })
        } else {
            None
        };
        let device_lookup_alpha_powers =
            if let Some(host_powers) = host_lookup_alpha_powers.as_ref() {
                Some(context.alloc(host_powers.len(), AllocationPlacement::BestFit)?)
            } else {
                None
            };
        let weighted_column = if self.host.columns_count > 3 && generic_lookup_len > 0 {
            Some(context.alloc(generic_lookup_len, AllocationPlacement::BestFit)?)
        } else {
            None
        };

        Ok(GpuGKRLookupPrecomputations {
            host_lookup_gamma,
            device_lookup_gamma,
            host_lookup_alpha_powers,
            device_lookup_alpha_powers,
            range_check_16: context.alloc(1usize << 16, AllocationPlacement::BestFit)?,
            timestamp_range_check: context.alloc(
                1usize << TIMESTAMP_COLUMNS_NUM_BITS,
                AllocationPlacement::BestFit,
            )?,
            generic_lookup: context.alloc(generic_lookup_len, AllocationPlacement::BestFit)?,
            weighted_column,
            vectorized_lookup_setup_poly: Arc::new(
                context.alloc(compiled_circuit.trace_len, AllocationPlacement::BestFit)?,
            ),
            total_setup_columns: self.host.columns_count,
        })
    }

    pub(crate) fn schedule_lookup_precomputations<'b, E>(
        &self,
        lookup_precomputations: &mut GpuGKRLookupPrecomputations<E>,
        lookup_challenges: UnsafeAccessor<[E]>,
        callbacks: &mut Callbacks<'b>,
        context: &ProverContext,
    ) -> CudaResult<()>
    where
        E: Field + SetByRef + BatchInv + 'b,
        Add: BinaryOp<E, E, E>,
        Add: BinaryOp<BF, E, E>,
        Mul: BinaryOp<BF, E, E>,
    {
        self.ensure_transferred(context)?;

        let lookup_gamma_accessor = lookup_precomputations.host_lookup_gamma.get_mut_accessor();
        let alpha_powers_accessor = lookup_precomputations
            .host_lookup_alpha_powers
            .as_mut()
            .map(|allocation| allocation.get_mut_accessor());
        let alpha_powers_len = lookup_precomputations
            .host_lookup_alpha_powers
            .as_ref()
            .map(|allocation| allocation.len())
            .unwrap_or(0);
        callbacks.schedule(
            move || unsafe {
                let lookup_challenges = lookup_challenges.get();
                assert!(
                    lookup_challenges.len() >= 2,
                    "lookup scheduling expects [lookup_alpha, lookup_gamma, ...]",
                );
                let lookup_alpha = lookup_challenges[0];
                let lookup_gamma = lookup_challenges[1];
                lookup_gamma_accessor.get_mut()[0] = lookup_gamma;
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
            &mut lookup_precomputations.device_lookup_gamma,
            &lookup_precomputations.host_lookup_gamma,
            context.get_exec_stream(),
        )?;
        if let (Some(device_alpha_powers), Some(host_alpha_powers)) = (
            lookup_precomputations.device_lookup_alpha_powers.as_mut(),
            lookup_precomputations.host_lookup_alpha_powers.as_ref(),
        ) {
            memory_copy_async(
                device_alpha_powers,
                host_alpha_powers,
                context.get_exec_stream(),
            )?;
        }

        let raw = self.trace_holder.get_hypercube_evals();
        let stream = context.get_exec_stream();
        let lookup_gamma =
            DeviceVectorChunk::new(&lookup_precomputations.device_lookup_gamma, 0, 1);

        set_by_ref(
            &lookup_gamma,
            lookup_precomputations.range_check_16.deref_mut(),
            stream,
        )?;
        let range_source = DeviceVectorChunk::new(raw, self.host.column_offset(0), 1usize << 16);
        add_into_y(
            &range_source,
            lookup_precomputations.range_check_16.deref_mut(),
            stream,
        )?;
        batch_inv_in_place(&mut lookup_precomputations.range_check_16, stream)?;

        set_by_ref(
            &lookup_gamma,
            lookup_precomputations.timestamp_range_check.deref_mut(),
            stream,
        )?;
        let timestamp_source = DeviceVectorChunk::new(
            raw,
            self.host.column_offset(1),
            1usize << TIMESTAMP_COLUMNS_NUM_BITS,
        );
        add_into_y(
            &timestamp_source,
            lookup_precomputations.timestamp_range_check.deref_mut(),
            stream,
        )?;
        batch_inv_in_place(&mut lookup_precomputations.timestamp_range_check, stream)?;

        if lookup_precomputations.generic_lookup.len() > 0 {
            set_by_ref(
                &lookup_gamma,
                lookup_precomputations.generic_lookup.deref_mut(),
                stream,
            )?;
            let base_column = DeviceVectorChunk::new(
                raw,
                self.host.column_offset(2),
                lookup_precomputations.generic_lookup.len(),
            );
            add_into_y(
                &base_column,
                lookup_precomputations.generic_lookup.deref_mut(),
                stream,
            )?;

            if let (Some(weighted_column), Some(alpha_powers)) = (
                lookup_precomputations.weighted_column.as_mut(),
                lookup_precomputations.device_lookup_alpha_powers.as_ref(),
            ) {
                for setup_column in 3..lookup_precomputations.total_setup_columns {
                    let source = DeviceVectorChunk::new(
                        raw,
                        self.host.column_offset(setup_column),
                        lookup_precomputations.generic_lookup.len(),
                    );
                    let challenge_power = DeviceVectorChunk::new(alpha_powers, setup_column - 2, 1);
                    set_by_ref(&challenge_power, weighted_column.deref_mut(), stream)?;
                    mul_into_y(&source, weighted_column.deref_mut(), stream)?;
                    let weighted_column_chunk =
                        DeviceVectorChunk::new(&*weighted_column, 0, weighted_column.len());
                    add_into_y(
                        &weighted_column_chunk,
                        lookup_precomputations.generic_lookup.deref_mut(),
                        stream,
                    )?;
                }
            }
            batch_inv_in_place(&mut lookup_precomputations.generic_lookup, stream)?;
        }

        set_by_ref(
            &lookup_gamma,
            Arc::get_mut(&mut lookup_precomputations.vectorized_lookup_setup_poly)
                .expect("vectorized lookup setup poly must not be shared while scheduling")
                .deref_mut(),
            stream,
        )?;
        if lookup_precomputations.generic_lookup.len() > 0 {
            let src = DeviceVectorChunk::new(
                &lookup_precomputations.generic_lookup,
                0,
                lookup_precomputations.generic_lookup.len(),
            );
            let mut dst = DeviceVectorChunkMut::new(
                Arc::get_mut(&mut lookup_precomputations.vectorized_lookup_setup_poly)
                    .expect("vectorized lookup setup poly must not be shared while scheduling"),
                0,
                lookup_precomputations.generic_lookup.len(),
            );
            set_by_ref(&src, &mut dst, stream)?;
        }

        Ok(())
    }
}

pub(crate) struct GpuGKRLookupPrecomputations<E> {
    host_lookup_gamma: HostAllocation<[E]>,
    device_lookup_gamma: DeviceAllocation<E>,
    host_lookup_alpha_powers: Option<HostAllocation<[E]>>,
    device_lookup_alpha_powers: Option<DeviceAllocation<E>>,
    pub(crate) range_check_16: DeviceAllocation<E>,
    pub(crate) timestamp_range_check: DeviceAllocation<E>,
    pub(crate) generic_lookup: DeviceAllocation<E>,
    weighted_column: Option<DeviceAllocation<E>>,
    vectorized_lookup_setup_poly: Arc<DeviceAllocation<E>>,
    total_setup_columns: usize,
}

impl<E> GpuGKRLookupPrecomputations<E> {
    pub(crate) fn vectorized_lookup_setup_poly(&self) -> GpuExtensionFieldPoly<E>
    where
        E: Copy,
    {
        GpuExtensionFieldPoly::from_arc(
            Arc::clone(&self.vectorized_lookup_setup_poly),
            0,
            self.vectorized_lookup_setup_poly.len(),
        )
    }
}

#[cfg(test)]
mod tests {
    use std::alloc::Global;
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
    use crate::primitives::context::ProverContextConfig;

    fn make_context() -> ProverContext {
        let mut config = ProverContextConfig::default();
        config.max_device_allocation_blocks_count = Some(256);
        config.host_allocator_blocks_count = 64;
        ProverContext::new(&config).unwrap()
    }

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

    fn stage1_caps_from_host_allocations(
        caps: &[HostAllocation<[Digest]>],
        log_lde_factor: u32,
    ) -> Vec<MerkleTreeCapVarLength> {
        (0..(1usize << log_lde_factor))
            .map(|stage1_pos| {
                let natural_coset_index = bitreverse_index(stage1_pos, log_lde_factor);
                let cap = unsafe { caps[natural_coset_index].get_accessor().get().to_vec() };
                MerkleTreeCapVarLength { cap }
            })
            .collect_vec()
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
        let context = make_context();

        let host = GpuGKRSetupHost::from_cpu_setup(
            &setup,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            &context,
        )
        .unwrap();

        assert_eq!(
            unsafe { host.raw_hypercube_evals.get_accessor().get() },
            flatten_setup(&setup)
        );

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
        let context = make_context();

        let host = Arc::new(
            GpuGKRSetupHost::from_cpu_setup(
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
}
