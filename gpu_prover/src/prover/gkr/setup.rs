use std::marker::PhantomData;
use std::ptr::{null, null_mut};
use std::sync::Arc;

use cs::definitions::GKRAddress;
use cs::gkr_compiler::GKRCircuitArtifact;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::slice::CudaSlice;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use fft::materialize_powers_serial_starting_with_one;
use field::{Field, FieldExtension, PrimeField};

use super::stage1::GpuGKRStage1Output;
use super::{GpuBaseFieldPoly, GpuGKRStorage};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::Digest;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, ProverContext};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::primitives::static_host::{alloc_static_pinned_box_uninit, StaticPinnedBox};
use crate::primitives::transfer::Transfer;
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use crate::prover::trace_holder::{TraceHolder, TreesCacheMode, TreesHolder};
use cs::tables::TableType;
use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;

pub(crate) use super::setup_kernels::*;

pub(crate) struct GpuGKRSetupTransfer<'a> {
    pub(crate) host: Arc<GpuGKRSetupHost>,
    pub(crate) trace_holder: TraceHolder<BF>,
    pub(crate) transfer: Transfer<'a>,
}

impl<'a> GpuGKRSetupTransfer<'a> {
    /// Convenience accessor for the unified device cap that
    /// `schedule_transfer` H2Ds into. Used by `prove()` to D2D the cap into
    /// the initial-transcript input range.
    pub(crate) fn unified_device_cap(&self) -> &DeviceAllocation<Digest> {
        self.trace_holder.unified_device_cap()
    }
}

pub(crate) struct GpuGKRSetupTransferHostKeepalive<'a> {
    _transfer_callbacks: Callbacks<'a>,
}

impl<'a> GpuGKRSetupTransfer<'a> {
    pub(crate) fn new(host: Arc<GpuGKRSetupHost>, context: &ProverContext) -> CudaResult<Self> {
        let mut trace_holder = TraceHolder::<BF>::new_without_cosets(
            host.log_domain_size,
            host.log_lde_factor,
            host.log_rows_per_leaf,
            host.log_tree_cap_size,
            host.columns_count,
            TreesCacheMode::CachePartial,
            context,
        )?;
        // Unified device cap is allocated up front so the pre-prove H2D in
        // `schedule_transfer` has a stable destination. Length matches the
        // host-side `unified_tree_cap` that was built during precomputation.
        let cap_size = 1usize << host.log_tree_cap_size;
        let unified_cap = context.alloc::<Digest>(cap_size, AllocationPlacement::BestFit)?;
        assert!(trace_holder
            .unified_device_cap
            .replace(unified_cap)
            .is_none());
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
            &self.host.raw_hypercube_evals[..],
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
            memory_copy_async(dst_tree, &src_tree[..], stream)?;
        }
        // H2D the unified host cap directly into the device unified cap on
        // h2d_stream — gated by the same `Transfer::record_transferred` fence
        // as the polynomials and partial trees above. Replaces the legacy
        // per-coset host-pinned `tree_caps` clone callback path.
        let unified_dst = self
            .trace_holder
            .unified_device_cap
            .as_mut()
            .expect("setup transfer must have allocated the unified device cap");
        memory_copy_async(unified_dst, &self.host.unified_tree_cap[..], stream)?;
        self.transfer.record_transferred(context)
    }

    pub(crate) fn ensure_transferred(&self, context: &ProverContext) -> CudaResult<()> {
        self.transfer.ensure_transferred(context)
    }

    pub(crate) fn into_host_keepalive(self) -> GpuGKRSetupTransferHostKeepalive<'a> {
        let Self {
            host: _,
            trace_holder: _,
            transfer,
        } = self;
        // trace_holder (device alloc) and host drop here — all exec-stream ops that
        // used them have already been scheduled.
        GpuGKRSetupTransferHostKeepalive {
            _transfer_callbacks: transfer.into_callbacks(),
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
        context: &ProverContext,
    ) -> CudaResult<GpuGKRStorage<BF, E>> {
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

        Ok(storage)
    }

    pub(crate) fn bootstrap_storage_from_stage1<E>(
        &self,
        stage1: &GpuGKRStage1Output,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRStorage<BF, E>> {
        self.bootstrap_storage(
            &stage1.memory_trace_holder,
            &stage1.witness_trace_holder,
            context,
        )
    }

    pub(crate) fn schedule_forward_setup<E>(
        &self,
        compiled_circuit: &GKRCircuitArtifact<BF>,
        d_lookup_challenges: DeviceAllocation<E>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRForwardSetup<E>>
    where
        E: Field
            + FieldExtension<BF>
            + GpuGKRForwardSetupGenericLookupKernelSet
            + crate::ops::powers::GetPowersByRef
            + 'static,
    {
        self.ensure_transferred(context)?;
        schedule_forward_setup_for_shape(
            Some((&self.trace_holder, self.host.columns_count)),
            compiled_circuit.trace_len,
            compiled_circuit.generic_lookup_tables_width,
            compiled_circuit.total_tables_size,
            compiled_circuit.tables_ids_in_generic_lookups,
            d_lookup_challenges,
            context,
        )
    }
}

pub(crate) fn schedule_forward_setup_for_shape<E>(
    setup_trace_holder: Option<(&TraceHolder<BF>, usize)>,
    trace_len: usize,
    generic_lookup_width: usize,
    generic_lookup_len: usize,
    tables_ids_in_generic_lookups: bool,
    d_lookup_challenges: DeviceAllocation<E>,
    context: &ProverContext,
) -> CudaResult<GpuGKRForwardSetup<E>>
where
    E: Field
        + FieldExtension<BF>
        + GpuGKRForwardSetupGenericLookupKernelSet
        + crate::ops::powers::GetPowersByRef
        + 'static,
{
    if let Some((setup_trace_holder, setup_columns_count)) = setup_trace_holder {
        assert_eq!(
            trace_len,
            1usize << setup_trace_holder.log_domain_size,
            "forward setup trace length mismatch",
        );
        assert_eq!(
            generic_lookup_width, setup_columns_count,
            "generic lookup setup width does not match uploaded setup columns",
        );
    } else {
        assert_eq!(
            generic_lookup_width, 0,
            "setup-less forward scheduling does not support uploaded setup columns",
        );
        assert_eq!(
            generic_lookup_len, 0,
            "setup-less forward scheduling does not support generic lookup preprocessing",
        );
    }

    assert!(
        generic_lookup_len == 0
            || generic_lookup_width <= GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS,
        "generic lookup setup width {} exceeds the fused setup cap of {}",
        generic_lookup_width,
        GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS
    );
    assert!(
        d_lookup_challenges.len() >= 2,
        "lookup scheduling expects [lookup_alpha, lookup_additive_part, ...]",
    );
    let stream = context.get_exec_stream();
    let tracing_ranges = Vec::new();
    let callbacks = Callbacks::new();

    let mut device_decoder_lookup_fill_value =
        context.alloc::<E>(1, AllocationPlacement::BestFit)?;

    // We need `alpha_powers` populated in setup constant memory whenever we'll
    // launch the generic-lookup kernel. The kernel runs when either:
    //   (a) there is real generic lookup preprocessing to do (`generic_lookup_len > 0`), or
    //   (b) we still need to emit the decoder fill value inline (tables_ids_in_generic_lookups
    //       && generic_lookup_width > 0), even though there are no generic lookups to accumulate.
    let decoder_table_id_value = if tables_ids_in_generic_lookups && generic_lookup_width > 0 {
        TableType::Decoder as u32
    } else {
        0
    };
    let needs_generic_lookup_kernel = generic_lookup_len > 0 || decoder_table_id_value != 0;
    if needs_generic_lookup_kernel && generic_lookup_width > 0 {
        schedule_lookup_alpha_powers_prelude(
            d_lookup_challenges.as_ptr().cast::<E4>(),
            generic_lookup_width,
            context,
        )?;
    }
    if decoder_table_id_value == 0 {
        // No decoder fill value to compute. Zero-init the 1-E slot so it's deterministic;
        // downstream forward-cache kernels won't read from it when `decoder_mask` is null.
        unsafe {
            era_cudart::memory::memory_set_async(
                device_decoder_lookup_fill_value.transmute_mut::<u8>(),
                0,
                stream,
            )?;
        }
    }

    let mut generic_lookup = if generic_lookup_len > 0 {
        Some(context.alloc::<E>(generic_lookup_len, AllocationPlacement::BestFit)?)
    } else {
        None
    };

    if needs_generic_lookup_kernel && generic_lookup_width > 0 {
        let setup_columns: Vec<*const BF> =
            if let Some((setup_trace_holder, _)) = setup_trace_holder {
                let raw = setup_trace_holder.get_hypercube_evals();
                (0..generic_lookup_width)
                    .map(|column_idx| unsafe { raw.as_ptr().add(column_idx * trace_len) })
                    .collect()
            } else {
                // The `setup_trace_holder.is_none()` branch asserts generic_lookup_width == 0 above,
                // so we never reach here when there is no setup.
                unreachable!(
                    "generic_lookup_width > 0 requires a setup_trace_holder (asserted earlier)"
                );
            };
        let (output_ptr, output_len) = if let Some(gl) = generic_lookup.as_mut() {
            (gl.as_mut_ptr(), gl.len())
        } else {
            (null_mut(), 0)
        };
        let batch = pack_forward_setup_generic_lookup_batch(
            &setup_columns,
            output_ptr,
            device_decoder_lookup_fill_value.as_mut_ptr(),
            decoder_table_id_value,
        );
        launch_forward_setup_generic_lookup(&batch, output_len, context)?;
    }

    Ok(GpuGKRForwardSetup {
        _tracing_ranges: tracing_ranges,
        _callbacks: callbacks,
        d_lookup_challenges,
        device_decoder_lookup_fill_value,
        generic_lookup,
    })
}

pub(crate) fn bootstrap_storage_from_trace_holders<E>(
    setup_trace_holder: Option<&TraceHolder<BF>>,
    setup_columns_count: usize,
    trace_len_log2: u32,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_tree_cap_size: u32,
    memory_trace_holder: &TraceHolder<BF>,
    witness_trace_holder: &TraceHolder<BF>,
    context: &ProverContext,
) -> CudaResult<GpuGKRStorage<BF, E>> {
    for (label, trace_holder) in [
        ("memory", memory_trace_holder),
        ("witness", witness_trace_holder),
    ] {
        assert_eq!(
            trace_holder.log_domain_size, trace_len_log2,
            "{label} trace holder must match setup trace length",
        );
        assert_eq!(
            trace_holder.log_lde_factor, log_lde_factor,
            "{label} trace holder must match setup LDE factor",
        );
        assert_eq!(
            trace_holder.log_rows_per_leaf, log_rows_per_leaf,
            "{label} trace holder must match setup rows per leaf",
        );
        assert_eq!(
            trace_holder.log_tree_cap_size, log_tree_cap_size,
            "{label} trace holder must match setup tree cap size",
        );
    }
    if let Some(setup_trace_holder) = setup_trace_holder {
        assert_eq!(
            setup_trace_holder.log_domain_size, trace_len_log2,
            "setup trace holder must match trace length",
        );
        assert_eq!(
            setup_trace_holder.log_lde_factor, log_lde_factor,
            "setup trace holder must match LDE factor",
        );
        assert_eq!(
            setup_trace_holder.log_rows_per_leaf, log_rows_per_leaf,
            "setup trace holder must match rows per leaf",
        );
        assert_eq!(
            setup_trace_holder.log_tree_cap_size, log_tree_cap_size,
            "setup trace holder must match tree cap size",
        );
        assert_eq!(
            setup_trace_holder.columns_count, setup_columns_count,
            "setup trace holder columns count mismatch",
        );
    } else {
        assert_eq!(
            setup_columns_count, 0,
            "setup-less storage bootstrap expects zero uploaded setup columns",
        );
    }

    let mut storage = GpuGKRStorage::default();
    if let Some(setup_trace_holder) = setup_trace_holder {
        bind_trace_holder_columns_into_storage(setup_trace_holder, &mut storage, GKRAddress::Setup);
    }
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

    Ok(storage)
}

pub(crate) struct GpuGKRForwardSetup<E> {
    _tracing_ranges: Vec<Range>,
    _callbacks: Callbacks<'static>,
    d_lookup_challenges: DeviceAllocation<E>,
    device_decoder_lookup_fill_value: DeviceAllocation<E>,
    generic_lookup: Option<DeviceAllocation<E>>,
}

pub(crate) struct GpuGKRForwardSetupHostKeepalive<E> {
    _tracing_ranges: Vec<Range>,
    _callbacks: Callbacks<'static>,
    _marker: PhantomData<E>,
}

impl<E> GpuGKRForwardSetup<E> {
    pub(crate) fn has_generic_lookup(&self) -> bool {
        self.generic_lookup.is_some()
    }

    /// Device view over `d_lookup_challenges[1..2]` — `lookup_additive_part` lives in the
    /// second slot of the device-resident lookup challenges buffer. No standalone allocation.
    pub(crate) fn lookup_additive_part_device(&self) -> &era_cudart::slice::DeviceSlice<E> {
        &self.d_lookup_challenges[1..2]
    }

    pub(crate) fn decoder_lookup_fill_value_device(&self) -> &DeviceAllocation<E> {
        &self.device_decoder_lookup_fill_value
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
            _tracing_ranges,
            _callbacks,
            d_lookup_challenges: _,
            device_decoder_lookup_fill_value: _,
            generic_lookup: _,
        } = self;
        // d_lookup_challenges and generic_lookup (device allocs) drop here —
        // all exec-stream ops that used them have already been scheduled.
        GpuGKRForwardSetupHostKeepalive {
            _tracing_ranges,
            _callbacks,
            _marker: PhantomData,
        }
    }

    /// Variant of [`Self::into_host_keepalive`] that hands the
    /// `d_lookup_challenges` device buffer back to the caller instead of
    /// dropping it. The forward pass no longer reads it once this is called,
    /// so it can be repurposed as the lookup-and-constraint device input for
    /// `schedule_execute_backward_workflow_from_shared_state` — saves the
    /// otherwise-required separate allocation + D2D from the post-forward
    /// transcript squeeze (Opp. 3 of the pre-WHIR copy elimination plan).
    pub(crate) fn into_host_keepalive_taking_lookup_challenges(
        self,
    ) -> (GpuGKRForwardSetupHostKeepalive<E>, DeviceAllocation<E>) {
        let Self {
            _tracing_ranges,
            _callbacks,
            d_lookup_challenges,
            device_decoder_lookup_fill_value: _,
            generic_lookup: _,
        } = self;
        (
            GpuGKRForwardSetupHostKeepalive {
                _tracing_ranges,
                _callbacks,
                _marker: PhantomData,
            },
            d_lookup_challenges,
        )
    }
}

pub(super) fn flatten_setup_columns_into_pinned_buffer(
    setup: &CpuGKRSetup<BF>,
    columns_count: usize,
    trace_len: usize,
) -> CudaResult<StaticPinnedBox<BF>> {
    let mut raw_hypercube_evals = alloc_static_pinned_box_uninit(columns_count * trace_len)?;
    for (column_idx, src_column) in setup.hypercube_evals.iter().enumerate() {
        let dst_range = column_idx * trace_len..(column_idx + 1) * trace_len;
        raw_hypercube_evals[dst_range].copy_from_slice(src_column.as_ref());
    }
    Ok(raw_hypercube_evals)
}

pub(super) fn precompute_partial_tree_cache(
    raw_hypercube_evals: &StaticPinnedBox<BF>,
    log_domain_size: u32,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_tree_cap_size: u32,
    columns_count: usize,
    context: &ProverContext,
) -> CudaResult<(Vec<StaticPinnedBox<Digest>>, StaticPinnedBox<Digest>)> {
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
        &raw_hypercube_evals[..],
        context.get_exec_stream(),
    )?;
    trace_holder.ensure_cosets_materialized(context)?;
    trace_holder.commit_all(context)?;

    let partial_trees = match &trace_holder.trees {
        TreesHolder::Partial(trees) => copy_partial_trees_to_pinned_host(trees, context)?,
        _ => unreachable!("host setup precomputation always caches partial trees"),
    };

    // D2H the unified device cap directly into a pinned host buffer suitable
    // for the pre-prove H2D in `schedule_transfer`. Synchronization happens
    // here because precomputation is a one-shot scheduling-time operation,
    // not part of `prove()`'s hot path.
    let cap_size = 1usize << log_tree_cap_size;
    let mut unified_tree_cap = alloc_static_pinned_box_uninit::<Digest>(cap_size)?;
    memory_copy_async(
        &mut unified_tree_cap[..],
        trace_holder.unified_device_cap(),
        context.get_exec_stream(),
    )?;
    context.get_exec_stream().synchronize()?;

    Ok((partial_trees, unified_tree_cap))
}

fn copy_partial_trees_to_pinned_host(
    trees: &[DeviceAllocation<Digest>],
    context: &ProverContext,
) -> CudaResult<Vec<StaticPinnedBox<Digest>>> {
    let mut result = Vec::with_capacity(trees.len());
    for tree in trees.iter() {
        let mut host_tree = alloc_static_pinned_box_uninit(tree.len())?;
        memory_copy_async(&mut host_tree[..], tree, context.get_exec_stream())?;
        result.push(host_tree);
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use std::alloc::Global;
    use std::ops::DerefMut;
    use std::sync::Arc;

    use crate::primitives::context::HostAllocation;
    use cs::definitions::VirtualSetupPoly;
    use era_cudart::memory::memory_copy_async;
    use field::{FieldExtension, PrimeField};
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
        let mut columns = Vec::with_capacity(generic_lookup_width);
        for _ in 0..generic_lookup_width {
            columns.push(vec![BF::ZERO; trace_len].into_boxed_slice());
        }

        for row in 0..total_tables_size {
            for column in 0..generic_lookup_width {
                columns[column][row] =
                    BF::from_u32_unchecked(10 * (column as u32 + 1) + row as u32);
            }
        }

        CpuGKRSetup {
            hypercube_evals: columns.into_iter().map(Arc::new).collect(),
        }
    }

    fn flatten_setup(setup: &CpuGKRSetup<BF>) -> Vec<BF> {
        if setup.hypercube_evals.is_empty() {
            return Vec::new();
        }
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

    fn stage1_caps_from_unified_host_cap(
        unified_cap: &[Digest],
        log_lde_factor: u32,
    ) -> Vec<MerkleTreeCapVarLength> {
        let lde_factor = 1usize << log_lde_factor;
        debug_assert_eq!(unified_cap.len() % lde_factor, 0);
        let per_coset = unified_cap.len() / lde_factor;
        (0..lde_factor)
            .map(|stage1_pos| MerkleTreeCapVarLength {
                cap: unified_cap[stage1_pos * per_coset..(stage1_pos + 1) * per_coset].to_vec(),
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
        memory_copy_async(&mut source, values, context.get_exec_stream()).unwrap();
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
        let mut host = vec![BF::ZERO; poly.len()];
        memory_copy_async(&mut host, &tmp, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        host
    }

    fn read_ext_allocation(values: &DeviceAllocation<E4>, context: &ProverContext) -> Vec<E4> {
        let mut host = vec![E4::ZERO; values.len()];
        memory_copy_async(&mut host, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        host
    }

    fn expected_generic_lookup_preprocessing(
        setup: &CpuGKRSetup<BF>,
        generic_lookup_width: usize,
        generic_lookup_len: usize,
        lookup_alpha: E4,
    ) -> Vec<E4> {
        let powers = materialize_powers_serial_starting_with_one::<E4, Global>(
            lookup_alpha,
            generic_lookup_width,
        );
        let mut result = Vec::with_capacity(generic_lookup_len);
        for row in 0..generic_lookup_len {
            let mut value = E4::ZERO;
            for column in 0..generic_lookup_width {
                let mut contribution = powers[column];
                contribution.mul_assign_by_base(&setup.hypercube_evals[column][row]);
                value.add_assign(&contribution);
            }
            result.push(value);
        }
        result
    }

    fn launch_generic_lookup_preprocessing(
        setup: &CpuGKRSetup<BF>,
        generic_lookup_width: usize,
        generic_lookup_len: usize,
        lookup_alpha: E4,
        context: &ProverContext,
    ) -> Vec<E4> {
        let log_lde_factor = 1u32;
        let log_rows_per_leaf = 1u32;
        let log_tree_cap_size = 1u32;
        let host = Arc::new(
            GpuGKRSetupHost::precompute_from_cpu_setup(
                setup,
                log_lde_factor,
                log_rows_per_leaf,
                log_tree_cap_size,
                context,
            )
            .unwrap(),
        );
        let mut transfer = GpuGKRSetupTransfer::new(Arc::clone(&host), context).unwrap();
        transfer.schedule_transfer(context).unwrap();
        context.get_h2d_stream().synchronize().unwrap();

        let mut device_lookup_alpha = context.alloc(1, AllocationPlacement::BestFit).unwrap();
        memory_copy_async(
            &mut device_lookup_alpha,
            &[lookup_alpha],
            context.get_exec_stream(),
        )
        .unwrap();
        schedule_lookup_alpha_powers_prelude(
            device_lookup_alpha.as_ptr(),
            generic_lookup_width,
            context,
        )
        .unwrap();
        let mut generic_lookup = context
            .alloc(generic_lookup_len, AllocationPlacement::BestFit)
            .unwrap();
        let batch = lower_forward_setup_generic_lookup_batch(
            host.as_ref(),
            transfer.trace_holder.get_hypercube_evals(),
            generic_lookup_width,
            &mut generic_lookup,
        );
        launch_forward_setup_generic_lookup::<E4>(&batch, generic_lookup_len, context).unwrap();

        read_ext_allocation(&generic_lookup, context)
    }

    fn read_host_ext_allocation(values: &HostAllocation<[E4]>) -> Vec<E4> {
        unsafe { values.get_accessor().get().to_vec() }
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

        assert_eq!(&host.raw_hypercube_evals[..], flatten_setup(&setup));

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
            stage1_caps_from_unified_host_cap(&host.unified_tree_cap[..], log_lde_factor),
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
        memory_copy_async(
            &mut raw,
            transfer.trace_holder.get_hypercube_evals(),
            context.get_exec_stream(),
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();
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
        memory_copy_async(&mut fresh_source, &raw, context.get_exec_stream()).unwrap();
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
        memory_copy_async(
            &mut indexes_device,
            &query_indexes,
            context.get_exec_stream(),
        )
        .unwrap();

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
            transfer
                .trace_holder
                .read_per_coset_caps_synchronously(&context)
                .unwrap(),
            fresh_holder
                .read_per_coset_caps_synchronously(&context)
                .unwrap()
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

        let storage = transfer
            .bootstrap_storage::<E4>(&memory_trace_holder, &witness_trace_holder, &context)
            .unwrap();
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
        for address in [
            GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits),
            GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheckTimestamp),
            GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
            GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
        ] {
            assert!(
                storage.try_get_base_poly(address).is_none(),
                "virtual setup source {:?} should not be materialized in storage",
                address
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

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn bootstrap_storage_without_uploaded_setup_leaves_virtual_setup_unmaterialized() {
        let trace_len = 1usize << 19;
        let log_lde_factor = 1u32;
        let log_rows_per_leaf = 1u32;
        let log_tree_cap_size = 1u32;
        let context = make_test_context(256, 64);
        let memory_values = (0..trace_len)
            .map(|i| BF::from_u32_unchecked(i as u32 + 1))
            .collect_vec();
        let memory_trace_holder = materialize_trace_holder_from_values(
            &memory_values,
            1,
            trace_len,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            &context,
        );
        let witness_trace_holder = materialize_trace_holder_from_values(
            &[],
            0,
            trace_len,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            &context,
        );

        let storage = bootstrap_storage_from_trace_holders::<E4>(
            None,
            0,
            trace_len.trailing_zeros(),
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            &memory_trace_holder,
            &witness_trace_holder,
            &context,
        )
        .unwrap();

        for address in [
            GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits),
            GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheckTimestamp),
            GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
            GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
        ] {
            assert!(
                storage.try_get_base_poly(address).is_none(),
                "virtual setup source {:?} should not be materialized in storage",
                address
            );
        }
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn forward_setup_generic_lookup_fused_kernel_matches_expected_for_max_width() {
        let trace_len = 1usize << 10;
        let generic_lookup_width = GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS;
        let generic_lookup_len = 64;
        let setup = make_test_cpu_setup(trace_len, generic_lookup_width, generic_lookup_len);
        let context = make_test_context(256, 64);
        let lookup_alpha =
            E4::from_array_of_base([BF::new(3), BF::new(5), BF::new(7), BF::new(11)]);

        let actual = launch_generic_lookup_preprocessing(
            &setup,
            generic_lookup_width,
            generic_lookup_len,
            lookup_alpha,
            &context,
        );
        let expected = expected_generic_lookup_preprocessing(
            &setup,
            generic_lookup_width,
            generic_lookup_len,
            lookup_alpha,
        );

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn forward_setup_generic_lookup_fused_kernel_handles_single_column() {
        let trace_len = 1usize << 8;
        let generic_lookup_width = 1;
        let generic_lookup_len = 32;
        let setup = make_test_cpu_setup(trace_len, generic_lookup_width, generic_lookup_len);
        let context = make_test_context(256, 64);
        let lookup_alpha =
            E4::from_array_of_base([BF::new(13), BF::new(17), BF::new(19), BF::new(23)]);

        let actual = launch_generic_lookup_preprocessing(
            &setup,
            generic_lookup_width,
            generic_lookup_len,
            lookup_alpha,
            &context,
        );
        let expected = expected_generic_lookup_preprocessing(
            &setup,
            generic_lookup_width,
            generic_lookup_len,
            lookup_alpha,
        );

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn forward_setup_schedule_generic_lookup_matches_cpu() {
        let trace_len = 1usize << 10;
        let generic_lookup_width = 4;
        let generic_lookup_len = 32;
        let setup = make_test_cpu_setup(trace_len, generic_lookup_width, generic_lookup_len);
        let context = make_test_context(256, 64);
        let log_lde_factor = 1u32;
        let log_rows_per_leaf = 1u32;
        let log_tree_cap_size = 1u32;
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
        let mut transfer = GpuGKRSetupTransfer::new(Arc::clone(&host), &context).unwrap();
        transfer.schedule_transfer(&context).unwrap();
        context.get_h2d_stream().synchronize().unwrap();

        let lookup_alpha =
            E4::from_array_of_base([BF::new(3), BF::new(5), BF::new(7), BF::new(11)]);
        let lookup_additive_part =
            E4::from_array_of_base([BF::new(13), BF::new(17), BF::new(19), BF::new(23)]);
        let constraints_batch_challenge =
            E4::from_array_of_base([BF::new(29), BF::new(31), BF::new(37), BF::new(41)]);
        let mut d_lookup_challenges: DeviceAllocation<E4> =
            context.alloc(3, AllocationPlacement::BestFit).unwrap();
        memory_copy_async(
            &mut d_lookup_challenges,
            &[
                lookup_alpha,
                lookup_additive_part,
                constraints_batch_challenge,
            ][..],
            context.get_exec_stream(),
        )
        .unwrap();

        let scheduled = schedule_forward_setup_for_shape::<E4>(
            Some((&transfer.trace_holder, transfer.host.columns_count)),
            trace_len,
            generic_lookup_width,
            generic_lookup_len,
            false,
            d_lookup_challenges,
            &context,
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        let actual_generic_lookup = read_ext_allocation(
            scheduled
                .generic_lookup
                .as_ref()
                .expect("expected generic lookup"),
            &context,
        );
        let expected_generic_lookup = expected_generic_lookup_preprocessing(
            &setup,
            generic_lookup_width,
            generic_lookup_len,
            lookup_alpha,
        );
        assert_eq!(actual_generic_lookup, expected_generic_lookup);
    }

    #[test]
    #[should_panic(expected = "exceeding the fused setup cap")]
    fn forward_setup_generic_lookup_batch_panics_when_width_exceeds_cap() {
        let setup_columns = vec![null(); GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS + 1];
        let _ = pack_forward_setup_generic_lookup_batch::<E4>(
            &setup_columns,
            null_mut(),
            null_mut(),
            0,
        );
    }
}
