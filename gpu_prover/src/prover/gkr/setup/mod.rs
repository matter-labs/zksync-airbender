use std::marker::PhantomData;
use std::ptr::null_mut;
use std::sync::Arc;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::CudaSlice;

use super::GpuGKRStorage;
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::Digest;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, ProverContext};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::primitives::static_host::{alloc_static_pinned_box_uninit, StaticPinnedBox};
use crate::primitives::transfer::Transfer;
use crate::prover::trace::holder::{TraceHolder, TreesCacheMode, TreesHolder};
use crate::upstream::{
    CpuGKRSetup, Field, FieldExtension, GKRAddress, GKRCircuitArtifact, TableType,
};

pub(crate) mod kernels;
pub(crate) use kernels::*;

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
        // as the polynomials and partial trees above.
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

    #[cfg(test)]
    pub(crate) fn bind_setup_columns_into_storage<E>(&self, storage: &mut GpuGKRStorage<BF, E>) {
        assert_eq!(self.trace_holder.columns_count, self.host.columns_count);
        assert_eq!(
            1usize << self.trace_holder.log_domain_size,
            self.host.trace_len
        );
        bind_trace_holder_columns_into_storage(&self.trace_holder, storage, GKRAddress::Setup);
    }

    #[cfg(test)]
    pub(crate) fn bootstrap_storage<E>(
        &self,
        memory_trace_holder: &TraceHolder<BF>,
        witness_trace_holder: &TraceHolder<BF>,
        _context: &ProverContext,
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

    pub(crate) fn schedule_forward_setup<E>(
        &self,
        compiled_circuit: &GKRCircuitArtifact<BF>,
        d_lookup_challenges: DeviceAllocation<E>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRForwardSetup<E>>
    where
        E: Field
            + FieldExtension<BF>
            + crate::prover::gkr::GpuKernels
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
        + crate::prover::gkr::GpuKernels
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
    _context: &ProverContext,
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
    #[cfg(test)]
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

    /// Hands the `d_lookup_challenges` device buffer back to the caller instead
    /// of dropping it. The forward pass no longer reads it once this is called,
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
mod tests;
