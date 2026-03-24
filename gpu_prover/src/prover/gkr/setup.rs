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
use field::Field;

use super::stage1::GpuGKRStage1Output;
use super::{GpuBaseFieldPoly, GpuGKRStorage};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::Digest;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E2, E4, E6};
use crate::primitives::static_host::{
    alloc_static_pinned_box_from_slice, alloc_static_pinned_box_uninit, StaticPinnedBox,
};
use crate::primitives::transfer::Transfer;
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use crate::prover::trace_holder::{allocate_tree_caps, TraceHolder, TreesCacheMode, TreesHolder};
use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;

const GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS: usize = 10;
const GKR_FORWARD_SETUP_THREADS_PER_BLOCK: u32 = WARP_SIZE * 4;

pub(crate) struct GpuGKRSetupHost {
    pub(crate) raw_hypercube_evals: StaticPinnedBox<BF>,
    pub(crate) partial_trees: Vec<StaticPinnedBox<Digest>>,
    pub(crate) tree_caps: Vec<StaticPinnedBox<Digest>>,
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

#[repr(C)]
#[derive(Clone, Copy, Debug)]
struct GpuGKRForwardSetupGenericLookupDescriptor {
    input: *const BF,
}

impl Default for GpuGKRForwardSetupGenericLookupDescriptor {
    fn default() -> Self {
        Self { input: null() }
    }
}

#[repr(C)]
struct GpuGKRForwardSetupGenericLookupBatch<
    E,
    const MAX_COLUMNS: usize = GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS,
> {
    column_count: u32,
    _reserved: u32,
    alpha_powers: *const E,
    output: *mut E,
    descriptors: [GpuGKRForwardSetupGenericLookupDescriptor; MAX_COLUMNS],
}

impl<E, const MAX_COLUMNS: usize> Copy for GpuGKRForwardSetupGenericLookupBatch<E, MAX_COLUMNS> {}

impl<E, const MAX_COLUMNS: usize> Clone for GpuGKRForwardSetupGenericLookupBatch<E, MAX_COLUMNS> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E, const MAX_COLUMNS: usize> Default for GpuGKRForwardSetupGenericLookupBatch<E, MAX_COLUMNS> {
    fn default() -> Self {
        Self {
            column_count: 0,
            _reserved: 0,
            alpha_powers: null(),
            output: null_mut(),
            descriptors: [GpuGKRForwardSetupGenericLookupDescriptor::default(); MAX_COLUMNS],
        }
    }
}

cuda_kernel_signature_arguments_and_function!(
    GpuGKRForwardSetupGenericLookup<T>,
    batch: GpuGKRForwardSetupGenericLookupBatch<T>,
    row_count: u32,
);

pub(crate) trait GpuGKRForwardSetupGenericLookupKernelSet: Copy + Sized {
    const FORWARD_SETUP_GENERIC_LOOKUP: GpuGKRForwardSetupGenericLookupSignature<Self>;
}

macro_rules! gkr_forward_setup_generic_lookup_kernels {
    ($type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_gkr_forward_setup_generic_lookup_ $type:lower _kernel>](
                    batch: GpuGKRForwardSetupGenericLookupBatch<$type>,
                    row_count: u32,
                )
            );

            impl GpuGKRForwardSetupGenericLookupKernelSet for $type {
                const FORWARD_SETUP_GENERIC_LOOKUP:
                    GpuGKRForwardSetupGenericLookupSignature<Self> =
                    [<ab_gkr_forward_setup_generic_lookup_ $type:lower _kernel>];
            }
        }
    };
}

gkr_forward_setup_generic_lookup_kernels!(E2);
gkr_forward_setup_generic_lookup_kernels!(E4);
gkr_forward_setup_generic_lookup_kernels!(E6);

fn pack_forward_setup_generic_lookup_batch<E>(
    setup_columns: &[*const BF],
    alpha_powers: *const E,
    output: *mut E,
) -> GpuGKRForwardSetupGenericLookupBatch<E> {
    assert!(
        setup_columns.len() <= GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS,
        "generic lookup setup has {} columns, exceeding the fused setup cap of {}",
        setup_columns.len(),
        GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS
    );

    let mut batch = GpuGKRForwardSetupGenericLookupBatch::default();
    batch.column_count = setup_columns.len() as u32;
    batch.alpha_powers = alpha_powers;
    batch.output = output;
    for (input, descriptor) in setup_columns.iter().zip(batch.descriptors.iter_mut()) {
        descriptor.input = *input;
    }

    batch
}

fn lower_forward_setup_generic_lookup_batch<E>(
    host: &GpuGKRSetupHost,
    raw: &(impl CudaSlice<BF> + ?Sized),
    generic_lookup_width: usize,
    alpha_powers: &DeviceAllocation<E>,
    generic_lookup: &mut DeviceAllocation<E>,
) -> GpuGKRForwardSetupGenericLookupBatch<E> {
    assert!(
        generic_lookup_width <= GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS,
        "generic lookup setup width {} exceeds the fused setup cap of {}",
        generic_lookup_width,
        GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS
    );
    assert!(
        generic_lookup_width > 0,
        "generic lookup setup expects at least one setup column when total_tables_size > 0",
    );

    let setup_columns = (0..generic_lookup_width)
        .map(|column_idx| unsafe { raw.as_ptr().add(host.column_offset(column_idx + 2)) })
        .collect::<Vec<_>>();
    pack_forward_setup_generic_lookup_batch(
        &setup_columns,
        alpha_powers.as_ptr(),
        generic_lookup.as_mut_ptr(),
    )
}

fn gkr_forward_setup_generic_lookup_launch_config(
    row_count: u32,
    context: &ProverContext,
) -> CudaLaunchConfig<'_> {
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(
        GKR_FORWARD_SETUP_THREADS_PER_BLOCK,
        row_count.max(1),
    );
    CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream())
}

fn launch_forward_setup_generic_lookup<E: GpuGKRForwardSetupGenericLookupKernelSet>(
    batch: &GpuGKRForwardSetupGenericLookupBatch<E>,
    row_count: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(row_count <= u32::MAX as usize);
    let config = gkr_forward_setup_generic_lookup_launch_config(row_count as u32, context);
    let args = GpuGKRForwardSetupGenericLookupArguments::new(*batch, row_count as u32);
    GpuGKRForwardSetupGenericLookupFunction(E::FORWARD_SETUP_GENERIC_LOOKUP).launch(&config, &args)
}

pub(crate) struct GpuGKRSetupTransfer<'a> {
    pub(crate) host: Arc<GpuGKRSetupHost>,
    pub(crate) trace_holder: TraceHolder<BF>,
    pub(crate) transfer: Transfer<'a>,
}

pub(crate) struct GpuGKRSetupTransferHostKeepalive<'a> {
    _transfer_callbacks: Callbacks<'a>,
}

impl<'a> GpuGKRSetupTransfer<'a> {
    fn schedule_forward_setup_for_shape<E>(
        &self,
        trace_len: usize,
        generic_lookup_width: usize,
        generic_lookup_len: usize,
        lookup_challenges: &HostAllocation<[E]>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRForwardSetup<E>>
    where
        E: Field + GpuGKRForwardSetupGenericLookupKernelSet + 'static,
    {
        self.ensure_transferred(context)?;
        assert_eq!(trace_len, self.host.trace_len);
        assert_eq!(generic_lookup_width + 2, self.host.columns_count);

        assert!(
            generic_lookup_len == 0
                || generic_lookup_width <= GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS,
            "generic lookup setup width {} exceeds the fused setup cap of {}",
            generic_lookup_width,
            GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS
        );
        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let schedule_range = Range::new("gkr.forward_setup.schedule")?;
        schedule_range.start(stream)?;
        let mut host_lookup_additive_part = unsafe { context.alloc_host_uninit_slice(1) };
        let mut device_lookup_additive_part = context.alloc(1, AllocationPlacement::BestFit)?;
        let mut host_lookup_alpha_powers = if generic_lookup_len > 0 {
            Some(unsafe { context.alloc_host_uninit_slice(self.host.columns_count - 2) })
        } else {
            None
        };
        let mut generic_lookup = if generic_lookup_len > 0 {
            Some(context.alloc::<E>(generic_lookup_len, AllocationPlacement::BestFit)?)
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
        let device_lookup_alpha_powers =
            if let Some(host_alpha_powers) = host_lookup_alpha_powers.as_ref() {
                let mut device =
                    context.alloc(host_alpha_powers.len(), AllocationPlacement::BestFit)?;
                memory_copy_async(&mut device, host_alpha_powers, context.get_exec_stream())?;
                Some(device)
            } else {
                None
            };

        if let (Some(generic_lookup), Some(device_lookup_alpha_powers)) =
            (generic_lookup.as_mut(), device_lookup_alpha_powers.as_ref())
        {
            let generic_lookup_range = Range::new("gkr.forward_setup.build_generic_lookup")?;
            generic_lookup_range.start(stream)?;
            let raw = self.trace_holder.get_hypercube_evals();
            let batch = lower_forward_setup_generic_lookup_batch(
                &self.host,
                raw,
                generic_lookup_width,
                device_lookup_alpha_powers,
                generic_lookup,
            );
            launch_forward_setup_generic_lookup(&batch, generic_lookup.len(), context)?;
            generic_lookup_range.end(stream)?;
            tracing_ranges.push(generic_lookup_range);
        }
        schedule_range.end(stream)?;
        tracing_ranges.push(schedule_range);

        Ok(GpuGKRForwardSetup {
            _tracing_ranges: tracing_ranges,
            _callbacks: callbacks,
            _host_lookup_additive_part: host_lookup_additive_part,
            _host_lookup_alpha_powers: host_lookup_alpha_powers,
            device_lookup_additive_part,
            _device_lookup_alpha_powers: device_lookup_alpha_powers,
            generic_lookup,
        })
    }

    pub(crate) fn new(host: Arc<GpuGKRSetupHost>, context: &ProverContext) -> CudaResult<Self> {
        let trace_holder = TraceHolder::<BF>::new_without_cosets(
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
        self.schedule_tree_caps_clone(context)?;
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
        lookup_challenges: &HostAllocation<[E]>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRForwardSetup<E>>
    where
        E: Field + GpuGKRForwardSetupGenericLookupKernelSet + 'static,
    {
        self.schedule_forward_setup_for_shape(
            compiled_circuit.trace_len,
            compiled_circuit.generic_lookup_tables_width,
            compiled_circuit.total_tables_size,
            lookup_challenges,
            context,
        )
    }

    fn schedule_tree_caps_clone(&mut self, context: &ProverContext) -> CudaResult<()> {
        let host = Arc::clone(&self.host);
        let mut tree_caps =
            allocate_tree_caps(host.log_lde_factor, host.log_tree_cap_size, context);
        let tree_cap_accessors = tree_caps
            .iter_mut()
            .map(HostAllocation::get_mut_accessor)
            .collect::<Vec<_>>();
        self.transfer.callbacks.schedule(
            move || unsafe {
                // SAFETY: the callback owns raw accessors into `tree_caps`, and those host
                // allocations are kept alive by the returned `trace_holder` keepalive until all
                // exec-stream users have been scheduled. Queuing the copy on exec_stream preserves
                // the contract's stream-ordered host lifetime semantics for pooled tree-cap
                // buffers.
                for (src, dst) in host.tree_caps.iter().zip(tree_cap_accessors.iter()) {
                    dst.get_mut().copy_from_slice(&src[..]);
                }
            },
            context.get_exec_stream(),
        )?;
        assert!(self.trace_holder.tree_caps.replace(tree_caps).is_none());
        Ok(())
    }
}

pub(crate) struct GpuGKRForwardSetup<E> {
    _tracing_ranges: Vec<Range>,
    _callbacks: Callbacks<'static>,
    _host_lookup_additive_part: HostAllocation<[E]>,
    _host_lookup_alpha_powers: Option<HostAllocation<[E]>>,
    device_lookup_additive_part: DeviceAllocation<E>,
    _device_lookup_alpha_powers: Option<DeviceAllocation<E>>,
    generic_lookup: Option<DeviceAllocation<E>>,
}

pub(crate) struct GpuGKRForwardSetupHostKeepalive<E> {
    _tracing_ranges: Vec<Range>,
    _callbacks: Callbacks<'static>,
    _host_lookup_additive_part: HostAllocation<[E]>,
    _host_lookup_alpha_powers: Option<HostAllocation<[E]>>,
    _marker: PhantomData<E>,
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
            _tracing_ranges,
            _callbacks,
            _host_lookup_additive_part,
            _host_lookup_alpha_powers,
            device_lookup_additive_part: _,
            _device_lookup_alpha_powers: _,
            generic_lookup: _,
        } = self;
        // device_lookup_additive_part and generic_lookup (device allocs) drop here —
        // all exec-stream ops that used them have already been scheduled.
        GpuGKRForwardSetupHostKeepalive {
            _tracing_ranges,
            _callbacks,
            _host_lookup_additive_part,
            _host_lookup_alpha_powers,
            _marker: PhantomData,
        }
    }
}

fn flatten_setup_columns_into_pinned_buffer(
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

fn precompute_partial_tree_cache(
    raw_hypercube_evals: &StaticPinnedBox<BF>,
    log_domain_size: u32,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_tree_cap_size: u32,
    columns_count: usize,
    context: &ProverContext,
) -> CudaResult<(Vec<StaticPinnedBox<Digest>>, Vec<StaticPinnedBox<Digest>>)> {
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
) -> CudaResult<Vec<StaticPinnedBox<Digest>>> {
    let mut result = Vec::with_capacity(trees.len());
    for tree in trees.iter() {
        let mut host_tree = alloc_static_pinned_box_uninit(tree.len())?;
        memory_copy_async(&mut host_tree[..], tree, context.get_exec_stream())?;
        result.push(host_tree);
    }
    Ok(result)
}

fn copy_host_allocation<T: Copy>(
    source: &HostAllocation<[T]>,
    _: &ProverContext,
) -> StaticPinnedBox<T> {
    alloc_static_pinned_box_from_slice(unsafe { source.get_accessor().get() })
        .expect("static setup host copies must fit in pinned host memory")
}

#[cfg(test)]
mod tests {
    use std::alloc::Global;
    use std::ops::DerefMut;
    use std::sync::Arc;

    use cs::definitions::TIMESTAMP_COLUMNS_NUM_BITS;
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
                contribution.mul_assign_by_base(&setup.hypercube_evals[2 + column][row]);
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

        let powers = materialize_powers_serial_starting_with_one::<E4, Global>(
            lookup_alpha,
            generic_lookup_width,
        );
        let mut device_lookup_alpha_powers = context
            .alloc(powers.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy_async(
            &mut device_lookup_alpha_powers,
            &powers,
            context.get_exec_stream(),
        )
        .unwrap();
        let mut generic_lookup = context
            .alloc(generic_lookup_len, AllocationPlacement::BestFit)
            .unwrap();
        let batch = lower_forward_setup_generic_lookup_batch(
            host.as_ref(),
            transfer.trace_holder.get_hypercube_evals(),
            generic_lookup_width,
            &device_lookup_alpha_powers,
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
    fn forward_setup_schedule_generic_lookup_matches_cpu_and_powers() {
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
        let mut lookup_challenges = unsafe { context.alloc_host_uninit_slice(3) };
        unsafe {
            lookup_challenges
                .get_mut_accessor()
                .get_mut()
                .copy_from_slice(&[
                    lookup_alpha,
                    lookup_additive_part,
                    constraints_batch_challenge,
                ]);
        }

        let scheduled = transfer
            .schedule_forward_setup_for_shape(
                trace_len,
                generic_lookup_width,
                generic_lookup_len,
                &lookup_challenges,
                &context,
            )
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        let expected_powers = materialize_powers_serial_starting_with_one::<E4, Global>(
            lookup_alpha,
            generic_lookup_width,
        );
        let actual_host_powers = read_host_ext_allocation(
            scheduled
                ._host_lookup_alpha_powers
                .as_ref()
                .expect("expected host alpha powers"),
        );
        assert_eq!(actual_host_powers, expected_powers);

        let actual_device_powers = read_ext_allocation(
            scheduled
                ._device_lookup_alpha_powers
                .as_ref()
                .expect("expected device alpha powers"),
            &context,
        );
        assert_eq!(actual_device_powers, expected_powers);

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
        let _ = pack_forward_setup_generic_lookup_batch::<E4>(&setup_columns, null(), null_mut());
    }
}
