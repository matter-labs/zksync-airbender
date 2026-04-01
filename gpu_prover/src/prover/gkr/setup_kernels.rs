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

use super::setup::{flatten_setup_columns_into_pinned_buffer, precompute_partial_tree_cache};
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

pub(super) const GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS: usize = 10;
pub(super) const GKR_FORWARD_SETUP_THREADS_PER_BLOCK: u32 = WARP_SIZE * 4;

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

pub(super) fn bind_trace_holder_columns_into_storage<E>(
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
pub(super) struct GpuGKRForwardSetupGenericLookupDescriptor {
    pub(super) input: *const BF,
}

impl Default for GpuGKRForwardSetupGenericLookupDescriptor {
    fn default() -> Self {
        Self { input: null() }
    }
}

#[repr(C)]
pub(super) struct GpuGKRForwardSetupGenericLookupBatch<
    E,
    const MAX_COLUMNS: usize = GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS,
> {
    pub(super) column_count: u32,
    pub(super) _reserved: u32,
    pub(super) alpha_powers: *const E,
    pub(super) output: *mut E,
    pub(super) descriptors: [GpuGKRForwardSetupGenericLookupDescriptor; MAX_COLUMNS],
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

pub(super) fn pack_forward_setup_generic_lookup_batch<E>(
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

pub(super) fn lower_forward_setup_generic_lookup_batch<E>(
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
        .map(|column_idx| unsafe { raw.as_ptr().add(host.column_offset(column_idx)) })
        .collect::<Vec<_>>();
    pack_forward_setup_generic_lookup_batch(
        &setup_columns,
        alpha_powers.as_ptr(),
        generic_lookup.as_mut_ptr(),
    )
}

pub(super) fn gkr_forward_setup_generic_lookup_launch_config(
    row_count: u32,
    context: &ProverContext,
) -> CudaLaunchConfig<'_> {
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(
        GKR_FORWARD_SETUP_THREADS_PER_BLOCK,
        row_count.max(1),
    );
    CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream())
}

pub(super) fn launch_forward_setup_generic_lookup<E: GpuGKRForwardSetupGenericLookupKernelSet>(
    batch: &GpuGKRForwardSetupGenericLookupBatch<E>,
    row_count: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(row_count <= u32::MAX as usize);
    let config = gkr_forward_setup_generic_lookup_launch_config(row_count as u32, context);
    let args = GpuGKRForwardSetupGenericLookupArguments::new(*batch, row_count as u32);
    GpuGKRForwardSetupGenericLookupFunction(E::FORWARD_SETUP_GENERIC_LOOKUP).launch(&config, &args)
}
