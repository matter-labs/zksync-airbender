use std::ffi::c_void;
use std::ptr::{self, null, null_mut};

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::{CudaSlice, DeviceSlice, DeviceVariable};
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::cudaGetSymbolAddress;

use super::super::{GpuBaseFieldPoly, GpuGKRStorage};
use super::{flatten_setup_columns_into_pinned_buffer, precompute_partial_tree_cache};
use crate::ops::blake2s::Digest;
#[cfg(test)]
use crate::primitives::context::DeviceAllocation;
use crate::primitives::context::ProverContext;
use crate::primitives::field::{BF, E4};
use crate::primitives::static_host::StaticPinnedBox;
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use crate::prover::trace::holder::TraceHolder;
use crate::upstream::{CpuGKRSetup, GKRAddress};

pub(super) const GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS: usize = 10;
pub(super) const GKR_FORWARD_SETUP_THREADS_PER_BLOCK: u32 = WARP_SIZE * 4;

extern "C" {
    static ab_gkr_lookup_alpha_powers: [E4; GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS];
}

fn get_lookup_alpha_powers_device_ptr() -> *mut E4 {
    use std::sync::OnceLock;

    static PTR: OnceLock<usize> = OnceLock::new();
    let ptr = *PTR.get_or_init(|| {
        let mut p: *mut c_void = ptr::null_mut();
        // SAFETY: ab_gkr_lookup_alpha_powers is a valid __constant__ e4 array
        // defined in native/prover/gkr/setup/kernels.cu.
        unsafe {
            cudaGetSymbolAddress(
                &mut p,
                &ab_gkr_lookup_alpha_powers as *const _ as *const c_void,
            )
        }
        .wrap()
        .expect("cudaGetSymbolAddress failed for ab_gkr_lookup_alpha_powers");
        p as usize
    });
    ptr as *mut E4
}

pub(super) fn schedule_lookup_alpha_powers_prelude(
    lookup_alpha: *const E4,
    generic_lookup_width: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(
        generic_lookup_width <= GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS,
        "generic lookup setup width {} exceeds the fused setup cap of {}",
        generic_lookup_width,
        GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS
    );
    if generic_lookup_width == 0 {
        return Ok(());
    }

    let powers_ptr = get_lookup_alpha_powers_device_ptr();
    // SAFETY: the constant symbol storage contains exactly
    // GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS E4 elements.
    let powers = unsafe {
        DeviceSlice::from_raw_parts_mut(powers_ptr, GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS)
    };
    // SAFETY: the caller passes a device-resident alpha scalar that remains
    // valid until this stream-ordered prelude has been scheduled.
    let alpha = unsafe { DeviceVariable::from_raw_parts(lookup_alpha) };
    crate::ops::powers::get_powers_by_ref::<E4>(
        alpha,
        0,
        false,
        &mut powers[..generic_lookup_width],
        context.get_exec_stream(),
    )
}

#[allow(dead_code)]
pub(crate) struct GpuGKRSetupHost {
    pub(crate) raw_hypercube_evals: StaticPinnedBox<BF>,
    pub(crate) partial_trees: Vec<StaticPinnedBox<Digest>>,
    /// Single contiguous Merkle cap of length `1 << log_tree_cap_size`, stored
    /// in canonical bit-reversed coset order so a single H2D fills the device
    /// unified cap directly.
    pub(crate) unified_tree_cap: StaticPinnedBox<Digest>,
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
        let (partial_trees, unified_tree_cap) = precompute_partial_tree_cache(
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
            unified_tree_cap,
            trace_len,
            log_domain_size,
            columns_count,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
        })
    }

    #[cfg(test)]
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
    // Register the trace holder Arc as the consolidated per-class backing for
    // this layer-0 slot. The storage layout uses `poly_idx == column index`
    // for trace-holder-aligned slots, so the layout-driven lookup
    // `bases[class] + (poly_idx << log2_stride)` resolves to the same column
    // pointer that the per-poly views above hand out. Layout-aware consumers
    // (compact kernel encoding, `allocate_base_view`) read the trace holder
    // backing through the unified `base_class_backings` path.
    if trace_holder.columns_count > 0 {
        let class = crate::prover::gkr::gkr_address_audit::classify(&make_address(0), 0);
        if storage.layers.is_empty() {
            storage
                .layers
                .resize_with(1, crate::prover::gkr::GpuGKRLayerSource::default);
        }
        let prev = storage.layers[0].base_class_backings.insert(class, backing);
        assert!(
            prev.is_none(),
            "trace holder backing already registered for layer 0 class {class:?}"
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
pub(crate) struct GpuGKRForwardSetupGenericLookupBatch<
    E,
    const MAX_COLUMNS: usize = GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS,
> {
    pub(super) column_count: u32,
    pub(super) decoder_table_id: u32,
    pub(super) output: *mut E,
    pub(super) decoder_fill_value_out: *mut E,
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
            decoder_table_id: 0,
            output: null_mut(),
            decoder_fill_value_out: null_mut(),
            descriptors: [GpuGKRForwardSetupGenericLookupDescriptor::default(); MAX_COLUMNS],
        }
    }
}

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRForwardSetupGenericLookup<T>,
    batch: GpuGKRForwardSetupGenericLookupBatch<T>,
    row_count: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_forward_setup_generic_lookup_e4_kernel(
        batch: GpuGKRForwardSetupGenericLookupBatch<E4>,
        row_count: u32,
    )
);

pub(super) fn pack_forward_setup_generic_lookup_batch<E>(
    setup_columns: &[*const BF],
    output: *mut E,
    decoder_fill_value_out: *mut E,
    decoder_table_id: u32,
) -> GpuGKRForwardSetupGenericLookupBatch<E> {
    assert!(
        setup_columns.len() <= GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS,
        "generic lookup setup has {} columns, exceeding the fused setup cap of {}",
        setup_columns.len(),
        GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS
    );

    let mut batch = GpuGKRForwardSetupGenericLookupBatch::default();
    batch.column_count = setup_columns.len() as u32;
    batch.decoder_table_id = decoder_table_id;
    batch.output = output;
    batch.decoder_fill_value_out = decoder_fill_value_out;
    for (input, descriptor) in setup_columns.iter().zip(batch.descriptors.iter_mut()) {
        descriptor.input = *input;
    }

    batch
}

#[cfg(test)]
pub(super) fn lower_forward_setup_generic_lookup_batch<E>(
    host: &GpuGKRSetupHost,
    raw: &(impl CudaSlice<BF> + ?Sized),
    generic_lookup_width: usize,
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
        generic_lookup.as_mut_ptr(),
        null_mut(),
        0,
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

pub(super) fn launch_forward_setup_generic_lookup<E: crate::prover::gkr::GpuKernels>(
    batch: &GpuGKRForwardSetupGenericLookupBatch<E>,
    row_count: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(row_count <= u32::MAX as usize);
    let config = gkr_forward_setup_generic_lookup_launch_config(row_count as u32, context);
    let args = GpuGKRForwardSetupGenericLookupArguments::new(*batch, row_count as u32);
    GpuGKRForwardSetupGenericLookupFunction(E::FORWARD_SETUP_GENERIC_LOOKUP).launch(&config, &args)
}
