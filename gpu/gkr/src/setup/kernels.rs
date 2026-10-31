use std::ffi::c_void;
use std::ptr::{null, null_mut};

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
#[cfg(test)]
use era_cudart::slice::CudaSlice;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::{cudaGetSymbolAddress, cuda_struct_and_stub};

use super::super::{GpuBaseFieldPoly, GpuGKRStorage};
use super::{
    flatten_setup_columns_into_pinned_buffer, precompute_partial_tree_cache,
    precompute_partial_tree_cache_in_holder,
};
use crate::upstream::{BaseCommitmentGeometry, BaseOracleRole, CpuGKRSetup, Field, GKRAddress};
#[cfg(test)]
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::static_host::StaticPinnedBox;
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use gpu_hash::blake2s::Digest;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::holder::TraceHolder;

// Includes the table ID; must match descriptors.cuh.
pub(crate) const GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS: usize = 11;
pub(super) const GKR_FORWARD_SETUP_THREADS_PER_BLOCK: u32 = WARP_SIZE * 4;

cuda_struct_and_stub! {
    static ab_gkr_lookup_alpha_powers: [E4; GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS];
}

fn get_lookup_alpha_powers_device_ptr() -> *mut E4 {
    let mut ptr: *mut c_void = null_mut();
    // SAFETY: ab_gkr_lookup_alpha_powers is a valid __constant__ e4 array
    // defined in native/gkr/setup/kernels.cu.
    unsafe {
        cudaGetSymbolAddress(
            &mut ptr,
            &ab_gkr_lookup_alpha_powers as *const _ as *const c_void,
        )
    }
    .wrap()
    .expect("cudaGetSymbolAddress failed for ab_gkr_lookup_alpha_powers");
    ptr.cast()
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
    gpu_ops::powers::get_powers_by_ref::<E4>(
        alpha,
        0,
        &mut powers[..generic_lookup_width],
        context.get_exec_stream(),
    )
}

pub struct GpuGKRSetupHost {
    pub(crate) raw_hypercube_evals: StaticPinnedBox<BF>,
    pub(crate) partial_trees: Vec<StaticPinnedBox<Digest>>,
    /// Single contiguous Merkle cap of length `1 << log_tree_cap_size`, stored
    /// in canonical bit-reversed coset order so a single H2D fills the device
    /// unified cap directly.
    pub(crate) unified_tree_cap: StaticPinnedBox<Digest>,
    pub log_domain_size: u32,
    pub columns_count: usize,
    pub log_lde_factor: u32,
    pub log_rows_per_leaf: u32,
    pub log_tree_cap_size: u32,
    base_geometry: Option<BaseCommitmentGeometry>,
    pub(crate) partial_tree_reduction_layers: u32,
}

impl GpuGKRSetupHost {
    pub fn base_commitment_geometry(&self) -> Option<BaseCommitmentGeometry> {
        self.base_geometry
    }

    pub fn commitment_log_domain_size(&self) -> u32 {
        self.base_geometry.map_or(self.log_domain_size, |geometry| {
            u32::try_from(geometry.message_size_log2()).expect("message log2 exceeds u32")
        })
    }

    pub fn validate_base_geometry(setup: &CpuGKRSetup<BF>, geometry: &BaseCommitmentGeometry) {
        assert!(
            !setup.hypercube_evals.is_empty(),
            "empty setup has no setup host"
        );
        assert_eq!(
            geometry.logical_columns().setup,
            setup.hypercube_evals.len(),
            "setup geometry column mismatch"
        );
        for column in &setup.hypercube_evals {
            assert_eq!(
                column.len(),
                1usize << geometry.trace_len_log2(),
                "setup geometry trace length mismatch"
            );
        }
        TraceHolder::<BF>::validate_base_layout(
            geometry,
            gpu_trace::trace::holder::TreesCacheMode::CachePartial,
        );
    }

    /// Adapt the existing BF setup producer: pinned GKR columns stay logical,
    /// while its device trees and cap carry the producing commitment geometry.
    pub fn precompute_for_geometry(
        setup: &CpuGKRSetup<BF>,
        geometry: BaseCommitmentGeometry,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        Self::validate_base_geometry(setup, &geometry);
        gpu_trace::trace::holder::validate_baby_bear_base_geometry(
            &geometry,
            context
                .ntt_device_context()
                .whir_leaf_transform_params()
                .omega_log_order,
        );
        let columns_count = setup.hypercube_evals.len();
        let trace_len = 1usize << geometry.trace_len_log2();
        let raw_hypercube_evals =
            flatten_setup_columns_into_pinned_buffer(setup, columns_count, trace_len)?;
        let holder = TraceHolder::<BF>::new_base(
            geometry,
            BaseOracleRole::Setup,
            gpu_trace::trace::holder::TreesCacheMode::CachePartial,
            gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
            context,
        )?;
        let (partial_trees, unified_tree_cap) =
            precompute_partial_tree_cache_in_holder(&raw_hypercube_evals, holder, context)?;
        Ok(Self {
            raw_hypercube_evals,
            partial_trees,
            unified_tree_cap,
            log_domain_size: u32::try_from(geometry.trace_len_log2())
                .expect("trace log2 exceeds u32"),
            columns_count,
            log_lde_factor: geometry.lde_factor().trailing_zeros(),
            log_rows_per_leaf: geometry.values_per_leaf().trailing_zeros(),
            log_tree_cap_size: geometry.cap_size().trailing_zeros(),
            base_geometry: Some(geometry),
            partial_tree_reduction_layers:
                gpu_trace::trace::holder::resolve_partial_tree_reduction_layers(
                    gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
                    u32::try_from(geometry.message_size_log2()).expect("message log2 exceeds u32"),
                    geometry.lde_factor().trailing_zeros(),
                    geometry.values_per_leaf().trailing_zeros(),
                    geometry.cap_size().trailing_zeros(),
                ),
        })
    }

    /// Full job geometry (including mode and counts) is a divergence guard;
    /// setup bytes alone do not depend on memory/witness commitment mode.
    pub fn validate_for_geometry(&self, geometry: &BaseCommitmentGeometry) {
        assert_eq!(
            self.log_domain_size as usize,
            geometry.trace_len_log2(),
            "setup trace geometry mismatch"
        );
        assert_eq!(
            self.columns_count,
            geometry.logical_columns().setup,
            "setup column geometry mismatch"
        );
        assert_eq!(
            self.log_lde_factor,
            geometry.lde_factor().trailing_zeros(),
            "setup LDE geometry mismatch"
        );
        assert_eq!(
            self.log_rows_per_leaf,
            geometry.values_per_leaf().trailing_zeros(),
            "setup leaf geometry mismatch"
        );
        assert_eq!(
            self.log_tree_cap_size,
            geometry.cap_size().trailing_zeros(),
            "setup cap geometry mismatch"
        );
        if let Some(producing) = self.base_geometry {
            assert_eq!(producing, *geometry, "setup producing geometry mismatch");
        } else {
            assert!(
                !gpu_trace::trace::memory::uses_base_commitment_geometry(geometry),
                "legacy setup cannot supply packed, virtual or merged commitments"
            );
        }
    }

    pub fn unified_tree_cap(&self) -> &[Digest] {
        &self.unified_tree_cap
    }

    pub fn precompute_from_cpu_setup(
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
        let partial_tree_reduction_layers =
            gpu_trace::trace::holder::resolve_partial_tree_reduction_layers(
                gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
                log_domain_size,
                log_lde_factor,
                log_rows_per_leaf,
                log_tree_cap_size,
            );
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
            log_domain_size,
            columns_count,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            base_geometry: None,
            partial_tree_reduction_layers,
        })
    }

    #[cfg(test)]
    pub(crate) fn column_offset(&self, column: usize) -> usize {
        assert!(column < self.columns_count);
        column * (1usize << self.log_domain_size)
    }
}

pub(super) fn bind_trace_holder_columns_into_storage<E>(
    trace_holder: &TraceHolder<BF>,
    storage: &mut GpuGKRStorage<BF, E>,
    make_address: impl Fn(usize) -> GKRAddress,
) {
    bind_trace_holder_column_range_into_storage(
        trace_holder,
        0,
        trace_holder.columns_count,
        storage,
        make_address,
    );
}

pub(super) fn bind_trace_holder_column_range_into_storage<E>(
    trace_holder: &TraceHolder<BF>,
    first_column: usize,
    columns_count: usize,
    storage: &mut GpuGKRStorage<BF, E>,
    make_address: impl Fn(usize) -> GKRAddress,
) {
    let trace_len = 1usize << trace_holder.log_domain_size;
    assert_eq!(
        trace_holder.get_hypercube_evals().len(),
        trace_holder.columns_count * trace_len,
        "trace holder backing must be laid out as flat column-major hypercube evals",
    );
    assert!(first_column
        .checked_add(columns_count)
        .is_some_and(|end| end <= trace_holder.columns_count));
    let class_offset = first_column
        .checked_mul(trace_len)
        .expect("class backing offset overflow");
    let backing = trace_holder.raw_hypercube_backing();
    for column in 0..columns_count {
        storage.insert_base_field_at_layer(
            0,
            make_address(column),
            GpuBaseFieldPoly::from_arc(
                backing.clone(),
                class_offset + column * trace_len,
                trace_len,
            ),
        );
    }
    // Register the trace holder Arc as the consolidated per-class backing for
    // this layer-0 slot. The storage layout uses `poly_idx == column index`
    // for trace-holder-aligned slots, so the layout-driven lookup
    // `bases[class] + (poly_idx << log2_stride)` resolves to the same column
    // pointer that the per-poly views above hand out. Layout-aware consumers
    // (compact kernel encoding, `allocate_base_view`) read the trace holder
    // backing through the unified `base_class_backings` path.
    if columns_count > 0 {
        let class = crate::gkr_address_audit::classify(&make_address(0), 0);
        if storage.layers.is_empty() {
            storage
                .layers
                .resize_with(1, crate::GpuGKRLayerSource::default);
        }
        let prev = storage.layers[0].base_class_backings.insert(
            class,
            crate::ClassBacking {
                backing,
                offset: class_offset,
            },
        );
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
    pub(super) padding_value: BF,
    pub(super) output: *mut E,
    pub(super) decoder_fill_value_out: *mut E,
    pub(super) padding_fill_value_out: *mut E,
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
            padding_value: BF::ZERO,
            output: null_mut(),
            decoder_fill_value_out: null_mut(),
            padding_fill_value_out: null_mut(),
            descriptors: [GpuGKRForwardSetupGenericLookupDescriptor::default(); MAX_COLUMNS],
        }
    }
}

const _: () = {
    use std::mem::{align_of, offset_of, size_of};
    type Batch = GpuGKRForwardSetupGenericLookupBatch<E4>;
    assert!(size_of::<Batch>() == 128);
    assert!(align_of::<Batch>() == 8);
    assert!(offset_of!(Batch, decoder_table_id) == 4);
    assert!(offset_of!(Batch, padding_value) == 8);
    assert!(offset_of!(Batch, output) == 16);
    assert!(offset_of!(Batch, decoder_fill_value_out) == 24);
    assert!(offset_of!(Batch, padding_fill_value_out) == 32);
    assert!(offset_of!(Batch, descriptors) == 40);
};

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
    padding_fill_value_out: *mut E,
    decoder_table_id: u32,
    padding_value: BF,
) -> GpuGKRForwardSetupGenericLookupBatch<E> {
    assert!(
        setup_columns.len() <= GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS,
        "generic lookup setup has {} columns, exceeding the fused setup cap of {}",
        setup_columns.len(),
        GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS
    );

    let mut batch = GpuGKRForwardSetupGenericLookupBatch {
        column_count: setup_columns.len() as u32,
        decoder_table_id,
        padding_value,
        output,
        decoder_fill_value_out,
        padding_fill_value_out,
        ..Default::default()
    };
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
        null_mut(),
        0,
        BF::ZERO,
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

pub(super) fn launch_forward_setup_generic_lookup(
    batch: &GpuGKRForwardSetupGenericLookupBatch<E4>,
    row_count: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(row_count <= u32::MAX as usize);
    let config = gkr_forward_setup_generic_lookup_launch_config(row_count as u32, context);
    let args = GpuGKRForwardSetupGenericLookupArguments::new(*batch, row_count as u32);
    GpuGKRForwardSetupGenericLookupFunction(ab_gkr_forward_setup_generic_lookup_e4_kernel)
        .launch(&config, &args)
}
