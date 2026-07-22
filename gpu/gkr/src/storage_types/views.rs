use std::collections::BTreeMap;
use std::ptr::null;
use std::sync::Arc;

use crate::gkr_address_audit::AddressClass;
use crate::storage_layout::GpuGKRStorageLayout;
use crate::upstream::{Field, GKRAddress};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::{DeviceAllocation, HostAllocation};
use gpu_core::primitives::device_structures::{DeviceVectorChunk, DeviceVectorChunkMut};
use gpu_prover_context::ProverContext;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, DeviceSlice};

use super::ffi_descriptors::{
    GpuBaseFieldPolySource, GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor,
    GpuBaseFieldPolySourceAfterOneFoldingPlan, GpuBaseFieldPolySourceAfterTwoFoldingsPlan,
    GpuBaseFieldSourceKind, GpuExtensionFieldPolyContinuingLaunchDescriptor,
    GpuExtensionFieldPolyContinuingSourcePlan, GpuExtensionFieldPolyInitialSource,
};

#[doc(hidden)]
pub struct GpuGKRLayerSource<B, E> {
    pub base_field_inputs: BTreeMap<GKRAddress, GpuBaseFieldPoly<B>>,
    pub extension_field_inputs: BTreeMap<GKRAddress, GpuExtensionFieldPoly<E>>,
    pub(crate) intermediate_storage_for_folder_base_field_inputs:
        BTreeMap<GKRAddress, (usize, GpuBaseFieldPolyIntermediateFoldingStorage<E>)>,
    pub(crate) intermediate_storage_for_folder_extension_field_inputs:
        BTreeMap<GKRAddress, (usize, GpuExtensionFieldPolyIntermediateFoldingStorage<E>)>,
    /// Consolidated per-`AddressClass` backings for base-field polys living at
    /// this layer. Lazily allocated by `GpuGKRStorage::allocate_base_view`
    /// when a layout is set; size is taken from the layout's per-slot poly
    /// count. Empty when no consolidated allocations have been requested for
    /// this layer.
    pub(crate) base_class_backings: BTreeMap<AddressClass, Arc<DeviceAllocation<B>>>,
    pub(crate) ext_class_backings: BTreeMap<AddressClass, Arc<DeviceAllocation<E>>>,
    /// Per-layer consolidated backing for ext-field intermediate folding
    /// buffers used by dim-reducing rounds 1+. Pre-allocated by
    /// `GpuGKRStorage::register_dim_reducing_inputs_for_layer` from the
    /// blueprint input set; subsequent `plan_ext_source_for_rounds_1_and_beyond`
    /// calls slice views from this allocation instead of allocating per-poly.
    pub(crate) intermediate_folding_consolidated: Option<ConsolidatedFoldingBacking<E>>,
    /// Per-layer consolidated backing for base-field intermediate folding
    /// buffers used by main-layer flat-path rounds 1+. Pre-allocated by
    /// `GpuGKRStorage::register_flat_base_folding_for_layer` from the
    /// main-layer blueprint base-input set; subsequent
    /// `plan_base_source_for_round_1` / `_round_2` /
    /// `_for_rounds_3_and_beyond` calls slice views into this allocation
    /// instead of allocating per-poly. Polys whose address is not present in
    /// the storage layout (currently `VirtualSetup`) take a lazy per-poly path.
    pub(crate) intermediate_base_folding_consolidated: Option<ConsolidatedBaseFoldingBacking<E>>,
}

/// Pre-allocated per-(layer, AddressClass) backings for ext-field intermediate
/// folding storage. Set up by
/// `GpuGKRStorage::register_dim_reducing_inputs_for_layer` and consumed by the
/// step==1 branch of `plan_ext_source_for_rounds_1_and_beyond`.
///
/// Per-class shape keeps the cache pointer table compact, while `poly_index`
/// assigns dense layer-local cache indices independent of the source poly_idx
/// used for reads. This is what lets copy aliases read canonical storage
/// without materializing into an alias-local source slot.
pub(crate) struct ConsolidatedFoldingBacking<E> {
    /// `AddressClass -> Arc<DeviceAllocation<E>>`. One Arc per class that has
    /// dim-reducing input polys at this layer.
    pub(crate) per_class: BTreeMap<AddressClass, Arc<DeviceAllocation<E>>>,
    /// Dense layer-local cache poly index per dim-reducing input address.
    pub(crate) poly_index: BTreeMap<GKRAddress, u16>,
    /// Per-poly buffer size = `2 * size_after_one_fold = poly_size`. Uniform
    /// across all polys at a layer (all dim-reducing inputs at one layer share
    /// the same `trace_len`).
    pub(crate) per_poly_size: usize,
}

/// Pre-allocated per-(layer, AddressClass) backings for base-field
/// intermediate folding storage on the main-layer flat path. Set up by
/// `GpuGKRStorage::register_flat_base_folding_for_layer` and consumed by
/// `plan_base_source_for_round_1` / `_round_2` / `_for_rounds_3_and_beyond`.
///
/// Real base polys use dense layer-local cache indices in `real_index`, while
/// virtual polys use `virtual_index`. Each backing is sized by the number of
/// source addresses that actually need a cache slot for the current layer.
///
/// `per_poly_size = base_poly_size / 2` (matches the per-poly
/// `GpuBaseFieldPolyIntermediateFoldingStorage::new_for_base_poly_size`
/// allocation: `2 * size_after_two_folds = base_poly_size / 2`).
pub(crate) struct ConsolidatedBaseFoldingBacking<E> {
    /// `AddressClass -> Arc<DeviceAllocation<E>>`. One Arc per class that has
    /// real base-field input polys at this layer (excludes `VirtualSetup`).
    pub(crate) per_class: BTreeMap<AddressClass, Arc<DeviceAllocation<E>>>,
    /// Dense layer-local cache poly index per real base-field input address.
    pub(crate) real_index: BTreeMap<GKRAddress, u16>,
    /// `AddressClass -> Arc<DeviceAllocation<E>>` for `VirtualSetup` polys at
    /// this layer. Virtuals don't have a layout slot — their per-poly buffer
    /// shape is the same as real base polys, but they need their own Arc
    /// because the layout's per-class poly-idx assignment skips them. Each
    /// virtual poly's index in `virtual_per_class[class]` is given by
    /// `virtual_index[poly]`.
    pub(crate) virtual_per_class: BTreeMap<AddressClass, Arc<DeviceAllocation<E>>>,
    /// `GKRAddress -> poly_idx within virtual_per_class[address's class]`.
    /// Set by `register_flat_base_folding_for_layer` per layer.
    pub(crate) virtual_index: BTreeMap<GKRAddress, u16>,
    /// Per-poly buffer size in E-elements = `base_poly_size / 2` =
    /// `2 * size_after_two_folds`. Uniform across all polys at this layer.
    pub(crate) per_poly_size: usize,
}

#[doc(hidden)]
pub struct GpuGKRStorage<B, E> {
    pub layers: Vec<GpuGKRLayerSource<B, E>>,
    /// Pre-computed storage layout from `GKRCircuitArtifact`. When set,
    /// `allocate_base_view` / `allocate_ext_view` route through the per-class
    /// consolidated backings; when `None`, callers must use the per-poly
    /// allocation path directly (test-only).
    pub(crate) layout: Option<Arc<GpuGKRStorageLayout>>,
}

impl<B, E> Default for GpuGKRLayerSource<B, E> {
    fn default() -> Self {
        Self {
            base_field_inputs: BTreeMap::new(),
            extension_field_inputs: BTreeMap::new(),
            intermediate_storage_for_folder_base_field_inputs: BTreeMap::new(),
            intermediate_storage_for_folder_extension_field_inputs: BTreeMap::new(),
            base_class_backings: BTreeMap::new(),
            ext_class_backings: BTreeMap::new(),
            intermediate_folding_consolidated: None,
            intermediate_base_folding_consolidated: None,
        }
    }
}

impl<B, E> Default for GpuGKRStorage<B, E> {
    fn default() -> Self {
        Self {
            layers: Vec::new(),
            layout: None,
        }
    }
}

#[doc(hidden)]
pub struct GpuBaseFieldPoly<B> {
    pub(crate) backing: Arc<DeviceAllocation<B>>,
    pub(crate) offset: usize,
    pub(crate) len: usize,
}

impl<B> Clone for GpuBaseFieldPoly<B> {
    fn clone(&self) -> Self {
        Self {
            backing: Arc::clone(&self.backing),
            offset: self.offset,
            len: self.len,
        }
    }
}

impl<B> GpuBaseFieldPoly<B> {
    pub(crate) fn from_arc(backing: Arc<DeviceAllocation<B>>, offset: usize, len: usize) -> Self {
        assert!(len.is_power_of_two(), "poly length must be a power of two");
        assert!(len > 0, "poly length must be non-zero");
        assert!(
            offset + len <= backing.len(),
            "view [{offset}, {}) is out of bounds for backing of len {}",
            offset + len,
            backing.len()
        );

        Self {
            backing,
            offset,
            len,
        }
    }

    pub(crate) fn clone_shared(&self) -> Self {
        self.clone()
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn as_ptr(&self) -> *const B {
        unsafe { self.backing.as_ptr().add(self.offset) }
    }

    /// Mutable raw pointer to the view's range. Caller must ensure exclusive
    /// write access (no concurrent writes from other clones of this view).
    /// Used by forward kernel descriptors that write into the consolidated
    /// per-class backing through this view's slot.
    pub(crate) fn as_mut_ptr(&self) -> *mut B {
        unsafe { self.backing.as_ptr().add(self.offset) as *mut B }
    }

    pub fn as_device_chunk(&self) -> DeviceVectorChunk<'_, B> {
        DeviceVectorChunk::new(self.backing.as_ref(), self.offset, self.len)
    }

    /// Forge a `DeviceVectorChunkMut` covering this view's range, so the view
    /// can be passed as the `&mut` destination of a stream-ordered op.
    /// SAFETY: same contract as `as_mut_ptr` — caller must ensure exclusive
    /// write access (no concurrent writes from other clones of this view) for
    /// the duration of every op scheduled against the returned chunk.
    pub(crate) unsafe fn as_mut_chunk_unchecked(&self) -> DeviceVectorChunkMut<'_, B> {
        let slice = DeviceSlice::from_raw_parts_mut(self.as_mut_ptr(), self.len);
        DeviceVectorChunkMut::new(slice, 0, self.len)
    }

    pub(crate) fn accessor(&self) -> GpuBaseFieldPolySource<B> {
        GpuBaseFieldPolySource {
            start: self.as_ptr(),
            next_layer_size: self.len / 2,
            source_kind: GpuBaseFieldSourceKind::Real,
        }
    }
}

#[doc(hidden)]
pub struct GpuExtensionFieldPoly<E> {
    pub(crate) backing: Arc<DeviceAllocation<E>>,
    pub(crate) offset: usize,
    pub(crate) len: usize,
}

impl<E> Clone for GpuExtensionFieldPoly<E> {
    fn clone(&self) -> Self {
        Self {
            backing: Arc::clone(&self.backing),
            offset: self.offset,
            len: self.len,
        }
    }
}

impl<E> GpuExtensionFieldPoly<E> {
    pub(crate) fn from_arc(backing: Arc<DeviceAllocation<E>>, offset: usize, len: usize) -> Self {
        assert!(len.is_power_of_two(), "poly length must be a power of two");
        assert!(len > 0, "poly length must be non-zero");
        assert!(
            offset + len <= backing.len(),
            "view [{offset}, {}) is out of bounds for backing of len {}",
            offset + len,
            backing.len()
        );

        Self {
            backing,
            offset,
            len,
        }
    }

    pub(crate) fn clone_shared(&self) -> Self {
        self.clone()
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn as_ptr(&self) -> *const E {
        unsafe { self.backing.as_ptr().add(self.offset) }
    }

    /// Mutable raw pointer to the view's range. Caller must ensure exclusive
    /// write access (no concurrent writes from other clones of this view).
    pub(crate) fn as_mut_ptr(&self) -> *mut E {
        unsafe { self.backing.as_ptr().add(self.offset) as *mut E }
    }

    /// Forge a `DeviceVectorChunkMut` covering this view's range, so the view
    /// can be passed as the `&mut` destination of a stream-ordered op.
    /// SAFETY: same contract as `as_mut_ptr` — caller must ensure exclusive
    /// write access (no concurrent writes from other clones of this view) for
    /// the duration of every op scheduled against the returned chunk.
    pub(crate) unsafe fn as_mut_chunk_unchecked(&self) -> DeviceVectorChunkMut<'_, E> {
        let slice = DeviceSlice::from_raw_parts_mut(self.as_mut_ptr(), self.len);
        DeviceVectorChunkMut::new(slice, 0, self.len)
    }

    pub(crate) fn as_device_slice(&self) -> &DeviceSlice<E> {
        &self.backing[self.offset..self.offset + self.len]
    }

    pub(crate) fn accessor(&self) -> GpuExtensionFieldPolyInitialSource<E> {
        GpuExtensionFieldPolyInitialSource {
            start: self.as_ptr(),
            next_layer_size: self.len / 2,
        }
    }
}

/// Per-poly intermediate folding state for base-field flat-path inputs.
///
/// Always holds an `Arc<DeviceAllocation<E>>` backing slice (the cache
/// data is in E because folding mixes the base-field input with the
/// extension-field challenge). `new_for_base_poly_size` allocates a
/// fresh per-poly Arc; `from_arc` slices a view into a per-layer
/// consolidated allocation. Both forms expose the same buffer-pointer
/// semantics; the `offset_in_backing` field shifts the buffer's effective
/// start within `backing`.
pub(crate) struct GpuBaseFieldPolyIntermediateFoldingStorage<E> {
    pub(crate) backing: Arc<DeviceAllocation<E>>,
    pub(crate) offset_in_backing: usize,
    pub(crate) size_after_two_folds: usize,
}

impl<E> GpuBaseFieldPolyIntermediateFoldingStorage<E> {
    pub(crate) fn new_for_base_poly_size(
        base_poly_size: usize,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        assert!(base_poly_size.is_power_of_two());
        assert!(base_poly_size > 4);

        let size_after_two_folds = base_poly_size / 4;
        let buffer_size = size_after_two_folds * 2;
        let backing = Arc::new(context.alloc::<E>(buffer_size, AllocationPlacement::Top)?);

        Ok(Self {
            backing,
            offset_in_backing: 0,
            size_after_two_folds,
        })
    }

    /// View into a pre-allocated consolidated layer backing. The caller is
    /// responsible for ensuring the
    /// `[offset_in_backing, offset_in_backing + 2 * size_after_two_folds)` range
    /// is exclusively assigned to this poly.
    pub(crate) fn from_arc(
        backing: Arc<DeviceAllocation<E>>,
        offset_in_backing: usize,
        base_poly_size: usize,
    ) -> Self {
        assert!(base_poly_size.is_power_of_two());
        assert!(base_poly_size > 4);
        let size_after_two_folds = base_poly_size / 4;
        assert!(offset_in_backing + 2 * size_after_two_folds <= backing.len());
        Self {
            backing,
            offset_in_backing,
            size_after_two_folds,
        }
    }

    fn buffer_start_mut(&self) -> *mut E {
        // SAFETY: `offset_in_backing` is bounded by `backing.len()` (asserted in
        // every constructor). Cast-to-mut mirrors the pattern used by
        // `GpuExtensionFieldPolyIntermediateFoldingStorage::buffer_start_mut`.
        unsafe { self.backing.as_ptr().cast_mut().add(self.offset_in_backing) }
    }

    pub(crate) fn initial_pointer(&mut self) -> *mut E {
        self.buffer_start_mut()
    }

    pub(crate) fn pointers_for_sumcheck_accessor_step(&mut self, step: usize) -> (*mut E, *mut E) {
        unsafe {
            assert!(step > 2);
            let mut input_offset = self.buffer_start_mut();
            let mut input_size = self.size_after_two_folds;
            let mut next_step_offset = input_offset.add(input_size);
            for _ in 3..step {
                input_offset = next_step_offset;
                input_size /= 2;
                next_step_offset = next_step_offset.add(input_size);
            }

            (input_offset, next_step_offset)
        }
    }
}

/// Per-poly intermediate folding state for ext-field dim-reducing inputs.
///
/// Always holds an `Arc<DeviceAllocation<E>>` backing slice.
/// `new_for_extension_poly_size` allocates a fresh per-poly allocation;
/// `from_arc` slices a view into a per-layer consolidated allocation.
/// Both forms expose the same buffer-pointer semantics; the
/// `offset_in_backing` field shifts the buffer's effective start within
/// `backing`.
pub(crate) struct GpuExtensionFieldPolyIntermediateFoldingStorage<E> {
    pub(crate) backing: Arc<DeviceAllocation<E>>,
    pub(crate) offset_in_backing: usize,
    pub(crate) size_after_one_fold: usize,
}

impl<E> GpuExtensionFieldPolyIntermediateFoldingStorage<E> {
    pub(crate) fn new_for_extension_poly_size(
        poly_size: usize,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        assert!(poly_size.is_power_of_two());
        assert!(poly_size > 2);

        let size_after_one_fold = poly_size / 2;
        let buffer_size = size_after_one_fold * 2;
        let backing = Arc::new(context.alloc::<E>(buffer_size, AllocationPlacement::Top)?);

        Ok(Self {
            backing,
            offset_in_backing: 0,
            size_after_one_fold,
        })
    }

    /// View into a pre-allocated consolidated layer backing. The caller is
    /// responsible for ensuring the `[offset_in_backing, offset_in_backing + 2 * size_after_one_fold)`
    /// range is exclusively assigned to this poly.
    pub(crate) fn from_arc(
        backing: Arc<DeviceAllocation<E>>,
        offset_in_backing: usize,
        poly_size: usize,
    ) -> Self {
        assert!(poly_size.is_power_of_two());
        assert!(poly_size > 2);
        let size_after_one_fold = poly_size / 2;
        assert!(offset_in_backing + 2 * size_after_one_fold <= backing.len());
        Self {
            backing,
            offset_in_backing,
            size_after_one_fold,
        }
    }

    fn buffer_start_mut(&self) -> *mut E {
        // SAFETY: `offset_in_backing` is bounded by `backing.len()` (asserted in
        // every constructor). Cast-to-mut mirrors the pattern used by
        // `GpuExtensionFieldPoly::as_mut_ptr` — the Arc-backed allocation is
        // pool-owned and pointer-mutable through stream-ordered ops.
        unsafe { self.backing.as_ptr().cast_mut().add(self.offset_in_backing) }
    }

    pub(crate) fn pointer_for_sumcheck_after_one_fold(&mut self) -> *mut E {
        self.buffer_start_mut()
    }

    pub(crate) fn pointer_for_sumcheck_continuation(&mut self, step: usize) -> (*mut E, *mut E) {
        unsafe {
            assert!(step >= 2);
            let mut input_offset = self.buffer_start_mut();
            let mut input_size = self.size_after_one_fold;
            let mut next_step_offset = input_offset.add(input_size);
            for _ in 2..step {
                input_offset = next_step_offset;
                input_size /= 2;
                debug_assert!(input_size > 0);
                next_step_offset = next_step_offset.add(input_size);
            }

            (input_offset, next_step_offset)
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct GpuSumcheckRound1PreparedStorage<B, E> {
    pub(crate) base_field_inputs: Vec<GpuBaseFieldPolySourceAfterOneFoldingPlan<B, E>>,
    pub(crate) extension_field_inputs: Vec<GpuExtensionFieldPolyContinuingSourcePlan<E>>,
}

#[derive(Clone, Debug)]
pub(crate) struct GpuSumcheckRound2PreparedStorage<B, E> {
    pub(crate) base_field_inputs: Vec<GpuBaseFieldPolySourceAfterTwoFoldingsPlan<B, E>>,
    pub(crate) extension_field_inputs: Vec<GpuExtensionFieldPolyContinuingSourcePlan<E>>,
}

#[derive(Clone, Debug)]
pub(crate) struct GpuSumcheckRound3AndBeyondPreparedStorage<E> {
    pub(crate) base_field_inputs: Vec<GpuExtensionFieldPolyContinuingSourcePlan<E>>,
    pub(crate) extension_field_inputs: Vec<GpuExtensionFieldPolyContinuingSourcePlan<E>>,
}

// Round-1 launch-descriptor types + the prepared-storage upload path,
// relocated out of the crate's `#[cfg(test)] mod tests` (production-shaped,
// no test-framework dependency) so the apex e2e suite can drive
// `schedule_round_1` and read `.device.base_field_inputs` across the crate
// boundary. `#[doc(hidden)] pub` per the split's test-reference policy.
#[doc(hidden)]
pub struct GpuSumcheckRound1DeviceLaunchDescriptors<B, E> {
    pub base_field_inputs:
        DeviceAllocation<GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E>>,
    pub extension_field_inputs:
        DeviceAllocation<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
}

#[doc(hidden)]
pub struct GpuSumcheckRound1ScheduledLaunchDescriptors<B, E> {
    pub device: GpuSumcheckRound1DeviceLaunchDescriptors<B, E>,
}

#[doc(hidden)]
#[derive(Clone, Debug)]
pub struct GpuSumcheckRound1HostLaunchDescriptors<B, E: Copy> {
    pub base_field_inputs: Vec<GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E>>,
    pub extension_field_inputs: Vec<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
}

/// Stream-ordered host staging: fill via a scheduled callback, then upload.
#[doc(hidden)]
pub fn alloc_host_and_schedule_copy<T: Copy + Send + Sync + 'static>(
    context: &ProverContext,
    callbacks: &mut Callbacks<'static>,
    values: Vec<T>,
) -> HostAllocation<[T]> {
    let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
    let host_accessor = host.get_mut_accessor();
    callbacks
        .schedule(
            move || unsafe {
                host_accessor.get_mut().copy_from_slice(&values);
            },
            context.get_exec_stream(),
        )
        .expect("failed to schedule host copy callback");
    host
}

#[doc(hidden)]
pub fn alloc_device_and_schedule_upload<T: Copy>(
    context: &ProverContext,
    host: &HostAllocation<[T]>,
) -> CudaResult<DeviceAllocation<T>> {
    let mut device = context.alloc(host.len(), AllocationPlacement::Top)?;
    memory_copy_async(&mut device, host, context.get_exec_stream())?;
    Ok(device)
}

impl<B: 'static, E: Field + 'static> GpuSumcheckRound1PreparedStorage<B, E> {
    #[doc(hidden)]
    pub fn build_launch_descriptors(&self) -> GpuSumcheckRound1HostLaunchDescriptors<B, E> {
        let base_field_inputs = self
            .base_field_inputs
            .iter()
            .map(
                |plan| GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                    base_layer_half_size: plan.base_layer_half_size,
                    next_layer_size: plan.next_layer_size,
                    base_input_start: plan.base_input_start,
                    this_layer_cache_start: plan.this_layer_cache_start,
                    first_access: plan.first_access,
                    source_kind: plan.source_kind,
                    _marker: core::marker::PhantomData,
                },
            )
            .collect();
        let extension_field_inputs = self
            .extension_field_inputs
            .iter()
            .map(|plan| GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: plan.previous_layer_start,
                this_layer_start: plan.this_layer_start,
                this_layer_size: plan.this_layer_size,
                next_layer_size: plan.next_layer_size,
                first_access: plan.first_access,
            })
            .collect();
        GpuSumcheckRound1HostLaunchDescriptors {
            base_field_inputs,
            extension_field_inputs,
        }
    }

    #[doc(hidden)]
    pub fn schedule_upload_launch_descriptors(
        &self,
        context: &ProverContext,
        callbacks: &mut Callbacks<'static>,
    ) -> CudaResult<GpuSumcheckRound1ScheduledLaunchDescriptors<B, E>> {
        let descriptors = self.build_launch_descriptors();
        let host_base =
            alloc_host_and_schedule_copy(context, callbacks, descriptors.base_field_inputs);
        let base_field_inputs_device = alloc_device_and_schedule_upload(context, &host_base)?;
        drop(host_base);
        let host_ext =
            alloc_host_and_schedule_copy(context, callbacks, descriptors.extension_field_inputs);
        let extension_field_inputs_device = alloc_device_and_schedule_upload(context, &host_ext)?;
        drop(host_ext);
        let device = GpuSumcheckRound1DeviceLaunchDescriptors {
            base_field_inputs: base_field_inputs_device,
            extension_field_inputs: extension_field_inputs_device,
        };
        Ok(GpuSumcheckRound1ScheduledLaunchDescriptors { device })
    }
}

impl<B, E> GpuGKRStorage<B, E> {
    /// Attach a pre-computed storage layout. Subsequent
    /// `allocate_base_view` / `allocate_ext_view` calls will route allocations
    /// through the per-class consolidated backings indexed by this layout.
    pub(crate) fn set_layout(&mut self, layout: Arc<GpuGKRStorageLayout>) {
        assert!(self.layout.is_none(), "layout already set");
        self.layout = Some(layout);
    }

    pub(crate) fn base_trace_len(&self) -> usize {
        self.layers
            .first()
            .and_then(|layer| {
                layer
                    .base_field_inputs
                    .values()
                    .map(GpuBaseFieldPoly::len)
                    .max()
            })
            .expect("layer 0 must contain at least one real base-field polynomial")
    }

    pub(crate) fn base_poly_layer(address: GKRAddress) -> Option<usize> {
        match address {
            GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => Some(layer),
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..)
            | GKRAddress::ScratchSpace(..) => Some(0),
        }
    }

    pub(crate) fn ext_poly_layer(address: GKRAddress) -> Option<usize> {
        match address {
            GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => Some(layer),
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..)
            | GKRAddress::ScratchSpace(..) => None,
        }
    }

    pub(crate) fn get_base_poly_for_address(
        &self,
        address: GKRAddress,
    ) -> Option<&GpuBaseFieldPoly<B>> {
        let layer = Self::base_poly_layer(address)?;
        self.layers.get(layer)?.base_field_inputs.get(&address)
    }

    pub(crate) fn get_ext_poly_for_address(
        &self,
        address: GKRAddress,
    ) -> Option<&GpuExtensionFieldPoly<E>> {
        let layer = Self::ext_poly_layer(address)?;
        self.layers.get(layer)?.extension_field_inputs.get(&address)
    }

    pub(crate) fn get_base_source_for_round_0(
        &self,
        address: GKRAddress,
    ) -> GpuBaseFieldPolySource<B> {
        if let Some(source_kind) = GpuBaseFieldSourceKind::from_address(address) {
            return GpuBaseFieldPolySource {
                start: null(),
                next_layer_size: self.base_trace_len() / 2,
                source_kind,
            };
        }

        let layer = match address {
            GKRAddress::Cached { layer, .. } | GKRAddress::InnerLayer { layer, .. } => layer,
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..)
            | GKRAddress::ScratchSpace(..) => 0,
        };
        let source = self.layers[layer]
            .base_field_inputs
            .get(&address)
            .unwrap_or_else(|| {
                panic!(
                    "Polynomial with address {:?} is missing from input sources for base field polys",
                    address
                )
            });
        source.accessor()
    }

    #[cfg(test)]
    pub(crate) fn get_base_layer_mem(&self, offset: usize) -> &GpuBaseFieldPoly<B> {
        self.get_base_poly_for_address(GKRAddress::BaseLayerMemory(offset))
            .expect("base layer memory poly must exist")
    }

    pub fn get_base_layer(&self, address: GKRAddress) -> &GpuBaseFieldPoly<B> {
        self.get_base_poly_for_address(address)
            .expect("base layer poly must exist")
    }

    pub fn try_get_base_poly(&self, address: GKRAddress) -> Option<&GpuBaseFieldPoly<B>> {
        self.get_base_poly_for_address(address)
    }

    pub fn try_get_ext_poly(&self, address: GKRAddress) -> Option<&GpuExtensionFieldPoly<E>> {
        self.get_ext_poly_for_address(address)
    }

    pub(crate) fn purge_up_to_layer(&mut self, layer: usize) {
        self.layers.truncate(layer + 1);
    }

    pub fn get_ext_poly(&self, address: GKRAddress) -> &GpuExtensionFieldPoly<E> {
        self.get_ext_poly_for_address(address)
            .expect("extension poly must exist")
    }

    pub(crate) fn insert_base_field_at_layer(
        &mut self,
        layer: usize,
        address: GKRAddress,
        value: GpuBaseFieldPoly<B>,
    ) {
        if layer >= self.layers.len() {
            self.layers
                .resize_with(layer + 1, GpuGKRLayerSource::default);
        }
        let existing = self.layers[layer].base_field_inputs.insert(address, value);
        assert!(
            existing.is_none(),
            "trying to insert another value for layer {}, address {:?}",
            layer,
            address
        );
    }

    pub(crate) fn insert_extension_at_layer(
        &mut self,
        layer: usize,
        address: GKRAddress,
        value: GpuExtensionFieldPoly<E>,
    ) {
        if layer >= self.layers.len() {
            self.layers
                .resize_with(layer + 1, GpuGKRLayerSource::default);
        }
        let existing = self.layers[layer]
            .extension_field_inputs
            .insert(address, value);
        assert!(
            existing.is_none(),
            "trying to insert another value for layer {}, address {:?}",
            layer,
            address
        );
    }
}

// Relocated from `#[cfg(test)] mod tests` (row 39 test-reference): apex
// stagewise/asserts read backing sharing + device chunks off polys.
impl<B> GpuBaseFieldPoly<B> {
    // Only this crate's own test files (`tests.rs`, `forward/tests/**`)
    // construct/inspect polys via `new`/`offset` directly; production code
    // and cross-crate test callers go through `from_arc`/`shares_backing_with`.
    #[cfg(test)]
    pub(crate) fn new(backing: DeviceAllocation<B>) -> Self {
        let len = backing.len();
        Self::from_arc(Arc::new(backing), 0, len)
    }

    #[cfg(test)]
    pub(crate) fn offset(&self) -> usize {
        self.offset
    }

    #[doc(hidden)]
    pub fn shares_backing_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.backing, &other.backing)
    }
}

impl<E> GpuExtensionFieldPoly<E> {
    // See the `GpuBaseFieldPoly` impl above: test-only constructor/accessor.
    #[cfg(test)]
    pub(crate) fn new(backing: DeviceAllocation<E>) -> Self {
        let len = backing.len();
        Self::from_arc(Arc::new(backing), 0, len)
    }

    #[cfg(test)]
    pub(crate) fn offset(&self) -> usize {
        self.offset
    }

    #[doc(hidden)]
    pub fn shares_backing_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.backing, &other.backing)
    }

    #[doc(hidden)]
    pub fn as_device_chunk(&self) -> DeviceVectorChunk<'_, E> {
        DeviceVectorChunk::new(self.backing.as_ref(), self.offset, self.len)
    }
}
