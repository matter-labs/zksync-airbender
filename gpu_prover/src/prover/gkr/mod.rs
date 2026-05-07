// GPU scheduling contract: see docs/gpu_scheduling_contract.md

pub(crate) mod backward;
pub(crate) mod backward_compact_encoder;
pub(crate) mod backward_flat;
pub(crate) mod backward_flat_compact;
pub(crate) mod backward_kernels;
pub(crate) mod base_layer_claims;
pub(crate) mod forward;
pub(crate) mod forward_kernels;
pub(crate) mod gkr_address_audit;
pub(crate) mod setup;
pub(crate) mod setup_kernels;
pub(crate) mod stage1;
pub(crate) mod storage_layout;
pub(crate) mod transform;

use std::collections::BTreeMap;
use std::ptr::null;
use std::sync::Arc;

use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext};
use crate::primitives::device_structures::{DeviceVectorChunk, DeviceVectorChunkMut};
use crate::prover::gkr::gkr_address_audit::AddressClass;
use crate::prover::gkr::storage_layout::{FieldType, GpuGKRStorageLayout, StorageSlot};
use cs::definitions::{GKRAddress, VirtualSetupPoly};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, DeviceSlice};
use field::Field;
use prover::gkr::sumcheck::evaluation_kernels::GKRInputs;

pub(crate) struct GpuGKRLayerSource<B, E> {
    pub(crate) base_field_inputs: BTreeMap<GKRAddress, GpuBaseFieldPoly<B>>,
    pub(crate) extension_field_inputs: BTreeMap<GKRAddress, GpuExtensionFieldPoly<E>>,
    pub(crate) intermediate_storage_for_folder_base_field_inputs:
        BTreeMap<GKRAddress, (usize, GpuBaseFieldPolyIntermediateFoldingStorage<E>)>,
    pub(crate) intermediate_storage_for_folder_extension_field_inputs:
        BTreeMap<GKRAddress, (usize, GpuExtensionFieldPolyIntermediateFoldingStorage<E>)>,
    /// Consolidated per-`AddressClass` backings for base-field polys living at
    /// this layer. Lazily allocated by `GpuGKRStorage::allocate_base_view`
    /// when a layout is set; size is taken from the layout's per-slot poly
    /// count. Empty when no consolidated allocations have been requested for
    /// this layer (per-poly fallback path).
    pub(crate) base_class_backings: BTreeMap<AddressClass, Arc<DeviceAllocation<B>>>,
    pub(crate) ext_class_backings: BTreeMap<AddressClass, Arc<DeviceAllocation<E>>>,
    /// Per-layer consolidated backing for ext-field intermediate folding
    /// buffers used by dim-reducing rounds 1+. Pre-allocated by
    /// `GpuGKRStorage::register_dim_reducing_inputs_for_layer` from the
    /// blueprint input set; subsequent `plan_ext_source_for_rounds_1_and_beyond`
    /// calls slice views from this allocation instead of allocating per-poly.
    /// `None` when registration hasn't been called (legacy lazy per-poly path).
    pub(crate) intermediate_folding_consolidated: Option<ConsolidatedFoldingBacking<E>>,
    /// Per-layer consolidated backing for base-field intermediate folding
    /// buffers used by main-layer flat-path rounds 1+ (Phase A2-flat-base).
    /// Pre-allocated by `GpuGKRStorage::register_flat_base_folding_for_layer`
    /// from the main-layer blueprint base-input set; subsequent
    /// `plan_base_source_for_round_1` / `_round_2` /
    /// `_for_rounds_3_and_beyond` calls slice views into this allocation
    /// instead of allocating per-poly. Polys whose address is not present in
    /// the storage layout (currently `VirtualSetup`) fall back to the legacy
    /// lazy per-poly path. `None` when registration hasn't been called.
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
/// `per_poly_size = base_poly_size / 2` (matches the legacy
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

pub(crate) struct GpuGKRStorage<B, E> {
    pub(crate) layers: Vec<GpuGKRLayerSource<B, E>>,
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

pub(crate) struct GpuBaseFieldPoly<B> {
    backing: Arc<DeviceAllocation<B>>,
    offset: usize,
    len: usize,
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
    pub(crate) fn new(backing: DeviceAllocation<B>) -> Self {
        let len = backing.len();
        Self::from_arc(Arc::new(backing), 0, len)
    }

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

    pub(crate) fn len(&self) -> usize {
        self.len
    }

    pub(crate) fn offset(&self) -> usize {
        self.offset
    }

    pub(crate) fn shares_backing_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.backing, &other.backing)
    }

    pub(crate) fn as_ptr(&self) -> *const B {
        unsafe { self.backing.as_ptr().add(self.offset) }
    }

    /// Mutable raw pointer to the view's range. Caller must ensure exclusive
    /// write access (no concurrent writes from other clones of this view).
    /// Used by forward kernel descriptors that write into the consolidated
    /// per-class backing through this view's slot.
    pub(crate) fn as_mut_ptr(&self) -> *mut B {
        unsafe { self.backing.as_ptr().add(self.offset) as *mut B }
    }

    pub(crate) fn as_device_chunk(&self) -> DeviceVectorChunk<'_, B> {
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

pub(crate) struct GpuExtensionFieldPoly<E> {
    backing: Arc<DeviceAllocation<E>>,
    offset: usize,
    len: usize,
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
    pub(crate) fn new(backing: DeviceAllocation<E>) -> Self {
        let len = backing.len();
        Self::from_arc(Arc::new(backing), 0, len)
    }

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

    pub(crate) fn len(&self) -> usize {
        self.len
    }

    pub(crate) fn offset(&self) -> usize {
        self.offset
    }

    pub(crate) fn shares_backing_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.backing, &other.backing)
    }

    pub(crate) fn as_ptr(&self) -> *const E {
        unsafe { self.backing.as_ptr().add(self.offset) }
    }

    /// Mutable raw pointer to the view's range. Caller must ensure exclusive
    /// write access (no concurrent writes from other clones of this view).
    pub(crate) fn as_mut_ptr(&self) -> *mut E {
        unsafe { self.backing.as_ptr().add(self.offset) as *mut E }
    }

    pub(crate) fn as_device_chunk(&self) -> DeviceVectorChunk<'_, E> {
        DeviceVectorChunk::new(self.backing.as_ref(), self.offset, self.len)
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
/// fresh per-poly Arc (legacy lazy path); `from_arc` slices a view into
/// a per-layer consolidated allocation (Phase A2-flat-base path). Both
/// forms expose the same buffer-pointer semantics; the
/// `offset_in_backing` field shifts the buffer's effective start within
/// `backing`.
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
/// Always holds an `Arc<DeviceAllocation<E>>` backing slice. `new_for_extension_poly_size`
/// allocates a fresh per-poly allocation (legacy lazy path); `from_arc` slices a
/// view into a per-layer consolidated allocation (Phase B consolidation path).
/// Both forms expose the same buffer-pointer semantics; the `offset_in_backing`
/// field shifts the buffer's effective start within `backing`.
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

#[derive(Debug, PartialEq, Eq)]
#[repr(u32)]
pub(crate) enum GpuBaseFieldSourceKind {
    Empty = 0,
    Real = 1,
    VirtualRangeCheck16Bits = 2,
    VirtualRangeCheckTimestamp = 3,
    VirtualInitsAndTeardownsLow = 4,
    VirtualInitsAndTeardownsHigh = 5,
}

impl Clone for GpuBaseFieldSourceKind {
    fn clone(&self) -> Self {
        *self
    }
}

impl Copy for GpuBaseFieldSourceKind {}

impl Default for GpuBaseFieldSourceKind {
    fn default() -> Self {
        Self::Empty
    }
}

impl GpuBaseFieldSourceKind {
    pub(crate) const fn from_virtual_setup(poly: VirtualSetupPoly) -> Self {
        match poly {
            VirtualSetupPoly::RangeCheck16Bits => Self::VirtualRangeCheck16Bits,
            VirtualSetupPoly::RangeCheckTimestamp => Self::VirtualRangeCheckTimestamp,
            VirtualSetupPoly::InitsAndTeardownsLow => Self::VirtualInitsAndTeardownsLow,
            VirtualSetupPoly::InitsAndTeardownsHigh => Self::VirtualInitsAndTeardownsHigh,
        }
    }

    pub(crate) const fn from_address(address: GKRAddress) -> Option<Self> {
        match address {
            GKRAddress::VirtualSetup(poly) => Some(Self::from_virtual_setup(poly)),
            _ => None,
        }
    }
}

#[derive(Debug)]
#[repr(C)]
pub(crate) struct GpuBaseFieldPolySource<B> {
    pub(crate) start: *const B,
    pub(crate) next_layer_size: usize,
    pub(crate) source_kind: GpuBaseFieldSourceKind,
}

impl<B> Clone for GpuBaseFieldPolySource<B> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<B> Copy for GpuBaseFieldPolySource<B> {}

// SAFETY: contains only a device pointer and a size — safe to send across threads.
unsafe impl<B> Send for GpuBaseFieldPolySource<B> {}
unsafe impl<B> Sync for GpuBaseFieldPolySource<B> {}

impl<B> GpuBaseFieldPolySource<B> {
    pub(crate) fn empty() -> Self {
        Self {
            start: null(),
            next_layer_size: 0,
            source_kind: GpuBaseFieldSourceKind::Empty,
        }
    }
}

// These descriptors live in preallocated host/device buffers that are owned by the scheduler.
// Dynamic transcript data is staged separately in tiny per-round challenge buffers.
#[derive(Debug)]
#[repr(C)]
pub(crate) struct GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E> {
    pub(crate) base_layer_half_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) base_input_start: *const B,
    pub(crate) this_layer_cache_start: *mut E,
    pub(crate) first_access: bool,
    pub(crate) source_kind: GpuBaseFieldSourceKind,
    pub(crate) _marker: core::marker::PhantomData<E>,
}

impl<B, E: Copy> Clone for GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<B, E: Copy> Copy for GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E> {}

// SAFETY: contains only device pointers and sizes — safe to send across threads.
unsafe impl<B, E> Send for GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E> {}
unsafe impl<B, E> Sync for GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E> {}

#[derive(Debug)]
#[repr(C)]
pub(crate) struct GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E> {
    pub(crate) base_input_start: *const B,
    pub(crate) this_layer_cache_start: *mut E,
    pub(crate) base_layer_half_size: usize,
    pub(crate) base_quarter_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) first_access: bool,
    pub(crate) source_kind: GpuBaseFieldSourceKind,
}

impl<B, E: Copy> Clone for GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<B, E: Copy> Copy for GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E> {}

// SAFETY: contains only device pointers and sizes — safe to send across threads.
unsafe impl<B, E> Send for GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E> {}
unsafe impl<B, E> Sync for GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E> {}

#[derive(Debug)]
#[repr(C)]
pub(crate) struct GpuExtensionFieldPolyInitialSource<E> {
    pub(crate) start: *const E,
    pub(crate) next_layer_size: usize,
}

impl<E> Clone for GpuExtensionFieldPolyInitialSource<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E> Copy for GpuExtensionFieldPolyInitialSource<E> {}

// SAFETY: contains only a device pointer and a size — safe to send across threads.
unsafe impl<E> Send for GpuExtensionFieldPolyInitialSource<E> {}
unsafe impl<E> Sync for GpuExtensionFieldPolyInitialSource<E> {}

impl<E> GpuExtensionFieldPolyInitialSource<E> {
    pub(crate) fn empty() -> Self {
        Self {
            start: null(),
            next_layer_size: 0,
        }
    }
}

#[derive(Debug)]
#[repr(C)]
pub(crate) struct GpuExtensionFieldPolyContinuingLaunchDescriptor<E> {
    pub(crate) previous_layer_start: *const E,
    pub(crate) this_layer_start: *mut E,
    pub(crate) this_layer_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) first_access: bool,
}

impl<E: Copy> Clone for GpuExtensionFieldPolyContinuingLaunchDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E: Copy> Copy for GpuExtensionFieldPolyContinuingLaunchDescriptor<E> {}

// SAFETY: contains only device pointers and sizes — safe to send across threads.
unsafe impl<E> Send for GpuExtensionFieldPolyContinuingLaunchDescriptor<E> {}
unsafe impl<E> Sync for GpuExtensionFieldPolyContinuingLaunchDescriptor<E> {}

#[derive(Clone, Debug)]
pub(crate) struct GpuSumcheckRound0LaunchDescriptors<B, E> {
    pub(crate) base_field_inputs: Vec<GpuBaseFieldPolySource<B>>,
    pub(crate) extension_field_inputs: Vec<GpuExtensionFieldPolyInitialSource<E>>,
    pub(crate) base_field_outputs: Vec<GpuBaseFieldPolySource<B>>,
    pub(crate) extension_field_outputs: Vec<GpuExtensionFieldPolyInitialSource<E>>,
}

impl<B, E> Default for GpuSumcheckRound0LaunchDescriptors<B, E> {
    fn default() -> Self {
        Self {
            base_field_inputs: Vec::new(),
            extension_field_inputs: Vec::new(),
            base_field_outputs: Vec::new(),
            extension_field_outputs: Vec::new(),
        }
    }
}

pub(crate) struct GpuSumcheckRound0HostLaunchDescriptors<B, E> {
    pub(crate) base_field_inputs: HostAllocation<[GpuBaseFieldPolySource<B>]>,
    pub(crate) extension_field_inputs: HostAllocation<[GpuExtensionFieldPolyInitialSource<E>]>,
    pub(crate) base_field_outputs: HostAllocation<[GpuBaseFieldPolySource<B>]>,
    pub(crate) extension_field_outputs: HostAllocation<[GpuExtensionFieldPolyInitialSource<E>]>,
}

pub(crate) struct GpuSumcheckRound0DeviceLaunchDescriptors<B, E> {
    pub(crate) base_field_inputs: DeviceAllocation<GpuBaseFieldPolySource<B>>,
    pub(crate) extension_field_inputs: DeviceAllocation<GpuExtensionFieldPolyInitialSource<E>>,
    pub(crate) base_field_outputs: DeviceAllocation<GpuBaseFieldPolySource<B>>,
    pub(crate) extension_field_outputs: DeviceAllocation<GpuExtensionFieldPolyInitialSource<E>>,
}

pub(crate) struct GpuSumcheckRound0ScheduledLaunchDescriptors<B, E> {
    pub(crate) callbacks: Callbacks<'static>,
    #[cfg(test)]
    pub(crate) host: GpuSumcheckRound0HostLaunchDescriptors<B, E>,
    pub(crate) device: GpuSumcheckRound0DeviceLaunchDescriptors<B, E>,
}

pub(crate) struct GpuSumcheckRound1DeviceLaunchDescriptors<B, E> {
    pub(crate) base_field_inputs:
        DeviceAllocation<GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E>>,
    pub(crate) extension_field_inputs:
        DeviceAllocation<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
}

pub(crate) struct GpuSumcheckRound1ScheduledLaunchDescriptors<B, E> {
    pub(crate) device: GpuSumcheckRound1DeviceLaunchDescriptors<B, E>,
}

#[derive(Clone, Debug)]
pub(crate) struct GpuSumcheckRound1HostLaunchDescriptors<B, E: Copy> {
    pub(crate) base_field_inputs: Vec<GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E>>,
    pub(crate) extension_field_inputs: Vec<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
}

pub(crate) struct GpuSumcheckRound2DeviceLaunchDescriptors<B, E> {
    pub(crate) base_field_inputs:
        DeviceAllocation<GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E>>,
    pub(crate) extension_field_inputs:
        DeviceAllocation<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
}

pub(crate) struct GpuSumcheckRound2ScheduledLaunchDescriptors<B, E> {
    pub(crate) device: GpuSumcheckRound2DeviceLaunchDescriptors<B, E>,
}

#[derive(Clone, Debug)]
pub(crate) struct GpuSumcheckRound2HostLaunchDescriptors<B, E: Copy> {
    pub(crate) base_field_inputs: Vec<GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E>>,
    pub(crate) extension_field_inputs: Vec<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
}

pub(crate) struct GpuSumcheckRound3AndBeyondDeviceLaunchDescriptors<E> {
    pub(crate) base_field_inputs:
        DeviceAllocation<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
    pub(crate) extension_field_inputs:
        DeviceAllocation<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
}

pub(crate) struct GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors<E> {
    pub(crate) device: GpuSumcheckRound3AndBeyondDeviceLaunchDescriptors<E>,
}

#[derive(Clone, Debug)]
pub(crate) struct GpuSumcheckRound3AndBeyondHostLaunchDescriptors<E: Copy> {
    pub(crate) base_field_inputs: Vec<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
    pub(crate) extension_field_inputs: Vec<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
}

#[derive(Debug)]
pub(crate) struct GpuBaseFieldPolySourceAfterOneFoldingPlan<B, E> {
    pub(crate) base_layer_half_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) base_input_start: *const B,
    pub(crate) this_layer_cache_start: *mut E,
    pub(crate) first_access: bool,
    pub(crate) source_kind: GpuBaseFieldSourceKind,
}

impl<B, E> Clone for GpuBaseFieldPolySourceAfterOneFoldingPlan<B, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<B, E> Copy for GpuBaseFieldPolySourceAfterOneFoldingPlan<B, E> {}

unsafe impl<B, E> Send for GpuBaseFieldPolySourceAfterOneFoldingPlan<B, E> {}
unsafe impl<B, E> Sync for GpuBaseFieldPolySourceAfterOneFoldingPlan<B, E> {}

impl<B, E> GpuBaseFieldPolySourceAfterOneFoldingPlan<B, E> {
    fn empty() -> Self {
        Self {
            base_layer_half_size: 0,
            next_layer_size: 0,
            base_input_start: null(),
            this_layer_cache_start: null::<E>().cast_mut(),
            first_access: false,
            source_kind: GpuBaseFieldSourceKind::Empty,
        }
    }
}

#[derive(Debug)]
pub(crate) struct GpuBaseFieldPolySourceAfterTwoFoldingsPlan<B, E> {
    pub(crate) base_input_start: *const B,
    pub(crate) this_layer_cache_start: *mut E,
    pub(crate) base_layer_half_size: usize,
    pub(crate) base_quarter_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) first_access: bool,
    pub(crate) source_kind: GpuBaseFieldSourceKind,
}

impl<B, E> Clone for GpuBaseFieldPolySourceAfterTwoFoldingsPlan<B, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<B, E> Copy for GpuBaseFieldPolySourceAfterTwoFoldingsPlan<B, E> {}

unsafe impl<B, E> Send for GpuBaseFieldPolySourceAfterTwoFoldingsPlan<B, E> {}
unsafe impl<B, E> Sync for GpuBaseFieldPolySourceAfterTwoFoldingsPlan<B, E> {}

impl<B, E> GpuBaseFieldPolySourceAfterTwoFoldingsPlan<B, E> {
    fn empty() -> Self {
        Self {
            base_input_start: null(),
            this_layer_cache_start: null::<E>().cast_mut(),
            base_layer_half_size: 0,
            base_quarter_size: 0,
            next_layer_size: 0,
            first_access: false,
            source_kind: GpuBaseFieldSourceKind::Empty,
        }
    }
}

#[derive(Debug)]
pub(crate) struct GpuExtensionFieldPolyContinuingSourcePlan<E> {
    pub(crate) previous_layer_start: *const E,
    pub(crate) this_layer_start: *mut E,
    pub(crate) this_layer_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) first_access: bool,
}

impl<E> Clone for GpuExtensionFieldPolyContinuingSourcePlan<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E> Copy for GpuExtensionFieldPolyContinuingSourcePlan<E> {}

unsafe impl<E> Send for GpuExtensionFieldPolyContinuingSourcePlan<E> {}
unsafe impl<E> Sync for GpuExtensionFieldPolyContinuingSourcePlan<E> {}

impl<E> GpuExtensionFieldPolyContinuingSourcePlan<E> {
    fn empty() -> Self {
        Self {
            previous_layer_start: null(),
            this_layer_start: null::<E>().cast_mut(),
            this_layer_size: 0,
            next_layer_size: 0,
            first_access: false,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct GpuSumcheckRound1PreparedStorage<B, E> {
    pub(crate) base_field_inputs: Vec<GpuBaseFieldPolySourceAfterOneFoldingPlan<B, E>>,
    pub(crate) extension_field_inputs: Vec<GpuExtensionFieldPolyContinuingSourcePlan<E>>,
    pub(crate) sumcheck_step: usize,
}

#[derive(Clone, Debug)]
pub(crate) struct GpuSumcheckRound2PreparedStorage<B, E> {
    pub(crate) base_field_inputs: Vec<GpuBaseFieldPolySourceAfterTwoFoldingsPlan<B, E>>,
    pub(crate) extension_field_inputs: Vec<GpuExtensionFieldPolyContinuingSourcePlan<E>>,
    pub(crate) sumcheck_step: usize,
}

#[derive(Clone, Debug)]
pub(crate) struct GpuSumcheckRound3AndBeyondPreparedStorage<E> {
    pub(crate) base_field_inputs: Vec<GpuExtensionFieldPolyContinuingSourcePlan<E>>,
    pub(crate) extension_field_inputs: Vec<GpuExtensionFieldPolyContinuingSourcePlan<E>>,
    pub(crate) sumcheck_step: usize,
}

pub(super) fn alloc_host_and_schedule_copy<T: Copy + Send + Sync + 'static>(
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

fn alloc_device_and_schedule_upload<T: Copy>(
    context: &ProverContext,
    host: &HostAllocation<[T]>,
) -> CudaResult<DeviceAllocation<T>> {
    let mut device = context.alloc(host.len(), AllocationPlacement::Top)?;
    memory_copy_async(&mut device, host, context.get_exec_stream())?;
    Ok(device)
}

fn schedule_callback_populated_upload<'a, T: Copy + 'a>(
    context: &ProverContext,
    len: usize,
    callbacks: &mut Callbacks<'a>,
    fill: impl Fn(&mut [T]) + Send + Sync + 'a,
) -> CudaResult<(HostAllocation<[T]>, DeviceAllocation<T>)> {
    let mut host = unsafe { context.alloc_host_uninit_slice(len) };
    let host_accessor = host.get_mut_accessor();
    callbacks.schedule(
        move || unsafe { fill(host_accessor.get_mut()) },
        context.get_exec_stream(),
    )?;
    let device = alloc_device_and_schedule_upload(context, &host)?;
    Ok((host, device))
}

impl<B, E> GpuGKRStorage<B, E> {
    /// Attach a pre-computed storage layout. Subsequent
    /// `allocate_base_view` / `allocate_ext_view` calls will route allocations
    /// through the per-class consolidated backings indexed by this layout.
    pub(crate) fn set_layout(&mut self, layout: Arc<GpuGKRStorageLayout>) {
        assert!(self.layout.is_none(), "layout already set");
        self.layout = Some(layout);
    }

    fn base_trace_len(&self) -> usize {
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

    fn base_poly_layer(address: GKRAddress) -> Option<usize> {
        match address {
            GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => Some(layer),
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..) => Some(0),
            GKRAddress::ScratchSpace(..) => None,
        }
    }

    fn ext_poly_layer(address: GKRAddress) -> Option<usize> {
        match address {
            GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => Some(layer),
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..)
            | GKRAddress::ScratchSpace(..) => None,
        }
    }

    fn get_base_poly_for_address(&self, address: GKRAddress) -> Option<&GpuBaseFieldPoly<B>> {
        let layer = Self::base_poly_layer(address)?;
        self.layers.get(layer)?.base_field_inputs.get(&address)
    }

    fn get_ext_poly_for_address(&self, address: GKRAddress) -> Option<&GpuExtensionFieldPoly<E>> {
        let layer = Self::ext_poly_layer(address)?;
        self.layers.get(layer)?.extension_field_inputs.get(&address)
    }

    fn get_base_source_for_round_0(&self, address: GKRAddress) -> GpuBaseFieldPolySource<B> {
        if let Some(source_kind) = GpuBaseFieldSourceKind::from_address(address) {
            return GpuBaseFieldPolySource {
                start: null(),
                next_layer_size: self.base_trace_len() / 2,
                source_kind,
            };
        }

        let layer = match address {
            GKRAddress::ScratchSpace(..) => unreachable!(),
            GKRAddress::Cached { layer, .. } | GKRAddress::InnerLayer { layer, .. } => layer,
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..) => 0,
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

    pub(crate) fn get_base_layer(&self, address: GKRAddress) -> &GpuBaseFieldPoly<B> {
        self.get_base_poly_for_address(address)
            .expect("base layer poly must exist")
    }

    pub(crate) fn try_get_base_poly(&self, address: GKRAddress) -> Option<&GpuBaseFieldPoly<B>> {
        self.get_base_poly_for_address(address)
    }

    pub(crate) fn try_get_ext_poly(
        &self,
        address: GKRAddress,
    ) -> Option<&GpuExtensionFieldPoly<E>> {
        self.get_ext_poly_for_address(address)
    }

    pub(crate) fn purge_up_to_layer(&mut self, layer: usize) {
        self.layers.truncate(layer + 1);
    }

    pub(crate) fn get_ext_poly(&self, address: GKRAddress) -> &GpuExtensionFieldPoly<E> {
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

    /// Returns a fresh `GpuBaseFieldPoly<B>` view backed by the consolidated
    /// per-`AddressClass` allocation for `(layer, FieldType::Base)` at this
    /// storage layer. The backing is lazily allocated on first call for that
    /// `(layer, class)` pair, sized from the layout's per-slot poly count.
    /// Panics if no layout is set, or if the address has no entry in the
    /// layout's per-layer index, or if its layout entry is `FieldType::Ext`.
    pub(crate) fn allocate_base_view(
        &mut self,
        layer: usize,
        address: GKRAddress,
        context: &ProverContext,
    ) -> CudaResult<GpuBaseFieldPoly<B>>
    where
        B: 'static,
    {
        let layout = self
            .layout
            .as_ref()
            .expect("storage layout required for allocate_base_view")
            .clone();
        let (canonical_layer, class, field, poly_idx) = layout
            .lookup(layer, &address)
            .unwrap_or_else(|| panic!("address {address:?} missing from layer {layer} layout"));
        assert_eq!(
            field,
            FieldType::Base,
            "address {address:?} is not classified as a base poly in layout"
        );
        let layer_layout = layout
            .layers
            .get(canonical_layer)
            .unwrap_or_else(|| panic!("canonical layer {canonical_layer} out of range in layout"));

        if canonical_layer >= self.layers.len() {
            self.layers
                .resize_with(canonical_layer + 1, GpuGKRLayerSource::default);
        }

        let layer_log2_stride = layer_layout.log2_stride;
        let stride = 1usize << layer_log2_stride;
        let offset = (poly_idx as usize) << layer_log2_stride;
        let backing = match self.layers[canonical_layer].base_class_backings.get(&class) {
            Some(arc) => Arc::clone(arc),
            None => {
                let count = layer_layout
                    .slot_poly_counts
                    .get(&StorageSlot {
                        class,
                        field: FieldType::Base,
                    })
                    .copied()
                    .unwrap_or_else(|| {
                        panic!("layout missing slot count for layer {canonical_layer} class {class:?} base")
                    });
                assert!(count > 0);
                let total_size = (count as usize) << layer_log2_stride;
                let alloc = context.alloc(total_size, AllocationPlacement::Top)?;
                let arc = Arc::new(alloc);
                self.layers[canonical_layer]
                    .base_class_backings
                    .insert(class, Arc::clone(&arc));
                arc
            }
        };
        Ok(GpuBaseFieldPoly::from_arc(backing, offset, stride))
    }

    /// Extension-field analogue of `allocate_base_view`.
    pub(crate) fn allocate_ext_view(
        &mut self,
        layer: usize,
        address: GKRAddress,
        context: &ProverContext,
    ) -> CudaResult<GpuExtensionFieldPoly<E>>
    where
        E: 'static,
    {
        let layout = self
            .layout
            .as_ref()
            .expect("storage layout required for allocate_ext_view")
            .clone();
        let (canonical_layer, class, field, poly_idx) = layout
            .lookup(layer, &address)
            .unwrap_or_else(|| panic!("address {address:?} missing from layer {layer} layout"));
        assert_eq!(
            field,
            FieldType::Ext,
            "address {address:?} is not classified as an extension poly in layout"
        );
        let layer_layout = layout
            .layers
            .get(canonical_layer)
            .unwrap_or_else(|| panic!("canonical layer {canonical_layer} out of range in layout"));

        if canonical_layer >= self.layers.len() {
            self.layers
                .resize_with(canonical_layer + 1, GpuGKRLayerSource::default);
        }

        let layer_log2_stride = layer_layout.log2_stride;
        let stride = 1usize << layer_log2_stride;
        let offset = (poly_idx as usize) << layer_log2_stride;
        let backing = match self.layers[canonical_layer].ext_class_backings.get(&class) {
            Some(arc) => Arc::clone(arc),
            None => {
                let count = layer_layout
                    .slot_poly_counts
                    .get(&StorageSlot {
                        class,
                        field: FieldType::Ext,
                    })
                    .copied()
                    .unwrap_or_else(|| {
                        panic!("layout missing slot count for layer {canonical_layer} class {class:?} ext")
                    });
                assert!(count > 0);
                let total_size = (count as usize) << layer_log2_stride;
                let alloc = context.alloc(total_size, AllocationPlacement::Top)?;
                let arc = Arc::new(alloc);
                self.layers[canonical_layer]
                    .ext_class_backings
                    .insert(class, Arc::clone(&arc));
                arc
            }
        };
        Ok(GpuExtensionFieldPoly::from_arc(backing, offset, stride))
    }
}

impl<B: 'static, E: Field> GpuGKRStorage<B, E> {
    /// Pre-allocate the per-(layer, AddressClass) ext-intermediate-folding
    /// backings for a layer. Called once per layer at the start of
    /// dim-reducing prep, before any `prepare_for_sumcheck_round_*` call.
    ///
    /// `addresses` is the set of `GKRAddress`es that will be passed as
    /// `inputs_in_extension` to dim-reducing rounds at this layer (union over
    /// all blueprints, placeholders excluded). The storage layout
    /// (`Self::layout`) determines each address's `(class, poly_idx)`; this
    /// method allocates one Arc per class, sized = `class_poly_count *
    /// per_poly_size`, and the poly's offset within its class's Arc is
    /// `poly_idx * per_poly_size` — aligned with `ext_class_backings` so a u16
    /// source descriptor's poly_idx round-trips between the two for the
    /// round-1 dual-source-record cache half.
    ///
    /// Phase A2 covers tower layers via `from_artifact_with_tower`, so the
    /// caller can rely on every dim-reducing input address (artifact or tower)
    /// resolving through the layout. The only no-op path is "no layout set",
    /// which is restricted to test code.
    pub(crate) fn register_dim_reducing_inputs_for_layer(
        &mut self,
        layer: usize,
        addresses: &std::collections::BTreeSet<GKRAddress>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        if addresses.is_empty() {
            return Ok(());
        }
        let layout = match self.layout.as_ref() {
            Some(l) => l.clone(),
            None => return Ok(()),
        };
        let n_layers = self.layers.len();
        let layer_storage = self.layers.get_mut(layer).unwrap_or_else(|| {
            panic!(
                "register_dim_reducing_inputs_for_layer called for layer {layer} but storage has only {n_layers} layers"
            )
        });
        if layer_storage.intermediate_folding_consolidated.is_some() {
            // Single call site (`prepare_layer_from_blueprints`) — bail loudly
            // on a second call rather than silently merging or reallocating.
            panic!(
                "register_dim_reducing_inputs_for_layer called twice for layer {layer}; the prep flow must call it exactly once per layer",
            );
        }

        // Group addresses by class via the storage layout, validate uniform
        // per-poly size, and confirm all are ext-typed.
        let mut addrs_by_class: BTreeMap<AddressClass, Vec<GKRAddress>> = BTreeMap::new();
        let mut per_poly_size: Option<usize> = None;
        for addr in addresses.iter() {
            let (_canonical_layer, class, field, _poly_idx) =
                layout.lookup(layer, addr).unwrap_or_else(|| {
                    panic!(
                        "dim-reducing input {addr:?} missing from storage layout at layer {layer}"
                    )
                });
            assert_eq!(
                field,
                FieldType::Ext,
                "dim-reducing input {addr:?} must be ext-typed (got {field:?})",
            );
            addrs_by_class.entry(class).or_default().push(*addr);
            let len = layer_storage
                .extension_field_inputs
                .get(addr)
                .unwrap_or_else(|| {
                    panic!("dim-reducing input {addr:?} missing from ext storage at layer {layer}")
                })
                .len();
            match per_poly_size {
                None => per_poly_size = Some(len),
                Some(p) => assert_eq!(
                    len, p,
                    "dim-reducing inputs at layer {layer} have non-uniform sizes (first={p}, {addr:?}={len}); consolidation requires uniform per-poly size",
                ),
            }
        }
        let per_poly_size = per_poly_size.expect("non-empty addresses verified above");
        assert!(
            per_poly_size.is_power_of_two() && per_poly_size > 2,
            "per_poly_size {per_poly_size} must be a power of two greater than 2"
        );

        // Allocate one backing per class, sized to mirror ext_class_backings'
        // capacity for that class. poly_idx within the backing is the same as
        // the layout's per-class poly_idx — wasted slots for non-dim-reducing
        // polys are bounded by the audit's GKR_MAX_POLYS_PER_SLOT ceiling.
        let mut per_class = BTreeMap::new();
        let mut poly_index = BTreeMap::new();
        for (class, addrs) in addrs_by_class {
            let count = addrs.len();
            assert!(
                count > 0,
                "class {class:?} ext poly count must be positive at layer {layer}"
            );
            let total_size = count * per_poly_size;
            let backing = Arc::new(context.alloc::<E>(total_size, AllocationPlacement::Top)?);
            per_class.insert(class, backing);
            for (idx, addr) in addrs.into_iter().enumerate() {
                assert!(
                    idx <= u16::MAX as usize,
                    "ext cache poly index {idx} exceeds u16"
                );
                poly_index.insert(addr, idx as u16);
            }
        }
        layer_storage.intermediate_folding_consolidated = Some(ConsolidatedFoldingBacking {
            per_class,
            poly_index,
            per_poly_size,
        });
        Ok(())
    }

    /// Pre-allocate per-(layer, AddressClass) consolidated folding backings
    /// for the main-layer flat path's base-field input set
    /// (Phase A2-flat-base). Mirrors `register_dim_reducing_inputs_for_layer`
    /// but operates on base-field addresses.
    ///
    /// `addresses` includes both real and virtual base-field inputs. Real
    /// inputs route through the layout's per-class index. `VirtualSetup`
    /// polys have no layout slot — they get a separate per-class Arc
    /// (`virtual_per_class`), with a deterministic poly_idx assignment
    /// (`virtual_index`). After this call, every base address in the set
    /// has a consolidated cache slot pre-allocated; subsequent
    /// `materialize_base_folding_buffer` calls slice views into it.
    pub(crate) fn register_flat_base_folding_for_layer(
        &mut self,
        layer: usize,
        addresses: &std::collections::BTreeSet<GKRAddress>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        if addresses.is_empty() {
            return Ok(());
        }
        let layout = match self.layout.as_ref() {
            Some(l) => l.clone(),
            None => return Ok(()),
        };
        let n_layers = self.layers.len();
        let layer_storage = self.layers.get_mut(layer).unwrap_or_else(|| {
            panic!(
                "register_flat_base_folding_for_layer called for layer {layer} but storage has only {n_layers} layers"
            )
        });
        if layer_storage
            .intermediate_base_folding_consolidated
            .is_some()
        {
            // Single call site (`prepare_layer_from_blueprints`) — bail loudly
            // on a second call rather than silently merging or reallocating.
            panic!(
                "register_flat_base_folding_for_layer called twice for layer {layer}; the prep flow must call it exactly once per layer",
            );
        }

        // Walk addresses, splitting into real (layout-indexed) and virtual
        // (`VirtualSetup`) sets. Validate uniform per-poly size for real polys
        // (they're tracked in `base_field_inputs`); for virtuals, fall back to
        // the layer's `base_trace_len` proxy since they have no real backing.
        let mut addrs_by_class: BTreeMap<AddressClass, Vec<GKRAddress>> = BTreeMap::new();
        let mut per_poly_size: Option<usize> = None;
        let mut virtuals_by_class: BTreeMap<AddressClass, Vec<GKRAddress>> = BTreeMap::new();
        for addr in addresses.iter() {
            if matches!(addr, GKRAddress::VirtualSetup(_)) {
                let class = match addr {
                    GKRAddress::VirtualSetup(_) => AddressClass::Setup,
                    _ => unreachable!(),
                };
                virtuals_by_class.entry(class).or_default().push(*addr);
                continue;
            }
            let (_canonical_layer, class, field, _poly_idx) = layout
                .lookup(layer, addr)
                .unwrap_or_else(|| {
                    panic!(
                        "flat base-folding input {addr:?} missing from storage layout at layer {layer}"
                    )
                });
            assert_eq!(
                field,
                FieldType::Base,
                "flat base-folding input {addr:?} must be base-typed (got {field:?})",
            );
            addrs_by_class.entry(class).or_default().push(*addr);
            let len = layer_storage
                .base_field_inputs
                .get(addr)
                .unwrap_or_else(|| {
                    panic!(
                        "flat base-folding input {addr:?} missing from base storage at layer {layer}"
                    )
                })
                .len();
            match per_poly_size {
                None => per_poly_size = Some(len),
                Some(p) => assert_eq!(
                    len, p,
                    "flat base-folding inputs at layer {layer} have non-uniform sizes (first={p}, {addr:?}={len}); consolidation requires uniform per-poly size",
                ),
            }
        }
        // If only virtuals were present we still need a per-poly size; use
        // `base_trace_len` (matches the legacy per-poly path's allocation).
        let base_poly_size = match per_poly_size {
            Some(p) => p,
            None => self.base_trace_len(),
        };
        assert!(
            base_poly_size.is_power_of_two() && base_poly_size > 4,
            "base_poly_size {base_poly_size} must be a power of two greater than 4"
        );
        let cache_per_poly_size = base_poly_size / 2;

        let layer_storage = self.layers.get_mut(layer).expect("checked above");

        // Real-poly backings: one Arc per class, sized to the layout's class
        // count. poly_idx within the Arc matches the layout's per-class
        // poly_idx (mirrors `base_class_backings`), so the kernel-side
        // resolver can recover both the read source and the cache view
        // through the same index value.
        let mut per_class = BTreeMap::new();
        let mut real_index = BTreeMap::new();
        for (class, addrs) in addrs_by_class {
            let count = addrs.len();
            assert!(
                count > 0,
                "class {class:?} base poly count must be positive at layer {layer}"
            );
            let total_size = count * cache_per_poly_size;
            let backing = Arc::new(context.alloc::<E>(total_size, AllocationPlacement::Top)?);
            per_class.insert(class, backing);
            for (idx, addr) in addrs.into_iter().enumerate() {
                assert!(
                    idx <= u16::MAX as usize,
                    "base cache poly index {idx} exceeds u16"
                );
                real_index.insert(addr, idx as u16);
            }
        }

        // Virtual-poly backings: one Arc per class with virtuals, sized to
        // the count of distinct virtual addresses at that class. Sequential
        // poly_idx per class.
        let mut virtual_per_class: BTreeMap<AddressClass, Arc<DeviceAllocation<E>>> =
            BTreeMap::new();
        let mut virtual_index: BTreeMap<GKRAddress, u16> = BTreeMap::new();
        for (class, addrs) in virtuals_by_class {
            let count = addrs.len();
            let total_size = count * cache_per_poly_size;
            let backing = Arc::new(context.alloc::<E>(total_size, AllocationPlacement::Top)?);
            virtual_per_class.insert(class, backing);
            for (idx, addr) in addrs.into_iter().enumerate() {
                assert!(
                    idx <= u16::MAX as usize,
                    "virtual poly index {idx} exceeds u16 range",
                );
                virtual_index.insert(addr, idx as u16);
            }
        }

        layer_storage.intermediate_base_folding_consolidated =
            Some(ConsolidatedBaseFoldingBacking {
                per_class,
                real_index,
                virtual_per_class,
                virtual_index,
                per_poly_size: cache_per_poly_size,
            });
        Ok(())
    }

    fn round_input_layer(address: GKRAddress) -> usize {
        match address {
            GKRAddress::ScratchSpace(..) => unreachable!(),
            GKRAddress::Cached { layer, .. } => layer,
            GKRAddress::InnerLayer { layer, .. } => layer,
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..) => 0,
        }
    }

    fn round_output_layer(address: GKRAddress) -> usize {
        match address {
            GKRAddress::ScratchSpace(..)
            | GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..) => unreachable!(),
            GKRAddress::Cached { .. } => unreachable!(),
            GKRAddress::InnerLayer { layer, .. } => layer,
        }
    }

    /// Materialize the per-poly base-field folding buffer for `poly` at
    /// `layer`. Slices a view into the per-(layer, AddressClass) consolidated
    /// backing when `register_flat_base_folding_for_layer` has run for this
    /// layer. Layout-indexed (real) addresses use `per_class`;
    /// `VirtualSetup` polys use `virtual_per_class` keyed by
    /// `virtual_index[poly]`. Falls back to a fresh per-poly Arc if no
    /// consolidated backing exists for this layer (test-only path).
    fn materialize_base_folding_buffer(
        &self,
        layer: usize,
        poly: GKRAddress,
        base_poly_len: usize,
        context: &ProverContext,
    ) -> CudaResult<GpuBaseFieldPolyIntermediateFoldingStorage<E>> {
        if let Some(consolidated) = self.layers[layer]
            .intermediate_base_folding_consolidated
            .as_ref()
        {
            let cache_per_poly_size = base_poly_len / 2;
            assert_eq!(
                consolidated.per_poly_size, cache_per_poly_size,
                "consolidated base-folding backing per-poly size {} mismatches required cache size {} at layer {layer}",
                consolidated.per_poly_size, cache_per_poly_size,
            );
            // Real (layout-indexed) addresses route through `per_class`.
            if let Some(layout) = self.layout.as_ref() {
                if let Some((_canonical_layer, class, _field, _poly_idx_in_class)) =
                    layout.lookup(layer, &poly)
                {
                    if let Some(backing) = consolidated.per_class.get(&class) {
                        let cache_idx = consolidated.real_index.get(&poly).copied().unwrap_or_else(|| {
                            panic!(
                                "consolidated base-folding missing dense cache index for {poly:?} at layer {layer}"
                            )
                        });
                        let offset = cache_idx as usize * consolidated.per_poly_size;
                        return Ok(GpuBaseFieldPolyIntermediateFoldingStorage::from_arc(
                            Arc::clone(backing),
                            offset,
                            base_poly_len,
                        ));
                    }
                }
            }
            // Virtual addresses: look up the virtual poly_idx, then slice into
            // `virtual_per_class[class]`.
            if let Some(&virt_poly_idx) = consolidated.virtual_index.get(&poly) {
                let class = match poly {
                    GKRAddress::VirtualSetup(_) => AddressClass::Setup,
                    _ => panic!(
                        "consolidated base-folding virtual_index has non-VirtualSetup entry {poly:?} at layer {layer}"
                    ),
                };
                let backing = consolidated.virtual_per_class.get(&class).unwrap_or_else(|| {
                    panic!(
                        "consolidated base-folding has virtual_index for {poly:?} but no Arc for class {class:?} at layer {layer}"
                    )
                });
                let offset = virt_poly_idx as usize * consolidated.per_poly_size;
                return Ok(GpuBaseFieldPolyIntermediateFoldingStorage::from_arc(
                    Arc::clone(backing),
                    offset,
                    base_poly_len,
                ));
            }
            // Address not registered for consolidation at this layer (e.g.
            // a virtual poly that wasn't in the blueprint set passed to
            // `register_flat_base_folding_for_layer`). Fall through to the
            // per-poly lazy path. This shouldn't happen in production paths
            // — production callers pass the full input set to register —
            // but the test/unit paths still rely on it.
        }
        GpuBaseFieldPolyIntermediateFoldingStorage::new_for_base_poly_size(base_poly_len, context)
    }

    fn plan_base_source_for_round_1(
        &mut self,
        poly: GKRAddress,
        context: &ProverContext,
    ) -> CudaResult<GpuBaseFieldPolySourceAfterOneFoldingPlan<B, E>> {
        let layer = Self::base_poly_layer(poly).expect("must exist");
        let sumcheck_step = 1;
        let (base_poly_len, base_poly_ptr, source_kind) =
            if let Some(source_kind) = GpuBaseFieldSourceKind::from_address(poly) {
                (self.base_trace_len(), null(), source_kind)
            } else {
                let poly = self.get_base_poly_for_address(poly).expect("must exist");
                (poly.len(), poly.as_ptr(), GpuBaseFieldSourceKind::Real)
            };

        if !self.layers[layer]
            .intermediate_storage_for_folder_base_field_inputs
            .contains_key(&poly)
        {
            let buffer =
                self.materialize_base_folding_buffer(layer, poly, base_poly_len, context)?;
            self.layers[layer]
                .intermediate_storage_for_folder_base_field_inputs
                .insert(poly, (0, buffer));
        }

        let (last_used_for_layer, buffer) = self.layers[layer]
            .intermediate_storage_for_folder_base_field_inputs
            .get_mut(&poly)
            .expect("must be present");
        let this_layer_start = buffer.initial_pointer();
        let first_access = if *last_used_for_layer >= sumcheck_step {
            false
        } else {
            *last_used_for_layer = sumcheck_step;
            true
        };

        Ok(GpuBaseFieldPolySourceAfterOneFoldingPlan {
            base_layer_half_size: base_poly_len / 2,
            next_layer_size: base_poly_len / 4,
            base_input_start: base_poly_ptr,
            this_layer_cache_start: this_layer_start,
            first_access,
            source_kind,
        })
    }

    fn plan_base_source_for_round_2(
        &mut self,
        poly: GKRAddress,
        context: &ProverContext,
    ) -> CudaResult<GpuBaseFieldPolySourceAfterTwoFoldingsPlan<B, E>> {
        let layer = Self::base_poly_layer(poly).expect("must exist");
        let sumcheck_step = 2;
        let (base_poly_len, base_poly_ptr, source_kind) =
            if let Some(source_kind) = GpuBaseFieldSourceKind::from_address(poly) {
                (self.base_trace_len(), null(), source_kind)
            } else {
                let poly = self.get_base_poly_for_address(poly).expect("must exist");
                (poly.len(), poly.as_ptr(), GpuBaseFieldSourceKind::Real)
            };

        if !self.layers[layer]
            .intermediate_storage_for_folder_base_field_inputs
            .contains_key(&poly)
        {
            let buffer =
                self.materialize_base_folding_buffer(layer, poly, base_poly_len, context)?;
            self.layers[layer]
                .intermediate_storage_for_folder_base_field_inputs
                .insert(poly, (1, buffer));
        }

        let (last_used_for_layer, buffer) = self.layers[layer]
            .intermediate_storage_for_folder_base_field_inputs
            .get_mut(&poly)
            .expect("must be present");
        assert!(
            *last_used_for_layer >= sumcheck_step - 1,
            "base folding storage for {:?} advanced only through step {}, but step {} was requested",
            poly,
            *last_used_for_layer,
            sumcheck_step
        );
        let this_layer_start = buffer.initial_pointer();

        let first_access = if *last_used_for_layer >= sumcheck_step {
            false
        } else {
            *last_used_for_layer = sumcheck_step;
            true
        };

        Ok(GpuBaseFieldPolySourceAfterTwoFoldingsPlan {
            base_input_start: base_poly_ptr,
            this_layer_cache_start: this_layer_start,
            base_layer_half_size: base_poly_len / 2,
            base_quarter_size: base_poly_len / 4,
            next_layer_size: base_poly_len / 8,
            first_access,
            source_kind,
        })
    }

    fn plan_base_source_for_rounds_3_and_beyond(
        &mut self,
        poly: GKRAddress,
        sumcheck_step: usize,
    ) -> GpuExtensionFieldPolyContinuingSourcePlan<E> {
        assert!(sumcheck_step >= 3);

        let layer = Self::base_poly_layer(poly).expect("must be present");
        let (last_used_for_layer, buffer) = self.layers[layer]
            .intermediate_storage_for_folder_base_field_inputs
            .get_mut(&poly)
            .expect("must be present");
        assert!(
            *last_used_for_layer >= sumcheck_step - 1,
            "base folding storage for {:?} advanced only through step {}, but step {} was requested",
            poly,
            *last_used_for_layer,
            sumcheck_step
        );
        let (previous_layer_start, this_layer_start) =
            buffer.pointers_for_sumcheck_accessor_step(sumcheck_step);
        let this_layer_size = buffer.size_after_two_folds >> (sumcheck_step - 2);
        let next_layer_size = this_layer_size / 2;

        let first_access = if *last_used_for_layer >= sumcheck_step {
            false
        } else {
            *last_used_for_layer = sumcheck_step;
            true
        };

        GpuExtensionFieldPolyContinuingSourcePlan {
            previous_layer_start,
            this_layer_start,
            this_layer_size,
            next_layer_size,
            first_access,
        }
    }

    fn plan_ext_source_for_rounds_1_and_beyond(
        &mut self,
        poly: GKRAddress,
        sumcheck_step: usize,
        context: &ProverContext,
    ) -> CudaResult<GpuExtensionFieldPolyContinuingSourcePlan<E>> {
        assert!(sumcheck_step >= 1);

        let layer = Self::ext_poly_layer(poly).expect("must be present");

        if sumcheck_step == 1
            && !self.layers[layer]
                .intermediate_storage_for_folder_extension_field_inputs
                .contains_key(&poly)
        {
            let poly_ref = self.layers[layer]
                .extension_field_inputs
                .get(&poly)
                .expect("must be present");
            let size = poly_ref.len();
            let input_pointer = poly_ref.as_ptr();
            let mut buffer = if self.layers[layer]
                .intermediate_folding_consolidated
                .is_some()
            {
                let layout = self
                    .layout
                    .as_ref()
                    .expect("storage layout required for consolidated folding lookup")
                    .clone();
                let (_canonical_layer, class, _field, _poly_idx_in_class) = layout
                    .lookup(layer, &poly)
                    .unwrap_or_else(|| {
                        panic!(
                            "dim-reducing input {poly:?} missing from storage layout at layer {layer}"
                        )
                    });
                let consolidated = self.layers[layer]
                    .intermediate_folding_consolidated
                    .as_ref()
                    .expect("checked above");
                assert_eq!(
                    consolidated.per_poly_size, size,
                    "consolidated folding backing per-poly size {} mismatches input poly len {} at layer {layer}",
                    consolidated.per_poly_size, size,
                );
                let backing = consolidated.per_class.get(&class).unwrap_or_else(|| {
                    panic!(
                        "dim-reducing input {poly:?} class {class:?} missing from consolidated folding backing at layer {layer}"
                    )
                });
                let cache_idx = consolidated
                    .poly_index
                    .get(&poly)
                    .copied()
                    .unwrap_or_else(|| {
                        panic!(
                        "dim-reducing input {poly:?} missing dense cache index at layer {layer}"
                    )
                    });
                let offset = cache_idx as usize * consolidated.per_poly_size;
                GpuExtensionFieldPolyIntermediateFoldingStorage::from_arc(
                    Arc::clone(backing),
                    offset,
                    size,
                )
            } else {
                GpuExtensionFieldPolyIntermediateFoldingStorage::new_for_extension_poly_size(
                    size, context,
                )?
            };
            let buffer_pointer = buffer.pointer_for_sumcheck_after_one_fold();

            self.layers[layer]
                .intermediate_storage_for_folder_extension_field_inputs
                .insert(poly, (1, buffer));

            Ok(GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start: input_pointer,
                this_layer_start: buffer_pointer,
                this_layer_size: size / 2,
                next_layer_size: size / 4,
                first_access: true,
            })
        } else {
            let (last_used_for_layer, buffer) = self.layers[layer]
                .intermediate_storage_for_folder_extension_field_inputs
                .get_mut(&poly)
                .expect("must be present");
            assert!(
                *last_used_for_layer >= sumcheck_step - 1,
                "extension folding storage for {:?} advanced only through step {}, but step {} was requested",
                poly,
                *last_used_for_layer,
                sumcheck_step
            );
            let (previous_layer_start, this_layer_start) =
                buffer.pointer_for_sumcheck_continuation(sumcheck_step);
            let this_layer_size = buffer.size_after_one_fold >> (sumcheck_step - 1);
            let next_layer_size = this_layer_size / 2;

            let first_access = if *last_used_for_layer >= sumcheck_step {
                false
            } else {
                *last_used_for_layer = sumcheck_step;
                true
            };

            Ok(GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start,
                this_layer_start,
                this_layer_size,
                next_layer_size,
                first_access,
            })
        }
    }

    pub(crate) fn get_for_sumcheck_round_0(
        &self,
        inputs: &GKRInputs,
    ) -> GpuSumcheckRound0LaunchDescriptors<B, E> {
        let mut storage = GpuSumcheckRound0LaunchDescriptors::default();

        for input in inputs.inputs_in_base.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .base_field_inputs
                    .push(GpuBaseFieldPolySource::empty());
            } else {
                storage
                    .base_field_inputs
                    .push(self.get_base_source_for_round_0(*input));
            }
        }

        for input in inputs.inputs_in_extension.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .extension_field_inputs
                    .push(GpuExtensionFieldPolyInitialSource::empty());
            } else {
                let layer = Self::round_input_layer(*input);
                let source = self.layers[layer]
                    .extension_field_inputs
                    .get(input)
                    .unwrap_or_else(|| {
                        panic!(
                            "Polynomial with address {:?} is missing from input sources for extension field polys",
                            input
                        )
                    });
                storage.extension_field_inputs.push(source.accessor());
            }
        }

        for output in inputs.outputs_in_base.iter() {
            if *output == GKRAddress::placeholder() {
                storage
                    .base_field_outputs
                    .push(GpuBaseFieldPolySource::empty());
            } else {
                let layer = Self::round_output_layer(*output);
                let source = self.layers[layer]
                    .base_field_inputs
                    .get(output)
                    .unwrap_or_else(|| {
                        panic!(
                            "Polynomial with address {:?} is missing from output sources for base field polys",
                            output
                        )
                    });
                storage.base_field_outputs.push(source.accessor());
            }
        }

        for output in inputs.outputs_in_extension.iter() {
            if *output == GKRAddress::placeholder() {
                storage
                    .extension_field_outputs
                    .push(GpuExtensionFieldPolyInitialSource::empty());
            } else {
                let layer = Self::round_output_layer(*output);
                let source = self.layers[layer]
                    .extension_field_inputs
                    .get(output)
                    .unwrap_or_else(|| {
                        panic!(
                            "Polynomial with address {:?} is missing from output sources for extension field polys",
                            output
                        )
                    });
                storage.extension_field_outputs.push(source.accessor());
            }
        }

        storage
    }

    pub(crate) fn schedule_upload_for_sumcheck_round_0(
        &self,
        inputs: &GKRInputs,
        context: &ProverContext,
    ) -> CudaResult<GpuSumcheckRound0ScheduledLaunchDescriptors<B, E>> {
        let host_values = self.get_for_sumcheck_round_0(inputs);
        let mut callbacks = Callbacks::new();
        let host = GpuSumcheckRound0HostLaunchDescriptors {
            base_field_inputs: alloc_host_and_schedule_copy(
                context,
                &mut callbacks,
                host_values.base_field_inputs,
            ),
            extension_field_inputs: alloc_host_and_schedule_copy(
                context,
                &mut callbacks,
                host_values.extension_field_inputs,
            ),
            base_field_outputs: alloc_host_and_schedule_copy(
                context,
                &mut callbacks,
                host_values.base_field_outputs,
            ),
            extension_field_outputs: alloc_host_and_schedule_copy(
                context,
                &mut callbacks,
                host_values.extension_field_outputs,
            ),
        };
        let device = GpuSumcheckRound0DeviceLaunchDescriptors {
            base_field_inputs: alloc_device_and_schedule_upload(context, &host.base_field_inputs)?,
            extension_field_inputs: alloc_device_and_schedule_upload(
                context,
                &host.extension_field_inputs,
            )?,
            base_field_outputs: alloc_device_and_schedule_upload(
                context,
                &host.base_field_outputs,
            )?,
            extension_field_outputs: alloc_device_and_schedule_upload(
                context,
                &host.extension_field_outputs,
            )?,
        };

        Ok(GpuSumcheckRound0ScheduledLaunchDescriptors {
            callbacks,
            #[cfg(test)]
            host,
            device,
        })
    }

    pub(crate) fn prepare_for_sumcheck_round_1(
        &mut self,
        inputs: &GKRInputs,
        context: &ProverContext,
    ) -> CudaResult<GpuSumcheckRound1PreparedStorage<B, E>> {
        let mut storage = GpuSumcheckRound1PreparedStorage {
            base_field_inputs: Vec::new(),
            extension_field_inputs: Vec::new(),
            sumcheck_step: 1,
        };
        for input in inputs.inputs_in_base.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .base_field_inputs
                    .push(GpuBaseFieldPolySourceAfterOneFoldingPlan::empty());
            } else {
                storage
                    .base_field_inputs
                    .push(self.plan_base_source_for_round_1(*input, context)?);
            }
        }
        for input in inputs.inputs_in_extension.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .extension_field_inputs
                    .push(GpuExtensionFieldPolyContinuingSourcePlan::empty());
            } else {
                storage
                    .extension_field_inputs
                    .push(self.plan_ext_source_for_rounds_1_and_beyond(*input, 1, context)?);
            }
        }

        Ok(storage)
    }

    pub(crate) fn prepare_for_sumcheck_round_2(
        &mut self,
        inputs: &GKRInputs,
        context: &ProverContext,
    ) -> CudaResult<GpuSumcheckRound2PreparedStorage<B, E>> {
        let mut storage = GpuSumcheckRound2PreparedStorage {
            base_field_inputs: Vec::new(),
            extension_field_inputs: Vec::new(),
            sumcheck_step: 2,
        };
        for input in inputs.inputs_in_base.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .base_field_inputs
                    .push(GpuBaseFieldPolySourceAfterTwoFoldingsPlan::empty());
            } else {
                storage
                    .base_field_inputs
                    .push(self.plan_base_source_for_round_2(*input, context)?);
            }
        }
        for input in inputs.inputs_in_extension.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .extension_field_inputs
                    .push(GpuExtensionFieldPolyContinuingSourcePlan::empty());
            } else {
                storage
                    .extension_field_inputs
                    .push(self.plan_ext_source_for_rounds_1_and_beyond(*input, 2, context)?);
            }
        }

        Ok(storage)
    }

    pub(crate) fn prepare_for_sumcheck_round_3_and_beyond(
        &mut self,
        inputs: &GKRInputs,
        sumcheck_step: usize,
        context: &ProverContext,
    ) -> CudaResult<GpuSumcheckRound3AndBeyondPreparedStorage<E>> {
        assert!(sumcheck_step >= 3);

        let mut storage = GpuSumcheckRound3AndBeyondPreparedStorage {
            base_field_inputs: Vec::new(),
            extension_field_inputs: Vec::new(),
            sumcheck_step,
        };
        for input in inputs.inputs_in_base.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .base_field_inputs
                    .push(GpuExtensionFieldPolyContinuingSourcePlan::empty());
            } else {
                storage
                    .base_field_inputs
                    .push(self.plan_base_source_for_rounds_3_and_beyond(*input, sumcheck_step));
            }
        }
        for input in inputs.inputs_in_extension.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .extension_field_inputs
                    .push(GpuExtensionFieldPolyContinuingSourcePlan::empty());
            } else {
                storage
                    .extension_field_inputs
                    .push(self.plan_ext_source_for_rounds_1_and_beyond(
                        *input,
                        sumcheck_step,
                        context,
                    )?);
            }
        }

        Ok(storage)
    }
}

impl<B: 'static, E: Field + 'static> GpuSumcheckRound1PreparedStorage<B, E> {
    pub(crate) fn build_launch_descriptors(&self) -> GpuSumcheckRound1HostLaunchDescriptors<B, E> {
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

    pub(crate) fn schedule_upload_launch_descriptors(
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

impl<B: 'static, E: Field + 'static> GpuSumcheckRound2PreparedStorage<B, E> {
    pub(crate) fn build_launch_descriptors(&self) -> GpuSumcheckRound2HostLaunchDescriptors<B, E> {
        let base_field_inputs = self
            .base_field_inputs
            .iter()
            .map(
                |plan| GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor {
                    base_input_start: plan.base_input_start,
                    this_layer_cache_start: plan.this_layer_cache_start,
                    base_layer_half_size: plan.base_layer_half_size,
                    base_quarter_size: plan.base_quarter_size,
                    next_layer_size: plan.next_layer_size,
                    first_access: plan.first_access,
                    source_kind: plan.source_kind,
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
        GpuSumcheckRound2HostLaunchDescriptors {
            base_field_inputs,
            extension_field_inputs,
        }
    }

    pub(crate) fn schedule_upload_launch_descriptors(
        &self,
        context: &ProverContext,
        callbacks: &mut Callbacks<'static>,
    ) -> CudaResult<GpuSumcheckRound2ScheduledLaunchDescriptors<B, E>> {
        let descriptors = self.build_launch_descriptors();
        let host_base =
            alloc_host_and_schedule_copy(context, callbacks, descriptors.base_field_inputs);
        let base_field_inputs_device = alloc_device_and_schedule_upload(context, &host_base)?;
        drop(host_base);
        let host_ext =
            alloc_host_and_schedule_copy(context, callbacks, descriptors.extension_field_inputs);
        let extension_field_inputs_device = alloc_device_and_schedule_upload(context, &host_ext)?;
        drop(host_ext);
        let device = GpuSumcheckRound2DeviceLaunchDescriptors {
            base_field_inputs: base_field_inputs_device,
            extension_field_inputs: extension_field_inputs_device,
        };
        Ok(GpuSumcheckRound2ScheduledLaunchDescriptors { device })
    }
}

impl<E: Field + 'static> GpuSumcheckRound3AndBeyondPreparedStorage<E> {
    pub(crate) fn build_launch_descriptors(
        &self,
    ) -> GpuSumcheckRound3AndBeyondHostLaunchDescriptors<E> {
        let base_field_inputs = self
            .base_field_inputs
            .iter()
            .map(|plan| GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: plan.previous_layer_start,
                this_layer_start: plan.this_layer_start,
                this_layer_size: plan.this_layer_size,
                next_layer_size: plan.next_layer_size,
                first_access: plan.first_access,
            })
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
        GpuSumcheckRound3AndBeyondHostLaunchDescriptors {
            base_field_inputs,
            extension_field_inputs,
        }
    }

    pub(crate) fn schedule_upload_launch_descriptors(
        &self,
        context: &ProverContext,
        callbacks: &mut Callbacks<'static>,
    ) -> CudaResult<GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors<E>> {
        let descriptors = self.build_launch_descriptors();
        let host_base =
            alloc_host_and_schedule_copy(context, callbacks, descriptors.base_field_inputs);
        let base_field_inputs_device = alloc_device_and_schedule_upload(context, &host_base)?;
        drop(host_base);
        let host_ext =
            alloc_host_and_schedule_copy(context, callbacks, descriptors.extension_field_inputs);
        let extension_field_inputs_device = alloc_device_and_schedule_upload(context, &host_ext)?;
        drop(host_ext);
        let device = GpuSumcheckRound3AndBeyondDeviceLaunchDescriptors {
            base_field_inputs: base_field_inputs_device,
            extension_field_inputs: extension_field_inputs_device,
        };
        Ok(GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors { device })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::allocator::tracker::AllocationPlacement;
    use crate::primitives::callbacks::Callbacks;
    use crate::primitives::field::{BF, E4};
    use crate::prover::test_utils::make_test_context;
    use cs::definitions::VirtualSetupPoly;
    use era_cudart::memory::memory_copy_async;
    use serial_test::serial;

    fn alloc_and_copy<T: Copy>(context: &ProverContext, values: &[T]) -> DeviceAllocation<T> {
        let mut allocation = context
            .alloc(values.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy_async(&mut allocation, values, context.get_exec_stream()).unwrap();
        allocation
    }

    fn copy_device_values<T: Copy>(
        context: &ProverContext,
        values: &DeviceAllocation<T>,
    ) -> Vec<T> {
        let mut allocation = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy_async(&mut allocation, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        unsafe { allocation.get_accessor().get().to_vec() }
    }

    fn sample_ext(seed: u32) -> E4 {
        E4::from_array_of_base([
            BF::new(seed),
            BF::new(seed + 1),
            BF::new(seed + 2),
            BF::new(seed + 3),
        ])
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn insert_get_try_get_and_purge_match_cpu_semantics() {
        let context = make_test_context(64, 8);
        let mut storage = GpuGKRStorage::<BF, E4>::default();

        let base_memory = GpuBaseFieldPoly::new(alloc_and_copy(
            &context,
            &(0..8).map(|i| BF::new(i as u32 + 1)).collect::<Vec<_>>(),
        ));
        let base_setup = GpuBaseFieldPoly::new(alloc_and_copy(
            &context,
            &(10..18).map(|i| BF::new(i as u32)).collect::<Vec<_>>(),
        ));
        let ext_inner = GpuExtensionFieldPoly::new(alloc_and_copy(
            &context,
            &(0..8)
                .map(|i| sample_ext(i as u32 + 20))
                .collect::<Vec<_>>(),
        ));

        let base_memory_ptr = base_memory.as_ptr();
        let base_setup_ptr = base_setup.as_ptr();
        let ext_inner_ptr = ext_inner.as_ptr();

        storage.insert_base_field_at_layer(0, GKRAddress::BaseLayerMemory(0), base_memory);
        storage.insert_base_field_at_layer(0, GKRAddress::Setup(0), base_setup);
        storage.insert_extension_at_layer(
            1,
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 0,
            },
            ext_inner,
        );

        assert_eq!(storage.get_base_layer_mem(0).as_ptr(), base_memory_ptr);
        assert_eq!(
            storage.get_base_layer(GKRAddress::Setup(0)).as_ptr(),
            base_setup_ptr
        );
        assert_eq!(
            storage
                .try_get_base_poly(GKRAddress::BaseLayerMemory(0))
                .unwrap()
                .as_ptr(),
            base_memory_ptr
        );
        assert_eq!(
            storage
                .try_get_ext_poly(GKRAddress::InnerLayer {
                    layer: 1,
                    offset: 0
                })
                .unwrap()
                .as_ptr(),
            ext_inner_ptr
        );
        assert_eq!(
            storage
                .get_ext_poly(GKRAddress::InnerLayer {
                    layer: 1,
                    offset: 0
                })
                .as_ptr(),
            ext_inner_ptr
        );

        storage.purge_up_to_layer(0);
        assert_eq!(storage.layers.len(), 1);
        assert!(storage
            .try_get_ext_poly(GKRAddress::InnerLayer {
                layer: 1,
                offset: 0
            })
            .is_none());
        assert_eq!(storage.get_base_layer_mem(0).as_ptr(), base_memory_ptr);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn shared_views_support_subviews_and_drop_on_last_reference() {
        let context = make_test_context(64, 8);
        let baseline = context.get_used_mem_current();

        let backing = Arc::new(alloc_and_copy(
            &context,
            &(0..16).map(|i| BF::new(i as u32 + 1)).collect::<Vec<_>>(),
        ));

        let col0 = GpuBaseFieldPoly::from_arc(Arc::clone(&backing), 0, 8);
        let col1 = GpuBaseFieldPoly::from_arc(Arc::clone(&backing), 8, 8);
        let col0_copy = col0.clone_shared();

        assert!(col0.shares_backing_with(&col1));
        assert!(col0.shares_backing_with(&col0_copy));
        assert_eq!(col0.offset(), 0);
        assert_eq!(col1.offset(), 8);
        assert_eq!(unsafe { col1.as_ptr().offset_from(col0.as_ptr()) }, 8);

        let mut storage = GpuGKRStorage::<BF, E4>::default();
        storage.insert_base_field_at_layer(0, GKRAddress::BaseLayerMemory(0), col0);
        storage.insert_base_field_at_layer(0, GKRAddress::BaseLayerMemory(1), col1);

        assert!(context.get_used_mem_current() > baseline);

        drop(storage);
        assert!(context.get_used_mem_current() > baseline);

        drop(col0_copy);
        drop(backing);
        assert_eq!(context.get_used_mem_current(), baseline);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn round_builders_allocate_and_reuse_scratch() {
        let context = make_test_context(64, 8);
        let baseline = context.get_used_mem_current();

        let mut storage = GpuGKRStorage::<BF, E4>::default();
        let base_backing = Arc::new(alloc_and_copy(
            &context,
            &(0..16).map(|i| BF::new(i as u32 + 1)).collect::<Vec<_>>(),
        ));
        let ext_values = (0..8)
            .map(|i| sample_ext(i as u32 + 40))
            .collect::<Vec<_>>();
        let ext_poly = GpuExtensionFieldPoly::new(alloc_and_copy(&context, &ext_values));
        let base_input = GpuBaseFieldPoly::from_arc(base_backing, 0, 8);
        let base_output = GpuBaseFieldPoly::new(alloc_and_copy(
            &context,
            &(100..108).map(|i| BF::new(i as u32)).collect::<Vec<_>>(),
        ));
        let ext_output = GpuExtensionFieldPoly::new(alloc_and_copy(
            &context,
            &(0..8)
                .map(|i| sample_ext(i as u32 + 60))
                .collect::<Vec<_>>(),
        ));

        let base_input_ptr = base_input.as_ptr();
        let base_output_ptr = base_output.as_ptr();
        let ext_input_ptr = ext_poly.as_ptr();
        let ext_output_ptr = ext_output.as_ptr();

        storage.insert_base_field_at_layer(0, GKRAddress::BaseLayerMemory(0), base_input);
        storage.insert_base_field_at_layer(
            1,
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 1,
            },
            base_output,
        );
        storage.insert_extension_at_layer(
            1,
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 0,
            },
            ext_poly,
        );
        storage.insert_extension_at_layer(
            1,
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 2,
            },
            ext_output,
        );

        let inputs = GKRInputs {
            inputs_in_base: vec![GKRAddress::BaseLayerMemory(0), GKRAddress::placeholder()],
            inputs_in_extension: vec![
                GKRAddress::InnerLayer {
                    layer: 1,
                    offset: 0,
                },
                GKRAddress::placeholder(),
            ],
            outputs_in_base: vec![
                GKRAddress::InnerLayer {
                    layer: 1,
                    offset: 1,
                },
                GKRAddress::placeholder(),
            ],
            outputs_in_extension: vec![
                GKRAddress::InnerLayer {
                    layer: 1,
                    offset: 2,
                },
                GKRAddress::placeholder(),
            ],
        };

        {
            let round0 = storage
                .schedule_upload_for_sumcheck_round_0(&inputs, &context)
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let round0_base_inputs = copy_device_values(&context, &round0.device.base_field_inputs);
            let round0_base_outputs =
                copy_device_values(&context, &round0.device.base_field_outputs);
            let round0_ext_inputs =
                copy_device_values(&context, &round0.device.extension_field_inputs);
            let round0_ext_outputs =
                copy_device_values(&context, &round0.device.extension_field_outputs);
            assert_eq!(round0_base_inputs[0].start, base_input_ptr);
            assert_eq!(round0_base_outputs[0].start, base_output_ptr);
            assert_eq!(round0_ext_inputs[0].start, ext_input_ptr);
            assert_eq!(round0_ext_outputs[0].start, ext_output_ptr);
            assert!(round0_base_inputs[1].start.is_null());
            assert!(round0_ext_inputs[1].start.is_null());
        }

        let r1 = sample_ext(100);
        {
            let mut callbacks = Callbacks::new();
            let round1 = storage
                .prepare_for_sumcheck_round_1(&inputs, &context)
                .unwrap()
                .schedule_upload_launch_descriptors(&context, &mut callbacks)
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let round1_base_inputs_device =
                copy_device_values(&context, &round1.device.base_field_inputs);
            let round1_ext_inputs_device =
                copy_device_values(&context, &round1.device.extension_field_inputs);
            assert_eq!(
                round1_base_inputs_device[0].base_input_start,
                base_input_ptr
            );
            assert!(round1_base_inputs_device[1].base_input_start.is_null());
            assert_eq!(
                round1_ext_inputs_device[0].previous_layer_start,
                ext_input_ptr
            );
            assert!(round1_ext_inputs_device[0].first_access);
            assert!(round1_ext_inputs_device[1].previous_layer_start.is_null());
        }
        let used_after_round1 = context.get_used_mem_current();
        assert!(used_after_round1 > baseline);

        let r2 = sample_ext(200);
        let (base_round2_cache_ptr, ext_round2_cache_ptr) = {
            let mut callbacks = Callbacks::new();
            let round2_first = storage
                .prepare_for_sumcheck_round_2(&inputs, &context)
                .unwrap()
                .schedule_upload_launch_descriptors(&context, &mut callbacks)
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let round2_first_base_inputs_device =
                copy_device_values(&context, &round2_first.device.base_field_inputs);
            let round2_first_ext_inputs_device =
                copy_device_values(&context, &round2_first.device.extension_field_inputs);
            assert!(round2_first_base_inputs_device[0].first_access);
            assert!(round2_first_ext_inputs_device[0].first_access);
            (
                round2_first_base_inputs_device[0].this_layer_cache_start,
                round2_first_ext_inputs_device[0].this_layer_start,
            )
        };

        {
            let mut callbacks = Callbacks::new();
            let round2_second = storage
                .prepare_for_sumcheck_round_2(&inputs, &context)
                .unwrap()
                .schedule_upload_launch_descriptors(&context, &mut callbacks)
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let round2_second_base_inputs_device =
                copy_device_values(&context, &round2_second.device.base_field_inputs);
            let round2_second_ext_inputs_device =
                copy_device_values(&context, &round2_second.device.extension_field_inputs);
            assert!(!round2_second_base_inputs_device[0].first_access);
            assert!(!round2_second_ext_inputs_device[0].first_access);
            assert_eq!(
                round2_second_base_inputs_device[0].this_layer_cache_start,
                base_round2_cache_ptr
            );
            assert_eq!(
                round2_second_ext_inputs_device[0].this_layer_start,
                ext_round2_cache_ptr
            );
        }

        let r3 = sample_ext(300);
        let (round3_base_cache_ptr, round3_ext_cache_ptr) = {
            let mut callbacks = Callbacks::new();
            let round3_first = storage
                .prepare_for_sumcheck_round_3_and_beyond(&inputs, 3, &context)
                .unwrap()
                .schedule_upload_launch_descriptors(&context, &mut callbacks)
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let round3_first_base_inputs_device =
                copy_device_values(&context, &round3_first.device.base_field_inputs);
            let round3_first_ext_inputs_device =
                copy_device_values(&context, &round3_first.device.extension_field_inputs);
            assert!(round3_first_base_inputs_device[0].first_access);
            assert!(round3_first_ext_inputs_device[0].first_access);
            assert_eq!(
                unsafe {
                    round3_first_base_inputs_device[0]
                        .this_layer_start
                        .offset_from(round3_first_base_inputs_device[0].previous_layer_start)
                },
                2
            );
            assert_eq!(
                unsafe {
                    round3_first_ext_inputs_device[0]
                        .this_layer_start
                        .offset_from(round3_first_ext_inputs_device[0].previous_layer_start)
                },
                1
            );
            assert_eq!(round3_first_base_inputs_device[0].this_layer_size, 1);
            assert_eq!(round3_first_ext_inputs_device[0].this_layer_size, 1);
            (
                round3_first_base_inputs_device[0].this_layer_start,
                round3_first_ext_inputs_device[0].this_layer_start,
            )
        };

        {
            let mut callbacks = Callbacks::new();
            let round3_second = storage
                .prepare_for_sumcheck_round_3_and_beyond(&inputs, 3, &context)
                .unwrap()
                .schedule_upload_launch_descriptors(&context, &mut callbacks)
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let round3_second_base_inputs_device =
                copy_device_values(&context, &round3_second.device.base_field_inputs);
            let round3_second_ext_inputs_device =
                copy_device_values(&context, &round3_second.device.extension_field_inputs);
            assert!(!round3_second_base_inputs_device[0].first_access);
            assert!(!round3_second_ext_inputs_device[0].first_access);
            assert_eq!(
                round3_second_base_inputs_device[0].this_layer_start,
                round3_base_cache_ptr
            );
            assert_eq!(
                round3_second_ext_inputs_device[0].this_layer_start,
                round3_ext_cache_ptr
            );
        }

        {
            let mut callbacks = Callbacks::new();
            let round2_reuse_after_round3 = storage
                .prepare_for_sumcheck_round_2(&inputs, &context)
                .unwrap()
                .schedule_upload_launch_descriptors(&context, &mut callbacks)
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let round2_reuse_base_inputs_device = copy_device_values(
                &context,
                &round2_reuse_after_round3.device.base_field_inputs,
            );
            let round2_reuse_ext_inputs_device = copy_device_values(
                &context,
                &round2_reuse_after_round3.device.extension_field_inputs,
            );
            assert!(!round2_reuse_base_inputs_device[0].first_access);
            assert!(!round2_reuse_ext_inputs_device[0].first_access);
            assert_eq!(
                round2_reuse_base_inputs_device[0].this_layer_cache_start,
                base_round2_cache_ptr
            );
            assert_eq!(
                round2_reuse_ext_inputs_device[0].this_layer_start,
                ext_round2_cache_ptr
            );
        }

        drop(storage);
        assert_eq!(context.get_used_mem_current(), baseline);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn virtual_setup_sources_lower_to_synthetic_descriptors() {
        let context = make_test_context(64, 8);
        let mut storage = GpuGKRStorage::<BF, E4>::default();
        let base_values = (0..8)
            .map(|idx| BF::new(idx as u32 + 1))
            .collect::<Vec<_>>();
        storage.insert_base_field_at_layer(
            0,
            GKRAddress::BaseLayerMemory(0),
            GpuBaseFieldPoly::new(alloc_and_copy(&context, &base_values)),
        );

        let inputs = GKRInputs {
            inputs_in_base: vec![
                GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits),
                GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
            ],
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: Vec::new(),
        };

        let round0 = storage.get_for_sumcheck_round_0(&inputs);
        assert!(round0.base_field_inputs[0].start.is_null());
        assert_eq!(round0.base_field_inputs[0].next_layer_size, 4);
        assert_eq!(
            round0.base_field_inputs[0].source_kind,
            GpuBaseFieldSourceKind::VirtualRangeCheck16Bits
        );
        assert!(round0.base_field_inputs[1].start.is_null());
        assert_eq!(round0.base_field_inputs[1].next_layer_size, 4);
        assert_eq!(
            round0.base_field_inputs[1].source_kind,
            GpuBaseFieldSourceKind::VirtualInitsAndTeardownsHigh
        );

        let round1 = storage
            .prepare_for_sumcheck_round_1(&inputs, &context)
            .unwrap();
        assert!(round1.base_field_inputs[0].base_input_start.is_null());
        assert_eq!(round1.base_field_inputs[0].base_layer_half_size, 4);
        assert_eq!(round1.base_field_inputs[0].next_layer_size, 2);
        assert_eq!(
            round1.base_field_inputs[0].source_kind,
            GpuBaseFieldSourceKind::VirtualRangeCheck16Bits
        );
        assert!(round1.base_field_inputs[1].base_input_start.is_null());
        assert_eq!(
            round1.base_field_inputs[1].source_kind,
            GpuBaseFieldSourceKind::VirtualInitsAndTeardownsHigh
        );

        let round2_first = storage
            .prepare_for_sumcheck_round_2(&inputs, &context)
            .unwrap();
        assert!(round2_first.base_field_inputs[0].base_input_start.is_null());
        assert_eq!(round2_first.base_field_inputs[0].base_layer_half_size, 4);
        assert_eq!(round2_first.base_field_inputs[0].base_quarter_size, 2);
        assert_eq!(round2_first.base_field_inputs[0].next_layer_size, 1);
        assert!(round2_first.base_field_inputs[0].first_access);
        assert_eq!(
            round2_first.base_field_inputs[0].source_kind,
            GpuBaseFieldSourceKind::VirtualRangeCheck16Bits
        );
        assert!(round2_first.base_field_inputs[1].base_input_start.is_null());
        assert!(round2_first.base_field_inputs[1].first_access);
        assert_eq!(
            round2_first.base_field_inputs[1].source_kind,
            GpuBaseFieldSourceKind::VirtualInitsAndTeardownsHigh
        );

        let round2_second = storage
            .prepare_for_sumcheck_round_2(&inputs, &context)
            .unwrap();
        assert!(!round2_second.base_field_inputs[0].first_access);
        assert!(!round2_second.base_field_inputs[1].first_access);
        assert_eq!(
            round2_second.base_field_inputs[0].source_kind,
            GpuBaseFieldSourceKind::VirtualRangeCheck16Bits
        );
        assert_eq!(
            round2_second.base_field_inputs[1].source_kind,
            GpuBaseFieldSourceKind::VirtualInitsAndTeardownsHigh
        );
    }
}
