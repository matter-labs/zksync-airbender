// GPU scheduling contract: see docs/gpu_scheduling_contract.md

pub(crate) mod backward;
pub(crate) mod base_layer_claims;
pub(crate) mod eval_recipes;
pub(crate) mod forward;
pub(crate) mod gkr_address_audit;
#[cfg(test)]
pub(crate) mod gkr_address_audit_helpers;
pub(crate) mod gkr_initial_inner_products;
mod gpu_kernels;
pub(crate) mod immediate_factors;
pub(crate) mod setup;
pub(crate) mod stage1;
pub(crate) mod storage_layout;
mod storage_ops;
pub(crate) mod transform;

pub(crate) use gpu_kernels::GpuKernels;

use std::collections::BTreeMap;
use std::ptr::null;
use std::sync::Arc;

use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::{DeviceAllocation, ProverContext};
use crate::primitives::device_structures::{DeviceVectorChunk, DeviceVectorChunkMut};
use crate::prover::gkr::gkr_address_audit::AddressClass;
use crate::prover::gkr::storage_layout::GpuGKRStorageLayout;

use crate::upstream::{GKRAddress, GKRInputs, VirtualSetupPoly};
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, DeviceSlice};

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

    pub(crate) fn as_ptr(&self) -> *const E {
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
// FFI: kernel argument type — consumed by GPU code through compiled kernel
// signatures even though the host-side construction sites are all test-only.
#[allow(dead_code)]
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

// FFI: kernel argument type — consumed by GPU code through compiled kernel
// signatures even though the host-side construction sites are all test-only.
#[allow(dead_code)]
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

// FFI: kernel argument type — consumed by GPU code through compiled kernel
// signatures even though the host-side construction sites are all test-only.
#[allow(dead_code)]
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

#[cfg(test)]
pub(crate) use tests::{
    alloc_device_and_schedule_upload, alloc_host_and_schedule_copy,
    GpuSumcheckRound0DeviceLaunchDescriptors, GpuSumcheckRound0HostLaunchDescriptors,
    GpuSumcheckRound0ScheduledLaunchDescriptors, GpuSumcheckRound1DeviceLaunchDescriptors,
    GpuSumcheckRound1HostLaunchDescriptors, GpuSumcheckRound1ScheduledLaunchDescriptors,
    GpuSumcheckRound2DeviceLaunchDescriptors, GpuSumcheckRound2HostLaunchDescriptors,
    GpuSumcheckRound2ScheduledLaunchDescriptors, GpuSumcheckRound3AndBeyondDeviceLaunchDescriptors,
    GpuSumcheckRound3AndBeyondHostLaunchDescriptors,
    GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors,
};

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
            | GKRAddress::VirtualSetup(..)
            | GKRAddress::ScratchSpace(..) => Some(0),
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
}

mod storage_views;

#[cfg(test)]
mod round_prepared_test_impls;

#[cfg(test)]
pub(crate) mod tests;
