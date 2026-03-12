// Async scheduling contract for GPU GKR storage:
// - All GKR allocations, frees, callbacks, descriptor uploads, and kernel launches are treated as
//   logically ordered on the exec stream.
// - Host callbacks only materialize challenge-dependent host data; they must not call CUDA APIs or
//   perform device allocation/deallocation.
// - Device allocations do not need to remain owned after scheduling returns: their logical
//   lifetime is determined by the already-queued exec-stream work.
// - Host buffers that are referenced by queued callbacks or async copies must remain owned by the
//   enclosing prover job until the stream has consumed them. Any proof data needed after execution
//   must be copied back to host as part of the scheduled workflow.

pub(crate) mod setup;

use std::collections::BTreeMap;
use std::ptr::null;
use std::sync::Arc;

use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor};
use crate::primitives::device_structures::DeviceVectorChunk;
use cs::definitions::GKRAddress;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::CudaSlice;
use field::Field;
use prover::gkr::sumcheck::evaluation_kernels::GKRInputs;

pub(crate) struct GpuGKRLayerSource<B, E> {
    pub(crate) base_field_inputs: BTreeMap<GKRAddress, GpuBaseFieldPoly<B>>,
    pub(crate) extension_field_inputs: BTreeMap<GKRAddress, GpuExtensionFieldPoly<E>>,
    pub(crate) intermediate_storage_for_folder_base_field_inputs:
        BTreeMap<GKRAddress, (usize, GpuBaseFieldPolyIntermediateFoldingStorage<E>)>,
    pub(crate) intermediate_storage_for_folder_extension_field_inputs:
        BTreeMap<GKRAddress, (usize, GpuExtensionFieldPolyIntermediateFoldingStorage<E>)>,
}

pub(crate) struct GpuGKRStorage<B, E> {
    pub(crate) layers: Vec<GpuGKRLayerSource<B, E>>,
}

impl<B, E> Default for GpuGKRLayerSource<B, E> {
    fn default() -> Self {
        Self {
            base_field_inputs: BTreeMap::new(),
            extension_field_inputs: BTreeMap::new(),
            intermediate_storage_for_folder_base_field_inputs: BTreeMap::new(),
            intermediate_storage_for_folder_extension_field_inputs: BTreeMap::new(),
        }
    }
}

impl<B, E> Default for GpuGKRStorage<B, E> {
    fn default() -> Self {
        Self { layers: Vec::new() }
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

    pub(crate) fn as_device_chunk(&self) -> DeviceVectorChunk<'_, B> {
        DeviceVectorChunk::new(self.backing.as_ref(), self.offset, self.len)
    }

    pub(crate) fn accessor(&self) -> GpuBaseFieldPolySource<B> {
        GpuBaseFieldPolySource {
            start: self.as_ptr(),
            next_layer_size: self.len / 2,
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

    pub(crate) fn as_device_chunk(&self) -> DeviceVectorChunk<'_, E> {
        DeviceVectorChunk::new(self.backing.as_ref(), self.offset, self.len)
    }

    pub(crate) fn accessor(&self) -> GpuExtensionFieldPolyInitialSource<E> {
        GpuExtensionFieldPolyInitialSource {
            start: self.as_ptr(),
            next_layer_size: self.len / 2,
        }
    }
}

pub(crate) struct GpuBaseFieldPolyIntermediateFoldingStorage<E> {
    pub(crate) continuous_buffer: DeviceAllocation<E>,
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
        let continuous_buffer = context.alloc(buffer_size, AllocationPlacement::Top)?;

        Ok(Self {
            continuous_buffer,
            size_after_two_folds,
        })
    }

    pub(crate) fn initial_pointer(&mut self) -> *mut E {
        self.continuous_buffer.as_mut_ptr()
    }

    pub(crate) fn pointers_for_sumcheck_accessor_step(&mut self, step: usize) -> (*mut E, *mut E) {
        unsafe {
            assert!(step > 2);
            let mut input_offset = self.continuous_buffer.as_mut_ptr();
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

pub(crate) struct GpuExtensionFieldPolyIntermediateFoldingStorage<E> {
    pub(crate) continuous_buffer: DeviceAllocation<E>,
    pub(crate) size_after_one_fold: usize,
}

impl<E> GpuExtensionFieldPolyIntermediateFoldingStorage<E> {
    pub(crate) fn new_for_extension_poly_size(
        poly_size: usize,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        assert!(poly_size.is_power_of_two());
        assert!(poly_size > 2);

        let size_after_one_fold = poly_size / 4;
        let buffer_size = size_after_one_fold * 2;
        let continuous_buffer = context.alloc(buffer_size, AllocationPlacement::Top)?;

        Ok(Self {
            continuous_buffer,
            size_after_one_fold,
        })
    }

    pub(crate) fn pointer_for_sumcheck_after_one_fold(&mut self) -> *mut E {
        self.continuous_buffer.as_mut_ptr()
    }

    pub(crate) fn pointer_for_sumcheck_continuation(&mut self, step: usize) -> (*mut E, *mut E) {
        unsafe {
            assert!(step >= 2);
            let mut input_offset = self.continuous_buffer.as_mut_ptr();
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

#[derive(Debug)]
#[repr(C)]
pub(crate) struct GpuBaseFieldPolySource<B> {
    pub(crate) start: *const B,
    pub(crate) next_layer_size: usize,
}

impl<B> Clone for GpuBaseFieldPolySource<B> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<B> Copy for GpuBaseFieldPolySource<B> {}

impl<B> GpuBaseFieldPolySource<B> {
    pub(crate) fn empty() -> Self {
        Self {
            start: null(),
            next_layer_size: 0,
        }
    }
}

// These descriptors live in preallocated host/device buffers that are owned by the scheduler.
// Callbacks only fill the host buffers once transcript challenges are available, and the already
// queued H2D copies upload them to device memory before the future kernel launches consume them.
#[derive(Debug)]
#[repr(C)]
pub(crate) struct GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E> {
    pub(crate) base_layer_half_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) base_input_start: *const B,
    pub(crate) first_folding_challenge_and_squared: (E, E),
}

impl<B, E: Copy> Clone for GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<B, E: Copy> Copy for GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E> {}

#[derive(Debug)]
#[repr(C)]
pub(crate) struct GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E> {
    pub(crate) base_input_start: *const B,
    pub(crate) this_layer_cache_start: *mut E,
    pub(crate) base_layer_half_size: usize,
    pub(crate) base_quarter_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) first_folding_challenge: E,
    pub(crate) second_folding_challenge: E,
    pub(crate) combined_challenges: E,
    pub(crate) first_access: bool,
}

impl<B, E: Copy> Clone for GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<B, E: Copy> Copy for GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E> {}

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
    pub(crate) folding_challenge: E,
    pub(crate) first_access: bool,
}

impl<E: Copy> Clone for GpuExtensionFieldPolyContinuingLaunchDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E: Copy> Copy for GpuExtensionFieldPolyContinuingLaunchDescriptor<E> {}

#[derive(Debug)]
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
    #[allow(dead_code)] // Keeps pinned host descriptors alive until queued uploads complete.
    pub(crate) host: GpuSumcheckRound0HostLaunchDescriptors<B, E>,
    pub(crate) device: GpuSumcheckRound0DeviceLaunchDescriptors<B, E>,
}

pub(crate) struct GpuSumcheckRound1HostLaunchDescriptors<B, E> {
    pub(crate) base_field_inputs:
        HostAllocation<[GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E>]>,
    pub(crate) extension_field_inputs:
        HostAllocation<[GpuExtensionFieldPolyContinuingLaunchDescriptor<E>]>,
}

pub(crate) struct GpuSumcheckRound1DeviceLaunchDescriptors<B, E> {
    pub(crate) base_field_inputs:
        DeviceAllocation<GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E>>,
    pub(crate) extension_field_inputs:
        DeviceAllocation<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
}

pub(crate) struct GpuSumcheckRound1ScheduledLaunchDescriptors<B, E> {
    pub(crate) host: GpuSumcheckRound1HostLaunchDescriptors<B, E>,
    pub(crate) device: GpuSumcheckRound1DeviceLaunchDescriptors<B, E>,
}

pub(crate) struct GpuSumcheckRound2HostLaunchDescriptors<B, E> {
    pub(crate) base_field_inputs:
        HostAllocation<[GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E>]>,
    pub(crate) extension_field_inputs:
        HostAllocation<[GpuExtensionFieldPolyContinuingLaunchDescriptor<E>]>,
}

pub(crate) struct GpuSumcheckRound2DeviceLaunchDescriptors<B, E> {
    pub(crate) base_field_inputs:
        DeviceAllocation<GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E>>,
    pub(crate) extension_field_inputs:
        DeviceAllocation<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
}

pub(crate) struct GpuSumcheckRound2ScheduledLaunchDescriptors<B, E> {
    pub(crate) host: GpuSumcheckRound2HostLaunchDescriptors<B, E>,
    pub(crate) device: GpuSumcheckRound2DeviceLaunchDescriptors<B, E>,
}

pub(crate) struct GpuSumcheckRound3AndBeyondHostLaunchDescriptors<E> {
    pub(crate) base_field_inputs:
        HostAllocation<[GpuExtensionFieldPolyContinuingLaunchDescriptor<E>]>,
    pub(crate) extension_field_inputs:
        HostAllocation<[GpuExtensionFieldPolyContinuingLaunchDescriptor<E>]>,
}

pub(crate) struct GpuSumcheckRound3AndBeyondDeviceLaunchDescriptors<E> {
    pub(crate) base_field_inputs:
        DeviceAllocation<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
    pub(crate) extension_field_inputs:
        DeviceAllocation<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
}

pub(crate) struct GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors<E> {
    pub(crate) host: GpuSumcheckRound3AndBeyondHostLaunchDescriptors<E>,
    pub(crate) device: GpuSumcheckRound3AndBeyondDeviceLaunchDescriptors<E>,
}

#[derive(Debug)]
pub(crate) struct GpuBaseFieldPolySourceAfterOneFoldingPlan<B> {
    pub(crate) base_layer_half_size: usize,
    pub(crate) next_layer_size: usize,
    pub(crate) base_input_start: *const B,
}

impl<B> Clone for GpuBaseFieldPolySourceAfterOneFoldingPlan<B> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<B> Copy for GpuBaseFieldPolySourceAfterOneFoldingPlan<B> {}

unsafe impl<B> Send for GpuBaseFieldPolySourceAfterOneFoldingPlan<B> {}
unsafe impl<B> Sync for GpuBaseFieldPolySourceAfterOneFoldingPlan<B> {}

impl<B> GpuBaseFieldPolySourceAfterOneFoldingPlan<B> {
    fn empty() -> Self {
        Self {
            base_layer_half_size: 0,
            next_layer_size: 0,
            base_input_start: null(),
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
    pub(crate) base_field_inputs: Vec<GpuBaseFieldPolySourceAfterOneFoldingPlan<B>>,
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

fn alloc_host_and_copy<T: Copy>(context: &ProverContext, values: &[T]) -> HostAllocation<[T]> {
    let mut allocation = unsafe { context.alloc_host_uninit_slice(values.len()) };
    unsafe {
        allocation
            .get_mut_accessor()
            .get_mut()
            .copy_from_slice(values);
    }
    allocation
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
    fn base_poly_layer(address: GKRAddress) -> Option<usize> {
        match address {
            GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => Some(layer),
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..) => Some(0),
            GKRAddress::OptimizedOut(..) => None,
        }
    }

    fn ext_poly_layer(address: GKRAddress) -> Option<usize> {
        match address {
            GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => Some(layer),
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::OptimizedOut(..) => None,
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

impl<B, E: Field> GpuGKRStorage<B, E> {
    fn round_input_layer(address: GKRAddress) -> usize {
        match address {
            GKRAddress::OptimizedOut(..) => unreachable!(),
            GKRAddress::Cached { layer, .. } => {
                assert_eq!(layer, 0);
                0
            }
            GKRAddress::InnerLayer { layer, .. } => layer,
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..) => 0,
        }
    }

    fn round_output_layer(address: GKRAddress) -> usize {
        match address {
            GKRAddress::OptimizedOut(..)
            | GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..) => unreachable!(),
            GKRAddress::Cached { .. } => unreachable!(),
            GKRAddress::InnerLayer { layer, .. } => layer,
        }
    }

    fn plan_base_source_for_round_1(
        &self,
        poly: GKRAddress,
    ) -> GpuBaseFieldPolySourceAfterOneFoldingPlan<B> {
        let poly = self.get_base_poly_for_address(poly).expect("must exist");

        GpuBaseFieldPolySourceAfterOneFoldingPlan {
            base_layer_half_size: poly.len() / 2,
            next_layer_size: poly.len() / 4,
            base_input_start: poly.as_ptr(),
        }
    }

    fn plan_base_source_for_round_2(
        &mut self,
        poly: GKRAddress,
        context: &ProverContext,
    ) -> CudaResult<GpuBaseFieldPolySourceAfterTwoFoldingsPlan<B, E>> {
        let layer = Self::base_poly_layer(poly).expect("must exist");
        let sumcheck_step = 2;
        let (base_poly_len, base_poly_ptr) = {
            let poly = self.get_base_poly_for_address(poly).expect("must exist");
            (poly.len(), poly.as_ptr())
        };

        if !self.layers[layer]
            .intermediate_storage_for_folder_base_field_inputs
            .contains_key(&poly)
        {
            let buffer = GpuBaseFieldPolyIntermediateFoldingStorage::new_for_base_poly_size(
                base_poly_len,
                context,
            )?;
            self.layers[layer]
                .intermediate_storage_for_folder_base_field_inputs
                .insert(poly, (1, buffer));
        }

        let (last_used_for_layer, buffer) = self.layers[layer]
            .intermediate_storage_for_folder_base_field_inputs
            .get_mut(&poly)
            .expect("must be present");
        assert!(*last_used_for_layer == sumcheck_step || *last_used_for_layer == sumcheck_step - 1);
        let this_layer_start = buffer.initial_pointer();

        let first_access = if *last_used_for_layer == sumcheck_step {
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
        assert!(*last_used_for_layer == sumcheck_step || *last_used_for_layer == sumcheck_step - 1);
        let (previous_layer_start, this_layer_start) =
            buffer.pointers_for_sumcheck_accessor_step(sumcheck_step);
        let this_layer_size = buffer.size_after_two_folds >> (sumcheck_step - 2);
        let next_layer_size = this_layer_size / 2;

        let first_access = if *last_used_for_layer == sumcheck_step {
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
            let mut buffer =
                GpuExtensionFieldPolyIntermediateFoldingStorage::new_for_extension_poly_size(
                    size, context,
                )?;
            let buffer_pointer = buffer.pointer_for_sumcheck_after_one_fold();
            let input_pointer = poly_ref.as_ptr();

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
                *last_used_for_layer == sumcheck_step || *last_used_for_layer == sumcheck_step - 1
            );
            let (previous_layer_start, this_layer_start) =
                buffer.pointer_for_sumcheck_continuation(sumcheck_step);
            let this_layer_size = buffer.size_after_one_fold >> (sumcheck_step - 2);
            let next_layer_size = this_layer_size / 2;

            let first_access = if *last_used_for_layer == sumcheck_step {
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
                let layer = Self::round_input_layer(*input);
                let source = self.layers[layer]
                    .base_field_inputs
                    .get(input)
                    .unwrap_or_else(|| {
                        panic!(
                            "Polynomial with address {:?} is missing from input sources for base field polys",
                            input
                        )
                    });
                storage.base_field_inputs.push(source.accessor());
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
        let host = GpuSumcheckRound0HostLaunchDescriptors {
            base_field_inputs: alloc_host_and_copy(context, &host_values.base_field_inputs),
            extension_field_inputs: alloc_host_and_copy(
                context,
                &host_values.extension_field_inputs,
            ),
            base_field_outputs: alloc_host_and_copy(context, &host_values.base_field_outputs),
            extension_field_outputs: alloc_host_and_copy(
                context,
                &host_values.extension_field_outputs,
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

        Ok(GpuSumcheckRound0ScheduledLaunchDescriptors { host, device })
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
                    .push(self.plan_base_source_for_round_1(*input));
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

impl<B, E: Field> GpuSumcheckRound1PreparedStorage<B, E> {
    pub(crate) fn schedule_upload_launch_descriptors<'a>(
        &self,
        folding_challenges: UnsafeAccessor<[E]>,
        callbacks: &mut Callbacks<'a>,
        context: &ProverContext,
    ) -> CudaResult<GpuSumcheckRound1ScheduledLaunchDescriptors<B, E>>
    where
        B: 'a,
        E: 'a,
    {
        let base_field_inputs_plan = self.base_field_inputs.clone();
        let extension_field_inputs_plan = self.extension_field_inputs.clone();
        let sumcheck_step = self.sumcheck_step;

        let (base_field_inputs, base_field_inputs_device) = schedule_callback_populated_upload(
            context,
            self.base_field_inputs.len(),
            callbacks,
            move |dst: &mut [GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E>]| unsafe {
                let folding_challenges = folding_challenges.get();
                assert_eq!(folding_challenges.len(), sumcheck_step);
                let folding_challenge = folding_challenges[0];
                let mut challenge_squared = folding_challenge;
                challenge_squared.square();

                for (dst, plan) in dst.iter_mut().zip(base_field_inputs_plan.iter().copied()) {
                    *dst = GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                        base_layer_half_size: plan.base_layer_half_size,
                        next_layer_size: plan.next_layer_size,
                        base_input_start: plan.base_input_start,
                        first_folding_challenge_and_squared: (folding_challenge, challenge_squared),
                    };
                }
            },
        )?;
        let (extension_field_inputs, extension_field_inputs_device) =
            schedule_callback_populated_upload(
                context,
                self.extension_field_inputs.len(),
                callbacks,
                move |dst: &mut [GpuExtensionFieldPolyContinuingLaunchDescriptor<E>]| unsafe {
                    let folding_challenges = folding_challenges.get();
                    assert_eq!(folding_challenges.len(), sumcheck_step);
                    let folding_challenge = folding_challenges[0];

                    for (dst, plan) in dst
                        .iter_mut()
                        .zip(extension_field_inputs_plan.iter().copied())
                    {
                        *dst = GpuExtensionFieldPolyContinuingLaunchDescriptor {
                            previous_layer_start: plan.previous_layer_start,
                            this_layer_start: plan.this_layer_start,
                            this_layer_size: plan.this_layer_size,
                            next_layer_size: plan.next_layer_size,
                            folding_challenge,
                            first_access: plan.first_access,
                        };
                    }
                },
            )?;
        let device = GpuSumcheckRound1DeviceLaunchDescriptors {
            base_field_inputs: base_field_inputs_device,
            extension_field_inputs: extension_field_inputs_device,
        };
        let host = GpuSumcheckRound1HostLaunchDescriptors {
            base_field_inputs,
            extension_field_inputs,
        };

        Ok(GpuSumcheckRound1ScheduledLaunchDescriptors { host, device })
    }
}

impl<B, E: Field> GpuSumcheckRound2PreparedStorage<B, E> {
    pub(crate) fn schedule_upload_launch_descriptors<'a>(
        &self,
        folding_challenges: UnsafeAccessor<[E]>,
        callbacks: &mut Callbacks<'a>,
        context: &ProverContext,
    ) -> CudaResult<GpuSumcheckRound2ScheduledLaunchDescriptors<B, E>>
    where
        B: 'a,
        E: 'a,
    {
        let base_field_inputs_plan = self.base_field_inputs.clone();
        let extension_field_inputs_plan = self.extension_field_inputs.clone();
        let sumcheck_step = self.sumcheck_step;

        let (base_field_inputs, base_field_inputs_device) = schedule_callback_populated_upload(
            context,
            self.base_field_inputs.len(),
            callbacks,
            move |dst: &mut [GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E>]| unsafe {
                let folding_challenges = folding_challenges.get();
                assert_eq!(folding_challenges.len(), sumcheck_step);
                let first_folding_challenge = folding_challenges[0];
                let second_folding_challenge = folding_challenges[1];
                let mut combined_challenges = first_folding_challenge;
                combined_challenges.mul_assign(&second_folding_challenge);

                for (dst, plan) in dst.iter_mut().zip(base_field_inputs_plan.iter().copied()) {
                    *dst = GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor {
                        base_input_start: plan.base_input_start,
                        this_layer_cache_start: plan.this_layer_cache_start,
                        base_layer_half_size: plan.base_layer_half_size,
                        base_quarter_size: plan.base_quarter_size,
                        next_layer_size: plan.next_layer_size,
                        first_folding_challenge,
                        second_folding_challenge,
                        combined_challenges,
                        first_access: plan.first_access,
                    };
                }
            },
        )?;
        let (extension_field_inputs, extension_field_inputs_device) =
            schedule_callback_populated_upload(
                context,
                self.extension_field_inputs.len(),
                callbacks,
                move |dst: &mut [GpuExtensionFieldPolyContinuingLaunchDescriptor<E>]| unsafe {
                    let folding_challenges = folding_challenges.get();
                    assert_eq!(folding_challenges.len(), sumcheck_step);
                    let second_folding_challenge = folding_challenges[1];

                    for (dst, plan) in dst
                        .iter_mut()
                        .zip(extension_field_inputs_plan.iter().copied())
                    {
                        *dst = GpuExtensionFieldPolyContinuingLaunchDescriptor {
                            previous_layer_start: plan.previous_layer_start,
                            this_layer_start: plan.this_layer_start,
                            this_layer_size: plan.this_layer_size,
                            next_layer_size: plan.next_layer_size,
                            folding_challenge: second_folding_challenge,
                            first_access: plan.first_access,
                        };
                    }
                },
            )?;
        let device = GpuSumcheckRound2DeviceLaunchDescriptors {
            base_field_inputs: base_field_inputs_device,
            extension_field_inputs: extension_field_inputs_device,
        };
        let host = GpuSumcheckRound2HostLaunchDescriptors {
            base_field_inputs,
            extension_field_inputs,
        };

        Ok(GpuSumcheckRound2ScheduledLaunchDescriptors { host, device })
    }
}

impl<E: Field> GpuSumcheckRound3AndBeyondPreparedStorage<E> {
    pub(crate) fn schedule_upload_launch_descriptors<'a>(
        &self,
        folding_challenges: UnsafeAccessor<[E]>,
        callbacks: &mut Callbacks<'a>,
        context: &ProverContext,
    ) -> CudaResult<GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors<E>>
    where
        E: 'a,
    {
        let base_field_inputs_plan = self.base_field_inputs.clone();
        let extension_field_inputs_plan = self.extension_field_inputs.clone();
        let sumcheck_step = self.sumcheck_step;

        let (base_field_inputs, base_field_inputs_device) = schedule_callback_populated_upload(
            context,
            self.base_field_inputs.len(),
            callbacks,
            move |dst: &mut [GpuExtensionFieldPolyContinuingLaunchDescriptor<E>]| unsafe {
                let folding_challenges = folding_challenges.get();
                assert_eq!(folding_challenges.len(), sumcheck_step);
                let folding_challenge = *folding_challenges.last().expect("must be present");

                for (dst, plan) in dst.iter_mut().zip(base_field_inputs_plan.iter().copied()) {
                    *dst = GpuExtensionFieldPolyContinuingLaunchDescriptor {
                        previous_layer_start: plan.previous_layer_start,
                        this_layer_start: plan.this_layer_start,
                        this_layer_size: plan.this_layer_size,
                        next_layer_size: plan.next_layer_size,
                        folding_challenge,
                        first_access: plan.first_access,
                    };
                }
            },
        )?;
        let (extension_field_inputs, extension_field_inputs_device) =
            schedule_callback_populated_upload(
                context,
                self.extension_field_inputs.len(),
                callbacks,
                move |dst: &mut [GpuExtensionFieldPolyContinuingLaunchDescriptor<E>]| unsafe {
                    let folding_challenges = folding_challenges.get();
                    assert_eq!(folding_challenges.len(), sumcheck_step);
                    let folding_challenge = *folding_challenges.last().expect("must be present");

                    for (dst, plan) in dst
                        .iter_mut()
                        .zip(extension_field_inputs_plan.iter().copied())
                    {
                        *dst = GpuExtensionFieldPolyContinuingLaunchDescriptor {
                            previous_layer_start: plan.previous_layer_start,
                            this_layer_start: plan.this_layer_start,
                            this_layer_size: plan.this_layer_size,
                            next_layer_size: plan.next_layer_size,
                            folding_challenge,
                            first_access: plan.first_access,
                        };
                    }
                },
            )?;
        let device = GpuSumcheckRound3AndBeyondDeviceLaunchDescriptors {
            base_field_inputs: base_field_inputs_device,
            extension_field_inputs: extension_field_inputs_device,
        };
        let host = GpuSumcheckRound3AndBeyondHostLaunchDescriptors {
            base_field_inputs,
            extension_field_inputs,
        };

        Ok(GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors { host, device })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::allocator::tracker::AllocationPlacement;
    use crate::primitives::callbacks::Callbacks;
    use crate::primitives::field::{BF, E4};
    use crate::prover::test_utils::make_test_context;
    use era_cudart::memory::memory_copy;
    use serial_test::serial;

    fn alloc_and_copy<T: Copy>(context: &ProverContext, values: &[T]) -> DeviceAllocation<T> {
        let mut allocation = context
            .alloc(values.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy(&mut allocation, values).unwrap();
        allocation
    }

    fn alloc_host_values<T: Copy>(context: &ProverContext, values: &[T]) -> HostAllocation<[T]> {
        let mut allocation = unsafe { context.alloc_host_uninit_slice(values.len()) };
        unsafe {
            allocation
                .get_mut_accessor()
                .get_mut()
                .copy_from_slice(values);
        }
        allocation
    }

    fn copy_device_values<T: Copy>(
        context: &ProverContext,
        values: &DeviceAllocation<T>,
    ) -> Vec<T> {
        let mut allocation = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy(&mut allocation, values).unwrap();
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
        let mut callbacks = Callbacks::new();

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
            let round1_challenges = alloc_host_values(&context, &[r1]);
            let round1 = storage
                .prepare_for_sumcheck_round_1(&inputs, &context)
                .unwrap()
                .schedule_upload_launch_descriptors(
                    round1_challenges.get_accessor(),
                    &mut callbacks,
                    &context,
                )
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let round1_base_inputs_accessor = round1.host.base_field_inputs.get_accessor();
            let round1_base_inputs = unsafe { round1_base_inputs_accessor.get() };
            let round1_ext_inputs_accessor = round1.host.extension_field_inputs.get_accessor();
            let round1_ext_inputs = unsafe { round1_ext_inputs_accessor.get() };
            assert_eq!(round1_base_inputs[0].base_input_start, base_input_ptr);
            assert!(round1_base_inputs[1].base_input_start.is_null());
            assert_eq!(round1_ext_inputs[0].previous_layer_start, ext_input_ptr);
            assert!(round1_ext_inputs[0].first_access);
            assert!(round1_ext_inputs[1].previous_layer_start.is_null());
            let round1_base_inputs_device =
                copy_device_values(&context, &round1.device.base_field_inputs);
            let round1_ext_inputs_device =
                copy_device_values(&context, &round1.device.extension_field_inputs);
            assert_eq!(
                round1_base_inputs_device[0]
                    .first_folding_challenge_and_squared
                    .0,
                r1
            );
            assert_eq!(round1_ext_inputs_device[0].folding_challenge, r1);
        }
        let used_after_round1 = context.get_used_mem_current();
        assert!(used_after_round1 > baseline);

        let r2 = sample_ext(200);
        let (base_round2_cache_ptr, ext_round2_cache_ptr) = {
            let round2_challenges = alloc_host_values(&context, &[r1, r2]);
            let round2_first = storage
                .prepare_for_sumcheck_round_2(&inputs, &context)
                .unwrap()
                .schedule_upload_launch_descriptors(
                    round2_challenges.get_accessor(),
                    &mut callbacks,
                    &context,
                )
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let round2_first_base_inputs_accessor =
                round2_first.host.base_field_inputs.get_accessor();
            let round2_first_base_inputs = unsafe { round2_first_base_inputs_accessor.get() };
            let round2_first_ext_inputs_accessor =
                round2_first.host.extension_field_inputs.get_accessor();
            let round2_first_ext_inputs = unsafe { round2_first_ext_inputs_accessor.get() };
            assert!(round2_first_base_inputs[0].first_access);
            assert!(round2_first_ext_inputs[0].first_access);
            let round2_first_base_inputs_device =
                copy_device_values(&context, &round2_first.device.base_field_inputs);
            let round2_first_ext_inputs_device =
                copy_device_values(&context, &round2_first.device.extension_field_inputs);
            assert_eq!(
                round2_first_base_inputs_device[0].second_folding_challenge,
                r2
            );
            assert_eq!(round2_first_ext_inputs_device[0].folding_challenge, r2);
            (
                round2_first_base_inputs[0].this_layer_cache_start,
                round2_first_ext_inputs[0].this_layer_start,
            )
        };

        {
            let round2_challenges = alloc_host_values(&context, &[r1, r2]);
            let round2_second = storage
                .prepare_for_sumcheck_round_2(&inputs, &context)
                .unwrap()
                .schedule_upload_launch_descriptors(
                    round2_challenges.get_accessor(),
                    &mut callbacks,
                    &context,
                )
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let round2_second_base_inputs_accessor =
                round2_second.host.base_field_inputs.get_accessor();
            let round2_second_base_inputs = unsafe { round2_second_base_inputs_accessor.get() };
            let round2_second_ext_inputs_accessor =
                round2_second.host.extension_field_inputs.get_accessor();
            let round2_second_ext_inputs = unsafe { round2_second_ext_inputs_accessor.get() };
            assert!(!round2_second_base_inputs[0].first_access);
            assert!(!round2_second_ext_inputs[0].first_access);
            assert_eq!(
                round2_second_base_inputs[0].this_layer_cache_start,
                base_round2_cache_ptr
            );
            assert_eq!(
                round2_second_ext_inputs[0].this_layer_start,
                ext_round2_cache_ptr
            );
        }

        let r3 = sample_ext(300);
        let (round3_base_cache_ptr, round3_ext_cache_ptr) = {
            let round3_challenges = alloc_host_values(&context, &[r1, r2, r3]);
            let round3_first = storage
                .prepare_for_sumcheck_round_3_and_beyond(&inputs, 3, &context)
                .unwrap()
                .schedule_upload_launch_descriptors(
                    round3_challenges.get_accessor(),
                    &mut callbacks,
                    &context,
                )
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let round3_first_base_inputs_accessor =
                round3_first.host.base_field_inputs.get_accessor();
            let round3_first_base_inputs = unsafe { round3_first_base_inputs_accessor.get() };
            let round3_first_ext_inputs_accessor =
                round3_first.host.extension_field_inputs.get_accessor();
            let round3_first_ext_inputs = unsafe { round3_first_ext_inputs_accessor.get() };
            assert!(round3_first_base_inputs[0].first_access);
            assert!(round3_first_ext_inputs[0].first_access);
            let round3_first_base_inputs_device =
                copy_device_values(&context, &round3_first.device.base_field_inputs);
            let round3_first_ext_inputs_device =
                copy_device_values(&context, &round3_first.device.extension_field_inputs);
            assert_eq!(round3_first_base_inputs_device[0].folding_challenge, r3);
            assert_eq!(round3_first_ext_inputs_device[0].folding_challenge, r3);
            assert_eq!(
                unsafe {
                    round3_first_base_inputs[0]
                        .this_layer_start
                        .offset_from(round3_first_base_inputs[0].previous_layer_start)
                },
                2
            );
            assert_eq!(
                unsafe {
                    round3_first_ext_inputs[0]
                        .this_layer_start
                        .offset_from(round3_first_ext_inputs[0].previous_layer_start)
                },
                1
            );
            assert_eq!(round3_first_base_inputs[0].this_layer_size, 1);
            assert_eq!(round3_first_ext_inputs[0].this_layer_size, 1);
            (
                round3_first_base_inputs[0].this_layer_start,
                round3_first_ext_inputs[0].this_layer_start,
            )
        };

        {
            let round3_challenges = alloc_host_values(&context, &[r1, r2, r3]);
            let round3_second = storage
                .prepare_for_sumcheck_round_3_and_beyond(&inputs, 3, &context)
                .unwrap()
                .schedule_upload_launch_descriptors(
                    round3_challenges.get_accessor(),
                    &mut callbacks,
                    &context,
                )
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let round3_second_base_inputs_accessor =
                round3_second.host.base_field_inputs.get_accessor();
            let round3_second_base_inputs = unsafe { round3_second_base_inputs_accessor.get() };
            let round3_second_ext_inputs_accessor =
                round3_second.host.extension_field_inputs.get_accessor();
            let round3_second_ext_inputs = unsafe { round3_second_ext_inputs_accessor.get() };
            assert!(!round3_second_base_inputs[0].first_access);
            assert!(!round3_second_ext_inputs[0].first_access);
            assert_eq!(
                round3_second_base_inputs[0].this_layer_start,
                round3_base_cache_ptr
            );
            assert_eq!(
                round3_second_ext_inputs[0].this_layer_start,
                round3_ext_cache_ptr
            );
        }

        drop(storage);
        assert_eq!(context.get_used_mem_current(), baseline);
    }
}
