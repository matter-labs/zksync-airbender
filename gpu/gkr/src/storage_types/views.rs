use std::collections::BTreeMap;
use std::sync::Arc;

use crate::gkr_address_audit::AddressClass;
use crate::storage_layout::GpuGKRStorageLayout;
use crate::upstream::GKRAddress;
use era_cudart::slice::{CudaSlice, DeviceSlice};
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_structures::DeviceVectorChunk;

#[doc(hidden)]
pub struct GpuGKRLayerSource<B, E> {
    pub base_field_inputs: BTreeMap<GKRAddress, GpuBaseFieldPoly<B>>,
    pub extension_field_inputs: BTreeMap<GKRAddress, GpuExtensionFieldPoly<E>>,
    /// Consolidated per-`AddressClass` backings for base-field polys living at
    /// this layer. Lazily allocated by `GpuGKRStorage::allocate_base_view`
    /// when a layout is set; size is taken from the layout's per-slot poly
    /// count. Empty when no consolidated allocations have been requested for
    /// this layer.
    pub(crate) base_class_backings: BTreeMap<AddressClass, Arc<DeviceAllocation<B>>>,
    pub(crate) ext_class_backings: BTreeMap<AddressClass, Arc<DeviceAllocation<E>>>,
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
            base_class_backings: BTreeMap::new(),
            ext_class_backings: BTreeMap::new(),
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

    pub fn as_device_chunk(&self) -> DeviceVectorChunk<'_, B> {
        DeviceVectorChunk::new(self.backing.as_ref(), self.offset, self.len)
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

    pub(crate) fn as_mut_ptr(&self) -> *mut E {
        self.as_ptr().cast_mut()
    }

    #[cfg(test)]
    pub(crate) fn as_device_slice(&self) -> &DeviceSlice<E> {
        &self.backing[self.offset..self.offset + self.len]
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

impl<B> GpuBaseFieldPoly<B> {
    #[cfg(test)]
    pub(crate) fn offset(&self) -> usize {
        self.offset
    }

    #[cfg(test)]
    pub(crate) fn shares_backing_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.backing, &other.backing)
    }
}

impl<E> GpuExtensionFieldPoly<E> {
    #[cfg(test)]
    pub(crate) fn new(backing: DeviceAllocation<E>) -> Self {
        let len = backing.len();
        Self::from_arc(Arc::new(backing), 0, len)
    }

    #[doc(hidden)]
    pub fn as_device_chunk(&self) -> DeviceVectorChunk<'_, E> {
        DeviceVectorChunk::new(self.backing.as_ref(), self.offset, self.len)
    }
}
