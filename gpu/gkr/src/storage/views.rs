use std::sync::Arc;

use era_cudart::result::CudaResult;

use super::super::{GpuBaseFieldPoly, GpuExtensionFieldPoly, GpuGKRLayerSource, GpuGKRStorage};
use crate::storage_layout::{FieldType, StorageSlot};
use crate::upstream::GKRAddress;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_prover_context::ProverContext;

impl<B, E> GpuGKRStorage<B, E> {
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

    pub(crate) fn resolve_base_view_or_panic(&self, address: GKRAddress) -> GpuBaseFieldPoly<B> {
        let layout = self
            .layout
            .as_ref()
            .expect("storage layout required to resolve a base column");
        let physical = layout
            .scratch_space_mapping_rev
            .iter()
            .find_map(|(&slot, &logical)| {
                (logical == address).then_some(GKRAddress::ScratchSpace(slot))
            })
            .unwrap_or(address);
        let canonical = layout.aliases.get(&physical).copied().unwrap_or(physical);
        self.try_get_base_poly(canonical)
            .unwrap_or_else(|| {
                panic!("base column {address:?} has no live backing at {canonical:?}")
            })
            .clone()
    }

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::make_test_context;
    use gpu_core::primitives::field::{BF, E4};

    #[test]
    fn scratch_alias_resolves_after_layer_release() {
        let context = make_test_context(64, 16);
        let logical = GKRAddress::InnerLayer {
            layer: 1,
            offset: 8,
        };
        let scratch = GKRAddress::ScratchSpace(0);
        let mut layout = crate::storage_layout::handcrafted_layout(
            scratch,
            GKRAddress::ScratchSpace(1),
            GKRAddress::Cached {
                layer: 0,
                offset: 0,
            },
            GKRAddress::Cached {
                layer: 0,
                offset: 1,
            },
        );
        layout.scratch_space_mapping_rev.insert(0, logical);
        let mut storage = GpuGKRStorage::<BF, E4>::default();
        storage.set_layout(Arc::new(layout));
        let value = storage.allocate_base_view(0, scratch, &context).unwrap();
        let pointer = value.as_ptr();
        storage.insert_base_field_at_layer(0, scratch, value.clone());
        storage.insert_base_field_at_layer(1, logical, value);

        storage.release_main_layer_inputs(1);
        assert_eq!(
            storage.resolve_base_view_or_panic(logical).as_ptr(),
            pointer
        );
    }
}
