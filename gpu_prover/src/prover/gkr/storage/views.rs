use std::sync::Arc;

use era_cudart::result::CudaResult;

use super::super::{GpuBaseFieldPoly, GpuExtensionFieldPoly, GpuGKRLayerSource, GpuGKRStorage};
use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::ProverContext;
use crate::prover::gkr::storage_layout::{FieldType, StorageSlot};
use crate::upstream::GKRAddress;

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

    /// Non-mutating resolver: returns a `GpuBaseFieldPoly<B>` view for an
    /// already-populated address. Unlike `allocate_base_view`, this does
    /// NOT lazily allocate a backing — it returns a clone of the view
    /// stored in `storage.layers[L].base_field_inputs[addr]`, which the
    /// forward pass populates via `insert_base_field_at_layer` and the
    /// scratch / trace-holder bindings. Used by code paths that read an
    /// existing poly through the consolidated storage (e.g., main-layer
    /// extras eval) without forcing the allocation lifecycle that
    /// mutates the storage.
    ///
    /// Resolution order:
    ///   1. `storage.layers[layer].base_field_inputs[addr]` — direct hit.
    ///   2. Layout-driven canonical-layer lookup (handles `CopyIn`
    ///      aliases and addresses stored at a different canonical
    ///      layer than `layer`).
    /// Panics with diagnostic context on miss in both.
    pub(crate) fn resolve_base_view_or_panic(
        &self,
        layer: usize,
        address: GKRAddress,
    ) -> GpuBaseFieldPoly<B> {
        // Fast path: direct hit on the requested layer's per-address
        // map. Forward populates this for every address it materializes
        // into a layer's storage (including scratch hydration for
        // `InnerLayer { layer, .. }` addresses that alias to the
        // consolidated `ScratchSpace` backing).
        if let Some(layer_source) = self.layers.get(layer) {
            if let Some(view) = layer_source.base_field_inputs.get(&address) {
                return view.clone();
            }
        }
        // Try the address at its canonical storage layer (handles
        // `InnerLayer { layer: L', .. }` addresses requested through a
        // different logical layer).
        let canonical_layer = match address {
            GKRAddress::BaseLayerWitness(_)
            | GKRAddress::BaseLayerMemory(_)
            | GKRAddress::Setup(_)
            | GKRAddress::VirtualSetup(_)
            | GKRAddress::ScratchSpace(_) => 0,
            GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => layer,
        };
        if canonical_layer != layer {
            if let Some(layer_source) = self.layers.get(canonical_layer) {
                if let Some(view) = layer_source.base_field_inputs.get(&address) {
                    return view.clone();
                }
            }
        }
        // Final fallback: layout-driven canonical resolution. Aliases
        // map (e.g., `CopyInBaseField`) here; production code populates
        // the canonical's view in `base_field_inputs`, so this branch
        // exists for completeness against test paths that bypass the
        // forward population.
        let layout = self
            .layout
            .as_ref()
            .expect("storage layout required for resolve_base_view_or_panic");
        let (alias_canonical_layer, class, field, poly_idx) = layout
            .lookup(layer, &address)
            .unwrap_or_else(|| panic!("address {address:?} missing from layer {layer} layout"));
        assert_eq!(
            field,
            FieldType::Base,
            "address {address:?} is not classified as a base poly in layout"
        );
        let layer_layout = layout.layers.get(alias_canonical_layer).unwrap_or_else(|| {
            panic!("canonical layer {alias_canonical_layer} out of range in layout")
        });
        let layer_log2_stride = layer_layout.log2_stride;
        let stride = 1usize << layer_log2_stride;
        let offset = (poly_idx as usize) << layer_log2_stride;
        let layer_source = self.layers.get(alias_canonical_layer).unwrap_or_else(|| {
            panic!(
                "resolve_base_view_or_panic: storage layer {alias_canonical_layer} not present \
                 (address {address:?} requested at logical layer {layer})"
            )
        });
        let backing = layer_source.base_class_backings.get(&class).unwrap_or_else(|| {
            panic!(
                "resolve_base_view_or_panic: no consolidated base backing at layer {alias_canonical_layer} \
                 class {class:?} (address {address:?} requested at logical layer {layer})"
            )
        });
        GpuBaseFieldPoly::from_arc(Arc::clone(backing), offset, stride)
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
