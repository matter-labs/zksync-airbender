#[cfg(test)]
mod tests {
    use crate::test_utils::make_test_context;
    use crate::{upstream::GKRAddress, GpuGKRStorage};
    use gpu_core::primitives::field::{BF, E4};
    use std::sync::Arc;

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
