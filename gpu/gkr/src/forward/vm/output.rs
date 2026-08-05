use era_cudart::result::CudaResult;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;

use crate::gkr_address_audit::AddressClass;
use crate::storage_layout::FieldType;
use crate::upstream::{Field, FieldExtension, GKRAddress, GKRLayerDescription, NoFieldGKRRelation};
use crate::GpuGKRStorage;

/// Register copy gates, which intentionally have no VM store instruction.
pub(super) fn register_layer_copy_aliases<B, E>(
    layer_idx: usize,
    layer: &GKRLayerDescription,
    storage: &mut GpuGKRStorage<B, E>,
) where
    B: Clone,
    E: Clone,
{
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        match &gate.enforced_relation {
            NoFieldGKRRelation::CopyInBaseField { input, output }
            | NoFieldGKRRelation::CopyInExtensionField { input, output } => {
                assert_eq!(gate.output_layer, layer_idx + 1);
                let out_layer = layer_idx + 1;
                let base_source = storage.try_get_base_poly(*input).map(|p| p.clone_shared());
                if let Some(source) = base_source {
                    storage.insert_base_field_at_layer(out_layer, *output, source);
                } else {
                    let ext_source = storage.get_ext_poly(*input).clone_shared();
                    storage.insert_extension_at_layer(out_layer, *output, ext_source);
                }
            }
            _ => {}
        }
    }
}

pub(super) fn materialize_ext_output_slot<E>(
    storage: &mut GpuGKRStorage<BF, E>,
    storage_layer: usize,
    class: AddressClass,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<Option<*mut E4>>
where
    E: Field + FieldExtension<BF> + 'static,
{
    let layout = storage.layout.as_ref().expect("storage layout").clone();
    let addrs: Vec<GKRAddress> = layout
        .layers
        .get(storage_layer)
        .into_iter()
        .flat_map(|layer| layer.index.iter())
        .filter(|(_, (candidate, field, _))| *candidate == class && *field == FieldType::Ext)
        .map(|(address, _)| *address)
        .collect();
    if addrs.is_empty() {
        return Ok(None);
    }
    for address in addrs {
        let view = storage.allocate_ext_view(storage_layer, address, context)?;
        debug_assert_eq!(view.len(), trace_len);
        storage.insert_extension_at_layer(storage_layer, address, view);
    }
    Ok(Some(
        storage.layers[storage_layer].ext_class_backings[&class].as_ptr() as *mut E4,
    ))
}

pub(super) fn materialize_base_output_slot<E>(
    storage: &mut GpuGKRStorage<BF, E>,
    storage_layer: usize,
    class: AddressClass,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<Option<*mut BF>>
where
    E: Field + FieldExtension<BF> + 'static,
{
    let layout = storage.layout.as_ref().expect("storage layout").clone();
    let addrs: Vec<GKRAddress> = layout
        .layers
        .get(storage_layer)
        .into_iter()
        .flat_map(|layer| layer.index.iter())
        .filter(|(_, (candidate, field, _))| *candidate == class && *field == FieldType::Base)
        .map(|(address, _)| *address)
        .collect();
    if addrs.is_empty() {
        return Ok(None);
    }
    for address in addrs {
        let view = storage.allocate_base_view(storage_layer, address, context)?;
        debug_assert_eq!(view.len(), trace_len);
        storage.insert_base_field_at_layer(storage_layer, address, view);
    }
    Ok(Some(
        storage.layers[storage_layer].base_class_backings[&class].as_ptr() as *mut BF,
    ))
}
