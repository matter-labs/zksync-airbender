use era_cudart::result::CudaResult;
use gpu_core::primitives::field::BF;
use gpu_prover_context::ProverContext;

use crate::gkr_address_audit::AddressClass;
use crate::storage_layout::FieldType;
use crate::upstream::{Field, FieldExtension, GKRAddress, GKRLayerDescription, GKRRelation};
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
            GKRRelation::CopyInBaseField { input, output } => {
                assert_eq!(gate.output_layer, layer_idx + 1);
                let out_layer = layer_idx + 1;
                let source = storage
                    .try_get_base_poly(*input)
                    .expect("base-field copy source must exist")
                    .clone_shared();
                storage.insert_base_field_at_layer(out_layer, *output, source);
            }
            GKRRelation::CopyInExtensionField { input, output } => {
                assert_eq!(gate.output_layer, layer_idx + 1);
                let out_layer = layer_idx + 1;
                let source = storage.get_ext_poly(*input).clone_shared();
                storage.insert_extension_at_layer(out_layer, *output, source);
            }
            _ => {}
        }
    }
}

pub(super) fn materialize_output_slot<E>(
    storage: &mut GpuGKRStorage<BF, E>,
    storage_layer: usize,
    class: AddressClass,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: Field + FieldExtension<BF> + 'static,
{
    let layout = storage.layout.as_ref().expect("storage layout").clone();
    let outputs: Vec<(GKRAddress, FieldType)> = layout
        .layers
        .get(storage_layer)
        .into_iter()
        .flat_map(|layer| layer.index.iter())
        .filter(|(_, (candidate, _, _))| *candidate == class)
        .map(|(address, (_, field, _))| (*address, *field))
        .collect();
    for (address, field) in outputs {
        match field {
            FieldType::Base => {
                let view = storage.allocate_base_view(storage_layer, address, context)?;
                debug_assert_eq!(view.len(), trace_len);
                storage.insert_base_field_at_layer(storage_layer, address, view);
            }
            FieldType::Ext => {
                let view = storage.allocate_ext_view(storage_layer, address, context)?;
                debug_assert_eq!(view.len(), trace_len);
                storage.insert_extension_at_layer(storage_layer, address, view);
            }
        }
    }
    Ok(())
}
