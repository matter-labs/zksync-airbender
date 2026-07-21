//! Appends per-round dim-reducing tower layers past the artifact's last
//! storage layer.

use std::collections::BTreeMap;

use crate::address_audit::AddressClass;
use crate::upstream::{GKRAddress, GKRCircuitArtifact, OutputType, PrimeField};

use super::types::{FieldType, GpuGKRLayerLayout, StorageSlot};

/// Append per-tower-layer `GpuGKRLayerLayout` entries to `layers`, mirroring
/// the address derivation in
/// `gpu_circuit_prover::prover::gkr::backward::derive_dimension_reducing_inputs`
/// and the output assignment in
/// `gpu_circuit_prover::prover::gkr::forward::lower_dimension_reducing_forward_round`.
///
/// Tower layer N (relative to the artifact's last storage layer) holds polys
/// of size `1 << (initial_trace_log_2 - 1 - N)` (one halving per round).
/// All tower outputs are extension-field `InnerLayer { layer, offset }` with
/// `AddressClass::ThisLayerInnerLayerWrite` (since `addr.layer == output_layer`
/// in `classify`'s sense). Sequential `offset` per layer maps directly to
/// `poly_idx`.
pub(super) fn append_tower_layers<F: PrimeField>(
    layers: &mut Vec<GpuGKRLayerLayout>,
    artifact: &GKRCircuitArtifact<F>,
    initial_trace_log_2: usize,
    final_trace_log_2: usize,
) {
    let total_rounds = initial_trace_log_2.saturating_sub(final_trace_log_2);
    if total_rounds == 0 {
        return;
    }
    // Tower starts one storage layer past the artifact's last input layer.
    // `schedule_dimension_reduction_forward` is called with
    // `initial_layer_idx = compiled_circuit.layers.len()` and writes round 0's
    // outputs at `output_layer = initial_layer_idx + 1`. The artifact-driven
    // layout already covers up to `compiled_circuit.layers.len()`, so the
    // first new layer to allocate is `compiled_circuit.layers.len() + 1`.
    let initial_layer_idx = artifact.layers.len();

    let mut layer_inputs: BTreeMap<OutputType, Vec<GKRAddress>> =
        artifact.global_output_map.clone();
    for round in 0..total_rounds {
        // `output_layer` advances by exactly one storage layer per round past
        // `initial_layer_idx`; no separate running counter is needed.
        let output_layer = initial_layer_idx + round + 1;
        let input_size_log_2 = initial_trace_log_2 - round;
        let output_log2_stride = (input_size_log_2 - 1) as u32;

        let mut new_layer_layout = GpuGKRLayerLayout {
            log2_stride: output_log2_stride,
            ..GpuGKRLayerLayout::default()
        };
        let mut output_idx: u32 = 0;
        let mut next_inputs: BTreeMap<OutputType, Vec<GKRAddress>> = BTreeMap::new();

        for (arg_type, inputs) in layer_inputs.iter() {
            assert_eq!(
                inputs.len(),
                2,
                "dim reduction tower expects 2 inputs per slot for {:?}",
                arg_type,
            );
            let out_a = GKRAddress::InnerLayer {
                layer: output_layer,
                offset: output_idx as usize,
            };
            let poly_idx_a = output_idx;
            output_idx += 1;
            let out_b = GKRAddress::InnerLayer {
                layer: output_layer,
                offset: output_idx as usize,
            };
            let poly_idx_b = output_idx;
            output_idx += 1;

            let class = AddressClass::ThisLayerInnerLayerWrite;
            let field = FieldType::Ext;
            new_layer_layout
                .index
                .insert(out_a, (class, field, poly_idx_a));
            new_layer_layout
                .index
                .insert(out_b, (class, field, poly_idx_b));
            next_inputs.insert(*arg_type, vec![out_a, out_b]);
        }
        if output_idx > 0 {
            new_layer_layout.slot_poly_counts.insert(
                StorageSlot {
                    class: AddressClass::ThisLayerInnerLayerWrite,
                    field: FieldType::Ext,
                },
                output_idx,
            );
        }

        // Resize layers vector to cover `output_layer`. The tower layout's
        // `log2_stride` carries the round-specific size — earlier (artifact)
        // strides do not apply to these fresh per-round outputs.
        if output_layer >= layers.len() {
            layers.resize_with(output_layer + 1, GpuGKRLayerLayout::default);
        }
        layers[output_layer] = new_layer_layout;

        layer_inputs = next_inputs;
    }
}
