use std::collections::BTreeMap;

use crate::upstream::{DimensionReducingInputOutput, GKRAddress, OutputType};

/// Structural variant of `prepare_dimension_reduction_forward`'s
/// `dimension_reduction_description` output: replicates the address-only
/// portion of the per-round lowering in
/// `gpu/gkr/src/forward/dimension_reducing.rs`'s
/// `lower_dimension_reducing_forward_round` without scheduling any GPU work.
///
/// Address-assignment rules (matched exactly):
/// - Each round walks `layer_inputs.iter()` (BTreeMap → ordered by `OutputType`).
/// - Both `PermutationProduct` and `Lookup*` arg types emit two output addresses
///   per slot (`InnerLayer { layer: output_layer, offset: output_idx }` then
///   `output_idx += 1`), so the offset assignment is purely positional.
/// - Round 0's `layer_inputs` is `compiled_circuit.global_output_map`; subsequent
///   rounds chain from the previous round's `output`.
///
/// Used to size the proof slab before forward runs.
pub(crate) fn derive_dimension_reducing_inputs(
    initial_layer_idx: usize,
    initial_output_map: &BTreeMap<OutputType, Vec<GKRAddress>>,
    initial_trace_log_2: u32,
    final_trace_log_2: u32,
) -> BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>> {
    let mut result: BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>> =
        BTreeMap::new();
    let total_rounds = initial_trace_log_2.saturating_sub(final_trace_log_2);
    if total_rounds == 0 {
        return result;
    }
    let mut layer_inputs: BTreeMap<OutputType, Vec<GKRAddress>> = initial_output_map.clone();

    for (layer_offset, _) in (0..total_rounds).enumerate() {
        let current_layer_idx = initial_layer_idx + layer_offset;
        let output_layer = current_layer_idx + 1;
        let mut output_idx = 0usize;
        let mut layer_description: BTreeMap<OutputType, DimensionReducingInputOutput> =
            BTreeMap::new();

        for (arg_type, inputs) in layer_inputs.iter() {
            assert_eq!(
                inputs.len(),
                2,
                "dim reduction expects 2 inputs per slot for {:?}",
                arg_type,
            );
            let out_a = GKRAddress::InnerLayer {
                layer: output_layer,
                offset: output_idx,
            };
            output_idx += 1;
            let out_b = GKRAddress::InnerLayer {
                layer: output_layer,
                offset: output_idx,
            };
            output_idx += 1;
            layer_description.insert(
                *arg_type,
                DimensionReducingInputOutput {
                    inputs: inputs.clone(),
                    output: vec![out_a, out_b],
                },
            );
        }

        layer_inputs = layer_description
            .iter()
            .map(|(k, v)| (*k, v.output.clone()))
            .collect();

        result.insert(current_layer_idx, layer_description);
    }
    result
}
