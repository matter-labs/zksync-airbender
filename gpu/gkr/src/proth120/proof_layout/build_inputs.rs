use std::collections::BTreeSet;

use crate::proth120::programs::GkrProgramsPr;
use crate::upstream::GKRAddress;

pub(crate) struct LayerDimsPr {
    pub layer_idx: usize,
    pub rounds: usize,
    pub degree: usize,
    pub inputs: Vec<GKRAddress>,
    pub extras: Vec<GKRAddress>,
}

pub(crate) fn layers(programs: &GkrProgramsPr, final_log: usize) -> Vec<LayerDimsPr> {
    let circuit = &programs.runtime_circuit;
    let trace_log = circuit.trace_len.trailing_zeros() as usize;
    let dr = crate::backward::derive_dimension_reducing_inputs(
        circuit.layers.len(),
        &circuit.global_output_map,
        trace_log as u32,
        final_log as u32,
    );
    let mut result = Vec::new();
    for (layer_idx, map) in dr.iter().rev() {
        result.push(LayerDimsPr {
            layer_idx: *layer_idx,
            rounds: final_log + result.len(),
            degree: 2,
            inputs: map
                .values()
                .flat_map(|io| io.inputs.iter().copied())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect(),
            extras: vec![],
        });
    }
    for layer_idx in (0..circuit.layers.len()).rev() {
        let protocol = |address| {
            crate::transform::logical_protocol_address(address, &circuit.scratch_space_mapping_rev)
        };
        let inputs: BTreeSet<_> = programs.backward_layers[layer_idx]
            .inputs
            .iter()
            .copied()
            .filter(|a| *a != GKRAddress::placeholder())
            .map(protocol)
            .collect();
        let extras = circuit.layers[layer_idx]
            .cached_relations
            .values()
            .flat_map(|r| r.dependencies())
            .map(protocol)
            .filter(|a| !inputs.contains(a))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        result.push(LayerDimsPr {
            layer_idx,
            rounds: trace_log,
            degree: 1,
            inputs: inputs.into_iter().collect(),
            extras,
        });
    }
    result
}
