use std::collections::HashMap;

use gkr_eval_ir::{DagCircuit, FieldKind, ReadPlace, SinkInfo, SinkKind};

/// Resolve every cross-layer read to the field of the sink that produced it.
///
/// This is circuit analysis shared by the forward and backward compilers; it
/// carries no GPU scheduling policy.
pub fn build_cross_layer_field_map(circuit: &DagCircuit) -> HashMap<ReadPlace, FieldKind> {
    let mut map = HashMap::new();
    for layer in &circuit.layers {
        for root in &layer.roots {
            if let Some(SinkInfo { kind, field }) = root.materialize.as_ref() {
                match *kind {
                    SinkKind::Inner { layer, offset } => {
                        map.insert(ReadPlace::LayerOutput { layer, offset }, *field);
                    }
                    SinkKind::Cache { layer, offset } => {
                        map.insert(ReadPlace::CacheOutput { layer, offset }, *field);
                    }
                    SinkKind::Export { .. } | SinkKind::Scratch { .. } => {}
                }
            }
        }
    }
    map
}
