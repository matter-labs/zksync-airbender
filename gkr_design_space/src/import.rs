//! Load a codegen-IR JSON artifact and build per-layer analysis graphs.

use crate::graph::AnalysisGraph;
use cs::gkr_compiler::CodegenCircuit;
use std::path::Path;

pub struct LoadedCircuit {
    pub circuit: CodegenCircuit,
    pub graphs: Vec<AnalysisGraph>,
}

pub fn load_circuit(path: &Path) -> Result<LoadedCircuit, String> {
    let text =
        std::fs::read_to_string(path).map_err(|e| format!("read {}: {e}", path.display()))?;
    let circuit: CodegenCircuit =
        serde_json::from_str(&text).map_err(|e| format!("parse {}: {e}", path.display()))?;
    let graphs = circuit
        .layers
        .iter()
        .map(AnalysisGraph::from_layer)
        .collect();
    Ok(LoadedCircuit { circuit, graphs })
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    pub(crate) fn fixture(name: &str) -> std::path::PathBuf {
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../cs/compiled_circuits")
            .join(name)
    }

    #[test]
    fn loads_add_sub_cached_fixture() {
        let c = load_circuit(&fixture("add_sub_lui_auipc_mop_codegen_ir_gkr.json")).unwrap();
        assert_eq!(c.graphs.len(), 4);
        assert_eq!(c.graphs[0].nodes.len(), 224);
        assert_eq!(c.circuit.layers[0].gates.len(), 45);
        assert_eq!(c.circuit.layers[0].caches.len(), 16);
        assert!(c.circuit.globals.trace_len > 0);
    }
}
