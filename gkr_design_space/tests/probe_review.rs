//! TEMP review probe (delete after review): empirically check classification
//! of the fixture against the GPU round-0 semantics.
use cs::definitions::GKRAddress;
use cs::gkr_compiler::codegen_ir::{GateKind, gate_kind_input_nodes};
use gkr_design_space::graph::Origin;
use gkr_design_space::import::load_circuit;

fn fixture(name: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../cs/compiled_circuits")
        .join(name)
}

#[test]
fn probe() {
    let c = load_circuit(&fixture("add_sub_lui_auipc_mop_codegen_ir_gkr.json")).unwrap();
    for (li, (layer, g)) in c.circuit.layers.iter().zip(&c.graphs).enumerate() {
        let mut kind_counts: std::collections::BTreeMap<&'static str, usize> = Default::default();
        for gate in layer.gates_external.iter().chain(layer.gates.iter()) {
            let name: &'static str = match &gate.kind {
                GateKind::LinearBaseField { .. } => "LinearBaseField",
                GateKind::MaxQuadratic { .. } => "MaxQuadratic",
                GateKind::EnforceSingleMaxQuadraticConstraint { .. } => "EnforceSingleMaxQuad",
                GateKind::EnforceConstraintsMaxQuadratic { .. } => "EnforceConstraintsMaxQuad",
                GateKind::CopyInBaseField { .. } => "CopyInBaseField",
                GateKind::CopyInExtensionField { .. } => "CopyInExtensionField",
                GateKind::MaterializeSingleLookupInput { .. } => "MaterializeSingleLookupInput",
                GateKind::MaterializeGrandProductTermExpression { .. } => "MaterializeGPTerm",
                GateKind::TrivialProduct { .. } => "TrivialProduct",
                GateKind::InitialGrandProductFromCaches { .. } => "InitGPFromCaches",
                GateKind::InitialGrandProductWithoutCaches { .. } => "InitGPWithoutCaches",
                GateKind::MaskIntoIdentityProduct { .. } => "MaskIntoIdentityProduct",
                GateKind::LookupWithCachedDensAndSetup { .. } => "LookupWithCachedDensAndSetup",
                _ => "OtherLookup",
            };
            *kind_counts.entry(name).or_default() += 1;
        }
        // virtual operand count
        let mut virt_nodes = 0usize;
        let mut cached_place = 0usize;
        let mut scratch_place = 0usize;
        for n in &g.nodes {
            match n.origin {
                Origin::InputColumn(GKRAddress::VirtualSetup(_)) => virt_nodes += 1,
                Origin::CachedColumn(_) => cached_place += 1,
                Origin::Scratch(_) => scratch_place += 1,
                _ => {}
            }
        }
        // gate operands that resolve to GateOutput nodes (same-layer produced)
        let mut gateout_operands = 0usize;
        for gate in layer.gates_external.iter().chain(layer.gates.iter()) {
            for id in gate_kind_input_nodes(&gate.kind) {
                let n = &g.nodes[id.0 as usize];
                if matches!(n.origin, Origin::Computed)
                    && g.outputs.iter().any(|o| o.node == id.0 as usize)
                {
                    gateout_operands += 1;
                }
            }
        }
        // prefill outputs
        let prefill = g.outputs.iter().filter(|o| o.prefill).count();
        // copy/linear gate input columns (round-0 overcount candidates)
        let mut copylin_inputs = std::collections::HashSet::new();
        for gate in layer.gates_external.iter().chain(layer.gates.iter()) {
            match &gate.kind {
                GateKind::LinearBaseField { .. }
                | GateKind::CopyInBaseField { .. }
                | GateKind::CopyInExtensionField { .. }
                | GateKind::MaterializeSingleLookupInput { .. } => {
                    for id in gate_kind_input_nodes(&gate.kind) {
                        copylin_inputs.insert(id.0);
                    }
                }
                _ => {}
            }
        }
        println!(
            "layer {li}: kinds={kind_counts:?} virt_nodes={virt_nodes} cached_place={cached_place} scratch_place={scratch_place} gateout_operands={gateout_operands} prefill_outputs={prefill} copylin_input_nodes={}",
            copylin_inputs.len()
        );
        // cache same-layer consumption check
        for cache in &layer.caches {
            let addr = cache.out.1;
            let consumed_here = g
                .nodes
                .iter()
                .any(|n| matches!(n.origin, Origin::CachedColumn(a) if a == addr));
            if !consumed_here {
                println!("  cache {addr:?} NOT consumed as Place in producing layer");
            }
        }
    }
}
