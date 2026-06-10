use gkr_design_space::analysis::{depth::depth_stats, schedule, working_set::layer_working_set};
use gkr_design_space::import::load_circuit;
use std::path::PathBuf;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../cs/compiled_circuits")
        .join(name)
}

const FIXTURES: [&str; 4] = [
    "add_sub_lui_auipc_mop_codegen_ir_gkr.json",
    "add_sub_lui_auipc_mop_codegen_ir_no_caches_gkr.json",
    "blake2_with_extended_control_codegen_ir_gkr.json",
    "blake2_with_extended_control_codegen_ir_no_caches_gkr.json",
];

#[test]
fn all_fixtures_satisfy_graph_invariants() {
    for f in FIXTURES {
        let c = load_circuit(&fixture(f)).unwrap_or_else(|e| panic!("{f}: {e}"));
        for (li, g) in c.graphs.iter().enumerate() {
            // children strictly precede parents (topological arena)
            for (i, n) in g.nodes.iter().enumerate() {
                for &ch in &n.children {
                    assert!(ch < i, "{f} layer {li}: edge {i}->{ch} not topological");
                }
            }
            // every output slot points at a real node
            for o in &g.outputs {
                assert!(o.node < g.nodes.len(), "{f} layer {li}: dangling output");
            }
            // passes run without panicking on every layer
            let ws = layer_working_set(g);
            let d = depth_stats(g);
            let arena = schedule::simulate(g, schedule::Order::Arena);
            let sched = schedule::simulate(g, schedule::Order::PressureAware);
            assert!(
                sched.max_live_bytes <= arena.max_live_bytes,
                "{f} layer {li}: scheduler increased pressure"
            );
            assert!(d.max_depth as usize <= g.nodes.len());
            let _ = ws;
        }
    }
}

#[test]
fn blake2_layer0_known_sizes() {
    let c = load_circuit(&fixture(FIXTURES[2])).unwrap();
    assert_eq!(c.graphs.len(), 8);
    assert_eq!(c.graphs[0].nodes.len(), 3576);
    assert_eq!(c.circuit.layers[0].gates.len(), 547);
    assert_eq!(c.circuit.layers[0].caches.len(), 382);
}
