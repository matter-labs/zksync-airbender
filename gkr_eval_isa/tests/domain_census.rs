//! Domain census + guard: FORWARD programs are pure bf in the current
//! eval-core boundary. The forward PASS does carry e4 values everywhere —
//! grand-product / lookup-fraction gates produce Ext GateOutputs at layer k
//! that layer k+1 consumes — but `resolve(addr, Domain::Ext)` always yields a
//! single leaf node (Place or produced GateOutput), never an expression cone,
//! and the bf operands feeding those gates (mem tuples, lookup columns) are
//! lowered at Domain::Base. So all e4 arithmetic rides the NATIVE gate path
//! via staged source descriptors and never touches program cells.
//!
//! If this test ever fails, the budget-sweep numbers change meaning: program
//! state would hold 4-cell e4 values and every cell budget interpretation
//! (pinning widths, max_live, access concentration) must be revisited.

use cs::gkr_compiler::codegen_ir::{Domain, ExprNode};
use gkr_design_space::import::load_circuit;
use gkr_eval_isa::compiler::view;

#[test]
fn forward_programs_are_pure_bf() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits");
    let mut paths: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| {
            let p = e.unwrap().path();
            p.file_name()?.to_str()?.contains("codegen_ir").then_some(p)
        })
        .collect();
    paths.sort();
    assert_eq!(paths.len(), 22, "expected 22 IR fixtures");

    for p in &paths {
        let c = load_circuit(p).unwrap();
        let name = p.file_name().unwrap().to_str().unwrap();
        for (li, (layer, g)) in c.circuit.layers.iter().zip(&c.graphs).enumerate() {
            let arena = &layer.arena.nodes;
            let pv = view::build(layer, g);
            let mut native_ext_leaves = 0usize;
            for (i, n) in arena.iter().enumerate() {
                let ext = matches!(
                    n,
                    ExprNode::Place { domain: Domain::Ext, .. }
                        | ExprNode::GateOutput { domain: Domain::Ext, .. }
                        | ExprNode::Sum { domain: Domain::Ext, .. }
                        | ExprNode::Product { domain: Domain::Ext, .. }
                );
                if !ext {
                    continue;
                }
                // Ext values exist only as leaves consumed natively by gates.
                assert!(
                    matches!(n, ExprNode::Place { .. } | ExprNode::GateOutput { .. }),
                    "{name} L{li} node {i}: Ext expression in arena — program-side e4"
                );
                assert_eq!(
                    pv.uses[i], 0,
                    "{name} L{li} node {i}: Ext leaf used by the program"
                );
                native_ext_leaves += 1;
            }
            for &(_, n) in &pv.program_outputs {
                assert!(
                    !matches!(
                        arena[n],
                        ExprNode::Sum { domain: Domain::Ext, .. }
                            | ExprNode::Product { domain: Domain::Ext, .. }
                            | ExprNode::Place { domain: Domain::Ext, .. }
                            | ExprNode::GateOutput { domain: Domain::Ext, .. }
                    ),
                    "{name} L{li}: Ext program output"
                );
            }
            if li == 0 {
                println!("{name}: {native_ext_leaves} native-side ext leaves at L0");
            }
        }
    }
}
