//! M0 sizing spike (spec §3 decision point): sweep `analysis::size_layer`
//! over every forward layer of every fixture, plus one backward row per
//! fixture (Ext-regime distill of L0, the hot layer), and print the table
//! the M0 report is built from.
//!
//! Run: RUSTFLAGS="-Awarnings" cargo test -p gkr_flatten --release --test m0_sizing -- --ignored --nocapture

use cs::gkr_compiler::dag_ir::{BwdRegime, ExprId};
use gkr_eval_isa::bwd::distill::distill;
use gkr_flatten::analysis::size_layer;
use gkr_flatten::dag::LayerView;
use gkr_flatten::fixtures::{load_circuit, FIXTURES};

#[test]
#[ignore = "release-only sizing sweep over all fixtures"]
fn m0_sizing_report() {
    println!("pass fixture layer roots nodes sites depth peak floor ceiling");
    for name in FIXTURES {
        let (dag, cross) = load_circuit(name);
        for (li, layer) in dag.layers.iter().enumerate() {
            let view = LayerView { layer, cross: &cross, overrides: None };
            let roots: Vec<ExprId> = layer.roots.iter().map(|r| r.expr).collect();
            let r = size_layer(&view, &roots);
            println!(
                "fwd {name} L{li} {} {} {} {} {} {} {}",
                r.roots, r.dag_nodes, r.sites, r.max_depth, r.peak, r.floor, r.ceiling
            );
            assert!(r.floor as u128 <= r.ceiling, "bracket violated: fwd {name} L{li}");
        }

        // bwd: Ext-regime distill of L0 (the hot layer).
        let d = distill(&dag.layers[0], BwdRegime::Ext, &cross, None);
        let bview = LayerView {
            layer: &d.layer,
            cross: &d.cross_fields,
            overrides: Some(&d.field_overrides),
        };
        let root = d.layer.roots[d.root.0 as usize].expr;
        let r = size_layer(&bview, &[root]);
        println!(
            "bwd {name} L0 {} {} {} {} {} {} {}",
            r.roots, r.dag_nodes, r.sites, r.max_depth, r.peak, r.floor, r.ceiling
        );
        assert!(r.floor as u128 <= r.ceiling, "bracket violated: bwd {name} L0");
    }
}
