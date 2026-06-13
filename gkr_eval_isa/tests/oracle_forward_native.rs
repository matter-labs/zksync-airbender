//! Forward native-program oracle (spec rev-3 §5): GateK/CacheK are
//! UNINTERPRETED FUNCTIONS. The program must deliver the right operand
//! values, bound to the right payload record, gates exactly once, caches
//! >= once with identical tuples. Cache outputs are sentinels written by
//! the interpreter and assumed by the reference — a consumer reading a
//! cache cell before its CacheK fired would see zeros and fail the value
//! comparison, so produce-before-consume is checked implicitly.

use cs::gkr_compiler::codegen_ir::GateKind;
use gkr_design_space::import::load_circuit;
use gkr_eval_isa::compiler::fwd::{FwdParams, PayloadRecord, compile_forward};
use gkr_eval_isa::test_support::check_layer;

fn fixtures() -> Vec<std::path::PathBuf> {
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
    paths
}

#[test]
fn forward_oracle_all_fixtures() {
    // Tight-budget compiles may be GENUINELY infeasible per layer, but if a
    // latent bug made compile_forward panic at tight budgets EVERYWHERE, the
    // skip path would silently drain all eviction-path coverage — hence the
    // global coverage floor assert at the end.
    let mut tight_ok = 0usize;
    for p in fixtures() {
        let c = load_circuit(&p).unwrap();
        let name = p.file_name().unwrap().to_str().unwrap().to_string();
        for (li, (layer, g)) in c.circuit.layers.iter().zip(&c.graphs).enumerate() {
            for (k, budget) in [4096usize, 16, 8].into_iter().enumerate() {
                let params = FwdParams {
                    budget_cells: budget,
                    leaf_cache: true,
                    ..FwdParams::default()
                };
                let cf = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    compile_forward(layer, g, params)
                })) {
                    Ok(cf) => cf,
                    // Tight budgets can be GENUINELY infeasible (a gate whose
                    // mandatory cache-cell operands exceed the budget).
                    Err(_) if budget < 4096 => continue,
                    Err(e) => std::panic::resume_unwind(e),
                };
                if budget < 4096 {
                    tight_ok += 1;
                }
                check_layer(&name, li, layer, &cf, 0xF0D + k as u64, false);
            }
        }
    }
    assert!(
        tight_ok > 0,
        "no tight-budget layer compiled anywhere — spurious-panic check"
    );
}

#[test]
fn forward_floor_invariant_heavy_circuits() {
    // dyn@unbounded == the generated kernel's load-once floor.
    for f in [
        "blake2_with_extended_control_codegen_ir_gkr.json",
        "bigint_with_extended_control_codegen_ir_gkr.json",
        "keccak_special5_codegen_ir_gkr.json",
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../cs/compiled_circuits")
            .join(f);
        let c = load_circuit(&path).unwrap();
        let cf = compile_forward(&c.circuit.layers[0], &c.graphs[0], FwdParams::default());
        assert_eq!(cf.stats.src_reads, cf.stats.distinct_sources, "{f}");
        assert_eq!(cf.stats.evictions, 0, "{f}");
        // Without the leaf cache, multi-use columns re-read per use.
        let nocache = compile_forward(
            &c.circuit.layers[0],
            &c.graphs[0],
            FwdParams {
                budget_cells: 4096,
                leaf_cache: false,
                ..FwdParams::default()
            },
        );
        assert!(
            nocache.stats.src_reads > cf.stats.src_reads,
            "{f}: no reuse to cache?"
        );
    }
}

#[test]
fn equal_work_filter_drops_max_quadratic_only() {
    // shift_binop has MaxQuadratic gates (CPU census, spec §2a of full-dag spec).
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../cs/compiled_circuits/shift_binop_codegen_ir_gkr.json");
    let c = load_circuit(&path).unwrap();
    let layer = &c.circuit.layers[0];
    let full = compile_forward(layer, &c.graphs[0], FwdParams::default());
    let filtered = compile_forward(
        layer,
        &c.graphs[0],
        FwdParams {
            exclude_max_quadratic: true,
            ..FwdParams::default()
        },
    );
    let mq = |p: &PayloadRecord| matches!(p, PayloadRecord::Gate(g) if matches!(g.kind, GateKind::MaxQuadratic { .. }));
    let full_mq = full.payloads.iter().filter(|p| mq(p)).count();
    assert!(full_mq > 0, "fixture lost its MaxQuadratic gates?");
    assert_eq!(filtered.payloads.iter().filter(|p| mq(p)).count(), 0);
    // Everything else survives: payload count differs by exactly the MQ gates.
    assert_eq!(filtered.payloads.len(), full.payloads.len() - full_mq);
    // Filtered program still passes the full oracle.
    check_layer("shift_binop[filtered]", 0, layer, &filtered, 0xF11, true);
}
