//! Forward native-program oracle (spec rev-3 §5): GateK/CacheK are
//! UNINTERPRETED FUNCTIONS. The program must deliver the right operand
//! values, bound to the right payload record, gates exactly once, caches
//! >= once with identical tuples. Cache outputs are sentinels written by
//! the interpreter and assumed by the reference — a consumer reading a
//! cache cell before its CacheK fired would see zeros and fail the value
//! comparison, so produce-before-consume is checked implicitly.

use cs::definitions::GKRAddress;
use cs::gkr_compiler::codegen_ir::{ExprNode, GateKind, gate_kind_input_nodes};
use gkr_design_space::import::load_circuit;
use gkr_eval_isa::compiler::fwd::{
    CompiledForward, FwdParams, PayloadRecord, compile_forward, fwd_eligible,
};
use gkr_eval_isa::eval_ref::{self, Bf, Ext, lift, random_row};
use gkr_eval_isa::interp::{StagedSources, execute};
use gkr_eval_isa::isa::Op;
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::collections::HashMap;

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

fn base_part(v: Ext) -> Bf {
    use field::{Field, FieldExtension};
    let coeffs = <Ext as FieldExtension<Bf>>::into_coeffs(v);
    assert!(coeffs[1..].iter().all(|c| c.is_zero()), "bf source holds non-base value");
    coeffs[0]
}

fn rand_ext(rng: &mut StdRng, e4: bool) -> Ext {
    use field::FieldExtension;
    use field::PrimeField;
    let mut rb = |rng: &mut StdRng| Bf::from_u32_with_reduction(rng.random::<u32>());
    if e4 {
        <Ext as FieldExtension<Bf>>::from_coeffs([rb(rng), rb(rng), rb(rng), rb(rng)])
    } else {
        lift(rb(rng))
    }
}

fn check_layer(
    name: &str,
    li: usize,
    layer: &cs::gkr_compiler::codegen_ir::CodegenLayer,
    cf: &CompiledForward,
    seed: u64,
    exclude_max_quadratic: bool,
) {
    let arena = &layer.arena.nodes;
    let mut rng = StdRng::seed_from_u64(seed ^ ((li as u64) << 32));

    // Independent alias derivation (cross-check against the compiler's).
    let mut addr_to_cache: HashMap<GKRAddress, u16> = HashMap::new();
    for (ci, cache) in layer.caches.iter().enumerate() {
        addr_to_cache.insert(cache.out.1, ci as u16);
    }
    let mut alias: HashMap<usize, u16> = HashMap::new();
    for (i, n) in arena.iter().enumerate() {
        if let ExprNode::Place { addr, .. } = n {
            if let Some(&ci) = addr_to_cache.get(addr) {
                alias.insert(i, ci);
            }
        }
    }
    assert_eq!(alias, cf.cached_alias, "{name} L{li}: alias maps diverge");

    // Sentinels per cache — domain must match PayloadMeta.e4 (the alias Place
    // node domain the compiler uses for write_cells). Historically the cache
    // out GateOutput was stamped Ext unconditionally and could diverge from
    // the consumer Place; lower_cache now stamps per CacheKind and the
    // native_guards test pins producer/consumer agreement. PayloadMeta.e4
    // remains the right coupling: it is literally the domain the program
    // writes with.
    let sentinels: Vec<Ext> = (0..layer.caches.len())
        .map(|ci| rand_ext(&mut rng, cf.program.payloads[ci].e4))
        .collect();

    // Reference: random row, Cached places patched to their sentinels.
    let mut row = random_row(arena, &mut rng);
    for (&place, &ci) in &alias {
        row.leaf_vals[place] = Some(sentinels[ci as usize]);
    }
    let vals = eval_ref::eval_all(arena, &row);

    // Reference payload table + operand values (canonical order: caches
    // first, then eligible gates in gates -> gates_external order). The
    // operand contract is re-derived INLINE — gate_kind_input_nodes with the
    // trailing MaxQuadratic expr lane dropped — and NOT via the compiler's
    // fwd_operand_nodes, so a bug there cannot hide from this oracle.
    let mut ref_payloads: Vec<PayloadRecord> = Vec::new();
    let mut ref_operands: Vec<Vec<usize>> = Vec::new();
    let mut ref_vals: Vec<Vec<Ext>> = Vec::new();
    for cache in &layer.caches {
        ref_payloads.push(PayloadRecord::Cache(cache.clone()));
        let ops: Vec<usize> = cache.inputs.iter().map(|id| id.0 as usize).collect();
        ref_vals.push(ops.iter().map(|&n| vals[n]).collect());
        ref_operands.push(ops);
    }
    for gate in layer.gates.iter().chain(&layer.gates_external) {
        if !fwd_eligible(gate) {
            continue;
        }
        // Equal-work filter mirror (NOT the compiler's helper): the predicate
        // is re-stated inline so a compiler-side filter bug cannot hide.
        if exclude_max_quadratic && matches!(gate.kind, GateKind::MaxQuadratic { .. }) {
            continue;
        }
        ref_payloads.push(PayloadRecord::Gate(gate.clone()));
        let mut ops: Vec<usize> =
            gate_kind_input_nodes(&gate.kind).iter().map(|id| id.0 as usize).collect();
        if matches!(gate.kind, GateKind::MaxQuadratic { .. }) {
            ops.pop(); // native-flat contract: expr lane dropped
        }
        ref_vals.push(ops.iter().map(|&n| vals[n]).collect());
        ref_operands.push(ops);
    }
    // PAYLOAD BINDING: the table the program references must equal the IR,
    // and the compiler's chosen operand nodes must equal the contract.
    assert_eq!(cf.payloads, ref_payloads, "{name} L{li}: payload table mismatch");
    assert_eq!(cf.payload_operands, ref_operands, "{name} L{li}: operand contract mismatch");

    // Execute.
    let src = StagedSources {
        bf: cf.source_map.bf.iter().map(|&n| base_part(row.leaf_vals[n].unwrap())).collect(),
        e4: cf.source_map.e4.iter().map(|&n| row.leaf_vals[n].unwrap()).collect(),
        cache_outs: sentinels,
    };
    let got = execute(&cf.program, &src);

    // Group fires by payload idx.
    let mut fires: Vec<Vec<&Vec<Ext>>> = vec![Vec::new(); ref_payloads.len()];
    for f in &got.native_trace {
        fires[f.payload as usize].push(&f.vals);
    }
    for (p, rec) in ref_payloads.iter().enumerate() {
        match rec {
            PayloadRecord::Gate(_) => assert_eq!(
                fires[p].len(),
                1,
                "{name} L{li}: gate payload {p} fired {} times",
                fires[p].len()
            ),
            PayloadRecord::Cache(_) => {
                assert!(!fires[p].is_empty(), "{name} L{li}: cache payload {p} never fired");
                for f in &fires[p][1..] {
                    assert_eq!(**f, *fires[p][0], "{name} L{li}: re-fire tuple diverges");
                }
            }
        }
        for f in &fires[p] {
            assert_eq!(**f, ref_vals[p], "{name} L{li}: payload {p} operand values wrong");
        }
    }

    // Program-output copies vs sentinel-patched reference.
    for &(j, node) in &cf.outputs {
        assert_eq!(
            got.outputs[j as usize].unwrap_or_else(|| panic!("output {j} never written")),
            vals[node],
            "{name} L{li} output {j}"
        );
    }

    // Purity guard: forward programs are arithmetic-free at EVERY layer
    // (NativeK + arity-1 loads/copies only — the flat contract).
    for i in &cf.program.instrs {
        assert!(
            i.op == Op::NativeK || (i.op == Op::SumK && i.operands.len() == 1),
            "{name} L{li}: unexpected arithmetic instruction {:?}",
            i.op
        );
    }
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
                let params =
                    FwdParams { budget_cells: budget, leaf_cache: true, ..FwdParams::default() };
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
    assert!(tight_ok > 0, "no tight-budget layer compiled anywhere — spurious-panic check");
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
            FwdParams { budget_cells: 4096, leaf_cache: false, ..FwdParams::default() },
        );
        assert!(nocache.stats.src_reads > cf.stats.src_reads, "{f}: no reuse to cache?");
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
        FwdParams { exclude_max_quadratic: true, ..FwdParams::default() },
    );
    let mq = |p: &PayloadRecord| {
        matches!(p, PayloadRecord::Gate(g) if matches!(g.kind, GateKind::MaxQuadratic { .. }))
    };
    let full_mq = full.payloads.iter().filter(|p| mq(p)).count();
    assert!(full_mq > 0, "fixture lost its MaxQuadratic gates?");
    assert_eq!(filtered.payloads.iter().filter(|p| mq(p)).count(), 0);
    // Everything else survives: payload count differs by exactly the MQ gates.
    assert_eq!(filtered.payloads.len(), full.payloads.len() - full_mq);
    // Filtered program still passes the full oracle.
    check_layer("shift_binop[filtered]", 0, layer, &filtered, 0xF11, true);
}
