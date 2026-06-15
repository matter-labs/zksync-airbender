//! Forward-oracle point-local check, factored out so consumers (the
//! `gkr_eval_isa` integration tests AND a downstream GPU bench harness in
//! `circuit_prover`) can call the SAME per-point CPU oracle.
//!
//! `#[doc(hidden)] pub` (not `#[cfg(test)]`): a dependency's `cfg(test)` items
//! are invisible to consumers, so a cross-crate test helper must be part of the
//! real public surface — matching the `gpu_ops` test-helper precedent in
//! `gpu/AGENTS.md`. `#[doc(hidden)]` keeps it out of rendered docs.
//!
//! GateK/CacheK are UNINTERPRETED FUNCTIONS (spec rev-3 §5). The program must
//! deliver the right operand values, bound to the right payload record, gate
//! exactly once, cache >= once with identical tuples. Cache outputs are
//! sentinels written by the interpreter and assumed by the reference — a
//! consumer reading a cache cell before its CacheK fired would see zeros and
//! fail the value comparison, so produce-before-consume is checked implicitly.

/// Absolute path to a fixture under `cs/compiled_circuits/`. Shared by in-crate
/// unit tests AND integration tests (the `eval_ref::tests::fixture` helper is
/// `#[cfg(test)] pub(crate)` and is NOT visible cross-crate).
#[doc(hidden)]
pub fn fixture_path(name: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../cs/compiled_circuits")
        .join(name)
}

/// All 22 `codegen_ir` fixtures, sorted.
#[doc(hidden)]
pub fn all_fixtures() -> Vec<std::path::PathBuf> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits");
    let mut paths: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| {
            let p = e.unwrap().path();
            p.file_name()?.to_str()?.contains("codegen_ir").then_some(p)
        })
        .collect();
    paths.sort();
    paths
}

use crate::compiler::fwd::{CompiledForward, PayloadRecord, fwd_eligible};
use crate::eval_ref::{self, Bf, Ext, lift, random_row};
use crate::interp::{StagedSources, execute};
use crate::isa::Op;
use cs::definitions::GKRAddress;
use cs::gkr_compiler::codegen_ir::{CodegenLayer, Domain, ExprNode, ForwardSource, GateKind, gate_kind_input_nodes};
use cs::gkr_compiler::InitsOrTeardownsTimestampAndValue;
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::collections::HashMap;

/// Union of every address a v2 program reads OR writes for one layer, annotated
/// with its field/domain. `GKRAddress` alone does NOT encode base-vs-ext; the
/// field lives in the IR node context. The single source-of-truth collector
/// (MatrixTable in a later task builds its per-backing field from this).
#[doc(hidden)]
pub fn collect_v2_address_refs(layer: &CodegenLayer) -> Vec<(GKRAddress, Domain)> {
    let arena = &layer.arena.nodes;
    let mut out: Vec<(GKRAddress, Domain)> = Vec::new();

    // SOURCES: every Place node carries its own address and domain directly.
    for n in arena {
        if let ExprNode::Place { addr, domain } = n {
            out.push((*addr, *domain));
        }
    }

    // DESTINATIONS — recover domain from the producing GateOutput node in the
    // arena, which is always a GateOutput { domain, .. }.
    //
    // Cache outs: cache.out = (NodeId, GKRAddress).
    for cache in &layer.caches {
        let (node_id, addr) = cache.out;
        let domain = match &arena[node_id.0 as usize] {
            ExprNode::GateOutput { domain, .. } => *domain,
            _ => Domain::Base, // defensive; IR invariant: cache out is always GateOutput
        };
        out.push((addr, domain));
    }

    // Gate dst slots (gates + gates_external): each OutputSlot has a node (the
    // GateOutput) and an addr.
    for gate in layer.gates.iter().chain(&layer.gates_external) {
        for slot in &gate.dst {
            let domain = match &arena[slot.node.0 as usize] {
                ExprNode::GateOutput { domain, .. } => *domain,
                _ => Domain::Base, // defensive; IR invariant: dst is always GateOutput
            };
            out.push((slot.addr, domain));
        }
    }

    // R4: the id-20 InitsOrTeardownsInitialPair Teardown arm reads lhs/rhs
    // timestamp+value BaseLayerMemory columns that live INSIDE the
    // `timestamp_and_value` enum — the cs lowering does NOT resolve them into
    // arena Place nodes (only `setup` is), so the source walk above misses them.
    // Collect them explicitly so the matrix table backs them. (The Init arm
    // carries none; the setup polys are arena Place nodes already collected.)
    for gate in layer.gates.iter().chain(&layer.gates_external) {
        if let GateKind::InitsOrTeardownsInitialPair { timestamp_and_value, .. } = &gate.kind {
            if let InitsOrTeardownsTimestampAndValue::Teardown {
                lhs_timestamp,
                lhs_value,
                rhs_timestamp,
                rhs_value,
            } = timestamp_and_value
            {
                for &off in lhs_timestamp
                    .iter()
                    .chain(lhs_value)
                    .chain(rhs_timestamp)
                    .chain(rhs_value)
                {
                    out.push((GKRAddress::BaseLayerMemory(off), Domain::Base));
                }
            }
        }
    }

    out
}

/// Column-only view for the R3 gate. Thin wrapper over the annotated collector
/// — one underlying walk, so the gate and any later table can't diverge.
#[doc(hidden)]
pub fn collect_v2_addresses(layer: &CodegenLayer) -> Vec<GKRAddress> {
    collect_v2_address_refs(layer).into_iter().map(|(a, _)| a).collect()
}

/// Per-address column offset within its backing; mirrors the v1 `safe_offset`
/// (returns 0 for VirtualSetup, whose `offset()` panics).
#[doc(hidden)]
pub fn column_offset(addr: &GKRAddress) -> u32 {
    match addr {
        GKRAddress::VirtualSetup(_) => 0,
        other => other.offset() as u32,
    }
}

#[doc(hidden)]
pub fn base_part(v: Ext) -> Bf {
    use field::{Field, FieldExtension};
    let coeffs = <Ext as FieldExtension<Bf>>::into_coeffs(v);
    assert!(
        coeffs[1..].iter().all(|c| c.is_zero()),
        "bf source holds non-base value"
    );
    coeffs[0]
}

#[doc(hidden)]
pub fn rand_ext(rng: &mut StdRng, e4: bool) -> Ext {
    use field::FieldExtension;
    use field::PrimeField;
    let mut rb = |rng: &mut StdRng| Bf::from_u32_with_reduction(rng.random::<u32>());
    if e4 {
        <Ext as FieldExtension<Bf>>::from_coeffs([rb(rng), rb(rng), rb(rng), rb(rng)])
    } else {
        lift(rb(rng))
    }
}

#[doc(hidden)]
pub fn check_layer(
    name: &str,
    li: usize,
    layer: &cs::gkr_compiler::codegen_ir::CodegenLayer,
    cf: &CompiledForward,
    seed: u64,
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
        // Production-faithful skip mirror (NOT the compiler's helper): the
        // predicate is re-stated inline so a compiler-side filter bug cannot
        // hide. A gate whose every output is scratch-prefilled (witness-stage
        // precomputed) is read from scratch, never computed forward — exactly
        // what the program must omit to match production.
        if gate.dst.iter().all(|s| matches!(s.forward_source, ForwardSource::ScratchPrefill)) {
            continue;
        }
        ref_payloads.push(PayloadRecord::Gate(gate.clone()));
        let mut ops: Vec<usize> = gate_kind_input_nodes(&gate.kind)
            .iter()
            .map(|id| id.0 as usize)
            .collect();
        if matches!(gate.kind, GateKind::MaxQuadratic { .. }) {
            ops.pop(); // native-flat contract: expr lane dropped
        }
        ref_vals.push(ops.iter().map(|&n| vals[n]).collect());
        ref_operands.push(ops);
    }
    // PAYLOAD BINDING: the table the program references must equal the IR,
    // and the compiler's chosen operand nodes must equal the contract.
    assert_eq!(
        cf.payloads, ref_payloads,
        "{name} L{li}: payload table mismatch"
    );
    assert_eq!(
        cf.payload_operands, ref_operands,
        "{name} L{li}: operand contract mismatch"
    );

    // Execute.
    let src = StagedSources {
        bf: cf
            .source_map
            .bf
            .iter()
            .map(|&n| base_part(row.leaf_vals[n].unwrap()))
            .collect(),
        e4: cf
            .source_map
            .e4
            .iter()
            .map(|&n| row.leaf_vals[n].unwrap())
            .collect(),
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
                assert!(
                    !fires[p].is_empty(),
                    "{name} L{li}: cache payload {p} never fired"
                );
                for f in &fires[p][1..] {
                    assert_eq!(**f, *fires[p][0], "{name} L{li}: re-fire tuple diverges");
                }
            }
        }
        for f in &fires[p] {
            assert_eq!(
                **f, ref_vals[p],
                "{name} L{li}: payload {p} operand values wrong"
            );
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
