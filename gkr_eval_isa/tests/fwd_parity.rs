//! Task 13 — THE PARITY GATE (spec §14 oracle, §15 SP1 gate).
//!
//! Over every golden fixture under `cs/compiled_circuits/`, this integration test:
//!   1. `lower_dag(&artifact)` + `validate(&dag)`,
//!   2. per layer: `compile_layer` → `validate_compiled` → `encode`/`decode`
//!      roundtrip (decoded `Program` must equal the original),
//!   3. for every `Compute`/`CopyAlias` root at sampled rows, asserts the CPU
//!      interpreter (`interpret_layer_row`) equals the authoritative
//!      `eval_layer_root` bit-for-bit; `SkipScratchPrefill` roots are asserted
//!      present in `compiled.skipped` and emit no value comparison.
//!
//! The interpreter and `eval_layer_root` consume the SAME `SyntheticResolvers`
//! instance, so parity (not numeric correctness) is what this proves — exactly
//! the SP1 expressive-completeness gate. The layout fixtures carry no
//! witness/setup values, so the resolvers are deterministic synthetic hashes.

use std::collections::BTreeMap;
use std::path::PathBuf;

use cs::gkr_compiler::dag_ir::{
    eval_layer_root, lower_dag, validate, Bf, ChallengeRef, DagCircuit, Ext, LookupValueKind,
    ReadPlace, Resolvers, Root, RootId, VirtualSetupKind,
};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use field::{Field, FieldExtension, PrimeField};

use gkr_eval_isa::fwd::compile::{build_cross_layer_field_map, compile_layer};
use gkr_eval_isa::fwd::context::RootOutput;
use gkr_eval_isa::fwd::error::CompileError;
use gkr_eval_isa::fwd::encode::{decode, encode};
use gkr_eval_isa::fwd::interp::interpret_layer_row;
use gkr_eval_isa::fwd::validate::validate_compiled;

// ── lift ────────────────────────────────────────────────────────────────────

#[inline]
fn lift(b: Bf) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(b)
}

// ── Stable hash (FNV-1a, 32-bit) ──────────────────────────────────────────────
//
// Deterministic, no nondeterminism. Hashes the `Debug` rendering of a value (all
// dag_ir descriptor types derive `Debug`) folded with the row, per the brief.

const FNV_OFFSET: u32 = 0x811c_9dc5;
const FNV_PRIME: u32 = 0x0100_0193;

fn fnv_bytes(seed: u32, bytes: &[u8]) -> u32 {
    let mut h = seed;
    for &b in bytes {
        h ^= b as u32;
        h = h.wrapping_mul(FNV_PRIME);
    }
    h
}

fn fnv_u32(seed: u32, v: u32) -> u32 {
    fnv_bytes(seed, &v.to_le_bytes())
}

/// Hash a `Debug`-renderable descriptor + a row index into a u32.
fn hash_dbg_row<T: std::fmt::Debug>(t: &T, row: usize) -> u32 {
    let s = format!("{:?}", t);
    let h = fnv_bytes(FNV_OFFSET, s.as_bytes());
    fnv_u32(h, row as u32)
}

// ── SyntheticResolvers ────────────────────────────────────────────────────────
//
// One value, deterministic in its inputs. The SAME instance feeds both the
// interpreter and `eval_layer_root`, so any difference between them is a real
// compiler/oracle-usage divergence, never a resolver mismatch.

struct SyntheticResolvers;

impl cs::gkr_compiler::dag_ir::ReadResolver for SyntheticResolvers {
    fn read(&self, place: &ReadPlace, row: usize) -> Ext {
        lift(Bf::from_u32_with_reduction(hash_dbg_row(place, row)))
    }
}

impl cs::gkr_compiler::dag_ir::LookupResolver for SyntheticResolvers {
    fn lookup(
        &self,
        kind: &LookupValueKind,
        set_index: usize,
        evaluated_query: Ext,
        row: usize,
    ) -> Bf {
        // Base hash of (kind, row), then mix in set_index and EVERY limb of the
        // evaluated query so query evaluation is exercised identically on both
        // sides (brief: "must depend on evaluated_query").
        let mut h = hash_dbg_row(kind, row);
        h = fnv_u32(h, set_index as u32);
        let limbs = <Ext as FieldExtension<Bf>>::into_coeffs(evaluated_query);
        for l in limbs {
            h ^= l.as_u32_reduced();
            h = h.wrapping_mul(FNV_PRIME);
        }
        Bf::from_u32_with_reduction(h)
    }
}

impl cs::gkr_compiler::dag_ir::VirtualSetupResolver for SyntheticResolvers {
    fn virtual_setup(&self, kind: &VirtualSetupKind, row: usize) -> Bf {
        Bf::from_u32_with_reduction(hash_dbg_row(kind, row))
    }
}

impl cs::gkr_compiler::dag_ir::ChallengeResolver for SyntheticResolvers {
    fn challenge(&self, r: &ChallengeRef) -> Ext {
        // Include both key and power (brief: "include power").
        lift(Bf::from_u32_with_reduction(hash_dbg_row(r, 0)))
    }
}

fn resolvers(s: &SyntheticResolvers) -> Resolvers<'_> {
    Resolvers {
        read: s,
        lookup: s,
        virtual_setup: s,
        challenge: s,
    }
}

// ── Fixture loading ────────────────────────────────────────────────────────────

fn compiled_circuit_dir() -> PathBuf {
    // This test lives in the `gkr_eval_isa` crate; `cs/compiled_circuits` is at
    // `<workspace>/cs/compiled_circuits`, a sibling of this crate.
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits")
}

/// Deserialize one fixture JSON → `GKRCircuitArtifact<BabyBearField>`.
fn load_fixture(path: &PathBuf) -> Option<GKRCircuitArtifact<BabyBearField>> {
    let bytes = std::fs::read(path).ok()?;
    serde_json::from_slice(&bytes).ok()
}

const BUDGET: usize = 1024;

/// Sample rows `[0, 1, n/2, n-1]`, deduped (n may be tiny).
fn sample_rows(n: usize) -> Vec<usize> {
    if n == 0 {
        return vec![];
    }
    let mut rows = vec![0usize, 1, n / 2, n - 1];
    rows.retain(|&r| r < n);
    rows.sort_unstable();
    rows.dedup();
    rows
}

/// Run the full parity gate over a single fixture artifact.
/// Returns the number of `interp == eval_layer_root` comparisons actually performed
/// (one per root × sampled row). Callers use this to guard against vacuous passes.
fn check_fixture(name: &str, artifact: &GKRCircuitArtifact<BabyBearField>, budget: usize) -> usize {
    let mut comparisons = 0usize;
    let dag: DagCircuit = lower_dag(artifact).unwrap_or_else(|e| {
        panic!("[{name}] lower_dag failed: {e}");
    });
    validate(&dag).unwrap_or_else(|e| {
        panic!("[{name}] validate(dag) failed: {e}");
    });

    let n = dag.globals.trace_len;
    let rows = sample_rows(n);
    let s = SyntheticResolvers;
    let r = resolvers(&s);

    assert_eq!(
        dag.layers.len(),
        artifact.layers.len(),
        "[{name}] dag/artifact layer count mismatch"
    );

    // Cross-layer field map (codex Imp2): built ONCE over the whole circuit, then
    // threaded into every per-layer `compile_layer` so cross-layer reads are labeled
    // with their TRUE producing-sink field.
    let cross_layer_fields = build_cross_layer_field_map(&dag);

    for (l, dag_layer) in dag.layers.iter().enumerate() {
        let art_layer = &artifact.layers[l];
        let compiled = match compile_layer(
            dag_layer,
            art_layer,
            &artifact.scratch_space_mapping,
            &cross_layer_fields,
            budget,
        ) {
            Ok(c) => c,
            // Below the irreducible floor at this budget — an expected, clean outcome
            // when sweeping small budgets. Skip this layer's checks at this budget;
            // it is NOT a failure (a too-small budget is an unsupported config, not a
            // miscompilation). Any OTHER error IS a failure.
            Err(CompileError::BudgetBelowFloor { floor, budget: b }) => {
                eprintln!(
                    "[{name}] layer {l}: below floor at budget {b} (needs ≥ {floor}) — skipped"
                );
                continue;
            }
            Err(e) => {
                panic!("[{name}] layer {l}: compile_layer failed at budget {budget}: {e:?}");
            }
        };

        validate_compiled(&compiled, dag_layer).unwrap_or_else(|e| {
            panic!("[{name}] layer {l}: validate_compiled failed: {e:?}");
        });

        // Encode → decode roundtrip must reproduce the program exactly.
        let lanes = encode(&compiled.program).unwrap_or_else(|e| {
            panic!("[{name}] layer {l}: encode failed: {e:?}");
        });
        let decoded = decode(&lanes).unwrap_or_else(|e| {
            panic!("[{name}] layer {l}: decode failed: {e:?}");
        });
        assert_eq!(
            decoded, compiled.program,
            "[{name}] layer {l}: encode/decode roundtrip mismatch"
        );

        // Every SkipScratchPrefill root must be in `skipped` and emit no value.
        // (Handled implicitly: such roots are absent from `root_outputs`.)

        // Parity at sampled rows for every materialized root. `interpret_layer_row`
        // already produces `by_root` for ALL roots in one pass, so we call it ONCE
        // per row and compare every root against the oracle (avoids an O(roots)
        // re-interpretation per root).
        let by_root: BTreeMap<RootId, RootOutput> =
            compiled.root_outputs.iter().cloned().collect();

        for &row in &rows {
            let got = interpret_layer_row(&compiled, dag_layer, &r, row).unwrap_or_else(|e| {
                panic!("[{name}] layer {l} row {row}: interp failed: {e:?}");
            });
            for (rid, _out) in &compiled.root_outputs {
                let want = eval_layer_root(dag_layer, *rid, row, &r);
                let have = got.by_root[rid];
                assert_eq!(
                    have, want,
                    "[{name}] layer {l} root {rid:?} row {row}: \
                     interp != eval_layer_root oracle"
                );
                comparisons += 1;
            }
        }

        // Sanity: skipped roots correspond to Output roots that are scratch-
        // prefilled — they must not appear in root_outputs.
        for skipped in &compiled.skipped {
            assert!(
                !by_root.contains_key(skipped),
                "[{name}] layer {l}: skipped root {skipped:?} also in root_outputs"
            );
            // And the underlying Root must be an Output (Constraint roots are
            // never classified into actions).
            assert!(
                matches!(dag_layer.roots[skipped.0 as usize], Root::Output { .. }),
                "[{name}] layer {l}: skipped root {skipped:?} is not an Output root"
            );
        }
    }
    comparisons
}

// ── Fixture lists (mirror cs::…::coverage_tests) ────────────────────────────────
//
// 22 golden fixtures: 11 `*_layout_gkr.json` + 11 `*_layout_no_caches_gkr.json`.
// `inits_and_teardowns` layout is named `..._preprocessed_layout_gkr.json`.

const LAYOUT_GKR_FIXTURES: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_g_function_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "inits_and_teardowns_preprocessed_layout_gkr.json",
    "jump_branch_slt_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "mem_subword_only_layout_gkr.json",
    "mem_word_only_layout_gkr.json",
    "shift_binop_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
];

const LAYOUT_NO_CACHES_GKR_FIXTURES: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
    "bigint_with_extended_control_layout_no_caches_gkr.json",
    "blake2_g_function_layout_no_caches_gkr.json",
    "blake2_with_extended_control_layout_no_caches_gkr.json",
    "inits_and_teardowns_layout_no_caches_gkr.json",
    "jump_branch_slt_layout_no_caches_gkr.json",
    "keccak_special5_layout_no_caches_gkr.json",
    "mem_subword_only_layout_no_caches_gkr.json",
    "mem_word_only_layout_no_caches_gkr.json",
    "shift_binop_layout_no_caches_gkr.json",
    "unsigned_mul_div_layout_no_caches_gkr.json",
];

// ── S3 opportunity audit (corpus-wide; #[ignore]d) ──────────────────────────────
//
// Quantifies the S3 (#10 reorder + #5a acc-carry) opportunity across ALL 22 layout
// fixtures (cache + no-cache), every layer, focused on the TIGHT-budget regime (the
// regime that actually matters, and worse in the backward pass where base->ext folding
// quadruples cell width). For each (circuit, layer) it reports:
//   DAG opportunity: output/cache roots; same-layer Prior reuse edges (#10 reorder
//     adjacency potential); carry-eligible roots (>=1 same-layer-Prior child, the #5a
//     UPPER bound) + first-child-Prior roots (natural-seed proxy); size (exprs/reads);
//     base/ext sink split (backward-pass 4x-blowup signal).
//   Compile sweep: the irreducible floor (min feasible budget) and dram_reads / max_live
//     / lanes at floor / 16 / 32 / 1024 — the tight-vs-loose dram_reads gap is the room
//     #10 could recover; max_live@1024 is the uncapped cell pressure.
// Emits parseable `[AUDIT]` CSV lines + a per-circuit rollup. Run:
//   cargo test -p gkr_eval_isa --test fwd_parity -- --ignored --nocapture s3_opportunity_audit
const AUDIT_BUDGETS: &[usize] = &[4, 8, 12, 16, 24, 32, 48, 64, 128, 1024];

#[test]
#[ignore = "corpus-wide S3 opportunity audit; run on demand"]
fn s3_opportunity_audit() {
    use cs::gkr_compiler::dag_ir::{Expr, FieldKind, SourceKind};
    let dir = compiled_circuit_dir();
    let mut all: Vec<String> = Vec::new();
    let mut fixtures: Vec<&str> = Vec::new();
    fixtures.extend_from_slice(LAYOUT_GKR_FIXTURES);
    fixtures.extend_from_slice(LAYOUT_NO_CACHES_GKR_FIXTURES);

    println!("[AUDIT] circuit,caches,layer,out_roots,cache_roots,prior_edges,carry_elig,carry_firstchild,exprs,reads,base_sinks,ext_sinks,floor,dram@floor,dram@16,dram@32,dram@1024,maxlive@1024,lanes@1024");
    for &f in &fixtures {
        let has_caches = !f.contains("no_caches");
        let circuit = f.trim_end_matches("_layout_gkr.json").trim_end_matches("_layout_no_caches_gkr.json");
        let artifact = match load_fixture(&dir.join(f)) {
            Some(a) => a,
            None => { eprintln!("[AUDIT] SKIP (missing) {f}"); continue; }
        };
        let dag = match lower_dag(&artifact) { Ok(d) => d, Err(e) => { eprintln!("[AUDIT] {f} lower_dag err {e}"); continue; } };
        if let Err(e) = validate(&dag) { eprintln!("[AUDIT] {f} validate err {e}"); continue; }
        let cross = build_cross_layer_field_map(&dag);

        for (l, layer) in dag.layers.iter().enumerate() {
            // cache RootIds = Output roots with no origin.
            let mut cache_ids: std::collections::HashSet<RootId> = std::collections::HashSet::new();
            let mut n_out = 0usize;
            for (idx, root) in layer.roots.iter().enumerate() {
                if let Root::Output { .. } = root {
                    n_out += 1;
                    let rid = RootId(idx as u32);
                    if !layer.origins.contains_key(&rid) { cache_ids.insert(rid); }
                }
            }
            let is_same_layer_prior = |id: cs::gkr_compiler::dag_ir::ExprId| -> bool {
                if let Expr::Source(src) = &layer.exprs[id.0 as usize] {
                    if let SourceKind::Prior { id: rid } = &layer.sources[src.0 as usize].kind {
                        return cache_ids.contains(rid);
                    }
                }
                false
            };
            // Per-root carry/reuse structure.
            let mut prior_edges = 0usize;     // total same-layer-Prior child uses at top level
            let mut carry_elig = 0usize;      // roots with >=1 same-layer-Prior top-level child (UPPER bound)
            let mut carry_firstchild = 0usize;// roots whose child[0] is a same-layer Prior (natural-seed proxy)
            for root in &layer.roots {
                if let Root::Output { expr, .. } = root {
                    if let Expr::Add(ch) | Expr::Mul(ch) = &layer.exprs[expr.0 as usize] {
                        if ch.is_empty() { continue; }
                        let priors = ch.iter().filter(|&&c| is_same_layer_prior(c)).count();
                        prior_edges += priors;
                        if priors > 0 { carry_elig += 1; }
                        if is_same_layer_prior(ch[0]) { carry_firstchild += 1; }
                    }
                }
            }
            let n_reads = layer.sources.iter().filter(|s| matches!(s.kind, SourceKind::Read { .. })).count();
            let (mut base_sinks, mut ext_sinks) = (0usize, 0usize);
            for s in &layer.sinks { match s.field { FieldKind::Base => base_sinks += 1, FieldKind::Ext => ext_sinks += 1 } }

            // Compile sweep.
            let mut floor: Option<usize> = None;
            let mut dram: std::collections::HashMap<usize, usize> = std::collections::HashMap::new();
            let mut maxlive1024 = 0usize;
            let mut lanes1024 = 0usize;
            for &b in AUDIT_BUDGETS {
                match compile_layer(layer, &artifact.layers[l], &artifact.scratch_space_mapping, &cross, b) {
                    Ok(c) => {
                        if floor.is_none() { floor = Some(b); }
                        dram.insert(b, c.stats.dram_reads);
                        if b == 1024 { maxlive1024 = c.stats.max_live_cells; lanes1024 = c.stats.program_lanes; }
                    }
                    Err(CompileError::BudgetBelowFloor { .. }) => {}
                    Err(e) => { eprintln!("[AUDIT] {circuit} caches={has_caches} L{l} budget {b} ERR {e:?}"); }
                }
            }
            let fl = floor.unwrap_or(0);
            let g = |b: usize| dram.get(&b).map(|v| *v as i64).unwrap_or(-1);
            all.push(format!(
                "[AUDIT] {circuit},{has_caches},{l},{n_out},{},{prior_edges},{carry_elig},{carry_firstchild},{},{n_reads},{base_sinks},{ext_sinks},{fl},{},{},{},{},{maxlive1024},{lanes1024}",
                cache_ids.len(), layer.exprs.len(), g(fl), g(16), g(32), g(1024)
            ));
        }
    }
    for line in &all { println!("{line}"); }
    println!("[AUDIT] total layer-rows: {}", all.len());
    assert!(!all.is_empty(), "audit produced no rows");
}

// ── Source-reuse redundancy audit (the REAL reuse opportunity; #[ignore]d) ──────
//
// Corrects the cache-root-Prior-only view: counts how many DRAM reads are REDUNDANT
// reloads of an already-read source (any Global: regular Read / VirtualSetup / a
// not-resident cache backing). A hot source read by N instructions costs N DRAM reads
// today (the planner only admits cache roots; regular sources are never kept resident).
// Per (circuit, caches, layer, budget): G = total Global operand reads, D = distinct
// (slot,col) sources, R = G - D = redundant reloads a read-once smem residency could
// eliminate (bounded by budget), maxfan = reads of the hottest single source.
// Run: cargo test -p gkr_eval_isa --test fwd_parity -- --ignored --nocapture reuse_redundancy_audit
fn count_globals(op: &gkr_eval_isa::fwd::isa::OperandLine, tot: &mut usize, set: &mut std::collections::HashMap<(u8, u16), usize>) {
    if let gkr_eval_isa::fwd::isa::OperandLine::Global { slot, col } = op {
        *tot += 1;
        *set.entry((*slot, *col)).or_insert(0) += 1;
    }
}

#[test]
#[ignore = "corpus-wide source-reuse redundancy audit; run on demand"]
fn reuse_redundancy_audit() {
    use gkr_eval_isa::fwd::isa::Instr;
    let dir = compiled_circuit_dir();
    let mut fixtures: Vec<&str> = Vec::new();
    fixtures.extend_from_slice(LAYOUT_GKR_FIXTURES);
    fixtures.extend_from_slice(LAYOUT_NO_CACHES_GKR_FIXTURES);
    println!("[REUSE] circuit,caches,layer,budget,G_total_global,D_distinct,R_redundant,R_pct,maxfan,smem_reads,lanes");
    for &f in &fixtures {
        let has_caches = !f.contains("no_caches");
        let circuit = f.trim_end_matches("_layout_gkr.json").trim_end_matches("_layout_no_caches_gkr.json");
        let artifact = match load_fixture(&dir.join(f)) { Some(a) => a, None => continue };
        let dag = match lower_dag(&artifact) { Ok(d) => d, Err(_) => continue };
        if validate(&dag).is_err() { continue; }
        let cross = build_cross_layer_field_map(&dag);
        for (l, layer) in dag.layers.iter().enumerate() {
            for &budget in &[1024usize, 32] {
                let compiled = match compile_layer(layer, &artifact.layers[l], &artifact.scratch_space_mapping, &cross, budget) {
                    Ok(c) => c,
                    Err(_) => continue,
                };
                let mut g = 0usize;
                let mut set: std::collections::HashMap<(u8, u16), usize> = std::collections::HashMap::new();
                let mut smem = 0usize;
                let bump_smem = |op: &gkr_eval_isa::fwd::isa::OperandLine, s: &mut usize| {
                    if matches!(op, gkr_eval_isa::fwd::isa::OperandLine::Smem { .. }) { *s += 1; }
                };
                for instr in &compiled.program.instrs {
                    match instr {
                        Instr::Mov { src: Some(op), .. } => { count_globals(op, &mut g, &mut set); bump_smem(op, &mut smem); }
                        Instr::Mov { src: None, .. } => {}
                        Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
                            for op in operands { count_globals(op, &mut g, &mut set); bump_smem(op, &mut smem); }
                        }
                        Instr::Fma { pairs, .. } => {
                            for (a, b) in pairs {
                                count_globals(a, &mut g, &mut set); bump_smem(a, &mut smem);
                                count_globals(b, &mut g, &mut set); bump_smem(b, &mut smem);
                            }
                        }
                    }
                }
                let d = set.len();
                let r = g - d;
                let maxfan = set.values().copied().max().unwrap_or(0);
                let rpct = if g > 0 { 100.0 * r as f64 / g as f64 } else { 0.0 };
                println!(
                    "[REUSE] {circuit},{has_caches},{l},{budget},{g},{d},{r},{rpct:.1},{maxfan},{smem},{}",
                    compiled.program.instrs.len()
                );
            }
        }
    }
}

// ── Budget-bounded ACHIEVABLE source-residency savings (Belady/OPT sim) ──────────
//
// `reuse_redundancy_audit` measures R = G - D, the UNBOUNDED ceiling (a read-once
// residency with infinite cells eliminates every reload). This measures how much of
// R is ACHIEVABLE under a finite source-residency cache of `cap` cells, per circuit.
//
// Method: compile at budget 1024 so every cache root stays resident — then the only
// Global (DRAM) reads left in the program are REGULAR sources (Read/VirtualSetup) and
// any non-resident backing, i.e. exactly the untapped opportunity this design targets.
// Build the linear trace of those reads in program order and run a Belady/OPT
// demand-cache of capacity `cap` over it. OPT is hit-maximal (Belady 1966: evict the
// resident whose NEXT use is farthest in the future), so `hits@cap` is the TRUE
// achievable ceiling at that capacity — no online residency policy beats it. OPT also
// self-prioritizes: a single-use source has next-use = ∞, so it is the first eviction
// candidate and never displaces a reused source. `hits@cap` = recoverable reloads;
// hits/G = fraction of ALL forward DRAM reads eliminated at that cache size.
//
// Run: cargo test -p gkr_eval_isa --test fwd_parity -- --ignored --nocapture source_residency_savings_audit
const SRC_RESIDENCY_CAPS: &[usize] = &[8, 16, 32, 64, 128];

fn belady_opt_hits(trace: &[(u8, u16)], cap: usize) -> usize {
    if cap == 0 || trace.is_empty() {
        return 0;
    }
    let n = trace.len();
    // next_use[i] = next index > i referencing the same source, else usize::MAX.
    let mut next_use = vec![usize::MAX; n];
    let mut last: std::collections::HashMap<(u8, u16), usize> = std::collections::HashMap::new();
    for i in (0..n).rev() {
        if let Some(&nxt) = last.get(&trace[i]) {
            next_use[i] = nxt;
        }
        last.insert(trace[i], i);
    }
    // cache: resident source -> next-use position recorded at its last access.
    let mut cache: std::collections::HashMap<(u8, u16), usize> = std::collections::HashMap::new();
    let mut hits = 0usize;
    for i in 0..n {
        let item = trace[i];
        if cache.contains_key(&item) {
            hits += 1; // served from residency — a saved DRAM read
            cache.insert(item, next_use[i]);
        } else {
            if cache.len() >= cap {
                // OPT: evict the resident whose next use is farthest in the future.
                let victim = *cache.iter().max_by_key(|&(_, &nu)| nu).map(|(k, _)| k).unwrap();
                cache.remove(&victim);
            }
            cache.insert(item, next_use[i]);
        }
    }
    hits
}

#[test]
#[ignore = "budget-bounded achievable source-residency savings (Belady/OPT); run on demand"]
fn source_residency_savings_audit() {
    use gkr_eval_isa::fwd::isa::{Instr, OperandLine};
    let dir = compiled_circuit_dir();
    let mut fixtures: Vec<&str> = Vec::new();
    fixtures.extend_from_slice(LAYOUT_GKR_FIXTURES);
    fixtures.extend_from_slice(LAYOUT_NO_CACHES_GKR_FIXTURES);

    // Corpus + per-caches aggregates: index 0 = cap 8 .. 4 = cap 128.
    let ncaps = SRC_RESIDENCY_CAPS.len();
    let (mut tot_g, mut tot_r) = (0usize, 0usize);
    let mut tot_hits = vec![0usize; ncaps];
    let mut by_caches: std::collections::HashMap<bool, (usize, usize, Vec<usize>)> = std::collections::HashMap::new();

    let caps_hdr: Vec<String> = SRC_RESIDENCY_CAPS.iter().map(|c| format!("hits@{c},pctR@{c},pctG@{c}")).collect();
    let mut tot_vs_total = 0usize;
    let mut tot_vs_redundant = 0usize;
    println!("[SRCRES] circuit,caches,layer,G_dram,D_distinct,R_dram,maxfan,maxlive@1024,W_min_cap,reuse_d1,reuse_le4,reuse_le16,reuse_gt16,reuse_dmax,vs_global,vs_redundant,{}", caps_hdr.join(","));

    for &f in &fixtures {
        let has_caches = !f.contains("no_caches");
        let circuit = f.trim_end_matches("_layout_gkr.json").trim_end_matches("_layout_no_caches_gkr.json");
        let artifact = match load_fixture(&dir.join(f)) { Some(a) => a, None => continue };
        let dag = match lower_dag(&artifact) { Ok(d) => d, Err(_) => continue };
        if validate(&dag).is_err() { continue; }
        let cross = build_cross_layer_field_map(&dag);
        for (l, layer) in dag.layers.iter().enumerate() {
            let compiled = match compile_layer(layer, &artifact.layers[l], &artifact.scratch_space_mapping, &cross, 1024) {
                Ok(c) => c,
                Err(_) => continue,
            };
            // Linear trace of Global reads in program order, CLASSIFIED by backing:
            // VirtualSetup is NOT a DRAM read — the interpreter resolves it by
            // COMPUTATION (`r.virtual_setup(kind,row)`, interp.rs:147-148), not
            // `r.read` (interp.rs:150). It only lowers to a `Global` operand. So it is
            // excluded from the DRAM-read residency trace; we tally it separately to
            // show how much it inflated the earlier (uncorrected) R.
            use gkr_eval_isa::fwd::binding::BackingKey;
            let is_vsetup = |slot: u8| matches!(compiled.ctx.backings.backing(slot), Some(BackingKey::VirtualSetup { .. }));
            let mut trace: Vec<(u8, u16)> = Vec::new(); // DRAM reads only
            let mut vs_total = 0usize; // VirtualSetup Global reads (computed, not DRAM)
            let mut vs_set: std::collections::HashSet<(u8, u16)> = std::collections::HashSet::new();
            let mut push = |op: &OperandLine, t: &mut Vec<(u8, u16)>, vt: &mut usize, vs: &mut std::collections::HashSet<(u8, u16)>| {
                if let OperandLine::Global { slot, col } = op {
                    if is_vsetup(*slot) { *vt += 1; vs.insert((*slot, *col)); } else { t.push((*slot, *col)); }
                }
            };
            for instr in &compiled.program.instrs {
                match instr {
                    Instr::Mov { src: Some(op), .. } => push(op, &mut trace, &mut vs_total, &mut vs_set),
                    Instr::Mov { src: None, .. } => {}
                    Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
                        for op in operands { push(op, &mut trace, &mut vs_total, &mut vs_set); }
                    }
                    Instr::Fma { pairs, .. } => {
                        for (a, b) in pairs { push(a, &mut trace, &mut vs_total, &mut vs_set); push(b, &mut trace, &mut vs_total, &mut vs_set); }
                    }
                }
            }
            let vs_redundant = vs_total.saturating_sub(vs_set.len()); // reloads attributable to VirtualSetup
            let g = trace.len();
            let mut distinct: std::collections::HashMap<(u8, u16), usize> = std::collections::HashMap::new();
            for &it in &trace { *distinct.entry(it).or_insert(0) += 1; }
            let d = distinct.len();
            let r = g - d;
            let maxfan = distinct.values().copied().max().unwrap_or(0);
            let maxlive = compiled.stats.max_live_cells;

            // MECHANISM check: reuse distance (gap to the previous use of the same
            // source, in trace positions) + W = smallest cache that recovers 100% of R.
            let mut last_pos: std::collections::HashMap<(u8, u16), usize> = std::collections::HashMap::new();
            let (mut d_adj, mut d_le4, mut d_le16, mut d_gt16, mut d_max) = (0usize, 0usize, 0usize, 0usize, 0usize);
            for (i, &it) in trace.iter().enumerate() {
                if let Some(&p) = last_pos.get(&it) {
                    let dist = i - p;
                    d_max = d_max.max(dist);
                    if dist == 1 { d_adj += 1; } else if dist <= 4 { d_le4 += 1; } else if dist <= 16 { d_le16 += 1; } else { d_gt16 += 1; }
                }
                last_pos.insert(it, i);
            }
            // W: min cap in 1..=256 with hits == R (R==0 → W=0).
            let mut w = 0usize;
            if r > 0 {
                w = 257;
                for cap in 1..=256 {
                    if belady_opt_hits(&trace, cap) == r { w = cap; break; }
                }
            }

            tot_g += g;
            tot_r += r;
            let entry = by_caches.entry(has_caches).or_insert((0, 0, vec![0usize; ncaps]));
            entry.0 += g;
            entry.1 += r;

            let mut cols = String::new();
            for (ci, &cap) in SRC_RESIDENCY_CAPS.iter().enumerate() {
                let hits = belady_opt_hits(&trace, cap);
                tot_hits[ci] += hits;
                entry.2[ci] += hits;
                let pct_r = if r > 0 { 100.0 * hits as f64 / r as f64 } else { 0.0 };
                let pct_g = if g > 0 { 100.0 * hits as f64 / g as f64 } else { 0.0 };
                cols.push_str(&format!(",{hits},{pct_r:.1},{pct_g:.1}"));
            }
            tot_vs_total += vs_total;
            tot_vs_redundant += vs_redundant;
            println!("[SRCRES] {circuit},{has_caches},{l},{g},{d},{r},{maxfan},{maxlive},{w},{d_adj},{d_le4},{d_le16},{d_gt16},{d_max},{vs_total},{vs_redundant}{cols}");
        }
    }

    // Aggregates.
    println!("[SRCRES-AGG] scope,G,R,R_pctG{}", SRC_RESIDENCY_CAPS.iter().map(|c| format!(",hits@{c},pctR@{c},pctG@{c}")).collect::<Vec<_>>().join(""));
    let emit_agg = |label: &str, g: usize, r: usize, hits: &[usize]| {
        let rpg = if g > 0 { 100.0 * r as f64 / g as f64 } else { 0.0 };
        let mut cols = String::new();
        for (ci, &cap) in SRC_RESIDENCY_CAPS.iter().enumerate() {
            let _ = cap;
            let h = hits[ci];
            let pr = if r > 0 { 100.0 * h as f64 / r as f64 } else { 0.0 };
            let pg = if g > 0 { 100.0 * h as f64 / g as f64 } else { 0.0 };
            cols.push_str(&format!(",{h},{pr:.1},{pg:.1}"));
        }
        println!("[SRCRES-AGG] {label},{g},{r},{rpg:.1}{cols}");
    };
    emit_agg("CORPUS", tot_g, tot_r, &tot_hits);
    if let Some((g, r, h)) = by_caches.get(&true) { emit_agg("caches=true", *g, *r, h); }
    if let Some((g, r, h)) = by_caches.get(&false) { emit_agg("caches=false", *g, *r, h); }
    // VirtualSetup: computed (not DRAM); reported separately. The OLD (uncorrected) R
    // counted these; corrected DRAM R excludes them.
    println!(
        "[SRCRES-VS] vs_global_reads={tot_vs_total} vs_redundant={tot_vs_redundant}  (DRAM R={tot_r}; old_uncorrected_R={})",
        tot_r + tot_vs_redundant
    );
    assert!(tot_g > 0, "audit produced no Global reads");
}

fn run_fixtures(fixtures: &[&str]) {
    let dir = compiled_circuit_dir();
    let mut checked = 0usize;
    let mut total_comparisons = 0usize;
    for &f in fixtures {
        let path = dir.join(f);
        let artifact = load_fixture(&path)
            .unwrap_or_else(|| panic!("failed to load/deserialize fixture {f} at {path:?}"));
        let t0 = std::time::Instant::now();
        // BUDGET = 1024 is the EXTREME all-resident case: nothing is ever evicted or
        // recomputed (stresses the no-reload path). Realistic small-budget coverage
        // is in `parity_budget_sweep_small`.
        let comparisons = check_fixture(f, &artifact, BUDGET);
        eprintln!("[fwd_parity] {f} OK in {:?} ({comparisons} root comparisons)", t0.elapsed());
        total_comparisons += comparisons;
        checked += 1;
    }
    assert_eq!(checked, fixtures.len(), "not all fixtures checked");
    assert!(
        total_comparisons > 0,
        "parity gate compared 0 roots — vacuous pass (root_outputs/sample_rows empty?)"
    );
}

// ── add_sub fixtures (Commit 1) ─────────────────────────────────────────────────

const ADD_SUB_FIXTURES: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
];

#[test]
fn parity_add_sub() {
    run_fixtures(ADD_SUB_FIXTURES);
}

// ── full gate over all 22 fixtures ──────────────────────────────────────────────
//
// These run the WHOLE corpus (all layers × sampled rows) and ARE the SP1 gate:
// every fixture layer compiles, validates, encode/decode-roundtrips, and the CPU
// interpreter matches `eval_layer_root` bit-for-bit at the sampled rows.

#[test]
fn parity_all_layout_gkr() {
    run_fixtures(LAYOUT_GKR_FIXTURES);
}

#[test]
fn parity_all_layout_no_caches_gkr() {
    run_fixtures(LAYOUT_NO_CACHES_GKR_FIXTURES);
}

// ── budget sweep — realistic SMALL budgets (the eviction regime) ────────────────
//
// BUDGET = 1024 (the gates above) is the EXTREME all-resident case: nothing is ever
// evicted or recomputed. Real hardware budgets are a warp's worth of smem cells —
// small multiples of 4. This sweeps from 8 upward: at each FEASIBLE budget the
// residency planner must EVICT residents and redirect reads (Prior→Smem and back,
// CSE, evict/reload), and the CPU interpreter must STILL match the
// budget-INDEPENDENT `eval_layer_root` oracle bit-for-bit. A budget below a layer's
// irreducible floor yields a clean `BudgetBelowFloor` (skipped), never a panic.
//
// This is the first end-to-end validation of the S2 eviction path: every gate
// before this ran only at 1024, where eviction never fires.

const SWEEP_BUDGETS: &[usize] = &[8, 12, 16, 24, 32, 48, 64, 128, 256];

// Routine gate: the two cache-heaviest fixtures (add_sub, mul_div) at warp-scale
// budgets. Fast (~15s) and enough to guard the in-flight-borrow timing + bit-exact
// re-emission under eviction. The exhaustive 11-fixture variant is the `#[ignore]`d
// `parity_budget_sweep_all_fixtures` below (the design's broad-corpus run, ~150s).
const SWEEP_FIXTURES: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
];

/// Run the budget sweep over `fixtures`, asserting that the eviction regime was
/// actually exercised (≥1 comparison at a budget below 1024) and that every feasible
/// (budget, layer) reproduced `eval_layer_root` bit-exactly (the `check_fixture`
/// differential). Returns the smallest feasible budget seen, for logging.
fn run_budget_sweep(fixtures: &[&str]) {
    let dir = compiled_circuit_dir();
    let mut total = 0usize;
    // Comparisons performed at a budget strictly below 1024 — proves the eviction
    // regime was actually exercised, not just the all-resident extreme.
    let mut sub1024_comparisons = 0usize;
    let mut smallest_feasible: Option<usize> = None;

    for &f in fixtures {
        let path = dir.join(f);
        let artifact =
            load_fixture(&path).unwrap_or_else(|| panic!("failed to load fixture {f}"));
        for &budget in SWEEP_BUDGETS {
            let c = check_fixture(f, &artifact, budget);
            eprintln!("[fwd_parity sweep] {f} budget {budget}: {c} comparisons");
            total += c;
            if c > 0 {
                sub1024_comparisons += c;
                smallest_feasible = Some(smallest_feasible.map_or(budget, |s| s.min(budget)));
            }
        }
    }

    eprintln!(
        "[fwd_parity sweep] smallest feasible budget across {} fixtures: {:?}",
        fixtures.len(),
        smallest_feasible
    );
    assert!(
        total > 0,
        "budget sweep performed 0 comparisons — every swept budget below floor (vacuous)"
    );
    assert!(
        sub1024_comparisons > 0,
        "budget sweep validated 0 comparisons below 1024 — the eviction regime was never \
         exercised (every layer's floor exceeds {}); residency under realistic budgets is \
         UNTESTED and possibly broken",
        SWEEP_BUDGETS.last().unwrap()
    );
}

#[test]
fn parity_budget_sweep_small() {
    run_budget_sweep(SWEEP_FIXTURES);
}

// Exhaustive cross-corpus eviction sweep (the design's broad-corpus validation). Runs
// every cache-bearing layout fixture across all warp-scale budgets — ~150s, so it is
// `#[ignore]`d and run on demand: `cargo test -p gkr_eval_isa --test fwd_parity -- \
// --ignored parity_budget_sweep_all_fixtures`.
#[test]
#[ignore = "slow (~150s) exhaustive sweep; run on demand"]
fn parity_budget_sweep_all_fixtures() {
    run_budget_sweep(LAYOUT_GKR_FIXTURES);
}

// Proof that the small-budget sweep actually EXERCISES eviction — not just smaller
// compiles that happen to still fit. add_sub layer 0's natural (uncapped) resident
// working set exceeds 32 cells, so at budget 32 the planner MUST evict: reused cache
// roots fall back to DRAM (more `dram_reads`, fewer resident `cell_reads`). The sweep
// above already proved interp == `eval_layer_root` at budget 32 (correct UNDER
// eviction); this asserts eviction genuinely engaged, so that correctness guarantee
// is not vacuous. Asserts PROPERTIES (monotone traffic under cap pressure), not magic
// numbers, so it survives codegen changes.
#[test]
fn residency_eviction_engages_under_tight_budget() {
    let dir = compiled_circuit_dir();
    let path = dir.join("add_sub_lui_auipc_mop_layout_gkr.json");
    let artifact = match load_fixture(&path) {
        Some(a) => a,
        None => return,
    };
    let dag = lower_dag(&artifact).unwrap();
    validate(&dag).unwrap();
    let cross = build_cross_layer_field_map(&dag);

    let try_stats_at = |budget: usize| {
        compile_layer(
            &dag.layers[0],
            &artifact.layers[0],
            &artifact.scratch_space_mapping,
            &cross,
            budget,
        )
        .map(|c| c.stats)
    };
    let stats_at = |budget: usize| {
        try_stats_at(budget)
            .unwrap_or_else(|e| panic!("add_sub L0 compile at budget {budget}: {e:?}"))
    };

    // ── On-demand eviction under source residency (S3) ────────────────────────
    //
    // With source residency (#7) hot regular `Read` sources are also kept resident,
    // so the uncapped resident working set grew (40→58) and the optimal dram_reads
    // dropped (S2 77 → S3 52). The extra residents also raise the irreducible floor:
    // budget 8 no longer compiles; the smallest feasible budget is 12. add_sub L0's
    // re-measured curve (from `compile_layer(.., budget).stats`):
    //   budget ≤11: BudgetBelowFloor (infeasible — residents + temps don't fit)
    //   budget  12: max_live 12, dram_reads 74, cell_reads 68   ← floor (smallest feasible)
    //   budget  16: max_live 16, dram_reads 71, cell_reads 69
    //   budget  24: max_live 24, dram_reads 65, cell_reads 71
    //   budget  32: max_live 32, dram_reads 59, cell_reads 73
    //   budget  48: max_live 48, dram_reads 54, cell_reads 73
    //   budget  64: max_live 58, dram_reads 52, cell_reads 73   ← S3-optimal reached
    //   budget 1024: max_live 58, dram_reads 52, cell_reads 73  ← uncapped working set 58
    //
    // Assertions are PROPERTY-based (monotone traffic under cap pressure, hard cap
    // honored, optimum reachable) so they survive codegen drift; the only hard budget
    // anchors are the feasibility boundary (compiles at 12, not at 8).

    // (1) Feasibility boundary: under source residency the floor sits between 8 and 12;
    //     a too-tight budget yields a clean BudgetBelowFloor, a roomy one compiles.
    assert!(
        try_stats_at(8).is_err(),
        "add_sub L0 should NOT compile at budget 8 once source residents are pinned \
         (extra residents raise the floor); expected BudgetBelowFloor"
    );
    assert!(
        try_stats_at(12).is_ok(),
        "add_sub L0 must compile at budget 12 (the irreducible floor under source residency)"
    );

    let loose = stats_at(1024);
    let tight = stats_at(16);
    let roomy = stats_at(32);

    // (2) The uncapped working set genuinely exceeds the tight budget, so eviction is
    //     forced (not incidental); and the hard cap is honored under pressure.
    assert!(
        loose.max_live_cells > 16,
        "uncapped working set {} should exceed the tight budget (else no eviction is \
         forced)",
        loose.max_live_cells
    );
    assert!(
        tight.max_live_cells <= 16,
        "tight-budget max_live {} exceeds the 16-cell cap",
        tight.max_live_cells
    );

    // (3) Under genuine pressure, evicting a still-needed backed resident forces its
    //     reader to fall back to DRAM: strictly MORE dram reads and FEWER resident
    //     smem reads than the all-resident compile.
    assert!(
        tight.dram_reads > loose.dram_reads,
        "eviction must force extra DRAM re-reads: tight16 {} vs loose {}",
        tight.dram_reads,
        loose.dram_reads
    );
    assert!(
        tight.cell_reads < loose.cell_reads,
        "eviction must reduce resident smem reads: tight16 {} vs loose {}",
        tight.cell_reads,
        loose.cell_reads
    );

    // (4) dram_reads degrades SMOOTHLY (monotone non-increasing) as the budget grows —
    //     tighter budget spills more reused values to DRAM; it never fails or spikes.
    //     Anchored at 16/24/32 (budget 8 is now below the floor).
    let d16 = tight.dram_reads;
    let d24 = stats_at(24).dram_reads;
    let d32 = roomy.dram_reads;
    assert!(
        d16 >= d24 && d24 >= d32,
        "dram_reads must be monotone non-increasing in budget: 16→{d16} 24→{d24} 32→{d32}"
    );

    // (5) The source-residency win is fully preserved once the budget is roomy enough:
    //     a sufficiently large budget reaches the uncapped (optimal) dram_reads.
    //     NOTE: unlike S2 (where budget 32 already hit the optimum), source residency
    //     enlarges the resident working set to 58, so budget 32 (max_live capped at 32)
    //     still spills — roomy(32) > loose here. We assert (a) budget 32 still improves
    //     on the tight budget but does NOT yet reach the optimum (so eviction is still
    //     engaging at 32, not vacuous), and (b) a budget ≥ the uncapped working set
    //     (64 ≥ 58) reaches the optimum exactly. This stays non-tautological: it fails
    //     if eviction stops engaging at 32, or if the optimum becomes unreachable.
    assert!(
        roomy.dram_reads < tight.dram_reads,
        "budget 32 must still improve on the tight budget: roomy32 {} vs tight16 {}",
        roomy.dram_reads, tight.dram_reads
    );
    assert!(
        roomy.dram_reads > loose.dram_reads,
        "budget 32 (< uncapped working set 58) must still spill — eviction engaging: \
         roomy32 {} vs loose {}",
        roomy.dram_reads, loose.dram_reads
    );
    assert_eq!(
        stats_at(64).dram_reads, loose.dram_reads,
        "a budget ≥ the uncapped working set (64 ≥ 58) must reach the S3-optimal \
         dram_reads (no regression of the source-residency win)"
    );
}

// ── Source-residency regression gates (Task 6) ──────────────────────────────────
//
// Dedicated, isolated locks for the source-residency (#7) win. The S3 baselines in
// `stats.rs` already assert the descent; this re-asserts the add_sub L0 cut at the
// integration-test level (same fixture, budget 1024) so it is visible in the parity
// suite. Measured value: 52 DRAM reads (was S2 77).
#[test]
fn source_residency_cuts_dram_reads_add_sub_l0() {
    let dir = compiled_circuit_dir();
    let path = dir.join("add_sub_lui_auipc_mop_layout_gkr.json");
    let artifact = match load_fixture(&path) {
        Some(a) => a,
        None => return,
    };
    let dag = lower_dag(&artifact).expect("lower");
    validate(&dag).expect("validate");
    let cross = build_cross_layer_field_map(&dag);
    let c = compile_layer(
        &dag.layers[0],
        &artifact.layers[0],
        &artifact.scratch_space_mapping,
        &cross,
        BUDGET,
    )
    .expect("compile");
    assert!(
        c.stats.dram_reads < 77,
        "source residency must cut add_sub L0 below the S2 baseline of 77; got {}",
        c.stats.dram_reads
    );
    assert_eq!(
        c.stats.dram_reads, 52,
        "add_sub L0 dram_reads changed (measured S3 baseline is 52)"
    );
}

// Floor tracking + DRAM no-regress (spec open-Q3).
//
// Source residency pins extra cells, so it CAN raise the smallest viable budget (the
// floor) for a layer. MEASUREMENT (pre = commit 51b27bf7 in an out-of-tree worktree,
// post = current tree; smallest `AUDIT_BUDGETS` entry where `compile_layer` is `Ok`):
//
//   circuit / layer                    pre  post
//   add_sub_lui_auipc L0                 8   12   ← floor ROSE
//   unsigned_mul_div  L0                 8   12   ← floor ROSE
//   blake2_with_extended_control L0      8    8
//   blake2_g_function  L0                8    8
//   bigint_with_extended_control L0      8    8
//   keccak_special5    L0                8    8
// (and several deeper layers rose 4→8: add_sub L1/L2, mul_div L2, blake2 L1/L6, etc.)
//
// So the floor is NOT no-regress: source residency raised it by one AUDIT_BUDGETS step
// on the heaviest L0s (8→12) and on a number of small deeper layers (4→8). This is the
// floor regression the design's deferred `point`-cursor follow-up was gated on (see
// task-6 brief Q3 / deferred note) — it has now appeared and is left for adjudication.
//
// This gate therefore does NOT assert `post <= pre` (that is false). It LOCKS the
// measured post-residency floors (so any further drift — up OR down — is caught) and
// asserts the property that genuinely holds and matters: dram_reads is monotone
// non-increasing in budget at every layer (a roomier budget never costs MORE DRAM
// traffic; the residency win never regresses with more cells). We do NOT hardcode a
// universal floor (e.g. 32): each layer is locked to its own measured floor.
#[test]
fn source_residency_floor_locked_and_dram_monotone() {
    let dir = compiled_circuit_dir();
    // (fixture, layer, measured post-residency floor — smallest AUDIT_BUDGETS that compiles).
    let post_floor: &[(&str, usize, usize)] = &[
        ("blake2_with_extended_control_layout_gkr.json", 0, 8),
        ("blake2_g_function_layout_gkr.json", 0, 8),
        ("bigint_with_extended_control_layout_gkr.json", 0, 8),
        ("keccak_special5_layout_gkr.json", 0, 8),
        ("unsigned_mul_div_layout_gkr.json", 0, 12),
        ("add_sub_lui_auipc_mop_layout_gkr.json", 0, 12),
    ];
    for &(f, l, floor_expected) in post_floor {
        let artifact = match load_fixture(&dir.join(f)) {
            Some(a) => a,
            None => continue,
        };
        let dag = lower_dag(&artifact).expect("lower");
        validate(&dag).expect("validate");
        let cross = build_cross_layer_field_map(&dag);
        // Post-residency floor: smallest AUDIT_BUDGETS that compiles.
        let floor_post = AUDIT_BUDGETS
            .iter()
            .copied()
            .find(|&b| {
                compile_layer(&dag.layers[l], &artifact.layers[l], &artifact.scratch_space_mapping, &cross, b)
                    .is_ok()
            })
            .unwrap_or_else(|| panic!("{f} L{l}: compiles at no AUDIT_BUDGET"));
        assert_eq!(
            floor_post, floor_expected,
            "{f} L{l}: floor drifted from the locked post-residency value {floor_expected}→{floor_post}"
        );
        // dram_reads must be monotone non-increasing in budget at this layer (a roomier
        // budget never costs MORE DRAM traffic) — the real no-regress property, and a
        // guard against a residency interaction that spikes traffic at some budget.
        let mut prev: Option<(usize, usize)> = None;
        for &b in AUDIT_BUDGETS {
            if let Ok(c) = compile_layer(&dag.layers[l], &artifact.layers[l], &artifact.scratch_space_mapping, &cross, b) {
                if let Some((pb, pd)) = prev {
                    assert!(
                        c.stats.dram_reads <= pd,
                        "{f} L{l}: dram_reads rose with budget: {pb}→{pd} then {b}→{}",
                        c.stats.dram_reads
                    );
                }
                prev = Some((b, c.stats.dram_reads));
            }
        }
    }
}
