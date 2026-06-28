//! Task 13 — value-level differential harness (spec §8).
//!
//! The **primary** signal of the new GKR DAG IR: the row-bound evaluator
//! (`eval_layer_root`) produces the SAME per-root values as the prover's own
//! authoritative reference ([`super::dag_ir_reference::reference_relation_values`]),
//! across:
//!
//!   * an **exhaustive per-relation** differential — every
//!     `cs::gkr_compiler::test_support::sample_relations()` variant AND every
//!     `sample_relation_cases()` named subcase, lowered via `lower_dag` over a
//!     `single_relation_artifact`, with a **completeness assertion** that FAILS
//!     if any sampled relation lacks a reference arm (no log-only escape —
//!     spec §8 review 4/M);
//!   * the **four enforced golden circuits** (`golden_circuit_artifacts()`):
//!       - structural correspondence via Task-12 `validate` + `check_batching_parity`
//!         (the §8 "structural" leg: which root ↔ which beta power);
//!       - a value-differential on each golden circuit's **layer 0**
//!         (base-only reads, no cross-layer/cache `Prior` aliasing);
//!   * an explicit **memory-tuple** value check against the prover's real
//!     `evaluate_memory_query` (independent ground truth, not the mirrored
//!     reference).
//!
//! On divergence, root-cause BOTH ways (spec §8.4): either side may carry a bug;
//! a prover-reference bug is recorded as a finding, never "fixed" by editing the
//! new IR.

use std::collections::BTreeSet;

use cs::definitions::gkr::RamWordRepresentation;
use cs::definitions::GKRAddress;
use cs::gkr_compiler::codegen_ir::lower as retired_lower;
use cs::gkr_compiler::dag_ir::{
    check_batching_parity, eval_layer_root, lower_dag, validate, DagLayer, Expr, ExprId, Resolvers,
    Root, RootGroup, RootSlot, SinkKind,
};
use cs::gkr_compiler::test_support::{
    build_add_sub_artifact, golden_circuit_artifacts, sample_relation_cases, sample_relations,
    single_relation_artifact, variant_name, ConcreteField,
};
use cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
    NoFieldGKRRelation, NoFieldSpecialMemoryContributionRelation,
};

use field::Field;

use super::dag_ir_reference::{
    collect_addresses, reference_relation_values, RefChallengeResolver, RefCtx,
    RefLookupResolver, RefVirtualSetupResolver, StorageReadResolver, E,
};

const TRACE_LEN: usize = 2;
const ROW: usize = 0;

// ── per-layer differential core ─────────────────────────────────────────────

/// Bind a `Resolvers` bundle to `ctx` and run the closure with it.
macro_rules! with_resolvers {
    ($ctx:expr, $resolvers:ident, $body:block) => {{
        let read = StorageReadResolver { ctx: $ctx };
        let challenge = RefChallengeResolver { ctx: $ctx };
        let lookup = RefLookupResolver { ctx: $ctx };
        let virtual_setup = RefVirtualSetupResolver { ctx: $ctx };
        let $resolvers = Resolvers {
            read: &read,
            lookup: &lookup,
            virtual_setup: &virtual_setup,
            challenge: &challenge,
        };
        $body
    }};
}

/// For one lowered `DagLayer`, and the relations of the source layer (in
/// `gates` then `gates_external` order), evaluate every claim-bearing root and
/// assert it equals the matching reference value selected by `RootOrigin.slot`.
///
/// Returns the number of roots compared.
fn diff_layer(
    layer: &DagLayer,
    gates: &[NoFieldGKRRelation],
    gates_external: &[NoFieldGKRRelation],
    ctx: &RefCtx,
    label: &str,
) -> usize {
    // Pre-compute the reference value vector per relation, once.
    let gate_refs: Vec<Option<Vec<E>>> = gates
        .iter()
        .map(|r| reference_relation_values(r, ROW, ctx))
        .collect();
    let ext_refs: Vec<Option<Vec<E>>> = gates_external
        .iter()
        .map(|r| reference_relation_values(r, ROW, ctx))
        .collect();

    let mut compared = 0usize;
    with_resolvers!(ctx, resolvers, {
        for (&root_id, origin) in layer.origins.iter() {
            let (relation, refs) = match origin.group {
                RootGroup::Gates => (&gates[origin.relation_index], &gate_refs[origin.relation_index]),
                RootGroup::GatesExternal => (
                    &gates_external[origin.relation_index],
                    &ext_refs[origin.relation_index],
                ),
            };
            let refs = refs
                .as_ref()
                .unwrap_or_else(|| panic!("{label}: missing reference arm for {:?}", relation));
            let slot = match origin.slot {
                RootSlot::Output(i) => i,
                RootSlot::Constraint(i) => i,
            };
            let expected = refs.get(slot).unwrap_or_else(|| {
                panic!(
                    "{label}: reference for {:?} has no slot {slot} (origin {:?})",
                    relation, origin
                )
            });
            let got = eval_layer_root(layer, root_id, ROW, &resolvers);
            assert_eq!(
                got, *expected,
                "{label}: DAG-IR root {:?} (origin {:?}, relation {:?}) diverged from prover reference",
                root_id, origin, relation
            );
            compared += 1;
        }
    });
    compared
}

// ── exhaustive per-relation differential ────────────────────────────────────

/// Lower a single relation through `lower_dag` and value-differentiate every
/// claim-bearing root against the reference. Returns the number of roots
/// compared (so the caller can assert non-vacuity per relation).
fn diff_single_relation(name: &str, rel: &NoFieldGKRRelation) -> usize {
    // Bind every base/inner/cache/virtual-setup address the relation reads.
    let mut addrs = BTreeSet::new();
    collect_addresses(rel, &mut addrs);
    let ctx = RefCtx::new(&addrs, TRACE_LEN);

    let artifact = single_relation_artifact(rel.clone());
    let circuit = lower_dag(&artifact)
        .unwrap_or_else(|e| panic!("{name}: lower_dag must succeed, got Err: {e}"));
    assert_eq!(
        circuit.layers.len(),
        1,
        "{name}: single_relation_artifact must be one layer"
    );
    let layer = &circuit.layers[0];
    // The single relation is gate 0 of the (single) source layer.
    diff_layer(layer, std::slice::from_ref(rel), &[], &ctx, name)
}

#[test]
fn exhaustive_per_relation_value_differential() {
    let mut total = 0usize;
    // 1) one representative per variant.
    for (name, rel) in sample_relations() {
        let n = diff_single_relation(name, &rel);
        assert!(
            n >= 1,
            "{name}: a sampled relation must produce at least one claim-bearing root"
        );
        total += n;
    }
    // 2) named semantic subcases (memory descriptor forms, init/teardown,
    //    range-check vs timestamp widths).
    for (name, rel) in sample_relation_cases() {
        let n = diff_single_relation(name, &rel);
        assert!(n >= 1, "{name}: subcase must produce at least one root");
        total += n;
    }
    assert!(total >= 30, "expected at least one root per variant, got {total}");
    println!("exhaustive per-relation differential: compared {total} claim-bearing roots");
}

/// COMPLETENESS (spec §8 review 4/M): every sampled relation MUST have a
/// `reference_relation_values` arm. A missing arm is a TEST FAILURE, not a
/// logged skip. (The exhaustive match in `dag_ir_reference` already makes a
/// missing variant a *build* failure; this asserts the runtime contract — that
/// every sampled fixture, including subcases, resolves to a non-`None` value
/// vector of the right length.)
#[test]
fn every_sampled_relation_has_a_reference_arm() {
    let mut missing = Vec::new();
    for (name, rel) in sample_relations().into_iter().chain(sample_relation_cases()) {
        // Bind the addresses this relation actually reads, then resolve.
        let mut addrs = BTreeSet::new();
        collect_addresses(&rel, &mut addrs);
        let ctx = RefCtx::new(&addrs, TRACE_LEN);
        match reference_relation_values(&rel, ROW, &ctx) {
            Some(v) => assert!(
                !v.is_empty(),
                "{name}: reference arm returned an empty value vector"
            ),
            None => missing.push(format!("{name} ({})", variant_name(&rel))),
        }
    }
    assert!(
        missing.is_empty(),
        "spec §8 completeness violated — these sampled relations lack a reference arm: {missing:?}"
    );
}

// ── golden circuits: structural + layer-0 value ─────────────────────────────

#[inline]
fn is_base_layer_address(a: &GKRAddress) -> bool {
    matches!(
        a,
        GKRAddress::BaseLayerWitness(_)
            | GKRAddress::BaseLayerMemory(_)
            | GKRAddress::Setup(_)
            | GKRAddress::VirtualSetup(_)
    )
}

/// `true` if a relation reads ONLY base-layer addresses (no inner/cache/scratch)
/// — i.e. it does not consume a prior layer / cache and its per-root value can
/// be differentiated in isolation.
fn is_base_only(rel: &NoFieldGKRRelation) -> bool {
    let mut addrs = BTreeSet::new();
    collect_addresses(rel, &mut addrs);
    addrs.iter().all(is_base_layer_address)
}

#[test]
fn golden_circuits_structural_parity() {
    for (name, artifact) in golden_circuit_artifacts() {
        let dag = lower_dag(&artifact)
            .unwrap_or_else(|e| panic!("{name}: lower_dag must succeed, got Err: {e}"));
        validate(&dag).unwrap_or_else(|e| panic!("{name}: DAG must validate: {e}"));
        let retired = retired_lower::<ConcreteField>(&artifact)
            .unwrap_or_else(|e| panic!("{name}: retired lower must succeed: {e}"));
        check_batching_parity::<ConcreteField>(&dag, &retired)
            .unwrap_or_else(|e| panic!("{name}: batching parity must hold: {e}"));
        println!("golden '{name}': validate + batching parity OK ({} layers)", dag.layers.len());
    }
}

#[test]
fn golden_circuits_layer0_value_differential() {
    for (name, artifact) in golden_circuit_artifacts() {
        let dag = lower_dag(&artifact)
            .unwrap_or_else(|e| panic!("{name}: lower_dag must succeed, got Err: {e}"));
        let src_layer = &artifact.layers[0];
        let dag_layer = &dag.layers[0];

        let gates: Vec<NoFieldGKRRelation> =
            src_layer.gates.iter().map(|g| g.enforced_relation.clone()).collect();
        let gates_external: Vec<NoFieldGKRRelation> = src_layer
            .gates_with_external_connections
            .iter()
            .map(|g| g.enforced_relation.clone())
            .collect();

        // Bind EVERY base-layer address the whole DAG layer reads — not just the
        // base-only gates. Evaluating any root eagerly materializes ALL
        // materialization-only (cache) roots first (Task-5 evaluator contract),
        // and those caches read base columns too. We walk the lowered layer's
        // `Read` sources directly so the binding is exhaustive regardless of the
        // relation type (gate, external, or cache). Any non-base read in layer 0
        // (rare) is left unbound; relations consuming it are skipped below.
        let mut addrs = BTreeSet::new();
        for src in &dag_layer.sources {
            if let cs::gkr_compiler::dag_ir::SourceKind::Read { place } = &src.kind {
                // Bind base AND any cross-layer/cache read so eager cache
                // materialization never hits an unbound poly. Cross-layer values
                // are arbitrary fixed bindings; the value leg only compares
                // base-only roots whose reference reads base addresses, so the
                // extra bindings are harmless.
                if !matches!(place, cs::gkr_compiler::dag_ir::ReadPlace::Scratch { .. }) {
                    addrs.insert(super::dag_ir_reference::read_place_to_address(place));
                }
            }
        }
        // The IR bakes the inits/teardowns `high_bits_offset` from the artifact's
        // real `word_bits` + `trace_len`; the reference must mirror the SAME
        // offset (the `set_idx << offset` top-bits convention).
        let ctx = RefCtx::new(&addrs, TRACE_LEN).with_inits_offset(
            artifact.trace_len,
            artifact.memory_layout.inits_and_teardowns_word_bits,
        );

        let read = StorageReadResolver { ctx: &ctx };
        let challenge = RefChallengeResolver { ctx: &ctx };
        let lookup = RefLookupResolver { ctx: &ctx };
        let virtual_setup = RefVirtualSetupResolver { ctx: &ctx };
        let resolvers = Resolvers {
            read: &read,
            lookup: &lookup,
            virtual_setup: &virtual_setup,
            challenge: &challenge,
        };

        let mut compared = 0usize;
        for (&root_id, origin) in dag_layer.origins.iter() {
            let rel = match origin.group {
                RootGroup::Gates => &gates[origin.relation_index],
                RootGroup::GatesExternal => &gates_external[origin.relation_index],
            };
            // Value leg: only base-only relations (no cross-layer / cache `Prior`
            // operand of their OWN). Structural parity already covers the rest.
            if !is_base_only(rel) {
                continue;
            }
            let refs = reference_relation_values(rel, ROW, &ctx)
                .unwrap_or_else(|| panic!("{name}: missing reference arm for {:?}", rel));
            let slot = match origin.slot {
                RootSlot::Output(i) | RootSlot::Constraint(i) => i,
            };
            let expected = &refs[slot];
            let got = eval_layer_root(dag_layer, root_id, ROW, &resolvers);
            assert_eq!(
                got, *expected,
                "{name} layer0: DAG-IR root {:?} (origin {:?}, relation {:?}) diverged from prover reference",
                root_id, origin, rel
            );
            compared += 1;
        }
        assert!(
            compared >= 1,
            "{name}: layer-0 value differential must compare at least one base-only root (non-vacuity)"
        );
        println!("golden '{name}' layer0: value-matched {compared} base-only roots");
    }
}

// ── explicit memory-tuple check vs the real evaluate_memory_query ───────────

/// An INDEPENDENT ground-truth anchor for the memory family: build a memory
/// descriptor, lower a `MaterializeGrandProductTermExpression` (which lowers to
/// exactly one memory tuple), evaluate the DAG root, and compare against the
/// prover's REAL `evaluate_memory_query` (not the mirrored reference). This
/// catches a bug that would otherwise be invisible if both the mirrored
/// reference and the IR shared the same mistaken formula.
#[test]
fn memory_tuple_matches_prover_evaluate_memory_query() {
    use crate::gkr::prover::forward_loop::utils::evaluate_memory_query;

    // A non-trivial descriptor exercising a constant address-space, U32 address,
    // normal timestamp with offset, and U8Limbs value recomposition.
    //
    // NOTE: the address space is a `Constant`, NOT `IsRam`/`IsRegister`: the real
    // `evaluate_memory_query` `debug_assert!`s the address-space bit is 0/1, but
    // our pseudo-random column values are full field elements. A constant
    // address space avoids that boolean-column precondition while still
    // exercising the full address/timestamp/value affine arithmetic. The
    // boolean address-space arms are still covered by the mirrored-reference
    // exhaustive per-relation differential (`MemoryTuple::IsRegister`/`IsRam`).
    let desc = NoFieldSpecialMemoryContributionRelation {
        address_space: CompiledAddressSpaceRelationStrict::Constant(1),
        address: CompiledAddressStrict::U32Space([1, 2]),
        timestamp: CompiledMemoryTimestamp::Normal([3, 4]),
        value: RamWordRepresentation::U8Limbs([5, 6, 7, 8]),
        timestamp_offset: 7,
    };
    let rel = NoFieldGKRRelation::MaterializeGrandProductTermExpression {
        input: desc.clone(),
        output: GKRAddress::InnerLayer { layer: 1, offset: 0 },
    };

    // Bind a value for every memory column the descriptor reads.
    let mut addrs = BTreeSet::new();
    collect_addresses(&rel, &mut addrs);
    let ctx = RefCtx::new(&addrs, TRACE_LEN);

    // DAG side.
    let artifact = single_relation_artifact(rel.clone());
    let circuit = lower_dag(&artifact).expect("lower_dag must succeed");
    let layer = &circuit.layers[0];
    let (&root_id, _) = layer
        .origins
        .iter()
        .next()
        .expect("memory tuple relation must produce a claim-bearing root");
    let read = StorageReadResolver { ctx: &ctx };
    let challenge = RefChallengeResolver { ctx: &ctx };
    let lookup = RefLookupResolver { ctx: &ctx };
    let virtual_setup = RefVirtualSetupResolver { ctx: &ctx };
    let resolvers = Resolvers {
        read: &read,
        lookup: &lookup,
        virtual_setup: &virtual_setup,
        challenge: &challenge,
    };
    let dag_value = eval_layer_root(layer, root_id, ROW, &resolvers);

    // Independent prover ground truth: the REAL evaluate_memory_query.
    let external = ctx.external_challenges();
    let zero_pad = vec![ConcreteField::ZERO; TRACE_LEN];
    let sources = ctx.base_layer_memory_sources(8, &zero_pad); // max column referenced is 8.
    let prover_value =
        evaluate_memory_query::<ConcreteField, E>(&desc, ROW, &sources, &external);

    assert_eq!(
        dag_value, prover_value,
        "memory tuple: DAG-IR value diverged from prover evaluate_memory_query"
    );

    // And it agrees with the mirrored reference too (sanity on the reference).
    let mirrored = &reference_relation_values(&rel, ROW, &ctx).expect("mem arm")[0];
    assert_eq!(
        dag_value, *mirrored,
        "memory tuple: DAG-IR value diverged from the mirrored reference"
    );
    println!("memory tuple matched both evaluate_memory_query AND the mirrored reference");
}

// ── cache-cone alias-identity gate (Task 1 — the load-bearing test) ─────────

/// `true` if `target` is reachable from `start` by walking ONLY the pure
/// expression DAG: `Add`/`Mul` operands and a `LookupValue` source's `query`
/// sub-expr.
///
/// It deliberately does NOT follow any source→root edge. With the old
/// `SourceKind::Prior` machinery a same-layer cache read was an *opaque leaf*
/// (`Source(Prior{id})`) that pointed at a separate root — so a consumer's
/// expr-cone never reached the cache root's `expr` and this returns `false`
/// (RED). After Task 1 the cache read IS the cache value's shared `ExprId`, so
/// the consumer's cone contains it directly (GREEN).
fn cone_contains(layer: &DagLayer, start: ExprId, target: ExprId) -> bool {
    let mut stack = vec![start];
    let mut seen = BTreeSet::new();
    while let Some(id) = stack.pop() {
        if id == target {
            return true;
        }
        if !seen.insert(id.0) {
            continue;
        }
        match &layer.exprs[id.0 as usize] {
            Expr::Source(src_id) => {
                if let cs::gkr_compiler::dag_ir::SourceKind::LookupValue { query, .. } =
                    &layer.sources[src_id.0 as usize].kind
                {
                    stack.push(*query);
                }
            }
            Expr::Add(args) | Expr::Mul(args) => stack.extend_from_slice(args),
        }
    }
    false
}

/// The `expr` of `root` (both `Output` and `Constraint` carry one).
fn root_expr(root: &Root) -> ExprId {
    match root {
        Root::Output { expr, .. } | Root::Constraint { expr } => *expr,
    }
}

/// `true` if `root` is a `Cache`-sink (materialization-only) `Output` root.
fn is_cache_root(layer: &DagLayer, root: &Root) -> bool {
    matches!(root, Root::Output { sink, .. }
        if matches!(layer.sinks[sink.0 as usize].kind, SinkKind::Cache { .. }))
}

/// Task-1 load-bearing gate (review C1/codex#1): a same-layer cache read must be
/// the cache value's *shared `ExprId`*, not an opaque `Prior` leaf pointing at a
/// separate root.
///
/// The add_sub family circuit materializes denominator caches that are consumed
/// by same-layer product gates. For at least one such cache root we assert that
/// some claim-bearing (batched) root's expr-cone reaches the EXACT `ExprId` the
/// cache root materializes — DAG sharing, not a duplicated/aliased leaf.
///
/// RED (pre-rewrite): the consumer reads the cache via `Source(Prior{id})`, an
/// opaque leaf, so its cone (pure expr DAG) never reaches `cache_expr`. GREEN
/// (post-rewrite): the consumer shares the cache root's `ExprId`.
#[test]
fn cache_consumer_value_and_alias_identity() {
    let artifact = build_add_sub_artifact();
    let dag = lower_dag(&artifact).expect("lower_dag must succeed");

    let mut checked_layers = 0usize;
    let mut found_consumer = false;

    for layer in &dag.layers {
        // Cache-sink roots and the exact ExprId each materializes.
        let cache_exprs: Vec<ExprId> = layer
            .roots
            .iter()
            .filter(|r| is_cache_root(layer, r))
            .map(root_expr)
            .collect();
        if cache_exprs.is_empty() {
            continue;
        }
        checked_layers += 1;

        // For every claim-bearing (batched) root, walk its expr-cone (pure DAG,
        // NOT through Prior→root) and check it shares a cache root's ExprId.
        for &consumer_id in &layer.batching.roots {
            let consumer_expr = root_expr(&layer.roots[consumer_id.0 as usize]);
            for &cache_expr in &cache_exprs {
                if cone_contains(layer, consumer_expr, cache_expr) {
                    found_consumer = true;
                }
            }
        }
    }

    assert!(
        checked_layers >= 1,
        "add_sub must materialize at least one cache root for this gate to be meaningful"
    );
    assert!(
        found_consumer,
        "a claim-bearing root's expr-cone must SHARE a same-layer cache root's ExprId \
         (cache reuse must be DAG sharing, never an opaque Prior/CacheOutput leaf)"
    );
    println!(
        "cache alias-identity: a claim-bearing root shares a cache root's ExprId \
         across {checked_layers} cache-bearing layer(s)"
    );
}
