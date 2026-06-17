//! Structural validators for the DAG IR + batching-sequence parity against the
//! retired codegen IR (spec §7).
//!
//! # `validate`
//! A pure `cs`-internal structural pass over a [`DagCircuit`]. It enforces the
//! spec §7 invariants:
//! - Every claim-bearing root appears exactly once in [`BatchingOrder`];
//!   materialization-only (cache) roots are referenced via `Prior` and must NOT
//!   appear in `BatchingOrder`.
//! - Each `Output` root's sink is written exactly once per layer; `Constraint`
//!   roots have no sink.
//! - Every source field is inferable; every expr field is inferable by `join`.
//! - An `Output` root's expr field equals its sink field exactly (no implicit
//!   conversion either direction).
//! - `LookupValue`/`Constant` are base-field; `Challenge` is ext.
//! - Every `Prior` resolves to a declared root and the full dependency graph
//!   (`Expr→Source`, `Prior→root`, `LookupValue.query→Expr`) is acyclic.
//!
//! ## Cross-layer field resolution
//! `ReadPlace::LayerOutput`/`CacheOutput` carry no field tag (the model only
//! tags *sinks*). `validate` walks layers in declaration order and accumulates a
//! map from each layer's sink "place" (`Inner{layer,offset}` →
//! `LayerOutput{layer,offset}`, `Cache{layer,offset}` → `CacheOutput{layer,offset}`)
//! to the sink's [`FieldKind`]. A later layer's `Read` of that output resolves
//! its field from this map — this is the consumer that the generator's old
//! `read_field` placeholder was reserved for.
//!
//! # `check_batching_parity`
//! Lowers the same artifact through both paths and asserts the new
//! [`BatchingOrder`] reproduces the retired lowered `CodegenLayer` batching
//! sequence position-by-position (`gates.chain(gates_external)`; per-gate `dst`
//! output slots are claim-bearing output roots, an empty-`dst` constraint gate is
//! a constraint slot). Output roots are matched by **sink identity**; constraint
//! roots by [`RootOrigin`] plus a deterministic lowered-expression digest of the
//! constraint root's interned `Expr` subtree.

use std::collections::{HashMap, HashSet};

use field::PrimeField;

use crate::gkr_compiler::codegen_ir::CodegenCircuit;

use super::{
    expr_field, source_field, DagCircuit, DagLayer, Expr, ExprId, FieldKind, ReadPlace, Root,
    RootGroup, RootId, RootSlot, SinkKind, SourceKind,
};

// ── Cross-layer sink-field map ────────────────────────────────────────────────

/// The `ReadPlace` that a later layer would use to read this sink's output, if
/// any. `Inner`/`Cache` sinks are readable cross-layer; `Export`/`Scratch` sinks
/// are not addressable as a `LayerOutput`/`CacheOutput` read.
fn sink_read_place(kind: &SinkKind) -> Option<ReadPlace> {
    match kind {
        SinkKind::Inner { layer, offset } => Some(ReadPlace::LayerOutput {
            layer: *layer,
            offset: *offset,
        }),
        SinkKind::Cache { layer, offset } => Some(ReadPlace::CacheOutput {
            layer: *layer,
            offset: *offset,
        }),
        SinkKind::Export { .. } | SinkKind::Scratch { .. } => None,
    }
}

/// Resolve a layer's source field, falling back to the accumulated cross-layer
/// sink-field map for `Read{LayerOutput|CacheOutput}` reads.
fn resolve_source_field(
    kind: &SourceKind,
    layer: &DagLayer,
    cross_layer: &HashMap<ReadPlace, FieldKind>,
) -> Result<FieldKind, String> {
    match source_field(kind, &layer.roots, &layer.sinks) {
        Ok(f) => Ok(f),
        Err(place) => cross_layer.get(&place).cloned().ok_or_else(|| {
            format!("unresolved cross-layer read field for {:?}", place)
        }),
    }
}

/// Resolve an expr's field, recursing through `Add`/`Mul` and resolving cross-
/// layer reads from `cross_layer`.
fn resolve_expr_field(
    id: ExprId,
    layer: &DagLayer,
    cross_layer: &HashMap<ReadPlace, FieldKind>,
) -> Result<FieldKind, String> {
    // Fast path: the source-only inference already resolves everything that is
    // not a cross-layer read.
    match expr_field(&layer.exprs, &layer.sources, id, &layer.roots, &layer.sinks) {
        Ok(f) => Ok(f),
        Err(_) => {
            // At least one leaf is a cross-layer read; recompute by hand,
            // resolving those reads from `cross_layer`.
            match &layer.exprs[id.0 as usize] {
                Expr::Source(src_id) => {
                    resolve_source_field(&layer.sources[src_id.0 as usize].kind, layer, cross_layer)
                }
                Expr::Add(args) | Expr::Mul(args) => {
                    let mut acc = FieldKind::Base;
                    for &arg in args {
                        let f = resolve_expr_field(arg, layer, cross_layer)?;
                        acc = super::join(acc, f);
                    }
                    Ok(acc)
                }
            }
        }
    }
}

// ── Per-source field-kind invariants (spec §7) ───────────────────────────────

/// `Constant`/`LookupValue` must be base; `Challenge` must be ext. (`source_field`
/// already encodes these, but the validator asserts them explicitly so a future
/// change to the inference can't silently violate the contract.)
fn check_source_field_kinds(layer: &DagLayer, li: usize) -> Result<(), String> {
    for (si, src) in layer.sources.iter().enumerate() {
        match &src.kind {
            SourceKind::Constant { .. } => {
                if source_field(&src.kind, &layer.roots, &layer.sinks)
                    != Ok(FieldKind::Base)
                {
                    return Err(format!(
                        "layer {li} source {si}: Constant must be base-field"
                    ));
                }
            }
            SourceKind::LookupValue { .. } => {
                if source_field(&src.kind, &layer.roots, &layer.sinks)
                    != Ok(FieldKind::Base)
                {
                    return Err(format!(
                        "layer {li} source {si}: LookupValue must be base-field"
                    ));
                }
            }
            SourceKind::Challenge { .. } => {
                if source_field(&src.kind, &layer.roots, &layer.sinks)
                    != Ok(FieldKind::Ext)
                {
                    return Err(format!(
                        "layer {li} source {si}: Challenge must be ext-field"
                    ));
                }
            }
            _ => {}
        }
    }
    Ok(())
}

// ── Dependency-graph acyclicity (Expr→Source, Prior→root, LookupValue.query→Expr)

/// State color for the DFS cycle check over the unified dependency graph.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Color {
    White,
    Gray,
    Black,
}

/// A node in the unified per-layer dependency graph.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Node {
    Expr(u32),
    Root(u32),
}

/// Detect any cycle reachable through the three edge kinds:
/// - `Expr::Add/Mul → operand Expr`
/// - `Expr::Source(LookupValue{query}) → query Expr`
/// - `Expr::Source(Prior{id}) → that root` and `Root → its expr`
///
/// An unchecked `LookupValue.query` cycle would infinite-loop the evaluator
/// (review 2/M2), so this is a hard rejection.
fn check_acyclic(layer: &DagLayer, li: usize) -> Result<(), String> {
    let mut color: HashMap<Node, Color> = HashMap::new();

    // Iterative DFS with an explicit stack to avoid blowing the Rust stack on
    // deep DAGs. Each stack frame carries the node and an index into its
    // successor list (lazily materialized).
    fn successors(node: Node, layer: &DagLayer) -> Vec<Node> {
        match node {
            Node::Expr(e) => match &layer.exprs[e as usize] {
                Expr::Source(src_id) => {
                    match &layer.sources[src_id.0 as usize].kind {
                        SourceKind::LookupValue { query, .. } => vec![Node::Expr(query.0)],
                        SourceKind::Prior { id } => vec![Node::Root(id.0)],
                        _ => vec![],
                    }
                }
                Expr::Add(args) | Expr::Mul(args) => {
                    args.iter().map(|a| Node::Expr(a.0)).collect()
                }
            },
            Node::Root(r) => {
                let expr = match &layer.roots[r as usize] {
                    Root::Output { expr, .. } => *expr,
                    Root::Constraint { expr } => *expr,
                };
                vec![Node::Expr(expr.0)]
            }
        }
    }

    // Visit every expr and every root as a DFS root so disconnected components
    // are covered.
    let mut roots_to_visit: Vec<Node> = Vec::new();
    for i in 0..layer.exprs.len() {
        roots_to_visit.push(Node::Expr(i as u32));
    }
    for i in 0..layer.roots.len() {
        roots_to_visit.push(Node::Root(i as u32));
    }

    for start in roots_to_visit {
        if color.get(&start).copied().unwrap_or(Color::White) != Color::White {
            continue;
        }
        // (node, successors, next-index)
        let mut stack: Vec<(Node, Vec<Node>, usize)> = vec![(start, successors(start, layer), 0)];
        color.insert(start, Color::Gray);
        while let Some((node, succ, idx)) = stack.last_mut() {
            if *idx < succ.len() {
                let next = succ[*idx];
                *idx += 1;
                match color.get(&next).copied().unwrap_or(Color::White) {
                    Color::White => {
                        color.insert(next, Color::Gray);
                        let s = successors(next, layer);
                        stack.push((next, s, 0));
                    }
                    Color::Gray => {
                        return Err(format!(
                            "layer {li}: dependency cycle detected (back edge into a node on the active path)"
                        ));
                    }
                    Color::Black => {}
                }
            } else {
                color.insert(*node, Color::Black);
                stack.pop();
            }
        }
    }
    Ok(())
}

// ── Top-level structural validator ────────────────────────────────────────────

/// Structurally validate a [`DagCircuit`] against the spec §7 invariants.
///
/// Returns `Err(String)` describing the first violation found, `Ok(())` if the
/// circuit is well-formed.
pub fn validate(dag: &DagCircuit) -> Result<(), String> {
    // Accumulated cross-layer sink fields, keyed by the `ReadPlace` a later layer
    // would use to read the producing sink.
    let mut cross_layer: HashMap<ReadPlace, FieldKind> = HashMap::new();

    for (li, layer) in dag.layers.iter().enumerate() {
        // ── Per-source field-kind invariants ─────────────────────────────────
        check_source_field_kinds(layer, li)?;

        // ── Prior resolves to a declared materialization-only (cache) Output root
        // This MUST run before `check_acyclic` so that the DFS `successors`
        // helper can safely index `layer.roots[id.0 as usize]` without
        // panicking on an out-of-range id.  A `Prior` pointing at a
        // `Constraint` root is also rejected here: `source_field` in
        // `field_infer.rs` hits `unreachable!()` on that case, so we gate it
        // cleanly before the field-inference pass ever runs.
        //
        // F1: Also require that the Output's sink is `Cache` (materialization-
        // only).  `eval_layer_root` only materializes non-batching roots; a
        // non-cache Output IS in the batching set and is therefore never placed
        // into the `materialized` map — the `Prior` would panic at eval time.
        for (si, src) in layer.sources.iter().enumerate() {
            if let SourceKind::Prior { id } = &src.kind {
                if id.0 as usize >= layer.roots.len() {
                    return Err(format!(
                        "layer {li} source {si}: Prior references undeclared root {:?}",
                        id
                    ));
                }
                // Per the IR contract, Prior is only valid against a
                // materialization-only Output root (never a Constraint root).
                match &layer.roots[id.0 as usize] {
                    Root::Constraint { .. } => {
                        return Err(format!(
                            "layer {li} source {si}: Prior {:?} must reference an Output root, \
                             not a Constraint root",
                            id
                        ));
                    }
                    Root::Output { sink, .. } => {
                        // F1: the Output must be cache-sink (materialization-only).
                        // A non-cache Output is claim-bearing (in the batching set)
                        // and is never materialized by eval_layer_root; referencing
                        // it via Prior would panic at runtime.
                        if sink.0 as usize >= layer.sinks.len() {
                            return Err(format!(
                                "layer {li} source {si}: Prior {:?} target root references \
                                 undeclared sink {:?}",
                                id, sink
                            ));
                        }
                        if !matches!(layer.sinks[sink.0 as usize].kind, SinkKind::Cache { .. }) {
                            return Err(format!(
                                "layer {li} source {si}: Prior {:?} must reference a \
                                 materialization-only (Cache-sink) Output root, not a \
                                 claim-bearing Output root",
                                id
                            ));
                        }
                    }
                }
            }
        }

        // ── F2: Caches-lead ordering ──────────────────────────────────────────
        // `eval_layer_root` materializes non-batching roots in ascending index
        // order and stops at the target root index (eval.rs pre-pass).  This
        // means a `Prior` referencing a root with index >= the referencing
        // root's index is never materialized and would panic.  The lowering
        // guarantees cache roots occupy LEADING indices; we enforce the same
        // invariant here so that any hand-crafted or future-lowered `DagCircuit`
        // satisfies eval's precondition: all cache roots must precede all
        // non-cache roots.
        let mut seen_non_cache = false;
        for (ri, root) in layer.roots.iter().enumerate() {
            let is_cache = if let Root::Output { sink, .. } = root {
                (sink.0 as usize) < layer.sinks.len()
                    && matches!(layer.sinks[sink.0 as usize].kind, SinkKind::Cache { .. })
            } else {
                false
            };
            if is_cache {
                if seen_non_cache {
                    return Err(format!(
                        "layer {li} root {ri}: cache (materialization-only) root must \
                         appear before all claim-bearing roots (caches-lead ordering \
                         required by eval_layer_root's materialization pre-pass)",
                    ));
                }
            } else {
                seen_non_cache = true;
            }
        }

        // ── Acyclicity over the full dependency graph ─────────────────────────
        check_acyclic(layer, li)?;

        // ── Batching-membership: claim-bearing exactly once, caches absent ────
        // Classify each root: cache-sink Output = materialization-only; every
        // other Output and every Constraint = claim-bearing.
        let batching = &layer.batching.roots;
        let batching_set: HashSet<RootId> = batching.iter().copied().collect();
        if batching_set.len() != batching.len() {
            return Err(format!(
                "layer {li}: a root appears more than once in the batching order"
            ));
        }
        for (ri, root) in layer.roots.iter().enumerate() {
            let id = RootId(ri as u32);
            let is_cache = matches!(root, Root::Output { sink, .. }
                if matches!(layer.sinks[sink.0 as usize].kind, SinkKind::Cache { .. }));
            if is_cache {
                if batching_set.contains(&id) {
                    return Err(format!(
                        "layer {li}: cache root {:?} must not appear in the batching order",
                        id
                    ));
                }
            } else {
                // Claim-bearing root must appear exactly once.
                if !batching_set.contains(&id) {
                    return Err(format!(
                        "layer {li}: claim-bearing root {:?} missing from the batching order",
                        id
                    ));
                }
            }
        }
        // No stray ids in the batching order beyond declared roots.
        for id in batching {
            if id.0 as usize >= layer.roots.len() {
                return Err(format!(
                    "layer {li}: batching order references undeclared root {:?}",
                    id
                ));
            }
        }

        // ── Sink written exactly once per Output root; constraints have none ──
        let mut sink_seen: HashSet<u32> = HashSet::new();
        for (ri, root) in layer.roots.iter().enumerate() {
            match root {
                Root::Output { sink, .. } => {
                    if sink.0 as usize >= layer.sinks.len() {
                        return Err(format!(
                            "layer {li} root {ri}: Output references undeclared sink {:?}",
                            sink
                        ));
                    }
                    if !sink_seen.insert(sink.0) {
                        return Err(format!(
                            "layer {li} root {ri}: sink {:?} written by more than one root",
                            sink
                        ));
                    }
                }
                Root::Constraint { .. } => {
                    // Constraint roots carry no sink — nothing to check here.
                }
            }
        }

        // ── Field inference: every source/expr field inferable; Output expr ───
        //    field == sink field exactly.
        for (ri, root) in layer.roots.iter().enumerate() {
            match root {
                Root::Output { expr, sink } => {
                    let expr_f = resolve_expr_field(*expr, layer, &cross_layer)
                        .map_err(|e| format!("layer {li} root {ri} (Output): {e}"))?;
                    let sink_f = layer.sinks[sink.0 as usize].field;
                    if expr_f != sink_f {
                        return Err(format!(
                            "layer {li} root {ri}: Output expr field {:?} != sink field {:?}",
                            expr_f, sink_f
                        ));
                    }
                }
                Root::Constraint { expr } => {
                    // Field must still be inferable, but there is no sink to match.
                    resolve_expr_field(*expr, layer, &cross_layer)
                        .map_err(|e| format!("layer {li} root {ri} (Constraint): {e}"))?;
                }
            }
        }

        // ── Publish this layer's sink fields for later layers ─────────────────
        for sink in &layer.sinks {
            if let Some(place) = sink_read_place(&sink.kind) {
                cross_layer.insert(place, sink.field);
            }
        }
    }

    Ok(())
}

// ── Lowered-expression digest (constraint-root structural fingerprint) ─────────

/// A deterministic structural digest of the interned `Expr` subtree rooted at
/// `id`. Walks the DAG (with the layer's source table) and folds a stable
/// FNV-1a hash over the operator shape + source kinds. Used to compare two
/// constraint roots beyond their `RootOrigin` — kind alone is too weak, since two
/// constraint roots can swap while both stay kind `Constraint` (review 2/M2).
///
/// # Forward-looking guard (spec §7)
///
/// The inequality branch in `check_batching_parity` (where `prev != digest`) is
/// currently unreachable: the lowering emits exactly one `Root::Constraint` per
/// relation, so every `(group, relation_index)` key in
/// `constraint_digest_by_origin` is unique within a layer — no two batching
/// positions can share the same origin key.
///
/// The digest is intentionally kept as a **forward-looking guard mandated by
/// spec §7** ("constraint roots are compared by `RootOrigin` plus a
/// lowered-expression digest").  If a future lowering ever emits multiple
/// constraint roots for the same relation, the digest would catch a swap where
/// both share an origin but carry distinct expr subtrees.
///
/// The *actual* anti-swap protection that spec §7 requires today is delivered
/// by the position-by-position `RootOrigin` comparison that precedes the digest
/// check.  Do not remove the digest; it is a spec requirement, not dead code.
fn expr_digest(id: ExprId, layer: &DagLayer) -> u64 {
    fn fnv(mut h: u64, byte: u8) -> u64 {
        h ^= byte as u64;
        h.wrapping_mul(0x0000_0100_0000_01b3)
    }
    fn fnv_u64(mut h: u64, v: u64) -> u64 {
        for i in 0..8 {
            h = fnv(h, (v >> (i * 8)) as u8);
        }
        h
    }
    fn walk(id: ExprId, layer: &DagLayer, h: u64) -> u64 {
        let mut h = h;
        match &layer.exprs[id.0 as usize] {
            Expr::Source(src_id) => {
                h = fnv(h, 0x01);
                h = digest_source(&layer.sources[src_id.0 as usize].kind, layer, h);
            }
            Expr::Add(args) => {
                h = fnv(h, 0x02);
                h = fnv_u64(h, args.len() as u64);
                for &a in args {
                    h = walk(a, layer, h);
                }
            }
            Expr::Mul(args) => {
                h = fnv(h, 0x03);
                h = fnv_u64(h, args.len() as u64);
                for &a in args {
                    h = walk(a, layer, h);
                }
            }
        }
        h
    }
    fn digest_source(kind: &SourceKind, layer: &DagLayer, h: u64) -> u64 {
        let mut h = h;
        match kind {
            SourceKind::Read { place } => {
                h = fnv(h, 0x10);
                h = digest_read_place(place, h);
            }
            SourceKind::Prior { id } => {
                h = fnv(h, 0x11);
                h = fnv_u64(h, id.0 as u64);
            }
            SourceKind::Constant { value } => {
                h = fnv(h, 0x12);
                h = fnv_u64(h, *value as u64);
            }
            SourceKind::Challenge { reference } => {
                h = fnv(h, 0x13);
                // Hash the Debug form: a stable, deterministic serialization of
                // the challenge key + power.
                for b in format!("{:?}", reference).bytes() {
                    h = fnv(h, b);
                }
            }
            SourceKind::VirtualSetup { kind } => {
                h = fnv(h, 0x14);
                for b in format!("{:?}", kind).bytes() {
                    h = fnv(h, b);
                }
            }
            SourceKind::LookupValue {
                kind,
                set_index,
                query,
            } => {
                h = fnv(h, 0x15);
                for b in format!("{:?}", kind).bytes() {
                    h = fnv(h, b);
                }
                h = fnv_u64(h, *set_index as u64);
                h = walk(*query, layer, h);
            }
        }
        h
    }
    fn digest_read_place(place: &ReadPlace, h: u64) -> u64 {
        let mut h = h;
        for b in format!("{:?}", place).bytes() {
            h = fnv(h, b);
        }
        h
    }
    // FNV-1a offset basis.
    walk(id, layer, 0xcbf2_9ce4_8422_2325)
}

// ── Batching-sequence parity (spec §7) ─────────────────────────────────────────

/// A single expected batching-sequence slot derived from the retired lowered
/// `CodegenLayer`.
enum RetiredSlot {
    /// An output slot: identified by its output `GKRAddress` (sink identity).
    Output {
        group: RootGroup,
        relation_index: usize,
        /// Index of this output within its gate (0 for single, 0/1 for pairs).
        slot: usize,
        addr: crate::definitions::GKRAddress,
    },
    /// A no-output constraint slot.
    Constraint {
        group: RootGroup,
        relation_index: usize,
    },
}

/// Map a retired output `GKRAddress` to the DAG `SinkKind` it lowers to, for the
/// sink-identity comparison. Mirrors `lower::output_sink_kind`.
fn addr_to_sink_kind(addr: &crate::definitions::GKRAddress) -> Option<SinkKind> {
    use crate::definitions::GKRAddress;
    match addr {
        GKRAddress::InnerLayer { layer, offset } => Some(SinkKind::Inner {
            layer: *layer,
            offset: *offset,
        }),
        GKRAddress::Cached { layer, offset } => Some(SinkKind::Cache {
            layer: *layer,
            offset: *offset,
        }),
        GKRAddress::ScratchSpace(slot) => Some(SinkKind::Scratch { slot: *slot }),
        _ => None,
    }
}

/// Verify the new [`BatchingOrder`] reproduces the retired lowered
/// `CodegenLayer` batching sequence **position-by-position** (spec §7).
///
/// `dag` and `retired` must be lowerings of the SAME artifact. Output roots are
/// matched by sink identity; constraint roots by [`RootOrigin`] + a lowered-
/// expression digest.
pub fn check_batching_parity<F: PrimeField + PartialEq>(
    dag: &DagCircuit,
    retired: &CodegenCircuit,
) -> Result<(), String> {
    if dag.layers.len() != retired.layers.len() {
        return Err(format!(
            "layer count mismatch: dag {} vs retired {}",
            dag.layers.len(),
            retired.layers.len()
        ));
    }

    for (li, (dl, rl)) in dag.layers.iter().zip(retired.layers.iter()).enumerate() {
        // Per-layer: constraint-root digest keyed by its claimed origin. A second
        // batching position claiming the SAME constraint origin but a DIFFERENT
        // expr digest means the sparse origin table aliases two structurally
        // distinct constraint roots (review 2/M2 — kind `Constraint` alone is too
        // weak to catch a swap).
        let mut constraint_digest_by_origin: HashMap<(RootGroup, usize), u64> = HashMap::new();

        // Build the reference sequence from the retired lowered layer, iterating
        // gates THEN gates_external (the retired `assign_batch_powers` order).
        let mut expected: Vec<RetiredSlot> = Vec::new();
        for (group, gates) in [
            (RootGroup::Gates, &rl.gates),
            (RootGroup::GatesExternal, &rl.gates_external),
        ] {
            for (relation_index, gate) in gates.iter().enumerate() {
                if gate.dst.is_empty() {
                    // No-output constraint gate. `num_challenges` is 1 for the
                    // constraint families; each consumes exactly one batch slot.
                    for _ in 0..gate.num_challenges {
                        expected.push(RetiredSlot::Constraint {
                            group: group.clone(),
                            relation_index,
                        });
                    }
                } else {
                    for (slot, out) in gate.dst.iter().enumerate() {
                        expected.push(RetiredSlot::Output {
                            group: group.clone(),
                            relation_index,
                            slot,
                            addr: out.addr.clone(),
                        });
                    }
                }
            }
        }

        // The new batching order, position-by-position.
        let actual = &dl.batching.roots;
        if actual.len() != expected.len() {
            return Err(format!(
                "layer {li}: batching length mismatch: dag {} vs retired {}",
                actual.len(),
                expected.len()
            ));
        }

        for (pos, (root_id, slot)) in actual.iter().zip(expected.iter()).enumerate() {
            // F3: bounds-check before raw indexing — check_batching_parity's public
            // signature accepts an arbitrary DagCircuit, so malformed ids must
            // return Err rather than panic.
            if root_id.0 as usize >= dl.roots.len() {
                return Err(format!(
                    "layer {li} pos {pos}: batching root_id {:?} is out of range \
                     (roots.len() = {})",
                    root_id,
                    dl.roots.len()
                ));
            }
            let root = &dl.roots[root_id.0 as usize];
            let origin = dl.origins.get(root_id).ok_or_else(|| {
                format!("layer {li} pos {pos}: claim-bearing root {root_id:?} has no RootOrigin")
            })?;
            match slot {
                RetiredSlot::Output {
                    group,
                    relation_index,
                    slot: out_slot,
                    addr,
                } => {
                    // Must be an Output root.
                    let sink_id = match root {
                        Root::Output { sink, .. } => *sink,
                        Root::Constraint { .. } => {
                            return Err(format!(
                                "layer {li} pos {pos}: expected Output root, got Constraint"
                            ));
                        }
                    };
                    // Sink identity: the DAG sink must equal the retired output addr's sink.
                    let want_sink = addr_to_sink_kind(addr).ok_or_else(|| {
                        format!(
                            "layer {li} pos {pos}: retired output addr {addr:?} has no sink mapping"
                        )
                    })?;
                    // F3: bounds-check sink_id before indexing.
                    if sink_id.0 as usize >= dl.sinks.len() {
                        return Err(format!(
                            "layer {li} pos {pos}: Output root {:?} references sink {:?} \
                             out of range (sinks.len() = {})",
                            root_id,
                            sink_id,
                            dl.sinks.len()
                        ));
                    }
                    let got_sink = &dl.sinks[sink_id.0 as usize].kind;
                    if *got_sink != want_sink {
                        return Err(format!(
                            "layer {li} pos {pos}: sink-identity mismatch: dag {got_sink:?} vs retired {want_sink:?}"
                        ));
                    }
                    // Origin (group, relation_index, slot) must agree.
                    if origin.group != *group
                        || origin.relation_index != *relation_index
                        || origin.slot != RootSlot::Output(*out_slot)
                    {
                        return Err(format!(
                            "layer {li} pos {pos}: Output origin mismatch: dag {:?} vs retired (group={:?}, rel={relation_index}, slot=Output({out_slot}))",
                            origin, group
                        ));
                    }
                }
                RetiredSlot::Constraint {
                    group,
                    relation_index,
                } => {
                    let expr = match root {
                        Root::Constraint { expr } => *expr,
                        Root::Output { .. } => {
                            return Err(format!(
                                "layer {li} pos {pos}: expected Constraint root, got Output"
                            ));
                        }
                    };
                    if origin.group != *group
                        || origin.relation_index != *relation_index
                        || !matches!(origin.slot, RootSlot::Constraint(_))
                    {
                        return Err(format!(
                            "layer {li} pos {pos}: Constraint origin mismatch: dag {:?} vs retired (group={:?}, rel={relation_index}, slot=Constraint)",
                            origin, group
                        ));
                    }
                    // Structural fingerprint of the constraint's expr subtree.
                    // Two constraint roots that swapped (same kind, but the origin
                    // table now points one origin at the other's expr) carry
                    // distinct digests; cross-check that each origin maps to a
                    // single, consistent digest.
                    let digest = expr_digest(expr, dl);
                    let key = (origin.group.clone(), origin.relation_index);
                    match constraint_digest_by_origin.get(&key) {
                        Some(&prev) if prev != digest => {
                            return Err(format!(
                                "layer {li} pos {pos}: constraint origin {key:?} maps to two distinct expr digests ({prev:#x} != {digest:#x}) — origin/expr desync"
                            ));
                        }
                        _ => {
                            constraint_digest_by_origin.insert(key, digest);
                        }
                    }
                }
            }
        }
    }

    Ok(())
}

// ── Tests ──────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::gkr_compiler::codegen_ir::lower as retired_lower;
    use crate::gkr_compiler::dag_ir::{
        lower_dag, BatchingOrder, ChallengeKey, ChallengePower, ChallengeRef, DagGlobals, DagLayer,
        Expr, ExprId, FieldKind, LookupValueKind, ReadPlace, Root, RootGroup, RootId, RootOrigin,
        RootSlot, SinkId, SinkInfo, SinkKind, SourceId, SourceInfo, SourceKind,
    };
    use crate::gkr_compiler::test_support::{build_add_sub_artifact, ConcreteField};

    // ── Small hand-built circuit helpers ─────────────────────────────────────

    /// A single layer with one base Output root that passes validation:
    /// `Output(expr = Source(Constant(7)))` → `Inner{0,0}` sink (Base).
    fn good_single_layer() -> DagLayer {
        let sources = vec![SourceInfo {
            kind: SourceKind::Constant { value: 7 },
        }];
        let exprs = vec![Expr::Source(SourceId(0))];
        let sinks = vec![SinkInfo {
            kind: SinkKind::Inner { layer: 0, offset: 0 },
            field: FieldKind::Base,
        }];
        let roots = vec![Root::Output {
            expr: ExprId(0),
            sink: SinkId(0),
        }];
        let mut origins = BTreeMap::new();
        origins.insert(
            RootId(0),
            RootOrigin {
                group: RootGroup::Gates,
                relation_index: 0,
                slot: RootSlot::Output(0),
            },
        );
        DagLayer {
            sources,
            exprs,
            roots,
            sinks,
            batching: BatchingOrder {
                roots: vec![RootId(0)],
            },
            origins,
        }
    }

    fn circuit_of(layer: DagLayer) -> DagCircuit {
        DagCircuit {
            layers: vec![layer],
            globals: DagGlobals::default(),
        }
    }

    // ── Positive control ─────────────────────────────────────────────────────

    #[test]
    fn good_circuit_validates() {
        let c = circuit_of(good_single_layer());
        assert!(validate(&c).is_ok(), "well-formed circuit should validate: {:?}", validate(&c));
    }

    // ── Rejection: claim-bearing root missing from BatchingOrder ──────────────

    #[test]
    fn rejects_claim_bearing_root_missing_from_batching() {
        let mut layer = good_single_layer();
        // Drop the only claim-bearing root from the batching order.
        layer.batching = BatchingOrder { roots: vec![] };
        let c = circuit_of(layer);
        let err = validate(&c).expect_err("missing claim-bearing root must be rejected");
        assert!(
            err.contains("missing from the batching order"),
            "unexpected error: {err}"
        );
    }

    // ── Rejection: cache root present in BatchingOrder ────────────────────────

    #[test]
    fn rejects_cache_root_in_batching() {
        // Layer: root 0 is a Cache-sink Output (materialization-only), root 1 is
        // a claim-bearing Inner Output. Putting root 0 in batching is illegal.
        let sources = vec![SourceInfo {
            kind: SourceKind::Constant { value: 1 },
        }];
        let exprs = vec![Expr::Source(SourceId(0))];
        let sinks = vec![
            SinkInfo {
                kind: SinkKind::Cache { layer: 0, offset: 0 },
                field: FieldKind::Base,
            },
            SinkInfo {
                kind: SinkKind::Inner { layer: 0, offset: 0 },
                field: FieldKind::Base,
            },
        ];
        let roots = vec![
            Root::Output {
                expr: ExprId(0),
                sink: SinkId(0),
            },
            Root::Output {
                expr: ExprId(0),
                sink: SinkId(1),
            },
        ];
        let mut origins = BTreeMap::new();
        origins.insert(
            RootId(1),
            RootOrigin {
                group: RootGroup::Gates,
                relation_index: 0,
                slot: RootSlot::Output(0),
            },
        );
        let layer = DagLayer {
            sources,
            exprs,
            roots,
            sinks,
            // Illegal: cache root 0 is in the batching order.
            batching: BatchingOrder {
                roots: vec![RootId(0), RootId(1)],
            },
            origins,
        };
        let err = validate(&circuit_of(layer))
            .expect_err("cache root in batching order must be rejected");
        assert!(
            err.contains("must not appear in the batching order"),
            "unexpected error: {err}"
        );
    }

    // ── Rejection: output expr/sink field mismatch ────────────────────────────

    #[test]
    fn rejects_output_field_mismatch() {
        let mut layer = good_single_layer();
        // Expr is base (Constant) but the sink declares Ext → mismatch.
        layer.sinks[0].field = FieldKind::Ext;
        let err = validate(&circuit_of(layer))
            .expect_err("expr/sink field mismatch must be rejected");
        assert!(
            err.contains("!= sink field"),
            "unexpected error: {err}"
        );
    }

    // ── Rejection: Constant typed Ext ─────────────────────────────────────────
    //
    // A Constant source with an Ext sink mismatch is caught by the field-kind
    // invariant only if the inference is wrong; here we instead exercise the case
    // where the *declared* expr would have to be Ext for a Constant. The strongest
    // direct expression of "Constant typed Ext" is a base Constant feeding an Ext
    // sink — already covered above. This test pins the explicit per-source kind
    // check by constructing a layer whose only claim is a Constant and asserting it
    // is treated as Base end-to-end.

    #[test]
    fn constant_is_base_not_ext() {
        // Constant must infer to Base; an Ext sink for a pure-Constant expr is rejected.
        let mut layer = good_single_layer();
        layer.sinks[0].field = FieldKind::Ext;
        assert!(
            validate(&circuit_of(layer)).is_err(),
            "a Constant expr written to an Ext sink must be rejected (Constant is base)"
        );
    }

    // ── Rejection: cycle through Expr→Source / LookupValue.query→Expr ─────────

    #[test]
    fn rejects_expr_cycle() {
        // Build a self-referential Add: expr 0 = Add([expr 0]) — a direct cycle.
        let sources = vec![SourceInfo {
            kind: SourceKind::Constant { value: 1 },
        }];
        let exprs = vec![Expr::Add(vec![ExprId(0)])]; // refers to itself
        let sinks = vec![SinkInfo {
            kind: SinkKind::Inner { layer: 0, offset: 0 },
            field: FieldKind::Base,
        }];
        let roots = vec![Root::Output {
            expr: ExprId(0),
            sink: SinkId(0),
        }];
        let mut origins = BTreeMap::new();
        origins.insert(
            RootId(0),
            RootOrigin {
                group: RootGroup::Gates,
                relation_index: 0,
                slot: RootSlot::Output(0),
            },
        );
        let layer = DagLayer {
            sources,
            exprs,
            roots,
            sinks,
            batching: BatchingOrder {
                roots: vec![RootId(0)],
            },
            origins,
        };
        let err = validate(&circuit_of(layer)).expect_err("expr cycle must be rejected");
        assert!(err.contains("cycle"), "unexpected error: {err}");
    }

    #[test]
    fn rejects_lookup_query_cycle() {
        // LookupValue whose query expr references the LookupValue's own expr:
        //   expr 0 = Source(LookupValue{ query = expr 0 })  → query cycle.
        let sources = vec![SourceInfo {
            kind: SourceKind::LookupValue {
                kind: LookupValueKind::RangeCheck16Index,
                set_index: 0,
                query: ExprId(0),
            },
        }];
        let exprs = vec![Expr::Source(SourceId(0))]; // expr 0's source queries expr 0
        let sinks = vec![SinkInfo {
            kind: SinkKind::Inner { layer: 0, offset: 0 },
            field: FieldKind::Base,
        }];
        let roots = vec![Root::Output {
            expr: ExprId(0),
            sink: SinkId(0),
        }];
        let mut origins = BTreeMap::new();
        origins.insert(
            RootId(0),
            RootOrigin {
                group: RootGroup::Gates,
                relation_index: 0,
                slot: RootSlot::Output(0),
            },
        );
        let layer = DagLayer {
            sources,
            exprs,
            roots,
            sinks,
            batching: BatchingOrder {
                roots: vec![RootId(0)],
            },
            origins,
        };
        let err =
            validate(&circuit_of(layer)).expect_err("LookupValue.query cycle must be rejected");
        assert!(err.contains("cycle"), "unexpected error: {err}");
    }

    #[test]
    fn rejects_prior_root_cycle() {
        // Two cache-sink roots whose exprs Prior-reference each other (a cycle):
        //   root 0 (Cache{0,0}): expr = Source(Prior(root 1))
        //   root 1 (Cache{0,1}): expr = Source(Prior(root 0))
        //   root 2 (claim-bearing, Inner): constant expr
        //
        // Both root 0 and root 1 are Cache-sink (materialization-only), so the
        // F1 (non-cache Prior target) check passes and the cycle check fires.
        // The caches-lead invariant is satisfied: roots 0 and 1 (cache) precede
        // root 2 (non-cache).
        let sources = vec![
            SourceInfo {
                kind: SourceKind::Prior { id: RootId(1) }, // root 0 → Prior(root 1)
            },
            SourceInfo {
                kind: SourceKind::Prior { id: RootId(0) }, // root 1 → Prior(root 0)
            },
            SourceInfo {
                kind: SourceKind::Constant { value: 1 }, // root 2 (claim-bearing)
            },
        ];
        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Source(SourceId(2)),
        ];
        let sinks = vec![
            SinkInfo {
                kind: SinkKind::Cache { layer: 0, offset: 0 },
                field: FieldKind::Base,
            },
            SinkInfo {
                kind: SinkKind::Cache { layer: 0, offset: 1 },
                field: FieldKind::Base,
            },
            SinkInfo {
                kind: SinkKind::Inner { layer: 0, offset: 0 },
                field: FieldKind::Base,
            },
        ];
        let roots = vec![
            Root::Output { expr: ExprId(0), sink: SinkId(0) }, // cache root 0
            Root::Output { expr: ExprId(1), sink: SinkId(1) }, // cache root 1
            Root::Output { expr: ExprId(2), sink: SinkId(2) }, // claim-bearing root 2
        ];
        let mut origins = BTreeMap::new();
        origins.insert(
            RootId(2),
            RootOrigin {
                group: RootGroup::Gates,
                relation_index: 0,
                slot: RootSlot::Output(0),
            },
        );
        let layer = DagLayer {
            sources,
            exprs,
            roots,
            sinks,
            batching: BatchingOrder {
                roots: vec![RootId(2)], // only the claim-bearing root
            },
            origins,
        };
        let err = validate(&circuit_of(layer)).expect_err("Prior→root cycle must be rejected");
        assert!(err.contains("cycle"), "unexpected error: {err}");
    }

    // ── Cross-layer field resolution ──────────────────────────────────────────

    #[test]
    fn resolves_cross_layer_ext_read_field() {
        // Layer 0: Output(Challenge) → Inner{0,0} sink declared Ext.
        // Layer 1: Output(Read(LayerOutput{0,0})) → Inner{1,0} sink declared Ext.
        //   The read's field must resolve to Ext from layer 0's sink, matching the
        //   layer-1 sink. (If we wrongly defaulted to Base, this would mismatch.)
        let layer0 = {
            let sources = vec![SourceInfo {
                kind: SourceKind::Challenge {
                    reference: ChallengeRef {
                        key: ChallengeKey::ConstraintAggregation,
                        power: ChallengePower::One,
                    },
                },
            }];
            let exprs = vec![Expr::Source(SourceId(0))];
            let sinks = vec![SinkInfo {
                kind: SinkKind::Inner { layer: 0, offset: 0 },
                field: FieldKind::Ext,
            }];
            let roots = vec![Root::Output {
                expr: ExprId(0),
                sink: SinkId(0),
            }];
            let mut origins = BTreeMap::new();
            origins.insert(
                RootId(0),
                RootOrigin {
                    group: RootGroup::Gates,
                    relation_index: 0,
                    slot: RootSlot::Output(0),
                },
            );
            DagLayer {
                sources,
                exprs,
                roots,
                sinks,
                batching: BatchingOrder {
                    roots: vec![RootId(0)],
                },
                origins,
            }
        };
        let layer1 = {
            let sources = vec![SourceInfo {
                kind: SourceKind::Read {
                    place: ReadPlace::LayerOutput { layer: 0, offset: 0 },
                },
            }];
            let exprs = vec![Expr::Source(SourceId(0))];
            let sinks = vec![SinkInfo {
                kind: SinkKind::Inner { layer: 1, offset: 0 },
                field: FieldKind::Ext,
            }];
            let roots = vec![Root::Output {
                expr: ExprId(0),
                sink: SinkId(0),
            }];
            let mut origins = BTreeMap::new();
            origins.insert(
                RootId(0),
                RootOrigin {
                    group: RootGroup::Gates,
                    relation_index: 0,
                    slot: RootSlot::Output(0),
                },
            );
            DagLayer {
                sources,
                exprs,
                roots,
                sinks,
                batching: BatchingOrder {
                    roots: vec![RootId(0)],
                },
                origins,
            }
        };
        let c = DagCircuit {
            layers: vec![layer0, layer1],
            globals: DagGlobals::default(),
        };
        assert!(
            validate(&c).is_ok(),
            "cross-layer Ext read should resolve and match: {:?}",
            validate(&c)
        );
    }

    #[test]
    fn rejects_cross_layer_field_mismatch() {
        // Same as above but layer 1's sink claims Base while the cross-layer read
        // resolves to Ext → mismatch must be rejected.
        let layer0 = {
            let sources = vec![SourceInfo {
                kind: SourceKind::Challenge {
                    reference: ChallengeRef {
                        key: ChallengeKey::ConstraintAggregation,
                        power: ChallengePower::One,
                    },
                },
            }];
            let exprs = vec![Expr::Source(SourceId(0))];
            let sinks = vec![SinkInfo {
                kind: SinkKind::Inner { layer: 0, offset: 0 },
                field: FieldKind::Ext,
            }];
            let roots = vec![Root::Output {
                expr: ExprId(0),
                sink: SinkId(0),
            }];
            let mut origins = BTreeMap::new();
            origins.insert(
                RootId(0),
                RootOrigin {
                    group: RootGroup::Gates,
                    relation_index: 0,
                    slot: RootSlot::Output(0),
                },
            );
            DagLayer {
                sources,
                exprs,
                roots,
                sinks,
                batching: BatchingOrder {
                    roots: vec![RootId(0)],
                },
                origins,
            }
        };
        let layer1 = {
            let sources = vec![SourceInfo {
                kind: SourceKind::Read {
                    place: ReadPlace::LayerOutput { layer: 0, offset: 0 },
                },
            }];
            let exprs = vec![Expr::Source(SourceId(0))];
            let sinks = vec![SinkInfo {
                kind: SinkKind::Inner { layer: 1, offset: 0 },
                field: FieldKind::Base, // WRONG: resolved read is Ext
            }];
            let roots = vec![Root::Output {
                expr: ExprId(0),
                sink: SinkId(0),
            }];
            let mut origins = BTreeMap::new();
            origins.insert(
                RootId(0),
                RootOrigin {
                    group: RootGroup::Gates,
                    relation_index: 0,
                    slot: RootSlot::Output(0),
                },
            );
            DagLayer {
                sources,
                exprs,
                roots,
                sinks,
                batching: BatchingOrder {
                    roots: vec![RootId(0)],
                },
                origins,
            }
        };
        let c = DagCircuit {
            layers: vec![layer0, layer1],
            globals: DagGlobals::default(),
        };
        let err = validate(&c).expect_err("cross-layer field mismatch must be rejected");
        assert!(err.contains("!= sink field"), "unexpected error: {err}");
    }

    // ── add_sub: validate + batching parity ──────────────────────────────────

    #[test]
    fn add_sub_validates() {
        let artifact = build_add_sub_artifact();
        let dag = lower_dag(&artifact).expect("lower_dag must succeed");
        validate(&dag).expect("add_sub DAG must validate");
    }

    #[test]
    fn add_sub_batching_parity() {
        let artifact = build_add_sub_artifact();
        let dag = lower_dag(&artifact).expect("lower_dag must succeed");
        let retired = retired_lower::<ConcreteField>(&artifact).expect("retired lower must succeed");
        check_batching_parity::<ConcreteField>(&dag, &retired)
            .expect("add_sub batching parity must hold");
    }

    /// Non-vacuity guard: a deliberately reversed batching order must FAIL parity.
    /// Without this, a parity check that silently passed everything would go
    /// unnoticed (count-only parity is exactly the bug spec §7 Finding 1 warns of).
    #[test]
    fn parity_rejects_reversed_batching_order() {
        let artifact = build_add_sub_artifact();
        let mut dag = lower_dag(&artifact).expect("lower_dag must succeed");
        let retired = retired_lower::<ConcreteField>(&artifact).expect("retired lower must succeed");
        // Find a layer with >= 2 batched roots and reverse it, then expect failure.
        let mut perturbed = false;
        for layer in &mut dag.layers {
            if layer.batching.roots.len() >= 2 {
                layer.batching.roots.reverse();
                perturbed = true;
                break;
            }
        }
        assert!(perturbed, "fixture must have a layer with >=2 batched roots");
        assert!(
            check_batching_parity::<ConcreteField>(&dag, &retired).is_err(),
            "reversed batching order must FAIL parity (proves test is not vacuous)"
        );
    }

    #[test]
    fn add_sub_no_caches_batching_parity() {
        use crate::gkr_compiler::test_support::build_add_sub_artifact_no_caches;
        let artifact = build_add_sub_artifact_no_caches();
        let dag = lower_dag(&artifact).expect("lower_dag must succeed");
        let retired = retired_lower::<ConcreteField>(&artifact).expect("retired lower must succeed");
        validate(&dag).expect("add_sub (no caches) DAG must validate");
        check_batching_parity::<ConcreteField>(&dag, &retired)
            .expect("add_sub (no caches) batching parity must hold");
    }

    // ── Finding 1: validate must return Err (not panic) on malformed Priors ──

    /// An out-of-range Prior id must produce `Err`, never an index-out-of-bounds
    /// panic.  Previously `check_acyclic` indexed `layer.roots[id.0 as usize]`
    /// before the bounds check ran, causing a panic.
    #[test]
    fn rejects_out_of_range_prior() {
        let mut layer = good_single_layer();
        // Inject a second source whose Prior id (99) is well beyond roots.len() (1).
        layer.sources.push(SourceInfo {
            kind: SourceKind::Prior { id: RootId(99) },
        });
        // Add a second expr and a second sink so the batching/field checks don't
        // fire first for an unrelated reason.
        layer.exprs.push(Expr::Source(SourceId(1)));
        layer.sinks.push(SinkInfo {
            kind: SinkKind::Inner { layer: 0, offset: 1 },
            field: FieldKind::Base,
        });
        // Add a second root pointing at the new expr/sink so the batching order
        // stays well-formed (claim-bearing root present exactly once).
        layer.roots.push(Root::Output {
            expr: ExprId(1),
            sink: SinkId(1),
        });
        layer.batching.roots.push(RootId(1));
        layer.origins.insert(
            RootId(1),
            RootOrigin {
                group: RootGroup::Gates,
                relation_index: 1,
                slot: RootSlot::Output(0),
            },
        );
        let result = validate(&circuit_of(layer));
        assert!(
            result.is_err(),
            "out-of-range Prior must be rejected with Err, not panic"
        );
        let msg = result.unwrap_err();
        assert!(
            msg.contains("undeclared root"),
            "error should mention undeclared root, got: {msg}"
        );
    }

    /// A Prior that points at a `Constraint` root (not an `Output` root) must
    /// produce `Err`.  Previously this reached `source_field` → `unreachable!()`
    /// → panic.
    #[test]
    fn rejects_prior_to_constraint_root() {
        // Layer:
        //   root 0: Constraint { expr 0 }          ← the target of the Prior
        //   root 1: Output { expr 1, sink 0 }       ← claim-bearing
        //
        //   source 0: Constant(7)                   ← feeds expr 0
        //   source 1: Prior { id: RootId(0) }       ← illegal: points at Constraint
        //   expr 0: Source(SourceId(0))
        //   expr 1: Source(SourceId(1))             ← the Output root's expr
        //
        // The Constraint root has no sink; the Output root sinks to Inner{0,0}.
        let sources = vec![
            SourceInfo { kind: SourceKind::Constant { value: 7 } },
            SourceInfo { kind: SourceKind::Prior { id: RootId(0) } }, // invalid: targets Constraint
        ];
        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
        ];
        let sinks = vec![SinkInfo {
            kind: SinkKind::Inner { layer: 0, offset: 0 },
            field: FieldKind::Base,
        }];
        let roots = vec![
            Root::Constraint { expr: ExprId(0) },
            Root::Output { expr: ExprId(1), sink: SinkId(0) },
        ];
        let mut origins = BTreeMap::new();
        // root 0 is a Constraint — claim-bearing; must appear in batching.
        origins.insert(
            RootId(0),
            RootOrigin {
                group: RootGroup::Gates,
                relation_index: 0,
                slot: RootSlot::Constraint(0),
            },
        );
        origins.insert(
            RootId(1),
            RootOrigin {
                group: RootGroup::Gates,
                relation_index: 1,
                slot: RootSlot::Output(0),
            },
        );
        let layer = DagLayer {
            sources,
            exprs,
            roots,
            sinks,
            batching: BatchingOrder {
                roots: vec![RootId(0), RootId(1)],
            },
            origins,
        };
        let result = validate(&circuit_of(layer));
        assert!(
            result.is_err(),
            "Prior pointing at a Constraint root must be rejected with Err, not panic"
        );
        let msg = result.unwrap_err();
        assert!(
            msg.contains("Constraint root"),
            "error should mention Constraint root, got: {msg}"
        );
    }

    // ── F1: Prior → non-cache Output root must be rejected ───────────────────

    /// A `Prior` that points at a claim-bearing (non-cache) `Output` root must
    /// produce `Err`.  Previously this passed `validate` but would panic at
    /// eval time because `eval_layer_root` only materializes cache (non-batching)
    /// roots; a non-cache Output is in the batching set and never placed into
    /// the `materialized` map.
    #[test]
    fn rejects_prior_to_non_cache_output() {
        // Layer:
        //   root 0 (cache):       Output { expr 0, sink 0 (Cache{0,0}) }
        //   root 1 (claim-bearing): Output { expr 1, sink 1 (Inner{0,1}) }
        //
        //   source 0: Constant(5)           → feeds root 0's expr
        //   source 1: Prior { id: RootId(1) } → ILLEGAL: root 1 is NOT a cache root
        //   source 2: Constant(3)           → feeds root 2's expr (see below)
        //   root 2 (claim-bearing): Output { expr 2, sink 2 (Inner{0,2}) }
        //   expr 2: Source(SourceId(1)) [the Prior] — this is the root that uses the bad Prior
        //
        // Actually let's keep it simpler:
        //   root 0 (Inner-sink Output, claim-bearing): expr = Constant(5), sink = Inner{0,0}
        //   root 1 (claim-bearing, uses Prior(0)):    expr = Prior(0), sink = Inner{0,1}
        //
        // source 0: Constant(5)
        // source 1: Prior { id: RootId(0) }   ← RootId(0) is Inner-sink, NOT cache
        // expr 0: Source(0)  → feeds root 0
        // expr 1: Source(1)  → feeds root 1
        let sources = vec![
            SourceInfo { kind: SourceKind::Constant { value: 5 } },
            SourceInfo { kind: SourceKind::Prior { id: RootId(0) } }, // invalid: root 0 is not Cache
        ];
        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
        ];
        let sinks = vec![
            SinkInfo {
                kind: SinkKind::Inner { layer: 0, offset: 0 },
                field: FieldKind::Base,
            },
            SinkInfo {
                kind: SinkKind::Inner { layer: 0, offset: 1 },
                field: FieldKind::Base,
            },
        ];
        let roots = vec![
            Root::Output { expr: ExprId(0), sink: SinkId(0) }, // claim-bearing (non-cache)
            Root::Output { expr: ExprId(1), sink: SinkId(1) }, // claim-bearing
        ];
        let mut origins = BTreeMap::new();
        origins.insert(
            RootId(0),
            RootOrigin {
                group: RootGroup::Gates,
                relation_index: 0,
                slot: RootSlot::Output(0),
            },
        );
        origins.insert(
            RootId(1),
            RootOrigin {
                group: RootGroup::Gates,
                relation_index: 1,
                slot: RootSlot::Output(0),
            },
        );
        let layer = DagLayer {
            sources,
            exprs,
            roots,
            sinks,
            batching: BatchingOrder { roots: vec![RootId(0), RootId(1)] },
            origins,
        };
        let result = validate(&circuit_of(layer));
        assert!(
            result.is_err(),
            "Prior pointing at a non-cache Output root must be rejected with Err, not panic"
        );
        let msg = result.unwrap_err();
        assert!(
            msg.contains("materialization-only") || msg.contains("Cache-sink"),
            "error should mention that the target must be a Cache-sink root, got: {msg}"
        );
    }

    // ── F2: caches-not-leading ordering must be rejected ─────────────────────

    /// A layer where a cache root appears AFTER a claim-bearing root must be
    /// rejected.  The `eval_layer_root` pre-pass only materializes roots with
    /// index < the target root index; a cache root appearing after a
    /// claim-bearing root would never be materialized before a `Prior` that
    /// references it.
    #[test]
    fn rejects_caches_not_leading() {
        // Layer:
        //   root 0 (claim-bearing): Output { expr 0, sink 0 (Inner{0,0}) }
        //   root 1 (cache):         Output { expr 0, sink 1 (Cache{0,0}) }
        //
        // root 1 is a cache root but appears at index 1 (after the claim-bearing
        // root at index 0) — violates caches-lead.
        let sources = vec![SourceInfo {
            kind: SourceKind::Constant { value: 1 },
        }];
        let exprs = vec![Expr::Source(SourceId(0))];
        let sinks = vec![
            SinkInfo {
                kind: SinkKind::Inner { layer: 0, offset: 0 },
                field: FieldKind::Base,
            },
            SinkInfo {
                kind: SinkKind::Cache { layer: 0, offset: 0 },
                field: FieldKind::Base,
            },
        ];
        let roots = vec![
            Root::Output { expr: ExprId(0), sink: SinkId(0) }, // claim-bearing at index 0
            Root::Output { expr: ExprId(0), sink: SinkId(1) }, // cache at index 1 — ILLEGAL
        ];
        let mut origins = BTreeMap::new();
        origins.insert(
            RootId(0),
            RootOrigin {
                group: RootGroup::Gates,
                relation_index: 0,
                slot: RootSlot::Output(0),
            },
        );
        let layer = DagLayer {
            sources,
            exprs,
            roots,
            sinks,
            // Only the claim-bearing root is in batching.
            batching: BatchingOrder { roots: vec![RootId(0)] },
            origins,
        };
        let result = validate(&circuit_of(layer));
        assert!(
            result.is_err(),
            "cache root appearing after a claim-bearing root must be rejected with Err"
        );
        let msg = result.unwrap_err();
        assert!(
            msg.contains("caches-lead") || msg.contains("materialization-only"),
            "error should mention the caches-lead ordering requirement, got: {msg}"
        );
    }

    // ── F3: check_batching_parity must bounds-check root/sink ids ────────────

    /// `check_batching_parity` with a batching root_id that is out of range for
    /// `dl.roots` must return `Err`, not panic.
    #[test]
    fn parity_rejects_out_of_range_root_id() {
        let artifact = build_add_sub_artifact();
        let mut dag = lower_dag(&artifact).expect("lower_dag must succeed");
        let retired = retired_lower::<ConcreteField>(&artifact).expect("retired lower must succeed");
        // Corrupt the batching order in the first layer that has at least one
        // batched root: replace the first root_id with a clearly out-of-range id.
        let target_layer = dag
            .layers
            .iter_mut()
            .find(|l| !l.batching.roots.is_empty())
            .expect("fixture must have at least one layer with batched roots");
        target_layer.batching.roots[0] = RootId(u32::MAX);
        let result = check_batching_parity::<ConcreteField>(&dag, &retired);
        assert!(
            result.is_err(),
            "out-of-range root_id in batching must return Err (not panic)"
        );
        let msg = result.unwrap_err();
        assert!(
            msg.contains("out of range"),
            "error should mention out of range, got: {msg}"
        );
    }
}
