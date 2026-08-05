//! Structural validators for the canonical DAG IR.
//!
//! # `validate`
//! A GPU-independent structural pass over a [`DagCircuit`]. It enforces the
//! spec §7 invariants:
//! - Every claim-bearing root appears exactly once in [`BatchingOrder`];
//!   materialization-only (cache) roots must NOT appear in `BatchingOrder`. A
//!   same-layer cache value is reused by sharing its `ExprId` (DAG sharing), not
//!   by a separate source reference.
//! - Each `Output` root's sink is written exactly once per layer; `Constraint`
//!   roots have no sink.
//! - Every source field is inferable; every expr field is inferable by `join`.
//! - An `Output` root's expr field equals its sink field exactly (no implicit
//!   conversion either direction).
//! - `LookupValue`/`Constant` are base-field; `Challenge` is ext.
//! - Every referenced `ExprId`/`SourceId` (including each `Root.expr`) is in
//!   range and the dependency graph (`Expr→operands`, `LookupValue.query→Expr`,
//!   `Root→expr`) is acyclic.
//!
//! ## Cross-layer field resolution
//! `ReadPlace::LayerOutput`/`CacheOutput` carry no field tag (the model only
//! tags *sinks*). `validate` walks layers in declaration order and accumulates a
//! map from each layer's sink "place" (`Inner{layer,offset}` →
//! `LayerOutput{layer,offset}`, `Cache{layer,offset}` → `CacheOutput{layer,offset}`)
//! to the sink's [`FieldKind`]. A later layer's `Read` of that output resolves
//! its field from this map — this is the consumer that the generator's old
//! `read_field` placeholder was reserved for.

use std::collections::{HashMap, HashSet};

use cs::definitions::gkr::DECODER_LOOKUP_FORMAL_SET_INDEX;

use super::{
    expr_field, source_field, ChallengeKey, ChallengePower, DagCircuit, DagLayer, Expr, ExprId,
    FieldKind, LookupValueKind, RangeWidth, ReadPlace, ResolutionStrategy, RootId, SinkKind,
    SourceId, SourceKind,
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
    cross_layer: &HashMap<ReadPlace, FieldKind>,
) -> Result<FieldKind, String> {
    match source_field(kind) {
        Ok(f) => Ok(f),
        Err(place) => cross_layer
            .get(&place)
            .cloned()
            .ok_or_else(|| format!("unresolved cross-layer read field for {:?}", place)),
    }
}

/// Resolve an expr's field, recursing through `Add`/`Mul` and resolving cross-
/// layer reads from `cross_layer`.
pub(crate) fn resolve_expr_field(
    id: ExprId,
    layer: &DagLayer,
    cross_layer: &HashMap<ReadPlace, FieldKind>,
) -> Result<FieldKind, String> {
    // Fast path: the source-only inference already resolves everything that is
    // not a cross-layer read.
    match expr_field(&layer.exprs, &layer.sources, id) {
        Ok(f) => Ok(f),
        Err(_) => {
            // At least one leaf is a cross-layer read; recompute by hand,
            // resolving those reads from `cross_layer`.
            match &layer.exprs[id.0 as usize] {
                Expr::Source(src_id) => {
                    resolve_source_field(&layer.sources[src_id.0 as usize].kind, cross_layer)
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

/// The cross-layer sink-field map accumulated from layers `0..upto_layer`, exactly as
/// `validate()` publishes it ([validate.rs] sink-publish loop). Used by schedule validation
/// to resolve the field/width of an `ExprId` whose cone reads a prior layer's output/cache.
pub(crate) fn cross_layer_field_map_upto(
    circuit: &DagCircuit,
    upto_layer: usize,
) -> std::collections::HashMap<ReadPlace, FieldKind> {
    let mut cross_layer = std::collections::HashMap::new();
    for layer in circuit.layers.iter().take(upto_layer) {
        for root in &layer.roots {
            if let Some(sink) = &root.materialize {
                if let Some(place) = sink_read_place(&sink.kind) {
                    cross_layer.insert(place, sink.field);
                }
            }
        }
    }
    cross_layer
}

// ── Per-source field-kind invariants (spec §7) ───────────────────────────────

/// `Constant`/`LookupValue` must be base; `Challenge` must be ext. (`source_field`
/// already encodes these, but the validator asserts them explicitly so a future
/// change to the inference can't silently violate the contract.)
fn check_source_field_kinds(layer: &DagLayer, li: usize) -> Result<(), String> {
    for (si, src) in layer.sources.iter().enumerate() {
        match &src.kind {
            SourceKind::Constant { .. } | SourceKind::InitsAndTeardownsTopBits { .. } => {
                if source_field(&src.kind) != Ok(FieldKind::Base) {
                    return Err(format!(
                        "layer {li} source {si}: Constant must be base-field"
                    ));
                }
            }
            SourceKind::LookupValue { .. } => {
                if source_field(&src.kind) != Ok(FieldKind::Base) {
                    return Err(format!(
                        "layer {li} source {si}: LookupValue must be base-field"
                    ));
                }
            }
            SourceKind::Challenge { .. } => {
                if source_field(&src.kind) != Ok(FieldKind::Ext) {
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

// ── Dependency-graph acyclicity (Expr→Source, Root→Expr, LookupValue.query→Expr)

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

/// Return the direct successors of `node` in the per-layer dependency graph,
/// following these edge kinds:
/// - `Expr::Add/Mul → operand Expr`
/// - `Expr::Source(LookupValue{query}) → query Expr`
/// - `Root → its expr`
///
/// NOTE: `successors()` is shared between `check_acyclic` and
/// `collect_root_reachable_exprs`. The `Node::Root → expr` arm is dual-purpose:
/// besides acyclicity, it is the sole descent path for the reachability oracle
/// (`collect_root_reachable_exprs`, seeded from roots) that `check_resolutions`
/// relies on — do NOT drop it.
fn successors(node: Node, layer: &DagLayer) -> Vec<Node> {
    match node {
        Node::Expr(e) => match &layer.exprs[e as usize] {
            Expr::Source(src_id) => match &layer.sources[src_id.0 as usize].kind {
                SourceKind::LookupValue { query, .. } => vec![Node::Expr(query.0)],
                _ => vec![],
            },
            Expr::Add(args) | Expr::Mul(args) => args.iter().map(|a| Node::Expr(a.0)).collect(),
        },
        Node::Root(r) => {
            let expr = layer.roots[r as usize].expr;
            vec![Node::Expr(expr.0)]
        }
    }
}

/// Detect any cycle reachable through the edge kinds in `successors`
/// (`Expr::Add/Mul → operand`, `LookupValue.query → Expr`, `Root → its expr`).
///
/// The expr DAG is acyclic by construction (operands are interned before their
/// parent ⇒ a child `ExprId` is always < its parent), but an unchecked
/// `LookupValue.query` cycle would infinite-loop the evaluator (review 2/M2), so
/// this remains a hard rejection.
fn check_acyclic(layer: &DagLayer, li: usize) -> Result<(), String> {
    let mut color: HashMap<Node, Color> = HashMap::new();

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

// ── Resolution-table helpers ──────────────────────────────────────────────────

/// Collect every `ExprId` reachable from the layer's ROOTS, following the same
/// edges as `check_acyclic`'s `successors` (Add/Mul operands, `LookupValue.query`,
/// `Root → expr`). Seeded from `layer.roots` ONLY — NOT from all exprs (unlike
/// `check_acyclic`) — so it is a true root-reachability oracle.
fn collect_root_reachable_exprs(layer: &DagLayer) -> std::collections::HashSet<u32> {
    let mut visited: std::collections::HashSet<Node> = std::collections::HashSet::new();
    let mut stack: Vec<Node> = (0..layer.roots.len())
        .map(|i| Node::Root(i as u32))
        .collect();
    while let Some(node) = stack.pop() {
        if !visited.insert(node) {
            continue;
        }
        for next in successors(node, layer) {
            if !visited.contains(&next) {
                stack.push(next);
            }
        }
    }
    visited
        .into_iter()
        .filter_map(|n| match n {
            Node::Expr(e) => Some(e),
            Node::Root(_) => None,
        })
        .collect()
}

/// Validate the `resolutions` side-table (M2 forward-peek hints). Fires only on
/// present entries; an empty map is always valid (absent ⇒ recompute).
fn check_resolutions(layer: &DagLayer, li: usize) -> Result<(), String> {
    if layer.resolutions.is_empty() {
        return Ok(());
    }
    let reachable = collect_root_reachable_exprs(layer);
    for (&leaf, strat) in &layer.resolutions {
        if leaf.0 as usize >= layer.exprs.len() {
            return Err(format!(
                "layer {li}: resolution keys out-of-range expr {:?}",
                leaf
            ));
        }
        if !reachable.contains(&leaf.0) {
            return Err(format!(
                "layer {li}: resolution leaf {:?} ({:?}) is not reachable from any root",
                leaf, strat
            ));
        }
        match strat {
            ResolutionStrategy::PeekSingleColumn { set_index, width } => {
                let SourceKind::LookupValue {
                    kind,
                    set_index: si,
                    ..
                } = source_of(leaf, layer)
                else {
                    return Err(format!(
                        "layer {li}: PeekSingleColumn leaf {:?} is not a LookupValue source",
                        leaf
                    ));
                };
                if si != *set_index {
                    return Err(format!(
                        "layer {li}: PeekSingleColumn leaf {:?} set {si} != strategy set {set_index}",
                        leaf
                    ));
                }
                let ok = matches!(
                    (&kind, width),
                    (LookupValueKind::RangeCheck16Index, RangeWidth::Bits16)
                        | (LookupValueKind::TimestampIndex, RangeWidth::Timestamp)
                );
                if !ok {
                    return Err(format!(
                        "layer {li}: PeekSingleColumn leaf {:?} kind/width mismatch",
                        leaf
                    ));
                }
            }
            ResolutionStrategy::PeekAggregate { set_index } => {
                if *set_index == DECODER_LOOKUP_FORMAL_SET_INDEX {
                    return Err(format!(
                        "layer {li}: PeekAggregate must not use the decoder set on {:?}",
                        leaf
                    ));
                }
                check_folded_lookup_shape(leaf, layer, li, *set_index)?;
            }
            ResolutionStrategy::PeekDecoder { predicate, fill } => {
                // The predicate is checked only as "a base-layer read" and is NOT
                // independently verifiable as == machine_state.execute at validate() time
                // (the IR carries no machine_state). That equality is guaranteed by the
                // generator's check_decoder_masks guard + the
                // resolutions_peek_decoder_predicate_matches_global_execute coverage test.
                if !matches!(predicate, ReadPlace::BaseLayerMemory { .. }) {
                    return Err(format!(
                        "layer {li}: PeekDecoder predicate must be a base-layer read on {:?}",
                        leaf
                    ));
                }
                let _ = fill; // FillSource has a single variant; nothing to cross-check statically.
                check_folded_lookup_shape(leaf, layer, li, DECODER_LOOKUP_FORMAL_SET_INDEX)?;
            }
            ResolutionStrategy::PeekSetup => {
                check_folded_setup_shape(leaf, layer, li)?;
            }
        }
    }
    Ok(())
}

/// Validate `leaf` is EXACTLY the `folded_lookup` shape for `expected_set`:
/// 1 column ⇒ bare `Source(LookupValue{GenericColumn{0}})`;
/// >1 columns ⇒ `Add` of one UNSCALED column-0 lookup plus, per j≥1, a 2-factor
/// `Mul([Challenge{LookupMultiplicative,Static(j)}, LookupValue{GenericColumn{j}}])`.
/// Columns must be exactly {0..n-1}; column 0 unscaled; all sets == expected_set.
fn check_folded_lookup_shape(
    leaf: ExprId,
    layer: &DagLayer,
    li: usize,
    expected_set: usize,
) -> Result<(), String> {
    // (column, alpha_power): power None = the unscaled column-0 term.
    let mut terms: Vec<(usize, Option<u32>)> = Vec::new();
    let generic_col = |src_id: SourceId| -> Result<usize, String> {
        match &layer.sources[src_id.0 as usize].kind {
            SourceKind::LookupValue {
                kind: LookupValueKind::GenericColumn { column },
                set_index,
                ..
            } => {
                if *set_index != expected_set {
                    return Err(format!(
                        "layer {li}: folded lookup {:?} set {set_index} != {expected_set}",
                        leaf
                    ));
                }
                Ok(*column)
            }
            other => Err(format!(
                "layer {li}: folded lookup {:?} expected GenericColumn, got {:?}",
                leaf, other
            )),
        }
    };
    match &layer.exprs[leaf.0 as usize] {
        Expr::Source(src_id) => terms.push((generic_col(*src_id)?, None)),
        Expr::Add(add_terms) => {
            for &t in add_terms {
                match &layer.exprs[t.0 as usize] {
                    Expr::Source(src_id) => terms.push((generic_col(*src_id)?, None)),
                    Expr::Mul(factors) => {
                        if factors.len() != 2 {
                            return Err(format!(
                                "layer {li}: folded lookup {:?} term is not a 2-factor Mul",
                                leaf
                            ));
                        }
                        let (mut power, mut column) = (None, None);
                        for &f in factors {
                            let Expr::Source(s) = &layer.exprs[f.0 as usize] else {
                                return Err(format!(
                                    "layer {li}: folded lookup {:?} Mul factor is not a source",
                                    leaf
                                ));
                            };
                            match &layer.sources[s.0 as usize].kind {
                                SourceKind::Challenge { reference } => {
                                    if reference.key != ChallengeKey::LookupMultiplicative {
                                        return Err(format!(
                                            "layer {li}: folded lookup {:?} wrong challenge key",
                                            leaf
                                        ));
                                    }
                                    match reference.power {
                                        ChallengePower::Static(p) => power = Some(p),
                                        ChallengePower::One => {
                                            return Err(format!(
                                                "layer {li}: folded lookup {:?} scaled term must use Static(j)",
                                                leaf
                                            ))
                                        }
                                    }
                                }
                                SourceKind::LookupValue {
                                    kind: LookupValueKind::GenericColumn { column: c },
                                    set_index,
                                    ..
                                } => {
                                    if *set_index != expected_set {
                                        return Err(format!(
                                            "layer {li}: folded lookup {:?} set {set_index} != {expected_set}",
                                            leaf
                                        ));
                                    }
                                    column = Some(*c);
                                }
                                other => {
                                    return Err(format!(
                                        "layer {li}: folded lookup {:?} unexpected Mul factor {:?}",
                                        leaf, other
                                    ))
                                }
                            }
                        }
                        match (power, column) {
                            (Some(p), Some(c)) => terms.push((c, Some(p))),
                            _ => {
                                return Err(format!(
                                "layer {li}: folded lookup {:?} Mul missing challenge or lookup",
                                leaf
                            ))
                            }
                        }
                    }
                    other => {
                        return Err(format!(
                            "layer {li}: folded lookup {:?} unexpected Add term {:?}",
                            leaf, other
                        ))
                    }
                }
            }
        }
        other => {
            return Err(format!(
                "layer {li}: folded lookup {:?} is neither Source nor Add ({:?})",
                leaf, other
            ))
        }
    }
    terms.sort_by_key(|&(c, _)| c);
    if terms.is_empty() {
        return Err(format!(
            "layer {li}: folded lookup {:?} has no columns",
            leaf
        ));
    }
    for (i, &(col, power)) in terms.iter().enumerate() {
        if col != i {
            return Err(format!(
                "layer {li}: folded lookup {:?} columns not contiguous from 0: {:?}",
                leaf, terms
            ));
        }
        match (i, power) {
            (0, None) => {} // column 0 must be unscaled (alpha^0 = 1, emitted as a bare Source)
            (_, Some(p)) if i >= 1 && p as usize == i => {} // column j>=1 scaled by alpha^j
            _ => {
                return Err(format!(
                    "layer {li}: folded lookup {:?} column {i} has wrong scaling {:?}",
                    leaf, power
                ))
            }
        }
    }
    Ok(())
}

/// Validate `leaf` is EXACTLY the `folded_setup` shape:
/// `Σ_j alpha^j · Read(Setup{..})`, column 0 unscaled, j≥1 scaled by `alpha^j`.
///
/// Validates the alpha-power STRUCTURE (powers exactly {0..n-1}, column 0
/// unscaled, all leaves Setup reads) but deliberately does NOT bind each setup
/// column to its power, because `PeekSetup` is row-indexed and carries no
/// column metadata.
fn check_folded_setup_shape(leaf: ExprId, layer: &DagLayer, li: usize) -> Result<(), String> {
    let mut powers: Vec<Option<u32>> = Vec::new(); // None = the unscaled (power-0) term
    let is_setup = |src_id: SourceId| -> Result<(), String> {
        match &layer.sources[src_id.0 as usize].kind {
            SourceKind::Read {
                place: ReadPlace::Setup { .. },
            } => Ok(()),
            other => Err(format!(
                "layer {li}: folded setup {:?} expected Read(Setup), got {:?}",
                leaf, other
            )),
        }
    };
    match &layer.exprs[leaf.0 as usize] {
        Expr::Source(src_id) => {
            is_setup(*src_id)?;
            powers.push(None);
        }
        Expr::Add(add_terms) => {
            for &t in add_terms {
                match &layer.exprs[t.0 as usize] {
                    Expr::Source(src_id) => {
                        is_setup(*src_id)?;
                        powers.push(None);
                    }
                    Expr::Mul(factors) => {
                        if factors.len() != 2 {
                            return Err(format!(
                                "layer {li}: folded setup {:?} term is not a 2-factor Mul",
                                leaf
                            ));
                        }
                        let (mut power, mut saw_setup) = (None, false);
                        for &f in factors {
                            let Expr::Source(s) = &layer.exprs[f.0 as usize] else {
                                return Err(format!(
                                    "layer {li}: folded setup {:?} Mul factor is not a source",
                                    leaf
                                ));
                            };
                            match &layer.sources[s.0 as usize].kind {
                                SourceKind::Challenge { reference } => {
                                    if reference.key != ChallengeKey::LookupMultiplicative {
                                        return Err(format!(
                                            "layer {li}: folded setup {:?} wrong challenge key",
                                            leaf
                                        ));
                                    }
                                    match reference.power {
                                        ChallengePower::Static(p) => power = Some(p),
                                        ChallengePower::One => {
                                            return Err(format!(
                                                "layer {li}: folded setup {:?} scaled term must use Static(j)",
                                                leaf
                                            ))
                                        }
                                    }
                                }
                                SourceKind::Read {
                                    place: ReadPlace::Setup { .. },
                                } => {
                                    saw_setup = true;
                                }
                                other => {
                                    return Err(format!(
                                        "layer {li}: folded setup {:?} unexpected Mul factor {:?}",
                                        leaf, other
                                    ))
                                }
                            }
                        }
                        match (power, saw_setup) {
                            (Some(p), true) => powers.push(Some(p)),
                            _ => {
                                return Err(format!(
                                "layer {li}: folded setup {:?} Mul missing challenge or Setup read",
                                leaf
                            ))
                            }
                        }
                    }
                    other => {
                        return Err(format!(
                            "layer {li}: folded setup {:?} unexpected Add term {:?}",
                            leaf, other
                        ))
                    }
                }
            }
        }
        other => {
            return Err(format!(
                "layer {li}: folded setup {:?} is neither Source nor Add ({:?})",
                leaf, other
            ))
        }
    }
    if powers.is_empty() {
        return Err(format!(
            "layer {li}: folded setup {:?} has no columns",
            leaf
        ));
    }
    let (mut seen_zero, mut scaled) = (false, Vec::new());
    for p in powers {
        match p {
            None if seen_zero => {
                return Err(format!(
                    "layer {li}: folded setup {:?} has two unscaled terms",
                    leaf
                ))
            }
            None => seen_zero = true,
            Some(p) => scaled.push(p),
        }
    }
    if !seen_zero {
        return Err(format!(
            "layer {li}: folded setup {:?} missing unscaled column-0 term",
            leaf
        ));
    }
    scaled.sort_unstable();
    if scaled.iter().enumerate().any(|(i, &p)| p as usize != i + 1) {
        return Err(format!(
            "layer {li}: folded setup {:?} alpha powers not {{1..n-1}}: {:?}",
            leaf, scaled
        ));
    }
    Ok(())
}

/// Read the `SourceKind` of a leaf that is a bare `Expr::Source`, else a sentinel
/// `Constant` (used only by the shape checks above).
fn source_of(leaf: ExprId, layer: &DagLayer) -> SourceKind {
    if let Expr::Source(src_id) = &layer.exprs[leaf.0 as usize] {
        layer.sources[src_id.0 as usize].kind.clone()
    } else {
        SourceKind::Constant { value: 0 }
    }
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

        // ── Reference-range invariants ────────────────────────────────────────
        // The expr DAG is acyclic by construction (operands interned before the
        // parent ⇒ child `ExprId` < parent), so there is no Prior/caches-lead
        // ordering to enforce. We DO check that every referenced index is in
        // range BEFORE `check_acyclic` so the DFS `successors` helper can index
        // `layer.exprs`/`layer.roots` without panicking.
        //
        // Every `Expr` operand `ExprId`, every `Source` id, and every
        // `LookupValue.query` must point inside the arena tables…
        for (ei, expr) in layer.exprs.iter().enumerate() {
            match expr {
                Expr::Source(src_id) => {
                    if src_id.0 as usize >= layer.sources.len() {
                        return Err(format!(
                            "layer {li} expr {ei}: Source references out-of-range source {:?}",
                            src_id
                        ));
                    }
                    if let SourceKind::LookupValue { query, .. } =
                        &layer.sources[src_id.0 as usize].kind
                    {
                        if query.0 as usize >= layer.exprs.len() {
                            return Err(format!(
                                "layer {li} expr {ei}: LookupValue.query references out-of-range expr {:?}",
                                query
                            ));
                        }
                    }
                }
                Expr::Add(args) | Expr::Mul(args) => {
                    for a in args {
                        if a.0 as usize >= layer.exprs.len() {
                            return Err(format!(
                                "layer {li} expr {ei}: operand references out-of-range expr {:?}",
                                a
                            ));
                        }
                    }
                }
            }
        }
        // …and every `Root.expr` must be in range too (review codex#5: keep the
        // root pointer explicitly checked, not just the arena exprs).
        for (ri, root) in layer.roots.iter().enumerate() {
            let expr = root.expr;
            if expr.0 as usize >= layer.exprs.len() {
                return Err(format!(
                    "layer {li} root {ri}: Root references out-of-range expr {:?}",
                    expr
                ));
            }
        }

        // ── Acyclicity over the full dependency graph ─────────────────────────
        check_acyclic(layer, li)?;
        check_resolutions(layer, li)?;

        // ── Batching-membership: claim-bearing exactly once, caches absent ────
        // Classify each root by its attributes: `claim: Some` = claim-bearing
        // (must appear in the batching order exactly once); `claim: None` =
        // materialization-only (a cache; must be absent). This mirrors the
        // lowering's `claim.is_some()` batching filter and the attribute-shape
        // test (`cache_is_materialize_only_claims_are_batched`).
        let batching = &layer.batching.roots;
        let batching_set: HashSet<RootId> = batching.iter().copied().collect();
        if batching_set.len() != batching.len() {
            return Err(format!(
                "layer {li}: a root appears more than once in the batching order"
            ));
        }
        for (ri, root) in layer.roots.iter().enumerate() {
            let id = RootId(ri as u32);
            // A root with neither a sink nor a claim is a degenerate shape that
            // lowering never emits; reject it explicitly so hand-crafted or
            // mis-generated DAGs are caught before any downstream pass.
            if root.materialize.is_none() && root.claim.is_none() {
                return Err(format!(
                    "layer {li} root {ri}: root carries neither materialize nor claim \
                     — degenerate (None, None) root is not a valid DAG IR shape"
                ));
            }
            if root.claim.is_some() {
                // Claim-bearing root must appear exactly once.
                if !batching_set.contains(&id) {
                    return Err(format!(
                        "layer {li}: claim-bearing root {:?} missing from the batching order",
                        id
                    ));
                }
            } else {
                // Materialization-only (cache) root must be absent.
                if batching_set.contains(&id) {
                    return Err(format!(
                        "layer {li}: cache root {:?} must not appear in the batching order",
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

        // ── Each materialized sink written by exactly one root ────────────────
        // Constraint roots (`materialize: None`) write no sink. Sink identity is
        // now the inlined `SinkKind` (carries layer/offset/slot), so dedup by it.
        let mut sink_seen: HashSet<SinkKind> = HashSet::new();
        for (ri, root) in layer.roots.iter().enumerate() {
            if let Some(sink) = &root.materialize {
                if !sink_seen.insert(sink.kind.clone()) {
                    return Err(format!(
                        "layer {li} root {ri}: sink {:?} written by more than one root",
                        sink.kind
                    ));
                }
            }
        }

        // ── Field inference: every source/expr field inferable; for a ─────────
        //    materialized root, expr field == sink field exactly (this is also
        //    the cache-Output expr/sink-field invariant — cache roots carry
        //    `materialize: Some(Cache)` and pass through here).
        for (ri, root) in layer.roots.iter().enumerate() {
            let expr_f = resolve_expr_field(root.expr, layer, &cross_layer)
                .map_err(|e| format!("layer {li} root {ri}: {e}"))?;
            if let Some(sink) = &root.materialize {
                if expr_f != sink.field {
                    return Err(format!(
                        "layer {li} root {ri}: materialized root expr field {:?} != sink field {:?}",
                        expr_f, sink.field
                    ));
                }
            }
        }

        // ── Publish this layer's sink fields for later layers ─────────────────
        // Iterate roots and visit each `materialize` sink. Cache roots
        // (`claim: None`) MUST be visited: `sink_read_place` returns `Some` for
        // `Cache`, so a later layer's `Read{CacheOutput}` can resolve its field.
        for root in &layer.roots {
            if let Some(sink) = &root.materialize {
                if let Some(place) = sink_read_place(&sink.kind) {
                    cross_layer.insert(place, sink.field);
                }
            }
        }
    }

    Ok(())
}

// ── `simplify_layer` output invariant (Task 5) ────────────────────────────────

/// Structurally validate that every layer of `dag` is a fixpoint of
/// `simplify_layer` — i.e. running `simplify_layer` on it again would be a
/// no-op. For every ROOT-REACHABLE, non-fenced (`layer.resolutions` keys are
/// exempt) `Add`/`Mul` node:
/// - no same-op child with fan-out==1 (a non-fenced child) — would flatten;
/// - at most one `Constant` operand — multiple would const-fold;
/// - no `Constant(0)` operand in `Add`, no `Constant(1)` operand in `Mul` —
///   identity would drop it;
/// - no empty or unary non-fenced `Add`/`Mul` — collapse would fire;
/// - EXCEPTION: a `Mul` retaining a `Constant(0)` operand is legal iff the
///   node is NOT provably Base (the field-suppressed annihilator guard: an
///   Ext-valued zero product is intentionally NOT rewritten to a Base
///   constant).
///
/// `dag` need not otherwise satisfy [`validate`]'s artifact-shape invariants;
/// this is a narrower, simplify-specific check reusable on hand-built or
/// intermediate DAGs.
pub fn validate_simplified(dag: &DagCircuit) -> Result<(), String> {
    for (li, layer) in dag.layers.iter().enumerate() {
        let fenced: HashSet<ExprId> = layer.resolutions.keys().copied().collect();
        let reachable = collect_root_reachable_exprs(layer);
        let fan_out = super::simplify::fan_out(layer);
        let mut base_memo: HashMap<ExprId, bool> = HashMap::new();
        for &e in &reachable {
            let id = ExprId(e);
            if fenced.contains(&id) {
                continue;
            }
            let (is_add, children) = match &layer.exprs[e as usize] {
                Expr::Add(c) => (true, c),
                Expr::Mul(c) => (false, c),
                Expr::Source(_) => continue,
            };
            let op_name = if is_add { "Add" } else { "Mul" };

            if children.len() < 2 {
                return Err(format!(
                    "layer {li} expr {:?}: non-fenced {op_name} has {} operand(s), \
                     must have >=2 (empty/unary op would have been collapsed)",
                    id,
                    children.len()
                ));
            }

            let mut const_count = 0usize;
            let mut const_zero = false;
            let mut const_one = false;
            for &c in children {
                let same_op = matches!(
                    (&layer.exprs[c.0 as usize], is_add),
                    (Expr::Add(_), true) | (Expr::Mul(_), false)
                );
                if same_op && !fenced.contains(&c) && fan_out.get(&c).copied().unwrap_or(0) == 1 {
                    return Err(format!(
                        "layer {li} expr {:?}: unflattened same-op fan-out-1 child {:?} \
                         (simplify_layer would flatten this)",
                        id, c
                    ));
                }
                if let Expr::Source(sid) = &layer.exprs[c.0 as usize] {
                    if let SourceKind::Constant { value } = layer.sources[sid.0 as usize].kind {
                        const_count += 1;
                        const_zero |= value == 0;
                        const_one |= value == 1;
                    }
                }
            }

            if const_count > 1 {
                return Err(format!(
                    "layer {li} expr {:?}: {op_name} retains {const_count} Constant operands, \
                     must be const-folded to at most 1",
                    id
                ));
            }
            if is_add && const_zero {
                return Err(format!(
                    "layer {li} expr {:?}: Add retains a Constant(0) operand (identity not applied)",
                    id
                ));
            }
            if !is_add && const_one {
                return Err(format!(
                    "layer {li} expr {:?}: Mul retains a Constant(1) operand (identity not applied)",
                    id
                ));
            }
            if !is_add && const_zero {
                // Field-suppressed annihilator exception: legal iff NOT provably Base.
                if super::simplify::provably_base(layer, &mut base_memo, id) {
                    return Err(format!(
                        "layer {li} expr {:?}: Mul retains a Constant(0) operand but the node \
                         is provably Base — the annihilator rewrite should have fired",
                        id
                    ));
                }
            }
        }
    }
    Ok(())
}
