//! Structural validators for the DAG IR + batching-sequence parity against the
//! retired codegen IR (spec §7).
//!
//! # `validate`
//! A pure `cs`-internal structural pass over a [`DagCircuit`]. It enforces the
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

use crate::definitions::gkr::DECODER_LOOKUP_FORMAL_SET_INDEX;
use crate::gkr_compiler::codegen_ir::CodegenCircuit;

use super::{
    expr_field, source_field, ChallengeKey, ChallengePower, DagCircuit, DagLayer, Expr, ExprId,
    FieldKind, LookupValueKind, RangeWidth, ReadPlace, ResolutionStrategy, RootGroup,
    RootId, RootSlot, SinkKind, SourceId, SourceKind,
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

// ── Per-source field-kind invariants (spec §7) ───────────────────────────────

/// `Constant`/`LookupValue` must be base; `Challenge` must be ext. (`source_field`
/// already encodes these, but the validator asserts them explicitly so a future
/// change to the inference can't silently violate the contract.)
fn check_source_field_kinds(layer: &DagLayer, li: usize) -> Result<(), String> {
    for (si, src) in layer.sources.iter().enumerate() {
        match &src.kind {
            SourceKind::Constant { .. } => {
                if source_field(&src.kind)
                    != Ok(FieldKind::Base)
                {
                    return Err(format!(
                        "layer {li} source {si}: Constant must be base-field"
                    ));
                }
            }
            SourceKind::LookupValue { .. } => {
                if source_field(&src.kind)
                    != Ok(FieldKind::Base)
                {
                    return Err(format!(
                        "layer {li} source {si}: LookupValue must be base-field"
                    ));
                }
            }
            SourceKind::Challenge { .. } => {
                if source_field(&src.kind)
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
            Expr::Source(src_id) => {
                match &layer.sources[src_id.0 as usize].kind {
                    SourceKind::LookupValue { query, .. } => vec![Node::Expr(query.0)],
                    _ => vec![],
                }
            }
            Expr::Add(args) | Expr::Mul(args) => {
                args.iter().map(|a| Node::Expr(a.0)).collect()
            }
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
    let mut stack: Vec<Node> = (0..layer.roots.len()).map(|i| Node::Root(i as u32)).collect();
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
                let SourceKind::LookupValue { kind, set_index: si, .. } =
                    source_of(leaf, layer)
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
            (0, None) => {}                                  // column 0 must be unscaled (alpha^0 = 1, emitted as a bare Source)
            (_, Some(p)) if i >= 1 && p as usize == i => {} // column j>=1 scaled by alpha^j
            _ => return Err(format!(
                "layer {li}: folded lookup {:?} column {i} has wrong scaling {:?}",
                leaf, power
            )),
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
            SourceKind::Read { place: ReadPlace::Setup { .. } } => Ok(()),
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
                                SourceKind::Read { place: ReadPlace::Setup { .. } } => {
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
/// currently unreachable: the lowering emits exactly one constraint root per
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
            // Claim-bearing identity comes from the inlined `claim.origin` (codex#5
            // soundness anchor: origin + sink identity are compared position-by-
            // position over the claim-bearing roots).
            let origin = root.claim.as_ref().map(|c| &c.origin).ok_or_else(|| {
                format!("layer {li} pos {pos}: claim-bearing root {root_id:?} has no RootOrigin")
            })?;
            match slot {
                RetiredSlot::Output {
                    group,
                    relation_index,
                    slot: out_slot,
                    addr,
                } => {
                    // Must be a materialized (Output) root.
                    let got_sink = match &root.materialize {
                        Some(s) => &s.kind,
                        None => {
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
                    // A constraint root is claim-only: `materialize: None`.
                    if root.materialize.is_some() {
                        return Err(format!(
                            "layer {li} pos {pos}: expected Constraint root, got Output"
                        ));
                    }
                    let expr = root.expr;
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
    use crate::definitions::gkr::DECODER_LOOKUP_FORMAL_SET_INDEX;
    use crate::gkr_compiler::codegen_ir::lower as retired_lower;
    use crate::gkr_compiler::dag_ir::{
        lower_dag, BatchingOrder, ChallengeKey, ChallengePower, ChallengeRef, ClaimInfo, DagGlobals,
        DagLayer, Expr, ExprId, FieldKind, FillSource, LookupValueKind, ReadPlace, Root, RootGroup,
        RootId, RootOrigin, RootSlot, SinkInfo, SinkKind, SourceId, SourceInfo, SourceKind,
    };
    use crate::gkr_compiler::test_support::{build_add_sub_artifact, ConcreteField};

    // ── Root literal builders (sink inlined into `materialize`, origin into
    //    `claim`) — keep hand-built test layers concise after the Task-2 struct
    //    dissolve. ────────────────────────────────────────────────────────────

    /// A claim-bearing Output root with a `Gates`/`Output(0)` origin.
    fn out_root(expr: ExprId, kind: SinkKind, field: FieldKind) -> Root {
        Root {
            expr,
            materialize: Some(SinkInfo { kind, field }),
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index: 0,
                    slot: RootSlot::Output(0),
                },
            }),
        }
    }

    /// A materialization-only cache root (`claim: None`).
    fn cache_only_root(expr: ExprId, kind: SinkKind, field: FieldKind) -> Root {
        Root {
            expr,
            materialize: Some(SinkInfo { kind, field }),
            claim: None,
        }
    }

    // ── Small hand-built circuit helpers ─────────────────────────────────────

    /// A single layer with one base Output root that passes validation:
    /// `Output(expr = Source(Constant(7)))` → `Inner{0,0}` sink (Base).
    fn good_single_layer() -> DagLayer {
        let sources = vec![SourceInfo {
            kind: SourceKind::Constant { value: 7 },
        }];
        let exprs = vec![Expr::Source(SourceId(0))];
        let roots = vec![out_root(
            ExprId(0),
            SinkKind::Inner { layer: 0, offset: 0 },
            FieldKind::Base,
        )];
        DagLayer {
            sources,
            exprs,
            roots,
            batching: BatchingOrder {
                roots: vec![RootId(0)],
            },
            resolutions: BTreeMap::new(),
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
        let roots = vec![
            // root 0: materialization-only cache (claim: None).
            cache_only_root(ExprId(0), SinkKind::Cache { layer: 0, offset: 0 }, FieldKind::Base),
            // root 1: claim-bearing Inner Output.
            out_root(ExprId(0), SinkKind::Inner { layer: 0, offset: 0 }, FieldKind::Base),
        ];
        let layer = DagLayer {
            sources,
            exprs,
            roots,
            // Illegal: cache root 0 is in the batching order.
            batching: BatchingOrder {
                roots: vec![RootId(0), RootId(1)],
            },
            resolutions: BTreeMap::new(),
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
        layer.roots[0].materialize.as_mut().unwrap().field = FieldKind::Ext;
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
        layer.roots[0].materialize.as_mut().unwrap().field = FieldKind::Ext;
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
        let roots = vec![out_root(
            ExprId(0),
            SinkKind::Inner { layer: 0, offset: 0 },
            FieldKind::Base,
        )];
        let layer = DagLayer {
            sources,
            exprs,
            roots,
            batching: BatchingOrder {
                roots: vec![RootId(0)],
            },
            resolutions: BTreeMap::new(),
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
        let roots = vec![out_root(
            ExprId(0),
            SinkKind::Inner { layer: 0, offset: 0 },
            FieldKind::Base,
        )];
        let layer = DagLayer {
            sources,
            exprs,
            roots,
            batching: BatchingOrder {
                roots: vec![RootId(0)],
            },
            resolutions: BTreeMap::new(),
        };
        let err =
            validate(&circuit_of(layer)).expect_err("LookupValue.query cycle must be rejected");
        assert!(err.contains("cycle"), "unexpected error: {err}");
    }

    // (Task 1 removed `SourceKind::Prior`. The former `rejects_prior_root_cycle`
    // test built a Prior↔Prior root cycle; cache reuse is now DAG sharing, and
    // the expr DAG is acyclic by construction, so that cycle shape is no longer
    // representable. The retained `LookupValue.query` cycle test still exercises
    // the acyclicity check.)

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
            let roots = vec![out_root(
                ExprId(0),
                SinkKind::Inner { layer: 0, offset: 0 },
                FieldKind::Ext,
            )];
            DagLayer {
                sources,
                exprs,
                roots,
                batching: BatchingOrder {
                    roots: vec![RootId(0)],
                },
                resolutions: BTreeMap::new(),
            }
        };
        let layer1 = {
            let sources = vec![SourceInfo {
                kind: SourceKind::Read {
                    place: ReadPlace::LayerOutput { layer: 0, offset: 0 },
                },
            }];
            let exprs = vec![Expr::Source(SourceId(0))];
            let roots = vec![out_root(
                ExprId(0),
                SinkKind::Inner { layer: 1, offset: 0 },
                FieldKind::Ext,
            )];
            DagLayer {
                sources,
                exprs,
                roots,
                batching: BatchingOrder {
                    roots: vec![RootId(0)],
                },
                resolutions: BTreeMap::new(),
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
            let roots = vec![out_root(
                ExprId(0),
                SinkKind::Inner { layer: 0, offset: 0 },
                FieldKind::Ext,
            )];
            DagLayer {
                sources,
                exprs,
                roots,
                batching: BatchingOrder {
                    roots: vec![RootId(0)],
                },
                resolutions: BTreeMap::new(),
            }
        };
        let layer1 = {
            let sources = vec![SourceInfo {
                kind: SourceKind::Read {
                    place: ReadPlace::LayerOutput { layer: 0, offset: 0 },
                },
            }];
            let exprs = vec![Expr::Source(SourceId(0))];
            let roots = vec![out_root(
                ExprId(0),
                SinkKind::Inner { layer: 1, offset: 0 },
                FieldKind::Base, // WRONG: resolved read is Ext
            )];
            DagLayer {
                sources,
                exprs,
                roots,
                batching: BatchingOrder {
                    roots: vec![RootId(0)],
                },
                resolutions: BTreeMap::new(),
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

    // (Task 1 removed `SourceKind::Prior` and the caches-lead ordering invariant.
    // The former Prior-target / caches-not-leading rejection tests
    // (`rejects_out_of_range_prior`, `rejects_prior_to_constraint_root`,
    // `rejects_prior_to_non_cache_output`, `rejects_caches_not_leading`) tested
    // invariants that no longer exist; out-of-range index references are now
    // covered by the reference-range invariants in `validate`.)

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

    // ── Resolution side-table helpers ─────────────────────────────────────────

    fn layer_with_single_generic_lookup(set_index: usize) -> DagLayer {
        // A real 2-column folded lookup over an Ext sink:
        //   sources: 0=Constant(0) (query), 1=lv0, 2=alpha^1, 3=lv1
        //   exprs:   0=Source(0)=query, 1=Source(1)=lv0, 2=Source(2)=alpha^1,
        //            3=Source(3)=lv1, 4=Mul([2,3]), 5=Add([1,4])  <- fold leaf
        let query = ExprId(0);
        let lv = |column: usize| SourceInfo {
            kind: SourceKind::LookupValue {
                kind: LookupValueKind::GenericColumn { column },
                set_index,
                query,
            },
        };
        let alpha1 = SourceInfo {
            kind: SourceKind::Challenge {
                reference: ChallengeRef {
                    key: ChallengeKey::LookupMultiplicative,
                    power: ChallengePower::Static(1),
                },
            },
        };
        DagLayer {
            sources: vec![
                SourceInfo { kind: SourceKind::Constant { value: 0 } },
                lv(0),
                alpha1,
                lv(1),
            ],
            exprs: vec![
                Expr::Source(SourceId(0)),             // 0: query const
                Expr::Source(SourceId(1)),             // 1: lv0 (column 0, unscaled)
                Expr::Source(SourceId(2)),             // 2: alpha^1
                Expr::Source(SourceId(3)),             // 3: lv1 (column 1)
                Expr::Mul(vec![ExprId(2), ExprId(3)]), // 4: alpha^1 * lv1
                Expr::Add(vec![ExprId(1), ExprId(4)]), // 5: fold leaf
            ],
            roots: vec![out_root(
                ExprId(5),
                SinkKind::Inner { layer: 0, offset: 0 },
                FieldKind::Ext,
            )],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        }
    }

    fn generic_lookup_leaf_expr(_layer: &DagLayer) -> ExprId {
        ExprId(5) // the Add fold leaf built above
    }

    /// A 2-column setup fold used for B2 tests.
    ///
    /// sources: 0=Read(Setup{col:0}), 1=alpha^1 (Challenge{LookupMultiplicative,Static(1)}), 2=Read(Setup{col:1})
    /// exprs: 0=Source(0), 1=Source(1), 2=Source(2), 3=Mul([1,2]), 4=Add([0,3])
    /// root: Output{expr=ExprId(4)} materialize=SinkKind::Inner{layer:0,offset:0}, FieldKind::Ext
    fn layer_with_single_setup_fold() -> DagLayer {
        DagLayer {
            sources: vec![
                SourceInfo { kind: SourceKind::Read { place: ReadPlace::Setup { column: 0 } } }, // 0
                SourceInfo {
                    kind: SourceKind::Challenge {
                        reference: ChallengeRef {
                            key: ChallengeKey::LookupMultiplicative,
                            power: ChallengePower::Static(1),
                        },
                    },
                }, // 1: alpha^1
                SourceInfo { kind: SourceKind::Read { place: ReadPlace::Setup { column: 1 } } }, // 2
            ],
            exprs: vec![
                Expr::Source(SourceId(0)),             // 0: Setup col 0 (unscaled)
                Expr::Source(SourceId(1)),             // 1: alpha^1
                Expr::Source(SourceId(2)),             // 2: Setup col 1
                Expr::Mul(vec![ExprId(1), ExprId(2)]), // 3: alpha^1 * Setup{1}
                Expr::Add(vec![ExprId(0), ExprId(3)]), // 4: fold leaf
            ],
            roots: vec![out_root(
                ExprId(4),
                SinkKind::Inner { layer: 0, offset: 0 },
                FieldKind::Ext,
            )],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        }
    }

    // ── Resolution side-table tests ───────────────────────────────────────────

    #[test]
    fn resolutions_rejects_out_of_range_leaf() {
        // Key a resolution at an ExprId that is beyond the layer's expr vec.
        // The in-range check must reject it before reachability is tested.
        let mut layer = layer_with_single_generic_lookup(0);
        let out_of_range = ExprId(layer.exprs.len() as u32); // beyond the vec
        layer.resolutions.insert(out_of_range, ResolutionStrategy::PeekSetup);
        let c = circuit_of(layer);
        let e = validate(&c).expect_err("out-of-range resolution leaf must be rejected");
        assert!(e.contains("out-of-range"), "error must mention out-of-range, got: {e}");
    }

    #[test]
    fn resolutions_rejects_set_index_mismatch() {
        // Build a layer whose single Output root is a folded GenericColumn lookup with
        // set_index = 7, but tag it PeekAggregate { set_index: 9 }.
        let layer = layer_with_single_generic_lookup(/* set_index */ 7);
        let leaf = generic_lookup_leaf_expr(&layer); // the folded-lookup ExprId
        let mut bad = layer.clone();
        bad.resolutions.insert(leaf, ResolutionStrategy::PeekAggregate { set_index: 9 });
        let c = circuit_of(bad);
        let e = validate(&c).expect_err("set_index mismatch must be rejected");
        assert!(e.contains("set 7 != 9"), "error must mention set mismatch, got: {e}");
    }

    #[test]
    fn resolutions_accepts_well_formed_generic() {
        let layer = layer_with_single_generic_lookup(7);
        let leaf = generic_lookup_leaf_expr(&layer);
        let mut good = layer.clone();
        good.resolutions.insert(leaf, ResolutionStrategy::PeekAggregate { set_index: 7 });
        let c = circuit_of(good);
        assert!(
            validate(&c).is_ok(),
            "well-formed PeekAggregate must validate: {:?}",
            validate(&c)
        );
    }

    #[test]
    fn resolutions_rejects_extra_term_in_fold() {
        // The strict shape check must reject a fold with a stray non-fold term
        // (the false-negative the loose source-scan would have accepted).
        let mut layer = layer_with_single_generic_lookup(7);
        let c_src = SourceId(layer.sources.len() as u32);
        layer.sources.push(SourceInfo { kind: SourceKind::Constant { value: 1 } });
        let c_expr = ExprId(layer.exprs.len() as u32);
        layer.exprs.push(Expr::Source(c_src));
        // Rebuild the leaf Add (ExprId 5) to include the stray Constant term.
        layer.exprs[5] = Expr::Add(vec![ExprId(1), ExprId(4), c_expr]);
        layer
            .resolutions
            .insert(ExprId(5), ResolutionStrategy::PeekAggregate { set_index: 7 });
        let c = circuit_of(layer);
        let e = validate(&c).expect_err("a fold with an extra Constant term must be rejected");
        // The stray Constant source goes through the Source arm → generic_col rejects it
        // as "expected GenericColumn, got Constant". Any shape-rejection error is fine.
        assert!(
            e.contains("expected GenericColumn") || e.contains("unexpected Add term"),
            "error must mention shape rejection, got: {e}"
        );
    }

    #[test]
    fn resolutions_rejects_unreachable_leaf() {
        // Valid single-fold layer (root = the fold at ExprId(5)), then append a
        // SECOND well-formed 2-column fold that NO root references.
        let mut layer = layer_with_single_generic_lookup(7);
        let q = ExprId(0); // reuse the existing query-const expr
        let sbase = layer.sources.len() as u32;
        layer.sources.push(SourceInfo { kind: SourceKind::LookupValue {
            kind: LookupValueKind::GenericColumn { column: 0 }, set_index: 7, query: q } });
        layer.sources.push(SourceInfo { kind: SourceKind::Challenge { reference: ChallengeRef {
            key: ChallengeKey::LookupMultiplicative, power: ChallengePower::Static(1) } } });
        layer.sources.push(SourceInfo { kind: SourceKind::LookupValue {
            kind: LookupValueKind::GenericColumn { column: 1 }, set_index: 7, query: q } });
        let ebase = layer.exprs.len() as u32;
        layer.exprs.push(Expr::Source(SourceId(sbase)));                       // lv0
        layer.exprs.push(Expr::Source(SourceId(sbase + 1)));                   // alpha^1
        layer.exprs.push(Expr::Source(SourceId(sbase + 2)));                   // lv1
        layer.exprs.push(Expr::Mul(vec![ExprId(ebase + 1), ExprId(ebase + 2)])); // alpha*lv1
        layer.exprs.push(Expr::Add(vec![ExprId(ebase), ExprId(ebase + 3)]));     // orphaned fold leaf
        let orphan = ExprId(ebase + 4);
        layer.resolutions.insert(orphan, ResolutionStrategy::PeekAggregate { set_index: 7 });
        let c = circuit_of(layer);
        let e = validate(&c).expect_err("a well-formed but root-unreachable fold leaf must be rejected");
        assert!(e.contains("not reachable"), "error must mention not reachable, got: {e}");
    }

    // ── B2: check_folded_setup_shape negative test ────────────────────────────

    /// Positive control: a well-formed 2-column setup fold at ExprId(4) must validate.
    /// Negative: replacing Setup source 0 with a BaseLayerMemory read must reject.
    #[test]
    fn resolutions_rejects_malformed_setup_fold() {
        // Positive control.
        let mut good = layer_with_single_setup_fold();
        good.resolutions.insert(ExprId(4), ResolutionStrategy::PeekSetup);
        assert!(
            validate(&circuit_of(good)).is_ok(),
            "well-formed setup fold must validate"
        );

        // Negative: replace source 0 (Setup{col:0}) with a BaseLayerMemory read.
        let mut bad = layer_with_single_setup_fold();
        bad.sources[0] = SourceInfo {
            kind: SourceKind::Read { place: ReadPlace::BaseLayerMemory { column: 0 } },
        };
        bad.resolutions.insert(ExprId(4), ResolutionStrategy::PeekSetup);
        let e = validate(&circuit_of(bad))
            .expect_err("non-Setup read in setup fold must be rejected");
        assert!(
            e.contains("folded setup") && (e.contains("expected Read(Setup)") || e.contains("Setup")),
            "error must mention setup shape, got: {e}"
        );
    }

    // ── B3: decoder-set / predicate negatives ─────────────────────────────────

    /// PeekAggregate must not use DECODER_LOOKUP_FORMAL_SET_INDEX.
    #[test]
    fn resolutions_rejects_decoder_set_as_peek_aggregate() {
        let layer = layer_with_single_generic_lookup(DECODER_LOOKUP_FORMAL_SET_INDEX);
        let leaf = generic_lookup_leaf_expr(&layer);
        let mut bad = layer.clone();
        bad.resolutions.insert(leaf, ResolutionStrategy::PeekAggregate { set_index: DECODER_LOOKUP_FORMAL_SET_INDEX });
        let e = validate(&circuit_of(bad))
            .expect_err("PeekAggregate with decoder set must be rejected");
        assert!(
            e.contains("decoder set") || e.contains("PeekAggregate must not"),
            "error must mention decoder set, got: {e}"
        );
    }

    /// PeekDecoder predicate must be a BaseLayerMemory read; a Setup predicate must be rejected.
    #[test]
    fn resolutions_rejects_non_base_layer_predicate() {
        // Use set_index=7 (non-decoder); the predicate check fires before the
        // set_index shape check, so we get the predicate error first.
        let layer = layer_with_single_generic_lookup(7);
        let leaf = generic_lookup_leaf_expr(&layer);
        let mut bad = layer.clone();
        bad.resolutions.insert(
            leaf,
            ResolutionStrategy::PeekDecoder {
                predicate: ReadPlace::Setup { column: 0 }, // non-BaseLayerMemory → invalid
                fill: FillSource::DecoderLookupFill,
            },
        );
        let e = validate(&circuit_of(bad))
            .expect_err("non-BaseLayerMemory predicate must be rejected");
        assert!(
            e.contains("base-layer read") || e.contains("predicate"),
            "error must mention predicate, got: {e}"
        );
    }

    // ── A1: TDD — column-0 scaled by alpha^0 must be rejected ────────────────
    //
    // Column-0 of a folded lookup must be an UNSCALED bare Source (alpha^0 = 1
    // is an identity, not a real scaling; emitting Mul([alpha^0, lv0]) is a
    // generator bug). The guard `(0, None) => {}` accepts only an unscaled
    // column-0 term; a Mul([alpha^0, lv0]) produces `(0, Some(0))` which the
    // tightened guard `(_, Some(p)) if i >= 1 && p as usize == i` now rejects.
    #[test]
    fn resolutions_rejects_alpha0_scaled_column0() {
        // Build a 2-column folded lookup for set_index=7 where column-0 is
        // wrapped as Mul([alpha^0, lv0]) instead of a bare Source.
        //
        // Sources:
        //  0: Constant(0)  (query)
        //  1: lv0  GenericColumn{0}, set=7
        //  2: alpha^1  Challenge{LookupMultiplicative, Static(1)}
        //  3: lv1  GenericColumn{1}, set=7
        //  4: alpha^0  Challenge{LookupMultiplicative, Static(0)}  <- NEW
        //
        // Exprs:
        //  0: Source(0)  = query
        //  1: Source(1)  = lv0
        //  2: Source(2)  = alpha^1
        //  3: Source(3)  = lv1
        //  4: Mul([2,3]) = alpha^1 * lv1
        //  5: Source(4)  = alpha^0
        //  6: Mul([5,1]) = alpha^0 * lv0  <- the invalid "scaled" column-0 Mul
        //  7: Add([6,4]) = fold leaf (alpha^0*lv0 + alpha^1*lv1)
        let query = ExprId(0);
        let lv = |column: usize| SourceInfo {
            kind: SourceKind::LookupValue {
                kind: LookupValueKind::GenericColumn { column },
                set_index: 7,
                query,
            },
        };
        let alpha1 = SourceInfo {
            kind: SourceKind::Challenge {
                reference: ChallengeRef {
                    key: ChallengeKey::LookupMultiplicative,
                    power: ChallengePower::Static(1),
                },
            },
        };
        let alpha0 = SourceInfo {
            kind: SourceKind::Challenge {
                reference: ChallengeRef {
                    key: ChallengeKey::LookupMultiplicative,
                    power: ChallengePower::Static(0), // alpha^0 — the bad scaling
                },
            },
        };
        let mut layer = DagLayer {
            sources: vec![
                SourceInfo { kind: SourceKind::Constant { value: 0 } }, // 0: query
                lv(0),   // 1: lv0
                alpha1,  // 2: alpha^1
                lv(1),   // 3: lv1
                alpha0,  // 4: alpha^0  <- NEW
            ],
            exprs: vec![
                Expr::Source(SourceId(0)),             // 0: query
                Expr::Source(SourceId(1)),             // 1: lv0
                Expr::Source(SourceId(2)),             // 2: alpha^1
                Expr::Source(SourceId(3)),             // 3: lv1
                Expr::Mul(vec![ExprId(2), ExprId(3)]), // 4: alpha^1 * lv1
                Expr::Source(SourceId(4)),             // 5: alpha^0
                Expr::Mul(vec![ExprId(5), ExprId(1)]), // 6: alpha^0 * lv0 (invalid)
                Expr::Add(vec![ExprId(6), ExprId(4)]), // 7: fold leaf
            ],
            roots: vec![out_root(
                ExprId(7),
                SinkKind::Inner { layer: 0, offset: 0 },
                FieldKind::Ext,
            )],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        };
        // Tag the fold leaf ExprId(7) as PeekAggregate{set_index:7}.
        layer.resolutions.insert(ExprId(7), ResolutionStrategy::PeekAggregate { set_index: 7 });
        let c = circuit_of(layer);
        let e = validate(&c).expect_err("alpha^0-scaled column-0 must be rejected");
        assert!(
            e.contains("wrong scaling"),
            "error should mention wrong scaling, got: {e}"
        );
    }

    // ── M-B: degenerate (materialize: None, claim: None) root must be rejected ─

    /// A `Root { materialize: None, claim: None }` is structurally representable
    /// after the Task-2 struct dissolve but is semantically meaningless (neither
    /// materializes a value nor participates in batching). Lowering never emits
    /// it, but `validate` must explicitly reject it so a hand-crafted or future
    /// mis-generated DAG is caught early.
    ///
    /// RED: before the guard is added this test fails because `validate` silently
    /// accepts the degenerate root (the batching check only fires for roots that
    /// would appear in the batching order; a `claim: None` root is ignored by
    /// that arm, and the field-inference pass skips it too).
    #[test]
    fn rejects_degenerate_none_none_root() {
        // Layer: root 0 is a degenerate (None, None) root.  We still need a
        // valid claim-bearing root (root 1) so the batching order is satisfied
        // and we isolate the specific degenerate-root rejection.
        let sources = vec![SourceInfo {
            kind: SourceKind::Constant { value: 1 },
        }];
        let exprs = vec![Expr::Source(SourceId(0))];
        let roots = vec![
            // root 0: degenerate — neither materializes nor carries a claim.
            Root { expr: ExprId(0), materialize: None, claim: None },
            // root 1: well-formed claim-bearing Output (satisfies batching).
            out_root(ExprId(0), SinkKind::Inner { layer: 0, offset: 0 }, FieldKind::Base),
        ];
        let layer = DagLayer {
            sources,
            exprs,
            roots,
            batching: BatchingOrder { roots: vec![RootId(1)] },
            resolutions: BTreeMap::new(),
        };
        let err = validate(&circuit_of(layer))
            .expect_err("a (materialize: None, claim: None) root must be rejected");
        assert!(
            err.contains("neither materialize nor claim"),
            "error should mention degenerate shape, got: {err}"
        );
    }
}
