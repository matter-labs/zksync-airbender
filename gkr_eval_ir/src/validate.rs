//! Structural validators for the canonical DAG IR.
//!
//! # `validate`
//! A GPU-independent structural pass over a [`DagCircuit`]. It enforces:
//! - Every claim-bearing root appears exactly once in [`BatchingOrder`];
//!   materialization-only (cache) roots must NOT appear in `BatchingOrder`. A
//!   same-layer cache value is reused by sharing its `ExprId` (DAG sharing), not
//!   by a separate source reference.
//! - Each materialized sink is written exactly once per layer.
//! - Every source field is inferable; every expr field is inferable by `join`.
//! - A materialized root's expr field equals its sink field exactly (no implicit
//!   conversion either direction).
//! - Every referenced `ExprId`/`SourceId` (including each `Root.expr`) is in
//!   range and the expression dependency graph is acyclic.
//!
//! ## Cross-layer field resolution
//! `ReadPlace::LayerOutput`/`CacheOutput` carry no field tag (the model only
//! tags *sinks*). `validate` walks layers in declaration order and accumulates a
//! map from each layer's sink "place" (`Inner{layer,offset}` →
//! `LayerOutput{layer,offset}`, `Cache{layer,offset}` → `CacheOutput{layer,offset}`)
//! to the sink's [`FieldKind`]. A later layer's `Read` of that output resolves
//! its field from this map.

use std::collections::{HashMap, HashSet};

use cs::definitions::gkr::DECODER_LOOKUP_FORMAL_SET_INDEX;

use super::field_infer::expr_field_with_resolver;
use super::{
    ChallengeKey, ChallengePower, DagCircuit, DagLayer, Expr, ExprId, FieldKind, LookupValueKind,
    RangeWidth, ReadPlace, ResolutionStrategy, RootId, SinkKind, SourceId, SourceKind,
};

// ── Expression-graph acyclicity ──────────────────────────────────────────────

/// State color for Add/Mul child and lookup-query edges.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Color {
    White,
    Gray,
    Black,
}

fn successors(expr: u32, layer: &DagLayer) -> Vec<u32> {
    match &layer.exprs[expr as usize] {
        Expr::Source(src_id) => match &layer.sources[src_id.0 as usize] {
            SourceKind::LookupValue { query, .. } => vec![query.0],
            _ => vec![],
        },
        Expr::Add(args) | Expr::Mul(args) => args.iter().map(|a| a.0).collect(),
    }
}

fn check_acyclic(layer: &DagLayer, li: usize) -> Result<(), String> {
    let mut color = vec![Color::White; layer.exprs.len()];
    for start in 0..layer.exprs.len() as u32 {
        if color[start as usize] != Color::White {
            continue;
        }
        let mut stack = vec![(start, successors(start, layer), 0)];
        color[start as usize] = Color::Gray;
        while let Some((expr, succ, idx)) = stack.last_mut() {
            if *idx < succ.len() {
                let next = succ[*idx];
                *idx += 1;
                match color[next as usize] {
                    Color::White => {
                        color[next as usize] = Color::Gray;
                        stack.push((next, successors(next, layer), 0));
                    }
                    Color::Gray => {
                        return Err(format!(
                            "layer {li}: dependency cycle detected (back edge into a node on the active path)"
                        ));
                    }
                    Color::Black => {}
                }
            } else {
                color[*expr as usize] = Color::Black;
                stack.pop();
            }
        }
    }
    Ok(())
}

// ── Resolution-table helpers ──────────────────────────────────────────────────

fn collect_root_reachable_exprs(layer: &DagLayer) -> Vec<bool> {
    let mut visited = vec![false; layer.exprs.len()];
    let mut stack: Vec<u32> = layer.roots.iter().map(|root| root.expr.0).collect();
    while let Some(expr) = stack.pop() {
        if visited[expr as usize] {
            continue;
        }
        visited[expr as usize] = true;
        for next in successors(expr, layer) {
            if !visited[next as usize] {
                stack.push(next);
            }
        }
    }
    visited
}

/// Validate the forward resolution table.
fn check_resolutions(layer: &DagLayer, li: usize) -> Result<(), String> {
    if layer.resolutions.is_empty() {
        return Ok(());
    }
    let reachable = collect_root_reachable_exprs(layer);
    for (&leaf, strategy) in &layer.resolutions {
        if leaf.0 as usize >= layer.exprs.len() {
            return Err(format!(
                "layer {li}: resolution keys out-of-range expr {:?}",
                leaf
            ));
        }
        if !reachable[leaf.0 as usize] {
            return Err(format!(
                "layer {li}: resolution leaf {:?} ({:?}) is not reachable from any root",
                leaf, strategy
            ));
        }
        match strategy {
            ResolutionStrategy::PeekSingleColumn { set_index, width } => {
                let Some(SourceKind::LookupValue {
                    kind,
                    set_index: si,
                    ..
                }) = source_of(leaf, layer)
                else {
                    return Err(format!(
                        "layer {li}: PeekSingleColumn leaf {:?} is not a LookupValue source",
                        leaf
                    ));
                };
                if *si != *set_index {
                    return Err(format!(
                        "layer {li}: PeekSingleColumn leaf {:?} set {si} != strategy set {set_index}",
                        leaf
                    ));
                }
                let ok = matches!(
                    (kind, width),
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
            ResolutionStrategy::PeekDecoder { predicate } => {
                // The IR has no machine state, so equality with execute is checked while lowering.
                if !matches!(predicate, ReadPlace::BaseLayerMemory { .. }) {
                    return Err(format!(
                        "layer {li}: PeekDecoder predicate must be a base-layer read on {:?}",
                        leaf
                    ));
                }
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
/// More than one column ⇒ `Add` of one UNSCALED column-0 lookup plus, per j≥1, a 2-factor
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
        match &layer.sources[src_id.0 as usize] {
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
                            match &layer.sources[s.0 as usize] {
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
        match &layer.sources[src_id.0 as usize] {
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
                            match &layer.sources[s.0 as usize] {
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

fn source_of(leaf: ExprId, layer: &DagLayer) -> Option<&SourceKind> {
    if let Expr::Source(src_id) = &layer.exprs[leaf.0 as usize] {
        Some(&layer.sources[src_id.0 as usize])
    } else {
        None
    }
}

// ── Top-level structural validator ────────────────────────────────────────────

/// Structurally validate a [`DagCircuit`].
///
/// Returns `Err(String)` describing the first violation found, `Ok(())` if the
/// circuit is well-formed.
pub(crate) fn validate(dag: &DagCircuit) -> Result<(), String> {
    // Accumulated cross-layer sink fields, keyed by the `ReadPlace` a later layer
    // would use to read the producing sink.
    let mut cross_layer: HashMap<ReadPlace, FieldKind> = HashMap::new();

    for (li, layer) in dag.layers.iter().enumerate() {
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
                    if let SourceKind::LookupValue { query, .. } = &layer.sources[src_id.0 as usize]
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
        // Every root expression must also be in range.
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
            // incorrectly generated DAGs are caught before any downstream pass.
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
        // Roots without materialization write no sink.
        let mut sink_seen: HashSet<SinkKind> = HashSet::new();
        for (ri, root) in layer.roots.iter().enumerate() {
            if let Some(sink) = &root.materialize {
                if !sink_seen.insert(sink.kind) {
                    return Err(format!(
                        "layer {li} root {ri}: sink {:?} written by more than one root",
                        sink.kind
                    ));
                }
            }
        }

        // ── Field inference ──────────────────────────────────────────────────
        for (ri, root) in layer.roots.iter().enumerate() {
            let expr_f =
                expr_field_with_resolver(&layer.exprs, &layer.sources, root.expr, &|place| {
                    cross_layer.get(place).copied()
                })
                .map_err(|place| {
                    format!("layer {li} root {ri}: unresolved cross-layer read field for {place:?}")
                })?;
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
        // (`claim: None`) MUST be visited: `read_place` returns `Some` for
        // `Cache`, so a later layer's `Read{CacheOutput}` can resolve its field.
        for root in &layer.roots {
            if let Some(sink) = &root.materialize {
                if let Some(place) = sink.kind.read_place() {
                    cross_layer.insert(place, sink.field);
                }
            }
        }
    }

    Ok(())
}
