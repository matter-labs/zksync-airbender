//! Field-homogeneous arithmetic lowering: PURE helpers (spec §5, §6).
//!
//! Post-T3b these are the field-classification + structural-predicate helpers the
//! schedule-driven lowerer (`lower.rs`) reuses: `child_operand_field` (per-child
//! operand field for instruction-field selection), `build_cross_layer_field_map`,
//! `classify_additive_child`, the `field_from_u8`/`sign_from_u8` decoders, and the
//! `is_*` predicates. The old residency-coupled emission engine (the
//! `compile_expr`/`source_to_operand`/reduction/FMA machinery that threaded a
//! per-layer residency planner) was deleted in the T3b flip; `lower.rs` owns the
//! schedule-driven emission now.

use super::super::isa::{OperandField, Sign};
use cs::gkr_compiler::dag_ir::{
    expr_field, Expr, ExprId, FieldKind, ReadPlace, SinkInfo, SinkKind, SourceKind,
};
use std::collections::HashMap;

/// BabyBear modulus P = 2^31 − 2^27 + 1 = 0x78000001.
/// Field −1 is the canonical representative of P−1 (the additive inverse of 1).
const BABYBEAR_P: u32 = 0x78000001;
const BABYBEAR_NEG_ONE: u32 = BABYBEAR_P - 1;

// ── field classification ──────────────────────────────────────────────────────

/// Map a `dag_ir::FieldKind` to the ISA operand-field bit.
pub(crate) fn to_operand_field(f: FieldKind) -> OperandField {
    match f {
        FieldKind::Base => OperandField::Base,
        FieldKind::Ext => OperandField::Ext,
    }
}

/// A cross-layer field map: each prior-layer-produced `ReadPlace` → the TRUE field
/// of its producing sink. Built once per circuit (`build_cross_layer_field_map`) and
/// threaded through compilation so a cross-layer `Read{LayerOutput|CacheOutput}` is
/// labeled with the field of the LAYER THAT PRODUCED IT, not the enclosing sink.
///
/// Without it, `child_operand_field` would fall back to the enclosing reduction's
/// `expected` field for every cross-layer read (codex Imp2): correct for a FULLY-
/// cross-layer expr (whose result field == sink field), but WRONG for a MIXED expr
/// like `base_cross_layer_read + ext_challenge`, where the Base read would be
/// mislabeled Ext (the Ext sink field). The interpreter ignores the field bit for
/// value, so this is value-neutral, but the LABEL feeds the GPU ABI and the
/// validator — so it must be the read's true producing-sink field.
///
/// Walks EVERY layer's roots, reading each root's inline `materialize` sink;
/// `Inner{layer,offset}`/`Cache{layer,offset}` sinks are the only kinds re-read
/// cross-layer (via `ReadPlace::LayerOutput`/`CacheOutput`). `Export`/`Scratch` are
/// ignored — they are not read via those `ReadPlace` variants (`read_place_field`
/// already classifies `Scratch` reads as `Base`).
pub fn build_cross_layer_field_map(
    circuit: &cs::gkr_compiler::dag_ir::DagCircuit,
) -> HashMap<ReadPlace, FieldKind> {
    let mut map = HashMap::new();
    for dag_layer in &circuit.layers {
        for root in &dag_layer.roots {
            if let Some(SinkInfo { kind, field }) = root.materialize.as_ref() {
                match *kind {
                    SinkKind::Inner { layer, offset } => {
                        map.insert(ReadPlace::LayerOutput { layer, offset }, *field);
                    }
                    SinkKind::Cache { layer, offset } => {
                        map.insert(ReadPlace::CacheOutput { layer, offset }, *field);
                    }
                    SinkKind::Export { .. } | SinkKind::Scratch { .. } => {}
                }
            }
        }
    }
    map
}

/// The operand field of a child expression for instruction-field selection.
///
/// SP1 convention: `expr_field` returns `Err(ReadPlace)` for a prior-layer
/// `Read{LayerOutput|CacheOutput}` (and any expr that has such a read as a leaf)
/// because the field lives in a *prior* layer's sinks, which `expr_field` alone
/// cannot resolve. The interpreter resolves every operand to `Ext` and IGNORES the
/// field bit for value computation, so a mislabel here does NOT affect SP1 parity —
/// but it does feed the GPU ABI and the validator's field-transition tracker, so the
/// LABEL must be the expr's TRUE field.
///
/// On `Err` we recompute the field with `expr_field_with_map`, a map-aware mirror of
/// `expr_field` that resolves each cross-layer-read LEAF via the cross-layer field
/// `map` (built from EVERY layer's sinks by `build_cross_layer_field_map`) and joins
/// up the tree. This is exactly correct for both cases the short-circuiting
/// `expr_field` cannot distinguish:
///   - a BARE cross-layer read → its producing sink's field (codex Imp2: a Base read
///     in a mixed sibling group is now labeled Base, not the enclosing Ext);
///   - a COMPOUND subexpr with a cross-layer-read leaf → the join of all leaves, so a
///     `base_cross_layer_read + ext_challenge` lowered into a cell evicts as Ext (the
///     value the local lowering actually produces), not the leaf's producing-sink
///     field — which would otherwise mislabel the evict and trip the validator.
/// If any leaf is absent from the map (defensive — should not happen for a valid
/// circuit), `expr_field_with_map` returns `None` and we fall back to `expected`.
/// Where the field IS already known (`Ok`), `expected` and `map` are ignored.
pub(crate) fn child_operand_field(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    id: ExprId,
    expected: OperandField,
    map: &HashMap<ReadPlace, FieldKind>,
) -> OperandField {
    match expr_field(&layer.exprs, &layer.sources, id) {
        Ok(f) => to_operand_field(f),
        Err(_) => match expr_field_with_map(layer, id, map) {
            // The expr's TRUE field, resolving cross-layer leaves via the map.
            Some(f) => to_operand_field(f),
            // Defensive fallback: take the enclosing result field (legacy SP1 path).
            None => expected,
        },
    }
}

/// Map-aware mirror of `dag_ir::expr_field`: recompute an expr's field, resolving each
/// cross-layer-read leaf (`Read{LayerOutput|CacheOutput}` → `expr_field` `Err`) via the
/// cross-layer field `map`. Returns `None` if any such leaf is absent from the map
/// (defensive). Only invoked on the `Err` branch, where a plain `expr_field` failed.
fn expr_field_with_map(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    id: ExprId,
    map: &HashMap<ReadPlace, FieldKind>,
) -> Option<FieldKind> {
    match &layer.exprs[id.0 as usize] {
        Expr::Source(_) => {
            // A determinable source resolves through the standard inference; an
            // `Err(place)` is a cross-layer read whose field we look up in the map.
            match expr_field(&layer.exprs, &layer.sources, id) {
                Ok(f) => Some(f),
                Err(place) => map.get(&place).copied(),
            }
        }
        Expr::Add(children) | Expr::Mul(children) => {
            // Join children's fields; any Ext leaf (e.g. a challenge) promotes the
            // whole compound to Ext, matching what the local lowering produces.
            let mut acc = FieldKind::Base;
            for &c in children {
                let f = expr_field_with_map(layer, c, map)?;
                acc = join_field(acc, f);
            }
            Some(acc)
        }
    }
}

/// Lattice join mirroring `dag_ir::join`: `Base ⊔ Base = Base`, anything with `Ext` → `Ext`.
fn join_field(a: FieldKind, b: FieldKind) -> FieldKind {
    match (a, b) {
        (FieldKind::Base, FieldKind::Base) => FieldKind::Base,
        _ => FieldKind::Ext,
    }
}


pub(crate) fn field_from_u8(v: u8) -> OperandField {
    if v == 0 {
        OperandField::Base
    } else {
        OperandField::Ext
    }
}

pub(crate) fn sign_from_u8(v: u8) -> Sign {
    if v == 0 {
        Sign::Plus
    } else {
        Sign::Minus
    }
}

// ── small structural predicates ──────────────────────────────────────────────────

/// True if `id` is a `Source` whose value is the field element `−1` (= P−1 =
/// `BABYBEAR_NEG_ONE`). These factors are stripped from Mul children before
/// field-grouped reduction; their count's parity decides the unary negate.
pub(crate) fn is_neg_one_factor(layer: &cs::gkr_compiler::dag_ir::DagLayer, id: ExprId) -> bool {
    let Expr::Source(src) = &layer.exprs[id.0 as usize] else {
        return false;
    };
    matches!(
        &layer.sources[src.0 as usize].kind,
        SourceKind::Constant { value } if *value == BABYBEAR_NEG_ONE
    )
}

/// Decompose a `Mul` into `(negated_parity, surviving_factors)`: elide `Constant{1}`
/// factors, peel `-1` factors (tracking the odd/even parity of their count), and
/// return the remaining non-`±1` factors. `None` if `id` is not a `Mul`.
fn mul_surviving_factors(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    id: ExprId,
) -> Option<(bool, Vec<ExprId>)> {
    let Expr::Mul(factors) = &layer.exprs[id.0 as usize] else {
        return None;
    };
    let mut neg_one_count = 0usize;
    let mut kept: Vec<ExprId> = Vec::with_capacity(factors.len());
    for &f in factors {
        if is_constant_one(layer, f) {
            continue;
        }
        if is_neg_one_factor(layer, f) {
            neg_one_count += 1;
        } else {
            kept.push(f);
        }
    }
    Some((neg_one_count % 2 == 1, kept))
}

/// An additive child of a sum, classified for sign-aware lowering (#7):
/// - `Product { sign, lhs, rhs }` — a (possibly negated) binary product → one FMA pair.
/// - `Addend { sign, id }` — an additive term to lower into a sign-keyed ADD group.
///   A negated single-factor `Mul([-1, x])` becomes `Addend { Minus, x }` (lower `x`,
///   NOT the wrapping Mul — folding the negate into the consuming ADD's sign bit).
pub(crate) enum AdditiveChild {
    Product { sign: Sign, lhs: ExprId, rhs: ExprId },
    Addend { sign: Sign, id: ExprId },
}

/// Classify an additive child of a sum into a product (FMA) or a sign-keyed addend.
/// Shared by `try_compile_fma`'s product/addend partition AND `compile_reduction`'s
/// add path so the negate-into-sign fold is uniform (DRY).
pub(crate) fn classify_additive_child(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    id: ExprId,
) -> AdditiveChild {
    match mul_surviving_factors(layer, id) {
        Some((negated, kept)) if kept.len() == 2 => {
            let sign = if negated { Sign::Minus } else { Sign::Plus };
            AdditiveChild::Product { sign, lhs: kept[0], rhs: kept[1] }
        }
        Some((true, kept)) if kept.len() == 1 => {
            // Negated single surviving factor `(-1)·x`: lower `x` itself and fold the
            // negate into the consuming ADD's sign bit (no standalone unary negate).
            AdditiveChild::Addend { sign: Sign::Minus, id: kept[0] }
        }
        // Plain additive term (a source, a non-negated single-factor Mul, a compound
        // subtree, or any Mul whose surviving-factor count is not 1 or 2): no fold.
        _ => AdditiveChild::Addend { sign: Sign::Plus, id },
    }
}

pub(crate) fn is_constant_one(layer: &cs::gkr_compiler::dag_ir::DagLayer, id: ExprId) -> bool {
    let Expr::Source(src) = &layer.exprs[id.0 as usize] else {
        return false;
    };
    matches!(
        &layer.sources[src.0 as usize].kind,
        SourceKind::Constant { value: 1 }
    )
}

fn is_constant_zero(layer: &cs::gkr_compiler::dag_ir::DagLayer, id: ExprId) -> bool {
    let Expr::Source(src) = &layer.exprs[id.0 as usize] else {
        return false;
    };
    matches!(
        &layer.sources[src.0 as usize].kind,
        SourceKind::Constant { value: 0 }
    )
}

/// True if `id` evaluates to the field element 0: a `Constant{0}` source, or a
/// `Mul` with any zero factor (annihilator), recursively. Such a term contributes
/// nothing to a sum and is dropped by `compile_add` — `0` has no operand encoding
/// (`Special::Zero` is not emittable, §6), so it must never reach lowering.
pub(crate) fn is_zero_expr(layer: &cs::gkr_compiler::dag_ir::DagLayer, id: ExprId) -> bool {
    match &layer.exprs[id.0 as usize] {
        Expr::Source(_) => is_constant_zero(layer, id),
        Expr::Mul(factors) => factors.iter().any(|&f| is_zero_expr(layer, f)),
        Expr::Add(_) => false,
    }
}

