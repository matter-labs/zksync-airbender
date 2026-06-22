//! Field-homogeneous arithmetic lowering (spec §5, §6).
//!
//! `compile_expr` lowers one `dag_ir` expression into the accumulator as a stream
//! of `Instr`s, grouping additive/multiplicative reductions by operand field so a
//! single ADD/MUL never mixes Base and Ext operands (§5 "field is encoded per
//! instruction"). Product-sums lower to FMA (§6, H6); the lookup α-fold collapses
//! to `MOV col0; FMA{Base,Ext}[(col1,α1),…]` (§6 worked example, H5/H6).
//!
//! `source_to_operand` resolves a single `Expr::Source` (or a resolution-pruned
//! subtree) to one `OperandLine` (§8, §9).

use super::super::context::{CompileTrace, DagForwardContext};
use super::super::error::CompileError;
use super::super::isa::{
    DstLine, Instr, LdcSub, MovDir, OperandField, OperandLine, Sign, Special, MAX_ARITY,
};
use super::schedule::{split_reduction, CellAllocator};
use super::resolution::{resolve_or_descend, ResolveOutcome};
use cs::gkr_compiler::dag_ir::{
    expr_field, Expr, ExprId, FieldKind, ReadPlace, SinkKind, SourceKind,
};
use std::collections::HashMap;

/// BabyBear modulus P = 2^31 − 2^27 + 1 = 0x78000001.
/// Field −1 is the canonical representative of P−1 (the additive inverse of 1).
const BABYBEAR_P: u32 = 0x78000001;
const BABYBEAR_NEG_ONE: u32 = BABYBEAR_P - 1;

// ── field classification ──────────────────────────────────────────────────────

/// Map a `dag_ir::FieldKind` to the ISA operand-field bit.
fn to_operand_field(f: FieldKind) -> OperandField {
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
/// Walks EVERY layer's `sinks`; `Inner{layer,offset}`/`Cache{layer,offset}` sinks are
/// the only kinds re-read cross-layer (via `ReadPlace::LayerOutput`/`CacheOutput`).
/// `Export`/`Scratch` are ignored — they are not read via those `ReadPlace` variants
/// (`read_place_field` already classifies `Scratch` reads as `Base`).
pub fn build_cross_layer_field_map(
    circuit: &cs::gkr_compiler::dag_ir::DagCircuit,
) -> HashMap<ReadPlace, FieldKind> {
    let mut map = HashMap::new();
    for dag_layer in &circuit.layers {
        for sink in &dag_layer.sinks {
            match sink.kind {
                SinkKind::Inner { layer, offset } => {
                    map.insert(ReadPlace::LayerOutput { layer, offset }, sink.field);
                }
                SinkKind::Cache { layer, offset } => {
                    map.insert(ReadPlace::CacheOutput { layer, offset }, sink.field);
                }
                SinkKind::Export { .. } | SinkKind::Scratch { .. } => {}
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
fn child_operand_field(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    id: ExprId,
    expected: OperandField,
    map: &HashMap<ReadPlace, FieldKind>,
) -> OperandField {
    match expr_field(&layer.exprs, &layer.sources, id, &layer.roots, &layer.sinks) {
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
            match expr_field(&layer.exprs, &layer.sources, id, &layer.roots, &layer.sinks) {
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

// ── source_to_operand ─────────────────────────────────────────────────────────

/// Resolve one expression to a single `OperandLine` (§8, §9).
///
/// FIRST consult `resolve_or_descend`: a resolution-carrying expr collapses to one
/// `Special` and is NOT descended into (§9). Otherwise the expr must be a
/// `Expr::Source` and lowers per its `SourceKind`.
pub fn source_to_operand(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    expr_id: ExprId,
    ctx: &mut DagForwardContext,
    trace: &mut CompileTrace,
) -> Result<OperandLine, CompileError> {
    // §9: a resolved fold expr prunes to one Special; do not descend.
    match resolve_or_descend(layer, expr_id, &mut ctx.specials) {
        ResolveOutcome::Special(desc) => {
            trace.pruned_resolution_exprs.push(expr_id);
            return Ok(OperandLine::Special { desc });
        }
        ResolveOutcome::Descend => {}
    }

    let Expr::Source(src_id) = &layer.exprs[expr_id.0 as usize] else {
        // Not a source and not resolution-pruned: a composite operand must have
        // been lowered by `compile_expr` (acc / cell), never via `source_to_operand`.
        return Err(CompileError::FieldMismatch(format!(
            "source_to_operand on non-source expr {}",
            expr_id.0
        )));
    };

    match &layer.sources[src_id.0 as usize].kind {
        SourceKind::Read { place } => {
            let (slot, col) = ctx.backings.read_slot_col(place)?;
            Ok(OperandLine::Global { slot, col })
        }
        SourceKind::VirtualSetup { kind } => {
            let (slot, col) = ctx.backings.virtual_setup_slot(kind)?;
            Ok(OperandLine::Global { slot, col })
        }
        SourceKind::Constant { value } => {
            // Strength-reduction: the special field elements `1` and `−1` (= P−1)
            // get their dedicated `Special` literals rather than a `ConstBank` slot,
            // so they never occupy GPU `__constant__` storage and can't slip through
            // as ordinary constants. Mul-by-`1` and additive-`0` are already elided
            // upstream (`compile_mul` / `compile_add`), so a surviving `1` here is a
            // genuine additive term and `0` must never reach this arm — the
            // `ConstBank::intern` guard fails loud if it does.
            match *value {
                1 => Ok(OperandLine::Ldc { sub: LdcSub::Special, idx: Special::One as u16 }),
                v if v == BABYBEAR_NEG_ONE => {
                    Ok(OperandLine::Ldc { sub: LdcSub::Special, idx: Special::NegOne as u16 })
                }
                v => {
                    let idx = ctx.consts.intern(v);
                    Ok(OperandLine::Ldc { sub: LdcSub::Const, idx })
                }
            }
        }
        SourceKind::Challenge { reference } => {
            let (sub, idx) = ctx.challenges.intern(reference);
            Ok(OperandLine::Ldc { sub, idx })
        }
        SourceKind::Prior { id } => {
            // Caches lead: the driver populated `cache_loc[id]` before this read
            // (§5/§8). Re-read the cache backing.
            let (slot, col) = *ctx
                .cache_loc
                .get(id)
                .ok_or_else(|| CompileError::FieldMismatch(format!(
                    "Prior read of unmaterialized cache root {}",
                    id.0
                )))?;
            Ok(OperandLine::Global { slot, col })
        }
        SourceKind::LookupValue { .. } => {
            // Reached an uncovered LookupValue leaf by emitted-code traversal (§9,
            // §12): not pruned under a resolution-carrying parent → compile error.
            trace.reached_lookup_leaves.push(expr_id);
            Err(CompileError::UncoveredLookupLeaf(expr_id.0))
        }
    }
}

// ── compile_expr ───────────────────────────────────────────────────────────────

/// Lower one expression into the accumulator, appending instructions to `out`
/// (§5 init + §6 grouping + H6 FMA recognition).
///
/// - `Source` → `MOV AccFromSrc <operand>`.
/// - `Add`/`Mul` → init `MOV AccFromSrc child0`, then one ADD/MUL per operand-field
///   group over the remaining children (never mixing fields in one op). An `Add`
///   whose children are ALL products lowers to an FMA stream instead. Empty Add/Mul
///   emit nothing (NOP `+0` / `×1`); unary → just the init MOV. `Constant{1}`
///   factors are elided from a MUL.
///
/// `alloc` (Task 13) is a real per-layer `CellAllocator` sized by the budget: it
/// backs the GENERAL nested-subexpression fallback (`lower_operand`), where a
/// reduction child / FMA factor that is itself a compound `Add`/`Mul` (e.g. a
/// product-of-sums or a degree-≥3 addend) is recursively lowered into a fresh
/// smem cell and referenced as an `Smem` operand (§11). The proven Tasks 9–11
/// patterns (source children, FMA, α-fold, field-homogeneous groups, negate,
/// over-cap split) remain the primary path; the cell fallback only fires for
/// children that are neither a source nor resolution-pruned.
pub fn compile_expr(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    expr_id: ExprId,
    ctx: &mut DagForwardContext,
    trace: &mut CompileTrace,
    out: &mut Vec<Instr>,
    alloc: &mut CellAllocator,
    expected: OperandField,
) -> Result<(), CompileError> {
    // §9: a resolution-carrying expr collapses to a single Special operand, even at
    // the top of a root expr → init the acc from it and stop. The Special's field is
    // the resolved fold's field (PeekAggregate/PeekDecoder/PeekSetup are Ext,
    // PeekSingleColumn is Base): label the init MOV accordingly so the field-
    // transition tracker agrees with an Ext-typed materialize (§9/§12).
    if let ResolveOutcome::Special(desc) =
        resolve_or_descend(layer, expr_id, &mut ctx.specials)
    {
        trace.pruned_resolution_exprs.push(expr_id);
        let field = child_operand_field(layer, expr_id, expected, &ctx.cross_layer_fields);
        emit_init_field(out, OperandLine::Special { desc }, field);
        return Ok(());
    }

    match &layer.exprs[expr_id.0 as usize] {
        Expr::Source(_) => {
            let field = child_operand_field(layer, expr_id, expected, &ctx.cross_layer_fields);
            let op = source_to_operand(layer, expr_id, ctx, trace)?;
            emit_init_field(out, op, field);
            Ok(())
        }
        Expr::Add(children) => compile_add(layer, children.clone(), ctx, trace, out, alloc, expected),
        Expr::Mul(children) => compile_mul(layer, children.clone(), ctx, trace, out, alloc, expected),
    }
}

/// Resolve `expr_id` to one `OperandLine`, lowering a compound subexpression into a
/// fresh smem cell when it is neither a source nor resolution-pruned (§9, §11).
///
/// Returns `(operand, owned_cell)`: when `owned_cell` is `Some(cell)`, the caller
/// MUST `alloc.free(cell)` once the operand has been consumed (after the fold that
/// reads it). The general mechanism (Task 13):
///
///   - try `source_to_operand` (a source or a resolution-carrying fold) — no acc
///     disturbance, no cell;
///   - otherwise `compile_expr` the compound subtree into the acc, then evict the
///     acc into a freshly-allocated cell (`MOV DstFromAcc Smem{cell}`) and return
///     that cell as the operand.
///
/// Because lowering a compound child clobbers the accumulator, callers materialize
/// EVERY operand via `lower_operand` BEFORE initing the acc for the enclosing
/// reduction (see `compile_reduction`).
fn lower_operand(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    expr_id: ExprId,
    ctx: &mut DagForwardContext,
    trace: &mut CompileTrace,
    out: &mut Vec<Instr>,
    alloc: &mut CellAllocator,
    expected: OperandField,
) -> Result<(OperandLine, Option<u16>), CompileError> {
    // A source or a resolution-pruned fold lowers directly to one operand line.
    // `resolve_or_descend` (inside `source_to_operand`) prunes a resolved parent to
    // a Special without descending, so we never spuriously cell-lower a fold.
    //
    // Use the non-mutating `contains_key` probe here rather than calling
    // `resolve_or_descend` again: that call would push a SpecialDescriptor as a side
    // effect, and `source_to_operand` (below) calls `resolve_or_descend` once more —
    // doubling the descriptor for every resolution-pruned expr and halving descriptor
    // headroom. `contains_key` is the exact condition `resolve_or_descend` tests via
    // `.get()`, so it is semantically equivalent and side-effect-free.
    if layer.resolutions.contains_key(&expr_id)
        || matches!(&layer.exprs[expr_id.0 as usize], Expr::Source(_))
    {
        let op = source_to_operand(layer, expr_id, ctx, trace)?;
        return Ok((op, None));
    }

    // Compound child: recursively lower into the acc, then evict to a fresh cell.
    // The child's evict width follows its own field (cross-layer read → its producing
    // sink's field via the map; absent → `expected`).
    let field = child_operand_field(layer, expr_id, expected, &ctx.cross_layer_fields);
    compile_expr(layer, expr_id, ctx, trace, out, alloc, field)?;
    let cell = alloc.alloc(field)?;
    evict_acc_to_cell(out, field, cell);
    trace.max_live_cells = trace.max_live_cells.max(alloc.max_live());
    trace.nested_subexprs += 1;
    Ok((OperandLine::Smem { cell }, Some(cell)))
}

/// `MOV AccFromSrc <op>` — accumulator init (§5), labeling the acc field `Base`.
/// Used where the init term is intentionally Base and a later mixed op promotes the
/// acc to Ext (the α-fold / FMA `col0` idiom). The interpreter ignores the MOV field
/// for value; the label only feeds the validator's field-transition tracker.
fn emit_init(out: &mut Vec<Instr>, op: OperandLine) {
    emit_init_field(out, op, OperandField::Base);
}

/// `MOV AccFromSrc <op>` labeling the acc field explicitly (§5/§12). When a
/// reduction's first term is genuinely Ext (e.g. an Ext challenge or a prior Ext
/// cache read), the acc must start Ext so the validator's field-transition tracker
/// agrees with an Ext-typed materialize at the end (`check_field_transitions`).
fn emit_init_field(out: &mut Vec<Instr>, op: OperandLine, field: OperandField) {
    out.push(Instr::Mov {
        dir: MovDir::AccFromSrc,
        field,
        dst: None,
        src: Some(op),
    });
}

// ── Add lowering ───────────────────────────────────────────────────────────────

fn compile_add(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    children: Vec<ExprId>,
    ctx: &mut DagForwardContext,
    trace: &mut CompileTrace,
    out: &mut Vec<Instr>,
    alloc: &mut CellAllocator,
    expected: OperandField,
) -> Result<(), CompileError> {
    // §6 strength: drop additive zero terms (additive identity), mirroring
    // compile_mul's `Constant{1}` elision. This is `is_zero_expr`, so it also drops
    // a zero-VALUED product (`Mul` with a `0` factor — an annihilator), which would
    // otherwise lower its `Constant{0}` factor into the const bank as a silent `#0`.
    // Removes the no-op `ADD #0` lanes the dag carries (the permutation-additive
    // seed of every memory fold). A sum of only zeros collapses to empty here and
    // emits nothing — the post-elision `DegenerateRoot` guard in `compile_layer`
    // then catches a bare-0 root.
    let children: Vec<ExprId> =
        children.into_iter().filter(|&c| !is_zero_expr(layer, c)).collect();

    // §5: empty Add is a NOP (+0) — emit nothing.
    if children.is_empty() {
        return Ok(());
    }

    // H6: an Add fuses its product children ("mads") into FMA pairs; the plain
    // additive children seed the accumulator (init/ADD). By commutativity the two
    // groups split freely. `try_compile_fma` returns None — falling through to the
    // generic reduction — only when the Add has no product child (a pure additive
    // sum). Subsumes the α-fold case (a single leading bare column is one addend).
    if let Some(()) = try_compile_fma(layer, &children, ctx, trace, out, alloc, expected)? {
        return Ok(());
    }

    // Generic additive reduction grouped by operand field (pure additive sum).
    compile_reduction(layer, &children, ctx, trace, out, /* is_add */ true, /* negate */ false, alloc, expected)
}

// ── Mul lowering ───────────────────────────────────────────────────────────────

fn compile_mul(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    children: Vec<ExprId>,
    ctx: &mut DagForwardContext,
    trace: &mut CompileTrace,
    out: &mut Vec<Instr>,
    alloc: &mut CellAllocator,
    expected: OperandField,
) -> Result<(), CompileError> {
    // §6 strength: drop `Constant{1}` factors.
    let factors: Vec<ExprId> = children
        .into_iter()
        .filter(|&c| !is_constant_one(layer, c))
        .collect();

    // §5: empty Mul (incl. all-`1` factors elided) is a NOP (×1) — emit nothing.
    if factors.is_empty() {
        return Ok(());
    }

    // Task 10 — negate canonicalization (spec §6):
    // Strip any `−1` factors at the ExprId level; the parity of their count decides
    // whether a unary negate follows the multiply. We detect `−1` directly on the
    // source kind so that the surviving factor list retains its ExprId identity,
    // which lets `compile_reduction` re-resolve each factor and correctly assign
    // its operand field (Base vs Ext), restoring the field-homogeneous MUL grouping
    // that Task 9 established (§5).
    let mut neg_one_count = 0usize;
    let mut surviving: Vec<ExprId> = Vec::with_capacity(factors.len());
    for &f in &factors {
        if is_neg_one_factor(layer, f) {
            neg_one_count += 1;
        } else {
            surviving.push(f);
        }
    }
    let negate = neg_one_count % 2 == 1;

    if surviving.is_empty() {
        // All factors were −1: the product is a constant ±1. The spec's strength
        // model guarantees this never appears in a real dag_ir reduction. Reject
        // fail-loud instead of emitting a bare `emit_unary_negate` with no preceding
        // init MOV (which would materialize 0, not −1, silently miscompiling) or
        // silently emitting nothing (even count → identity would skip the root guard).
        return Err(CompileError::DegenerateConstProduct);
    }

    // Route surviving (non-`−1`) factors through Task 9's field-homogeneous
    // reduction: `compile_reduction` resolves each ExprId, classifies it as Base
    // or Ext via `child_operand_field`, and emits separate `Instr::Mul{field:Base}`
    // and `Instr::Mul{field:Ext}` groups (§5). This is the proven Task 9 path.
    // Pass `negate` so compile_reduction can insert the unary negate in the base
    // phase (before the first ext-promoting MUL) when a base phase exists (Task 5).
    compile_reduction(layer, &surviving, ctx, trace, out, /* is_add */ false, negate, alloc, expected)?;

    Ok(())
}

/// Emit a unary negate: `MUL` with sole operand `Special(NegOne)` (spec §6).
/// The Task 7 interpreter executes this as a field negation, not a multiply.
fn emit_unary_negate(out: &mut Vec<Instr>) {
    out.push(Instr::Mul {
        field: OperandField::Base,
        operands: vec![OperandLine::Ldc {
            sub: LdcSub::Special,
            idx: Special::NegOne as u16,
        }],
    });
}

// ── shared reduction grouping ───────────────────────────────────────────────────

/// Init `MOV AccFromSrc child0`, then ONE ADD (or MUL) per operand-field group over
/// the remaining children. Field-homogeneous: a Base group and an Ext group, each a
/// separate instruction — never one op mixing fields (§5).
///
/// `negate` is meaningful ONLY for the MUL path (`is_add == false`); the ADD path
/// always passes `false`. When `negate` is true (Task 5):
/// - If the seed is Base (a base phase exists): emit the unary negate AFTER the
///   base-field groups and BEFORE the ext-field groups — the acc is still 1-wide
///   when the negate fires, so no unnecessary promotion happens.
/// - If the seed is Ext (no base phase — all factors are Ext): emit the negate
///   AFTER all groups (trailing) — the unavoidable case.
/// - `ops.len() == 1` (seed only): emit the negate AFTER the init MOV.
fn compile_reduction(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    children: &[ExprId],
    ctx: &mut DagForwardContext,
    trace: &mut CompileTrace,
    out: &mut Vec<Instr>,
    is_add: bool,
    negate: bool,
    alloc: &mut CellAllocator,
    expected: OperandField,
) -> Result<(), CompileError> {
    debug_assert!(!children.is_empty());

    // Classify each child for sign-aware lowering (#7). In the ADD path a negated
    // single-factor addend `(-1)·x` lowers `x` itself under a `Sign::Minus` ADD bit
    // (no standalone unary negate); every other child is `Sign::Plus`. The MUL path
    // (`is_add == false`) has no sign — `compile_mul` already peeled `-1`s at the
    // ExprId level — so classification is skipped and each child lowers as-is (Plus).
    //
    // Pre-materialize EVERY child to an `OperandLine` BEFORE touching the acc: a
    // compound child is lowered into a fresh smem cell (general §11 fallback), and
    // that lowering clobbers the acc — so all operands must be resolved up front.
    // A source/resolution-pruned child resolves directly (no cell). Cells are freed
    // after the reduction's last fold reads them.
    let mut ops: Vec<(OperandField, OperandLine, Sign)> = Vec::with_capacity(children.len());
    let mut owned_cells: Vec<u16> = Vec::new();
    for &c in children {
        let (to_lower, sign) = if is_add {
            match classify_additive_child(layer, c) {
                // Products never reach here: `try_compile_fma` intercepts any sum
                // with a binary product before the generic reduction is invoked.
                AdditiveChild::Product { .. } => (c, Sign::Plus),
                AdditiveChild::Addend { sign, id } => (id, sign),
            }
        } else {
            (c, Sign::Plus)
        };
        let field = child_operand_field(layer, to_lower, expected, &ctx.cross_layer_fields);
        let (op, cell) = lower_operand(layer, to_lower, ctx, trace, out, alloc, expected)?;
        if let Some(cell) = cell {
            owned_cells.push(cell);
        }
        ops.push((field, op, sign));
    }

    // Base-as-long-as-possible (§5): seed the acc from a BASE operand when the
    // reduction has one, so every base fold runs while the acc is still
    // base-width and only the Ext group promotes it once. Seeding from an Ext
    // operand (e.g. an Ext challenge) when base children exist would force the
    // base folds into an Ext-width acc — a mixed op where a base op would do.
    // +/× are commutative, so the seed term may be any child. Label the init
    // MOV with the seed's actual field so the validator's field-transition
    // tracker agrees with the materialize at the end (§5/§12).
    //
    // The seed MUST be an un-negated (Plus) term: there is no `MOV AccFromSrc` that
    // negates, so the Minus-fold applies to NON-SEED additive terms only. Prefer a
    // Plus Base term, then a Plus Ext term; only if EVERY term is negated (does not
    // occur in the gated circuits) fall back to the current seed (preserving #5b's
    // Base-first ordering among candidates).
    let init_idx = ops
        .iter()
        .position(|(f, _, s)| *f == OperandField::Base && *s == Sign::Plus)
        .or_else(|| ops.iter().position(|(_, _, s)| *s == Sign::Plus))
        .or_else(|| ops.iter().position(|(f, _, _)| *f == OperandField::Base))
        .unwrap_or(0);
    emit_init_field(out, ops[init_idx].1, ops[init_idx].0);
    // If the chosen seed is negated — only when NO Plus term existed (every term in
    // this signed additive group is negated) — compensate now: `MOV AccFromSrc` cannot
    // negate, so negate the freshly-seeded acc before folding the remaining groups (#7).
    // (The MUL path never reaches this: compile_mul peels `-1`s, so its ops are all Plus.)
    if ops[init_idx].2 == Sign::Minus {
        emit_unary_negate(out);
    }

    if ops.len() == 1 {
        // Seed-only (unary): just the init MOV, then the negate if requested.
        // For the MUL path a negate here runs on a base-width acc (the seed is
        // necessarily Base when it's the only factor, since compile_mul seeded
        // base-first; if it's Ext, the negate is still correct — unavoidable).
        if negate {
            emit_unary_negate(out);
        }
        free_all(alloc, &owned_cells);
        return Ok(());
    }

    // Partition the remaining children (all but the seed) into `(field, sign)` groups.
    let mut base_plus: Vec<OperandLine> = Vec::new();
    let mut base_minus: Vec<OperandLine> = Vec::new();
    let mut ext_plus: Vec<OperandLine> = Vec::new();
    let mut ext_minus: Vec<OperandLine> = Vec::new();
    for (i, &(field, op, sign)) in ops.iter().enumerate() {
        if i == init_idx {
            continue;
        }
        match (field, sign) {
            (OperandField::Base, Sign::Plus) => base_plus.push(op),
            (OperandField::Base, Sign::Minus) => base_minus.push(op),
            (OperandField::Ext, Sign::Plus) => ext_plus.push(op),
            (OperandField::Ext, Sign::Minus) => ext_minus.push(op),
        }
    }

    // Emit the Base groups first (base-as-long-as-possible, §5), then the Ext groups.
    // Each group is a single ADD/MUL when it fits the arity cap (the proven Tasks
    // 9/10 path); an over-long group is split into ≤MAX_ARITY chunks combined via
    // the evict-to-cell primitive (§11) so `encode` never sees an over-cap arity.
    //
    // Task 5 (negate, MUL path only): when `negate` is true and the seed is Base
    // (a base phase exists), insert the unary negate AFTER the base-field groups
    // and BEFORE the ext-field groups — the acc is still 1-wide here so the negate
    // is cheaper and avoids widening the acc before necessary.
    // When the seed is Ext (no base phase), the negate trails after all groups.
    let seed_is_base = ops[init_idx].0 == OperandField::Base;

    // Base-phase groups.
    for (field, sign, group) in [
        (OperandField::Base, Sign::Plus, base_plus),
        (OperandField::Base, Sign::Minus, base_minus),
    ] {
        if group.is_empty() {
            continue;
        }
        emit_reduction_group(out, trace, field, group, is_add, sign, alloc)?;
    }

    // Insert negate between base and ext phases when a base phase exists.
    if negate && seed_is_base {
        emit_unary_negate(out);
    }

    // Ext-phase groups.
    for (field, sign, group) in [
        (OperandField::Ext, Sign::Plus, ext_plus),
        (OperandField::Ext, Sign::Minus, ext_minus),
    ] {
        if group.is_empty() {
            continue;
        }
        emit_reduction_group(out, trace, field, group, is_add, sign, alloc)?;
    }

    // Trailing negate when no base phase existed (all-Ext seed — unavoidable).
    if negate && !seed_is_base {
        emit_unary_negate(out);
    }

    free_all(alloc, &owned_cells);
    Ok(())
}

/// Free every cell that backed a lowered compound operand, in reverse alloc order.
fn free_all(alloc: &mut CellAllocator, cells: &[u16]) {
    for &c in cells.iter().rev() {
        alloc.free(c);
    }
}

/// Emit ONE field-homogeneous reduction group, folding `ops` into the running
/// accumulator. When `ops.len() <= MAX_ARITY` this is a single ADD/MUL — byte-for-
/// byte the Tasks 9/10 emission. When it exceeds the cap, the group is split into
/// `split_reduction` chunks and combined with the evict-to-cell primitive (§11):
///
///   chunk0:           fold into acc            (acc already holds the running value)
///   each later chunk: evict acc → fresh cell
///                     re-init acc from chunk[0], fold chunk[1..]
///                     fold the evict cell back in (ADD/MUL Smem{cell})
///                     free the cell
///
/// `is_add` selects ADD (sign +) vs MUL. The accumulator's running value is
/// preserved across the split because chunk0 folds into it and every later chunk's
/// partial is combined back through the evict cell.
fn emit_reduction_group(
    out: &mut Vec<Instr>,
    trace: &mut CompileTrace,
    field: OperandField,
    ops: Vec<OperandLine>,
    is_add: bool,
    sign: Sign,
    alloc: &mut CellAllocator,
) -> Result<(), CompileError> {
    if ops.len() <= MAX_ARITY {
        // Unsplit fast path — identical to the prior Tasks 9/10 emission.
        push_fold(out, field, ops, is_add, sign);
        return Ok(());
    }

    // Fail-loud: a `Sign::Minus` ADD group over the arity cap does not occur in the
    // gated circuits, and the evict-to-cell split below is NOT sign-trivial (the
    // running partial would need re-signing). Reject rather than miscompile (#7).
    if is_add && sign == Sign::Minus {
        return Err(CompileError::FieldMismatch(
            "over-MAX_ARITY Sign::Minus ADD group is unsupported (evict-split is not sign-trivial)"
                .into(),
        ));
    }

    // Over-cap: split into chunks bounded by the arity cap. The evict cell holds the
    // running partial between chunks; its width follows the group field (Ext → 4).
    // The evict cell is drawn from the SHARED allocator so it never collides with a
    // cell still holding a lowered compound operand of this very reduction (§11).
    let sizes = split_reduction(ops.len(), /* budget */ 4);
    let mut idx = 0usize;
    let mut chunks = sizes.into_iter();

    // The split path is `Sign::Plus`-only (the Minus case is rejected fail-loud
    // above), so every fold below is byte-for-byte the prior Plus emission.
    // chunk0 folds into the acc, which already holds the reduction's running value.
    let first = chunks.next().expect("split_reduction yields >=1 chunk for arity>0");
    push_fold(out, field, ops[idx..idx + first].to_vec(), is_add, Sign::Plus);
    idx += first;

    for size in chunks {
        // Evict the running acc to a fresh cell, then recompute the next chunk in
        // the acc and fold the evicted partial back in.
        let cell = alloc.alloc(field)?;
        evict_acc_to_cell(out, field, cell);

        let chunk = &ops[idx..idx + size];
        idx += size;
        // Re-init the acc from the chunk's first operand, fold the chunk's rest.
        emit_init(out, chunk[0]);
        if chunk.len() > 1 {
            push_fold(out, field, chunk[1..].to_vec(), is_add, Sign::Plus);
        }
        // Fold the evicted partial back in (ADD/MUL referencing the cell).
        push_fold(out, field, vec![OperandLine::Smem { cell }], is_add, Sign::Plus);
        alloc.free(cell);
    }

    trace.max_live_cells = trace.max_live_cells.max(alloc.max_live());
    Ok(())
}

/// Emit a single field-homogeneous fold of `ops` into the acc: ADD (carrying `sign`)
/// when `is_add`, else MUL. `sign` is ignored for MUL (a Mul has no sign — negation
/// is handled separately). Caller guarantees `ops.len() <= MAX_ARITY` and non-empty.
fn push_fold(out: &mut Vec<Instr>, field: OperandField, ops: Vec<OperandLine>, is_add: bool, sign: Sign) {
    if is_add {
        out.push(Instr::Add {
            field,
            sign,
            operands: ops,
        });
    } else {
        out.push(Instr::Mul { field, operands: ops });
    }
}

/// The evict primitive: `MOV DstFromAcc Smem{cell}` writes the current accumulator
/// to an smem cell so it can be referenced as an `OperandLine::Smem` operand later
/// (spec §11; Task 13 reuses this for nested subexpressions). `field` labels the
/// MOV for the validator; the interpreter ignores the MOV field for value.
fn evict_acc_to_cell(out: &mut Vec<Instr>, field: OperandField, cell: u16) {
    out.push(Instr::Mov {
        dir: MovDir::DstFromAcc,
        field,
        dst: Some(DstLine::Smem { cell }),
        src: None,
    });
}

// ── FMA (product-sum) ────────────────────────────────────────────────────────────

/// Lower an Add to `init/ADD (the additive terms) ; FMA[products grouped by
/// (lhs_field, rhs_field)]` (§6, H6). By commutativity an Add splits freely into
/// its binary-product children (the "mads") and its plain additive children:
/// - With ≥1 addend, the addends seed the accumulator (an init MOV from addend0,
///   then one field-grouped ADD per remaining Base/Ext group), and EVERY product
///   folds in as an FMA pair.
/// - With no addends, the accumulator is seeded from the first product
///   (`MOV lhs0; MUL rhs0`) and the remaining products fold in as FMA pairs — the
///   proven all-products form.
///
/// This subsumes the lookup α-fold (a single leading unscaled column is just one
/// addend → `MOV col0; FMA[(col1,α1),…]`).
///
/// Returns `Ok(Some(()))` if it applied, `Ok(None)` when the Add has NO binary
/// product child (a pure additive reduction — the caller falls back to the
/// generic field-grouped reduction).
fn try_compile_fma(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    children: &[ExprId],
    ctx: &mut DagForwardContext,
    trace: &mut CompileTrace,
    out: &mut Vec<Instr>,
    alloc: &mut CellAllocator,
    expected: OperandField,
) -> Result<Option<()>, CompileError> {
    // Partition (preserving order): a (possibly negated) binary product becomes a
    // signed FMA pair; every other child is an additive term that seeds/folds the
    // accumulator. A negated single-factor `(-1)·x` becomes a `Sign::Minus` addend
    // that lowers `x` (not the wrapping Mul) — the negate folds into the ADD's sign
    // bit (#7). Carry each term's sign so the negate never needs a unary MUL lit(-1).
    let mut products: Vec<(Sign, ExprId, ExprId)> = Vec::with_capacity(children.len());
    let mut addends: Vec<(Sign, ExprId)> = Vec::new();
    for &c in children {
        match classify_additive_child(layer, c) {
            AdditiveChild::Product { sign, lhs, rhs } => products.push((sign, lhs, rhs)),
            AdditiveChild::Addend { sign, id } => addends.push((sign, id)),
        }
    }
    // No product → not an FMA opportunity; let the generic reduction handle it.
    if products.is_empty() {
        return Ok(None);
    }

    // Pre-materialize EVERY operand BEFORE touching the acc (a compound child —
    // e.g. a product-of-sums — lowers to a cell, which clobbers the acc). Collect
    // each operand's field label via `child_operand_field` BEFORE the `&mut ctx`
    // borrow in `lower_operand` so the immutable `layer` borrow does not overlap.
    let mut owned_cells: Vec<u16> = Vec::new();
    let mut addend_ops: Vec<(OperandField, OperandLine, Sign)> =
        Vec::with_capacity(addends.len());
    for &(sign, c) in &addends {
        let f = child_operand_field(layer, c, expected, &ctx.cross_layer_fields);
        let (op, cell) = lower_operand(layer, c, ctx, trace, out, alloc, f)?;
        if let Some(cell) = cell {
            owned_cells.push(cell);
        }
        addend_ops.push((f, op, sign));
    }
    let mut lo: Vec<(Sign, OperandField, OperandLine, OperandField, OperandLine)> =
        Vec::with_capacity(products.len());
    for &(sign, lhs, rhs) in &products {
        let lf = child_operand_field(layer, lhs, expected, &ctx.cross_layer_fields);
        let rf = child_operand_field(layer, rhs, expected, &ctx.cross_layer_fields);
        let (lhs_op, lc) = lower_operand(layer, lhs, ctx, trace, out, alloc, lf)?;
        if let Some(c) = lc {
            owned_cells.push(c);
        }
        let (rhs_op, rc) = lower_operand(layer, rhs, ctx, trace, out, alloc, rf)?;
        if let Some(c) = rc {
            owned_cells.push(c);
        }
        lo.push((sign, lf, lhs_op, rf, rhs_op));
    }

    // Seed the accumulator; `fma_lo` is the product range still to fold as FMA.
    // The seed MUST be an un-negated (Plus) term — there is no negating init MOV.
    let fma_lo: &[(Sign, OperandField, OperandLine, OperandField, OperandLine)] =
        if !addend_ops.is_empty() {
            // Seed from a Plus BASE addend when one exists (base as long as possible,
            // §5; Plus because the seed cannot be negated), then a Plus Ext addend;
            // only if every addend is negated (does not occur in the gated circuits)
            // fall back to the current Base-first seed. The remaining addends fold as
            // `(field, sign)`-grouped ADDs (Base groups then Ext groups); every
            // product then folds in as a signed FMA pair.
            let seed = addend_ops
                .iter()
                .position(|(f, _, s)| *f == OperandField::Base && *s == Sign::Plus)
                .or_else(|| addend_ops.iter().position(|(_, _, s)| *s == Sign::Plus))
                .or_else(|| addend_ops.iter().position(|(f, _, _)| *f == OperandField::Base))
                .unwrap_or(0);
            emit_init_field(out, addend_ops[seed].1, addend_ops[seed].0);
            // Negated-seed compensation (#7): if every addend was negated the seed is
            // Minus; negate the acc right after the init since the init MOV cannot.
            if addend_ops[seed].2 == Sign::Minus {
                emit_unary_negate(out);
            }
            let mut base_plus: Vec<OperandLine> = Vec::new();
            let mut base_minus: Vec<OperandLine> = Vec::new();
            let mut ext_plus: Vec<OperandLine> = Vec::new();
            let mut ext_minus: Vec<OperandLine> = Vec::new();
            for (i, &(f, op, s)) in addend_ops.iter().enumerate() {
                if i == seed {
                    continue;
                }
                match (f, s) {
                    (OperandField::Base, Sign::Plus) => base_plus.push(op),
                    (OperandField::Base, Sign::Minus) => base_minus.push(op),
                    (OperandField::Ext, Sign::Plus) => ext_plus.push(op),
                    (OperandField::Ext, Sign::Minus) => ext_minus.push(op),
                }
            }
            for (f, s, group) in [
                (OperandField::Base, Sign::Plus, base_plus),
                (OperandField::Base, Sign::Minus, base_minus),
                (OperandField::Ext, Sign::Plus, ext_plus),
                (OperandField::Ext, Sign::Minus, ext_minus),
            ] {
                if group.is_empty() {
                    continue;
                }
                emit_reduction_group(out, trace, f, group, /* is_add */ true, s, alloc)?;
            }
            &lo[..]
        } else {
            // No addends: seed from a Plus product (MOV lhs0; MUL rhs0) — the seed
            // cannot be negated — then FMA the rest. Prefer a Plus product as the
            // seed; only if every product is negated (does not occur in the gated
            // circuits) fall back to the first product. This is the proven
            // all-products form when no negate is present.
            let seed = lo.iter().position(|(s, ..)| *s == Sign::Plus).unwrap_or(0);
            let (seed_sign, lf0, lhs0_op, rf0, rhs0_op) = lo[seed];
            emit_init_field(out, lhs0_op, lf0);
            out.push(Instr::Mul { field: rf0, operands: vec![rhs0_op] });
            // Negated-seed compensation (#7): if every product was negated the seed
            // product is Minus; negate the acc after seeding (MOV+MUL) since neither
            // the init MOV nor the seed MUL carries the sign.
            if seed_sign == Sign::Minus {
                emit_unary_negate(out);
            }
            if lo.len() == 1 {
                free_all(alloc, &owned_cells);
                return Ok(Some(()));
            }
            lo.remove(seed);
            &lo[..]
        };

    // Group the FMA pairs by canonical (lhs_field, rhs_field, sign). Canonical mixed
    // order is (Base, Ext): swap the commutative factors so EB is never emitted
    // (H5). A negated product folds as a `Sign::Minus` FMA pair (zero extra
    // instructions). Emit one (arity-chunked) FMA per (field-pair, sign) group.
    use std::collections::BTreeMap;
    let mut groups: BTreeMap<(u8, u8, u8), Vec<(OperandLine, OperandLine)>> = BTreeMap::new();
    for &(sign, lf, lhs_op, rf, rhs_op) in fma_lo {
        let ((cf_l, cf_r), (op_l, op_r)) = canonical_fma_pair(lf, rf, lhs_op, rhs_op);
        groups
            .entry((cf_l as u8, cf_r as u8, sign as u8))
            .or_default()
            .push((op_l, op_r));
    }
    for ((lf, rf, sign), gpairs) in groups {
        push_fma_chunked(out, field_from_u8(lf), field_from_u8(rf), sign_from_u8(sign), gpairs);
    }
    free_all(alloc, &owned_cells);
    Ok(Some(()))
}

/// Canonicalize a commutative FMA `(lhs, rhs)` pair so a mixed product is always
/// `(field_lhs=Base, field_rhs=Ext)` — never `EB` (H5). Same-field pairs keep order.
fn canonical_fma_pair(
    lf: OperandField,
    rf: OperandField,
    lhs: OperandLine,
    rhs: OperandLine,
) -> ((OperandField, OperandField), (OperandLine, OperandLine)) {
    match (lf, rf) {
        (OperandField::Ext, OperandField::Base) => {
            // swap to canonical (Base, Ext)
            ((OperandField::Base, OperandField::Ext), (rhs, lhs))
        }
        _ => ((lf, rf), (lhs, rhs)),
    }
}

fn field_from_u8(v: u8) -> OperandField {
    if v == 0 {
        OperandField::Base
    } else {
        OperandField::Ext
    }
}

fn sign_from_u8(v: u8) -> Sign {
    if v == 0 {
        Sign::Plus
    } else {
        Sign::Minus
    }
}

/// Emit one or more `Instr::Fma` instructions that together accumulate all `pairs`
/// for the given `(field_lhs, field_rhs)` group. Chunks `pairs` into slices of at
/// most `MAX_ARITY` to satisfy the encoder's 7-bit arity cap. Multiple Fma
/// instructions over the same group are value-correct: FMA accumulates into the acc,
/// so appending chunks is equivalent to a single large Fma (Split-before-encoding,
/// mirroring what `emit_reduction_group` does for ADD/MUL).
fn push_fma_chunked(
    out: &mut Vec<Instr>,
    field_lhs: OperandField,
    field_rhs: OperandField,
    sign: Sign,
    pairs: Vec<(OperandLine, OperandLine)>,
) {
    for chunk in pairs.chunks(MAX_ARITY) {
        out.push(Instr::Fma {
            field_lhs,
            field_rhs,
            sign,
            pairs: chunk.to_vec(),
        });
    }
}

// ── small structural predicates ──────────────────────────────────────────────────

/// True if `id` is a `Source` whose value is the field element `−1` (= P−1 =
/// `BABYBEAR_NEG_ONE`). These factors are stripped from Mul children before
/// field-grouped reduction; their count's parity decides the unary negate.
fn is_neg_one_factor(layer: &cs::gkr_compiler::dag_ir::DagLayer, id: ExprId) -> bool {
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
enum AdditiveChild {
    Product { sign: Sign, lhs: ExprId, rhs: ExprId },
    Addend { sign: Sign, id: ExprId },
}

/// Classify an additive child of a sum into a product (FMA) or a sign-keyed addend.
/// Shared by `try_compile_fma`'s product/addend partition AND `compile_reduction`'s
/// add path so the negate-into-sign fold is uniform (DRY).
fn classify_additive_child(
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

fn is_constant_one(layer: &cs::gkr_compiler::dag_ir::DagLayer, id: ExprId) -> bool {
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
fn is_zero_expr(layer: &cs::gkr_compiler::dag_ir::DagLayer, id: ExprId) -> bool {
    match &layer.exprs[id.0 as usize] {
        Expr::Source(_) => is_constant_zero(layer, id),
        Expr::Mul(factors) => factors.iter().any(|&f| is_zero_expr(layer, f)),
        Expr::Add(_) => false,
    }
}

// ── Tests ────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fwd::context::{CompileTrace, DagForwardContext};
    use crate::fwd::isa::{Instr, LdcSub, MovDir, OperandField, OperandLine, Sign, Special};
    use cs::gkr_compiler::dag_ir::{
        ArenaBuilder, BatchingOrder, ChallengeKey, ChallengePower, ChallengeRef, DagLayer, ExprId,
        ReadPlace, ResolutionStrategy, SourceKind,
    };
    use std::collections::BTreeMap;

    // Build a DagLayer from an arena with no roots/sinks (structural lowering only).
    fn layer_of(arena: &ArenaBuilder) -> DagLayer {
        DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots: vec![],
            sinks: vec![],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(),
            resolutions: BTreeMap::new(),
        }
    }

    fn run(layer: &DagLayer, expr: ExprId) -> Vec<Instr> {
        let mut ctx = DagForwardContext::default();
        let mut trace = CompileTrace::default();
        let mut out = Vec::new();
        let mut alloc = CellAllocator::new(1024);
        compile_expr(layer, expr, &mut ctx, &mut trace, &mut out, &mut alloc, OperandField::Base)
            .expect("compile_expr");
        out
    }

    fn try_run(layer: &DagLayer, expr: ExprId) -> Result<Vec<Instr>, CompileError> {
        let mut ctx = DagForwardContext::default();
        let mut trace = CompileTrace::default();
        let mut out = Vec::new();
        let mut alloc = CellAllocator::new(1024);
        compile_expr(layer, expr, &mut ctx, &mut trace, &mut out, &mut alloc, OperandField::Base)?;
        Ok(out)
    }

    // A base-storage column read → Global operand.
    fn read_base(arena: &mut ArenaBuilder, col: usize) -> ExprId {
        let s = arena.intern_source(SourceKind::Read {
            place: ReadPlace::BaseLayerMemory { column: col },
        });
        arena.source_expr(s)
    }

    // An Ext challenge → Ldc operand.
    fn challenge(arena: &mut ArenaBuilder, power: ChallengePower) -> ExprId {
        let s = arena.intern_source(SourceKind::Challenge {
            reference: ChallengeRef {
                key: ChallengeKey::LookupAdditive,
                power,
            },
        });
        arena.source_expr(s)
    }

    fn mov_acc(op: OperandLine) -> Instr {
        Instr::Mov {
            dir: MovDir::AccFromSrc,
            field: OperandField::Base,
            dst: None,
            src: Some(op),
        }
    }

    // ── Add(a) unary → [Mov AccFromSrc a] ─────────────────────────────────────
    #[test]
    fn add_unary_is_just_mov() {
        let mut arena = ArenaBuilder::new();
        let a = read_base(&mut arena, 0);
        let add = arena.add(vec![a]);
        let layer = layer_of(&arena);
        // arena.add of a single non-Add child returns the child expr itself —
        // assert the lowering of whichever id is the Add, else the source.
        let instrs = run(&layer, add);
        assert_eq!(instrs, vec![mov_acc(OperandLine::Global { slot: 0, col: 0 })]);
    }

    // ── Add(a_base, b_base) → [Mov a, Add Base +[b]] ──────────────────────────
    #[test]
    fn add_two_base() {
        let mut arena = ArenaBuilder::new();
        let a = read_base(&mut arena, 0); // lower ExprId
        let b = read_base(&mut arena, 1); // higher ExprId → second operand after sort
        let add = arena.add(vec![a, b]);
        let layer = layer_of(&arena);
        let instrs = run(&layer, add);
        assert_eq!(
            instrs,
            vec![
                mov_acc(OperandLine::Global { slot: 0, col: 0 }),
                Instr::Add {
                    field: OperandField::Base,
                    sign: Sign::Plus,
                    operands: vec![OperandLine::Global { slot: 0, col: 1 }],
                },
            ]
        );
    }

    // ── Add(a_base, c_ext) → [Mov a, Add Ext +[c]] (acc promotes; not mixed) ──
    #[test]
    fn add_base_plus_ext() {
        let mut arena = ArenaBuilder::new();
        let a = read_base(&mut arena, 0); // ExprId 0
        let c = challenge(&mut arena, ChallengePower::One); // ExprId 1
        let add = arena.add(vec![a, c]);
        let layer = layer_of(&arena);
        let instrs = run(&layer, add);
        assert_eq!(
            instrs,
            vec![
                mov_acc(OperandLine::Global { slot: 0, col: 0 }),
                Instr::Add {
                    field: OperandField::Ext,
                    sign: Sign::Plus,
                    operands: vec![OperandLine::Ldc {
                        sub: LdcSub::ConstChallenge,
                        idx: 0,
                    }],
                },
            ]
        );
    }

    // ── #5b: base-as-long-as-possible seed ────────────────────────────────────
    // When an EXT child has the lower ExprId (sorts first) but a BASE child is
    // present, the reduction must STILL seed the acc from the base operand so
    // the base accumulation runs base-width; the ext term then promotes via a
    // trailing ADD.e. Seeding from the ext child (the old `ops[0]` behavior)
    // would force the base fold into an ext-width acc — a mixed op where a base
    // op would do (§5).
    #[test]
    fn reduction_seeds_base_when_ext_sorts_first() {
        let mut arena = ArenaBuilder::new();
        let c = challenge(&mut arena, ChallengePower::One); // ExprId 0 (ext) — sorts first
        let a = read_base(&mut arena, 7); // ExprId 1 (base)
        let add = arena.add(vec![c, a]);
        let layer = layer_of(&arena);
        let instrs = run(&layer, add);
        // Seed is the BASE read, labeled Base — NOT the ext challenge.
        assert_eq!(
            instrs[0],
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Base,
                dst: None,
                src: Some(OperandLine::Global { slot: 0, col: 7 }),
            },
            "reduction must seed from the base operand even when the ext term sorts first",
        );
        // The ext challenge folds in as a promoting ADD.e (acc Base→Ext).
        assert!(
            matches!(instrs[1], Instr::Add { field: OperandField::Ext, .. }),
            "ext term must fold as ADD.e after the base seed, got {:?}",
            instrs[1],
        );
    }

    // ── Add(Mul(a,b), Mul(c,d)) → [Mov a, Mul Base [b], Fma + [(c,d)]] ─────────
    #[test]
    fn add_of_products_is_fma() {
        let mut arena = ArenaBuilder::new();
        let a = read_base(&mut arena, 0); // ExprId 0
        let b = read_base(&mut arena, 1); // ExprId 1
        let c = read_base(&mut arena, 2); // ExprId 2
        let d = read_base(&mut arena, 3); // ExprId 3
        let ab = arena.mul(vec![a, b]); // Mul([a,b])
        let cd = arena.mul(vec![c, d]); // Mul([c,d])
        let add = arena.add(vec![ab, cd]); // sorted by ExprId: ab < cd
        let layer = layer_of(&arena);
        let instrs = run(&layer, add);
        assert_eq!(
            instrs,
            vec![
                mov_acc(OperandLine::Global { slot: 0, col: 0 }),
                Instr::Mul {
                    field: OperandField::Base,
                    operands: vec![OperandLine::Global { slot: 0, col: 1 }],
                },
                Instr::Fma {
                    field_lhs: OperandField::Base,
                    field_rhs: OperandField::Base,
                    sign: Sign::Plus,
                    pairs: vec![(
                        OperandLine::Global { slot: 0, col: 2 },
                        OperandLine::Global { slot: 0, col: 3 },
                    )],
                },
            ]
        );
    }

    // ── Add(Mul(a,b), Mul(c,d), e1, e2) MUST still emit FMA ───────────────────
    //
    // A sum that MIXES products (mads) with plain additive terms is FMA-emittable:
    // by commutativity it decomposes to an init/ADD over the addends followed by
    // FMAs over the products. This is the shape of every real GKR memory/lookup
    // fold (e.g. add_sub's cache roots: `χ_add + 0 + Σ_j mem_j·χ_j`). The two
    // additive challenge terms guarantee this is neither all-products (the H6 FMA
    // guard) nor a single-leading-term α-fold — so it exercises the mixed path.
    //
    // Gap regression: the value-only parity gates cannot catch a MISSED fusion
    // (materialize-each-product-to-a-cell is value-correct), so this asserts the
    // emitted SHAPE directly: the compiler must in fact emit ≥1 Instr::Fma.
    #[test]
    fn add_of_products_mixed_with_addends_is_fma() {
        let mut arena = ArenaBuilder::new();
        let a = read_base(&mut arena, 0);
        let b = read_base(&mut arena, 1);
        let c = read_base(&mut arena, 2);
        let d = read_base(&mut arena, 3);
        let e1 = challenge(&mut arena, ChallengePower::One);
        let e2 = challenge(&mut arena, ChallengePower::Static(1));
        let ab = arena.mul(vec![a, b]);
        let cd = arena.mul(vec![c, d]);
        let add = arena.add(vec![ab, cd, e1, e2]); // a·b + c·d + e1 + e2
        let layer = layer_of(&arena);
        let instrs = run(&layer, add);
        assert!(
            instrs.iter().any(|i| matches!(i, Instr::Fma { .. })),
            "a·b + c·d + e1 + e2 is FMA-emittable, but the compiler emitted no FMA \
             (it materialized each product into a cell instead). Program:\n{instrs:#?}"
        );
    }

    // ── Add(a, const_0) → [Mov a] (the additive `0` elided) ──────────────────
    //
    // Symmetric to `mul_by_one_elides`: an additive `Constant{0}` term is identity
    // and must be dropped, not emitted as a no-op `ADD #0`. add_sub L0 carried 6 of
    // these (the permutation-additive seed of each memory fold).
    #[test]
    fn add_zero_elides() {
        let mut arena = ArenaBuilder::new();
        let a = read_base(&mut arena, 0);
        let zero_src = arena.intern_source(SourceKind::Constant { value: 0 });
        let zero = arena.source_expr(zero_src);
        let add = arena.add(vec![a, zero]);
        let layer = layer_of(&arena);
        let instrs = run(&layer, add);
        assert_eq!(instrs, vec![mov_acc(OperandLine::Global { slot: 0, col: 0 })]);
    }

    // ── Add(a, const_1) → [Mov a, Add lit(One)]: 1 goes to the Special literal ─
    //
    // The special field element `1` is encoded inline as `Special::One`, NOT
    // interned into the const bank (no GPU `__constant__` slot, can't slip through
    // as a plain const). The operand being `Ldc{Special, One}` rather than
    // `Ldc{Const, _}` proves it never hit the bank.
    #[test]
    fn additive_one_uses_special_not_const_bank() {
        let mut arena = ArenaBuilder::new();
        let a = read_base(&mut arena, 0);
        let one_src = arena.intern_source(SourceKind::Constant { value: 1 });
        let one = arena.source_expr(one_src);
        let add = arena.add(vec![a, one]);
        let layer = layer_of(&arena);
        let instrs = run(&layer, add);
        assert_eq!(
            instrs,
            vec![
                mov_acc(OperandLine::Global { slot: 0, col: 0 }),
                Instr::Add {
                    field: OperandField::Base,
                    sign: Sign::Plus,
                    operands: vec![OperandLine::Ldc { sub: LdcSub::Special, idx: Special::One as u16 }],
                },
            ]
        );
    }

    // ── Add(Mul(a,b), Mul(c,0)) → [Mov a, Mul b]: the zero product is dropped ───
    //
    // `c * 0` is a multiplicative annihilator (== 0); it must be dropped from the
    // sum, not lowered (its `Constant{0}` factor would otherwise leak into the
    // const bank as a silent `#0`). Only `a*b` survives.
    #[test]
    fn zero_product_term_dropped_from_sum() {
        let mut arena = ArenaBuilder::new();
        let a = read_base(&mut arena, 0);
        let b = read_base(&mut arena, 1);
        let c = read_base(&mut arena, 2);
        let zero_src = arena.intern_source(SourceKind::Constant { value: 0 });
        let zero = arena.source_expr(zero_src);
        let ab = arena.mul(vec![a, b]);
        let cz = arena.mul(vec![c, zero]); // c * 0 == 0
        let add = arena.add(vec![ab, cz]); // a*b + c*0  ==  a*b
        let layer = layer_of(&arena);
        let instrs = run(&layer, add);
        assert_eq!(
            instrs,
            vec![
                mov_acc(OperandLine::Global { slot: 0, col: 0 }),
                Instr::Mul {
                    field: OperandField::Base,
                    operands: vec![OperandLine::Global { slot: 0, col: 1 }],
                },
            ]
        );
    }

    // ── Mul(a, const_1) → [Mov a] (the `1` factor elided) ─────────────────────
    #[test]
    fn mul_by_one_elides() {
        let mut arena = ArenaBuilder::new();
        let a = read_base(&mut arena, 0);
        let one_src = arena.intern_source(SourceKind::Constant { value: 1 });
        let one = arena.source_expr(one_src);
        let mul = arena.mul(vec![a, one]);
        let layer = layer_of(&arena);
        let instrs = run(&layer, mul);
        assert_eq!(instrs, vec![mov_acc(OperandLine::Global { slot: 0, col: 0 })]);
    }

    // ── Mul(base_col, challenge) → [Mov base_col, Mul{Ext} [challenge]] ─────────
    //
    // Regression for the Task 10 regression: compile_mul must emit a separate
    // `Instr::Mul{field:Ext}` for the Ext-typed challenge factor — NOT a single
    // `Instr::Mul{field:Base}` over both operands. Verifies §5 field-homogeneous
    // MUL grouping is preserved after negate-canonicalization was introduced.
    #[test]
    fn mul_base_times_ext_groups_by_field() {
        let mut arena = ArenaBuilder::new();
        let a = read_base(&mut arena, 0); // Base-typed column
        let c = challenge(&mut arena, ChallengePower::One); // Ext-typed challenge
        let mul = arena.mul(vec![a, c]);
        let layer = layer_of(&arena);
        let instrs = run(&layer, mul);
        // Expected: MOV from Base col, then MUL{Ext} for the challenge.
        // A `MUL{field:Base}` over both is the bug this test catches.
        assert_eq!(
            instrs,
            vec![
                mov_acc(OperandLine::Global { slot: 0, col: 0 }),
                Instr::Mul {
                    field: OperandField::Ext,
                    operands: vec![OperandLine::Ldc {
                        sub: LdcSub::ConstChallenge,
                        idx: 0,
                    }],
                },
            ]
        );
    }

    // ── Mul(−1, base_col, challenge) → [Mov base_col, Mul{Base} [Special(NegOne)],
    //    Mul{Ext} [challenge]] — negate runs in the base phase (Task 5) ──────────
    //
    // Regression: negate canonicalization must strip the −1 factor BEFORE routing
    // through compile_reduction so field grouping still applies to survivors.
    // Task 5: for a mixed base×ext product the standalone negate is inserted AFTER
    // the base-field groups and BEFORE the ext-field groups — base-as-long-as-possible.
    // The acc is still base-width when the negate fires, so the 1-wide negate is
    // semantically identical but avoids promoting the acc unnecessarily early.
    #[test]
    fn mul_neg_one_base_ext_negate_and_groups_by_field() {
        let mut arena = ArenaBuilder::new();
        let neg_one_src = arena.intern_source(SourceKind::Constant { value: BABYBEAR_NEG_ONE });
        let neg_one = arena.source_expr(neg_one_src);
        let a = read_base(&mut arena, 0); // Base
        let c = challenge(&mut arena, ChallengePower::One); // Ext
        let mul = arena.mul(vec![neg_one, a, c]);
        let layer = layer_of(&arena);
        let instrs = run(&layer, mul);
        // Expected (Task 5): MOV Base col, unary negate MUL{Base}[NegOne], MUL{Ext} challenge.
        // The negate fires while the acc is still base-width; the ext MUL promotes it.
        assert_eq!(
            instrs,
            vec![
                mov_acc(OperandLine::Global { slot: 0, col: 0 }),
                Instr::Mul {
                    field: OperandField::Base,
                    operands: vec![OperandLine::Ldc {
                        sub: LdcSub::Special,
                        idx: Special::NegOne as u16,
                    }],
                },
                Instr::Mul {
                    field: OperandField::Ext,
                    operands: vec![OperandLine::Ldc {
                        sub: LdcSub::ConstChallenge,
                        idx: 0,
                    }],
                },
            ]
        );
    }

    // ── Over-long Base ADD reduction splits with evict-to-cell ────────────────
    //
    // A flat Add of 200 base columns exceeds the 7-bit arity cap (127) in a single
    // ADD instruction, which `encode` rejects. compile_reduction must split the
    // Base group via split_reduction + the evict-to-cell primitive so NO emitted
    // ADD carries more than MAX_ARITY operands, while every term is still folded in.
    #[test]
    fn long_add_reduction_splits_below_arity_cap() {
        const N: usize = 200;
        let mut arena = ArenaBuilder::new();
        let cols: Vec<ExprId> = (0..N).map(|i| read_base(&mut arena, i)).collect();
        let add = arena.add(cols);
        let layer = layer_of(&arena);
        let instrs = run(&layer, add);

        // No single ADD may exceed the arity cap.
        for instr in &instrs {
            if let Instr::Add { operands, .. } = instr {
                assert!(
                    operands.len() <= MAX_ARITY,
                    "ADD with arity {} exceeds MAX_ARITY {}",
                    operands.len(),
                    MAX_ARITY
                );
            }
        }

        // The split must use the evict-to-cell primitive: at least one
        // `MOV DstFromAcc -> Smem` (evict) and at least one ADD over a Smem operand
        // (fold the evicted partial back in).
        let has_evict = instrs.iter().any(|i| {
            matches!(
                i,
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    dst: Some(DstLine::Smem { .. }),
                    ..
                }
            )
        });
        assert!(has_evict, "expected an evict MOV DstFromAcc -> Smem");
        let folds_cell = instrs.iter().any(|i| matches!(
            i,
            Instr::Add { operands, .. }
                if operands.iter().any(|o| matches!(o, OperandLine::Smem { .. }))
        ));
        assert!(folds_cell, "expected an ADD folding a Smem partial back in");

        // Every distinct base column 0..N must appear as an ADD/MOV operand exactly
        // once (no term dropped, none duplicated) — Smem partials excepted.
        use std::collections::BTreeSet;
        let mut seen: BTreeSet<u16> = BTreeSet::new();
        let mut record = |op: &OperandLine| {
            if let OperandLine::Global { col, .. } = op {
                assert!(seen.insert(*col), "column {} folded twice", col);
            }
        };
        for instr in &instrs {
            match instr {
                Instr::Mov { src: Some(op), .. } => record(op),
                Instr::Add { operands, .. } => operands.iter().for_each(&mut record),
                _ => {}
            }
        }
        let expected: BTreeSet<u16> = (0..N as u16).collect();
        assert_eq!(seen, expected, "every base column must be folded exactly once");

        // End-to-end: the split program clears the encoder's arity cap-guard
        // (`pack_arith_header` rejects arity > MAX_ARITY) — the motivation for the
        // split. Without it, encode would return Err(ArityOutOfRange(199)).
        let program = crate::fwd::isa::Program { instrs };
        crate::fwd::encode::encode(&program).expect("split program must encode within arity cap");
    }

    // ── Mul([−1]) (single −1 factor) → Err(DegenerateConstProduct) ──────────────
    //
    // Before the fix, the odd-count surviving.is_empty() branch called
    // emit_unary_negate with NO preceding init MOV, materializing 0 not −1.
    // The DegenerateRoot guard in compile_layer missed it because instructions WERE
    // emitted. compile_mul must reject this case fail-loud.
    #[test]
    fn mul_only_neg_one_single_rejected() {
        let mut arena = ArenaBuilder::new();
        let neg_one_src = arena.intern_source(SourceKind::Constant { value: BABYBEAR_NEG_ONE });
        let neg_one = arena.source_expr(neg_one_src);
        let mul = arena.mul(vec![neg_one]); // Mul([−1]): single −1 factor, odd count
        let layer = layer_of(&arena);
        let err = try_run(&layer, mul).unwrap_err();
        assert_eq!(err, CompileError::DegenerateConstProduct);
    }

    // ── Mul([−1, −1]) (even count of −1) → Err(DegenerateConstProduct) ──────────
    //
    // Even count: product is +1 (NOP). The surviving.is_empty() branch previously
    // emitted nothing, and compile_layer's len_before guard might still catch it when
    // the Mul is a root. But compile_mul is also called for sub-expressions where no
    // such guard exists. Reject both parities fail-loud.
    #[test]
    fn mul_only_neg_one_even_count_rejected() {
        let mut arena = ArenaBuilder::new();
        let neg_one_src = arena.intern_source(SourceKind::Constant { value: BABYBEAR_NEG_ONE });
        let neg_one_a = arena.source_expr(neg_one_src);
        let neg_one_b = arena.source_expr(neg_one_src);
        let mul = arena.mul(vec![neg_one_a, neg_one_b]); // Mul([−1, −1]): even count
        let layer = layer_of(&arena);
        let err = try_run(&layer, mul).unwrap_err();
        assert_eq!(err, CompileError::DegenerateConstProduct);
    }

    // ── FMA group >127 pairs splits into multiple Fma each ≤ MAX_ARITY ───────────
    //
    // 130 binary products Mul(col_i, col_j) — all (Base,Base) → single group of 130
    // pairs. Before the fix, one Instr::Fma with 129 pairs was emitted (arity 129 >
    // MAX_ARITY=127), which encode rejects. After the fix, pairs are chunked ≤127.
    #[test]
    fn fma_over_max_arity_splits() {
        const N: usize = 130; // > MAX_ARITY (127)
        let mut arena = ArenaBuilder::new();
        // Allocate 2*N columns; pair up col_(2i) × col_(2i+1).
        let cols: Vec<ExprId> = (0..2 * N).map(|i| read_base(&mut arena, i)).collect();
        let products: Vec<ExprId> = (0..N)
            .map(|i| arena.mul(vec![cols[2 * i], cols[2 * i + 1]]))
            .collect();
        let add = arena.add(products);
        let layer = layer_of(&arena);
        let instrs = run(&layer, add);

        // Every Fma must have pairs.len() ≤ MAX_ARITY.
        for instr in &instrs {
            if let Instr::Fma { pairs, .. } = instr {
                assert!(
                    pairs.len() <= MAX_ARITY,
                    "Fma with {} pairs exceeds MAX_ARITY {}",
                    pairs.len(),
                    MAX_ARITY
                );
            }
        }

        // There must be at least 2 Fma instructions (the N=130 pairs can't fit in 1).
        let fma_count = instrs.iter().filter(|i| matches!(i, Instr::Fma { .. })).count();
        assert!(fma_count >= 2, "expected multiple Fma after split, got {}", fma_count);

        // The split program must encode cleanly (arity cap guard).
        let program = crate::fwd::isa::Program { instrs };
        crate::fwd::encode::encode(&program)
            .expect("split FMA program must encode within arity cap");
    }

    // ── α-fold → [Mov col0, Fma{lhs=Base,rhs=Ext} [(col1,α1),…]] ──────────────
    #[test]
    fn alpha_fold() {
        let mut arena = ArenaBuilder::new();
        // col0 (unscaled), col1·α1, col2·α2
        let col0 = read_base(&mut arena, 0); // ExprId 0
        let col1 = read_base(&mut arena, 1); // ExprId 1
        let col2 = read_base(&mut arena, 2); // ExprId 2
        let a1 = challenge(&mut arena, ChallengePower::Static(1)); // ExprId 3
        let a2 = challenge(&mut arena, ChallengePower::Static(2)); // ExprId 4
        let t1 = arena.mul(vec![col1, a1]); // Mul([col1, a1])
        let t2 = arena.mul(vec![col2, a2]); // Mul([col2, a2])
        let fold = arena.add(vec![col0, t1, t2]); // sorted ascending by ExprId
        let layer = layer_of(&arena);
        let instrs = run(&layer, fold);
        assert_eq!(
            instrs,
            vec![
                mov_acc(OperandLine::Global { slot: 0, col: 0 }),
                Instr::Fma {
                    field_lhs: OperandField::Base,
                    field_rhs: OperandField::Ext,
                    sign: Sign::Plus,
                    pairs: vec![
                        (
                            OperandLine::Global { slot: 0, col: 1 },
                            OperandLine::Ldc { sub: LdcSub::ConstChallenge, idx: 0 },
                        ),
                        (
                            OperandLine::Global { slot: 0, col: 2 },
                            OperandLine::Ldc { sub: LdcSub::ConstChallenge, idx: 1 },
                        ),
                    ],
                },
            ]
        );
    }

    // ── resolution probe in lower_operand emits exactly ONE descriptor ────────────
    //
    // Before the fix, lower_operand called resolve_or_descend (mutating) as a probe,
    // then source_to_operand called resolve_or_descend again — pushing TWO descriptors
    // for each resolution-pruned expr. After the fix, the probe is replaced with the
    // non-mutating `layer.resolutions.contains_key(&expr_id)`, so source_to_operand's
    // single call is the only push, yielding exactly one descriptor.
    #[test]
    fn resolution_probe_emits_single_descriptor() {
        let mut arena = ArenaBuilder::new();
        // Create a non-Source expr (Mul([a, b])) so it's not caught by the Source
        // branch — only the resolution branch fires.
        let a = read_base(&mut arena, 0);
        let b = read_base(&mut arena, 1);
        let fold = arena.mul(vec![a, b]); // a non-Source expr that will be resolved

        // Attach a PeekSetup resolution to the Mul expr.
        let mut resolutions = BTreeMap::new();
        resolutions.insert(fold, ResolutionStrategy::PeekSetup);

        let layer = DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots: vec![],
            sinks: vec![],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(),
            resolutions,
        };

        let mut ctx = DagForwardContext::default();
        let mut trace = CompileTrace::default();
        let mut out = Vec::new();
        let mut alloc = CellAllocator::new(1024);

        // lower_operand on the resolution-pruned expr should emit exactly one descriptor.
        lower_operand(&layer, fold, &mut ctx, &mut trace, &mut out, &mut alloc, OperandField::Base)
            .expect("lower_operand");

        assert_eq!(
            ctx.specials.len(),
            1,
            "expected exactly 1 SpecialDescriptor after lower_operand; got {}",
            ctx.specials.len()
        );
    }

    // ── codex Imp2: cross-layer field map ─────────────────────────────────────

    use cs::gkr_compiler::dag_ir::{
        DagCircuit, DagGlobals, FieldKind, Root, SinkId, SinkInfo, SinkKind,
    };
    use std::collections::HashMap;

    // A cross-layer LayerOutput read → Global operand.
    fn read_layer_output(arena: &mut ArenaBuilder, layer: usize, offset: usize) -> ExprId {
        let s = arena.intern_source(SourceKind::Read {
            place: ReadPlace::LayerOutput { layer, offset },
        });
        arena.source_expr(s)
    }

    // Compile one expr WITH a cross-layer field map injected into the ctx, mirroring
    // what `compile_layer` does. `expected` is the enclosing sink's field.
    fn run_with_map(
        layer: &DagLayer,
        expr: ExprId,
        map: HashMap<ReadPlace, FieldKind>,
        expected: OperandField,
    ) -> Vec<Instr> {
        let mut ctx = DagForwardContext::default();
        ctx.cross_layer_fields = map;
        let mut trace = CompileTrace::default();
        let mut out = Vec::new();
        let mut alloc = CellAllocator::new(1024);
        compile_expr(layer, expr, &mut ctx, &mut trace, &mut out, &mut alloc, expected)
            .expect("compile_expr");
        out
    }

    // (a) build_cross_layer_field_map over a 2-layer circuit maps LayerOutput{0,0}
    //     and CacheOutput{0,1} to layer-0's declared sink fields.
    #[test]
    fn cross_layer_field_map_records_producing_sink_field() {
        // Layer 0 produces two sinks: an Inner{layer:0,offset:0} (Base) read later as
        // LayerOutput{0,0}, and a Cache{layer:0,offset:1} (Ext) read as CacheOutput{0,1}.
        let layer0 = DagLayer {
            sources: vec![],
            exprs: vec![],
            roots: vec![],
            sinks: vec![
                SinkInfo { kind: SinkKind::Inner { layer: 0, offset: 0 }, field: FieldKind::Base },
                SinkInfo { kind: SinkKind::Cache { layer: 0, offset: 1 }, field: FieldKind::Ext },
                // Export/Scratch are NOT read cross-layer → excluded from the map.
                SinkInfo { kind: SinkKind::Export { slot: 7 }, field: FieldKind::Ext },
                SinkInfo { kind: SinkKind::Scratch { slot: 3 }, field: FieldKind::Base },
            ],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(),
            resolutions: BTreeMap::new(),
        };
        let layer1 = DagLayer {
            sources: vec![],
            exprs: vec![],
            roots: vec![],
            sinks: vec![],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(),
            resolutions: BTreeMap::new(),
        };
        let circuit = DagCircuit {
            layers: vec![layer0, layer1],
            globals: DagGlobals { trace_len: 1, scratch: BTreeMap::new() },
        };

        let map = build_cross_layer_field_map(&circuit);
        assert_eq!(
            map.get(&ReadPlace::LayerOutput { layer: 0, offset: 0 }),
            Some(&FieldKind::Base),
            "LayerOutput{{0,0}} must map to layer-0 Inner sink field Base"
        );
        assert_eq!(
            map.get(&ReadPlace::CacheOutput { layer: 0, offset: 1 }),
            Some(&FieldKind::Ext),
            "CacheOutput{{0,1}} must map to layer-0 Cache sink field Ext"
        );
        // Export/Scratch sinks contribute nothing → map has exactly the two reads.
        assert_eq!(map.len(), 2, "only Inner/Cache sinks enter the map");
    }

    // (b) A layer-1 root `Add([cross_layer_base_read, ext_challenge])` labels the
    //     cross-layer read's INIT MOV as Base — NOT the enclosing Ext sink field.
    //     This is the codex Imp2 fix: WITHOUT the map (empty), `child_operand_field`
    //     falls back to `expected` (Ext) and the init MOV would be Ext (mislabel).
    #[test]
    fn mixed_cross_layer_base_read_labeled_base_not_ext() {
        let mut arena = ArenaBuilder::new();
        // child0: a cross-layer Base read (LayerOutput{0,0}); child1: an Ext challenge.
        let base_read = read_layer_output(&mut arena, 0, 0); // ExprId 0
        let chal = challenge(&mut arena, ChallengePower::One); // ExprId 1
        let add = arena.add(vec![base_read, chal]);
        let layer = layer_of(&arena);

        // The producing sink (layer-0 Inner{0,0}) is Base.
        let mut map = HashMap::new();
        map.insert(ReadPlace::LayerOutput { layer: 0, offset: 0 }, FieldKind::Base);

        // Enclosing sink is Ext (the Add joins to Ext via the challenge).
        let instrs = run_with_map(&layer, add, map, OperandField::Ext);

        // The init MOV (child0, the cross-layer read) MUST be labeled Base.
        let init = &instrs[0];
        match init {
            Instr::Mov { dir: MovDir::AccFromSrc, field, .. } => {
                assert_eq!(
                    *field,
                    OperandField::Base,
                    "cross-layer Base read init MOV must be labeled Base, got {:?}",
                    field
                );
            }
            other => panic!("expected an init MOV AccFromSrc, got {:?}", other),
        }
        // The Ext challenge promotes the acc via a separate Ext ADD group (§5).
        assert!(
            instrs.iter().any(|i| matches!(i, Instr::Add { field: OperandField::Ext, .. })),
            "expected an Ext ADD group for the challenge"
        );
    }

    // (b′) The SAME root WITHOUT the map (empty) regresses to the codex Imp2 bug:
    //     the cross-layer read takes `expected` (Ext) → init MOV mislabeled Ext.
    //     Locks in that the map is what flips the label to Base.
    #[test]
    fn mixed_cross_layer_base_read_mislabeled_ext_without_map() {
        let mut arena = ArenaBuilder::new();
        let base_read = read_layer_output(&mut arena, 0, 0);
        let chal = challenge(&mut arena, ChallengePower::One);
        let add = arena.add(vec![base_read, chal]);
        let layer = layer_of(&arena);

        // Empty map → child_operand_field falls back to `expected` = Ext.
        let instrs = run_with_map(&layer, add, HashMap::new(), OperandField::Ext);
        match &instrs[0] {
            Instr::Mov { dir: MovDir::AccFromSrc, field, .. } => {
                assert_eq!(
                    *field,
                    OperandField::Ext,
                    "without the map the cross-layer read takes the enclosing Ext (the Imp2 bug)"
                );
            }
            other => panic!("expected an init MOV AccFromSrc, got {:?}", other),
        }
    }

    // A COMPOUND cross-layer child (`base_cross_layer_read + ext_challenge` nested as
    // a factor of an enclosing product) evicts to a cell labeled by its LOCAL field
    // join (Ext), NOT the leaf's producing-sink field (Base). Guards the regression
    // surfaced by the gate: a single map lookup of the short-circuited leaf would
    // mislabel the evict Base and trip the validator's narrowing check.
    #[test]
    fn compound_cross_layer_child_evicts_as_local_join_field() {
        let mut arena = ArenaBuilder::new();
        // inner = (LayerOutput{0,0} [Base] + challenge [Ext])  → local join Ext
        let base_read = read_layer_output(&mut arena, 0, 0);
        let chal = challenge(&mut arena, ChallengePower::One);
        let inner = arena.add(vec![base_read, chal]);
        // outer = inner * another_base_read  → forces `inner` to lower into a cell
        let other = read_base(&mut arena, 5);
        let outer = arena.mul(vec![inner, other]);
        let layer = layer_of(&arena);

        let mut map = HashMap::new();
        map.insert(ReadPlace::LayerOutput { layer: 0, offset: 0 }, FieldKind::Base);

        let instrs = run_with_map(&layer, outer, map, OperandField::Ext);
        // The compound child `inner` is evicted to a cell via MOV DstFromAcc → Smem.
        // That evict MUST be labeled Ext (the local join), not Base.
        let evict = instrs.iter().find(|i| {
            matches!(i, Instr::Mov { dir: MovDir::DstFromAcc, dst: Some(DstLine::Smem { .. }), .. })
        });
        match evict {
            Some(Instr::Mov { field, .. }) => assert_eq!(
                *field,
                OperandField::Ext,
                "compound cross-layer child must evict as its local join field Ext"
            ),
            _ => panic!("expected an evict MOV DstFromAcc → Smem for the compound child"),
        }
    }

    // ── Task 5: standalone negate of a mixed base×ext product runs in the base phase
    //
    // `(-1)·(w_base · c_ext)` is a standalone product (NOT an addend of a sum).
    // The unary `MUL [Special(NegOne)]` must be emitted BEFORE the ext-promoting MUL
    // — i.e. while the acc is still base-width — because `compile_reduction` now
    // inserts the negate between the base-field groups and the ext-field groups.
    // If the negate ran AFTER the ext MUL (the old trailing position), `n > e`.
    #[test]
    fn standalone_negate_runs_in_base_phase() {
        let mut arena = ArenaBuilder::new();
        let w = read_base(&mut arena, 0);
        let cx = challenge(&mut arena, ChallengePower::One); // ext
        let neg1 = arena.intern_source(SourceKind::Constant { value: BABYBEAR_NEG_ONE });
        let neg1e = arena.source_expr(neg1);
        let prod = arena.mul(vec![neg1e, w, cx]);
        let layer = layer_of(&arena);
        let instrs = run(&layer, prod);
        // Find the negate position and the ext MUL position; negate must come first (base phase).
        let neg_pos = instrs.iter().position(|i| matches!(i,
            Instr::Mul { operands, .. } if operands.len()==1
                && matches!(operands[0], OperandLine::Ldc { sub: LdcSub::Special, idx } if idx == Special::NegOne as u16)));
        let ext_mul_pos = instrs.iter().position(|i| matches!(i, Instr::Mul { field: OperandField::Ext, .. }));
        if let (Some(n), Some(e)) = (neg_pos, ext_mul_pos) {
            assert!(n < e, "negate (idx {n}) must precede the ext MUL (idx {e}) — base-as-long-as-possible: {instrs:?}");
        } else {
            panic!("expected both a unary negate and an ext MUL: {instrs:?}");
        }
    }

    // ── #7: negated product addend folds into a Sign::Minus FMA pair ───────────
    #[test]
    fn negated_product_addend_folds_into_minus_fma() {
        let mut arena = ArenaBuilder::new();
        let w = read_base(&mut arena, 0);
        let a = read_base(&mut arena, 1);
        let bx = challenge(&mut arena, ChallengePower::One); // ext
        let neg1 = arena.intern_source(SourceKind::Constant { value: BABYBEAR_NEG_ONE });
        let neg1e = arena.source_expr(neg1);
        let prod = arena.mul(vec![neg1e, a, bx]);      // (-1)·a·bx
        let add = arena.add(vec![w, prod]);            // w + (-1)·a·bx
        let layer = layer_of(&arena);
        let instrs = run(&layer, add);
        // No standalone unary negate.
        assert!(!instrs.iter().any(|i| matches!(i,
            Instr::Mul { operands, .. } if operands.len()==1
                && matches!(operands[0], OperandLine::Ldc { sub: LdcSub::Special, idx } if idx == Special::NegOne as u16))),
            "negate must be folded, not a standalone MUL lit(-1): {instrs:?}");
        // A Minus-signed FMA exists.
        assert!(instrs.iter().any(|i| matches!(i, Instr::Fma { sign: Sign::Minus, .. })),
            "expected a Sign::Minus FMA: {instrs:?}");
    }

    // ── #7: negated non-product addend folds into a Sign::Minus ADD group ──────
    #[test]
    fn negated_value_addend_folds_into_minus_add() {
        let mut arena = ArenaBuilder::new();
        let w = read_base(&mut arena, 0);
        let a = read_base(&mut arena, 1);
        let neg1 = arena.intern_source(SourceKind::Constant { value: BABYBEAR_NEG_ONE });
        let neg1e = arena.source_expr(neg1);
        let nega = arena.mul(vec![neg1e, a]);   // (-1)·a — single surviving factor, NOT a binary product
        let add = arena.add(vec![w, nega]);     // w + (-1)·a
        let layer = layer_of(&arena);
        let instrs = run(&layer, add);
        assert!(!instrs.iter().any(|i| matches!(i,
            Instr::Mul { operands, .. } if operands.len()==1
                && matches!(operands[0], OperandLine::Ldc { sub: LdcSub::Special, idx } if idx == Special::NegOne as u16))),
            "no standalone negate for a negated addend: {instrs:?}");
        assert!(instrs.iter().any(|i| matches!(i, Instr::Add { sign: Sign::Minus, .. })),
            "expected a Sign::Minus ADD group: {instrs:?}");
    }

    // ── #7 (codex review): when EVERY additive term is negated there is no Plus seed,
    // and `MOV AccFromSrc` cannot negate — the seed sign must be compensated with a
    // standalone unary negate right after the init, else the seed term loses its sign.

    /// Helper: a standalone unary negate `MUL [Special(NegOne)]` is present.
    fn has_standalone_negate(instrs: &[Instr]) -> bool {
        instrs.iter().any(|i| matches!(i,
            Instr::Mul { operands, .. } if operands.len() == 1
                && matches!(operands[0], OperandLine::Ldc { sub: LdcSub::Special, idx } if idx == Special::NegOne as u16)))
    }

    #[test]
    fn all_negated_additive_seed_compensated() {
        // Add([(-1)·a, (-1)·b]) → value -a-b. Pure additive (no product) routes through
        // compile_reduction; the Minus seed `a` must be negated, then `b` folds as ADD Minus.
        let mut arena = ArenaBuilder::new();
        let a = read_base(&mut arena, 0);
        let b = read_base(&mut arena, 1);
        let neg1 = arena.intern_source(SourceKind::Constant { value: BABYBEAR_NEG_ONE });
        let neg1e = arena.source_expr(neg1);
        let nega = arena.mul(vec![neg1e, a]); // (-1)·a
        let negb = arena.mul(vec![neg1e, b]); // (-1)·b
        let add = arena.add(vec![nega, negb]);
        let layer = layer_of(&arena);
        let instrs = run(&layer, add);
        assert!(has_standalone_negate(&instrs),
            "all-negated additive seed must be compensated with a unary negate (else acc = a, not -a): {instrs:?}");
        assert!(instrs.iter().any(|i| matches!(i, Instr::Add { sign: Sign::Minus, .. })),
            "the remaining negated addend folds as a Sign::Minus ADD: {instrs:?}");
    }

    #[test]
    fn sole_negated_addend_compensated() {
        // Add([(-1)·a]) → value -a. Single negated term: the seed-only path must still
        // emit the compensating unary negate after the init MOV.
        let mut arena = ArenaBuilder::new();
        let a = read_base(&mut arena, 0);
        let neg1 = arena.intern_source(SourceKind::Constant { value: BABYBEAR_NEG_ONE });
        let neg1e = arena.source_expr(neg1);
        let nega = arena.mul(vec![neg1e, a]); // (-1)·a
        let add = arena.add(vec![nega]);
        let layer = layer_of(&arena);
        let instrs = run(&layer, add);
        assert!(has_standalone_negate(&instrs),
            "a sole negated additive term must be negated, not seeded as +a: {instrs:?}");
    }

    #[test]
    fn negated_addend_with_product_compensates_seed() {
        // Add([(-1)·a, b·cx]) → value -a + b·cx. The FMA path seeds from the only addend
        // `a` (Minus, no Plus addend); it must be negated, then the product folds as a Plus FMA.
        let mut arena = ArenaBuilder::new();
        let a = read_base(&mut arena, 0);
        let b = read_base(&mut arena, 1);
        let cx = challenge(&mut arena, ChallengePower::One); // ext
        let neg1 = arena.intern_source(SourceKind::Constant { value: BABYBEAR_NEG_ONE });
        let neg1e = arena.source_expr(neg1);
        let nega = arena.mul(vec![neg1e, a]); // (-1)·a  (single surviving factor → addend)
        let prod = arena.mul(vec![b, cx]);    // b·cx    (binary product)
        let add = arena.add(vec![nega, prod]);
        let layer = layer_of(&arena);
        let instrs = run(&layer, add);
        assert!(has_standalone_negate(&instrs),
            "the negated addend seed must be compensated (else acc = a + b·cx): {instrs:?}");
        assert!(instrs.iter().any(|i| matches!(i, Instr::Fma { sign: Sign::Plus, .. })),
            "the positive product folds as a Sign::Plus FMA: {instrs:?}");
    }

    #[test]
    fn all_negated_products_compensate_seed() {
        // Add([(-1)·(a·cx), (-1)·(b·cx)]) → value -(a·cx) - (b·cx). No addends: the
        // all-products seed is a Minus product; it must be negated after MOV+MUL.
        let mut arena = ArenaBuilder::new();
        let a = read_base(&mut arena, 0);
        let b = read_base(&mut arena, 1);
        let cx = challenge(&mut arena, ChallengePower::One); // ext
        let neg1 = arena.intern_source(SourceKind::Constant { value: BABYBEAR_NEG_ONE });
        let neg1e = arena.source_expr(neg1);
        let p1 = arena.mul(vec![neg1e, a, cx]); // (-1)·a·cx  (negated binary product)
        let p2 = arena.mul(vec![neg1e, b, cx]); // (-1)·b·cx  (negated binary product)
        let add = arena.add(vec![p1, p2]);
        let layer = layer_of(&arena);
        let instrs = run(&layer, add);
        assert!(has_standalone_negate(&instrs),
            "the all-negated all-products seed must be compensated (else acc = +a·cx ...): {instrs:?}");
    }
}
