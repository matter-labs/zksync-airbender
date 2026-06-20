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
    expr_field, Expr, ExprId, FieldKind, SourceKind,
};

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

/// The operand field of a child expression for instruction-field selection.
///
/// SP1 convention: `expr_field` returns `Err(ReadPlace)` for a prior-layer
/// `Read{LayerOutput|CacheOutput}` (and any expr built only from such reads)
/// because that field lives in a *prior* layer's sinks, which `compile_layer` does
/// not thread. The interpreter resolves every operand to `Ext` and IGNORES the
/// field bit for value computation, so a mislabel here does NOT affect SP1 parity.
///
/// On `Err` we fall back to `expected` — the enclosing root's result/sink field
/// (Task 13). This matters when an ENTIRE root expr is cross-layer (so `expr_field`
/// is `Err` for every node): the lowered acc would otherwise stay Base-labeled and
/// the validator's field-transition tracker would reject the final Ext materialize.
/// The result field of a fully-cross-layer root equals its sink field, so labeling
/// those reads with the sink field is exactly correct, not just convenient. Where
/// the field IS known (`Ok`), `expected` is ignored.
fn child_operand_field(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    id: ExprId,
    expected: OperandField,
) -> OperandField {
    match expr_field(&layer.exprs, &layer.sources, id, &layer.roots, &layer.sinks) {
        Ok(f) => to_operand_field(f),
        Err(_) => expected, // SP1 cross-layer convention: take the enclosing result field
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
            // Strength-reduction: recognize the field value −1 (= P−1) and emit
            // Special(NegOne). This is used by the interpreter and as a sentinel
            // when resolving operand lines (spec §6, Task 10).
            if *value == BABYBEAR_NEG_ONE {
                return Ok(OperandLine::Ldc {
                    sub: LdcSub::Special,
                    idx: Special::NegOne as u16,
                });
            }
            let idx = ctx.consts.intern(*value);
            Ok(OperandLine::Ldc {
                sub: LdcSub::Const,
                idx,
            })
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
        let field = child_operand_field(layer, expr_id, expected);
        emit_init_field(out, OperandLine::Special { desc }, field);
        return Ok(());
    }

    match &layer.exprs[expr_id.0 as usize] {
        Expr::Source(_) => {
            let field = child_operand_field(layer, expr_id, expected);
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
    if matches!(
        resolve_or_descend(layer, expr_id, &mut ctx.specials),
        ResolveOutcome::Special(_)
    ) || matches!(&layer.exprs[expr_id.0 as usize], Expr::Source(_))
    {
        let op = source_to_operand(layer, expr_id, ctx, trace)?;
        return Ok((op, None));
    }

    // Compound child: recursively lower into the acc, then evict to a fresh cell.
    // The child's evict width follows its own field (cross-layer `Err` → `expected`).
    let field = child_operand_field(layer, expr_id, expected);
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
    // §5: empty Add is a NOP (+0) — emit nothing.
    if children.is_empty() {
        return Ok(());
    }

    // H6: an Add whose children are ALL products lowers to an FMA stream.
    if children.len() >= 1 && children.iter().all(|&c| is_mul(layer, c)) {
        // Special-case the α-fold: first term is a bare column (single unscaled
        // factor) — but that surfaces as a non-Mul child, handled below, not here.
        if let Some(()) = try_compile_fma(layer, &children, ctx, trace, out, alloc, expected)? {
            return Ok(());
        }
    }

    // α-fold: first child a single unscaled column, the rest col×challenge products.
    if let Some(()) = try_compile_alpha_fold(layer, &children, ctx, trace, out, alloc, expected)? {
        return Ok(());
    }

    // Generic additive reduction grouped by operand field.
    compile_reduction(layer, &children, ctx, trace, out, /* is_add */ true, alloc, expected)
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
        // All factors were −1; the product is just ±1 as a negate or identity.
        // In practice dag_ir never produces a pure product of −1s without other
        // factors; emit a unary negate if odd count, otherwise NOP.
        if negate {
            emit_unary_negate(out);
        }
        return Ok(());
    }

    // Route surviving (non-`−1`) factors through Task 9's field-homogeneous
    // reduction: `compile_reduction` resolves each ExprId, classifies it as Base
    // or Ext via `child_operand_field`, and emits separate `Instr::Mul{field:Base}`
    // and `Instr::Mul{field:Ext}` groups (§5). This is the proven Task 9 path.
    compile_reduction(layer, &surviving, ctx, trace, out, /* is_add */ false, alloc, expected)?;

    // If sign was flipped by an odd number of −1 factors, apply a unary negate.
    if negate {
        emit_unary_negate(out);
    }

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
fn compile_reduction(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    children: &[ExprId],
    ctx: &mut DagForwardContext,
    trace: &mut CompileTrace,
    out: &mut Vec<Instr>,
    is_add: bool,
    alloc: &mut CellAllocator,
    expected: OperandField,
) -> Result<(), CompileError> {
    debug_assert!(!children.is_empty());

    // Pre-materialize EVERY child to an `OperandLine` BEFORE touching the acc:
    // a compound child is lowered into a fresh smem cell (general §11 fallback),
    // and that lowering clobbers the acc — so all operands must be resolved up
    // front. A source/resolution-pruned child resolves directly (no cell). Cells
    // are freed after the reduction's last fold reads them.
    let mut ops: Vec<(OperandField, OperandLine)> = Vec::with_capacity(children.len());
    let mut owned_cells: Vec<u16> = Vec::new();
    for &c in children {
        let field = child_operand_field(layer, c, expected);
        let (op, cell) = lower_operand(layer, c, ctx, trace, out, alloc, expected)?;
        if let Some(cell) = cell {
            owned_cells.push(cell);
        }
        ops.push((field, op));
    }

    // init from child0, labeling the acc field with child0's actual field so the
    // validator's field-transition tracker agrees with the materialize at the end
    // (§5/§12). A later mixed op still promotes Base→Ext as needed.
    emit_init_field(out, ops[0].1, ops[0].0);

    if ops.len() == 1 {
        free_all(alloc, &owned_cells);
        return Ok(()); // unary → just the MOV
    }

    // Partition the remaining children into Base and Ext operand groups.
    let mut base_ops: Vec<OperandLine> = Vec::new();
    let mut ext_ops: Vec<OperandLine> = Vec::new();
    for &(field, op) in &ops[1..] {
        match field {
            OperandField::Base => base_ops.push(op),
            OperandField::Ext => ext_ops.push(op),
        }
    }

    // Emit the Base group first (base-as-long-as-possible, §5), then the Ext group.
    // Each group is a single ADD/MUL when it fits the arity cap (the proven Tasks
    // 9/10 path); an over-long group is split into ≤MAX_ARITY chunks combined via
    // the evict-to-cell primitive (§11) so `encode` never sees an over-cap arity.
    for (field, group) in [
        (OperandField::Base, base_ops),
        (OperandField::Ext, ext_ops),
    ] {
        if group.is_empty() {
            continue;
        }
        emit_reduction_group(out, trace, field, group, is_add, alloc)?;
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
    alloc: &mut CellAllocator,
) -> Result<(), CompileError> {
    if ops.len() <= MAX_ARITY {
        // Unsplit fast path — identical to the prior Tasks 9/10 emission.
        push_fold(out, field, ops, is_add);
        return Ok(());
    }

    // Over-cap: split into chunks bounded by the arity cap. The evict cell holds the
    // running partial between chunks; its width follows the group field (Ext → 4).
    // The evict cell is drawn from the SHARED allocator so it never collides with a
    // cell still holding a lowered compound operand of this very reduction (§11).
    let sizes = split_reduction(ops.len(), /* budget */ 4);
    let mut idx = 0usize;
    let mut chunks = sizes.into_iter();

    // chunk0 folds into the acc, which already holds the reduction's running value.
    let first = chunks.next().expect("split_reduction yields >=1 chunk for arity>0");
    push_fold(out, field, ops[idx..idx + first].to_vec(), is_add);
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
            push_fold(out, field, chunk[1..].to_vec(), is_add);
        }
        // Fold the evicted partial back in (ADD/MUL referencing the cell).
        push_fold(out, field, vec![OperandLine::Smem { cell }], is_add);
        alloc.free(cell);
    }

    trace.max_live_cells = trace.max_live_cells.max(alloc.max_live());
    Ok(())
}

/// Emit a single field-homogeneous fold of `ops` into the acc: ADD (sign +) when
/// `is_add`, else MUL. Caller guarantees `ops.len() <= MAX_ARITY` and non-empty.
fn push_fold(out: &mut Vec<Instr>, field: OperandField, ops: Vec<OperandLine>, is_add: bool) {
    if is_add {
        out.push(Instr::Add {
            field,
            sign: Sign::Plus,
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

/// Lower an Add-of-products to `MOV lhs0; MUL rhs0; FMA[remaining pairs grouped by
/// (lhs_field, rhs_field)]` (§6, H6). Returns `Ok(Some(()))` if it applied,
/// `Ok(None)` if any product is not a clean binary `(lhs, rhs)` pair (caller falls
/// back to the generic reduction).
fn try_compile_fma(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    children: &[ExprId],
    ctx: &mut DagForwardContext,
    trace: &mut CompileTrace,
    out: &mut Vec<Instr>,
    alloc: &mut CellAllocator,
    expected: OperandField,
) -> Result<Option<()>, CompileError> {
    // Each child must be a binary product `Mul([f0, f1])` after `1`-elision.
    let mut pairs: Vec<(ExprId, ExprId)> = Vec::with_capacity(children.len());
    for &c in children {
        let Some(factors) = binary_mul_factors(layer, c) else {
            return Ok(None);
        };
        pairs.push(factors);
    }

    // Pre-materialize EVERY factor's operand BEFORE touching the acc (a compound
    // factor — e.g. a product-of-sums — lowers to a cell, which clobbers the acc).
    // Capture each factor's field + operand line; collect the field labels first so
    // the immutable `layer` borrow in `child_operand_field` does not overlap the
    // `&mut ctx` borrow in `lower_operand`.
    let mut lo: Vec<(OperandField, OperandLine, OperandField, OperandLine)> =
        Vec::with_capacity(pairs.len());
    let mut owned_cells: Vec<u16> = Vec::new();
    for &(lhs, rhs) in &pairs {
        let lf = child_operand_field(layer, lhs, expected);
        let rf = child_operand_field(layer, rhs, expected);
        let (lhs_op, lc) = lower_operand(layer, lhs, ctx, trace, out, alloc, lf)?;
        if let Some(c) = lc {
            owned_cells.push(c);
        }
        let (rhs_op, rc) = lower_operand(layer, rhs, ctx, trace, out, alloc, rf)?;
        if let Some(c) = rc {
            owned_cells.push(c);
        }
        lo.push((lf, lhs_op, rf, rhs_op));
    }

    // Init from the first product: MOV lhs0 (labeled with lhs0's field); MUL rhs0.
    let (lf0, lhs0_op, rf0, rhs0_op) = lo[0];
    emit_init_field(out, lhs0_op, lf0);
    out.push(Instr::Mul {
        field: rf0,
        operands: vec![rhs0_op],
    });

    if lo.len() == 1 {
        free_all(alloc, &owned_cells);
        return Ok(Some(()));
    }

    // Group the remaining (lhs, rhs) pairs by canonical (lhs_field, rhs_field).
    // Canonical mixed order is (Base, Ext): swap the commutative factors so EB is
    // never emitted (H5). Emit one FMA per field-pair group.
    use std::collections::BTreeMap;
    let mut groups: BTreeMap<(u8, u8), Vec<(OperandLine, OperandLine)>> = BTreeMap::new();
    for &(lf, lhs_op, rf, rhs_op) in &lo[1..] {
        let ((cf_l, cf_r), (op_l, op_r)) =
            canonical_fma_pair(lf, rf, lhs_op, rhs_op);
        groups
            .entry((cf_l as u8, cf_r as u8))
            .or_default()
            .push((op_l, op_r));
    }

    for ((lf, rf), gpairs) in groups {
        out.push(Instr::Fma {
            field_lhs: field_from_u8(lf),
            field_rhs: field_from_u8(rf),
            sign: Sign::Plus,
            pairs: gpairs,
        });
    }
    free_all(alloc, &owned_cells);
    Ok(Some(()))
}

/// The lookup α-fold special case: first child a single unscaled column,
/// remaining children `col×challenge` products. Lowers to
/// `MOV col0; FMA{Base,Ext}[(col1,α1),…]` (§6 worked example).
/// Returns `Ok(Some(()))` if it applied.
fn try_compile_alpha_fold(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    children: &[ExprId],
    ctx: &mut DagForwardContext,
    trace: &mut CompileTrace,
    out: &mut Vec<Instr>,
    alloc: &mut CellAllocator,
    expected: OperandField,
) -> Result<Option<()>, CompileError> {
    if children.len() < 2 {
        return Ok(None);
    }
    // child0 must be a bare source (the unscaled α⁰=1 column), NOT a product.
    if !matches!(&layer.exprs[children[0].0 as usize], Expr::Source(_)) {
        return Ok(None);
    }
    // every remaining child must be a binary product.
    let mut pairs: Vec<(ExprId, ExprId)> = Vec::with_capacity(children.len() - 1);
    for &c in &children[1..] {
        let Some(factors) = binary_mul_factors(layer, c) else {
            return Ok(None);
        };
        pairs.push(factors);
    }

    // Pre-materialize child0 + every (col, α) factor before initing the acc (a
    // compound factor lowers to a cell and clobbers the acc).
    let col0_field = child_operand_field(layer, children[0], expected);
    let (col0_op, col0_cell) =
        lower_operand(layer, children[0], ctx, trace, out, alloc, col0_field)?;
    let mut owned_cells: Vec<u16> = Vec::new();
    if let Some(c) = col0_cell {
        owned_cells.push(c);
    }
    let mut lo: Vec<(OperandField, OperandLine, OperandField, OperandLine)> =
        Vec::with_capacity(pairs.len());
    for &(lhs, rhs) in &pairs {
        let lf = child_operand_field(layer, lhs, expected);
        let rf = child_operand_field(layer, rhs, expected);
        let (lhs_op, lc) = lower_operand(layer, lhs, ctx, trace, out, alloc, lf)?;
        if let Some(c) = lc {
            owned_cells.push(c);
        }
        let (rhs_op, rc) = lower_operand(layer, rhs, ctx, trace, out, alloc, rf)?;
        if let Some(c) = rc {
            owned_cells.push(c);
        }
        lo.push((lf, lhs_op, rf, rhs_op));
    }

    // init MOV col0 (the α⁰=1 column), labeling with col0's field so the acc field
    // tracks correctly when col0 is a cross-layer Ext read.
    emit_init_field(out, col0_op, col0_field);

    // group the remaining (col, α) pairs by canonical (lhs_field, rhs_field).
    use std::collections::BTreeMap;
    let mut groups: BTreeMap<(u8, u8), Vec<(OperandLine, OperandLine)>> = BTreeMap::new();
    for &(lf, lhs_op, rf, rhs_op) in &lo {
        let ((cf_l, cf_r), (op_l, op_r)) = canonical_fma_pair(lf, rf, lhs_op, rhs_op);
        groups
            .entry((cf_l as u8, cf_r as u8))
            .or_default()
            .push((op_l, op_r));
    }
    for ((lf, rf), gpairs) in groups {
        out.push(Instr::Fma {
            field_lhs: field_from_u8(lf),
            field_rhs: field_from_u8(rf),
            sign: Sign::Plus,
            pairs: gpairs,
        });
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

// ── small structural predicates ──────────────────────────────────────────────────

fn is_mul(layer: &cs::gkr_compiler::dag_ir::DagLayer, id: ExprId) -> bool {
    matches!(&layer.exprs[id.0 as usize], Expr::Mul(_))
}

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

/// `Some((f0, f1))` if `id` is a `Mul` that, after eliding `Constant{1}` factors,
/// has exactly two factors. `None` otherwise (the FMA path bails to the generic
/// reduction so we never invent FMA pairs for non-binary products).
fn binary_mul_factors(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    id: ExprId,
) -> Option<(ExprId, ExprId)> {
    let Expr::Mul(factors) = &layer.exprs[id.0 as usize] else {
        return None;
    };
    let kept: Vec<ExprId> = factors
        .iter()
        .copied()
        .filter(|&f| !is_constant_one(layer, f))
        .collect();
    if kept.len() == 2 {
        Some((kept[0], kept[1]))
    } else {
        None
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

// ── Tests ────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fwd::context::{CompileTrace, DagForwardContext};
    use crate::fwd::isa::{Instr, LdcSub, MovDir, OperandField, OperandLine, Sign};
    use cs::gkr_compiler::dag_ir::{
        ArenaBuilder, BatchingOrder, ChallengeKey, ChallengePower, ChallengeRef, DagLayer, ExprId,
        ReadPlace, SourceKind,
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

    // ── Mul(−1, base_col, challenge) → [Mov base_col, Mul{Ext} [challenge],
    //    Mul{Base} [Special(NegOne)]] — negate + field grouping combined ─────────
    //
    // Regression: negate canonicalization must strip the −1 factor BEFORE routing
    // through compile_reduction so field grouping still applies to survivors.
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
        // Expected: MOV Base col, MUL{Ext} challenge, then unary negate MUL{Base}[NegOne].
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
                Instr::Mul {
                    field: OperandField::Base,
                    operands: vec![OperandLine::Ldc {
                        sub: LdcSub::Special,
                        idx: Special::NegOne as u16,
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
}
