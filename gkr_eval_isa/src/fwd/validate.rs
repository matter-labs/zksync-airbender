//! Backend validation pass (spec §12). Independent re-check of a `CompiledLayer`'s
//! invariants. Called after `compile_layer` succeeds; also useful as a standalone
//! correctness oracle over hand-built programs.

use super::context::{CompiledLayer, CompileTrace, DagForwardContext, ForwardAction, RootOutput};
use super::encode::encode;
use super::error::CompileError;
use super::isa::{DstLine, Instr, LdcSub, MovDir, OperandField, OperandLine, Program, Special};
use cs::gkr_compiler::dag_ir::{DagLayer, Expr, ExprId, Root, SourceKind};

// ── Check 1: coverage re-walk ─────────────────────────────────────────────────

/// Re-walk each `Compute` root's expr applying the §9 prune rule (stop at
/// `resolutions` entries). Any `LookupValue` leaf REACHED (not pruned by an
/// ancestor resolution) that is not itself single-column-resolvable → error.
fn check_coverage(compiled: &CompiledLayer, layer: &DagLayer) -> Result<(), CompileError> {
    for (rid, action) in &compiled.ctx.actions {
        if *action != ForwardAction::Compute {
            continue;
        }
        let root_idx = rid.0 as usize;
        // A Compute action only ever attaches to a materialize-bearing root.
        let expr_id = match layer.roots.get(root_idx) {
            Some(root) if root.materialize.is_some() => root.expr,
            _ => continue,
        };
        walk_coverage(layer, expr_id)?;
    }
    Ok(())
}

/// Recursive coverage walk with §9 prune: if `id` appears in `resolutions`, stop.
fn walk_coverage(layer: &DagLayer, id: ExprId) -> Result<(), CompileError> {
    // §9 prune: resolution at this expr → stop (entire subtree is covered).
    if layer.resolutions.contains_key(&id) {
        return Ok(());
    }
    let expr = layer.exprs.get(id.0 as usize).ok_or(CompileError::UncoveredLookupLeaf(id.0))?;
    match expr {
        Expr::Source(src_id) => {
            let src = layer
                .sources
                .get(src_id.0 as usize)
                .ok_or(CompileError::UncoveredLookupLeaf(id.0))?;
            // A LookupValue leaf reached without a covering resolution → error.
            if let SourceKind::LookupValue { .. } = &src.kind {
                // Single-column coverage: the expr itself has a resolution at id.
                // Since we already checked `resolutions.contains_key(&id)` above
                // and it was absent, this leaf is not covered.
                return Err(CompileError::UncoveredLookupLeaf(id.0));
            }
            Ok(())
        }
        Expr::Add(children) | Expr::Mul(children) => {
            for &child in children {
                walk_coverage(layer, child)?;
            }
            Ok(())
        }
    }
}

// ── Check 2: output action completeness ──────────────────────────────────────

/// Every materialize-bearing (forward-emitted) root has exactly one action in
/// `compiled.ctx.actions`.
fn check_action_completeness(compiled: &CompiledLayer, layer: &DagLayer) -> Result<(), CompileError> {
    for (idx, root) in layer.roots.iter().enumerate() {
        if root.materialize.is_none() {
            continue;
        }
        let rid = cs::gkr_compiler::dag_ir::RootId(idx as u32);
        if !compiled.ctx.actions.contains_key(&rid) {
            return Err(CompileError::OutputUnresolved(rid));
        }
    }
    Ok(())
}

// ── Check 3: field-transition internal consistency ────────────────────────────

/// Track the acc field by replaying the program's OWN field bits (§5 join).
/// IMPORTANT: this is an INTERNAL CONSISTENCY CHECK on the emitted instruction
/// stream — it does NOT re-derive fields from dag_ir. The compiler uses
/// `field=Base` for cross-layer reads (LayerOutput/CacheOutput) by convention;
/// re-deriving from dag_ir would spuriously reject valid programs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AccField { Base, Ext, Uninit }

fn operand_field_to_acc(f: OperandField) -> AccField {
    match f { OperandField::Base => AccField::Base, OperandField::Ext => AccField::Ext }
}

fn check_field_transitions(compiled: &CompiledLayer) -> Result<(), CompileError> {
    let mut acc = AccField::Uninit;

    for instr in &compiled.program.instrs {
        match instr {
            Instr::Mov { dir, field, dst, .. } => {
                match dir {
                    MovDir::AccFromSrc => {
                        // Load into acc — sets acc domain from the MOV field bit (§1.1).
                        acc = operand_field_to_acc(*field);
                    }
                    MovDir::DstFromAcc => {
                        // Materialize acc → dst. dst field must match acc; a Base
                        // store of an ext acc is the §1.4 implicit-truncation error
                        // specifically.
                        let dst_field = *field;
                        if dst_field == OperandField::Base && acc == AccField::Ext {
                            return Err(CompileError::AccTruncation);
                        }
                        let expected_acc = operand_field_to_acc(dst_field);
                        if acc != AccField::Uninit && acc != expected_acc {
                            return Err(CompileError::FieldMismatch(format!(
                                "DstFromAcc: acc={:?} but dst field={:?}",
                                acc, dst_field
                            )));
                        }
                        // acc doesn't change on a store.
                    }
                    MovDir::DstFromSrc => {
                        // Direct memory copy — field must be self-consistent.
                        // Does not affect acc.
                        let _ = dst;
                        // No acc state change needed — direct src→dst move.
                    }
                }
            }
            Instr::Add { field, promote, .. } => {
                // §1.3: Add{Ext} requires an ext acc; Add{Base} never does.
                acc = step_acc_domain_strict(acc, *field == OperandField::Ext, *promote)?;
            }
            Instr::Mul { field, promote, operands, .. } => {
                // §1.3: Mul{Base} dispatches on the acc domain (bf mul vs
                // 4-limb scale) — it never REQUIRES ext. Zero-arity Mul is
                // pure acc negation, typed by the acc domain: no requirement
                // regardless of the field bit. Only Mul{Ext} with operands
                // requires an ext acc.
                let requires_ext = *field == OperandField::Ext && !operands.is_empty();
                acc = step_acc_domain_strict(acc, requires_ext, *promote)?;
            }
            Instr::Fma { field_lhs, field_rhs, promote, .. } => {
                // EB order is non-canonical — reject structurally (check 7 also
                // catches this, but assert here as well for field-consistency).
                if *field_lhs == OperandField::Ext && *field_rhs == OperandField::Base {
                    return Err(CompileError::FieldMismatch(
                        "FMA in non-canonical EB order".to_string(),
                    ));
                }
                // §1.3: Fma{B,B} never requires ext; Fma{B,E} and Fma{E,E} do
                // (full e4 add of the product into acc).
                acc = step_acc_domain_strict(acc, *field_rhs == OperandField::Ext, *promote)?;
            }
        }
    }
    Ok(())
}

/// Strict v2 acc-domain step for one arith instruction (§1.2 promote-iff).
///
/// The tracked domain changes ONLY via `Mov AccFromSrc` (handled by the caller)
/// and a valid `promote` (base→ext lift). `Uninit` is treated as base for the
/// promote rules: an ext-requiring op must never execute against an
/// untracked/base acc (§1.6).
fn step_acc_domain_strict(
    acc: AccField,
    requires_ext: bool,
    promote: bool,
) -> Result<AccField, CompileError> {
    let base_domain = acc != AccField::Ext; // Base or Uninit
    if promote {
        // iff rule: promote exactly when the acc is base AND the op requires ext.
        if !(base_domain && requires_ext) {
            return Err(CompileError::PromoteNotRequired);
        }
        Ok(AccField::Ext)
    } else if requires_ext && base_domain {
        Err(CompileError::ExtAccWithoutPromote)
    } else {
        // Dispatch-only op: the acc domain is unchanged (a Base op on an ext
        // acc scales/limb-0-adds in place; the acc stays ext).
        Ok(acc)
    }
}

// ── Check 4: Smem wire-index bounds (v2 units: bf → lane, ext → bucket) ────────

/// Visit every `Smem` reference (operand AND dst) in the program with its
/// program-instruction index, wire cell index, and governing field bit (Add/Mul
/// apply `field` to every operand, Fma `field_lhs`/`field_rhs` per side, Mov
/// `field` to both src and dst). Shared by checks 4 and 8.
fn for_each_smem_ref(
    program: &Program,
    mut f: impl FnMut(usize, u16, OperandField) -> Result<(), CompileError>,
) -> Result<(), CompileError> {
    for (i, instr) in program.instrs.iter().enumerate() {
        match instr {
            Instr::Mov { dir, field, dst, src } => {
                if let MovDir::AccFromSrc | MovDir::DstFromSrc = dir {
                    if let Some(OperandLine::Smem { cell }) = src {
                        f(i, *cell, *field)?;
                    }
                }
                if let MovDir::DstFromAcc | MovDir::DstFromSrc = dir {
                    if let Some(DstLine::Smem { cell }) = dst {
                        f(i, *cell, *field)?;
                    }
                }
            }
            Instr::Add { field, operands, .. } | Instr::Mul { field, operands, .. } => {
                for op in operands {
                    if let OperandLine::Smem { cell } = op {
                        f(i, *cell, *field)?;
                    }
                }
            }
            Instr::Fma { field_lhs, field_rhs, pairs, .. } => {
                for (l, r) in pairs {
                    if let OperandLine::Smem { cell } = l {
                        f(i, *cell, *field_lhs)?;
                    }
                    if let OperandLine::Smem { cell } = r {
                        f(i, *cell, *field_rhs)?;
                    }
                }
            }
        }
    }
    Ok(())
}

/// v2 wire units (spec §3): an ext-field `Smem` index is a BUCKET index — its 4-lane
/// region `[cell*4, cell*4+4)` must fit the (bf-lane) budget — and a bf-field index
/// is a plain lane index `< budget`. Misalignment is no longer expressible on the
/// wire (any bucket index IS 4-lane-aligned by construction), so v1's `cell % 4`
/// check is gone; only bounds remain.
fn check_smem_bounds(compiled: &CompiledLayer) -> Result<(), CompileError> {
    for_each_smem_ref(&compiled.program, |_, cell, field| {
        let floor = match field {
            OperandField::Ext => cell as usize * 4 + 4,
            OperandField::Base => cell as usize + 1,
        };
        if floor > compiled.budget {
            return Err(CompileError::BudgetBelowFloor { floor, budget: compiled.budget });
        }
        Ok(())
    })
}

// ── Check 5: storage-field identity ──────────────────────────────────────────

/// A single physical Global (slot, col) appearing with conflicting field
/// assignments in one layer → error.
/// IMPORTANT: We use the field bits FROM THE INSTRUCTION STREAM, not re-derived
/// from dag_ir, to avoid spurious rejection of the cross-layer Base convention.
fn check_storage_field_identity(compiled: &CompiledLayer) -> Result<(), CompileError> {
    use std::collections::HashMap;
    // Track field seen for each (slot, col) pair.
    let mut seen: HashMap<(u8, u16), OperandField> = HashMap::new();

    let mut record = |slot: u8, col: u16, field: OperandField| -> Result<(), CompileError> {
        match seen.get(&(slot, col)) {
            None => { seen.insert((slot, col), field); Ok(()) }
            Some(&prev) if prev == field => Ok(()),
            Some(&prev) => Err(CompileError::FieldMismatch(format!(
                "Global (slot={slot}, col={col}) used as both {prev:?} and {field:?} in same layer"
            ))),
        }
    };

    // Determine the effective field for a global operand from the containing instruction.
    for instr in &compiled.program.instrs {
        match instr {
            Instr::Mov { field, src, dst, dir } => {
                match dir {
                    MovDir::AccFromSrc | MovDir::DstFromSrc => {
                        if let Some(OperandLine::Global { slot, col }) = src {
                            record(*slot, *col, *field)?;
                        }
                    }
                    _ => {}
                }
                match dir {
                    MovDir::DstFromSrc => {
                        if let Some(DstLine::GlobalMaterialize { slot, col }) = dst {
                            record(*slot, *col, *field)?;
                        }
                    }
                    MovDir::DstFromAcc => {
                        if let Some(DstLine::GlobalMaterialize { slot, col }) = dst {
                            record(*slot, *col, *field)?;
                        }
                    }
                    _ => {}
                }
            }
            Instr::Add { field, operands, .. } => {
                for op in operands {
                    if let OperandLine::Global { slot, col } = op {
                        record(*slot, *col, *field)?;
                    }
                }
            }
            Instr::Mul { field, operands, .. } => {
                for op in operands {
                    if let OperandLine::Global { slot, col } = op {
                        record(*slot, *col, *field)?;
                    }
                }
            }
            Instr::Fma { field_lhs, field_rhs, pairs, .. } => {
                for (l, r) in pairs {
                    if let OperandLine::Global { slot, col } = l {
                        record(*slot, *col, *field_lhs)?;
                    }
                    if let OperandLine::Global { slot, col } = r {
                        record(*slot, *col, *field_rhs)?;
                    }
                }
            }
        }
    }
    Ok(())
}

// ── Check 5b: field-vs-storage agreement (v2, spec §2) ───────────────────────

/// Every `Global` operand/dst field bit must match its SLOT's storage field
/// (`BackingTable::slot_field`): a slot is one homogeneous matrix, so in v2 the
/// bit controls the actual load/store width — a disagreement is a structural
/// error, not a label. Runs in BOTH acc-domain modes: the compiler already
/// emits field-correct Globals (cross-layer reads are labeled with their
/// producing sink's field via the cross-layer field map), and the slot keys are
/// derived from those same fields, so agreement holds by construction.
/// Slots absent from the table (hand-built test programs with an empty
/// `BackingTable`) are skipped — there is no storage metadata to check against.
fn check_field_storage_agreement(compiled: &CompiledLayer) -> Result<(), CompileError> {
    let backings = &compiled.ctx.backings;
    let check = |slot: u8, col: u16, field: OperandField| -> Result<(), CompileError> {
        match backings.slot_field(slot) {
            Some(sf) if sf != field => Err(CompileError::FieldStorageMismatch { slot, col }),
            _ => Ok(()),
        }
    };

    for instr in &compiled.program.instrs {
        match instr {
            Instr::Mov { field, src, dst, dir } => {
                if let MovDir::AccFromSrc | MovDir::DstFromSrc = dir {
                    if let Some(OperandLine::Global { slot, col }) = src {
                        check(*slot, *col, *field)?;
                    }
                }
                if let MovDir::DstFromAcc | MovDir::DstFromSrc = dir {
                    if let Some(DstLine::GlobalMaterialize { slot, col }) = dst {
                        check(*slot, *col, *field)?;
                    }
                }
            }
            Instr::Add { field, operands, .. } | Instr::Mul { field, operands, .. } => {
                for op in operands {
                    if let OperandLine::Global { slot, col } = op {
                        check(*slot, *col, *field)?;
                    }
                }
            }
            Instr::Fma { field_lhs, field_rhs, pairs, .. } => {
                for (l, r) in pairs {
                    if let OperandLine::Global { slot, col } = l {
                        check(*slot, *col, *field_lhs)?;
                    }
                    if let OperandLine::Global { slot, col } = r {
                        check(*slot, *col, *field_rhs)?;
                    }
                }
            }
        }
    }
    Ok(())
}

// ── Check 6: structural budget ────────────────────────────────────────────────

/// Every encoded index fits its lane: re-run `encode` and assert `Ok`. (Smem index
/// bounds against the budget are check 4's job — `check_smem_bounds` — since v2 the
/// bound is per-field: bucket vs lane.)
fn check_budget(compiled: &CompiledLayer) -> Result<(), CompileError> {
    // Re-encode the program — this also validates arity ≤ 127 and all lane widths.
    encode(&compiled.program).map_err(CompileError::Encode)?;
    Ok(())
}

// ── Check 7: canonical operands ───────────────────────────────────────────────

/// No `Special(0)`; no `EB`-order FMA. `0` is an additive identity / multiplicative
/// annihilator and must be ELIDED, never emitted as an operand. `Special(1)` (additive
/// 1) and `Special(-1)` (the negate) ARE valid arithmetic operands — encoded inline
/// instead of via the const bank. (EB-order is also caught by `encode` and check 3;
/// assert structurally.)
fn check_canonical_operands(compiled: &CompiledLayer) -> Result<(), CompileError> {
    for instr in &compiled.program.instrs {
        match instr {
            Instr::Fma { field_lhs, field_rhs, .. } => {
                if *field_lhs == OperandField::Ext && *field_rhs == OperandField::Base {
                    return Err(CompileError::FieldMismatch(
                        "FMA in non-canonical EB order".to_string(),
                    ));
                }
            }
            _ => {}
        }
        // Check all operand lines.
        for op in instr_operands(instr) {
            if let OperandLine::Ldc { sub: LdcSub::Special, idx } = op {
                if *idx == Special::Zero as u16 {
                    return Err(CompileError::FieldMismatch(
                        "Special(Zero) must be elided, not emitted as an operand".to_string(),
                    ));
                }
            }
        }
    }
    Ok(())
}

/// Collect all `OperandLine` refs from an instruction (for uniform scanning).
fn instr_operands(instr: &Instr) -> Vec<&OperandLine> {
    match instr {
        Instr::Add { operands, .. } | Instr::Mul { operands, .. } => operands.iter().collect(),
        Instr::Fma { pairs, .. } => pairs.iter().flat_map(|(l, r)| [l, r]).collect(),
        Instr::Mov { src, .. } => src.iter().collect(),
    }
}

// ── Check 8: Smem field-vs-placed-width agreement (v2, spec §3/§1.6) ──────────

/// Every `Smem` operand/dst field bit must agree with the PLACED width of the value
/// occupying that cell/bucket at that instruction: an ext-field reference to bucket
/// `b` must land on lanes the placement holds as an Ext (all 4 lanes of the bucket
/// are recorded), and a bf-field reference to lane `c` must not poke into a live Ext
/// bucket. In v2 the field bit controls the actual load/store width and region, so a
/// disagreement is a structural error, not a label. Checked against the placement
/// metadata `compile_layer` retains on `CompileTrace::placed_cell_fields`; an EMPTY
/// map (hand-built test programs with no placement) skips the check — the same
/// convention `check_field_storage_agreement` uses for slots absent from the table.
fn check_smem_region_agreement(compiled: &CompiledLayer) -> Result<(), CompileError> {
    let placed = &compiled.trace.placed_cell_fields;
    if placed.is_empty() {
        return Ok(());
    }
    for_each_smem_ref(&compiled.program, |i, cell, field| {
        match field {
            OperandField::Ext => {
                for j in 0..4 {
                    if let Some(&w) = placed.get(&(i, cell * 4 + j)) {
                        if w != OperandField::Ext {
                            return Err(CompileError::SmemRegionMismatch { cell });
                        }
                    }
                }
            }
            OperandField::Base => {
                if let Some(&w) = placed.get(&(i, cell)) {
                    if w != OperandField::Base {
                        return Err(CompileError::SmemRegionMismatch { cell });
                    }
                }
            }
        }
        Ok(())
    })
}

// ── Public entry point ────────────────────────────────────────────────────────

/// Backend validation pass (spec §12). Independently re-checks a compiled
/// layer's invariants. A successfully compiled layer MUST pass this cleanly.
/// Check 3 enforces the strict v2 acc-domain rules (promote **iff**, spec
/// §1.2–§1.4) — the ONLY acc-domain model since Task 5 flipped the compiler to
/// emit v2 (the staged `AccDomainMode::Legacy` v1-join arm is deleted).
pub fn validate_compiled(compiled: &CompiledLayer, layer: &DagLayer) -> Result<(), CompileError> {
    check_coverage(compiled, layer)?;
    check_action_completeness(compiled, layer)?;
    check_field_transitions(compiled)?;
    check_smem_bounds(compiled)?;
    check_storage_field_identity(compiled)?;
    check_field_storage_agreement(compiled)?;
    check_budget(compiled)?;
    check_canonical_operands(compiled)?;
    check_smem_region_agreement(compiled)?;
    Ok(())
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::context::{CompileTrace, DagForwardContext, ForwardAction, RootOutput, OutputCell};
    use super::super::stats::CompileStats;
    use super::super::isa::{DstLine, Instr, LdcSub, MovDir, OperandField, OperandLine, Program, Special};
    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, ClaimInfo, DagLayer, Expr, ExprId, FieldKind, ReadPlace, Root,
        RootGroup, RootId, RootOrigin, RootSlot, SinkInfo, SinkKind, SourceId, SourceInfo,
        SourceKind, LookupValueKind, ResolutionStrategy, RangeWidth,
    };
    use std::collections::BTreeMap;

    // ── layer builders ────────────────────────────────────────────────────────

    fn empty_layer() -> DagLayer {
        DagLayer {
            sources: vec![],
            exprs: vec![],
            roots: vec![],
            batching: BatchingOrder { roots: vec![] },
            resolutions: BTreeMap::new(),
        }
    }

    /// A minimal `DagLayer` with one `Output` root whose expr is a plain Source
    /// (no LookupValue), suitable as the clean base for most tests.
    fn simple_compute_layer() -> DagLayer {
        let mut layer = empty_layer();
        // Source 0: constant
        layer.sources.push(SourceInfo { kind: SourceKind::Constant { value: 42 } });
        // Expr 0: Source(0)
        layer.exprs.push(Expr::Source(SourceId(0)));
        // Root 0: claim-bearing materialized Output root.
        layer.roots.push(Root {
            expr: ExprId(0),
            materialize: Some(SinkInfo { kind: SinkKind::Export { slot: 0 }, field: FieldKind::Base }),
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index: 0,
                    slot: RootSlot::Output(0),
                },
            }),
        });
        layer
    }

    /// A `CompiledLayer` that cleanly passes all 7 checks.
    /// One `Compute` root; program = `MOV Acc←Global(0,0) ; DstFromAcc → Global(0,1)`.
    fn clean_compiled(layer: &DagLayer) -> CompiledLayer {
        let mut ctx = DagForwardContext::default();
        ctx.actions.insert(RootId(0), ForwardAction::Compute);

        let program = Program {
            instrs: vec![
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Global { slot: 0, col: 0 }),
                },
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: OperandField::Base,
                    dst: Some(DstLine::GlobalMaterialize { slot: 0, col: 1 }),
                    src: None,
                },
            ],
        };

        CompiledLayer {
            program,
            ctx,
            root_outputs: vec![(RootId(0), RootOutput::Cell(OutputCell::Global { slot: 0, col: 1 }))],
            skipped: vec![],
            trace: CompileTrace::default(),
            budget: 16,
            stats: CompileStats::default(),
            resident_realized: vec![],
        }
    }

    // ── Check 1: coverage ─────────────────────────────────────────────────────

    /// A LookupValue leaf reached without any covering resolution → UncoveredLookupLeaf.
    #[test]
    fn uncovered_lookup_leaf_rejected() {
        // Build a layer where the Output root's expr is directly a LookupValue source.
        let mut layer = empty_layer();
        layer.sources.push(SourceInfo {
            kind: SourceKind::LookupValue {
                kind: LookupValueKind::RangeCheck16Index,
                set_index: 0,
                query: ExprId(99),
            },
        });
        layer.exprs.push(Expr::Source(SourceId(0))); // ExprId(0) = LookupValue
        layer.roots.push(Root {
            expr: ExprId(0),
            materialize: Some(SinkInfo { kind: SinkKind::Export { slot: 0 }, field: FieldKind::Ext }),
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index: 0,
                    slot: RootSlot::Output(0),
                },
            }),
        });
        // No resolutions entry → leaf is uncovered.

        let compiled = {
            let mut ctx = DagForwardContext::default();
            ctx.actions.insert(RootId(0), ForwardAction::Compute);
            CompiledLayer {
                program: Program { instrs: vec![
                    Instr::Mov {
                        dir: MovDir::AccFromSrc,
                        field: OperandField::Base,
                        dst: None,
                        src: Some(OperandLine::Global { slot: 0, col: 0 }),
                    },
                ] },
                ctx,
                root_outputs: vec![],
                skipped: vec![],
                trace: CompileTrace::default(),
                budget: 16,
                stats: CompileStats::default(),
                resident_realized: vec![],
            }
        };

        let result = validate_compiled(&compiled, &layer);
        assert_eq!(result, Err(CompileError::UncoveredLookupLeaf(0)));
    }

    /// A LookupValue leaf pruned by a resolution at its parent → Ok.
    #[test]
    fn lookup_leaf_pruned_by_parent_resolution_ok() {
        let mut layer = empty_layer();
        // Source 0: LookupValue (the dangerous leaf)
        layer.sources.push(SourceInfo {
            kind: SourceKind::LookupValue {
                kind: LookupValueKind::RangeCheck16Index,
                set_index: 0,
                query: ExprId(99),
            },
        });
        // Expr 0: Source(0) — the LookupValue
        layer.exprs.push(Expr::Source(SourceId(0)));
        // Expr 1: Add([ExprId(0)]) — the parent, which carries the resolution
        layer.exprs.push(Expr::Add(vec![ExprId(0)]));
        // Resolution at ExprId(1) → prune the whole subtree
        layer.resolutions.insert(ExprId(1), ResolutionStrategy::PeekSingleColumn {
            set_index: 0,
            width: RangeWidth::Bits16,
        });
        layer.roots.push(Root {
            expr: ExprId(1),
            materialize: Some(SinkInfo { kind: SinkKind::Export { slot: 0 }, field: FieldKind::Base }),
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index: 0,
                    slot: RootSlot::Output(0),
                },
            }),
        });

        let mut ctx = DagForwardContext::default();
        ctx.actions.insert(RootId(0), ForwardAction::Compute);
        let compiled = CompiledLayer {
            program: Program { instrs: vec![
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Special { desc: 0 }),
                },
            ] },
            ctx,
            root_outputs: vec![],
            skipped: vec![],
            trace: CompileTrace::default(),
            budget: 16,
            stats: CompileStats::default(),
            resident_realized: vec![],
        };

        assert_eq!(validate_compiled(&compiled, &layer), Ok(()));
    }

    // ── Check 2: output action completeness ───────────────────────────────────

    /// An Output root with no corresponding action → OutputUnresolved.
    #[test]
    fn missing_action_rejected() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        // Remove the action for root 0 so it has no entry.
        compiled.ctx.actions.remove(&RootId(0));

        let result = validate_compiled(&compiled, &layer);
        assert_eq!(result, Err(CompileError::OutputUnresolved(RootId(0))));
    }

    // ── Check 3: field-transition internal consistency ────────────────────────

    /// Acc is Base (from MOV AccFromSrc field=Base), then DstFromAcc field=Ext → mismatch.
    #[test]
    fn field_mismatch_dst_from_acc_rejected() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        // Replace the second MOV: acc is Base but try to store as Ext.
        compiled.program.instrs[1] = Instr::Mov {
            dir: MovDir::DstFromAcc,
            field: OperandField::Ext, // mismatch: acc is Base
            dst: Some(DstLine::GlobalMaterialize { slot: 0, col: 1 }),
            src: None,
        };

        let result = validate_compiled(&compiled, &layer);
        assert!(matches!(result, Err(CompileError::FieldMismatch(_))), "got: {:?}", result);
    }

    /// Base acc + Base operand, then Base store → field consistent → Ok.
    #[test]
    fn field_consistent_base_ok() {
        let layer = simple_compute_layer();
        let compiled = clean_compiled(&layer);
        assert_eq!(validate_compiled(&compiled, &layer), Ok(()));
    }

    /// Cross-layer Base convention: a Global operand labeled field=Base even though
    /// its backing is LayerOutput/CacheOutput — the validator MUST NOT re-derive
    /// the field from dag_ir and must accept this as Ok (check 3/5 positive test).
    #[test]
    fn cross_layer_base_convention_not_spuriously_rejected() {
        // Build a layer with a LayerOutput source that the compiler annotated as Base.
        let mut layer = empty_layer();
        layer.sources.push(SourceInfo {
            kind: SourceKind::Read {
                place: ReadPlace::LayerOutput { layer: 0, offset: 0 },
            },
        });
        layer.exprs.push(Expr::Source(SourceId(0)));
        layer.roots.push(Root {
            expr: ExprId(0),
            materialize: Some(SinkInfo { kind: SinkKind::Export { slot: 0 }, field: FieldKind::Base }),
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index: 0,
                    slot: RootSlot::Output(0),
                },
            }),
        });

        let mut ctx = DagForwardContext::default();
        ctx.actions.insert(RootId(0), ForwardAction::Compute);

        // Compiler emits field=Base for the LayerOutput read (cross-layer convention).
        let program = Program {
            instrs: vec![
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base, // cross-layer Base convention
                    dst: None,
                    src: Some(OperandLine::Global { slot: 0, col: 0 }),
                },
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: OperandField::Base, // consistent with acc
                    dst: Some(DstLine::GlobalMaterialize { slot: 0, col: 1 }),
                    src: None,
                },
            ],
        };
        let compiled = CompiledLayer {
            program,
            ctx,
            root_outputs: vec![],
            skipped: vec![],
            trace: CompileTrace::default(),
            budget: 16,
            stats: CompileStats::default(),
            resident_realized: vec![],
        };

        // Must not spuriously reject due to dag_ir field re-derivation.
        assert_eq!(validate_compiled(&compiled, &layer), Ok(()));
    }

    // ── Check 4: Smem wire-index bounds (v2 units: bf → lane, ext → bucket) ───

    /// Ext-field smem index is a BUCKET index: bucket `b`'s lane region
    /// `[4b, 4b+4)` must fit the (bf-lane) budget. Misalignment is no longer
    /// expressible on the wire; out-of-bounds is the failure mode.
    #[test]
    fn ext_smem_bucket_out_of_bounds_rejected() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.budget = 16; // 4 buckets: valid ext indices are 0..=3
        compiled.program.instrs = vec![
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Ext,
                dst: None,
                src: Some(OperandLine::Smem { cell: 4 }), // bucket 4 → lanes 16..19 ✗
            },
        ];

        let result = validate_compiled(&compiled, &layer);
        assert_eq!(result, Err(CompileError::BudgetBelowFloor { floor: 20, budget: 16 }));
    }

    /// In-bounds bucket indices → Ok. At budget 32 (8 buckets), buckets 0 and 4
    /// (v1 lanes 0 and 16) both validate.
    #[test]
    fn ext_smem_bucket_indices_ok() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.budget = 32; // 8 buckets
        compiled.program.instrs = vec![
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Ext,
                dst: None,
                src: Some(OperandLine::Smem { cell: 0 }), // bucket 0 = lanes 0..3
            },
            Instr::Mov {
                dir: MovDir::DstFromAcc,
                field: OperandField::Ext,
                dst: Some(DstLine::Smem { cell: 4 }), // bucket 4 = lanes 16..19
                src: None,
            },
        ];

        assert_eq!(validate_compiled(&compiled, &layer), Ok(()));
    }

    // ── Check 5: storage-field identity ──────────────────────────────────────

    /// Same (slot, col) used as Base in one instr and Ext in another → FieldMismatch.
    #[test]
    fn conflicting_storage_field_rejected() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        // ADD reads Global(0,5) as Base, then MOV reads it as Ext — conflict.
        compiled.program.instrs = vec![
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Base,
                dst: None,
                src: Some(OperandLine::Global { slot: 0, col: 5 }),
            },
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Ext,  // same (slot=0, col=5) but Ext
                dst: None,
                src: Some(OperandLine::Global { slot: 0, col: 5 }),
            },
        ];

        let result = validate_compiled(&compiled, &layer);
        assert!(matches!(result, Err(CompileError::FieldMismatch(_))), "got: {:?}", result);
    }

    /// Same (slot, col) consistently Base in all uses → Ok.
    #[test]
    fn consistent_storage_field_ok() {
        let layer = simple_compute_layer();
        let compiled = clean_compiled(&layer); // uses (0,0) and (0,1) both Base
        assert_eq!(validate_compiled(&compiled, &layer), Ok(()));
    }

    // ── Check 6: structural budget ────────────────────────────────────────────

    /// Program references smem cell beyond budget → BudgetBelowFloor.
    #[test]
    fn over_budget_rejected() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.budget = 4; // only 4 cells
        // Smem cell 10 is way beyond budget of 4.
        compiled.program.instrs = vec![
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Base,
                dst: None,
                src: Some(OperandLine::Smem { cell: 10 }),
            },
        ];

        let result = validate_compiled(&compiled, &layer);
        assert!(matches!(result, Err(CompileError::BudgetBelowFloor { .. })), "got: {:?}", result);
    }

    /// Program with no smem refs in a budget of 16 → Ok (clean encode roundtrip).
    #[test]
    fn budget_ok_clean_encode_roundtrip() {
        let layer = simple_compute_layer();
        let compiled = clean_compiled(&layer);
        assert_eq!(validate_compiled(&compiled, &layer), Ok(()));
    }

    // ── Check 7: canonical operands ───────────────────────────────────────────

    /// `Special(0)` (Zero) as an arithmetic operand → FieldMismatch (canonical-operand error).
    #[test]
    fn special_zero_operand_rejected() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.program.instrs = vec![
            Instr::Add {
                field: OperandField::Base,
                sign: super::super::isa::Sign::Plus,
                promote: false,
                operands: vec![
                    OperandLine::Ldc { sub: LdcSub::Special, idx: Special::Zero as u16 },
                ],
            },
        ];

        let result = validate_compiled(&compiled, &layer);
        assert!(matches!(result, Err(CompileError::FieldMismatch(_))), "got: {:?}", result);
    }

    /// `Special(1)` (One) IS a valid arithmetic operand — additive 1, encoded inline
    /// instead of via the const bank (mul-by-1 is elided upstream).
    #[test]
    fn special_one_operand_ok() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.program.instrs = vec![
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Base,
                dst: None,
                src: Some(OperandLine::Global { slot: 0, col: 0 }),
            },
            Instr::Add {
                field: OperandField::Base,
                sign: super::super::isa::Sign::Plus,
                promote: false,
                operands: vec![
                    OperandLine::Ldc { sub: LdcSub::Special, idx: Special::One as u16 },
                ],
            },
            Instr::Mov {
                dir: MovDir::DstFromAcc,
                field: OperandField::Base,
                dst: Some(DstLine::GlobalMaterialize { slot: 0, col: 1 }),
                src: None,
            },
        ];

        assert_eq!(validate_compiled(&compiled, &layer), Ok(()));
    }

    /// `Special(NegOne)` (−1) as a unary MUL operand → Ok (the only valid Special).
    #[test]
    fn special_neg_one_ok() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.program.instrs = vec![
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Base,
                dst: None,
                src: Some(OperandLine::Global { slot: 0, col: 0 }),
            },
            Instr::Mul {
                field: OperandField::Base,
                promote: false,
                negate_acc: false,
                operands: vec![
                    OperandLine::Ldc { sub: LdcSub::Special, idx: Special::NegOne as u16 },
                ],
            },
            Instr::Mov {
                dir: MovDir::DstFromAcc,
                field: OperandField::Base,
                dst: Some(DstLine::GlobalMaterialize { slot: 0, col: 1 }),
                src: None,
            },
        ];

        assert_eq!(validate_compiled(&compiled, &layer), Ok(()));
    }

    /// FMA with `field_lhs=Ext, field_rhs=Base` (EB order) → FieldMismatch.
    #[test]
    fn fma_eb_order_rejected() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.program.instrs = vec![
            Instr::Fma {
                field_lhs: OperandField::Ext,  // EB = non-canonical
                field_rhs: OperandField::Base,
                sign: super::super::isa::Sign::Plus,
                promote: false,
                pairs: vec![(
                    OperandLine::Global { slot: 0, col: 0 },
                    OperandLine::Global { slot: 0, col: 1 },
                )],
            },
        ];

        let result = validate_compiled(&compiled, &layer);
        assert!(matches!(result, Err(CompileError::FieldMismatch(_))), "got: {:?}", result);
    }

    /// FMA with canonical `field_lhs=Base, field_rhs=Ext` (BE order) → Ok.
    /// `Fma{B,E}` on the (uninit ⇒ base) acc requires `promote` (§1.2 iff rule).
    #[test]
    fn fma_be_order_ok() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.budget = 16;
        compiled.program.instrs = vec![
            Instr::Fma {
                field_lhs: OperandField::Base,  // canonical BE
                field_rhs: OperandField::Ext,
                sign: super::super::isa::Sign::Plus,
                promote: true,
                pairs: vec![(
                    OperandLine::Global { slot: 0, col: 0 },
                    OperandLine::Global { slot: 0, col: 1 },
                )],
            },
        ];

        assert_eq!(validate_compiled(&compiled, &layer), Ok(()));
    }

    // ── Source-residency load primitive ──────────────────────────────────────

    /// Pin test: the source-residency load primitive `MOV DstFromSrc Smem{cell}
    /// ← Global{slot,col}` (emitted by the compiler for reused hot Read sources)
    /// must be accepted by the validator.  No red phase — the validator already
    /// accepts this shape; the test locks that in so future validator changes
    /// cannot silently reject the load instruction.
    #[test]
    fn validate_accepts_dstfromsrc_into_smem() {
        // The source-residency load-once primitive: MOV DstFromSrc Smem{0} <- Global{0,0}.
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        // Prepend the load into the passing program (Base field needs no cell alignment).
        // Global(0,0) is already read as Base in clean_compiled — same field, no conflict.
        compiled.program.instrs.insert(0, Instr::Mov {
            dir: MovDir::DstFromSrc,
            field: OperandField::Base,
            dst: Some(DstLine::Smem { cell: 0 }),
            src: Some(OperandLine::Global { slot: 0, col: 0 }),
        });
        assert!(validate_compiled(&compiled, &layer).is_ok(),
            "DstFromSrc into a Smem cell (the source-residency load) must validate");
    }

    // ── Full clean pass ───────────────────────────────────────────────────────

    /// A fully-valid `CompiledLayer` passes all 7 checks.
    #[test]
    fn clean_layer_passes_all_checks() {
        let layer = simple_compute_layer();
        let compiled = clean_compiled(&layer);
        assert_eq!(validate_compiled(&compiled, &layer), Ok(()));
    }

    // ── Check 3 strict v2: promote-iff acc-domain rules (§1.2–§1.4) ──────────

    use super::super::isa::Sign;

    /// Helper: `MOV Acc←Global(0,0)` with the given field bit.
    fn mov_acc_from_global(field: OperandField) -> Instr {
        Instr::Mov {
            dir: MovDir::AccFromSrc,
            field,
            dst: None,
            src: Some(OperandLine::Global { slot: 0, col: 0 }),
        }
    }

    /// Helper: `ADD{field}` of one ConstChallenge operand (avoids storage-field
    /// identity interactions with the Global read in the MOV).
    fn add_challenge(field: OperandField, promote: bool) -> Instr {
        Instr::Add {
            field,
            sign: Sign::Plus,
            promote,
            operands: vec![OperandLine::Ldc { sub: LdcSub::ConstChallenge, idx: 0 }],
        }
    }

    /// Spurious promote: `ADD{Base, promote}` on a base acc → the op does not
    /// require an ext acc, promote violates the iff rule.
    #[test]
    fn v2_spurious_promote_on_base_op_rejected() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.program.instrs = vec![
            mov_acc_from_global(OperandField::Base),
            add_challenge(OperandField::Base, true), // promote but Add{Base} never requires ext
        ];
        assert_eq!(
            validate_compiled(&compiled, &layer),
            Err(CompileError::PromoteNotRequired)
        );
    }

    /// Promote while the tracked acc domain is already ext → PromoteNotRequired.
    #[test]
    fn v2_promote_on_ext_acc_rejected() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.program.instrs = vec![
            mov_acc_from_global(OperandField::Ext), // acc domain = ext
            add_challenge(OperandField::Ext, true), // promote on an already-ext acc
        ];
        assert_eq!(
            validate_compiled(&compiled, &layer),
            Err(CompileError::PromoteNotRequired)
        );
    }

    /// Ext-requiring op on a base acc without promote → ExtAccWithoutPromote.
    #[test]
    fn v2_ext_op_on_base_acc_without_promote_rejected() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.program.instrs = vec![
            mov_acc_from_global(OperandField::Base),
            add_challenge(OperandField::Ext, false), // Add{Ext} requires ext acc
        ];
        assert_eq!(
            validate_compiled(&compiled, &layer),
            Err(CompileError::ExtAccWithoutPromote)
        );
    }

    /// `Fma{B,E}` requires an ext acc too (§1.3) — same rejection without promote.
    #[test]
    fn v2_mixed_fma_on_base_acc_without_promote_rejected() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.program.instrs = vec![
            mov_acc_from_global(OperandField::Base),
            Instr::Fma {
                field_lhs: OperandField::Base,
                field_rhs: OperandField::Ext,
                sign: Sign::Plus,
                promote: false,
                pairs: vec![(
                    OperandLine::Global { slot: 0, col: 0 },
                    OperandLine::Ldc { sub: LdcSub::ConstChallenge, idx: 0 },
                )],
            },
        ];
        assert_eq!(
            validate_compiled(&compiled, &layer),
            Err(CompileError::ExtAccWithoutPromote)
        );
    }

    /// `Mov DstFromAcc{Base}` while the tracked acc domain is ext → AccTruncation.
    #[test]
    fn v2_base_store_of_ext_acc_rejected() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.program.instrs = vec![
            mov_acc_from_global(OperandField::Base),
            add_challenge(OperandField::Ext, true), // correct promote: acc lifts to ext
            Instr::Mov {
                dir: MovDir::DstFromAcc,
                field: OperandField::Base, // implicit truncation — illegal
                dst: Some(DstLine::GlobalMaterialize { slot: 0, col: 1 }),
                src: None,
            },
        ];
        assert_eq!(
            validate_compiled(&compiled, &layer),
            Err(CompileError::AccTruncation)
        );
    }

    /// The canonical lift program passes strict v2: base load, promote exactly
    /// at the ext-requiring op, ext store.
    #[test]
    fn v2_canonical_promote_program_ok() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.program.instrs = vec![
            mov_acc_from_global(OperandField::Base),
            add_challenge(OperandField::Ext, true),
            Instr::Mov {
                dir: MovDir::DstFromAcc,
                field: OperandField::Ext,
                dst: Some(DstLine::GlobalMaterialize { slot: 0, col: 1 }),
                src: None,
            },
        ];
        assert_eq!(validate_compiled(&compiled, &layer), Ok(()));
    }

    /// `Mul{Base}` dispatches on the acc domain and never REQUIRES ext (§1.3):
    /// legal on an ext acc (4-limb scale) without promote, and the acc stays ext.
    #[test]
    fn v2_base_mul_on_ext_acc_ok_and_keeps_domain() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.program.instrs = vec![
            mov_acc_from_global(OperandField::Ext), // acc domain = ext
            Instr::Mul {
                field: OperandField::Base, // scale — dispatches, no promote needed
                promote: false,
                negate_acc: false,
                operands: vec![OperandLine::Ldc { sub: LdcSub::Const, idx: 0 }],
            },
            Instr::Mov {
                dir: MovDir::DstFromAcc,
                field: OperandField::Ext, // acc is still ext after the scale
                dst: Some(DstLine::GlobalMaterialize { slot: 0, col: 1 }),
                src: None,
            },
        ];
        assert_eq!(validate_compiled(&compiled, &layer), Ok(()));
    }

    /// Zero-arity `Mul{negate_acc}` (pure acc negation) dispatches on the acc
    /// domain — legal on a base acc without promote, acc stays base.
    #[test]
    fn v2_zero_arity_negate_on_base_acc_ok() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.program.instrs = vec![
            mov_acc_from_global(OperandField::Base),
            Instr::Mul {
                field: OperandField::Ext, // field bit irrelevant at arity 0
                promote: false,
                negate_acc: true,
                operands: vec![],
            },
            Instr::Mov {
                dir: MovDir::DstFromAcc,
                field: OperandField::Base,
                dst: Some(DstLine::GlobalMaterialize { slot: 0, col: 1 }),
                src: None,
            },
        ];
        assert_eq!(validate_compiled(&compiled, &layer), Ok(()));
    }

    // ── Check 5b: field-vs-storage agreement (v2) ─────────────────────────────

    /// Build a `CompiledLayer` whose `BackingTable` has slot 0 = LayerOutput
    /// {layer 0, Base} with dense cols 0..2, and the given program.
    fn compiled_with_base_layer_output_slot(instrs: Vec<Instr>) -> CompiledLayer {
        use super::super::binding::BackingKey;
        let mut ctx = DagForwardContext::default();
        ctx.actions.insert(RootId(0), ForwardAction::Compute);
        for off in 0..2usize {
            ctx.backings
                .slot_col(BackingKey::LayerOutput { layer: 0, field: OperandField::Base }, off)
                .unwrap();
        }
        CompiledLayer {
            program: Program { instrs },
            ctx,
            root_outputs: vec![],
            skipped: vec![],
            trace: CompileTrace::default(),
            budget: 16,
            stats: CompileStats::default(),
            resident_realized: vec![],
        }
    }

    /// A Global read labeled Ext against a Base-field slot → FieldStorageMismatch.
    #[test]
    fn field_storage_mismatch_read_rejected() {
        let layer = simple_compute_layer();
        let compiled = compiled_with_base_layer_output_slot(vec![
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Ext, // slot 0's matrix is Base
                dst: None,
                src: Some(OperandLine::Global { slot: 0, col: 0 }),
            },
        ]);
        assert_eq!(
            validate_compiled(&compiled, &layer),
            Err(CompileError::FieldStorageMismatch { slot: 0, col: 0 })
        );
    }

    /// A GlobalMaterialize dst labeled Ext against a Base-field slot →
    /// FieldStorageMismatch (write side checked identically to reads).
    #[test]
    fn field_storage_mismatch_write_rejected() {
        let layer = simple_compute_layer();
        let compiled = compiled_with_base_layer_output_slot(vec![
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Ext,
                dst: None,
                src: Some(OperandLine::Ldc { sub: LdcSub::ConstChallenge, idx: 0 }),
            },
            Instr::Mov {
                dir: MovDir::DstFromAcc,
                field: OperandField::Ext, // consistent with acc, but slot is Base storage
                dst: Some(DstLine::GlobalMaterialize { slot: 0, col: 1 }),
                src: None,
            },
        ]);
        assert_eq!(
            validate_compiled(&compiled, &layer),
            Err(CompileError::FieldStorageMismatch { slot: 0, col: 1 })
        );
    }

    // ── Check 8 (Task 6): Smem field-vs-placed-width agreement ───────────────

    /// Record placement-width metadata on a compiled layer's trace (the Task-6
    /// retained `placed_cell_fields` map: `(program instr idx, bf lane) → width`).
    fn with_placed(
        mut compiled: CompiledLayer,
        entries: &[((usize, u16), OperandField)],
    ) -> CompiledLayer {
        for &(k, f) in entries {
            compiled.trace.placed_cell_fields.insert(k, f);
        }
        compiled
    }

    /// A bf-field `Smem` read of a lane the placement holds as (part of) a live
    /// Ext bucket → SmemRegionMismatch.
    #[test]
    fn smem_base_read_of_ext_lane_rejected() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.program.instrs = vec![Instr::Mov {
            dir: MovDir::AccFromSrc,
            field: OperandField::Base,
            dst: None,
            src: Some(OperandLine::Smem { cell: 1 }), // lane 1 = inside ext bucket 0
        }];
        let compiled = with_placed(
            compiled,
            &[
                ((0, 0), OperandField::Ext),
                ((0, 1), OperandField::Ext),
                ((0, 2), OperandField::Ext),
                ((0, 3), OperandField::Ext),
            ],
        );
        assert_eq!(
            validate_compiled(&compiled, &layer),
            Err(CompileError::SmemRegionMismatch { cell: 1 })
        );
    }

    /// An ext-field `Smem` read of a bucket whose lanes the placement holds as
    /// Base values → SmemRegionMismatch.
    #[test]
    fn smem_ext_read_of_base_lane_rejected() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.program.instrs = vec![Instr::Mov {
            dir: MovDir::AccFromSrc,
            field: OperandField::Ext,
            dst: None,
            src: Some(OperandLine::Smem { cell: 1 }), // bucket 1 = lanes 4..7
        }];
        let compiled = with_placed(compiled, &[((0, 4), OperandField::Base)]);
        assert_eq!(
            validate_compiled(&compiled, &layer),
            Err(CompileError::SmemRegionMismatch { cell: 1 })
        );
    }

    /// Field bits agreeing with the placed widths → Ok; and an EMPTY map (hand-built
    /// program, no placement metadata) skips the check entirely.
    #[test]
    fn smem_region_agreement_ok_and_empty_map_skips() {
        let layer = simple_compute_layer();

        // Agreement: ext read of an ext-placed bucket, bf read of a bf-placed lane.
        let mut compiled = clean_compiled(&layer);
        compiled.program.instrs = vec![
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Ext,
                dst: None,
                src: Some(OperandLine::Smem { cell: 0 }), // bucket 0 = lanes 0..3
            },
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Base,
                dst: None,
                src: Some(OperandLine::Smem { cell: 4 }), // bf lane 4
            },
        ];
        let compiled = with_placed(
            compiled,
            &[
                ((0, 0), OperandField::Ext),
                ((0, 1), OperandField::Ext),
                ((0, 2), OperandField::Ext),
                ((0, 3), OperandField::Ext),
                ((1, 4), OperandField::Base),
            ],
        );
        assert_eq!(validate_compiled(&compiled, &layer), Ok(()));

        // Empty map: the same "wrong" shape as smem_base_read_of_ext_lane_rejected
        // passes when there is no placement metadata to check against.
        let mut compiled = clean_compiled(&layer);
        compiled.program.instrs = vec![Instr::Mov {
            dir: MovDir::AccFromSrc,
            field: OperandField::Base,
            dst: None,
            src: Some(OperandLine::Smem { cell: 1 }),
        }];
        assert_eq!(validate_compiled(&compiled, &layer), Ok(()));
    }

    /// Field bits agreeing with the slot's storage field → Ok (both modes' walk).
    #[test]
    fn field_storage_agreement_ok() {
        let layer = simple_compute_layer();
        let compiled = compiled_with_base_layer_output_slot(vec![
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Base,
                dst: None,
                src: Some(OperandLine::Global { slot: 0, col: 0 }),
            },
            Instr::Mov {
                dir: MovDir::DstFromAcc,
                field: OperandField::Base,
                dst: Some(DstLine::GlobalMaterialize { slot: 0, col: 1 }),
                src: None,
            },
        ]);
        assert_eq!(validate_compiled(&compiled, &layer), Ok(()));
    }

}
