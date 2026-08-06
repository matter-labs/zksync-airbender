//! Backend validation pass (spec §12). Independent re-check of a `CompiledLayer`'s
//! invariants. Called after `compile_layer` succeeds; also useful as a standalone
//! correctness oracle over hand-built programs.

use super::context::{CompiledLayer, ForwardAction};
use super::encode::encode;
use super::error::CompileError;
use super::isa::{DstLine, Instr, LdcSub, MovDir, OperandField, OperandLine, Program, Special};
use gkr_eval_ir::{DagLayer, Expr, ExprId, SourceKind};

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
    let expr = layer
        .exprs
        .get(id.0 as usize)
        .ok_or(CompileError::UncoveredLookupLeaf(id.0))?;
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
fn check_action_completeness(
    compiled: &CompiledLayer,
    layer: &DagLayer,
) -> Result<(), CompileError> {
    for (idx, root) in layer.roots.iter().enumerate() {
        if root.materialize.is_none() {
            continue;
        }
        let rid = gkr_eval_ir::RootId(idx as u32);
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
enum AccField {
    Base,
    Ext,
    Uninit,
}

fn operand_field_to_acc(f: OperandField) -> AccField {
    match f {
        OperandField::Base => AccField::Base,
        OperandField::Ext => AccField::Ext,
    }
}

fn check_field_transitions(compiled: &CompiledLayer) -> Result<(), CompileError> {
    let mut acc = AccField::Uninit;

    for instr in &compiled.program.instrs {
        match instr {
            Instr::Mov {
                dir, field, dst, ..
            } => {
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
            Instr::Mul {
                field,
                promote,
                operands,
                ..
            } => {
                // §1.3: Mul{Base} dispatches on the acc domain (bf mul vs
                // 4-limb scale) — it never REQUIRES ext. Zero-arity Mul is
                // pure acc negation, typed by the acc domain: no requirement
                // regardless of the field bit. Only Mul{Ext} with operands
                // requires an ext acc.
                let requires_ext = *field == OperandField::Ext && !operands.is_empty();
                acc = step_acc_domain_strict(acc, requires_ext, *promote)?;
            }
            Instr::Fma {
                field_lhs,
                field_rhs,
                promote,
                ..
            } => {
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
            Instr::Mov {
                dir,
                field,
                dst,
                src,
            } => {
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
            Instr::Add {
                field, operands, ..
            }
            | Instr::Mul {
                field, operands, ..
            } => {
                for op in operands {
                    if let OperandLine::Smem { cell } = op {
                        f(i, *cell, *field)?;
                    }
                }
            }
            Instr::Fma {
                field_lhs,
                field_rhs,
                pairs,
                ..
            } => {
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
        if floor > compiled.budget_lanes {
            return Err(CompileError::BudgetBelowFloor {
                floor,
                budget: compiled.budget_lanes,
            });
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
    // Track field seen for each logical or final physical source coordinate.
    let mut seen: HashMap<(bool, u8, u16), OperandField> = HashMap::new();

    let mut record = |physical: bool,
                      slot: u8,
                      col: u16,
                      field: OperandField|
     -> Result<(), CompileError> {
        match seen.get(&(physical, slot, col)) {
            None => {
                seen.insert((physical, slot, col), field);
                Ok(())
            }
            Some(&prev) if prev == field => Ok(()),
            Some(&prev) => Err(CompileError::FieldMismatch(format!(
                "Global (slot={slot}, col={col}) used as both {prev:?} and {field:?} in same layer"
            ))),
        }
    };

    // Determine the effective field for a global operand from the containing instruction.
    for instr in &compiled.program.instrs {
        match instr {
            Instr::Mov {
                field,
                src,
                dst,
                dir,
            } => {
                match dir {
                    MovDir::AccFromSrc | MovDir::DstFromSrc => {
                        if let Some(OperandLine::LogicalGlobal { slot, col }) = src {
                            record(false, *slot, *col, *field)?;
                        } else if let Some(OperandLine::Source { window, column, .. }) = src {
                            record(true, *window, *column as u16, *field)?;
                        }
                    }
                    _ => {}
                }
                match dir {
                    MovDir::DstFromSrc => {
                        if let Some(DstLine::GlobalMaterialize { slot, col }) = dst {
                            record(false, *slot, *col, *field)?;
                        }
                    }
                    MovDir::DstFromAcc => {
                        if let Some(DstLine::GlobalMaterialize { slot, col }) = dst {
                            record(false, *slot, *col, *field)?;
                        }
                    }
                    _ => {}
                }
            }
            Instr::Add {
                field, operands, ..
            } => {
                for op in operands {
                    if let OperandLine::LogicalGlobal { slot, col } = op {
                        record(false, *slot, *col, *field)?;
                    } else if let OperandLine::Source { window, column, .. } = op {
                        record(true, *window, *column as u16, *field)?;
                    }
                }
            }
            Instr::Mul {
                field, operands, ..
            } => {
                for op in operands {
                    if let OperandLine::LogicalGlobal { slot, col } = op {
                        record(false, *slot, *col, *field)?;
                    } else if let OperandLine::Source { window, column, .. } = op {
                        record(true, *window, *column as u16, *field)?;
                    }
                }
            }
            Instr::Fma {
                field_lhs,
                field_rhs,
                pairs,
                ..
            } => {
                for (l, r) in pairs {
                    if let OperandLine::LogicalGlobal { slot, col } = l {
                        record(false, *slot, *col, *field_lhs)?;
                    } else if let OperandLine::Source { window, column, .. } = l {
                        record(true, *window, *column as u16, *field_lhs)?;
                    }
                    if let OperandLine::LogicalGlobal { slot, col } = r {
                        record(false, *slot, *col, *field_rhs)?;
                    } else if let OperandLine::Source { window, column, .. } = r {
                        record(true, *window, *column as u16, *field_rhs)?;
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
    let check_source = |window: u8, column: u8, field: OperandField| -> Result<(), CompileError> {
        match compiled.ctx.source_windows.source_field(window) {
            Some(source_field) if source_field != field => {
                Err(CompileError::FieldStorageMismatch {
                    slot: window,
                    col: column as u16,
                })
            }
            _ => Ok(()),
        }
    };

    for instr in &compiled.program.instrs {
        match instr {
            Instr::Mov {
                field,
                src,
                dst,
                dir,
            } => {
                if let MovDir::AccFromSrc | MovDir::DstFromSrc = dir {
                    if let Some(OperandLine::LogicalGlobal { slot, col }) = src {
                        check(*slot, *col, *field)?;
                    } else if let Some(OperandLine::Source { window, column, .. }) = src {
                        check_source(*window, *column, *field)?;
                    }
                }
                if let MovDir::DstFromAcc | MovDir::DstFromSrc = dir {
                    if let Some(DstLine::GlobalMaterialize { slot, col }) = dst {
                        check(*slot, *col, *field)?;
                    }
                }
            }
            Instr::Add {
                field, operands, ..
            }
            | Instr::Mul {
                field, operands, ..
            } => {
                for op in operands {
                    if let OperandLine::LogicalGlobal { slot, col } = op {
                        check(*slot, *col, *field)?;
                    } else if let OperandLine::Source { window, column, .. } = op {
                        check_source(*window, *column, *field)?;
                    }
                }
            }
            Instr::Fma {
                field_lhs,
                field_rhs,
                pairs,
                ..
            } => {
                for (l, r) in pairs {
                    if let OperandLine::LogicalGlobal { slot, col } = l {
                        check(*slot, *col, *field_lhs)?;
                    } else if let OperandLine::Source { window, column, .. } = l {
                        check_source(*window, *column, *field_lhs)?;
                    }
                    if let OperandLine::LogicalGlobal { slot, col } = r {
                        check(*slot, *col, *field_rhs)?;
                    } else if let OperandLine::Source { window, column, .. } = r {
                        check_source(*window, *column, *field_rhs)?;
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
            Instr::Fma {
                field_lhs,
                field_rhs,
                ..
            } => {
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
            if let OperandLine::Ldc {
                sub: LdcSub::Special,
                idx,
            } = op
            {
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
