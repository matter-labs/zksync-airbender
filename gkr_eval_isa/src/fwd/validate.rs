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

fn join(a: AccField, b: OperandField) -> AccField {
    match (a, b) {
        (_, OperandField::Ext) => AccField::Ext,
        (AccField::Ext, _) => AccField::Ext,
        _ => AccField::Base,
    }
}

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
                        // Load into acc — sets acc field from MOV field bit.
                        acc = operand_field_to_acc(*field);
                    }
                    MovDir::DstFromAcc => {
                        // Materialize acc → dst. dst field must match acc.
                        // `promote` is rejected: we only accept what join produces
                        // from instruction's own field vs acc.
                        let dst_field = *field;
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
            Instr::Add { field, .. } => {
                if acc == AccField::Uninit {
                    // First ADD without a preceding MOV — treat as initializing.
                    acc = operand_field_to_acc(*field);
                } else {
                    acc = join(acc, *field);
                }
            }
            Instr::Mul { field, .. } => {
                if acc == AccField::Uninit {
                    acc = operand_field_to_acc(*field);
                } else {
                    acc = join(acc, *field);
                }
            }
            Instr::Fma { field_lhs, field_rhs, .. } => {
                // EB order is non-canonical — reject structurally (check 7 also
                // catches this, but assert here as well for field-consistency).
                if *field_lhs == OperandField::Ext && *field_rhs == OperandField::Base {
                    return Err(CompileError::FieldMismatch(
                        "FMA in non-canonical EB order".to_string(),
                    ));
                }
                let product_field = join(operand_field_to_acc(*field_lhs), *field_rhs);
                if acc == AccField::Uninit {
                    acc = product_field;
                } else {
                    acc = match (acc, product_field) {
                        (AccField::Ext, _) | (_, AccField::Ext) => AccField::Ext,
                        _ => AccField::Base,
                    };
                }
            }
        }
    }
    Ok(())
}

// ── Check 4: Ext smem alignment ───────────────────────────────────────────────

/// Every Ext smem cell referenced (as source or dst) must have `cell % 4 == 0`
/// and the four cells [cell, cell+3] must be in-bounds (< budget * 4, where
/// budget cells are BF-cell-indexed and Ext uses 4 consecutive cells).
fn check_ext_alignment(compiled: &CompiledLayer) -> Result<(), CompileError> {
    for instr in &compiled.program.instrs {
        match instr {
            Instr::Mov { dir, field, dst, src } => {
                if *field == OperandField::Ext {
                    if let MovDir::AccFromSrc | MovDir::DstFromSrc = dir {
                        if let Some(OperandLine::Smem { cell }) = src {
                            check_ext_cell(*cell, compiled.budget)?;
                        }
                    }
                    if let MovDir::DstFromAcc | MovDir::DstFromSrc = dir {
                        if let Some(DstLine::Smem { cell }) = dst {
                            check_ext_cell(*cell, compiled.budget)?;
                        }
                    }
                }
            }
            Instr::Add { field, operands, .. } if *field == OperandField::Ext => {
                for op in operands {
                    if let OperandLine::Smem { cell } = op {
                        check_ext_cell(*cell, compiled.budget)?;
                    }
                }
            }
            Instr::Mul { field, operands } if *field == OperandField::Ext => {
                for op in operands {
                    if let OperandLine::Smem { cell } = op {
                        check_ext_cell(*cell, compiled.budget)?;
                    }
                }
            }
            Instr::Fma { field_lhs, field_rhs, pairs, .. } => {
                for (l, r) in pairs {
                    if *field_lhs == OperandField::Ext {
                        if let OperandLine::Smem { cell } = l {
                            check_ext_cell(*cell, compiled.budget)?;
                        }
                    }
                    if *field_rhs == OperandField::Ext {
                        if let OperandLine::Smem { cell } = r {
                            check_ext_cell(*cell, compiled.budget)?;
                        }
                    }
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn check_ext_cell(cell: u16, budget: usize) -> Result<(), CompileError> {
    if cell % 4 != 0 {
        return Err(CompileError::ExtCellMisaligned(cell));
    }
    // 4 consecutive BF cells must be in-range within budget.
    let end = cell as usize + 4;
    if end > budget {
        return Err(CompileError::ExtCellMisaligned(cell));
    }
    Ok(())
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
            Instr::Mul { field, operands } => {
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

// ── Check 6: structural budget ────────────────────────────────────────────────

/// The program uses ≤ `compiled.budget` cells and every encoded index fits its
/// lane. Re-run `encode` and assert `Ok`.
fn check_budget(compiled: &CompiledLayer) -> Result<(), CompileError> {
    // Count max smem cell index used.
    let max_cell = max_smem_cell(&compiled.program);
    if max_cell > compiled.budget {
        return Err(CompileError::BudgetBelowFloor {
            floor: max_cell,
            budget: compiled.budget,
        });
    }
    // Re-encode the program — this also validates arity ≤ 127 and all lane widths.
    encode(&compiled.program).map_err(CompileError::Encode)?;
    Ok(())
}

fn max_smem_cell(program: &Program) -> usize {
    let mut max = 0usize;
    for instr in &program.instrs {
        match instr {
            Instr::Mov { src, dst, .. } => {
                if let Some(OperandLine::Smem { cell }) = src { max = max.max(*cell as usize + 1); }
                if let Some(DstLine::Smem { cell }) = dst { max = max.max(*cell as usize + 1); }
            }
            Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
                for op in operands {
                    if let OperandLine::Smem { cell } = op { max = max.max(*cell as usize + 1); }
                }
            }
            Instr::Fma { pairs, .. } => {
                for (l, r) in pairs {
                    if let OperandLine::Smem { cell } = l { max = max.max(*cell as usize + 1); }
                    if let OperandLine::Smem { cell } = r { max = max.max(*cell as usize + 1); }
                }
            }
        }
    }
    max
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

// ── Public entry point ────────────────────────────────────────────────────────

/// Backend validation pass (spec §12). Independently re-checks a compiled
/// layer's invariants. A successfully compiled layer MUST pass this cleanly.
pub fn validate_compiled(compiled: &CompiledLayer, layer: &DagLayer) -> Result<(), CompileError> {
    check_coverage(compiled, layer)?;
    check_action_completeness(compiled, layer)?;
    check_field_transitions(compiled)?;
    check_ext_alignment(compiled)?;
    check_storage_field_identity(compiled)?;
    check_budget(compiled)?;
    check_canonical_operands(compiled)?;
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
        };

        // Must not spuriously reject due to dag_ir field re-derivation.
        assert_eq!(validate_compiled(&compiled, &layer), Ok(()));
    }

    // ── Check 4: Ext smem alignment ───────────────────────────────────────────

    /// Ext smem operand with cell % 4 != 0 → ExtCellMisaligned.
    #[test]
    fn ext_smem_misaligned_rejected() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.budget = 32;
        compiled.program.instrs = vec![
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Ext,
                dst: None,
                src: Some(OperandLine::Smem { cell: 3 }), // 3 % 4 != 0
            },
        ];

        let result = validate_compiled(&compiled, &layer);
        assert_eq!(result, Err(CompileError::ExtCellMisaligned(3)));
    }

    /// Ext smem with cell % 4 == 0 and 4 in-bounds cells → Ok.
    #[test]
    fn ext_smem_aligned_ok() {
        let layer = simple_compute_layer();
        let mut compiled = clean_compiled(&layer);
        compiled.budget = 32; // 32 BF cells; Ext at cell=0 uses [0..3] ✓
        compiled.program.instrs = vec![
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Ext,
                dst: None,
                src: Some(OperandLine::Smem { cell: 0 }), // aligned, in-bounds
            },
            Instr::Mov {
                dir: MovDir::DstFromAcc,
                field: OperandField::Ext,
                dst: Some(DstLine::Smem { cell: 4 }), // aligned, in-bounds
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
}
