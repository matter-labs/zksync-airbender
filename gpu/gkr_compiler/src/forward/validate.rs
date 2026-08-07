//! Validation of the compiled forward program.

use super::context::CompiledLayerBuild;
use super::encode::encode;
use super::error::CompileError;
use super::isa::{DstLine, Instr, MovDir, OperandField, OperandLine, Program};

/// Track the accumulator field by replaying the program's field bits.
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

fn check_field_transitions(compiled: &CompiledLayerBuild) -> Result<(), CompileError> {
    let mut acc = AccField::Uninit;

    for instr in &compiled.program.instrs {
        match instr {
            Instr::Mov { dir, field, .. } => {
                match dir {
                    MovDir::AccFromSrc => {
                        // Loading the accumulator sets its domain.
                        acc = operand_field_to_acc(*field);
                    }
                    MovDir::DstFromAcc => {
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
                        // Direct copies do not affect the accumulator.
                    }
                }
            }
            Instr::Add { field, .. } => {
                if *field == OperandField::Ext {
                    acc = AccField::Ext;
                }
            }
            Instr::Mul {
                field, operands, ..
            } => {
                // Mul{Base} dispatches on the accumulator domain (bf mul vs
                // 4-limb scale) — it never REQUIRES ext. Zero-arity Mul is
                // pure acc negation, typed by the acc domain: no requirement
                // regardless of the field bit. Only Mul{Ext} with operands
                // requires an ext acc.
                let requires_ext = *field == OperandField::Ext && !operands.is_empty();
                if requires_ext {
                    acc = AccField::Ext;
                }
            }
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
                // Mixed and extension FMAs require an extension accumulator.
                // (full e4 add of the product into acc).
                if *field_rhs == OperandField::Ext {
                    acc = AccField::Ext;
                }
            }
        }
    }
    Ok(())
}

/// Visit every `Smem` reference (operand AND dst) in the program with its
/// program-instruction index, wire cell index, and governing field bit (Add/Mul
/// apply `field` to every operand, Fma `field_lhs`/`field_rhs` per side, Mov
/// `field` to both src and dst).
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

/// Extension-field indices address buckets; base-field indices address lanes.
fn check_smem_bounds(compiled: &CompiledLayerBuild) -> Result<(), CompileError> {
    for_each_smem_ref(&compiled.program, |_, cell, field| {
        let floor = (cell as usize + 1) * field.lanes();
        if floor > compiled.budget_lanes {
            return Err(CompileError::BudgetBelowFloor {
                floor,
                budget: compiled.budget_lanes,
            });
        }
        Ok(())
    })
}

/// Ensure each global operand matches its storage field.
fn check_field_storage_agreement(compiled: &CompiledLayerBuild) -> Result<(), CompileError> {
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
                    if let Some(OperandLine::Source { window, column, .. }) = src {
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
                    if let OperandLine::Source { window, column, .. } = op {
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
                    if let OperandLine::Source { window, column, .. } = l {
                        check_source(*window, *column, *field_lhs)?;
                    }
                    if let OperandLine::Source { window, column, .. } = r {
                        check_source(*window, *column, *field_rhs)?;
                    }
                }
            }
        }
    }
    Ok(())
}

fn check_budget(compiled: &CompiledLayerBuild) -> Result<(), CompileError> {
    // Re-encode the program — this also validates arity ≤ 127 and all lane widths.
    encode(&compiled.program).map_err(CompileError::Encode)?;
    Ok(())
}

pub(crate) fn validate_compiled(compiled: &CompiledLayerBuild) -> Result<(), CompileError> {
    check_field_transitions(compiled)?;
    check_smem_bounds(compiled)?;
    check_field_storage_agreement(compiled)?;
    check_budget(compiled)?;
    Ok(())
}
