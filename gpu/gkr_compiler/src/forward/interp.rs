//! CPU interpreter (spec §4–§6). Per-row, per-root outputs; reuses dag_ir resolvers.

use super::context::{CompiledLayer, DagForwardContext, OutputCell, RootOutput, RowOutputs};
use super::error::InterpError;
use super::isa::*;
use field::{Field, FieldExtension, PrimeField};
use gkr_eval_ir::{Bf, DagLayer, Ext, Resolvers, eval_layer_expr};
use std::collections::HashMap;

#[inline]
fn lift(b: Bf) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(b)
}

/// How the interpreter resolves a `Special { desc }` operand.
enum SpecialMode<'p> {
    /// SP1: re-run the authoritative fold (circular; synthetic/debug only).
    Fold,
    /// SP2: read the real peek binding.
    Peek(&'p dyn crate::forward::peek::PeekResolver),
}

pub fn interpret_layer_row(
    compiled: &CompiledLayer,
    layer: &DagLayer,
    r: &Resolvers<'_>,
    row: usize,
) -> Result<RowOutputs, InterpError> {
    let (_, cells, globals) =
        interpret_layer_row_impl(compiled, layer, r, &SpecialMode::Fold, row)?;
    row_outputs(
        compiled,
        layer,
        r,
        &SpecialMode::Fold,
        row,
        &cells,
        &globals,
    )
}

/// Execute a compiled program and return its final accumulator value. This is
/// used by evaluation-plan terminals that return the accumulator directly,
/// without materializing it through a forward output instruction.
pub fn interpret_program_row_acc(
    compiled: &CompiledLayer,
    layer: &DagLayer,
    r: &Resolvers<'_>,
    row: usize,
) -> Result<Ext, InterpError> {
    let (acc, _, _) = interpret_layer_row_impl(compiled, layer, r, &SpecialMode::Fold, row)?;
    Ok(acc)
}

pub fn interpret_layer_row_with_peeks(
    compiled: &CompiledLayer,
    layer: &DagLayer,
    r: &Resolvers<'_>,
    peek: &dyn crate::forward::peek::PeekResolver,
    row: usize,
) -> Result<RowOutputs, InterpError> {
    let mode = SpecialMode::Peek(peek);
    let (_, cells, globals) = interpret_layer_row_impl(compiled, layer, r, &mode, row)?;
    row_outputs(compiled, layer, r, &mode, row, &cells, &globals)
}

fn interpret_layer_row_impl(
    compiled: &CompiledLayer,
    layer: &DagLayer,
    r: &Resolvers<'_>,
    mode: &SpecialMode<'_>,
    row: usize,
) -> Result<(Ext, Vec<Ext>, HashMap<(u8, u16), Ext>), InterpError> {
    let ctx = &compiled.ctx;
    let mut acc = Ext::ZERO;
    // Tracked acc domain (spec §1.1): base until a Mov{Ext} AccFromSrc or a
    // `promote` bit lifts it. On this Ext-valued golden model the flag never
    // changes a value (bf↪e4 embedding); it exists so the interpreter mirrors
    // the state the Task 3 validator checks statically.
    let mut acc_is_ext = false;
    let mut cells: Vec<Ext> = vec![Ext::ZERO; compiled.budget_lanes.max(4)];
    let mut globals: HashMap<(u8, u16), Ext> = HashMap::new();

    for instr in &compiled.program.instrs {
        match instr {
            Instr::Mov {
                dir,
                field,
                dst,
                src,
            } => match dir {
                MovDir::AccFromSrc => {
                    acc = resolve(
                        &src.unwrap(),
                        *field,
                        &cells,
                        &globals,
                        ctx,
                        r,
                        row,
                        layer,
                        mode,
                    )?;
                    acc_is_ext = *field == OperandField::Ext;
                }
                MovDir::DstFromAcc => {
                    write_dst(&dst.unwrap(), *field, acc, &mut cells, &mut globals);
                }
                MovDir::DstFromSrc => {
                    let v = resolve(
                        &src.unwrap(),
                        *field,
                        &cells,
                        &globals,
                        ctx,
                        r,
                        row,
                        layer,
                        mode,
                    )?;
                    write_dst(&dst.unwrap(), *field, v, &mut cells, &mut globals);
                }
            },
            Instr::Add {
                field,
                sign,
                promote,
                operands,
            } => {
                acc_is_ext |= *promote;
                for o in operands {
                    let v = resolve(o, *field, &cells, &globals, ctx, r, row, layer, mode)?;
                    match sign {
                        Sign::Plus => {
                            acc.add_assign(&v);
                        }
                        Sign::Minus => {
                            acc.sub_assign(&v);
                        }
                    }
                }
            }
            Instr::Mul {
                field,
                promote,
                negate_acc,
                operands,
            } => {
                acc_is_ext |= *promote;
                // Sign bit = negate acc FIRST (spec §1.2); zero operands = pure negation.
                if *negate_acc {
                    acc.negate();
                }
                for o in operands {
                    let v = resolve(o, *field, &cells, &globals, ctx, r, row, layer, mode)?;
                    acc.mul_assign(&v);
                }
            }
            Instr::Fma {
                field_lhs,
                field_rhs,
                sign,
                promote,
                pairs,
            } => {
                acc_is_ext |= *promote;
                for (l, rhs) in pairs {
                    let mut prod =
                        resolve(l, *field_lhs, &cells, &globals, ctx, r, row, layer, mode)?;
                    prod.mul_assign(&resolve(
                        rhs, *field_rhs, &cells, &globals, ctx, r, row, layer, mode,
                    )?);
                    match sign {
                        Sign::Plus => {
                            acc.add_assign(&prod);
                        }
                        Sign::Minus => {
                            acc.sub_assign(&prod);
                        }
                    }
                }
            }
        }
    }

    // Values on this model never depend on the domain flag; static enforcement
    // of the promote/domain rules is the validator's job (Task 3).
    let _ = acc_is_ext;

    Ok((acc, cells, globals))
}

fn row_outputs(
    compiled: &CompiledLayer,
    layer: &DagLayer,
    r: &Resolvers<'_>,
    mode: &SpecialMode<'_>,
    row: usize,
    cells: &[Ext],
    globals: &HashMap<(u8, u16), Ext>,
) -> Result<RowOutputs, InterpError> {
    let ctx = &compiled.ctx;
    let mut by_root = HashMap::new();
    for (rid, out) in &compiled.root_outputs {
        let v = match out {
            RootOutput::Cell(OutputCell::Smem(c)) => cells[*c as usize],
            RootOutput::Cell(OutputCell::Global { slot, col }) => globals[&(*slot, *col)],
            // CopyAlias: resolved OUTSIDE the ISA stream (zero lanes). Always a
            // stable-storage operand (Global/Ldc/Special — never Smem, see
            // `copy_src_read_place`), so the field bit passed here is inert.
            RootOutput::Alias(op) => resolve(
                op,
                OperandField::Base,
                cells,
                globals,
                ctx,
                r,
                row,
                layer,
                mode,
            )?,
        };
        by_root.insert(*rid, v);
    }
    Ok(RowOutputs { by_root })
}

/// v2 wire unit of an `Smem` index (spec §3): the instruction's field bit selects the
/// view — bf → 4-B lane index (this model's `cells` vector is lane-addressed, exactly
/// v1), ext → 16-B BUCKET index, whose value lives at the bucket's first lane
/// (`cell * 4`). The interpreter is a faithful executor of the WIRE format, so it
/// multiplies the bucket back onto its lane-addressed cell file.
#[inline]
pub(crate) fn smem_lane(cell: u16, field: OperandField) -> usize {
    match field {
        OperandField::Base => cell as usize,
        OperandField::Ext => cell as usize * 4,
    }
}

// Free fn (not a closure): borrows `globals` immutably while the caller's loop
// mutates it via `write_dst`. `field` is the instruction's field bit governing this
// operand (per-side for FMA) — it selects the `Smem` index unit (see `smem_lane`).
#[allow(clippy::too_many_arguments)]
fn resolve(
    o: &OperandLine,
    field: OperandField,
    cells: &[Ext],
    globals: &HashMap<(u8, u16), Ext>,
    ctx: &DagForwardContext,
    r: &Resolvers<'_>,
    row: usize,
    layer: &DagLayer,
    mode: &SpecialMode<'_>,
) -> Result<Ext, InterpError> {
    match *o {
        OperandLine::LogicalGlobal { slot, col } => {
            // VM materialized this backing this row (incl. Prior re-read of a cache).
            if let Some(v) = globals.get(&(slot, col)) {
                return Ok(*v);
            }
            // Dense per-slot col → the ORIGINAL ReadPlace via the table's
            // first-class reverse map (the dense index is meaningless to the
            // resolver; a raw (key, col) reconstruction would read the wrong
            // column).
            let place = ctx
                .backings
                .slot_col_to_read_place(slot, col)
                .ok_or(InterpError::UnknownSlot(slot))?;
            Ok(r.read.read(&place, row))
        }
        OperandLine::LogicalFold { slot, col, desc } => Err(InterpError::MalformedInstr(format!(
            "unbound fold source {slot}:{col} descriptor {desc}"
        ))),
        OperandLine::Source { window, column, .. } => {
            let place = ctx
                .source_windows
                .resolve_read_place(window, column)
                .ok_or_else(|| {
                    InterpError::MalformedInstr(format!(
                        "unknown source window {window} column {column}"
                    ))
                })?;
            Ok(r.read.read(&place, row))
        }
        OperandLine::Smem { cell } => Ok(cells[smem_lane(cell, field)]),
        OperandLine::Ldc { sub, idx } => match sub {
            LdcSub::Const => Ok(lift(Bf::from_u32_with_reduction(
                ctx.consts.get(idx).ok_or(InterpError::UnknownConst(idx))?,
            ))),
            LdcSub::Special => Ok(match idx {
                0 => Ext::ZERO,
                1 => Ext::ONE,
                2 => {
                    let mut z = Ext::ZERO;
                    z.sub_assign(&Ext::ONE);
                    z
                }
                _ => return Err(InterpError::MalformedInstr("special idx".into())),
            }),
            LdcSub::ConstDerivedE4 | LdcSub::ArgDerivedE4 => {
                let cr = ctx
                    .derived_e4
                    .get(sub, idx)
                    .ok_or(InterpError::UnknownDerivedE4(idx))?;
                Ok(r.challenge.challenge(cr))
            }
        },
        OperandLine::Special { desc } => {
            let d = ctx
                .specials
                .get(desc)
                .ok_or(InterpError::UnknownSpecial(desc))?;
            match mode {
                SpecialMode::Fold => Ok(eval_layer_expr(layer, d.origin_expr, row, r)),
                SpecialMode::Peek(p) => p.peek(d, row, r).map_err(InterpError::Peek),
            }
        }
    }
}

fn write_dst(
    dst: &DstLine,
    field: OperandField,
    v: Ext,
    cells: &mut Vec<Ext>,
    globals: &mut HashMap<(u8, u16), Ext>,
) {
    match *dst {
        DstLine::Smem { cell } => {
            let lane = smem_lane(cell, field);
            if cells.len() <= lane {
                cells.resize(lane + 4, Ext::ZERO);
            }
            cells[lane] = v;
        }
        DstLine::GlobalMaterialize { slot, col } => {
            globals.insert((slot, col), v);
        }
    }
}
