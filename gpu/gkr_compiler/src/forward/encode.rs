//! 16-bit-lane wire format (spec §7). Streaming encode/decode + cap-guards (§12).

use super::error::{DecodeError, EncodeError};
use super::isa::*;

pub fn pack_operand(o: OperandLine) -> Result<u16, EncodeError> {
    match o {
        OperandLine::LogicalGlobal { slot, col } => {
            Err(EncodeError::UnboundLogicalSource { slot, col })
        }
        OperandLine::LogicalFold { slot, col, desc } => {
            Err(EncodeError::UnboundLogicalFold { slot, col, desc })
        }
        OperandLine::Source {
            window,
            column,
            first_access,
        } => {
            if (window as u32) >= MAX_SOURCE_WINDOWS {
                return Err(EncodeError::SourceWindowOutOfRange(window));
            }
            if (column as u32) >= SOURCE_WINDOW_COLUMNS {
                return Err(EncodeError::SourceColumnOutOfRange(column));
            }
            Ok(TAG_SOURCE
                | ((first_access as u16) << FIRST_ACCESS_SHIFT)
                | ((window as u16) << SOURCE_WINDOW_SHIFT)
                | ((column as u16) << SOURCE_COLUMN_SHIFT))
        }
        OperandLine::Smem { cell } => {
            if (cell as u32) >= MAX_CELL {
                return Err(EncodeError::CellOutOfRange(cell));
            }
            Ok(TAG_SMEM | (cell << TYPE_BITS))
        }
        OperandLine::Ldc { sub, idx } => {
            if (idx as u32) >= MAX_LDC_IDX {
                return Err(EncodeError::LdcIdxOutOfRange(idx));
            }
            Ok(TAG_LDC | ((sub as u16) << TYPE_BITS) | (idx << (TYPE_BITS + LDC_SUB_BITS)))
        }
        OperandLine::Special { desc } => {
            if (desc as u32) >= MAX_DESC {
                return Err(EncodeError::DescOutOfRange(desc));
            }
            Ok(TAG_SPECIAL | (desc << TYPE_BITS))
        }
    }
}

pub fn unpack_operand(lane: u16) -> Result<OperandLine, DecodeError> {
    match lane & TYPE_MASK {
        TAG_SOURCE => Ok(OperandLine::Source {
            window: ((lane >> SOURCE_WINDOW_SHIFT) & SOURCE_WINDOW_MASK) as u8,
            column: ((lane >> SOURCE_COLUMN_SHIFT) & SOURCE_COLUMN_MASK) as u8,
            first_access: ((lane >> FIRST_ACCESS_SHIFT) & 1) != 0,
        }),
        TAG_SMEM => Ok(OperandLine::Smem {
            cell: (lane >> TYPE_BITS) & ((1 << CELL_BITS) - 1),
        }),
        TAG_LDC => {
            let sub = match (lane >> TYPE_BITS) & LDC_SUB_MASK {
                0 => LdcSub::Const,
                1 => LdcSub::ConstDerivedE4,
                2 => LdcSub::ArgDerivedE4,
                _ => LdcSub::Special,
            };
            Ok(OperandLine::Ldc {
                sub,
                idx: lane >> (TYPE_BITS + LDC_SUB_BITS),
            })
        }
        _ => Ok(OperandLine::Special {
            desc: lane >> TYPE_BITS,
        }), // TAG_SPECIAL
    }
}

pub fn pack_dst(d: DstLine) -> Result<u16, EncodeError> {
    match d {
        DstLine::Smem { cell } => {
            if (cell as u32) >= MAX_CELL {
                return Err(EncodeError::CellOutOfRange(cell));
            }
            Ok(DST_TAG_SMEM | (cell << DST_TAG_BITS))
        }
        DstLine::GlobalMaterialize { slot, col } => {
            if (slot as u32) >= MAX_SLOTS {
                return Err(EncodeError::SlotOutOfRange(slot));
            }
            if (col as u32) >= MAX_COLS {
                return Err(EncodeError::ColOutOfRange(col));
            }
            Ok(DST_TAG_GLOBAL
                | ((slot as u16) << DST_TAG_BITS)
                | (col << (DST_TAG_BITS + SLOT_BITS)))
        }
    }
}

pub fn unpack_dst(lane: u16) -> Result<DstLine, DecodeError> {
    if lane & DST_TAG_MASK == DST_TAG_SMEM {
        Ok(DstLine::Smem {
            cell: (lane >> DST_TAG_BITS) & ((1 << CELL_BITS) - 1),
        })
    } else {
        Ok(DstLine::GlobalMaterialize {
            slot: ((lane >> DST_TAG_BITS) & ((1 << SLOT_BITS) - 1)) as u8,
            col: lane >> (DST_TAG_BITS + SLOT_BITS),
        })
    }
}

fn pack_arith_header(
    op: Opcode,
    arity: usize,
    f0: OperandField,
    f1: OperandField,
    promote: bool,
    sign: Sign,
) -> Result<u16, EncodeError> {
    // Zero arity is legal only for Mul-minus (pure acc negation, §1.2).
    let zero_arity_ok = op == Opcode::Mul && sign == Sign::Minus;
    if (arity == 0 && !zero_arity_ok) || arity > MAX_ARITY {
        return Err(EncodeError::ArityOutOfRange(arity));
    }
    Ok((op as u16)
        | ((arity as u16) << ARITY_SHIFT)
        | ((f0 as u16) << F0_SHIFT)
        | ((f1 as u16) << F1_SHIFT)
        | ((promote as u16) << PROMOTE_SHIFT)
        | ((sign as u16) << SIGN_SHIFT))
}

pub fn encode(p: &Program) -> Result<Vec<u16>, EncodeError> {
    let mut out = Vec::new();
    for instr in &p.instrs {
        match instr {
            Instr::Add {
                field,
                sign,
                promote,
                operands,
            } => {
                out.push(pack_arith_header(
                    Opcode::Add,
                    operands.len(),
                    *field,
                    OperandField::Base,
                    *promote,
                    *sign,
                )?);
                for o in operands {
                    out.push(pack_operand(*o)?);
                }
            }
            Instr::Mul {
                field,
                promote,
                negate_acc,
                operands,
            } => {
                let sign = if *negate_acc { Sign::Minus } else { Sign::Plus };
                out.push(pack_arith_header(
                    Opcode::Mul,
                    operands.len(),
                    *field,
                    OperandField::Base,
                    *promote,
                    sign,
                )?);
                for o in operands {
                    out.push(pack_operand(*o)?);
                }
            }
            Instr::Fma {
                field_lhs,
                field_rhs,
                sign,
                promote,
                pairs,
            } => {
                if *field_lhs == OperandField::Ext && *field_rhs == OperandField::Base {
                    return Err(EncodeError::NonCanonicalFmaOrder);
                }
                out.push(pack_arith_header(
                    Opcode::Fma,
                    pairs.len(),
                    *field_lhs,
                    *field_rhs,
                    *promote,
                    *sign,
                )?);
                for (l, r) in pairs {
                    out.push(pack_operand(*l)?);
                    out.push(pack_operand(*r)?);
                }
            }
            Instr::Mov {
                dir,
                field,
                dst,
                src,
            } => {
                out.push(
                    (Opcode::Mov as u16)
                        | ((*dir as u16) << MOV_DIR_SHIFT)
                        | ((*field as u16) << MOV_FIELD_SHIFT),
                );
                match dir {
                    MovDir::AccFromSrc => out.push(pack_operand(src.expect("AccFromSrc src"))?),
                    MovDir::DstFromAcc => out.push(pack_dst(dst.expect("DstFromAcc dst"))?),
                    MovDir::DstFromSrc => {
                        out.push(pack_dst(dst.expect("DstFromSrc dst"))?);
                        out.push(pack_operand(src.expect("DstFromSrc src"))?);
                    }
                }
            }
        }
    }
    Ok(out)
}

/// Count the lanes an instruction stream will occupy without attempting to
/// encode compiler-private logical source payloads.
pub fn encoded_lane_count(p: &Program) -> Result<usize, EncodeError> {
    let mut lanes = 0usize;
    for instr in &p.instrs {
        lanes += match instr {
            Instr::Add {
                field,
                sign,
                promote,
                operands,
            } => {
                pack_arith_header(
                    Opcode::Add,
                    operands.len(),
                    *field,
                    OperandField::Base,
                    *promote,
                    *sign,
                )?;
                1 + operands.len()
            }
            Instr::Mul {
                field,
                promote,
                negate_acc,
                operands,
            } => {
                let sign = if *negate_acc { Sign::Minus } else { Sign::Plus };
                pack_arith_header(
                    Opcode::Mul,
                    operands.len(),
                    *field,
                    OperandField::Base,
                    *promote,
                    sign,
                )?;
                1 + operands.len()
            }
            Instr::Fma {
                field_lhs,
                field_rhs,
                sign,
                promote,
                pairs,
            } => {
                if *field_lhs == OperandField::Ext && *field_rhs == OperandField::Base {
                    return Err(EncodeError::NonCanonicalFmaOrder);
                }
                pack_arith_header(
                    Opcode::Fma,
                    pairs.len(),
                    *field_lhs,
                    *field_rhs,
                    *promote,
                    *sign,
                )?;
                1 + 2 * pairs.len()
            }
            Instr::Mov { dir, .. } => match dir {
                MovDir::AccFromSrc | MovDir::DstFromAcc => 2,
                MovDir::DstFromSrc => 3,
            },
        };
    }
    Ok(lanes)
}

pub fn decode(lanes: &[u16]) -> Result<Program, DecodeError> {
    let mut instrs = Vec::new();
    let mut i = 0usize;
    fn next(lanes: &[u16], i: &mut usize) -> Result<u16, DecodeError> {
        let v = *lanes.get(*i).ok_or(DecodeError::Truncated)?;
        *i += 1;
        Ok(v)
    }
    while i < lanes.len() {
        let h = next(lanes, &mut i)?;
        let op = h & OPCODE_MASK;
        if op == Opcode::Mov as u16 {
            if (h >> MOV_RSVD_SHIFT) != 0 {
                return Err(DecodeError::NonZeroReserved);
            } // acc_sel + high bits
            let dir = match (h >> MOV_DIR_SHIFT) & MOV_DIR_MASK {
                0 => MovDir::AccFromSrc,
                1 => MovDir::DstFromAcc,
                2 => MovDir::DstFromSrc,
                d => return Err(DecodeError::BadMovDir(d)),
            };
            let field = if (h >> MOV_FIELD_SHIFT) & 1 == 1 {
                OperandField::Ext
            } else {
                OperandField::Base
            };
            let (dst, src) = match dir {
                MovDir::AccFromSrc => (None, Some(unpack_operand(next(lanes, &mut i)?)?)),
                MovDir::DstFromAcc => (Some(unpack_dst(next(lanes, &mut i)?)?), None),
                MovDir::DstFromSrc => {
                    let d = unpack_dst(next(lanes, &mut i)?)?;
                    (Some(d), Some(unpack_operand(next(lanes, &mut i)?)?))
                }
            };
            instrs.push(Instr::Mov {
                dir,
                field,
                dst,
                src,
            });
            continue;
        }
        if (h >> ARITH_RSVD_SHIFT) != 0 {
            return Err(DecodeError::NonZeroReserved);
        }
        let arity = ((h >> ARITY_SHIFT) & ARITY_MASK) as usize;
        let f0 = if (h >> F0_SHIFT) & 1 == 1 {
            OperandField::Ext
        } else {
            OperandField::Base
        };
        let f1 = if (h >> F1_SHIFT) & 1 == 1 {
            OperandField::Ext
        } else {
            OperandField::Base
        };
        let promote = (h >> PROMOTE_SHIFT) & 1 == 1;
        let sign = if (h >> SIGN_SHIFT) & 1 == 1 {
            Sign::Minus
        } else {
            Sign::Plus
        };
        match op {
            x if x == Opcode::Add as u16 => {
                if f1 != OperandField::Base {
                    return Err(DecodeError::NonCanonicalField);
                }
                if arity == 0 {
                    return Err(DecodeError::ZeroArity);
                }
                let operands = (0..arity)
                    .map(|_| unpack_operand(next(lanes, &mut i)?))
                    .collect::<Result<_, _>>()?;
                instrs.push(Instr::Add {
                    field: f0,
                    sign,
                    promote,
                    operands,
                });
            }
            x if x == Opcode::Mul as u16 => {
                if f1 != OperandField::Base {
                    return Err(DecodeError::NonCanonicalField);
                }
                let negate_acc = sign == Sign::Minus;
                // Zero-arity Mul = pure acc negation, legal iff negate_acc (§1.2).
                if arity == 0 && !negate_acc {
                    return Err(DecodeError::ZeroArity);
                }
                let operands = (0..arity)
                    .map(|_| unpack_operand(next(lanes, &mut i)?))
                    .collect::<Result<_, _>>()?;
                instrs.push(Instr::Mul {
                    field: f0,
                    promote,
                    negate_acc,
                    operands,
                });
            }
            _ => {
                // Fma
                // Mixed FMA is canonical (Base, Ext); EB is the swapped duplicate — reject it.
                if f0 == OperandField::Ext && f1 == OperandField::Base {
                    return Err(DecodeError::NonCanonicalField);
                }
                if arity == 0 {
                    return Err(DecodeError::ZeroArity);
                }
                let mut pairs = Vec::with_capacity(arity);
                for _ in 0..arity {
                    let l = unpack_operand(next(lanes, &mut i)?)?;
                    let r = unpack_operand(next(lanes, &mut i)?)?;
                    pairs.push((l, r));
                }
                instrs.push(Instr::Fma {
                    field_lhs: f0,
                    field_rhs: f1,
                    sign,
                    promote,
                    pairs,
                });
            }
        }
    }
    Ok(Program { instrs })
}
