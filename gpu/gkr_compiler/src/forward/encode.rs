//! Forward VM wire encoding.

use super::error::EncodeError;
use super::isa::*;

fn pack_operand(
    o: OperandLine,
    source_window_bits: u32,
    source_column_bits: u32,
) -> Result<u16, EncodeError> {
    match o {
        OperandLine::LogicalGlobal { slot, col } => {
            Err(EncodeError::UnboundLogicalSource { slot, col })
        }
        OperandLine::Source { window, column } => {
            if (window as u32) >= 1 << source_window_bits {
                return Err(EncodeError::SourceWindowOutOfRange(window));
            }
            if (column as u32) >= 1 << source_column_bits {
                return Err(EncodeError::SourceColumnOutOfRange(column));
            }
            Ok(TAG_SOURCE
                | ((window as u16) << SOURCE_WINDOW_SHIFT)
                | (column << (SOURCE_WINDOW_SHIFT + source_window_bits)))
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

fn pack_dst(d: DstLine) -> Result<u16, EncodeError> {
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

fn pack_arith_header(
    op: Opcode,
    arity: usize,
    f0: OperandField,
    f1: OperandField,
    sign: Sign,
) -> Result<u16, EncodeError> {
    // Zero arity is the pure accumulator negation.
    let zero_arity_ok = op == Opcode::Mul && sign == Sign::Minus;
    if (arity == 0 && !zero_arity_ok) || arity > MAX_ARITY {
        return Err(EncodeError::ArityOutOfRange(arity));
    }
    Ok((op as u16)
        | ((arity as u16) << ARITY_SHIFT)
        | ((f0 as u16) << F0_SHIFT)
        | ((f1 as u16) << F1_SHIFT)
        | ((sign as u16) << SIGN_SHIFT))
}

fn encode_with_source_bits(
    p: &Program,
    source_window_bits: u32,
    source_column_bits: u32,
) -> Result<Vec<u16>, EncodeError> {
    let mut out = Vec::new();
    for instr in &p.instrs {
        match instr {
            Instr::Add {
                field,
                sign,
                operands,
            } => {
                out.push(pack_arith_header(
                    Opcode::Add,
                    operands.len(),
                    *field,
                    OperandField::Base,
                    *sign,
                )?);
                for o in operands {
                    out.push(pack_operand(*o, source_window_bits, source_column_bits)?);
                }
            }
            Instr::Mul {
                field,
                negate_acc,
                operands,
            } => {
                let sign = if *negate_acc { Sign::Minus } else { Sign::Plus };
                out.push(pack_arith_header(
                    Opcode::Mul,
                    operands.len(),
                    *field,
                    OperandField::Base,
                    sign,
                )?);
                for o in operands {
                    out.push(pack_operand(*o, source_window_bits, source_column_bits)?);
                }
            }
            Instr::Fma {
                field_lhs,
                field_rhs,
                sign,
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
                    *sign,
                )?);
                for (l, r) in pairs {
                    out.push(pack_operand(*l, source_window_bits, source_column_bits)?);
                    out.push(pack_operand(*r, source_window_bits, source_column_bits)?);
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
                    MovDir::AccFromSrc => out.push(pack_operand(
                        src.expect("AccFromSrc src"),
                        source_window_bits,
                        source_column_bits,
                    )?),
                    MovDir::DstFromAcc => out.push(pack_dst(dst.expect("DstFromAcc dst"))?),
                    MovDir::DstFromSrc => {
                        out.push(pack_dst(dst.expect("DstFromSrc dst"))?);
                        out.push(pack_operand(
                            src.expect("DstFromSrc src"),
                            source_window_bits,
                            source_column_bits,
                        )?);
                    }
                }
            }
        }
    }
    Ok(out)
}

pub fn encode(p: &Program) -> Result<Vec<u16>, EncodeError> {
    encode_with_source_bits(p, SOURCE_WINDOW_BITS, SOURCE_COLUMN_BITS)
}

pub fn encode_runtime(p: &Program) -> Result<Vec<u16>, EncodeError> {
    encode_with_source_bits(p, RUNTIME_SOURCE_WINDOW_BITS, RUNTIME_SOURCE_COLUMN_BITS)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn program_with_source(window: u8, column: u16) -> Program {
        Program {
            instrs: vec![Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Base,
                dst: None,
                src: Some(OperandLine::Source { window, column }),
            }],
        }
    }

    #[test]
    fn runtime_source_layout_encodes_its_maximum_coordinate() {
        assert_eq!(
            encode_runtime(&program_with_source(15, 511)),
            Ok(vec![3, 32_764]),
        );
    }

    #[test]
    fn runtime_source_layout_rejects_each_overflow_boundary() {
        assert_eq!(
            encode_runtime(&program_with_source(16, 0)),
            Err(EncodeError::SourceWindowOutOfRange(16)),
        );
        assert_eq!(
            encode_runtime(&program_with_source(0, 512)),
            Err(EncodeError::SourceColumnOutOfRange(512)),
        );
    }
}
