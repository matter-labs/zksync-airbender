//! 16-bit-lane wire format (spec §7). Streaming encode/decode + cap-guards (§12).

use super::error::{DecodeError, EncodeError};
use super::isa::*;

const TYPE_MASK: u16 = 0b11;

pub fn pack_operand(o: OperandLine) -> Result<u16, EncodeError> {
    match o {
        OperandLine::Global { slot, col } => {
            if (slot as u32) >= MAX_SLOTS { return Err(EncodeError::SlotOutOfRange(slot)); }
            if (col as u32) >= MAX_COLS { return Err(EncodeError::ColOutOfRange(col)); }
            Ok(0b00 | ((slot as u16) << TYPE_BITS) | (col << (TYPE_BITS + SLOT_BITS)))
        }
        OperandLine::Smem { cell } => {
            if (cell as u32) >= MAX_CELL { return Err(EncodeError::CellOutOfRange(cell)); }
            Ok(0b01 | (cell << TYPE_BITS))
        }
        OperandLine::Ldc { sub, idx } => {
            if (idx as u32) >= MAX_LDC_IDX { return Err(EncodeError::LdcIdxOutOfRange(idx)); }
            Ok(0b10 | ((sub as u16) << TYPE_BITS) | (idx << (TYPE_BITS + LDC_SUB_BITS)))
        }
        OperandLine::Special { desc } => {
            if (desc as u32) >= MAX_DESC { return Err(EncodeError::DescOutOfRange(desc)); }
            Ok(0b11 | (desc << TYPE_BITS))
        }
    }
}

pub fn unpack_operand(lane: u16) -> Result<OperandLine, DecodeError> {
    match lane & TYPE_MASK {
        0b00 => Ok(OperandLine::Global {
            slot: ((lane >> TYPE_BITS) & ((1 << SLOT_BITS) - 1)) as u8,
            col: lane >> (TYPE_BITS + SLOT_BITS),
        }),
        0b01 => Ok(OperandLine::Smem { cell: (lane >> TYPE_BITS) & ((1 << CELL_BITS) - 1) }),
        0b10 => {
            let sub = match (lane >> TYPE_BITS) & 0b11 {
                0 => LdcSub::Const, 1 => LdcSub::ConstChallenge, 2 => LdcSub::ArgChallenge, _ => LdcSub::Special,
            };
            Ok(OperandLine::Ldc { sub, idx: lane >> (TYPE_BITS + LDC_SUB_BITS) })
        }
        _ => Ok(OperandLine::Special { desc: lane >> TYPE_BITS }),
    }
}

pub fn pack_dst(d: DstLine) -> Result<u16, EncodeError> {
    match d {
        DstLine::Smem { cell } => {
            if (cell as u32) >= MAX_CELL { return Err(EncodeError::CellOutOfRange(cell)); }
            Ok(cell << 1)
        }
        DstLine::GlobalMaterialize { slot, col } => {
            if (slot as u32) >= MAX_SLOTS { return Err(EncodeError::SlotOutOfRange(slot)); }
            if (col as u32) >= MAX_COLS { return Err(EncodeError::ColOutOfRange(col)); }
            Ok(0b1 | ((slot as u16) << 1) | (col << (1 + SLOT_BITS)))
        }
    }
}

pub fn unpack_dst(lane: u16) -> Result<DstLine, DecodeError> {
    if lane & 1 == 0 {
        Ok(DstLine::Smem { cell: (lane >> 1) & ((1 << CELL_BITS) - 1) })
    } else {
        Ok(DstLine::GlobalMaterialize {
            slot: ((lane >> 1) & ((1 << SLOT_BITS) - 1)) as u8,
            col: lane >> (1 + SLOT_BITS),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn operand_roundtrip_all_variants() {
        for c in [
            OperandLine::Global { slot: 15, col: 1023 },
            OperandLine::Smem { cell: 12 },
            OperandLine::Ldc { sub: LdcSub::ArgChallenge, idx: 4095 },
            OperandLine::Ldc { sub: LdcSub::Special, idx: Special::NegOne as u16 },
            OperandLine::Special { desc: 16383 },
        ] { assert_eq!(unpack_operand(pack_operand(c).unwrap()).unwrap(), c); }
    }
    #[test]
    fn dst_roundtrip_both_kinds() {
        for d in [DstLine::Smem { cell: 8 }, DstLine::GlobalMaterialize { slot: 3, col: 100 }] {
            assert_eq!(unpack_dst(pack_dst(d).unwrap()).unwrap(), d);
        }
    }
    #[test]
    fn cap_guards_reject_out_of_range() {
        assert_eq!(pack_operand(OperandLine::Global { slot: 16, col: 0 }), Err(EncodeError::SlotOutOfRange(16)));
        assert_eq!(pack_operand(OperandLine::Global { slot: 0, col: 1024 }), Err(EncodeError::ColOutOfRange(1024)));
        assert_eq!(pack_operand(OperandLine::Ldc { sub: LdcSub::Const, idx: 4096 }), Err(EncodeError::LdcIdxOutOfRange(4096)));
    }
}

fn pack_arith_header(op: Opcode, arity: usize, f0: OperandField, f1: OperandField, sign: Sign) -> Result<u16, EncodeError> {
    if arity == 0 || arity > MAX_ARITY { return Err(EncodeError::ArityOutOfRange(arity)); }
    Ok((op as u16) | ((arity as u16) << 2) | ((f0 as u16) << 9) | ((f1 as u16) << 10) | ((sign as u16) << 12))
}

pub fn encode(p: &Program) -> Result<Vec<u16>, EncodeError> {
    let mut out = Vec::new();
    for instr in &p.instrs {
        match instr {
            Instr::Add { field, sign, operands } => {
                out.push(pack_arith_header(Opcode::Add, operands.len(), *field, OperandField::Base, *sign)?);
                for o in operands { out.push(pack_operand(*o)?); }
            }
            Instr::Mul { field, operands } => {
                out.push(pack_arith_header(Opcode::Mul, operands.len(), *field, OperandField::Base, Sign::Plus)?);
                for o in operands { out.push(pack_operand(*o)?); }
            }
            Instr::Fma { field_lhs, field_rhs, sign, pairs } => {
                if *field_lhs == OperandField::Ext && *field_rhs == OperandField::Base {
                    return Err(EncodeError::NonCanonicalFmaOrder);
                }
                out.push(pack_arith_header(Opcode::Fma, pairs.len(), *field_lhs, *field_rhs, *sign)?);
                for (l, r) in pairs { out.push(pack_operand(*l)?); out.push(pack_operand(*r)?); }
            }
            Instr::Mov { dir, field, dst, src } => {
                out.push((Opcode::Mov as u16) | ((*dir as u16) << 2) | ((*field as u16) << 4));
                match dir {
                    MovDir::AccFromSrc => out.push(pack_operand(src.expect("AccFromSrc src"))?),
                    MovDir::DstFromAcc => out.push(pack_dst(dst.expect("DstFromAcc dst"))?),
                    MovDir::DstFromSrc => { out.push(pack_dst(dst.expect("DstFromSrc dst"))?); out.push(pack_operand(src.expect("DstFromSrc src"))?); }
                }
            }
        }
    }
    Ok(out)
}

pub fn decode(lanes: &[u16]) -> Result<Program, DecodeError> {
    let mut instrs = Vec::new();
    let mut i = 0usize;
    fn next(lanes: &[u16], i: &mut usize) -> Result<u16, DecodeError> {
        let v = *lanes.get(*i).ok_or(DecodeError::Truncated)?; *i += 1; Ok(v)
    }
    while i < lanes.len() {
        let h = next(lanes, &mut i)?;
        let op = h & 0b11;
        if op == Opcode::Mov as u16 {
            if (h >> 5) != 0 { return Err(DecodeError::NonZeroReserved); } // acc_sel + high bits
            let dir = match (h >> 2) & 0b11 { 0 => MovDir::AccFromSrc, 1 => MovDir::DstFromAcc, 2 => MovDir::DstFromSrc, d => return Err(DecodeError::BadMovDir(d)) };
            let field = if (h >> 4) & 1 == 1 { OperandField::Ext } else { OperandField::Base };
            let (dst, src) = match dir {
                MovDir::AccFromSrc => (None, Some(unpack_operand(next(lanes, &mut i)?)?)),
                MovDir::DstFromAcc => (Some(unpack_dst(next(lanes, &mut i)?)?), None),
                MovDir::DstFromSrc => { let d = unpack_dst(next(lanes, &mut i)?)?; (Some(d), Some(unpack_operand(next(lanes, &mut i)?)?)) }
            };
            instrs.push(Instr::Mov { dir, field, dst, src });
            continue;
        }
        if (h >> 11) & 1 == 1 { return Err(DecodeError::PromoteSet); }
        if (h >> 13) != 0 { return Err(DecodeError::NonZeroReserved); }
        let arity = ((h >> 2) & 0x7f) as usize;
        if arity == 0 { return Err(DecodeError::ZeroArity); }
        let f0 = if (h >> 9) & 1 == 1 { OperandField::Ext } else { OperandField::Base };
        let f1 = if (h >> 10) & 1 == 1 { OperandField::Ext } else { OperandField::Base };
        let sign = if (h >> 12) & 1 == 1 { Sign::Minus } else { Sign::Plus };
        match op {
            x if x == Opcode::Add as u16 => {
                if f1 != OperandField::Base { return Err(DecodeError::NonCanonicalField); }
                let operands = (0..arity).map(|_| unpack_operand(next(lanes, &mut i)?)).collect::<Result<_,_>>()?;
                instrs.push(Instr::Add { field: f0, sign, operands });
            }
            x if x == Opcode::Mul as u16 => {
                if f1 != OperandField::Base { return Err(DecodeError::NonCanonicalField); }
                if sign != Sign::Plus { return Err(DecodeError::NonCanonicalSign); }
                let operands = (0..arity).map(|_| unpack_operand(next(lanes, &mut i)?)).collect::<Result<_,_>>()?;
                instrs.push(Instr::Mul { field: f0, operands });
            }
            _ => { // Fma
                // Mixed FMA is canonical (Base, Ext); EB is the swapped duplicate — reject it.
                if f0 == OperandField::Ext && f1 == OperandField::Base { return Err(DecodeError::NonCanonicalField); }
                let mut pairs = Vec::with_capacity(arity);
                for _ in 0..arity { let l = unpack_operand(next(lanes, &mut i)?)?; let r = unpack_operand(next(lanes, &mut i)?)?; pairs.push((l, r)); }
                instrs.push(Instr::Fma { field_lhs: f0, field_rhs: f1, sign, pairs });
            }
        }
    }
    Ok(Program { instrs })
}

#[cfg(test)]
mod header_tests {
    use super::*;
    fn sample() -> Program {
        Program { instrs: vec![
            Instr::Mov { dir: MovDir::AccFromSrc, field: OperandField::Base, dst: None, src: Some(OperandLine::Global { slot: 0, col: 0 }) },
            Instr::Add { field: OperandField::Base, sign: Sign::Plus, operands: vec![OperandLine::Global { slot: 0, col: 1 }, OperandLine::Smem { cell: 4 }] },
            Instr::Mul { field: OperandField::Ext, operands: vec![OperandLine::Ldc { sub: LdcSub::Special, idx: Special::NegOne as u16 }] },
            Instr::Fma { field_lhs: OperandField::Base, field_rhs: OperandField::Ext, sign: Sign::Minus, pairs: vec![(OperandLine::Global { slot: 1, col: 2 }, OperandLine::Ldc { sub: LdcSub::ConstChallenge, idx: 1 })] }, // canonical mixed (Base,Ext)
            Instr::Mov { dir: MovDir::DstFromAcc, field: OperandField::Ext, dst: Some(DstLine::Smem { cell: 0 }), src: None },
            Instr::Mov { dir: MovDir::DstFromSrc, field: OperandField::Base, dst: Some(DstLine::GlobalMaterialize { slot: 2, col: 5 }), src: Some(OperandLine::Global { slot: 0, col: 9 }) },
        ] }
    }
    #[test] fn full_program_roundtrip() { let p = sample(); assert_eq!(decode(&encode(&p).unwrap()).unwrap(), p); }
    #[test] fn rejects_promote() { let h = (Opcode::Add as u16) | (1 << 2) | (1 << 11); assert_eq!(decode(&[h, 0]), Err(DecodeError::PromoteSet)); }
    #[test] fn rejects_mov_reserved() { assert_eq!(decode(&[(Opcode::Mov as u16) | (1 << 5), 0]), Err(DecodeError::NonZeroReserved)); }
    #[test] fn rejects_add_field1() { let h = (Opcode::Add as u16) | (1 << 2) | (1 << 10); assert_eq!(decode(&[h, 0]), Err(DecodeError::NonCanonicalField)); }
    #[test] fn rejects_mul_sign() { let h = (Opcode::Mul as u16) | (1 << 2) | (1 << 12); assert_eq!(decode(&[h, 0]), Err(DecodeError::NonCanonicalSign)); }
    #[test] fn rejects_zero_arity() { assert_eq!(decode(&[Opcode::Add as u16]), Err(DecodeError::ZeroArity)); }
    #[test] fn rejects_eb_fma() { let h = (Opcode::Fma as u16) | (1 << 2) | (1 << 9); /* f0=Ext,f1=Base */ assert_eq!(decode(&[h, 0, 0]), Err(DecodeError::NonCanonicalField)); }
    #[test] fn encode_rejects_eb_fma_order() {
        // EB (Ext,Base) is the non-canonical duplicate of canonical BE (Base,Ext).
        // encode must reject it so the compiler can never produce a bytestream decode refuses.
        let eb_fma = Instr::Fma {
            field_lhs: OperandField::Ext,
            field_rhs: OperandField::Base,
            sign: Sign::Plus,
            pairs: vec![(OperandLine::Global { slot: 0, col: 0 }, OperandLine::Global { slot: 0, col: 1 })],
        };
        assert_eq!(
            encode(&Program { instrs: vec![eb_fma] }),
            Err(EncodeError::NonCanonicalFmaOrder),
        );
        // Canonical BE (Base,Ext) must still encode Ok and round-trip.
        let p = sample();
        assert!(p.instrs.iter().any(|i| matches!(i, Instr::Fma { field_lhs: OperandField::Base, field_rhs: OperandField::Ext, .. })),
            "sample() must include a canonical BE FMA for this assertion to be meaningful");
        assert_eq!(decode(&encode(&p).unwrap()).unwrap(), p);
    }
    #[test] fn rejects_truncated() { let h = pack_arith_header(Opcode::Add, 2, OperandField::Base, OperandField::Base, Sign::Plus).unwrap(); assert_eq!(decode(&[h, 0]), Err(DecodeError::Truncated)); }
}
