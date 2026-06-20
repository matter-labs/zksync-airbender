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
