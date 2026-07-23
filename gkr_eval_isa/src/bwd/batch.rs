use crate::fwd::isa::DstLine;

pub const BATCH_COEFFICIENT_MAX: u16 = 0x3ffe;
pub const BATCH_COEFFICIENT_ONE: u16 = 0x3fff;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BatchDstError {
    IdOutOfRange(u16),
}

pub fn pack_batch_dst(id: u16) -> Result<DstLine, BatchDstError> {
    if id > BATCH_COEFFICIENT_ONE {
        return Err(BatchDstError::IdOutOfRange(id));
    }

    Ok(DstLine::GlobalMaterialize {
        slot: (id & 0x000f) as u8,
        col: id >> 4,
    })
}

pub fn unpack_batch_dst(dst: &DstLine) -> Option<u16> {
    match dst {
        DstLine::GlobalMaterialize { slot, col } => Some((*slot as u16) | (*col << 4)),
        DstLine::Smem { .. } => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{pack_batch_dst, unpack_batch_dst};
    use crate::fwd::{
        encode::{decode, encode},
        isa::{DstLine, Instr, MovDir, OperandField, Program},
    };

    #[test]
    fn batch_destinations_roundtrip_the_complete_fourteen_bit_payload() {
        for id in [0, 0x000f, 0x0010, 0x3ffe, 0x3fff] {
            let dst = pack_batch_dst(id).unwrap();
            assert_eq!(
                dst,
                DstLine::GlobalMaterialize {
                    slot: (id & 0x000f) as u8,
                    col: id >> 4,
                }
            );

            let program = Program {
                instrs: vec![Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: OperandField::Ext,
                    dst: Some(dst),
                    src: None,
                }],
            };
            let decoded = decode(&encode(&program).unwrap()).unwrap();
            let Instr::Mov { dst: Some(dst), .. } = &decoded.instrs[0] else {
                panic!("expected DstFromAcc instruction");
            };
            assert_eq!(unpack_batch_dst(dst), Some(id));
        }
    }

    #[test]
    fn batch_destination_rejects_values_above_fourteen_bits() {
        assert!(pack_batch_dst(0x4000).is_err());
    }

    #[test]
    fn smem_destination_is_not_a_batch_destination() {
        assert_eq!(unpack_batch_dst(&DstLine::Smem { cell: 0 }), None);
    }
}
