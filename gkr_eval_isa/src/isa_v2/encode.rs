//! ISA-v2 lane encoding (spec §5). Regular decode: header → operands → footer
//! dst(s); arity/routine fixes every lane boundary. No sentinels, no payload.

use super::*;

fn pack_operand(o: &Operand) -> u16 {
    match *o {
        Operand::Affine { slot, col } => {
            debug_assert!((slot as u32) < (1 << MATRIX_SLOT_BITS));
            debug_assert!((col as u32) < (1 << COL_BITS));
            0u16 | ((slot as u16) << 2) | ((col) << (2 + MATRIX_SLOT_BITS))
        }
        Operand::Slot { e4, cell } => {
            debug_assert!((cell as u32) < (1 << SLOT_CELL_BITS));
            0b01 | ((e4 as u16) << 2) | ((cell as u16) << 3)
        }
        Operand::Ldc { sub, idx } => {
            debug_assert!((idx as u32) < (1 << LDC_IDX_BITS));
            0b10 | ((sub as u16) << 2) | (idx << (2 + LDC_SUB_BITS))
        }
        Operand::Indirect { e4, desc } => {
            debug_assert!((desc as u32) < (1 << GATHER_DESC_BITS));
            0b11 | ((e4 as u16) << 2) | (desc << 3)
        }
    }
}

fn unpack_operand(l: u16) -> Operand {
    match l & 0b11 {
        0 => Operand::Affine {
            slot: ((l >> 2) & ((1 << MATRIX_SLOT_BITS) - 1)) as u8,
            col: l >> (2 + MATRIX_SLOT_BITS),
        },
        1 => Operand::Slot { e4: (l >> 2) & 1 == 1, cell: (l >> 3) as u8 },
        2 => Operand::Ldc {
            sub: match (l >> 2) & 0b11 {
                0 => LdcSub::Const,
                1 => LdcSub::ConstChallenge,
                2 => LdcSub::ArgChallenge,
                _ => LdcSub::Special,
            },
            idx: l >> (2 + LDC_SUB_BITS),
        },
        _ => Operand::Indirect { e4: (l >> 2) & 1 == 1, desc: l >> 3 },
    }
}

fn pack_dst(d: &Dst) -> u16 {
    match *d {
        Dst::Slot { e4, cell } => 0u16 | ((e4 as u16) << 1) | ((cell as u16) << 2),
        Dst::Materialize { slot, col } => {
            1u16 | ((slot as u16) << 1) | (col << (1 + MATRIX_SLOT_BITS))
        }
    }
}

fn unpack_dst(l: u16) -> Dst {
    if l & 1 == 0 {
        Dst::Slot { e4: (l >> 1) & 1 == 1, cell: (l >> 2) as u8 }
    } else {
        Dst::Materialize {
            slot: ((l >> 1) & ((1 << MATRIX_SLOT_BITS) - 1)) as u8,
            col: l >> (1 + MATRIX_SLOT_BITS),
        }
    }
}

pub fn encode2(p: &Program2) -> Vec<u16> {
    let mut lanes = Vec::new();
    for ins in &p.instrs {
        match ins.header {
            Header::Arith { op, arity } => {
                assert!((arity as u32) <= MAX_ARITY, "arity {arity} exceeds 7-bit cap");
                // family=0 | op:2 (bits 1..3) | arity:7 (bits 3..10)
                lanes.push(0u16 | ((op as u16) << 1) | ((arity as u16) << 3));
            }
            Header::Macro { routine } => {
                assert!(routine <= MAX_ROUTINE_ID, "routine-id over 127");
                // family=1 | routine:7 (bits 1..8)
                lanes.push(1u16 | ((routine as u16) << 1));
            }
        }
        // Operand region: shape decides whether a count lane precedes operands.
        //  - Arith / Fixed macro: NO count lane (count is the header arity / the
        //    routine schema's Fixed(n)).
        //  - Variable macro: a single count lane, then `count` operands.
        //  - MemTuple macro: a (count:4 | as_arm:2) lane, role-tagged operands,
        //    optional as_payload lane.
        match &ins.header {
            Header::Macro { routine } if ins.memtup.is_some() => {
                let mt = ins.memtup.as_ref().unwrap();
                debug_assert_eq!(routine_table()[*routine as usize].shape, super::routines::Shape::MemTuple);
                assert!(mt.roles.len() <= 8, "memory-tuple over 8 linear terms");
                lanes.push((mt.roles.len() as u16) | ((mt.as_arm as u16) << 4));
                for (role, op) in &mt.roles {
                    lanes.push(*role as u16);
                    lanes.push(pack_operand(op));
                }
                if let Some(p) = &mt.as_payload {
                    lanes.push(pack_operand(p));
                }
            }
            Header::Macro { routine } => {
                match routine_table()[*routine as usize].shape {
                    super::routines::Shape::Variable => {
                        assert!(ins.operands.len() <= 0x3FFF, "macro operand count overflow");
                        lanes.push(ins.operands.len() as u16); // count lane
                    }
                    super::routines::Shape::Fixed(n) => {
                        assert_eq!(ins.operands.len(), n as usize, "Fixed macro arity mismatch");
                    }
                    super::routines::Shape::MemTuple => unreachable!("MemTuple needs memtup"),
                }
                for o in &ins.operands {
                    lanes.push(pack_operand(o));
                }
            }
            Header::Arith { .. } => {
                for o in &ins.operands {
                    lanes.push(pack_operand(o));
                }
            }
        }
        for d in &ins.dsts {
            lanes.push(pack_dst(d));
        }
    }
    lanes
}

pub fn decode2(lanes: &[u16], n_instr: usize) -> Vec<Instr2> {
    use super::routines::routine_table;
    use super::routines::Shape;

    let mut pos = 0;
    let mut instrs = Vec::with_capacity(n_instr);

    for _ in 0..n_instr {
        let header_lane = lanes[pos];
        pos += 1;

        // Bit 0 = family: 0 → Arith, 1 → Macro.
        let header = if header_lane & 1 == 0 {
            // Arith: bits 1-2 = op, bits 3-9 = arity.
            let op = match (header_lane >> 1) & 0b11 {
                0 => ArithOp::Sum,
                1 => ArithOp::Prod,
                2 => ArithOp::Dot,
                _ => ArithOp::Fma,
            };
            let arity = (header_lane >> 3) as u8;
            Header::Arith { op, arity }
        } else {
            // Macro: bits 1-7 = routine.
            let routine = ((header_lane >> 1) & 0x7F) as u8;
            Header::Macro { routine }
        };

        let (operands, memtup, dst_count) = match header {
            Header::Arith { op, arity } => {
                // Dot uses 2*arity operand lanes; all others use arity.
                let n_ops = if matches!(op, ArithOp::Dot) {
                    2 * arity as usize
                } else {
                    arity as usize
                };
                let ops: Vec<Operand> = (0..n_ops).map(|_| {
                    let o = unpack_operand(lanes[pos]);
                    pos += 1;
                    o
                }).collect();
                (ops, None, 1usize)
            }
            Header::Macro { routine } => {
                let schema = &routine_table()[routine as usize];
                match schema.shape {
                    Shape::Fixed(n) => {
                        let ops: Vec<Operand> = (0..n as usize).map(|_| {
                            let o = unpack_operand(lanes[pos]);
                            pos += 1;
                            o
                        }).collect();
                        (ops, None, schema.output_count as usize)
                    }
                    Shape::Variable => {
                        // count lane first.
                        let count = lanes[pos] as usize;
                        pos += 1;
                        let ops: Vec<Operand> = (0..count).map(|_| {
                            let o = unpack_operand(lanes[pos]);
                            pos += 1;
                            o
                        }).collect();
                        (ops, None, schema.output_count as usize)
                    }
                    Shape::MemTuple => {
                        // count+as_arm lane: bits 3-0 = count, bits 5-4 = as_arm.
                        let count_arm_lane = lanes[pos];
                        pos += 1;
                        let count = (count_arm_lane & 0xF) as usize;
                        let as_arm = ((count_arm_lane >> 4) & 0x3) as u8;

                        let mut roles = Vec::with_capacity(count);
                        for _ in 0..count {
                            let role = lanes[pos] as u8;
                            pos += 1;
                            let op = unpack_operand(lanes[pos]);
                            pos += 1;
                            roles.push((role, op));
                        }

                        // as_payload present if as_arm != 0 (i.e., arm is not Empty).
                        let as_payload = if as_arm != 0 {
                            let p = unpack_operand(lanes[pos]);
                            pos += 1;
                            Some(p)
                        } else {
                            None
                        };

                        let mt = MemTup { roles, as_arm, as_payload };
                        (vec![], Some(mt), schema.output_count as usize)
                    }
                }
            }
        };

        // Footer dst lanes.
        let dsts: Vec<Dst> = (0..dst_count).map(|_| {
            let d = unpack_dst(lanes[pos]);
            pos += 1;
            d
        }).collect();

        instrs.push(Instr2 { header, operands, dsts, memtup });
    }

    instrs
}
