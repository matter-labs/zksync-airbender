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

/// Encode one memory-tuple side-block: as_arm lane (2 bits), then `roles.len()`
/// role-tagged `(role, operand)` pairs, an optional as_payload lane (present iff
/// as_arm != 0), then the R2 folded-constant block (a count lane + `(role,
/// value)` pairs). Self-described: `decode_memtup` mirrors this exactly.
fn encode_memtup(mt: &MemTup, lanes: &mut Vec<u16>) {
    assert!(mt.roles.len() <= 8, "memory-tuple over 8 linear terms");
    lanes.push(mt.as_arm as u16); // as_arm only (2 bits)
    for (role, op) in &mt.roles {
        lanes.push(*role as u16);
        lanes.push(pack_operand(op));
    }
    if let Some(p) = &mt.as_payload {
        lanes.push(pack_operand(p));
    }
    // R2 folded-constant block: count lane, then (role, value) pairs.
    lanes.push(mt.consts.len() as u16);
    for (role, op) in &mt.consts {
        lanes.push(*role as u16);
        lanes.push(pack_operand(op));
    }
}

/// Decode one memory-tuple side-block. `n_roles` is the role count (from the
/// header for the primary `memtup`; from this block's own leading count for
/// `memtup2`). Advances `pos` past the whole block.
fn decode_memtup(lanes: &[u16], pos: &mut usize, n_roles: usize) -> MemTup {
    let as_arm = (lanes[*pos] & 0x3) as u8;
    *pos += 1;

    let mut roles = Vec::with_capacity(n_roles);
    for _ in 0..n_roles {
        let role = lanes[*pos] as u8;
        *pos += 1;
        let op = unpack_operand(lanes[*pos]);
        *pos += 1;
        roles.push((role, op));
    }

    let as_payload = if as_arm != 0 {
        let p = unpack_operand(lanes[*pos]);
        *pos += 1;
        Some(p)
    } else {
        None
    };

    let n_consts = lanes[*pos] as usize;
    *pos += 1;
    let mut consts = Vec::with_capacity(n_consts);
    for _ in 0..n_consts {
        let role = lanes[*pos] as u8;
        *pos += 1;
        let op = unpack_operand(lanes[*pos]);
        *pos += 1;
        consts.push((role, op));
    }

    MemTup { roles, as_arm, as_payload, consts }
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

/// Lane COUNT for a program, without packing (so it never trips the
/// width debug-asserts in `pack_operand`/`pack_dst`). Used for the compiler's
/// stats `lanes`/`bytes` estimate, where only the count matters and a program
/// may legitimately exceed a single field's bit budget (e.g. a base-arith layer
/// with >127 live slot cells — a real ISA-width finding, separate from
/// macro lowering). The arithmetic mirrors `encode2`'s lane layout exactly.
/// Lane count of ONE memory-tuple side-block (as_arm + role pairs + optional
/// payload + the folded-constant count lane and its pairs). Shared by both
/// `memtup` and `memtup2`.
fn memtup_lane_count(mt: &MemTup) -> usize {
    let mut n = 1; // as_arm lane
    n += 2 * mt.roles.len(); // role + operand per term
    if mt.as_payload.is_some() {
        n += 1;
    }
    n += 1; // n_consts lane
    n += 2 * mt.consts.len();
    n
}

pub fn lane_count(p: &Program2) -> usize {
    let mut n = 0usize;
    for ins in &p.instrs {
        n += 1; // header lane
        match &ins.header {
            Header::Macro { routine, .. } if ins.memtup.is_some() => {
                let mt = ins.memtup.as_ref().unwrap();
                let two = super::routines::routine_is_two_tuples(*routine);
                if two {
                    n += 1; // leading role-count lane for the primary tuple
                }
                n += memtup_lane_count(mt);
                // memtup2 presence lane (always emitted for memtup-carrying
                // instrs), then the second tuple's own block when present.
                n += 1; // memtup2 presence lane
                if let Some(mt2) = &ins.memtup2 {
                    n += 1; // leading role-count lane for the second tuple
                    n += memtup_lane_count(mt2);
                }
            }
            Header::Macro { .. } => {
                n += ins.operands.len();
            }
            Header::Arith { .. } => {
                n += ins.operands.len();
            }
        }
        n += ins.dsts.len();
    }
    n
}

pub fn encode2(p: &Program2) -> Vec<u16> {
    let mut lanes = Vec::new();
    for ins in &p.instrs {
        match ins.header {
            Header::Arith { op, arity } => {
                assert!((arity as u32) <= MAX_ARITY, "arity {arity} exceeds 7-bit cap");
                // family=0 (bit0) | op:2 (bits 1..3) | arity:7 (bits 3..10)
                lanes.push(0u16 | ((op as u16) << 1) | ((arity as u16) << 3));
            }
            Header::Macro { routine, n_operands } => {
                assert!(routine <= MAX_ROUTINE_ID, "routine-id over 127");
                assert!(n_operands <= 127, "macro n_operands {n_operands} exceeds 7-bit cap");
                // family=1 (bit0) | routine:7 (bits 1..8) | n_operands:7 (bits
                // 8..15); bit15 spare. The operand COUNT rides the header — there
                // is NO count lane.
                lanes.push(1u16 | ((routine as u16) << 1) | ((n_operands as u16) << 8));
            }
        }
        // Operand region: dispatch ONLY on the wire structure.
        //  - Arith / Plain macro: `n_operands` consecutive operand lanes (count
        //    lives in the header).
        //  - MemTuple macro: an as_arm lane (2 bits), then `n_operands`
        //    role-tagged `(role, operand)` pairs, then an optional as_payload
        //    lane (present iff as_arm != 0).
        match &ins.header {
            Header::Macro { routine, .. } if ins.memtup.is_some() => {
                let mt = ins.memtup.as_ref().unwrap();
                let two = super::routines::routine_is_two_tuples(*routine);
                debug_assert!(
                    super::routines::routine_carries_memtup(*routine),
                    "memtup carried only by memtup-shaped routines"
                );
                // Two-tuple routines (id-14, id-20) carry the SUM of both tuples'
                // role counts in the header, so each tuple block is self-described
                // by a leading role-count lane. Single-tuple routines (id-15,
                // id-19) recover the role count from the header `n_operands`.
                if two {
                    lanes.push(mt.roles.len() as u16);
                }
                encode_memtup(mt, &mut lanes);
                // memtup2 presence lane (0/1), then the second tuple's block when
                // present (product-of-two-tuples routines).
                lanes.push(ins.memtup2.is_some() as u16);
                if let Some(mt2) = &ins.memtup2 {
                    debug_assert!(two, "memtup2 only on product-of-two-tuples routines");
                    lanes.push(mt2.roles.len() as u16);
                    encode_memtup(mt2, &mut lanes);
                }
            }
            Header::Macro { .. } | Header::Arith { .. } => {
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
            // Macro: bits 1-7 = routine, bits 8-14 = n_operands (bit15 spare).
            let routine = ((header_lane >> 1) & 0x7F) as u8;
            let n_operands = ((header_lane >> 8) & 0x7F) as u8;
            Header::Macro { routine, n_operands }
        };

        let (operands, memtup, memtup2, dst_count) = match header {
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
                (ops, None, None, 1usize)
            }
            Header::Macro { routine, n_operands } => {
                let schema = &routine_table()[routine as usize];
                match schema.shape {
                    Shape::Plain => {
                        // `n_operands` (from the header) consecutive operand lanes.
                        let ops: Vec<Operand> = (0..n_operands as usize).map(|_| {
                            let o = unpack_operand(lanes[pos]);
                            pos += 1;
                            o
                        }).collect();
                        (ops, None, None, schema.output_count as usize)
                    }
                    Shape::MemTuple => {
                        // Mirror `encode2`: two-tuple routines (id-14, id-20) carry
                        // the SUM of both tuples' role counts in the header, so the
                        // primary tuple's own role count rides a leading lane;
                        // single-tuple routines recover it from `n_operands`.
                        let two = super::routines::routine_is_two_tuples(routine);
                        let n_roles_primary = if two {
                            let c = lanes[pos] as usize;
                            pos += 1;
                            c
                        } else {
                            n_operands as usize
                        };
                        let mt = decode_memtup(lanes, &mut pos, n_roles_primary);

                        // memtup2 presence lane (always emitted for memtup-carrying
                        // instrs), then the second tuple's block (own leading
                        // role-count lane) when present.
                        let has_two = lanes[pos] != 0;
                        pos += 1;
                        let memtup2 = if has_two {
                            let n_roles2 = lanes[pos] as usize;
                            pos += 1;
                            Some(decode_memtup(lanes, &mut pos, n_roles2))
                        } else {
                            None
                        };

                        (vec![], Some(mt), memtup2, schema.output_count as usize)
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

        instrs.push(Instr2 { header, operands, dsts, memtup, memtup2 });
    }

    instrs
}
