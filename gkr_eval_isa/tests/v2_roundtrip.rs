use gkr_eval_isa::isa_v2::encode::{decode2, encode2};
use gkr_eval_isa::isa_v2::*;

#[test]
fn roundtrip_all_layouts() {
    let instrs = vec![
        // arith: header + 3 operands + 1 footer dst
        Instr2 {
            header: Header::Arith { op: ArithOp::Dot, arity: 2 },
            operands: vec![
                Operand::Affine { slot: 0, col: 645 },
                Operand::Ldc { sub: LdcSub::Const, idx: 7 },
                Operand::Slot { e4: true, cell: 12 },
                Operand::Ldc { sub: LdcSub::Special, idx: SPECIAL_NEG_ONE },
            ],
            dsts: vec![Dst::Slot { e4: false, cell: 3 }],
            memtup: None,
            memtup2: None,
        },
        // macro-plain: header (n_operands=2) + 2 operands + 2 footer dsts.
        // LookupExtPair is Shape::Plain (a num/den lookup pair, output_count 2);
        // the operand count rides the header, so there is NO count lane — the 2
        // operand lanes follow the header directly.
        Instr2 {
            header: Header::Macro { routine: RoutineId::LookupExtPair as u8, n_operands: 2 },
            operands: vec![
                Operand::Indirect { e4: true, desc: 4 },
                Operand::Ldc { sub: LdcSub::ConstChallenge, idx: 0 },
            ],
            dsts: vec![
                Dst::Materialize { slot: 1, col: 10 },
                Dst::Materialize { slot: 1, col: 11 },
            ],
            memtup: None,
            memtup2: None,
        },
        // macro-memtup: header (n_operands = role count) + as_arm lane +
        // role-tagged ops + as_payload + R2 folded-const block + dst.
        // MemoryTuple is Shape::MemTuple.
        Instr2 {
            header: Header::Macro { routine: RoutineId::MemoryTuple as u8, n_operands: 2 },
            operands: vec![],
            dsts: vec![Dst::Materialize { slot: 2, col: 0 }],
            memtup: Some(MemTup {
                roles: vec![
                    (0, Operand::Affine { slot: 0, col: 1 }),
                    (2, Operand::Affine { slot: 0, col: 2 }),
                ],
                as_arm: 3, // IsRam
                as_payload: Some(Operand::Affine { slot: 3, col: 0 }),
                // R2 folded constants: (role, Ldc value) pairs must round-trip.
                consts: vec![
                    (MT_CONST_ADDR_LOW, Operand::Ldc { sub: LdcSub::Const, idx: 5 }),
                    (MT_CONST_TS_LOW_OFFSET, Operand::Ldc { sub: LdcSub::Special, idx: 0 }),
                ],
            }),
            memtup2: None,
        },
        // macro-memtup product-of-two-tuples (id-14 GrandProductWithoutCaches):
        // BOTH memtup + memtup2 populated with DISTINCT role sets and as_arms.
        // The header carries the SUM of role counts (2 + 1); each tuple block is
        // self-described by a leading role-count lane, so it must round-trip.
        Instr2 {
            header: Header::Macro {
                routine: RoutineId::GrandProductWithoutCaches as u8,
                n_operands: 3,
            },
            operands: vec![],
            dsts: vec![Dst::Materialize { slot: 2, col: 7 }],
            memtup: Some(MemTup {
                roles: vec![
                    (0, Operand::Affine { slot: 0, col: 3 }),
                    (1, Operand::Affine { slot: 0, col: 4 }),
                ],
                as_arm: 1, // Constant
                as_payload: Some(Operand::Ldc { sub: LdcSub::Special, idx: SPECIAL_ONE }),
                consts: vec![
                    (MT_CONST_ADDR_HIGH, Operand::Ldc { sub: LdcSub::Const, idx: 9 }),
                ],
            }),
            memtup2: Some(MemTup {
                roles: vec![(2, Operand::Affine { slot: 1, col: 6 })],
                as_arm: 0, // Empty
                as_payload: None,
                consts: vec![],
            }),
        },
    ];
    let p = Program2 { instrs: instrs.clone(), ..Default::default() };
    let lanes = encode2(&p);
    assert_eq!(decode2(&lanes, instrs.len()), instrs);
}

#[test]
#[should_panic(expected = "arity")]
fn arity_over_127_rejected() {
    let p = Program2 {
        instrs: vec![Instr2 {
            header: Header::Arith { op: ArithOp::Sum, arity: 200 },
            operands: vec![Operand::Slot { e4: false, cell: 0 }; 200],
            dsts: vec![Dst::Slot { e4: false, cell: 0 }],
            memtup: None,
            memtup2: None,
        }],
        ..Default::default()
    };
    let _ = encode2(&p);
}
