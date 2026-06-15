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
        },
        // macro-variable: header + count lane + 2 operands + 2 footer dsts.
        // LookupNumDen is Shape::Variable, so encode2 emits a count lane (=2).
        Instr2 {
            header: Header::Macro { routine: RoutineId::LookupNumDen as u8 },
            operands: vec![
                Operand::Indirect { e4: true, desc: 4 },
                Operand::Ldc { sub: LdcSub::ConstChallenge, idx: 0 },
            ],
            dsts: vec![
                Dst::Materialize { slot: 1, col: 10 },
                Dst::Materialize { slot: 1, col: 11 },
            ],
            memtup: None,
        },
        // macro-memtup: header + (count+as_arm) + role-tagged ops + as_payload + dst
        Instr2 {
            header: Header::Macro { routine: RoutineId::MemoryTuple as u8 },
            operands: vec![],
            dsts: vec![Dst::Materialize { slot: 2, col: 0 }],
            memtup: Some(MemTup {
                roles: vec![
                    (0, Operand::Affine { slot: 0, col: 1 }),
                    (2, Operand::Affine { slot: 0, col: 2 }),
                ],
                as_arm: 3, // IsRam
                as_payload: Some(Operand::Affine { slot: 3, col: 0 }),
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
        }],
        ..Default::default()
    };
    let _ = encode2(&p);
}
