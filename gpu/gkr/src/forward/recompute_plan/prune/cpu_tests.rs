use super::*;
use gpu_gkr_compiler::ForwardSign;

fn prune(instructions: &[Instr]) -> Vec<Instr> {
    let mut acc = false;
    let mut cells = BTreeSet::new();
    let mut kept: Vec<_> = instructions
        .iter()
        .rev()
        .filter(|instruction| {
            keep_instruction(instruction, &mut acc, &mut cells, |_, col| col == 0)
        })
        .cloned()
        .collect();
    kept.reverse();
    kept
}

fn load(field: Field, src: Operand) -> Instr {
    Instr::Mov {
        dir: Mov::AccFromSrc,
        field,
        dst: None,
        src: Some(src),
    }
}

fn store(field: Field, col: u16) -> Instr {
    Instr::Mov {
        dir: Mov::DstFromAcc,
        field,
        dst: Some(Dst::GlobalMaterialize { slot: 0, col }),
        src: None,
    }
}

fn source(column: u16) -> Operand {
    Operand::Source { window: 0, column }
}

fn write_cell(field: Field, cell: u16, column: u16) -> Instr {
    Instr::Mov {
        dir: Mov::DstFromSrc,
        field,
        dst: Some(Dst::Smem { cell }),
        src: Some(source(column)),
    }
}

#[test]
fn keeps_mid_chain_cache_and_drops_tail_and_overwritten_accumulator() {
    let instructions = vec![
        load(Field::Ext, source(0)),
        load(Field::Ext, source(1)),
        Instr::Add {
            field: Field::Base,
            sign: ForwardSign::Plus,
            operands: vec![source(2)],
        },
        store(Field::Ext, 0),
        Instr::Mul {
            field: Field::Base,
            negate_acc: true,
            operands: vec![],
        },
        store(Field::Ext, 1),
    ];
    assert_eq!(prune(&instructions), instructions[1..4]);
}

#[test]
fn shared_cells_track_overlapping_bf_and_e4_writes() {
    let instructions = vec![
        write_cell(Field::Base, 6, 0), // Overwritten by the E4 store.
        write_cell(Field::Ext, 1, 1),
        write_cell(Field::Base, 5, 2),
        write_cell(Field::Base, 4, 3),
        load(Field::Ext, Operand::Smem { cell: 1 }),
        store(Field::Ext, 0),
    ];
    assert_eq!(prune(&instructions), instructions[1..]);

    let instructions = vec![
        write_cell(Field::Ext, 1, 0),
        load(Field::Base, Operand::Smem { cell: 5 }),
        store(Field::Base, 0),
    ];
    assert_eq!(prune(&instructions), instructions);
}

#[test]
fn mixed_fma_and_direct_moves_preserve_their_sources() {
    let instructions = vec![
        load(Field::Ext, source(0)),
        Instr::Mov {
            dir: Mov::DstFromAcc,
            field: Field::Ext,
            dst: Some(Dst::Smem { cell: 1 }),
            src: None,
        },
        write_cell(Field::Base, 0, 1),
        write_cell(Field::Base, 12, 2), // Dead cell, independent of the live accumulator.
        load(Field::Ext, source(3)),
        Instr::Fma {
            field_lhs: Field::Base,
            field_rhs: Field::Ext,
            sign: ForwardSign::Minus,
            pairs: vec![(Operand::Smem { cell: 0 }, Operand::Smem { cell: 1 })],
        },
        Instr::Mul {
            field: Field::Ext,
            negate_acc: true,
            operands: vec![],
        },
        store(Field::Ext, 0),
        load(Field::Ext, source(4)),
        store(Field::Ext, 1),
    ];
    let expected: Vec<_> = instructions[..8]
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != 3)
        .map(|(_, i)| i.clone())
        .collect();
    assert_eq!(prune(&instructions), expected);

    let direct = vec![
        load(Field::Ext, source(0)),
        write_cell(Field::Ext, 1, 1),
        Instr::Mov {
            dir: Mov::DstFromSrc,
            field: Field::Ext,
            dst: Some(Dst::GlobalMaterialize { slot: 0, col: 0 }),
            src: Some(Operand::Smem { cell: 1 }),
        },
    ];
    assert_eq!(prune(&direct), direct[1..]);
}
