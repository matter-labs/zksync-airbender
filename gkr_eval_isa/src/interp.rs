//! CPU reference interpreter. bf-granular state per spec §4; e4 values are
//! 4 consecutive bf cells, lifted to BabyBearExt4 for arithmetic.

use crate::eval_ref::{Bf, Ext, lift};
use crate::isa::{Dst, Op, Operand, Program};
use field::{Field, FieldExtension, PrimeField};

/// Staged post-fold source values, per-domain id namespaces.
pub struct StagedSources {
    pub bf: Vec<Bf>,
    pub e4: Vec<Ext>,
}

pub struct ExecResult {
    /// Indexed by ORIGINAL output-slot index; None = native-stored (or never
    /// written — the oracle distinguishes by the program_outputs list).
    pub outputs: Vec<Option<Ext>>,
    /// Indexed by gate-in staging index.
    pub gate_ins: Vec<Option<Ext>>,
}

fn read_cells(cells: &[Bf], cell: u16, e4: bool) -> Ext {
    let c = cell as usize;
    if e4 {
        <Ext as FieldExtension<Bf>>::from_coeffs([
            cells[c], cells[c + 1], cells[c + 2], cells[c + 3],
        ])
    } else {
        lift(cells[c])
    }
}

fn write_cells(cells: &mut [Bf], cell: u16, e4: bool, v: Ext) {
    let c = cell as usize;
    let coeffs = <Ext as FieldExtension<Bf>>::into_coeffs(v);
    if e4 {
        cells[c..c + 4].copy_from_slice(&coeffs);
    } else {
        debug_assert!(
            coeffs[1].is_zero() && coeffs[2].is_zero() && coeffs[3].is_zero(),
            "bf-result instruction produced a non-base value — compiler domain bug"
        );
        cells[c] = coeffs[0];
    }
}

pub fn execute(p: &Program, src: &StagedSources) -> ExecResult {
    let mut slots = vec![Bf::ZERO; p.n_slot_cells as usize];
    let mut fixed = vec![Bf::ZERO; p.n_fixed_cells as usize];
    let mut outputs: Vec<Option<Ext>> = vec![None; p.n_outputs as usize];
    let mut gate_ins: Vec<Option<Ext>> = vec![None; p.n_gate_ins as usize];

    for ins in &p.instrs {
        let read = |o: &Operand| -> Ext {
            match *o {
                Operand::Source { id, e4 } => {
                    if e4 { src.e4[id as usize] } else { lift(src.bf[id as usize]) }
                }
                Operand::Slot { cell, e4 } => read_cells(&slots, cell, e4),
                Operand::FixedReg { cell, e4 } => read_cells(&fixed, cell, e4),
                Operand::Const { idx } => {
                    lift(Bf::from_u32_with_reduction(p.consts[idx as usize]))
                }
                Operand::Zero => Ext::ZERO,
                Operand::One => Ext::ONE,
                Operand::NegOne => {
                    let mut v = Ext::ONE;
                    v.negate();
                    v
                }
            }
        };

        let acc = match ins.op {
            Op::SumK => {
                let mut a = Ext::ZERO;
                for o in &ins.operands {
                    let v = read(o);
                    a.add_assign(&v);
                }
                a
            }
            Op::ProdK => {
                let mut a = Ext::ONE;
                for o in &ins.operands {
                    let v = read(o);
                    a.mul_assign(&v);
                }
                a
            }
            Op::DotK => {
                let mut a = Ext::ZERO;
                for pair in ins.operands.chunks(2) {
                    let mut x = read(&pair[0]);
                    let y = read(&pair[1]);
                    x.mul_assign(&y);
                    a.add_assign(&x);
                }
                a
            }
            Op::NativeK => unreachable!("NativeK execution lands in the next task"),
        };

        match ins.dst {
            Dst::Slot(cell) => write_cells(&mut slots, cell, ins.e4_result, acc),
            Dst::FixedReg(cell) => write_cells(&mut fixed, cell, ins.e4_result, acc),
            Dst::Output(j) => outputs[j as usize] = Some(acc),
            Dst::GateIn(i) => gate_ins[i as usize] = Some(acc),
            Dst::Native => unreachable!("Dst::Native is NativeK-only"),
        }
    }
    ExecResult { outputs, gate_ins }
}
