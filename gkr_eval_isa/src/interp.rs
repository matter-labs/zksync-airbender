//! CPU reference interpreter. bf-granular state per spec §4; e4 values are
//! 4 consecutive bf cells, lifted to BabyBearExt4 for arithmetic.

use crate::eval_ref::{Bf, Ext, lift};
use crate::isa::{Dst, Op, Operand, Program};
use field::{Field, FieldExtension, PrimeField};

/// Staged post-fold source values, per-domain id namespaces.
pub struct StagedSources {
    pub bf: Vec<Bf>,
    pub e4: Vec<Ext>,
    /// CacheK sentinel outputs, indexed by cache index (PayloadMeta::cache).
    /// Empty for cone programs.
    pub cache_outs: Vec<Ext>,
}

/// One NativeK firing: which payload, and the operand values delivered.
#[derive(Clone, Debug, PartialEq)]
pub struct NativeFire {
    pub payload: u16,
    pub vals: Vec<Ext>,
}

pub struct ExecResult {
    /// Indexed by ORIGINAL output-slot index; None = native-stored (or never
    /// written — the oracle distinguishes by the program_outputs list).
    pub outputs: Vec<Option<Ext>>,
    /// Indexed by gate-in staging index.
    pub gate_ins: Vec<Option<Ext>>,
    /// NativeK firings in program order (the trace the oracle checks).
    pub native_trace: Vec<NativeFire>,
    /// FINAL slot cell file (length = program.n_slot_cells), snapshotted just
    /// before returning. Exists for cross-implementation parity checks (e.g.
    /// the GPU interpreter's debug cell-file dump).
    pub final_cells: Vec<Bf>,
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
    let mut native_trace: Vec<NativeFire> = Vec::new();

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

        if ins.op == Op::NativeK {
            let vals: Vec<Ext> = ins.operands.iter().map(|o| read(o)).collect();
            let pid = ins.payload.expect("NativeK without payload");
            native_trace.push(NativeFire { payload: pid, vals });
            // CacheK: write the caller-provided sentinel into the result cell.
            // GateK (Dst::Native): no interpreter-visible store.
            if let Some(c) = p.payloads[pid as usize].cache {
                if let Dst::Slot(cell) = ins.dst {
                    write_cells(&mut slots, cell, ins.e4_result, src.cache_outs[c as usize]);
                }
            }
            continue;
        }

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
            Op::NativeK => unreachable!("NativeK is handled by the early-continue above"),
        };

        match ins.dst {
            Dst::Slot(cell) => write_cells(&mut slots, cell, ins.e4_result, acc),
            Dst::FixedReg(cell) => write_cells(&mut fixed, cell, ins.e4_result, acc),
            Dst::Output(j) => outputs[j as usize] = Some(acc),
            Dst::GateIn(i) => gate_ins[i as usize] = Some(acc),
            Dst::Native => unreachable!("Dst::Native is NativeK-only"),
        }
    }
    ExecResult { outputs, gate_ins, native_trace, final_cells: slots }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::isa::{Instr, PayloadMeta};
    use field::PrimeField;

    #[test]
    fn nativek_traces_and_writes_sentinels() {
        let p = Program {
            instrs: vec![
                // CacheK 0: reads source 0, result sentinel into cell 0 (bf).
                Instr {
                    op: Op::NativeK,
                    e4_result: false,
                    dst: Dst::Slot(0),
                    operands: vec![Operand::Source { id: 0, e4: false }],
                    payload: Some(0),
                },
                // GateK 1: reads the cache cell and source 1.
                Instr {
                    op: Op::NativeK,
                    e4_result: false,
                    dst: Dst::Native,
                    operands: vec![
                        Operand::Slot { cell: 0, e4: false },
                        Operand::Source { id: 1, e4: false },
                    ],
                    payload: Some(1),
                },
            ],
            n_slot_cells: 1,
            n_sources_bf: 2,
            payloads: vec![
                PayloadMeta { cache: Some(0), e4: false },
                PayloadMeta { cache: None, e4: false },
            ],
            ..Default::default()
        };
        let src = StagedSources {
            bf: vec![Bf::from_u32_with_reduction(3), Bf::from_u32_with_reduction(5)],
            e4: vec![],
            cache_outs: vec![lift(Bf::from_u32_with_reduction(7))],
        };
        let got = execute(&p, &src);
        assert_eq!(got.native_trace.len(), 2);
        assert_eq!(got.native_trace[0].payload, 0);
        assert_eq!(got.native_trace[0].vals, vec![lift(Bf::from_u32_with_reduction(3))]);
        // The gate reads the SENTINEL from the cache cell, not the input.
        assert_eq!(
            got.native_trace[1].vals,
            vec![lift(Bf::from_u32_with_reduction(7)), lift(Bf::from_u32_with_reduction(5))]
        );
    }
}
