//! Human-readable disassembly for compiled backward-eval VM layers.
//!
//! Instruction rendering is shared with the forward disassembler. This module
//! supplies only the backward descriptor namespace and backward-specific
//! summary tables.

use std::fmt::Write;

use crate::fwd::context::DagForwardContext;
use crate::fwd::disasm::fmt_instr_with_specials;
use crate::fwd::isa::{Instr, MovDir, OperandField};
use crate::fwd::stats::{OP_ADD, OP_FMA, OP_MOV, OP_MUL};

use super::batch::{unpack_batch_dst, BATCH_COEFFICIENT_ONE};
use super::compile::BwdCompiledLayer;
use super::source::{BwdSpecial, OriginLeaf};

fn fmt_bwd_special(compiled: &BwdCompiledLayer, desc: u16) -> String {
    match compiled.specials.get(desc) {
        Some(BwdSpecial::AccInit) => "AccInit".to_owned(),
        Some(BwdSpecial::Coefficient { fragment }) => format!("Coefficient[f{fragment}]"),
        Some(BwdSpecial::FoldSource {
            origin: OriginLeaf::Read(place),
        }) => format!("FoldSource({place:?})"),
        Some(BwdSpecial::FoldSource {
            origin: OriginLeaf::VirtualSetup { kind },
        }) => format!("FoldSource(VirtualSetup {kind:?})"),
        Some(BwdSpecial::VirtualSetup { kind }) => format!("VirtualSetup {kind:?}"),
        None => format!("BWD_SPECIAL?{desc}"),
    }
}

fn fmt_bwd_instr(
    instr: &Instr,
    ctx: &DagForwardContext,
    fmt_special: &dyn Fn(u16) -> String,
) -> String {
    let batch_sink = if let Instr::Mov {
        dir: MovDir::DstFromAcc,
        field,
        dst: Some(dst),
        src: None,
    } = instr
    {
        unpack_batch_dst(dst).map(|coefficient_desc| (*field, coefficient_desc))
    } else {
        None
    };
    if let Some((field, coefficient_desc)) = batch_sink {
        let acc = match field {
            OperandField::Base => "acc.bf",
            OperandField::Ext => "acc.e4",
        };
        return if coefficient_desc == BATCH_COEFFICIENT_ONE {
            format!("batch += {acc}")
        } else {
            format!("batch += coeff[{coefficient_desc}] * {acc}")
        };
    }
    fmt_instr_with_specials(instr, ctx, fmt_special)
}

fn is_batch_sink(instr: &Instr) -> bool {
    matches!(
        instr,
        Instr::Mov {
            dir: MovDir::DstFromAcc,
            dst: Some(dst),
            src: None,
            ..
        } if unpack_batch_dst(dst).is_some()
    )
}

/// Render a compiled backward layer with the same instruction syntax used by
/// the forward VM disassembler.
pub fn disassemble_bwd_layer(title: &str, compiled: &BwdCompiledLayer) -> String {
    let ctx = DagForwardContext {
        consts: compiled.consts.clone(),
        derived_e4: compiled.derived_e4.clone(),
        backings: compiled.backings.clone(),
        source_windows: compiled.source_windows.clone(),
        ..DagForwardContext::default()
    };
    let fmt_special = |desc| fmt_bwd_special(compiled, desc);
    let has_batch_sink = compiled.program.instrs.iter().any(is_batch_sink);

    let mut out = String::new();
    let _ = writeln!(out, "===== {title} =====");
    let _ = writeln!(
        out,
        "budget = c{} ({} BF lanes)   instructions = {}",
        compiled.budget / 4,
        compiled.budget,
        compiled.program.instrs.len()
    );
    if has_batch_sink {
        match compiled.acc_init_desc {
            Some(desc) => {
                let _ = writeln!(out, "batch_init = coeff[{desc}]");
            }
            None => {
                let _ = writeln!(out, "batch_init = 0");
            }
        }
    }
    let _ = writeln!(
        out,
        "\n--- PROGRAM (single-accumulator VM; `acc` is implicit) ---"
    );
    for (index, instruction) in compiled.program.instrs.iter().enumerate() {
        let _ = writeln!(
            out,
            "  [{index:4}] {}",
            fmt_bwd_instr(instruction, &ctx, &fmt_special)
        );
    }

    let _ = writeln!(out, "\n--- backings (slot -> storage region) ---");
    for slot in 0u8..16 {
        match compiled.backings.backing(slot) {
            Some(backing) => {
                let _ = writeln!(out, "  s{slot} = {backing:?}");
            }
            None => break,
        }
    }
    if !compiled.consts.values().is_empty() {
        let _ = writeln!(out, "\nconst bank: {:?}", compiled.consts.values());
    }
    if compiled.specials.len() > 0 {
        let _ = writeln!(out, "\nbackward special descriptors:");
        for desc in 0..compiled.specials.len() {
            let _ = writeln!(
                out,
                "  BWD[{desc}] = {}",
                fmt_bwd_special(compiled, desc as u16)
            );
        }
    }

    let stats = &compiled.stats;
    let _ = writeln!(
        out,
        "\nstats: lanes={} | add={} mul={} fma={} mov={} | max_live_bf_lanes={} \
         | global_read_lanes={} fold_uses={} fold_read_lanes={}",
        stats.program_lanes,
        stats.op_counts[OP_ADD],
        stats.op_counts[OP_MUL],
        stats.op_counts[OP_FMA],
        stats.op_counts[OP_MOV],
        stats.max_live_cells,
        compiled.stats_ext.global,
        compiled.stats_ext.fold_uses,
        compiled.stats_ext.fold_traffic,
    );
    if has_batch_sink {
        let _ = writeln!(
            out,
            "batch_fma: bf={} e4={}",
            compiled.stats_ext.batch_fma_base, compiled.stats_ext.batch_fma_ext
        );
        let _ = writeln!(out, "terminal = ReturnBatch");
    } else {
        let _ = writeln!(out, "terminal = ReturnAcc");
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bwd::batch::{pack_batch_dst, BATCH_COEFFICIENT_ONE};
    use crate::fwd::isa::{Instr, LdcSub, MovDir, OperandField, OperandLine, Program, Special};

    #[test]
    fn batch_sinks_have_backward_specific_readable_syntax() {
        let base = Instr::Mov {
            dir: MovDir::DstFromAcc,
            field: OperandField::Base,
            dst: Some(pack_batch_dst(17).unwrap()),
            src: None,
        };
        let ext = Instr::Mov {
            dir: MovDir::DstFromAcc,
            field: OperandField::Ext,
            dst: Some(pack_batch_dst(BATCH_COEFFICIENT_ONE).unwrap()),
            src: None,
        };

        assert_eq!(
            fmt_bwd_instr(&base, &DagForwardContext::default(), &|_| {
                unreachable!()
            }),
            "batch += coeff[17] * acc.bf"
        );
        assert_eq!(
            fmt_bwd_instr(&ext, &DagForwardContext::default(), &|_| { unreachable!() }),
            "batch += acc.e4"
        );
    }

    #[test]
    fn result_in_acc_layer_keeps_return_acc_rendering() {
        let compiled = BwdCompiledLayer {
            program: Program {
                instrs: vec![Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Ldc {
                        sub: LdcSub::Special,
                        idx: Special::One as u16,
                    }),
                }],
            },
            acc_init_desc: None,
            specials: Default::default(),
            backings: Default::default(),
            source_windows: Default::default(),
            consts: Default::default(),
            derived_e4: Default::default(),
            budget: 4,
            stats: Default::default(),
            stats_ext: Default::default(),
        };

        let rendered = disassemble_bwd_layer("legacy", &compiled);
        assert!(rendered.contains("terminal = ReturnAcc"));
        assert!(!rendered.contains("terminal = ReturnBatch"));
        assert!(!rendered.contains("batch_init"));
        assert!(!rendered.contains("batch_fma"));
    }
}
