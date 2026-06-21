//! Human-readable disassembler for a compiled forward-eval VM layer.
//!
//! Renders a [`CompiledLayer`] (and, optionally, the source [`DagLayer`] it was
//! compiled from) as annotated text: the source/expr/root DAG, the instruction
//! stream with operands resolved to readable names, and the side tables
//! (backings, const bank, peek descriptors, cache locations, root outputs,
//! stats). Prover-agnostic — depends only on `gkr_eval_isa` + `cs::gkr_compiler`.
//!
//! This is a debugging / inspection tool, not part of the proving path. Use it
//! to eyeball what the compiler emitted for a given circuit layer (e.g. to spot
//! missed FMA fusion or unnecessary cell traffic).

use super::context::{CompiledLayer, DagForwardContext, ForwardAction, OutputCell, RootOutput};
use super::isa::{DstLine, Instr, LdcSub, MovDir, OperandField, OperandLine, Sign};
use super::stats::{OP_ADD, OP_FMA, OP_MOV, OP_MUL};
use cs::gkr_compiler::dag_ir::{DagLayer, Expr, Root, RootId, SourceKind};
use std::fmt::Write;

fn field_tag(f: &OperandField) -> &'static str {
    match f {
        OperandField::Base => "b",
        OperandField::Ext => "e",
    }
}

/// Format one operand line, resolving indices to readable names via the context's
/// banks/tables.
fn fmt_operand(op: &OperandLine, ctx: &DagForwardContext) -> String {
    match op {
        OperandLine::Global { slot, col } => match ctx.backings.backing(*slot) {
            Some(k) => format!("{k:?}[s{slot}:c{col}]"),
            None => format!("Global[s{slot}:c{col}]"),
        },
        OperandLine::Smem { cell } => format!("$cell{cell}"),
        OperandLine::Ldc { sub, idx } => match sub {
            LdcSub::Const => match ctx.consts.get(*idx) {
                Some(v) => format!("#{v}"),
                None => format!("#const?{idx}"),
            },
            LdcSub::ConstChallenge => match ctx.challenges.get(LdcSub::ConstChallenge, *idx) {
                Some(r) => format!("chalC({r:?})"),
                None => format!("chalC?{idx}"),
            },
            LdcSub::ArgChallenge => match ctx.challenges.get(LdcSub::ArgChallenge, *idx) {
                Some(r) => format!("chalA({r:?})"),
                None => format!("chalA?{idx}"),
            },
            LdcSub::Special => format!("lit(special#{idx})"),
        },
        OperandLine::Special { desc } => match ctx.specials.get(*desc) {
            Some(d) => format!("PEEK[{desc}]={:?}@e{}", d.strategy, d.origin_expr.0),
            None => format!("PEEK?{desc}"),
        },
    }
}

fn fmt_dst(d: &DstLine, ctx: &DagForwardContext) -> String {
    match d {
        DstLine::Smem { cell } => format!("$cell{cell}"),
        DstLine::GlobalMaterialize { slot, col } => match ctx.backings.backing(*slot) {
            Some(k) => format!("{k:?}[s{slot}:c{col}]"),
            None => format!("Global[s{slot}:c{col}]"),
        },
    }
}

/// Render one instruction as a single line (without the leading index).
pub fn fmt_instr(instr: &Instr, ctx: &DagForwardContext) -> String {
    let join = |ops: &[OperandLine], sep: &str| {
        ops.iter()
            .map(|o| fmt_operand(o, ctx))
            .collect::<Vec<_>>()
            .join(sep)
    };
    match instr {
        Instr::Add {
            field,
            sign,
            operands,
        } => {
            let s = if matches!(sign, Sign::Minus) {
                "-"
            } else {
                "+"
            };
            format!(
                "ADD.{} acc {s}= {}",
                field_tag(field),
                join(operands, " + ")
            )
        }
        Instr::Mul { field, operands } => {
            format!("MUL.{} acc *= {}", field_tag(field), join(operands, " * "))
        }
        Instr::Fma {
            field_lhs,
            field_rhs,
            sign,
            pairs,
        } => {
            let s = if matches!(sign, Sign::Minus) {
                "-"
            } else {
                "+"
            };
            let ps = pairs
                .iter()
                .map(|(l, r)| format!("{}*{}", fmt_operand(l, ctx), fmt_operand(r, ctx)))
                .collect::<Vec<_>>()
                .join(" + ");
            format!(
                "FMA.{}{} acc {s}= {ps}",
                field_tag(field_lhs),
                field_tag(field_rhs)
            )
        }
        Instr::Mov {
            dir,
            field,
            dst,
            src,
        } => {
            let d = dst
                .as_ref()
                .map(|d| fmt_dst(d, ctx))
                .unwrap_or_else(|| "-".into());
            let sc = src
                .as_ref()
                .map(|s| fmt_operand(s, ctx))
                .unwrap_or_else(|| "-".into());
            match dir {
                MovDir::AccFromSrc => format!("MOV.{} acc <- {sc}", field_tag(field)),
                MovDir::DstFromAcc => {
                    format!(
                        "MOV.{} {d} <- acc            (materialize)",
                        field_tag(field)
                    )
                }
                MovDir::DstFromSrc => format!("MOV.{} {d} <- {sc}", field_tag(field)),
            }
        }
    }
}

/// Disassemble a compiled layer to annotated text. Pass `layer` (the `DagLayer`
/// the compiled layer came from) to also dump the source/expr/root DAG; pass
/// `None` to dump just the program + side tables. `title` heads the output.
pub fn disassemble_layer(
    title: &str,
    compiled: &CompiledLayer,
    layer: Option<&DagLayer>,
) -> String {
    let ctx = &compiled.ctx;
    let mut o = String::new();
    let _ = writeln!(o, "===== {title} =====");
    let _ = writeln!(
        o,
        "budget(cells) = {}   instructions = {}",
        compiled.budget,
        compiled.program.instrs.len()
    );

    // ---- source DAG (optional) ----
    if let Some(layer) = layer {
        let _ = writeln!(
            o,
            "\n--- DAG: {} sources, {} exprs, {} roots, {} sinks ---",
            layer.sources.len(),
            layer.exprs.len(),
            layer.roots.len(),
            layer.sinks.len()
        );
        let _ = writeln!(o, "sources:");
        for (i, s) in layer.sources.iter().enumerate() {
            let desc = match &s.kind {
                SourceKind::Read { place } => format!("Read {place:?}"),
                SourceKind::Prior { id } => {
                    format!(
                        "Prior(root {})  <-- reuse of an already-computed root (cache/CSE)",
                        id.0
                    )
                }
                SourceKind::Constant { value } => format!("Constant {value}"),
                SourceKind::Challenge { reference } => format!("Challenge {reference:?}"),
                SourceKind::VirtualSetup { kind } => format!("VirtualSetup {kind:?}"),
                SourceKind::LookupValue {
                    kind,
                    set_index,
                    query,
                } => {
                    format!("LookupValue {kind:?} set={set_index} query=e{}", query.0)
                }
            };
            let _ = writeln!(o, "  src{i:<3} {desc}");
        }

        if !layer.resolutions.is_empty() {
            let _ = writeln!(o, "\nresolutions (forward peek hints, keyed by expr):");
            let mut rs: Vec<_> = layer.resolutions.iter().collect();
            rs.sort_by_key(|(e, _)| e.0);
            for (e, strat) in rs {
                let _ = writeln!(o, "  e{:<4} {strat:?}", e.0);
            }
        }

        let _ = writeln!(o, "\nroots:");
        for (idx, root) in layer.roots.iter().enumerate() {
            let rid = RootId(idx as u32);
            let action = ctx.actions.get(&rid);
            let kind = match root {
                Root::Output { expr, sink } => {
                    let si = &layer.sinks[sink.0 as usize];
                    let cache = if !layer.origins.contains_key(&rid) {
                        "  [CACHE root — no origin]"
                    } else {
                        ""
                    };
                    format!(
                        "Output expr=e{} -> {:?}/{:?}{cache}",
                        expr.0, si.kind, si.field
                    )
                }
                Root::Constraint { expr } => format!("Constraint expr=e{}", expr.0),
            };
            let _ = writeln!(o, "  root{idx:<3} {kind}  action={action:?}");
        }
    }

    // ---- program ----
    let _ = writeln!(
        o,
        "\n--- PROGRAM (single-accumulator VM; `acc` is implicit) ---"
    );
    for (i, instr) in compiled.program.instrs.iter().enumerate() {
        let _ = writeln!(o, "  [{i:4}] {}", fmt_instr(instr, ctx));
    }

    // ---- side tables ----
    let _ = writeln!(o, "\n--- backings (slot -> storage region) ---");
    for slot in 0u8..16 {
        match ctx.backings.backing(slot) {
            Some(k) => {
                let _ = writeln!(o, "  s{slot} = {k:?}");
            }
            None => break,
        }
    }
    if !ctx.consts.values().is_empty() {
        let _ = writeln!(o, "\nconst bank: {:?}", ctx.consts.values());
    }
    if ctx.specials.len() > 0 {
        let _ = writeln!(o, "\npeek descriptors:");
        for (d, sd) in ctx.specials.iter().enumerate() {
            let _ = writeln!(
                o,
                "  PEEK[{d}] {:?}  origin=e{}",
                sd.strategy, sd.origin_expr.0
            );
        }
    }
    if !ctx.cache_loc.is_empty() {
        let _ = writeln!(
            o,
            "\ncache_loc (cache root -> backing it materialized into; same-layer Prior reads target this):"
        );
        let mut cl: Vec<_> = ctx.cache_loc.iter().collect();
        cl.sort_by_key(|(r, _)| r.0);
        for (rid, (slot, col)) in cl {
            let region = ctx
                .backings
                .backing(*slot)
                .map(|k| format!("{k:?}"))
                .unwrap_or_else(|| "Global".into());
            let _ = writeln!(o, "  root{} -> {region}[s{slot}:c{col}]", rid.0);
        }
    }

    // action census
    let (mut compute, mut alias, mut skip) = (0usize, 0usize, 0usize);
    for v in ctx.actions.values() {
        match v {
            ForwardAction::Compute => compute += 1,
            ForwardAction::CopyAlias { .. } => alias += 1,
            ForwardAction::SkipScratchPrefill => skip += 1,
        }
    }

    // count Alias root outputs (no program lanes)
    let alias_outputs = compiled
        .root_outputs
        .iter()
        .filter(|(_, ro)| matches!(ro, RootOutput::Alias(_)))
        .count();
    let _ = writeln!(
        o,
        "\nroot outputs: {} total ({} Cell, {} Alias/no-lanes), skipped(scratch-prefill): {}",
        compiled.root_outputs.len(),
        compiled.root_outputs.len() - alias_outputs,
        alias_outputs,
        compiled.skipped.len()
    );

    let st = &compiled.stats;
    let _ = writeln!(
        o,
        "\nstats: lanes={} | add={} mul={} fma={} mov={} | peeks={} max_live_cells={} | actions: compute={compute} alias={alias} skip={skip}",
        st.program_lanes,
        st.op_counts[OP_ADD],
        st.op_counts[OP_MUL],
        st.op_counts[OP_FMA],
        st.op_counts[OP_MOV],
        st.special_gathers,
        st.max_live_cells,
    );
    o
}
