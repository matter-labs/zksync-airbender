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
use super::source::SpecialStrategy;
use super::stats::{OP_ADD, OP_FMA, OP_MOV, OP_MUL};
use cs::gkr_compiler::dag_ir::{DagLayer, Expr, Root, RootId, SourceKind};
use std::fmt::Write;

fn field_tag(f: &OperandField) -> &'static str {
    match f {
        OperandField::Base => "b",
        OperandField::Ext => "e",
    }
}

/// BabyBear prime (the forward VM is BabyBear-specific). Used only to render a
/// base-field constant near `P` as its small signed representative.
const BABYBEAR_P: u32 = 2013265921; // 15 * 2^27 + 1 = 0x78000001

/// Render a base-field constant value: small positives as-is, and a value in the
/// top half of `[0, P)` as its signed representative too (e.g. `2013265920(=-1)`,
/// `2013200385(=-65536)`) so masks / small negatives are legible.
fn fmt_const(v: u32) -> String {
    if v > BABYBEAR_P / 2 {
        format!("{v}(={})", v as i64 - BABYBEAR_P as i64)
    } else {
        format!("{v}")
    }
}

/// Decode a `LdcSub::Special` payload index to the `Special` enum it names
/// (`{Zero=0, One=1, NegOne=2}`); only `NegOne` (`-1`) is emitted in v1.
fn fmt_special_lit(idx: u16) -> String {
    match idx {
        0 => "lit(0)".to_string(),
        1 => "lit(1)".to_string(),
        2 => "lit(-1)".to_string(),
        n => format!("lit(special#{n})"),
    }
}

/// Resolve a peek's `origin_expr` to the DAG leaf it actually reads, so the peek site
/// names its value source instead of only an ExprId. A `PeekSingleColumn` origin is (by
/// `validate::check_resolutions`) a `LookupValue` leaf, so this typically renders e.g.
/// `LookupValue TimestampIndex set=35 query=e779` — the lookup table + query the forward
/// VM peeks the precomputed resolution of. Returns `None` if the DAG isn't supplied or
/// the origin isn't a plain source leaf.
fn describe_peek_origin(layer: Option<&DagLayer>, origin: cs::gkr_compiler::dag_ir::ExprId) -> Option<String> {
    let layer = layer?;
    let Expr::Source(sid) = layer.exprs.get(origin.0 as usize)? else {
        return None;
    };
    match &layer.sources.get(sid.0 as usize)?.kind {
        SourceKind::LookupValue { kind, set_index, query } => {
            Some(format!("LookupValue {kind:?} set={set_index} query=e{}", query.0))
        }
        other => Some(format!("{other:?}")),
    }
}

/// Format one operand line, resolving indices to readable names via the context's
/// banks/tables. `layer` (when supplied) lets a `PEEK` operand name the DAG leaf its
/// `origin_expr` reads.
fn fmt_operand(op: &OperandLine, ctx: &DagForwardContext, layer: Option<&DagLayer>) -> String {
    match op {
        OperandLine::Global { slot, col } => match ctx.backings.backing(*slot) {
            Some(k) => format!("{k:?}[s{slot}:c{col}]"),
            None => format!("Global[s{slot}:c{col}]"),
        },
        OperandLine::Smem { cell } => format!("$cell{cell}"),
        OperandLine::Ldc { sub, idx } => match sub {
            LdcSub::Const => match ctx.consts.get(*idx) {
                Some(v) => format!("#{}", fmt_const(v)),
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
            LdcSub::Special => fmt_special_lit(*idx),
        },
        OperandLine::Special { desc } => match ctx.specials.get(*desc) {
            // `VirtualSetup` is a computed, slotless Special (no backing slot, no DRAM
            // gather — see `SpecialStrategy::VirtualSetup`), unlike the peek strategies
            // below, so it gets an honest label rather than the "PEEK" wording, matching
            // the source-dump rendering of `SourceKind::VirtualSetup` (disasm.rs :206).
            Some(d) => match &d.strategy {
                SpecialStrategy::VirtualSetup { kind } => format!("VirtualSetup {kind:?}"),
                strategy => {
                    let via = describe_peek_origin(layer, d.origin_expr)
                        .map(|s| format!(" via {s}"))
                        .unwrap_or_default();
                    format!("PEEK[{desc}]={strategy:?}@e{}{via}", d.origin_expr.0)
                }
            },
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

/// Width of the `  [nnnn] ` index prefix that [`disassemble_layer`] prepends to
/// each program line (2 spaces + `[` + 4-wide index + `] `). Continuation lines
/// emitted by [`fmt_instr`] pad by this much so multi-lane operands align under
/// the first lane in the rendered program.
const PROGRAM_PREFIX_COLS: usize = 9;

/// Render a reduction (ADD/MUL/FMA) with each input lane on its own row: the
/// first lane sits on the instruction line right after `head`, and every
/// subsequent lane starts a fresh row led by `cont_op`, indented so the lane
/// text lines up vertically under the first one. Single-lane reductions stay on
/// one line. `head` is the mnemonic+accumulator prefix (e.g. `"ADD.b acc += "`).
fn fmt_lanes(head: &str, lanes: &[String], cont_op: char) -> String {
    let mut s = format!("{head}{}", lanes.first().map(String::as_str).unwrap_or(""));
    if lanes.len() > 1 {
        // Column where the first lane begins, so continuation lanes align under it;
        // `cont_op` + one space sits in the two columns just left of that.
        let lane_col = PROGRAM_PREFIX_COLS + head.len();
        let pad = " ".repeat(lane_col.saturating_sub(2));
        for lane in &lanes[1..] {
            let _ = write!(s, "\n{pad}{cont_op} {lane}");
        }
    }
    s
}

/// Render one instruction. Reductions with more than one input lane span
/// multiple rows (see [`fmt_lanes`]); everything else is a single line. Never
/// includes the leading `[nnnn]` index.
pub fn fmt_instr(instr: &Instr, ctx: &DagForwardContext, layer: Option<&DagLayer>) -> String {
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
            let lanes: Vec<String> = operands.iter().map(|o| fmt_operand(o, ctx, layer)).collect();
            fmt_lanes(&format!("ADD.{} acc {s}= ", field_tag(field)), &lanes, '+')
        }
        Instr::Mul { field, operands } => {
            let lanes: Vec<String> = operands.iter().map(|o| fmt_operand(o, ctx, layer)).collect();
            fmt_lanes(&format!("MUL.{} acc *= ", field_tag(field)), &lanes, '*')
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
            let lanes: Vec<String> = pairs
                .iter()
                .map(|(l, r)| format!("{}*{}", fmt_operand(l, ctx, layer), fmt_operand(r, ctx, layer)))
                .collect();
            fmt_lanes(
                &format!("FMA.{}{} acc {s}= ", field_tag(field_lhs), field_tag(field_rhs)),
                &lanes,
                '+',
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
                .map(|s| fmt_operand(s, ctx, layer))
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
        let materializes = layer.roots.iter().filter(|r| r.materialize.is_some()).count();
        let _ = writeln!(
            o,
            "\n--- DAG: {} sources, {} exprs, {} roots, {} materializes ---",
            layer.sources.len(),
            layer.exprs.len(),
            layer.roots.len(),
            materializes
        );
        let _ = writeln!(o, "sources:");
        for (i, s) in layer.sources.iter().enumerate() {
            let desc = match &s.kind {
                SourceKind::Read { place } => format!("Read {place:?}"),
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
            let kind = match (root.materialize.as_ref(), root.claim.as_ref()) {
                (Some(si), claim) => {
                    let cache = if claim.is_none() {
                        "  [CACHE root — materialize-only, no claim]"
                    } else {
                        ""
                    };
                    format!(
                        "Output expr=e{} -> {:?}/{:?}{cache}",
                        root.expr.0, si.kind, si.field
                    )
                }
                (None, _) => format!("Constraint expr=e{}", root.expr.0),
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
        let _ = writeln!(o, "  [{i:4}] {}", fmt_instr(instr, ctx, layer));
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
        "\nstats: lanes={} | add={} mul={} fma={} mov={} | peeks={} max_live_cells={} \
         | dram_traffic={} dram_reads={} | actions: compute={compute} alias={alias} skip={skip}",
        st.program_lanes,
        st.op_counts[OP_ADD],
        st.op_counts[OP_MUL],
        st.op_counts[OP_FMA],
        st.op_counts[OP_MOV],
        st.special_gathers,
        st.max_live_cells,
        st.dram_traffic,
        st.dram_reads,
    );
    o
}
