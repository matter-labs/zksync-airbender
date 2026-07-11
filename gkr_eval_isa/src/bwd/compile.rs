//! Bwd compile driver (Task 5, spec §3): compile a [`DistilledLayer`] to a
//! backward-VM program with the RESULT-IN-ACC terminal convention.
//!
//! The program ends with the distilled root's value in the accumulator: a
//! source-only root degenerates to a single `Mov AccFromSrc`, and
//! `DstLine::GlobalMaterialize` is never emitted (structurally unemittable —
//! the bwd lowering runs with empty materialize maps). Bindings are NOT a
//! compile input: the program is round- and policy-invariant, `bind()` only
//! produces per-run [`super::distill::BwdBindings`].
//!
//! Spine accumulation: `ArenaBuilder::add` flattens + sorts, so the distilled
//! alpha spine is one WIDE `Add`. Lowering it through the shared reduction
//! machinery would pre-materialize every term into a concurrent Ext temp
//! (never b16-feasible for a whole-layer root), so the driver accumulates
//! term-by-term — spill partial, compute term, fold spill back — bounding the
//! spine's own state to ONE Ext cell (`lower_bwd_root_virtual`). The
//! occurrence replay ([`OccurrenceStreams::build_bwd_root`]) mirrors exactly
//! this decomposition over [`spine_terms`].
//!
//! Descriptor namespace rule: `OperandLine::Special { desc }` in a bwd program
//! indexes ONLY [`BwdSpecialTable`] — fwd's `SpecialTable`/peek validators/fwd
//! stats tally are never applied to bwd programs, hence the local
//! [`tally_bwd_program`] and the [`BwdTrafficStats`] extension (a `FoldSource`
//! use encodes as a Special and would be invisible to `dram_traffic`).

use std::collections::BTreeMap;

use cs::gkr_compiler::dag_ir::{Expr, ExprId};

use crate::fwd::binding::BackingTable;
use crate::fwd::compile::decisions::OccurrenceStreams;
use crate::fwd::compile::{compile_bwd_program, SiteDecisions};
use crate::fwd::context::DagForwardContext;
use crate::fwd::error::CompileError;
use crate::fwd::isa::{DstLine, Instr, LdcSub, OperandField, OperandLine, Program};
use crate::fwd::source::{ChallengeBanks, ConstBank};
use crate::fwd::stats::{CompileStats, OP_ADD, OP_FMA, OP_MOV, OP_MUL};

use super::distill::{distilled_site_domain, DistilledLayer};
use super::source::{BwdSpecial, BwdSpecialTable};

// ── BwdTrafficStats ───────────────────────────────────────────────────────────

/// Search-facing traffic extension (REV2, moved from Task 12): `CompileStats.
/// dram_traffic` counts `Global` operands only, so FoldSources (encoded as
/// `Special`) would be invisible to the Task-8 objective. `fold_traffic` is the
/// ROLE-NEUTRAL tally at 4 cells (Ext width) per use — exact per-role/depth
/// byte costs stay in Task 12's census model.
///
/// `fold_traffic` counts 4 cells per READ-ORIGIN fold use ONLY: a VS-origin
/// fold (`origin.is_vs()`) uses the O(k) multilinear closed form — compute-only,
/// zero DRAM — so it contributes to `fold_uses` but adds NO `fold_traffic`.
/// Invariant: `fold_traffic == 4 * (fold_uses - vs_fold_uses)`, where
/// `vs_fold_uses` is the VS-origin subset of `fold_uses`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct BwdTrafficStats {
    /// Width-weighted `Global` (real DRAM backing) operand traffic, in cells —
    /// mirrors `CompileStats::dram_traffic` (R0-regime Reads and cross-layer reads).
    pub global: usize,
    /// `Special { desc }` operand uses whose desc is a `BwdSpecial::FoldSource`
    /// — BOTH Read-origin and VS-origin uses count here.
    pub fold_uses: usize,
    /// Role-neutral fold operand traffic: `4 * (fold_uses - vs_fold_uses)`
    /// (Ext width per READ-origin use only — VS-origin uses add no traffic).
    pub fold_traffic: usize,
}

// ── BwdCompiledLayer ──────────────────────────────────────────────────────────

/// A compiled backward layer: the round/policy-invariant program + the tables
/// its operands index. `budget` is in bf lanes (buckets = `budget / 4`).
#[derive(Clone, Debug)]
pub struct BwdCompiledLayer {
    pub program: Program,
    /// The BWD descriptor namespace `Special` operands index (never fwd's).
    pub specials: BwdSpecialTable,
    /// Backing slots for R0-regime `Global` reads.
    pub backings: BackingTable,
    pub consts: ConstBank,
    pub challenges: ChallengeBanks,
    /// Smem budget in bf lanes; v2 ext buckets = `budget / 4`.
    pub budget: usize,
    pub stats: CompileStats,
    pub stats_ext: BwdTrafficStats,
}

// ── spine terms ───────────────────────────────────────────────────────────────

/// The driver's term decomposition of the distilled root: the top-level
/// children of the (flattened, sorted — `ArenaBuilder` canonicalization) alpha
/// spine `Add`, or the root expr itself when it is not an `Add` (single-unit
/// layers / leaf roots). Accumulation over any decomposition is value-identical
/// by Add commutativity; the replay twin mirrors exactly this decomposition, so
/// both the driver and [`OccurrenceStreams::build_bwd_root`] MUST consume this
/// same function's output.
pub fn spine_terms(d: &DistilledLayer) -> Vec<ExprId> {
    let root_expr = d.layer.roots[d.root.0 as usize].expr;
    match &d.layer.exprs[root_expr.0 as usize] {
        Expr::Add(children) if !children.is_empty() => children.clone(),
        _ => vec![root_expr],
    }
}

// ── compile driver ────────────────────────────────────────────────────────────

/// Compile a distilled layer at `budget` (bf lanes). `decisions` carries the
/// per-site residency genes keyed to DISTILLED `ExprId`s (`None` = uncached
/// per-demand recompute). Bindings are deliberately NOT an input — see the
/// module doc (round/policy invariance).
///
/// Legacy-first compile driver (SP1). The baseline is the pre-materialize
/// lowering (`stream_reductions = false`, byte-identical to before this task);
/// only when it reports [`CompileError::BudgetBelowFloor`] do we retry with the
/// one-Ext-cell reduction streaming engaged. Feasibility with streaming ⊇ legacy
/// and streamed programs are value-identical to legacy on both the uncached and
/// searched paths, so this fallback never changes a value or shrinks feasibility.
pub fn compile_distilled(
    d: &DistilledLayer,
    budget: usize,
    decisions: Option<&SiteDecisions>,
) -> Result<BwdCompiledLayer, CompileError> {
    match compile_distilled_streamed(d, budget, decisions, false) {
        Err(CompileError::BudgetBelowFloor { .. }) => {
            compile_distilled_streamed(d, budget, decisions, true)
        }
        other => other,
    }
}

/// The legacy pre-materialize lowering ONLY (`stream_reductions = false`) — the
/// SP1 baseline, exposed for the parity tests that must observe the un-streamed
/// floor (a `BudgetBelowFloor` that streaming would otherwise mask).
pub fn compile_distilled_legacy_only(
    d: &DistilledLayer,
    budget: usize,
    decisions: Option<&SiteDecisions>,
) -> Result<BwdCompiledLayer, CompileError> {
    compile_distilled_streamed(d, budget, decisions, false)
}

/// Fill-then-trim compile at a fixed `stream_reductions` (same semantics as fwd
/// `compile_layer` at the same budget): lower with eviction effectively disabled
/// (FILL), let `plan_placement` at the real `budget` be the feasibility oracle,
/// and on overflow binary-search the largest lowering budget whose placement fits
/// (`lower_budget == budget` is the guaranteed baseline). `pub` for the SP1 parity
/// tests, which pin the streamed vs legacy variants against each other.
pub fn compile_distilled_streamed(
    d: &DistilledLayer,
    budget: usize,
    decisions: Option<&SiteDecisions>,
    stream_reductions: bool,
) -> Result<BwdCompiledLayer, CompileError> {
    const FILL: usize = 1 << 20;
    let at = |lb: usize| compile_distilled_at(d, budget, lb, decisions, stream_reductions);
    match at(FILL) {
        Ok(c) => return Ok(c),
        Err(CompileError::BudgetBelowFloor { .. }) => {}
        Err(e) => return Err(e),
    }
    let mut best = at(budget)?; // baseline — never worse than this
    let (mut lo, mut hi) = (budget, FILL); // lo fits, hi overflows
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        match at(mid) {
            Ok(c) => {
                best = c;
                lo = mid;
            }
            Err(CompileError::BudgetBelowFloor { .. }) => hi = mid,
            Err(e) => return Err(e),
        }
    }
    Ok(best)
}

/// Lower at `lower_budget` (eviction dial), place at `place_budget` (real cell
/// budget) — the bwd sibling of fwd's `compile_layer_at`.
fn compile_distilled_at(
    d: &DistilledLayer,
    place_budget: usize,
    lower_budget: usize,
    decisions: Option<&SiteDecisions>,
    stream_reductions: bool,
) -> Result<BwdCompiledLayer, CompileError> {
    let layer = &d.layer;
    let root_expr = layer.roots[d.root.0 as usize].expr;
    let terms = spine_terms(d);

    let mut ctx = DagForwardContext::default();
    ctx.cross_layer_fields = d.cross_fields.clone();

    // The bwd occurrence/demand replay, over the SAME term decomposition the
    // driver executes, gated by the DISTILLED site domain.
    let streams = decisions.map(|dec| {
        OccurrenceStreams::build_bwd_root(
            layer,
            d.root,
            root_expr,
            &terms,
            dec,
            &distilled_site_domain(d),
        )
    });

    let (program, max_live_cells) = compile_bwd_program(
        layer,
        root_expr,
        &terms,
        &mut ctx,
        &d.leaf_descs,
        &d.field_overrides,
        streams,
        place_budget,
        lower_budget,
        stream_reductions,
    )?;

    // The bwd lowering runs the fwd resolution hook with empty materialize maps
    // and CLEARED resolutions, so it must never intern a fwd SpecialDescriptor:
    // bwd Special operands index `d.specials` (the BWD table), a disjoint
    // namespace. A non-empty fwd table here means a resolution fence leaked into
    // the fwd descriptor namespace.
    assert!(ctx.specials.is_empty(), "bwd compile leaked into the fwd descriptor namespace");

    let (mut stats, stats_ext) = tally_bwd_program(&program, &d.specials);
    stats.max_live_cells = max_live_cells;

    Ok(BwdCompiledLayer {
        program,
        specials: d.specials.clone(),
        backings: ctx.backings,
        consts: ctx.consts,
        challenges: ctx.challenges,
        budget: place_budget,
        stats,
        stats_ext,
    })
}

// ── stats tally (bwd descriptor namespace) ────────────────────────────────────

/// Cell width of an operand under `field` (Ext = 4, Base = 1) — the same
/// convention as fwd's `tally_operand` width weighting.
fn width_of(field: OperandField) -> usize {
    match field {
        OperandField::Base => 1,
        OperandField::Ext => 4,
    }
}

/// Tally the concrete bwd program. Mirrors fwd's per-operand accounting, except
/// `Special { desc }` resolves against the BWD table: a `VirtualSetup` desc is
/// resolver-computed (0 traffic, uncounted, like fwd's VirtualSetup strategy); a
/// Read-origin `FoldSource` desc is a real fold-side gather — counted in
/// `special_reads` AND in the search-facing `BwdTrafficStats` (4 cells/use,
/// role-neutral). A VS-origin `FoldSource` uses the O(k) multilinear closed form
/// (Task 7): compute-only, zero DRAM, so it adds `fold_uses` but no `fold_traffic`.
fn tally_bwd_program(
    program: &Program,
    specials: &BwdSpecialTable,
) -> (CompileStats, BwdTrafficStats) {
    let mut stats = CompileStats::default();
    let mut ext = BwdTrafficStats::default();
    stats.program_lanes = program.instrs.len();
    let mut tally = |op: &OperandLine, field: OperandField, stats: &mut CompileStats, ext: &mut BwdTrafficStats| {
        match op {
            OperandLine::Global { .. } => {
                stats.dram_reads += 1;
                let w = width_of(field);
                stats.dram_traffic += w;
                ext.global += w;
            }
            OperandLine::Smem { .. } => stats.cell_reads += 1,
            OperandLine::Ldc { sub: LdcSub::Special, .. } => {} // inline literal
            OperandLine::Ldc { .. } => stats.ldc_reads += 1,
            OperandLine::Special { desc } => match specials.get(*desc) {
                Some(BwdSpecial::VirtualSetup { .. }) => {} // resolver-computed, 0 traffic
                Some(BwdSpecial::FoldSource { origin }) => {
                    stats.special_reads += 1;
                    ext.fold_uses += 1;
                    // A Read-origin fold gathers the FOLDED VALUE (always Ext, 4
                    // cells) per use — role-neutral, NOT the origin's own field
                    // width (Task 3's origin-width split lives only in cost.rs).
                    // A VS-origin fold uses the O(k) multilinear closed form
                    // (Task 7): compute-only, zero DRAM, so it is NOT tallied
                    // into the search-facing fold traffic (fold_uses is still
                    // counted — it is a real Special operand occurrence).
                    if !origin.is_vs() {
                        ext.fold_traffic += 4;
                    }
                }
                // A dense bwd table has a desc for every index a Special operand
                // can name; None means the program referenced an out-of-range desc.
                None => debug_assert!(false, "bwd Special operand names an unknown desc {desc}"),
            },
        }
    };
    for instr in &program.instrs {
        match instr {
            Instr::Mov { dir, dst, src, field, .. } => {
                stats.op_counts[OP_MOV] += 1;
                if let Some(op) = src {
                    tally(op, *field, &mut stats, &mut ext);
                }
                if matches!(
                    dir,
                    crate::fwd::isa::MovDir::DstFromAcc | crate::fwd::isa::MovDir::DstFromSrc
                ) && matches!(dst, Some(DstLine::Smem { .. }))
                {
                    stats.cell_stores += 1;
                }
            }
            Instr::Add { field, operands, .. } => {
                stats.op_counts[OP_ADD] += 1;
                for op in operands {
                    tally(op, *field, &mut stats, &mut ext);
                }
            }
            Instr::Mul { field, operands, .. } => {
                stats.op_counts[OP_MUL] += 1;
                for op in operands {
                    tally(op, *field, &mut stats, &mut ext);
                }
            }
            Instr::Fma { field_lhs, field_rhs, pairs, .. } => {
                stats.op_counts[OP_FMA] += 1;
                for (l, r) in pairs {
                    tally(l, *field_lhs, &mut stats, &mut ext);
                    tally(r, *field_rhs, &mut stats, &mut ext);
                }
            }
        }
    }
    // Fold-side gather descriptor count (the bwd sibling of fwd's peek-only
    // `special_gathers`): VirtualSetup descs are resolver-computed, excluded.
    stats.special_gathers = (0..specials.len() as u16)
        .filter(|&i| matches!(specials.get(i), Some(BwdSpecial::FoldSource { .. })))
        .count();
    (stats, ext)
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bwd::distill::{bind, distill};
    use crate::bwd::source::MaterializationPolicy;
    use crate::fwd::encode::encode;
    use crate::fwd::isa::MovDir;
    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, BwdRegime, ChallengeKey, ChallengePower, ChallengeRef, ClaimInfo, DagLayer,
        ReadPlace, Root, RootGroup, RootOrigin, RootSlot, SourceId, SourceInfo, SourceKind,
    };
    use std::collections::{BTreeMap, HashMap};

    // ── layer-building helpers (claim-only roots — bwd shape) ────────────────

    fn read_src(column: usize) -> SourceInfo {
        SourceInfo { kind: SourceKind::Read { place: ReadPlace::BaseLayerWitness { column } } }
    }

    fn claim_only_root(expr: ExprId, relation_index: usize) -> Root {
        Root {
            expr,
            materialize: None,
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index,
                    slot: RootSlot::Constraint(0),
                },
            }),
        }
    }

    fn layer(sources: Vec<SourceInfo>, exprs: Vec<Expr>, roots: Vec<Root>) -> DagLayer {
        let batching = BatchingOrder {
            roots: roots
                .iter()
                .enumerate()
                .filter(|(_, r)| r.claim.is_some())
                .map(|(i, _)| cs::gkr_compiler::dag_ir::RootId(i as u32))
                .collect(),
        };
        DagLayer { sources, exprs, roots, batching, resolutions: BTreeMap::new() }
    }

    /// All-sites decisions at priority 1.0 over the DISTILLED domain.
    fn all_sites(d: &DistilledLayer) -> SiteDecisions {
        SiteDecisions::new(distilled_site_domain(d).into_iter().map(|k| (k, 1.0)))
    }

    // ── terminal-acc invariant helpers ────────────────────────────────────────

    /// Spec §3: (i) `GlobalMaterialize` appears nowhere; (ii) the LAST instruction
    /// leaves the value in acc — an arith op (acc-folding) or `Mov AccFromSrc`.
    fn assert_result_in_acc(p: &Program) {
        assert!(!p.instrs.is_empty(), "bwd program must not be empty");
        for i in &p.instrs {
            if let Instr::Mov { dst: Some(DstLine::GlobalMaterialize { .. }), .. } = i {
                panic!("bwd program must never emit GlobalMaterialize: {i:?}");
            }
        }
        match p.instrs.last().unwrap() {
            Instr::Add { .. } | Instr::Mul { .. } | Instr::Fma { .. } => {}
            Instr::Mov { dir: MovDir::AccFromSrc, .. } => {}
            other => panic!("terminal instruction must leave the root value in acc: {other:?}"),
        }
    }

    fn for_each_operand(p: &Program, mut f: impl FnMut(&OperandLine)) {
        for instr in &p.instrs {
            match instr {
                Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
                    operands.iter().for_each(&mut f)
                }
                Instr::Fma { pairs, .. } => pairs.iter().for_each(|(l, r)| {
                    f(l);
                    f(r);
                }),
                Instr::Mov { src: Some(op), .. } => f(op),
                Instr::Mov { src: None, .. } => {}
            }
        }
    }

    fn count_desc_uses(p: &Program, desc: u16) -> usize {
        let mut n = 0;
        for_each_operand(p, |op| {
            if matches!(op, OperandLine::Special { desc: d } if *d == desc) {
                n += 1;
            }
        });
        n
    }

    fn count_smem_reads(p: &Program) -> usize {
        let mut n = 0;
        for_each_operand(p, |op| {
            if matches!(op, OperandLine::Smem { .. }) {
                n += 1;
            }
        });
        n
    }

    // ── (a)+(c): bare Read-leaf root — R0 Global / Ext FoldSource ─────────────

    #[test]
    fn terminal_bare_read_leaf_root() {
        // Single claim-only root whose cone is a bare Read leaf.
        let l = layer(
            vec![read_src(0)],
            vec![Expr::Source(SourceId(0))],
            vec![claim_only_root(ExprId(0), 0)],
        );
        // (a) R0: the leaf stays an ordinary Global backing read.
        let d = distill(&l, BwdRegime::R0, &HashMap::new(), None);
        let c = compile_distilled(&d, 16, None).expect("R0 compile");
        assert_result_in_acc(&c.program);
        assert_eq!(c.program.instrs.len(), 1, "source-only root is one Mov AccFromSrc");
        assert!(
            matches!(
                &c.program.instrs[0],
                Instr::Mov { dir: MovDir::AccFromSrc, src: Some(OperandLine::Global { .. }), .. }
            ),
            "R0 bare Read root must be Mov AccFromSrc <- Global, got {:?}",
            c.program.instrs[0]
        );
        assert_eq!(c.stats_ext.fold_uses, 0);
        assert!(c.stats_ext.global > 0);

        // (c) Ext: the leaf is a FoldSource Special in the BWD namespace.
        let d = distill(&l, BwdRegime::Ext, &HashMap::new(), None);
        let c = compile_distilled(&d, 16, None).expect("Ext compile");
        assert_result_in_acc(&c.program);
        assert_eq!(c.program.instrs.len(), 1);
        let Instr::Mov {
            dir: MovDir::AccFromSrc,
            field: OperandField::Ext,
            src: Some(OperandLine::Special { desc }),
            ..
        } = &c.program.instrs[0]
        else {
            panic!("Ext bare Read root must be Mov{{Ext}} AccFromSrc <- Special, got {:?}", c.program.instrs[0]);
        };
        assert!(
            matches!(c.specials.get(*desc), Some(BwdSpecial::FoldSource { .. })),
            "the desc must be a FoldSource in the BWD table"
        );
        assert_eq!(c.stats_ext, BwdTrafficStats { global: 0, fold_uses: 1, fold_traffic: 4 });
    }

    // ── (b): bare Challenge root ──────────────────────────────────────────────

    #[test]
    fn terminal_bare_challenge_root() {
        let l = layer(
            vec![SourceInfo {
                kind: SourceKind::Challenge {
                    reference: ChallengeRef {
                        key: ChallengeKey::ClaimBatching,
                        power: ChallengePower::One,
                    },
                },
            }],
            vec![Expr::Source(SourceId(0))],
            vec![claim_only_root(ExprId(0), 0)],
        );
        for regime in [BwdRegime::R0, BwdRegime::Ext] {
            let d = distill(&l, regime, &HashMap::new(), None);
            let c = compile_distilled(&d, 16, None).expect("compile");
            assert_result_in_acc(&c.program);
            assert!(
                matches!(
                    &c.program.instrs[0],
                    Instr::Mov { dir: MovDir::AccFromSrc, src: Some(OperandLine::Ldc { .. }), .. }
                ),
                "challenge root must load from an Ldc bank, got {:?}",
                c.program.instrs[0]
            );
        }
    }

    // ── (d): compound root ────────────────────────────────────────────────────

    #[test]
    fn terminal_compound_root() {
        // root = w0*w1 + w2 (one claim root, so the spine IS the cone).
        let l = layer(
            vec![read_src(0), read_src(1), read_src(2)],
            vec![
                Expr::Source(SourceId(0)),             // 0 = w0
                Expr::Source(SourceId(1)),             // 1 = w1
                Expr::Source(SourceId(2)),             // 2 = w2
                Expr::Mul(vec![ExprId(0), ExprId(1)]), // 3 = w0*w1
                Expr::Add(vec![ExprId(3), ExprId(2)]), // 4 = root
            ],
            vec![claim_only_root(ExprId(4), 0)],
        );
        for regime in [BwdRegime::R0, BwdRegime::Ext] {
            let d = distill(&l, regime, &HashMap::new(), None);
            let c = compile_distilled(&d, 16, None).expect("compile");
            assert_result_in_acc(&c.program);
            assert!(
                matches!(
                    c.program.instrs.last().unwrap(),
                    Instr::Add { .. } | Instr::Mul { .. } | Instr::Fma { .. }
                ),
                "compound root must terminate in an acc-folding arith op"
            );
            assert!(c.stats.program_lanes > 1);
        }
    }

    // ── (e): admissions under pressure — admitted-then-evicted, tight budget ──

    #[test]
    fn terminal_under_admission_and_eviction_pressure() {
        // Shared Ext compound c1 = w0 + w1 used by three claim roots; Ext regime
        // at b8 (2 ext buckets): the spill temp + an admitted c1 fill the file, so
        // subsequent mandatory temps force-evict the resident — the compile must
        // still terminate with the root value in acc and fit max_live_cells <= 8.
        let l = layer(
            vec![read_src(0), read_src(1), read_src(2), read_src(3)],
            vec![
                Expr::Source(SourceId(0)),             // 0 = w0
                Expr::Source(SourceId(1)),             // 1 = w1
                Expr::Source(SourceId(2)),             // 2 = w2
                Expr::Source(SourceId(3)),             // 3 = w3
                Expr::Add(vec![ExprId(0), ExprId(1)]), // 4 = c1 (shared)
                Expr::Mul(vec![ExprId(4), ExprId(2)]), // 5 = c1*w2
                Expr::Mul(vec![ExprId(4), ExprId(3)]), // 6 = c1*w3
                Expr::Add(vec![ExprId(4), ExprId(2)]), // 7 = c1+w2
            ],
            vec![
                claim_only_root(ExprId(5), 0),
                claim_only_root(ExprId(6), 1),
                claim_only_root(ExprId(7), 2),
            ],
        );
        let d = distill(&l, BwdRegime::Ext, &HashMap::new(), None);
        let decisions = all_sites(&d);
        let c = compile_distilled(&d, 8, Some(&decisions)).expect("b8 compile under pressure");
        assert_result_in_acc(&c.program);
        assert!(c.stats.max_live_cells <= 8, "placement must fit b8, got {}", c.stats.max_live_cells);
        assert!(c.stats.cell_reads > 0, "spill/residency traffic expected under pressure");
        assert!(c.stats.cell_stores > 0);
    }

    // ── replay/serve + admission alignment (rewritten LookupValue + FoldSource) ──

    /// Canonical: q = w0 + w1; lv = LookupValue{query = q}; root = lv*lv + w2.
    /// Distilled (Ext): the lv leaf is REWRITTEN to q (fan-out 2 site) and the
    /// Read leaves become FoldSources.
    fn lookup_fold_layer() -> DagLayer {
        layer(
            vec![
                read_src(0),
                read_src(1),
                SourceInfo {
                    kind: SourceKind::LookupValue {
                        kind: cs::gkr_compiler::dag_ir::LookupValueKind::GenericColumn { column: 0 },
                        set_index: 0,
                        query: ExprId(2),
                    },
                },
                read_src(2),
            ],
            vec![
                Expr::Source(SourceId(0)),             // 0 = w0
                Expr::Source(SourceId(1)),             // 1 = w1
                Expr::Add(vec![ExprId(0), ExprId(1)]), // 2 = q (the query)
                Expr::Source(SourceId(2)),             // 3 = lv
                Expr::Source(SourceId(3)),             // 4 = w2
                Expr::Mul(vec![ExprId(3), ExprId(3)]), // 5 = lv*lv
                Expr::Add(vec![ExprId(5), ExprId(4)]), // 6 = root
            ],
            vec![claim_only_root(ExprId(6), 0)],
        )
    }

    /// Locate distilled leaf ExprIds by their Read column, and q as the Add of
    /// the two w0/w1 leaves.
    fn find_distilled_ids(d: &DistilledLayer) -> (ExprId, ExprId, ExprId, ExprId) {
        let mut w = BTreeMap::new(); // column -> leaf ExprId
        for (i, e) in d.layer.exprs.iter().enumerate() {
            if let Expr::Source(sid) = e {
                if let SourceKind::Read { place: ReadPlace::BaseLayerWitness { column } } =
                    &d.layer.sources[sid.0 as usize].kind
                {
                    w.insert(*column, ExprId(i as u32));
                }
            }
        }
        let (w0, w1, w2) = (w[&0], w[&1], w[&2]);
        let q = d
            .layer
            .exprs
            .iter()
            .enumerate()
            .find_map(|(i, e)| match e {
                Expr::Add(ch) if ch.len() == 2 && ch.contains(&w0) && ch.contains(&w1) => {
                    Some(ExprId(i as u32))
                }
                _ => None,
            })
            .expect("distilled q = Add(w0, w1)");
        (w0, w1, w2, q)
    }

    /// Drain a value's occurrence stream, returning its total queued count.
    fn drain(streams: &mut OccurrenceStreams, v: ExprId) -> usize {
        let mut n = 0;
        while streams.effective_priority(v).is_some() {
            streams.serve(v);
            n += 1;
        }
        n
    }

    #[test]
    fn replay_serve_counts_match_uncached_emission() {
        let l = lookup_fold_layer();
        let d = distill(&l, BwdRegime::Ext, &HashMap::new(), None);
        // The LookupValue leaf must be gone (rewritten to its query).
        assert!(!d
            .layer
            .sources
            .iter()
            .any(|s| matches!(s.kind, SourceKind::LookupValue { .. })));
        let (w0, w1, w2, q) = find_distilled_ids(&d);
        let root_expr = d.layer.roots[d.root.0 as usize].expr;
        let terms = spine_terms(&d);
        assert_eq!(terms.len(), 2, "spine = [Mul(q,q), w2] after flatten");

        // Replay stream counts.
        let decisions = all_sites(&d);
        let mut streams = OccurrenceStreams::build_bwd_root(
            &d.layer,
            d.root,
            root_expr,
            &terms,
            &decisions,
            &distilled_site_domain(&d),
        );
        assert_eq!(drain(&mut streams, root_expr), 1, "one RootOutput serve");
        assert_eq!(drain(&mut streams, q), 2, "q demanded once per Mul operand slot");
        assert_eq!(drain(&mut streams, w0), 2, "w0 demanded once per q recompute");
        assert_eq!(drain(&mut streams, w1), 2);
        assert_eq!(
            drain(&mut streams, w2),
            0,
            "w2 is a spine TERM — the driver decomposes it, no operand site of its own"
        );

        // Uncached emission: every serve of a leaf is exactly one Special use.
        let c = compile_distilled(&d, 16, None).expect("uncached compile");
        assert_result_in_acc(&c.program);
        let desc_of = |e: ExprId| *d.leaf_descs.get(&e).expect("fold leaf desc");
        assert_eq!(count_desc_uses(&c.program, desc_of(w0)), 2);
        assert_eq!(count_desc_uses(&c.program, desc_of(w1)), 2);
        assert_eq!(count_desc_uses(&c.program, desc_of(w2)), 1, "one use as a term");
        assert_eq!(c.stats_ext.fold_uses, 5);
        assert_eq!(c.stats_ext.fold_traffic, 20);
    }

    #[test]
    fn replay_admission_reflects_in_emission() {
        // With decisions, q (fan-out 2, in the distilled domain) is admitted at
        // its first demand: one recompute (w0/w1 gathered ONCE) + a cell re-read.
        let l = lookup_fold_layer();
        let d = distill(&l, BwdRegime::Ext, &HashMap::new(), None);
        let (w0, w1, w2, _q) = find_distilled_ids(&d);
        let decisions = all_sites(&d);
        let c = compile_distilled(&d, 16, Some(&decisions)).expect("cached compile");
        assert_result_in_acc(&c.program);
        let desc_of = |e: ExprId| *d.leaf_descs.get(&e).expect("fold leaf desc");
        assert_eq!(count_desc_uses(&c.program, desc_of(w0)), 1, "q recomputed once (admitted)");
        assert_eq!(count_desc_uses(&c.program, desc_of(w1)), 1);
        assert_eq!(count_desc_uses(&c.program, desc_of(w2)), 1);
        assert!(count_smem_reads(&c.program) > 0, "q's second use must read its cell");
    }

    // ── bindings invariance ───────────────────────────────────────────────────

    #[test]
    fn program_bytes_invariant_across_bindings() {
        let l = lookup_fold_layer();
        let d = distill(&l, BwdRegime::Ext, &HashMap::new(), None);
        let decisions = all_sites(&d);

        let c1 = compile_distilled(&d, 16, Some(&decisions)).expect("compile 1");
        let b0 = bind(&d, MaterializationPolicy::AlwaysMaterialize, 0);
        let b1 = bind(&d, MaterializationPolicy::LazyUpTo(2), 5);
        assert_ne!(b0.states, b1.states, "bindings genuinely vary (non-vacuous)");

        let c2 = compile_distilled(&d, 16, Some(&decisions)).expect("compile 2");
        let e1 = encode(&c1.program).expect("encode 1");
        let e2 = encode(&c2.program).expect("encode 2");
        assert_eq!(e1, e2, "compile takes no bindings: bytes identical across bind() variations");
    }
}
