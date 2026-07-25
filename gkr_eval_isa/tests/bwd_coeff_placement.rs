//! Task 5 gates: Ext-first/BF-second physical placement with pathological move
//! repair (design §7.3), the §8 value-use contract, and the §12.2 cell-liveness
//! certificate.
//!
//! The move repair is gated on a SYNTHETIC layer, because production layers are
//! large enough that a hand-picked coordinate would prove nothing about WHICH
//! quad was cleared. The fixture is not invented, though: it was found by fuzzing
//! real `page_projections` output and then shrunk, so the plan it places is one
//! the production pager actually emits. The corpus then gates termination, move
//! scarcity and capacity compliance at every budget `c2`..`c16`.
//!
//! Nothing here touches source-window binding or the u16 encoding — those are
//! Tasks 6 and 7. Every lane number is a physical BF lane.

mod common;

use std::collections::{BTreeMap, BTreeSet};

use common::{FIXTURES, layers_with_bwd_roots};
use cs::gkr_compiler::dag_ir::{BwdRegime, FieldKind, ReadPlace};
use gkr_eval_isa::bwd::coeff::place::{
    CellRead, CoeffPlacement, LivenessError, PlacementError, PlacementFloor, PlanAction,
    ScheduledInstr, ValueUse, certify_cell_liveness, place_paging_plan,
};
use gkr_eval_isa::bwd::coeff::schedule::{
    CellBudget, OpCounts, PagingPlan, PagingRequest, ProjectionOutcome, SourcePrice, ValueWidth,
    certify_paging_plan, default_target_depth, page_projections, source_prices,
    stable_normalized_order,
};
use gkr_eval_isa::bwd::coeff::{
    CoeffLayer, CoeffSource, CoeffTerm, CoefficientRecipeId, ProjectionId, SourceId, TermId,
    census_coeff_layer, lower_coeff_layer_traced,
};
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::bwd::source::OriginLeaf;
use rayon::prelude::*;

// ── Synthetic construction ───────────────────────────────────────────────────

fn read_source(column: usize, field: FieldKind) -> CoeffSource {
    CoeffSource { origin: OriginLeaf::Read(ReadPlace::BaseLayerMemory { column }), field }
}

fn price_of(field: FieldKind) -> SourcePrice {
    match field {
        FieldKind::Base => {
            SourcePrice { width: ValueWidth::Bf, element_bytes: 4, endpoint_ops: OpCounts::ZERO }
        }
        FieldKind::Ext => {
            SourcePrice { width: ValueWidth::E4, element_bytes: 16, endpoint_ops: OpCounts::ZERO }
        }
    }
}

fn synthetic(regime: BwdRegime, fields: &[FieldKind], terms: Vec<CoeffTerm>) -> CoeffLayer {
    for (i, term) in terms.iter().enumerate() {
        assert_eq!(term.id(), TermId(i as u32), "synthetic terms must be dense and in order");
    }
    CoeffLayer {
        regime,
        c_init: None,
        coefficients: Vec::new(),
        sources: fields.iter().copied().enumerate().map(|(i, f)| read_source(i, f)).collect(),
        terms,
    }
}

fn c0(id: u32, source: u32, field: FieldKind) -> CoeffTerm {
    CoeffTerm::C0Linear {
        id: TermId(id),
        coefficient: CoefficientRecipeId::ONE,
        value: ProjectionId::endpoint0(SourceId(source)),
        field,
    }
}

fn c2(id: u32, lhs: u32, lhs_field: FieldKind, rhs: u32, rhs_field: FieldKind) -> CoeffTerm {
    CoeffTerm::C2Product {
        id: TermId(id),
        coefficient: CoefficientRecipeId::ONE,
        lhs: ProjectionId::delta(SourceId(lhs)),
        rhs: ProjectionId::delta(SourceId(rhs)),
        lhs_field,
        rhs_field,
    }
}

fn dual(id: u32, lhs: u32, rhs: u32) -> CoeffTerm {
    CoeffTerm::DualProduct {
        id: TermId(id),
        coefficient: CoefficientRecipeId::ONE,
        lhs: SourceId(lhs),
        rhs: SourceId(rhs),
    }
}

fn request(cells: u8) -> PagingRequest {
    PagingRequest { budget: CellBudget::new(cells).expect("c2..c16"), target_depth: 0 }
}

/// Page and place one synthetic layer at one budget, checking the two
/// certificates on the way through.
fn page_and_place(
    layer: &CoeffLayer,
    prices: &[SourcePrice],
    cells: u8,
) -> (PagingPlan, CoeffPlacement) {
    let order = stable_normalized_order(layer);
    let plan = page_projections(layer, prices, request(cells), &order).expect("pager");
    certify_paging_plan(layer, prices, &plan).expect("paging certificate");
    let placement = place_paging_plan(layer, prices, &plan).expect("placement");
    certify_cell_liveness(layer, prices, &plan, &placement).expect("liveness certificate");
    (plan, placement)
}

// ── The pathological fixture ─────────────────────────────────────────────────

/// A layer whose `c2` paging plan CANNOT be seated by the offline two-pass even
/// though its peak weighted occupancy fits, and whose event-scan repair needs
/// exactly one `MoveBF`.
///
/// Found by fuzzing real `page_projections` output over random small layers and
/// then shrinking by term removal, so every step of the plan it places is one the
/// production pager produced from a stable normalized order. `Ext` source 3
/// competes with four `Bf` sources for two quads, which is exactly the mixed-width
/// fragmentation §7.3 keeps moves for.
fn pathological_layer() -> (CoeffLayer, Vec<SourcePrice>) {
    use FieldKind::{Base as B, Ext as E};
    let fields = [B, B, B, E, B];
    let terms = vec![
        c2(0, 3, E, 4, B),
        c2(1, 0, B, 1, B),
        c2(2, 1, B, 2, B),
        c2(3, 0, B, 2, B),
        c2(4, 1, B, 2, B),
        c0(5, 1, B),
        c0(6, 4, B),
        c2(7, 3, E, 2, B),
        c2(8, 1, B, 3, E),
    ];
    let prices = fields.iter().copied().map(price_of).collect();
    (synthetic(BwdRegime::R0, &fields, terms), prices)
}

/// The regression fixture for the placer/certificate move-destination
/// disagreement.
///
/// At `c2` this layer's plan forces a two-move repair before term 4, and one of
/// those moves lands `SourceId(3).Delta` in a lane that the SECOND operand slot
/// of that same term then fills. That is legal — the plan drops the relocated
/// value at that step and nothing reads it again — but the certificate used to
/// reject every move destination any slot of the term filled, so
/// `place_paging_plan` returned `Ok` and `certify_cell_liveness` returned
/// `MoveDestinationNotDead`. Found by a 2.4M-placement hunt (8 hits), which is far
/// too rare for the randomized gate to catch, so it is pinned here instead.
fn later_slot_reclaim_layer() -> (CoeffLayer, Vec<SourcePrice>) {
    use FieldKind::{Base as B, Ext as E};
    let fields = [B, B, B, B, B, B, B, E];
    let terms = vec![
        c2(0, 7, E, 5, B),
        c2(1, 3, B, 5, B),
        c0(2, 7, E),
        c2(3, 3, B, 4, B),
        c2(4, 7, E, 1, B),
        c2(5, 1, B, 6, B),
        c2(6, 2, B, 1, B),
        c2(7, 6, B, 2, B),
        c2(8, 5, B, 7, E),
        c0(9, 5, B),
        c2(10, 5, B, 7, E),
        c0(11, 4, B),
        c2(12, 3, B, 4, B),
        c0(13, 3, B),
        c2(14, 3, B, 3, B),
    ];
    let prices = fields.iter().copied().map(price_of).collect();
    (synthetic(BwdRegime::R0, &fields, terms), prices)
}

/// A layer with no mixed-width contention: uniform `Ext` sources at a comfortable
/// budget, the shape design §7.3 expects to stay move-free.
fn uniform_ext_layer() -> (CoeffLayer, Vec<SourcePrice>) {
    let fields = [FieldKind::Ext; 4];
    let terms = vec![
        dual(0, 0, 1),
        dual(1, 1, 2),
        c0(2, 0, FieldKind::Ext),
        dual(3, 2, 3),
        c0(4, 3, FieldKind::Ext),
        dual(5, 0, 3),
    ];
    let prices = fields.iter().copied().map(price_of).collect();
    (synthetic(BwdRegime::Ext, &fields, terms), prices)
}

/// A mixed BF/E4 layer at a budget wide enough for the two-pass to seat it.
fn mixed_r0_layer() -> (CoeffLayer, Vec<SourcePrice>) {
    use FieldKind::{Base as B, Ext as E};
    let fields = [B, E, B, B, E, B];
    let terms = vec![
        c0(0, 0, B),
        c2(1, 2, B, 4, E),
        c2(2, 1, E, 3, B),
        c0(3, 4, E),
        c2(4, 0, B, 5, B),
        c2(5, 1, E, 4, E),
        c0(6, 2, B),
        c2(7, 3, B, 5, B),
    ];
    let prices = fields.iter().copied().map(price_of).collect();
    (synthetic(BwdRegime::R0, &fields, terms), prices)
}

// ── Stream walkers (independent of the placement module's internals) ─────────

/// Every `(projection, base lane, width)` the stream READS from a cell.
fn cell_reads(
    placement: &CoeffPlacement,
    prices: &[SourcePrice],
) -> Vec<(usize, ProjectionId, u16, ValueWidth)> {
    let mut out = Vec::new();
    for (index, instr) in placement.instrs.iter().enumerate() {
        let ScheduledInstr::Term { uses, .. } = instr else { continue };
        for u in uses {
            match u {
                ValueUse::Cell(CellRead::Single { projection, lane }) => {
                    out.push((index, *projection, *lane, prices[projection.source.0 as usize].width))
                }
                ValueUse::Cell(CellRead::Pair { source, endpoint0_lane, delta_lane }) => {
                    let w = prices[source.0 as usize].width;
                    out.push((index, ProjectionId::endpoint0(*source), *endpoint0_lane, w));
                    out.push((index, ProjectionId::delta(*source), *delta_lane, w));
                }
                ValueUse::PlannedDelta { source, endpoint0, delta } => {
                    let w = prices[source.0 as usize].width;
                    if let PlanAction::UseResident { lane } = endpoint0 {
                        out.push((index, ProjectionId::endpoint0(*source), *lane, w));
                    }
                    if let PlanAction::UseResident { lane } = delta {
                        out.push((index, ProjectionId::delta(*source), *lane, w));
                    }
                }
                ValueUse::Direct { .. } | ValueUse::Fill { .. } => {}
            }
        }
    }
    out
}

/// Every `(projection, base lane, width)` the stream WRITES with a fill.
fn fills(
    placement: &CoeffPlacement,
    prices: &[SourcePrice],
) -> Vec<(usize, ProjectionId, u16, ValueWidth)> {
    let mut out = Vec::new();
    for (index, instr) in placement.instrs.iter().enumerate() {
        let ScheduledInstr::Term { uses, .. } = instr else { continue };
        for u in uses {
            match u {
                ValueUse::Fill { projection, dst_lane } => {
                    out.push((index, *projection, *dst_lane, prices[projection.source.0 as usize].width))
                }
                ValueUse::PlannedDelta { source, endpoint0, delta } => {
                    let w = prices[source.0 as usize].width;
                    if let PlanAction::Fill { lane } = endpoint0 {
                        out.push((index, ProjectionId::endpoint0(*source), *lane, w));
                    }
                    if let PlanAction::Fill { lane } = delta {
                        out.push((index, ProjectionId::delta(*source), *lane, w));
                    }
                }
                ValueUse::Direct { .. } | ValueUse::Cell(_) => {}
            }
        }
    }
    out
}

fn moves(placement: &CoeffPlacement) -> Vec<(usize, ProjectionId, u16, u16, bool)> {
    placement
        .instrs
        .iter()
        .enumerate()
        .filter_map(|(i, instr)| match instr {
            ScheduledInstr::MoveBF { projection, from_lane, to_lane } => {
                Some((i, *projection, *from_lane, *to_lane, false))
            }
            ScheduledInstr::MoveE4 { projection, from_lane, to_lane } => {
                Some((i, *projection, *from_lane, *to_lane, true))
            }
            ScheduledInstr::Term { .. } => None,
        })
        .collect()
}

// ── 1. Normal cases are move-free ────────────────────────────────────────────

#[test]
fn two_pass_placement_is_move_free_on_normal_cases() {
    let cases: Vec<(&str, (CoeffLayer, Vec<SourcePrice>))> =
        vec![("uniform_ext", uniform_ext_layer()), ("mixed_r0", mixed_r0_layer())];
    for (name, (layer, prices)) in &cases {
        for cells in [4u8, 6, 8, 12, 16] {
            let (_, placement) = page_and_place(layer, prices, cells);
            assert!(
                !placement.stats.repaired,
                "[{name} c{cells}] the offline two-pass must seat a normal case"
            );
            assert_eq!(placement.stats.bf_moves, 0, "[{name} c{cells}] unexpected BF move");
            assert_eq!(placement.stats.e4_moves, 0, "[{name} c{cells}] unexpected E4 move");
            assert!(moves(&placement).is_empty(), "[{name} c{cells}] move in the stream");
        }
    }

    // The same claim on real layers, where it actually matters.
    let sample: Vec<_> = corpus_coordinates().into_iter().take(8).collect();
    for (name, li, regime, layer, prices) in &sample {
        for cells in [8u8, 16] {
            let order = stable_normalized_order(layer);
            let req = PagingRequest { budget: CellBudget::new(cells).unwrap(), target_depth: default_target_depth(*regime) };
            let plan = page_projections(layer, prices, req, &order).expect("pager");
            let placement = place_paging_plan(layer, prices, &plan).expect("placement");
            assert!(
                !placement.stats.repaired,
                "[{name} L{li} {regime:?} c{cells}] a production layer needed repair"
            );
        }
    }
}

// ── 2. Pathological fragmentation ────────────────────────────────────────────

#[test]
fn pathological_fragmentation_inserts_one_bf_move() {
    let (layer, prices) = pathological_layer();
    let (plan, placement) = page_and_place(&layer, &prices, 2);

    assert!(placement.stats.repaired, "the offline two-pass must have failed here");
    assert_eq!(placement.stats.bf_moves, 1, "exactly one BF relocation repairs it");
    assert_eq!(placement.stats.e4_moves, 0, "no E4 relocation is needed");
    assert!(
        placement.stats.peak_lanes <= plan.request.budget.lanes(),
        "peak {} exceeds the c2 budget {}",
        placement.stats.peak_lanes,
        plan.request.budget.lanes()
    );

    let emitted = moves(&placement);
    assert_eq!(emitted.len(), 1, "one move instruction in the stream: {emitted:?}");
    let (index, projection, from_lane, to_lane, is_e4) = emitted[0];
    assert!(!is_e4, "the repair relocates a BF projection");
    assert_eq!(
        prices[projection.source.0 as usize].width,
        ValueWidth::Bf,
        "a MoveBF must name a BF projection"
    );
    assert_ne!(from_lane, to_lane, "a move must actually relocate");

    // The move precedes the term whose fill forced it, and that term is the next
    // instruction: §8's "a local move is the only standalone cell-file action".
    assert!(
        matches!(placement.instrs.get(index + 1), Some(ScheduledInstr::Term { .. })),
        "the move must immediately precede the term it clears a quad for"
    );

    // A move destination may never be a lane the following term reads.
    let ScheduledInstr::Term { term, .. } = placement.instrs[index + 1] else { unreachable!() };
    let read_lanes: BTreeSet<u16> = cell_reads(&placement, &prices)
        .into_iter()
        .filter(|(i, ..)| *i == index + 1)
        .flat_map(|(_, _, lane, w)| lane..lane + w.lanes() as u16)
        .collect();
    assert!(
        !read_lanes.contains(&to_lane),
        "move into lane {to_lane} clobbers an input of term {term:?}"
    );
    let read_projections: BTreeSet<ProjectionId> = cell_reads(&placement, &prices)
        .into_iter()
        .filter(|(i, ..)| *i == index + 1)
        .map(|(_, p, ..)| p)
        .collect();
    assert!(
        !read_projections.contains(&projection),
        "a value that is an input of the current term must never be moved"
    );
}

// ── 3. Placement changes no paging decision ──────────────────────────────────

#[test]
fn placement_never_changes_paging_decisions() {
    let cases: Vec<(&str, (CoeffLayer, Vec<SourcePrice>))> = vec![
        ("uniform_ext", uniform_ext_layer()),
        ("mixed_r0", mixed_r0_layer()),
        ("pathological", pathological_layer()),
    ];
    for (name, (layer, prices)) in &cases {
        for budget in CellBudget::ALL {
            let order = stable_normalized_order(layer);
            let req = PagingRequest { budget, target_depth: 0 };
            let plan = page_projections(layer, prices, req, &order).expect("pager");

            // The ONLY mechanism that proves a decision was not changed. Re-running
            // `certify_paging_plan` would accept a consistently-updated but
            // different-and-legal eviction, so it proves nothing here.
            let before = plan.canonical_bytes();
            let placement = place_paging_plan(layer, prices, &plan).expect("placement");
            assert_eq!(
                plan.canonical_bytes(),
                before,
                "[{name} {}] placement mutated the paging plan",
                budget.label()
            );

            // Second, weaker check: the plan is still a VALID plan.
            certify_paging_plan(layer, prices, &plan).expect("plan still certifies");
            // And the emitted stream realizes exactly this plan's residency.
            certify_cell_liveness(layer, prices, &plan, &placement)
                .unwrap_or_else(|e| panic!("[{name} {}] liveness: {e:?}", budget.label()));
        }
    }
}

// ── 4. A fill consumes the resolved register ─────────────────────────────────

#[test]
fn fill_uses_the_resolved_register_without_reload() {
    let cases: Vec<(&str, (CoeffLayer, Vec<SourcePrice>), u8)> = vec![
        ("uniform_ext", uniform_ext_layer(), 4),
        ("mixed_r0", mixed_r0_layer(), 4),
        ("pathological", pathological_layer(), 2),
    ];
    let mut total_fills = 0usize;
    for (name, (layer, prices), cells) in &cases {
        let (_, placement) = page_and_place(layer, prices, *cells);
        total_fills += fills(&placement, prices).len();

        for instr in &placement.instrs {
            let ScheduledInstr::Term { term, uses, .. } = instr else { continue };
            // Per term: the projections this term FILLS, and the ones it reads back
            // out of a cell. A fill that reloaded its own destination would appear
            // in both.
            let filled: BTreeSet<ProjectionId> = uses
                .iter()
                .flat_map(|u| match u {
                    ValueUse::Fill { projection, .. } => vec![*projection],
                    ValueUse::PlannedDelta { source, endpoint0, delta } => {
                        let mut v = Vec::new();
                        if matches!(endpoint0, PlanAction::Fill { .. }) {
                            v.push(ProjectionId::endpoint0(*source));
                        }
                        if matches!(delta, PlanAction::Fill { .. }) {
                            v.push(ProjectionId::delta(*source));
                        }
                        v
                    }
                    _ => Vec::new(),
                })
                .collect();
            let reloaded: BTreeSet<ProjectionId> = uses
                .iter()
                .flat_map(|u| match u {
                    ValueUse::Cell(CellRead::Single { projection, .. }) => vec![*projection],
                    ValueUse::Cell(CellRead::Pair { source, .. }) => {
                        vec![ProjectionId::endpoint0(*source), ProjectionId::delta(*source)]
                    }
                    ValueUse::PlannedDelta { source, endpoint0, delta } => {
                        let mut v = Vec::new();
                        if matches!(endpoint0, PlanAction::UseResident { .. }) {
                            v.push(ProjectionId::endpoint0(*source));
                        }
                        if matches!(delta, PlanAction::UseResident { .. }) {
                            v.push(ProjectionId::delta(*source));
                        }
                        v
                    }
                    _ => Vec::new(),
                })
                .collect();
            let both: Vec<_> = filled.intersection(&reloaded).collect();
            assert!(
                both.is_empty(),
                "[{name}] term {term:?} fills and reloads {both:?} — a fill must consume the \
                 just-resolved register value"
            );
        }

        // A `Fill` carries only a destination lane, never a source lane, so the
        // shape itself cannot express a reload. Pin that as a stream property so a
        // later task cannot widen it back.
        for (_, _, lane, width) in fills(&placement, prices) {
            assert!(
                u32::from(lane) + width.lanes() <= placement.request.budget.lanes(),
                "[{name}] fill destination out of bounds"
            );
        }
    }
    assert!(total_fills > 0, "vacuous: no fill was emitted at all");
}

// ── 5. A resident cell is never re-materialized ──────────────────────────────

#[test]
fn resident_cell_is_not_materialized_again() {
    let cases: Vec<(&str, (CoeffLayer, Vec<SourcePrice>), u8)> = vec![
        ("uniform_ext", uniform_ext_layer(), 4),
        ("mixed_r0", mixed_r0_layer(), 4),
        ("pathological", pathological_layer(), 2),
    ];
    let mut total_hits = 0u64;
    for (name, (layer, prices), cells) in &cases {
        let (plan, placement) = page_and_place(layer, prices, *cells);
        total_hits += plan.cost.hits;

        // Every projection the plan declares a `Hit` on is served from its cell in
        // the emitted stream — never resolved from source again.
        let read: BTreeSet<(usize, ProjectionId)> =
            cell_reads(&placement, prices).into_iter().map(|(i, p, ..)| (i, p)).collect();
        let filled: BTreeSet<ProjectionId> =
            fills(&placement, prices).into_iter().map(|(_, p, ..)| p).collect();
        let mut term_of_step: Vec<TermId> = Vec::new();
        for a in &plan.actions {
            term_of_step.push(a.term);
        }
        // Map term -> instruction index once, so a hit can be located in the stream.
        let mut instr_of_term: BTreeMap<TermId, usize> = BTreeMap::new();
        for (i, instr) in placement.instrs.iter().enumerate() {
            if let ScheduledInstr::Term { term, .. } = instr {
                instr_of_term.insert(*term, i);
            }
        }
        let mut hits = 0usize;
        for action in &plan.actions {
            for pa in &action.projections {
                if pa.outcome != ProjectionOutcome::Hit {
                    continue;
                }
                hits += 1;
                let index = instr_of_term[&action.term];
                assert!(
                    read.contains(&(index, pa.projection)),
                    "[{name}] hit on {:?} at term {:?} was not served from its cell",
                    pa.projection,
                    action.term
                );
            }
        }
        assert!(hits > 0, "[{name}] vacuous: the plan declares no hit");

        // The number of emitted fills equals the number of fills the plan decided.
        assert_eq!(
            fills(&placement, prices).len() as u64,
            plan.cost.fills,
            "[{name}] emitted fill count must equal the plan's"
        );
        assert!(!filled.is_empty(), "[{name}] vacuous: nothing was filled");
    }
    assert!(total_hits > 0);
}

// ── 6. E4 lanes are four-lane-aligned ────────────────────────────────────────

#[test]
fn e4_cells_are_four_lane_aligned() {
    let cases: Vec<(&str, (CoeffLayer, Vec<SourcePrice>), u8)> = vec![
        ("uniform_ext", uniform_ext_layer(), 4),
        ("mixed_r0", mixed_r0_layer(), 4),
        ("pathological", pathological_layer(), 2),
    ];
    let mut e4_lanes_seen = 0usize;
    for (name, (layer, prices), cells) in &cases {
        let (_, placement) = page_and_place(layer, prices, *cells);
        let capacity = placement.request.budget.lanes();
        let mut check = |what: &str, lane: u16, width: ValueWidth| {
            assert!(
                u32::from(lane) + width.lanes() <= capacity,
                "[{name}] {what} lane {lane} (+{}) exceeds {capacity}",
                width.lanes()
            );
            if width == ValueWidth::E4 {
                assert_eq!(lane % 4, 0, "[{name}] {what} E4 lane {lane} is not four-lane-aligned");
                e4_lanes_seen += 1;
            }
        };
        for (_, _, lane, width) in cell_reads(&placement, prices) {
            check("read", lane, width);
        }
        for (_, _, lane, width) in fills(&placement, prices) {
            check("fill", lane, width);
        }
        for (_, projection, from_lane, to_lane, _) in moves(&placement) {
            let width = prices[projection.source.0 as usize].width;
            check("move source", from_lane, width);
            check("move destination", to_lane, width);
        }
    }
    assert!(e4_lanes_seen > 0, "vacuous: no E4 lane appeared in any stream");
}

// ── 7. The repair is deterministic ───────────────────────────────────────────

#[test]
fn move_repair_is_deterministic() {
    let (layer, prices) = pathological_layer();
    let order = stable_normalized_order(&layer);
    let plan = page_projections(&layer, &prices, request(2), &order).expect("pager");

    let first = place_paging_plan(&layer, &prices, &plan).expect("placement");
    for _ in 0..8 {
        let again = place_paging_plan(&layer, &prices, &plan).expect("placement");
        assert_eq!(first.instrs, again.instrs, "repair is not deterministic");
        assert_eq!(first.residences, again.residences, "residence lanes are not deterministic");
        assert_eq!(first.stats, again.stats, "placement stats are not deterministic");
    }

    // The candidate preference is `(fewest moves, lowest destination lanes, lowest
    // source lanes, ProjectionId)`. With one move the first key already decides:
    // the chosen quad is the one needing the fewest relocations, so no other quad
    // could have been cleared with zero or one cheaper move.
    let emitted = moves(&first);
    assert_eq!(emitted.len(), 1);
    let (index, _, _, to_lane, _) = emitted[0];
    // The freed quad is the one the following term's E4 fill takes.
    let e4_fill_lane = fills(&first, &prices)
        .into_iter()
        .find(|(i, _, _, w)| *i == index + 1 && *w == ValueWidth::E4)
        .map(|(_, _, lane, _)| lane)
        .expect("the repair exists to seat an E4 fill");
    assert_eq!(e4_fill_lane % 4, 0, "the cleared quad is four-lane-aligned");
    assert!(
        !(e4_fill_lane..e4_fill_lane + 4).contains(&to_lane),
        "a relocation must not land inside the quad it is clearing"
    );

    // Determinism across every budget, not only the repaired one.
    for budget in CellBudget::ALL {
        let req = PagingRequest { budget, target_depth: 0 };
        let plan = page_projections(&layer, &prices, req, &order).expect("pager");
        let a = place_paging_plan(&layer, &prices, &plan).expect("placement");
        let b = place_paging_plan(&layer, &prices, &plan).expect("placement");
        assert_eq!(a.instrs, b.instrs, "{} is not deterministic", budget.label());
    }
}

// ── 8. The liveness certificate rejects real corruption ──────────────────────

#[test]
fn liveness_certificate_rejects_overlap_and_stale_reads() {
    let (layer, prices) = mixed_r0_layer();
    let (plan, good) = page_and_place(&layer, &prices, 4);

    // (a) STALE READ: repoint a `Cell` read at a lane its projection does not own.
    let mut stale = good.clone();
    let mut patched = false;
    for instr in stale.instrs.iter_mut() {
        let ScheduledInstr::Term { uses, .. } = instr else { continue };
        for u in uses.iter_mut() {
            if let ValueUse::Cell(CellRead::Single { projection, lane }) = u {
                // A different lane of the SAME width class, still in bounds and
                // still correctly aligned, so the rejection is about staleness and
                // not about bounds or alignment.
                let step = prices[projection.source.0 as usize].width.lanes() as u16;
                *lane = (*lane + step) % (plan.request.budget.lanes() as u16);
                patched = true;
                break;
            }
        }
        if patched {
            break;
        }
    }
    assert!(patched, "vacuous: the stream has no single-projection cell read to corrupt");
    let err = certify_cell_liveness(&layer, &prices, &plan, &stale)
        .expect_err("a stale cell read must be rejected");
    assert!(
        matches!(
            err,
            LivenessError::StaleCellRead { .. } | LivenessError::ResidentWithoutLanes { .. }
        ),
        "expected a stale-read rejection, got {err:?}"
    );

    // (b) OVERLAP: repoint a fill onto a lane a still-resident projection owns.
    //     Find a step whose `resident_after` holds a projection other than the one
    //     being filled, and aim the fill at that projection's lane.
    let mut overlap = good.clone();
    let live_lane = cell_reads(&good, &prices)
        .into_iter()
        .map(|(_, _, lane, _)| lane)
        .next()
        .expect("the stream reads at least one resident cell");
    let mut aimed = false;
    for instr in overlap.instrs.iter_mut() {
        let ScheduledInstr::Term { uses, .. } = instr else { continue };
        for u in uses.iter_mut() {
            match u {
                ValueUse::Fill { dst_lane, projection }
                    if prices[projection.source.0 as usize].width == ValueWidth::Bf =>
                {
                    *dst_lane = live_lane;
                    aimed = true;
                }
                ValueUse::PlannedDelta { source, delta: PlanAction::Fill { lane }, .. }
                    if prices[source.0 as usize].width == ValueWidth::Bf =>
                {
                    *lane = live_lane;
                    aimed = true;
                }
                _ => {}
            }
            if aimed {
                break;
            }
        }
        if aimed {
            break;
        }
    }
    assert!(aimed, "vacuous: the stream has no BF fill to redirect");
    let err = certify_cell_liveness(&layer, &prices, &plan, &overlap)
        .expect_err("two live values sharing a lane must be rejected");
    assert!(
        matches!(
            err,
            LivenessError::FillClobbersLiveValue { .. }
                | LivenessError::StaleCellRead { .. }
                | LivenessError::ResidentWithoutLanes { .. }
        ),
        "expected an overlap rejection, got {err:?}"
    );

    // (c) A fabricated move of an input of the term it precedes.
    let (path_layer, path_prices) = pathological_layer();
    let (path_plan, path_placement) = page_and_place(&path_layer, &path_prices, 2);
    let mut tampered = path_placement.clone();
    let (index, ..) = moves(&path_placement)[0];
    let ScheduledInstr::Term { .. } = tampered.instrs[index + 1] else { unreachable!() };
    // Guarded exactly as (a) and (b) are. This is the ONLY coverage of
    // `MoveOfCurrentTermInput`, so if the fixture ever stops offering a BF cell
    // read on the term the move precedes, the test must fail loudly rather than
    // skip and stay green.
    let (_, projection, lane, _) = cell_reads(&path_placement, &path_prices)
        .into_iter()
        .find(|(i, _, _, w)| *i == index + 1 && *w == ValueWidth::Bf)
        .expect(
            "vacuous: the pathological fixture must read a BF cell in the term its move \
             precedes, or MoveOfCurrentTermInput has no coverage",
        );
    tampered.instrs[index] =
        ScheduledInstr::MoveBF { projection, from_lane: lane, to_lane: lane };
    let err = certify_cell_liveness(&path_layer, &path_prices, &path_plan, &tampered)
        .expect_err("moving an input of the current term must be rejected");
    assert!(
        matches!(err, LivenessError::MoveOfCurrentTermInput { .. }),
        "expected a current-term-input rejection, got {err:?}"
    );

    // The unmutated placement still certifies, so the rejections above are about
    // the mutations and not about the certificate being broken.
    certify_cell_liveness(&layer, &prices, &plan, &good).expect("the good placement certifies");
}

/// Regression: a move destination a LATER operand slot of the same term reclaims.
///
/// The placer and the certificate must state one rule here, and it is the
/// certificate that was wrong: rejecting every lane any slot of the term fills is
/// over-strict, because a later slot may legitimately reclaim the relocated
/// value's lane once the plan has dropped it — and the placer cannot even know a
/// later slot's destination when it picks the move, since that lane is chosen
/// afterwards. The genuine hazard, an EARLIER slot's fill overwriting the
/// relocated value, is caught by `FillClobbersLiveValue`.
#[test]
fn move_destination_may_be_reclaimed_by_a_later_slot_fill() {
    let (layer, prices) = later_slot_reclaim_layer();
    let (_, placement) = page_and_place(&layer, &prices, 2);

    assert!(placement.stats.repaired, "the fixture must exercise the repair");
    let emitted = moves(&placement);
    assert_eq!(emitted.len(), 2, "the fixture's repair takes two BF moves: {emitted:?}");

    // The load-bearing shape: some move's destination is filled by a slot of the
    // very term it precedes. Without this the test would pass for the wrong reason.
    let fill_lanes: BTreeSet<(usize, u16)> = fills(&placement, &prices)
        .into_iter()
        .flat_map(|(i, _, lane, w)| (lane..lane + w.lanes() as u16).map(move |l| (i, l)))
        .collect();
    let reclaimed = emitted.iter().any(|&(index, projection, _, to_lane, _)| {
        let width = prices[projection.source.0 as usize].width;
        let mut next_term = index + 1;
        while !matches!(placement.instrs.get(next_term), Some(ScheduledInstr::Term { .. })) {
            next_term += 1;
        }
        (to_lane..to_lane + width.lanes() as u16).any(|l| fill_lanes.contains(&(next_term, l)))
    });
    assert!(
        reclaimed,
        "vacuous: no move destination is reclaimed by a fill of the term it precedes"
    );

    // And the whole thing certifies — which is what regressed.
    let order = stable_normalized_order(&layer);
    let plan = page_projections(&layer, &prices, request(2), &order).expect("pager");
    certify_cell_liveness(&layer, &prices, &plan, &placement)
        .expect("a later-slot reclaim is legal and must certify");
}

/// The other half of the pair: a move that lands where a fill of the same term
/// will overwrite it while the plan still holds the relocated value resident is
/// still rejected.
///
/// This pins what REPLACED the dropped all-slot `term_fill_lanes` clause. That
/// clause was over-strict (see the sibling test), but it did cover one genuine
/// hazard, and the argument that the hazard is still caught rests on two things
/// no test asserted until now: `write`'s `after.contains(&victim)` check, and the
/// end-of-step eviction that keeps `held` in step with `resident_after`. Narrow
/// either one and the hazard silently reopens with every other test green — which
/// is exactly the regression the dropped clause used to prevent.
///
/// Rather than probe a single lane, this sweeps the whole cell file and pins the
/// complete partition, so the rule's boundary is documented rather than sampled.
#[test]
fn move_into_a_lane_the_term_fills_is_still_rejected() {
    let (layer, prices) = later_slot_reclaim_layer();
    let (plan, good) = page_and_place(&layer, &prices, 2);

    // The second move is the one whose destination the later slot reclaims.
    let emitted = moves(&good);
    assert_eq!(emitted.len(), 2, "the fixture's repair takes two BF moves");
    let (index, projection, from_lane, legal_to, _) = emitted[1];
    let capacity = plan.request.budget.lanes() as u16;

    let mut clobbered: Vec<u16> = Vec::new();
    let mut not_dead: Vec<u16> = Vec::new();
    let mut accepted: Vec<u16> = Vec::new();
    for to_lane in 0..capacity {
        let mut tampered = good.clone();
        tampered.instrs[index] = ScheduledInstr::MoveBF { projection, from_lane, to_lane };
        match certify_cell_liveness(&layer, &prices, &plan, &tampered) {
            Ok(_) => accepted.push(to_lane),
            Err(LivenessError::FillClobbersLiveValue { victim, .. }) => {
                assert_eq!(
                    victim, projection,
                    "the clobbered value must be the relocated one, not a bystander"
                );
                clobbered.push(to_lane);
            }
            Err(LivenessError::MoveDestinationNotDead { .. }) => not_dead.push(to_lane),
            Err(e) => panic!("unexpected rejection for to_lane {to_lane}: {e:?}"),
        }
    }

    // Exactly one destination is legal: the later-slot reclaim the sibling test
    // covers. Everything else is rejected, by one of the two rules.
    assert_eq!(accepted, vec![legal_to], "only the later-slot reclaim may be accepted");
    // The lanes the term's E4 fill takes are the replacement rule's own case: the
    // move lands there, the fill overwrites it, and the plan still lists the
    // relocated value resident at that step.
    assert!(
        !clobbered.is_empty(),
        "vacuous: no destination exercised FillClobbersLiveValue, so nothing pins the \
         replacement for the dropped clause"
    );
    assert!(
        !not_dead.is_empty(),
        "vacuous: no destination exercised the surviving MoveDestinationNotDead clause"
    );
    assert_eq!(
        clobbered.len() + not_dead.len() + accepted.len(),
        capacity as usize,
        "every lane must be classified"
    );
    println!(
        "move destination partition: ok={accepted:?} \
         fill_clobbers_live={clobbered:?} not_dead={not_dead:?}"
    );
}

/// A plan built for one regime may not be placed against a layer of the other.
#[test]
fn placement_rejects_a_regime_mismatch() {
    let (layer, prices) = mixed_r0_layer();
    let order = stable_normalized_order(&layer);
    let plan = page_projections(&layer, &prices, request(4), &order).expect("pager");
    assert_eq!(plan.regime, BwdRegime::R0);

    let mut other = layer.clone();
    other.regime = BwdRegime::Ext;
    assert_eq!(
        place_paging_plan(&other, &prices, &plan),
        Err(PlacementError::RegimeMismatch {
            declared: BwdRegime::R0,
            found: BwdRegime::Ext
        }),
        "an R0 plan against an Ext layer describes a different program"
    );
    // And the matched pair still places, so the guard is not rejecting everything.
    place_paging_plan(&layer, &prices, &plan).expect("the matching regime still places");
}

// ── Production corpus ────────────────────────────────────────────────────────

/// Every `(circuit, layer, regime)` coordinate, lowered, priced, and censused.
#[allow(clippy::type_complexity)]
fn corpus_coordinates() -> Vec<(String, usize, BwdRegime, CoeffLayer, Vec<SourcePrice>)> {
    let mut out = Vec::new();
    for name in FIXTURES {
        for (li, canonical, cross) in layers_with_bwd_roots(name) {
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                let distilled = distill(&canonical, regime, &cross, None);
                let (lowered, _) = lower_coeff_layer_traced(&canonical, &distilled)
                    .unwrap_or_else(|e| panic!("[{name} L{li}] lowering: {e:?}"));
                let depth = default_target_depth(regime);
                let prices = source_prices(&lowered, &distilled, depth);
                out.push((name.to_string(), li, regime, lowered, prices));
            }
        }
    }
    out
}

#[test]
fn corpus_placement_terminates_and_certifies_every_budget() {
    let coordinates = corpus_coordinates();
    assert_eq!(coordinates.len(), 114, "57 backward-bearing layers x 2 regimes");

    struct Row {
        tag: String,
        max_moves: usize,
        total_moves: usize,
        repaired_budgets: usize,
        c16_peak: u32,
    }

    let rows: Vec<Row> = coordinates
        .par_iter()
        .map(|(name, li, regime, layer, prices)| {
            let tag = format!(
                "{name} L{li} {}",
                if *regime == BwdRegime::R0 { "R0" } else { "Ext" }
            );
            let order = stable_normalized_order(layer);
            let mut max_moves = 0usize;
            let mut total_moves = 0usize;
            let mut repaired_budgets = 0usize;
            let mut c16_peak = 0u32;
            for budget in CellBudget::ALL {
                let req =
                    PagingRequest { budget, target_depth: default_target_depth(*regime) };
                let plan = page_projections(layer, prices, req, &order)
                    .unwrap_or_else(|e| panic!("[{tag} {}] pager: {e:?}", budget.label()));
                let before = plan.canonical_bytes();
                let placement = place_paging_plan(layer, prices, &plan)
                    .unwrap_or_else(|e| panic!("[{tag} {}] placement: {e:?}", budget.label()));
                assert_eq!(
                    plan.canonical_bytes(),
                    before,
                    "[{tag} {}] placement mutated the plan",
                    budget.label()
                );
                certify_cell_liveness(layer, prices, &plan, &placement).unwrap_or_else(|e| {
                    panic!("[{tag} {}] liveness: {e:?}", budget.label())
                });
                assert!(
                    placement.stats.lanes_used <= budget.lanes(),
                    "[{tag} {}] lane {} exceeds capacity {}",
                    budget.label(),
                    placement.stats.lanes_used,
                    budget.lanes()
                );
                let m = placement.stats.bf_moves + placement.stats.e4_moves;
                assert_eq!(placement.stats.e4_moves, 0, "[{tag} {}] MoveE4", budget.label());
                max_moves = max_moves.max(m);
                total_moves += m;
                if placement.stats.repaired {
                    repaired_budgets += 1;
                }
                if budget.cells() == 16 {
                    c16_peak = plan.cost.peak_resident_lanes;
                }
            }
            Row { tag, max_moves, total_moves, repaired_budgets, c16_peak }
        })
        .collect();

    let saturating: Vec<&Row> = rows.iter().filter(|r| r.c16_peak == 64).collect();
    println!("c16-saturating coordinates (peak_resident_lanes == 64): {}", saturating.len());
    let saturating_ext = saturating.iter().filter(|r| r.tag.ends_with(" Ext")).count();
    let saturating_r0 = saturating.iter().filter(|r| r.tag.ends_with(" R0")).count();
    for r in &saturating {
        println!(
            "  SATURATED {} max_moves={} total_moves={} repaired_budgets={}",
            r.tag, r.max_moves, r.total_moves, r.repaired_budgets
        );
    }
    let with_moves: Vec<&Row> = rows.iter().filter(|r| r.total_moves > 0).collect();
    println!("coordinates needing any move: {}", with_moves.len());
    for r in &with_moves {
        println!("  MOVES {} max_moves={} total={}", r.tag, r.max_moves, r.total_moves);
    }
    let corpus_max_moves = rows.iter().map(|r| r.max_moves).max().unwrap_or(0);
    println!("realized move maximum over the whole corpus x c2..c16: {corpus_max_moves}");

    assert_eq!(saturating.len(), 16, "Task 4 measured 16 c16-saturating coordinates");
    // The split is the evidence for "mixed BF/E4 competition is an R0-only
    // phenomenon": Ext programs are priced at ONE fold depth, so every Ext source
    // is E4 and the cell file is uniformly quad-width — quad colouring alone is
    // then optimal and can never strand a single-lane value, because there are
    // none. Saturation is a LANE-pressure fact, not an alignment one, and pinning
    // the split is what makes that claim checkable rather than narrated.
    assert_eq!(saturating_ext, 14, "14 of the 16 c16-saturating coordinates are Ext");
    assert_eq!(saturating_r0, 2, "2 of the 16 c16-saturating coordinates are R0");
    // The offline two-pass seats EVERY production coordinate at EVERY budget.
    // Pinned, not printed: this is the first real evidence bearing on Task 3's
    // `ASSUMED_MOVES_PER_REUSABLE_PROJECTION = 1`, and Task 8 has to revisit that
    // bound. A regression here means the assumption needs re-deriving, not
    // relaxing quietly.
    assert_eq!(
        corpus_max_moves, 0,
        "the offline two-pass no longer seats the whole corpus move-free"
    );
    assert!(with_moves.is_empty(), "no production coordinate should need a move");
}

/// The realized move count against Task 3's
/// `ASSUMED_MOVES_PER_REUSABLE_PROJECTION = 1` program-size assumption.
#[test]
fn corpus_moves_stay_within_the_assumed_bound() {
    let coordinates = corpus_coordinates();
    let rows: Vec<(String, usize, usize)> = coordinates
        .par_iter()
        .map(|(name, li, regime, layer, prices)| {
            let tag = format!(
                "{name} L{li} {}",
                if *regime == BwdRegime::R0 { "R0" } else { "Ext" }
            );
            let distilled_reusable = {
                // The census's own `reusable_projections`, recomputed from the same
                // lowering so the comparison is against Task 3's exact quantity.
                let mut counts: BTreeMap<ProjectionId, usize> = BTreeMap::new();
                for term in &layer.terms {
                    let mut here: BTreeSet<ProjectionId> = BTreeSet::new();
                    term.for_each_projection_use(|p| {
                        here.insert(p);
                    });
                    for p in here {
                        *counts.entry(p).or_insert(0) += 1;
                    }
                }
                counts.values().filter(|n| **n > 1).count()
            };
            let order = stable_normalized_order(layer);
            let mut max_moves = 0usize;
            for budget in CellBudget::ALL {
                let req = PagingRequest { budget, target_depth: default_target_depth(*regime) };
                let plan = page_projections(layer, prices, req, &order).expect("pager");
                let placement = place_paging_plan(layer, prices, &plan).expect("placement");
                max_moves = max_moves.max(placement.stats.bf_moves + placement.stats.e4_moves);
            }
            (tag, max_moves, distilled_reusable)
        })
        .collect();

    let mut over: Vec<&(String, usize, usize)> =
        rows.iter().filter(|(_, moves, reusable)| *moves > *reusable).collect();
    over.sort();
    println!("coordinates exceeding one move per reusable projection: {}", over.len());
    for (tag, moves, reusable) in &over {
        println!("  OVER {tag} moves={moves} reusable_projections={reusable}");
    }
    let worst = rows.iter().max_by_key(|(_, moves, _)| *moves).expect("non-empty");
    println!(
        "worst coordinate: {} realized_max_moves={} reusable_projections={}",
        worst.0, worst.1, worst.2
    );
    assert!(
        over.is_empty(),
        "Task 3's ASSUMED_MOVES_PER_REUSABLE_PROJECTION = 1 upper bound is violated"
    );
}

/// The census is unchanged by Task 5's typed-error conversion of
/// `live_term_categories`.
#[test]
fn census_still_totals_on_the_whole_corpus() {
    for name in FIXTURES {
        for (li, canonical, cross) in layers_with_bwd_roots(name) {
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                let distilled = distill(&canonical, regime, &cross, None);
                let (lowered, trace) = lower_coeff_layer_traced(&canonical, &distilled)
                    .unwrap_or_else(|e| panic!("[{name} L{li}] lowering: {e:?}"));
                census_coeff_layer(&canonical, &distilled, &lowered, &trace)
                    .unwrap_or_else(|e| panic!("[{name} L{li}] census: {e:?}"));
                gkr_eval_isa::bwd::coeff::live_term_categories(&lowered)
                    .unwrap_or_else(|e| panic!("[{name} L{li}] categories: {e:?}"));
            }
        }
    }
}

/// Bounded deterministic fuzz over random small layers at tight budgets.
///
/// This is the guard the pathological fixture came out of, and it is what caught
/// the two real defects in this task: a repair that relocated a value an EARLIER
/// operand slot of the same term had just filled (a move executes before its
/// term, so that value does not exist yet), and a certificate that cleared only
/// the overlapping lanes of a displaced E4 and left three phantom owners behind.
/// Both were found here, not by inspection, so the fuzz stays.
#[test]
fn randomized_placements_always_certify() {
    let mut state: u64 = 0x0123_4567_89ab_cdef;
    let mut next = |bound: u64| -> u64 {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (state >> 33) % bound.max(1)
    };
    let mut repaired = 0usize;
    let mut unplaceable = 0usize;
    let mut checked = 0usize;
    // Biased toward the shape that actually fragments: mostly-BF R0 layers with a
    // couple of E4 sources at tight budgets.
    //
    // The size of the layer is the lever, and it was measured rather than guessed.
    // A sweep over generator shapes at a fixed 24,000 placements gave, per shape,
    // the number that reach the repair path:
    //
    //     4..9 sources,  6..13 terms   ->    19
    //     6..13 sources, 12..25 terms  -> 1,085
    //     8..15 sources, 16..31 terms  -> 2,642
    //
    // Confining sources to a sliding window of terms — the intuitive "short-lived
    // BF occupant" bias — HALVES the yield at every size (1,085 -> 459), because a
    // relocation needs the cell file near capacity as well as fragmented, and short
    // residencies relieve exactly the pressure that fills it. Sustained occupancy
    // is what matters, so the generator stays uniform and the layers got bigger.
    for round in 0..6_000u64 {
        let regime = if round % 4 == 3 { BwdRegime::Ext } else { BwdRegime::R0 };
        let n_src = 6 + next(7) as usize;
        let fields: Vec<FieldKind> = (0..n_src)
            .map(|_| {
                if regime == BwdRegime::Ext || next(4) == 0 {
                    FieldKind::Ext
                } else {
                    FieldKind::Base
                }
            })
            .collect();
        let n_terms = 12 + next(13) as usize;
        let mut terms = Vec::with_capacity(n_terms);
        for i in 0..n_terms {
            let id = i as u32;
            let a = next(n_src as u64) as u32;
            let b = next(n_src as u64) as u32;
            let (fa, fb) = (fields[a as usize], fields[b as usize]);
            let pick = next(3);
            terms.push(if pick == 0 {
                c0(id, a, fa)
            } else if pick == 1 || regime == BwdRegime::R0 {
                c2(id, a, fa, b, fb)
            } else if fa == FieldKind::Ext && fb == FieldKind::Ext {
                dual(id, a, b)
            } else {
                c0(id, a, fa)
            });
        }
        let layer = synthetic(regime, &fields, terms);
        let prices: Vec<SourcePrice> = fields.iter().copied().map(price_of).collect();
        let order = stable_normalized_order(&layer);
        // c2/c3 alone was the sample that MISSED the placer/certificate
        // move-destination disagreement: at the tightest budgets few lanes are
        // live, so a relocation rarely lands where a later slot of the same term
        // fills. c4 and c6 give that interaction room to surface.
        for cells in [2u8, 3, 4, 6] {
            let req = PagingRequest { budget: CellBudget::new(cells).unwrap(), target_depth: 0 };
            let Ok(plan) = page_projections(&layer, &prices, req, &order) else { continue };
            let before = plan.canonical_bytes();
            match place_paging_plan(&layer, &prices, &plan) {
                Ok(placement) => {
                    assert_eq!(plan.canonical_bytes(), before, "placement mutated the plan");
                    certify_cell_liveness(&layer, &prices, &plan, &placement).unwrap_or_else(|e| {
                        panic!(
                            "c{cells} {regime:?} liveness: {e:?}\nfields {fields:?}\n{:?}",
                            layer.terms
                        )
                    });
                    if placement.stats.repaired {
                        repaired += 1;
                    }
                }
                // The brief's only sanctioned failure: the offline packing did not
                // fit and no legal relocation exists at this step. A move is a
                // standalone instruction emitted BEFORE its term, so it may not
                // relocate a value that term reads or produced, nor write a lane
                // that term reads or fills — and at the tightest budgets those
                // constraints can leave a fragmented cell file with no legal
                // repair. It never happens on the production corpus (zero moves at
                // every budget), so it is reported, not papered over.
                Err(PlacementError::BudgetBelowFloor {
                    reason: PlacementFloor::NoLegalRelocation { .. },
                    ..
                }) => unplaceable += 1,
                Err(e) => panic!(
                    "c{cells} {regime:?} unexpected placement error {e:?}\nfields {fields:?}\n{:?}",
                    layer.terms
                ),
            }
            checked += 1;
        }
    }
    println!(
        "randomized placements checked={checked} repaired={repaired} \
         no_legal_relocation={unplaceable}"
    );
    assert!(checked > 20_000, "vacuous: only {checked} instances reached placement");
    // Non-vacuity with real headroom: the repair path is reached hundreds of times
    // per run, not once. A shape change that quietly stops fragmenting fails here
    // instead of leaving the fuzz green and blind.
    assert!(repaired > 100, "the repair path was reached only {repaired} times");
}
