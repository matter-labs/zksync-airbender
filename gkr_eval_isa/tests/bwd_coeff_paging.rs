//! Task 4 gates: deterministic mixed-width projection paging (design §7.1, §8,
//! §12.2, §12.4).
//!
//! The pager's BEHAVIOUR is gated on hand-built synthetic layers, because a
//! synthetic layer is the only way to put a chosen projection at a chosen
//! next-use distance with a chosen rebuild price and read the eviction ranking
//! back unambiguously. The production corpus then gates TERMINATION and
//! CAPACITY COMPLIANCE at every budget c2..c16 (`corpus_*` below), so no claim
//! rests on synthetic data alone.
//!
//! Nothing here touches physical cells, lanes, quad alignment, moves, source
//! windows, or the u16 encoding — those are Tasks 5-7. Every assertion is about
//! the LOGICAL residency plan over `ProjectionId`s and its certificate.

mod common;

use std::collections::BTreeSet;

use common::{FIXTURES, layers_with_bwd_roots};
use cs::gkr_compiler::dag_ir::{BwdRegime, FieldKind, ReadPlace};
use gkr_eval_isa::bwd::coeff::schedule::{
    CellBudget, OpCounts, PagingAction, PagingCertificateError, PagingPlan, PagingRequest,
    ProjectionAction, ProjectionOutcome, ResolutionGroup, SeedKind, SourcePrice, ValueWidth,
    budget_aware_greedy_order, certify_paging_plan, default_target_depth, page_projections,
    select_paged_order, source_prices, stable_normalized_order, sweep_budgets,
};
use gkr_eval_isa::bwd::coeff::schedule::ScheduleError;
use gkr_eval_isa::bwd::coeff::{
    CoeffLayer, CoeffSource, CoeffTerm, CoefficientRecipeId, ProjectionId, SourceId, TermId,
    lower_coeff_layer,
};
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::bwd::source::OriginLeaf;
use rayon::prelude::*;

// ── Synthetic layer construction ─────────────────────────────────────────────

fn read_source(column: usize, field: FieldKind) -> CoeffSource {
    CoeffSource { origin: OriginLeaf::Read(ReadPlace::BaseLayerMemory { column }), field }
}

/// A layer over `fields.len()` read sources, one column each, with `terms` dense
/// and already in `TermId` order.
fn layer(regime: BwdRegime, fields: &[FieldKind], terms: Vec<CoeffTerm>) -> CoeffLayer {
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

// ── Synthetic prices ─────────────────────────────────────────────────────────

/// An ordinary base column: one lane, 4 B per endpoint, no fold arithmetic.
fn bf_read() -> SourcePrice {
    SourcePrice { width: ValueWidth::Bf, element_bytes: 4, endpoint_ops: OpCounts::ZERO }
}

/// An ordinary Ext-valued backing: four lanes, 16 B per endpoint.
fn e4_read() -> SourcePrice {
    SourcePrice { width: ValueWidth::E4, element_bytes: 16, endpoint_ops: OpCounts::ZERO }
}

/// A one-lane value that is EXPENSIVE to reload (a deep lazy fold of a base
/// column: `4 * 2^depth` bytes per endpoint at depth 1).
fn bf_read_costly() -> SourcePrice {
    SourcePrice { width: ValueWidth::Bf, element_bytes: 8, endpoint_ops: OpCounts::ZERO }
}

/// A one-lane PROCEDURAL value — the physically cheapest source there is: a
/// `VirtualSetup` origin moves zero DRAM (`bwd::cost`'s VS short-circuit) and
/// pays only closed-form arithmetic.
fn bf_procedural() -> SourcePrice {
    SourcePrice {
        width: ValueWidth::Bf,
        element_bytes: 0,
        endpoint_ops: OpCounts { bf: 1, mixed: 0, e4: 0 },
    }
}

fn budget(cells: u8) -> CellBudget {
    CellBudget::new(cells).expect("c2..c16")
}

fn r0(budget_cells: u8) -> PagingRequest {
    PagingRequest { budget: budget(budget_cells), target_depth: default_target_depth(BwdRegime::R0) }
}

fn ext(budget_cells: u8) -> PagingRequest {
    PagingRequest {
        budget: budget(budget_cells),
        target_depth: default_target_depth(BwdRegime::Ext),
    }
}

// ── Plan helpers ─────────────────────────────────────────────────────────────

/// Page the stable normalized order and certify it, panicking with context.
fn page_stable(lowered: &CoeffLayer, prices: &[SourcePrice], request: PagingRequest) -> PagingPlan {
    let order = stable_normalized_order(lowered);
    let plan = page_projections(lowered, prices, request, &order).expect("pager");
    certify_paging_plan(lowered, prices, &plan).expect("certificate accepts the pager's own plan");
    plan
}

/// The action serving term `term`'s operand slot `slot`.
fn action<'a>(plan: &'a PagingPlan, term: u32, slot: u8) -> &'a PagingAction {
    plan.actions
        .iter()
        .find(|a| a.term == TermId(term) && a.slot == slot)
        .unwrap_or_else(|| panic!("no action for term {term} slot {slot}"))
}

fn outcome_of(a: &PagingAction, projection: ProjectionId) -> ProjectionOutcome {
    a.projections
        .iter()
        .find(|p| p.projection == projection)
        .unwrap_or_else(|| panic!("action {} does not touch {projection:?}", a.step))
        .outcome
}

fn delta(source: u32) -> ProjectionId {
    ProjectionId::delta(SourceId(source))
}

fn endpoint0(source: u32) -> ProjectionId {
    ProjectionId::endpoint0(SourceId(source))
}

// ── 1. Mixed-width residency ─────────────────────────────────────────────────

#[test]
fn bf_values_fill_the_remainder_of_an_e4_budget() {
    // One E4 delta (4 lanes) plus four BF deltas (1 lane each) exactly saturate
    // the 8 BF-lane-equivalents of a c2 budget. A pager that reserved whole
    // cells for BF values, or that refused to mix widths, could not reach 8.
    let fields =
        [FieldKind::Ext, FieldKind::Base, FieldKind::Base, FieldKind::Base, FieldKind::Base];
    let e = FieldKind::Ext;
    let b = FieldKind::Base;
    let l = layer(
        BwdRegime::R0,
        &fields,
        vec![
            c2(0, 0, e, 1, b),
            c2(1, 2, b, 3, b),
            c2(2, 4, b, 1, b),
            c2(3, 0, e, 2, b),
            c2(4, 3, b, 4, b),
        ],
    );
    let prices = [e4_read(), bf_read(), bf_read(), bf_read(), bf_read()];

    let plan = page_stable(&l, &prices, r0(2));

    assert_eq!(plan.cost.evictions, 0, "the peak set fits c2 exactly, so nothing is evicted");
    assert_eq!(plan.cost.bypasses, 0, "every miss with a later use is admitted");
    assert_eq!(plan.cost.peak_resident_lanes, 8, "1 E4 (4 lanes) + 4 BF (1 lane each)");

    let peak = plan
        .actions
        .iter()
        .find(|a| a.resident_lanes_after == 8)
        .expect("a step reaches the full c2 budget");
    let resident: BTreeSet<_> = peak.resident_after.iter().copied().collect();
    assert!(resident.contains(&delta(0)), "the E4 delta is resident at the peak");
    for bf in 1..=4 {
        assert!(resident.contains(&delta(bf)), "BF delta {bf} fills the remainder");
    }
    assert_eq!(resident.len(), 5);
}

// ── 2/3. Eviction ranking ────────────────────────────────────────────────────

/// Eight one-lane residents saturating c2, each with a distinct next use, then a
/// wide or narrow miss that forces eviction. `costly` names the sources priced
/// above the rest.
fn eight_resident_bf_layer(
    ninth: FieldKind,
    ninth_price: SourcePrice,
    costly: &[u32],
    procedural: &[u32],
) -> (CoeffLayer, Vec<SourcePrice>) {
    let b = FieldKind::Base;
    // Sources 0..8 are the eight BF residents; source 8 is the ninth value.
    let mut fields = vec![b; 8];
    fields.push(ninth);
    let terms = vec![
        c2(0, 0, b, 1, b),
        c2(1, 2, b, 3, b),
        c2(2, 4, b, 5, b),
        c2(3, 6, b, 7, b),
        // Position 4: the miss that forces eviction. `lhs == rhs` so it is a
        // single deduplicated resolution group.
        c2(4, 8, ninth, 8, ninth),
        // Next uses: source 0 at 5, {1,2} at 6, {3,4} at 7, {5,6} at 8, 7 at 9.
        c2(5, 0, b, 8, ninth),
        c2(6, 1, b, 2, b),
        c2(7, 3, b, 4, b),
        c2(8, 5, b, 6, b),
        c2(9, 7, b, 7, b),
    ];
    let mut prices = vec![bf_read(); 8];
    prices.push(ninth_price);
    for &c in costly {
        prices[c as usize] = bf_read_costly();
    }
    for &p in procedural {
        prices[p as usize] = bf_procedural();
    }
    (layer(BwdRegime::R0, &fields, terms), prices)
}

#[test]
fn e4_miss_evicts_farthest_cheapest_set() {
    // Source 5 is priced ABOVE source 6, and both have their next use at term 8,
    // so the cheapest-rebuild key orders 6 before 5 inside that next-use tie.
    let (l, prices) = eight_resident_bf_layer(FieldKind::Ext, e4_read(), &[5], &[]);

    let plan = page_stable(&l, &prices, r0(2));
    let miss = action(&plan, 4, 0);

    assert_eq!(
        outcome_of(miss, delta(8)),
        ProjectionOutcome::Fill,
        "the E4 delta has a later use and is the nearest candidate, so it is admitted"
    );
    // Farthest next use first (7 at term 9), then the term-8 pair ordered
    // cheapest-rebuild-first (6 before the costlier 5), then the term-7 pair
    // ordered by stable ProjectionId (3 before 4). Exactly four lanes freed.
    assert_eq!(
        miss.evicted,
        vec![delta(7), delta(6), delta(5), delta(3)],
        "farthest next use, then cheapest rebuild price, then stable ProjectionId"
    );
    assert_eq!(miss.resident_lanes_after, 8, "4 surviving BF lanes + the 4-lane E4 fill");
}

#[test]
fn expensive_near_reuse_beats_cheap_far_reuse() {
    // Source 7 is PROCEDURAL: zero DRAM, the cheapest possible rebuild. Source 0
    // is an ordinary read and therefore strictly more expensive to rebuild. But
    // source 7's next use is term 9 and source 0's is term 5, and farthest next
    // use is the PRIMARY key — so the cheap far value is the one that goes.
    let (l, prices) = eight_resident_bf_layer(FieldKind::Base, bf_read(), &[], &[7]);

    let plan = page_stable(&l, &prices, r0(2));
    let miss = action(&plan, 4, 0);

    assert_eq!(
        miss.evicted,
        vec![delta(7)],
        "a cost-first ranking would have kept the free-to-rebuild value and evicted a read"
    );
    assert!(
        miss.resident_after.contains(&delta(0)),
        "the expensive value with the nearest reuse is retained"
    );
    assert_eq!(outcome_of(miss, delta(8)), ProjectionOutcome::Fill);
}

// ── 4. Bypass ────────────────────────────────────────────────────────────────

#[test]
fn miss_can_bypass_without_disturbing_residents() {
    // Source 8's next use (term 9) is farther than every resident's, so the
    // newly produced value is itself the top eviction candidate — step 7 turns
    // that into a bypass instead of a fill-then-evict.
    let b = FieldKind::Base;
    let mut fields = vec![b; 8];
    fields.push(b);
    let terms = vec![
        c2(0, 0, b, 1, b),
        c2(1, 2, b, 3, b),
        c2(2, 4, b, 5, b),
        c2(3, 6, b, 7, b),
        c2(4, 8, b, 8, b),
        c2(5, 0, b, 1, b),
        c2(6, 2, b, 3, b),
        c2(7, 4, b, 5, b),
        c2(8, 6, b, 7, b),
        c2(9, 8, b, 8, b),
    ];
    let l = layer(BwdRegime::R0, &fields, terms);
    let prices = vec![bf_read(); 9];

    let plan = page_stable(&l, &prices, r0(2));
    let miss = action(&plan, 4, 0);

    assert_eq!(outcome_of(miss, delta(8)), ProjectionOutcome::Bypass);
    assert!(miss.evicted.is_empty(), "a bypass disturbs nothing");
    assert_eq!(miss.resident_lanes_after, 8);
    let resident: BTreeSet<_> = miss.resident_after.iter().copied().collect();
    assert_eq!(
        resident,
        (0..8).map(delta).collect::<BTreeSet<_>>(),
        "every prior resident survives the bypass"
    );
    assert!(miss.source_read_bytes > 0, "a bypass still pays the source read");
}

// ── 5. Independent paired admission ──────────────────────────────────────────

#[test]
fn delta_pair_can_retain_only_endpoint0_or_only_delta() {
    let e = FieldKind::Ext;
    // Two E4 sources: 0 is the filler, 1 is the paired source. c2 = 8 lanes, so
    // the filler plus ONE of the pair fits and the other must go.
    let fields = [FieldKind::Ext, FieldKind::Ext];
    let prices = [e4_read(), e4_read()];

    // Case A — Endpoint0's next use (term 2) is nearer than Delta's (term 4), so
    // the pair retains only Endpoint0.
    let only_endpoint0 = layer(
        BwdRegime::R0,
        &fields,
        vec![
            c2(0, 0, e, 0, e),
            c2(1, 1, e, 1, e),
            c0(2, 1, e),
            c2(3, 0, e, 0, e),
            c2(4, 1, e, 1, e),
        ],
    );
    let plan = page_stable(&only_endpoint0, &prices, r0(2));
    let paired = action(&plan, 1, 0);
    assert_eq!(
        paired.group,
        ResolutionGroup::Pair {
            source: SourceId(1),
            endpoint0: endpoint0(1),
            delta: delta(1)
        },
        "a Delta miss whose Endpoint0 has a later use resolves the pair once"
    );
    assert_eq!(outcome_of(paired, endpoint0(1)), ProjectionOutcome::Fill);
    assert_eq!(outcome_of(paired, delta(1)), ProjectionOutcome::Bypass);

    // Case B — Delta's next use (term 3) is nearer than Endpoint0's (term 4), so
    // the SAME pair form retains only Delta. Same source, same price, same
    // budget: only the next-use distances differ.
    let only_delta = layer(
        BwdRegime::R0,
        &fields,
        vec![
            c2(0, 0, e, 0, e),
            c2(1, 1, e, 1, e),
            c2(2, 0, e, 0, e),
            c2(3, 1, e, 1, e),
            c0(4, 1, e),
        ],
    );
    let plan = page_stable(&only_delta, &prices, r0(2));
    let paired = action(&plan, 1, 0);
    assert_eq!(
        paired.group,
        ResolutionGroup::Pair {
            source: SourceId(1),
            endpoint0: endpoint0(1),
            delta: delta(1)
        }
    );
    assert_eq!(outcome_of(paired, endpoint0(1)), ProjectionOutcome::Bypass);
    assert_eq!(outcome_of(paired, delta(1)), ProjectionOutcome::Fill);
}

// ── 6. Native dual factors ───────────────────────────────────────────────────

#[test]
fn dual_product_resolves_each_factor_once() {
    let fields = [FieldKind::Ext, FieldKind::Ext];
    let prices = [e4_read(), e4_read()];

    // Distinct factors: exactly two paired resolutions, one per factor, each
    // reading TWO endpoints (not four projection reads).
    let distinct = layer(BwdRegime::Ext, &fields, vec![dual(0, 0, 1)]);
    let plan = page_stable(&distinct, &prices, ext(16));
    assert_eq!(plan.actions.len(), 2, "one resolution group per distinct factor");
    for (slot, source) in [(0u8, 0u32), (1, 1)] {
        let a = action(&plan, 0, slot);
        assert_eq!(
            a.group,
            ResolutionGroup::Pair {
                source: SourceId(source),
                endpoint0: endpoint0(source),
                delta: delta(source)
            }
        );
        assert_eq!(
            a.source_read_bytes, 32,
            "one source-PAIR resolution = two 16 B endpoints, not four reads"
        );
        assert_eq!(a.e4_ops, 1, "one E4 subtraction forms the delta");
    }
    assert_eq!(plan.cost.source_resolutions, 2);
    assert_eq!(plan.cost.source_read_bytes, 64);

    // Repeated factor: ONE resolution serves both operand slots.
    let repeated = layer(BwdRegime::Ext, &fields, vec![dual(0, 0, 0)]);
    let plan = page_stable(&repeated, &prices, ext(16));
    assert_eq!(plan.actions.len(), 1, "a repeated factor is one deduplicated resolution");
    assert_eq!(plan.cost.source_read_bytes, 32);
    assert_eq!(plan.cost.source_resolutions, 1);
}

// ── 7. Ported budget-aware greedy constructor ────────────────────────────────

#[test]
fn budget_aware_greedy_appends_terms_individually_and_keeps_expensive_reuse_contiguous() {
    // Terms 0 and 2 share the EXPENSIVE E4 delta of source 0; terms 0 and 1
    // share the CHEAP BF delta of source 1. Sources 2 and 3 are used once, so
    // they are not reuse values at all.
    let e = FieldKind::Ext;
    let b = FieldKind::Base;
    let fields = [FieldKind::Ext, FieldKind::Base, FieldKind::Base, FieldKind::Base];
    let l = layer(
        BwdRegime::R0,
        &fields,
        vec![c2(0, 0, e, 1, b), c2(1, 1, b, 2, b), c2(2, 0, e, 3, b)],
    );
    let prices = [e4_read(), bf_read(), bf_read(), bf_read()];

    let order = budget_aware_greedy_order(&l, &prices, budget(16)).expect("greedy order");

    // Terms {0,1,2} are one connected reuse component, so all three stay
    // contiguous. Inside it the frontier proxy appends ONE term at a time: term
    // 1 first (it opens only the cheap value), then term 0 (which closes the
    // cheap value and opens the expensive one), then term 2.
    assert_eq!(order, vec![TermId(1), TermId(0), TermId(2)]);
    assert_ne!(
        order,
        stable_normalized_order(&l),
        "the constructor is not a relabelled stable order"
    );

    let expensive: Vec<usize> = order
        .iter()
        .enumerate()
        .filter(|(_, t)| **t == TermId(0) || **t == TermId(2))
        .map(|(i, _)| i)
        .collect();
    assert_eq!(
        expensive,
        vec![1, 2],
        "the two terms sharing the expensive projection end up adjacent"
    );
}

// ── 8. Bounded seed selection ────────────────────────────────────────────────

/// Six shared E4 deltas (24 lanes of frontier) over nine terms — wide enough
/// that c2 and c16 make genuinely different greedy choices.
fn wide_reuse_layer() -> (CoeffLayer, Vec<SourcePrice>) {
    let e = FieldKind::Ext;
    let fields = [e; 6];
    let l = layer(
        BwdRegime::R0,
        &fields,
        vec![
            c2(0, 0, e, 1, e),
            c2(1, 2, e, 3, e),
            c2(2, 4, e, 5, e),
            c2(3, 0, e, 2, e),
            c2(4, 1, e, 3, e),
            c2(5, 4, e, 0, e),
            c2(6, 5, e, 1, e),
            c2(7, 2, e, 4, e),
            c2(8, 3, e, 5, e),
        ],
    );
    (l, vec![e4_read(); 6])
}

#[test]
fn seed_selector_checks_canonical_greedy_and_distinct_preceding_only() {
    let (l, prices) = wide_reuse_layer();
    let sweep = sweep_budgets(&l, &prices, default_target_depth(BwdRegime::R0)).expect("sweep");

    assert_eq!(sweep.outcomes.len(), CellBudget::ALL.len(), "c2..c16 inclusive");
    let stable = stable_normalized_order(&l);

    let mut saw_preceding = false;
    for (i, outcome) in sweep.outcomes.iter().enumerate() {
        assert_eq!(outcome.request.budget, CellBudget::ALL[i]);
        assert!(outcome.candidates.len() <= 3, "bounded seed selection: at most three orders");

        // No seed kind outside the three declared ones can appear, and they
        // appear in the declared listing order.
        let kinds: Vec<SeedKind> = outcome.candidates.iter().map(|c| c.seed).collect();
        let mut sorted = kinds.clone();
        sorted.sort_by_key(|k| match k {
            SeedKind::StableNormalized => 0,
            SeedKind::BudgetAwareGreedy => 1,
            SeedKind::PrecedingWinner => 2,
        });
        assert_eq!(kinds, sorted, "seeds are listed in the declared order");
        assert_eq!(
            kinds.iter().collect::<BTreeSet<_>>().len(),
            kinds.len(),
            "no seed kind is evaluated twice"
        );

        // Every evaluated order is distinct — an identical order is never paged
        // twice.
        let orders: BTreeSet<&Vec<TermId>> = outcome.candidates.iter().map(|c| &c.order).collect();
        assert_eq!(orders.len(), outcome.candidates.len(), "no duplicate order is evaluated");

        assert_eq!(
            outcome.candidates[0].seed,
            SeedKind::StableNormalized,
            "the stable normalized order is always a candidate"
        );
        assert_eq!(outcome.candidates[0].order, stable);

        let greedy = budget_aware_greedy_order(&l, &prices, outcome.request.budget).unwrap();
        let has_preceding = kinds.contains(&SeedKind::PrecedingWinner);
        if i == 0 {
            assert!(!has_preceding, "the first budget has no preceding winner");
        } else {
            let preceding = &sweep.outcomes[i - 1].plan.order;
            let distinct = *preceding != stable && *preceding != greedy;
            assert_eq!(
                has_preceding, distinct,
                "budget {} carries the preceding winner exactly when it is distinct",
                outcome.request.budget.label()
            );
            saw_preceding |= has_preceding;
            let _ = saw_preceding;
        }

        // The winner is the EXACT best (score, order) over the candidates.
        let best = outcome
            .candidates
            .iter()
            .min_by(|a, b| (a.score, &a.order).cmp(&(b.score, &b.order)))
            .unwrap();
        assert_eq!(outcome.plan.order, best.order, "the exact best score wins");
        assert_eq!(outcome.winner, best.seed);
        certify_paging_plan(&l, &prices, &outcome.plan).expect("every winning plan certifies");
    }
    // The sweep above proves the biconditional over the real budget ladder, but
    // on this layer the greedy order happens to be budget-invariant, so the
    // INCLUSION branch never fires there. Drive it directly instead — the
    // contract is about `select_paged_order`'s candidate set, so testing it at
    // that seam is both deterministic and complete.
    let request = PagingRequest {
        budget: budget(4),
        target_depth: default_target_depth(BwdRegime::R0),
    };
    let greedy = budget_aware_greedy_order(&l, &prices, request.budget).unwrap();
    let mut distinct = stable.clone();
    distinct.reverse();
    assert_ne!(distinct, stable);
    assert_ne!(distinct, greedy);

    let kinds = |preceding: Option<&[TermId]>| -> Vec<SeedKind> {
        select_paged_order(&l, &prices, request, preceding)
            .expect("seed selection")
            .candidates
            .iter()
            .map(|c| c.seed)
            .collect()
    };
    assert_eq!(
        kinds(Some(&distinct)),
        vec![SeedKind::StableNormalized, SeedKind::BudgetAwareGreedy, SeedKind::PrecedingWinner],
        "a preceding winner distinct from both is evaluated"
    );
    assert_eq!(
        kinds(Some(&stable)),
        vec![SeedKind::StableNormalized, SeedKind::BudgetAwareGreedy],
        "a preceding winner equal to the stable order is not re-evaluated"
    );
    assert_eq!(
        kinds(Some(&greedy)),
        vec![SeedKind::StableNormalized, SeedKind::BudgetAwareGreedy],
        "a preceding winner equal to this budget's greedy order is not re-evaluated"
    );
    assert_eq!(
        kinds(None),
        vec![SeedKind::StableNormalized, SeedKind::BudgetAwareGreedy],
        "no preceding winner, no third candidate"
    );
}

// ── 9. Determinism ───────────────────────────────────────────────────────────

#[test]
fn paging_is_deterministic_under_equal_scores() {
    // Sources 3 and 4 are byte-identical in width, price and next use (both are
    // consumed by term 9, the farthest next use of all), so ONLY the stable
    // `ProjectionId` order separates them. Sources 0..7 saturate c2's eight
    // lanes, then the term-4 miss needs one more.
    let b = FieldKind::Base;
    let fields = [b; 9];
    let l = layer(
        BwdRegime::R0,
        &fields,
        vec![
            c2(0, 0, b, 1, b),
            c2(1, 2, b, 3, b),
            c2(2, 4, b, 5, b),
            c2(3, 6, b, 7, b),
            c2(4, 8, b, 8, b),
            c2(5, 8, b, 0, b),
            c2(6, 1, b, 2, b),
            c2(7, 5, b, 6, b),
            c2(8, 7, b, 7, b),
            // Sources 3 and 4 tie here on next use, price and width.
            c2(9, 3, b, 4, b),
        ],
    );
    let prices = vec![bf_read(); 9];

    let first = page_stable(&l, &prices, r0(2));
    let second = page_stable(&l, &prices, r0(2));
    assert_eq!(
        first.canonical_bytes(),
        second.canonical_bytes(),
        "repeated paging emits identical action bytes"
    );

    // Sources 3 and 4 tie on next use (term 5), price and width, so the lower
    // stable ProjectionId is the victim.
    let miss = action(&first, 4, 0);
    assert_eq!(miss.evicted, vec![delta(3)], "an exact tie is broken by stable ProjectionId");

    // The whole sweep is deterministic too, seeds included.
    let (wide, wide_prices) = wide_reuse_layer();
    let depth = default_target_depth(BwdRegime::R0);
    let a = sweep_budgets(&wide, &wide_prices, depth).unwrap();
    let b_sweep = sweep_budgets(&wide, &wide_prices, depth).unwrap();
    let bytes = |s: &gkr_eval_isa::bwd::coeff::schedule::BudgetSweep| {
        s.outcomes.iter().flat_map(|o| o.plan.canonical_bytes()).collect::<Vec<u8>>()
    };
    assert_eq!(bytes(&a), bytes(&b_sweep), "the whole c2..c16 sweep is byte-reproducible");
}

// ── 10. Certificate independence ─────────────────────────────────────────────

#[test]
fn paging_certificate_rejects_mutated_action() {
    let (l, prices) = eight_resident_bf_layer(FieldKind::Ext, e4_read(), &[5], &[]);
    let good = page_stable(&l, &prices, r0(2));
    let step = good.actions.iter().position(|a| !a.evicted.is_empty()).expect("an eviction step");

    // Each mutation asserts the EXACT rejecting variant. A bare `is_err()` would
    // let a mutation pass for the wrong reason and leave the branch it was meant
    // to exercise untested.
    let rejects = |m: &PagingPlan| certify_paging_plan(&l, &prices, m).unwrap_err();

    // (a) A flipped hit/miss state.
    let mut m = good.clone();
    let hit = m
        .actions
        .iter_mut()
        .flat_map(|a| a.projections.iter_mut())
        .find(|p| p.outcome == ProjectionOutcome::Hit)
        .expect("a hit");
    hit.outcome = ProjectionOutcome::Fill;
    assert!(
        matches!(rejects(&m), PagingCertificateError::OutcomeMismatch { .. }),
        "a flipped hit/miss must be rejected as an outcome mismatch"
    );

    // (b) A tampered cost.
    let mut m = good.clone();
    m.actions[step].source_read_bytes += 4;
    assert!(
        matches!(
            rejects(&m),
            PagingCertificateError::StepCostMismatch { field: "source_read_bytes", .. }
        ),
        "a tampered read cost must be rejected as a step cost mismatch"
    );

    // (c) A tampered resident set.
    let mut m = good.clone();
    m.actions[step].resident_after.pop();
    assert!(
        matches!(rejects(&m), PagingCertificateError::ResidentSetMismatch { .. }),
        "a resident set that disagrees with the declared decisions must be rejected"
    );

    // (d) A dropped eviction — the width then exceeds the budget.
    let mut m = good.clone();
    m.actions[step].evicted.clear();
    assert!(
        matches!(rejects(&m), PagingCertificateError::CapacityExceeded { .. }),
        "dropping an eviction must be rejected as a capacity overrun"
    );

    // (f) A tampered total cost.
    let mut m = good.clone();
    m.cost.source_read_bytes += 1;
    assert!(
        matches!(
            rejects(&m),
            PagingCertificateError::TotalCostMismatch { field: "source_read_bytes", .. }
        ),
        "a tampered total must be rejected"
    );

    // (e) An illegal paired resolution. This needs a layer that HAS an
    // `Endpoint0`-only use: on a `C2Product` operand both `Single` and `Pair` are
    // legal forms (§8), so pairing one there is not the violation being tested —
    // it trips the projection-list check instead and leaves
    // `IllegalResolutionGroup` unexercised.
    let e = FieldKind::Ext;
    let c0_layer = layer(
        BwdRegime::R0,
        &[FieldKind::Ext],
        vec![c0(0, 0, e), c2(1, 0, e, 0, e), c0(2, 0, e)],
    );
    let c0_prices = [e4_read()];
    let c0_plan = page_stable(&c0_layer, &c0_prices, r0(2));

    let mut m = c0_plan.clone();
    let slot = m
        .actions
        .iter_mut()
        .find(|a| a.term == TermId(0))
        .expect("the C0Linear action");
    let victim = endpoint0(0);
    slot.group = ResolutionGroup::Pair { source: SourceId(0), endpoint0: victim, delta: delta(0) };
    slot.projections.push(ProjectionAction {
        projection: delta(0),
        consumed: false,
        outcome: ProjectionOutcome::Bypass,
    });
    assert!(
        matches!(
            certify_paging_plan(&c0_layer, &c0_prices, &m).unwrap_err(),
            PagingCertificateError::IllegalResolutionGroup { .. }
        ),
        "an Endpoint0-only use may never resolve s1, so pairing it is illegal (§8)"
    );

    // The untouched plans still certify, so the rejections above are about the
    // mutations and not about the certificate being vacuously strict.
    certify_paging_plan(&l, &prices, &good).expect("the unmutated plan certifies");
    certify_paging_plan(&c0_layer, &c0_prices, &c0_plan).expect("the unmutated C0 plan certifies");
}

/// A malformed term must be REJECTED, never silently dropped from the action
/// stream.
///
/// `expand` used to build its slots with `term_slots(..).into_iter().flatten()`,
/// which turns an `Err` into an EMPTY iterator — so a term with a bad operand
/// role or a field its source contradicts simply vanished, in the certificate as
/// well as the pager. Only the lowering's own discipline kept that latent.
#[test]
fn malformed_terms_are_rejected_not_silently_dropped() {
    let b = FieldKind::Base;
    let e = FieldKind::Ext;
    let prices = [bf_read(), bf_read()];

    // A `C0Linear` over a `Delta` — a role its opcode cannot consume.
    let bad_role = layer(
        BwdRegime::R0,
        &[b, b],
        vec![CoeffTerm::C0Linear {
            id: TermId(0),
            coefficient: CoefficientRecipeId::ONE,
            value: delta(0),
            field: b,
        }],
    );
    let order = stable_normalized_order(&bad_role);
    assert!(
        matches!(
            page_projections(&bad_role, &prices, r0(2), &order),
            Err(ScheduleError::ProjectionRoleMismatch { term: TermId(0), .. })
        ),
        "a C0Linear over a Delta must be rejected, not dropped"
    );
    assert!(
        budget_aware_greedy_order(&bad_role, &prices, budget(2)).is_err(),
        "the seed constructor must reject it too"
    );

    // A term whose declared operand field contradicts its source's field: the
    // opcode category and the resident width would disagree.
    let bad_field = layer(BwdRegime::R0, &[b, b], vec![c2(0, 0, e, 1, b)]);
    let order = stable_normalized_order(&bad_field);
    assert!(
        matches!(
            page_projections(&bad_field, &prices, r0(2), &order),
            Err(ScheduleError::OperandFieldConflict { term: TermId(0), .. })
        ),
        "a term field that contradicts its source must be rejected, not dropped"
    );

    // A term naming a source outside the table.
    let bad_source = layer(BwdRegime::R0, &[b], vec![c2(0, 0, b, 5, b)]);
    let order = stable_normalized_order(&bad_source);
    assert!(
        matches!(
            page_projections(&bad_source, &prices, r0(2), &order),
            Err(ScheduleError::UnknownSource { term: TermId(0), .. })
        ),
        "an out-of-range source must be rejected, not dropped"
    );
}

/// Width has two spellings, and this is the guard that stops them drifting.
///
/// `SourcePrice::width` and `CoeffSource::field` are one fact.
/// `source_prices` derives the former FROM the latter and so cannot disagree — but
/// every entry point is `pub` with every `SourcePrice` field `pub`, so a hand-built
/// price table is the exposed population, and a table claiming `Bf` for an `Ext`
/// source would make every downstream lane count four times too small: the
/// eviction ranking, the resident-lane accounting and the physical placement would
/// all size the projection differently from its opcode category.
///
/// `validate_prices` is called from every entry point that reads `prices[..].width`
/// — so all three checked here reject the SAME table with the SAME typed error
/// rather than one of them silently accepting it. Falsifying the guard is the point:
/// the correctly-priced table must still be accepted.
#[test]
fn a_price_table_that_contradicts_the_source_field_is_rejected_everywhere() {
    let e = FieldKind::Ext;
    // One `Ext` source, consumed by a `C2Product` that agrees with it.
    let lowered = layer(BwdRegime::R0, &[e, e], vec![c2(0, 0, e, 1, e)]);
    let order = stable_normalized_order(&lowered);

    let honest = [e4_read(), e4_read()];
    page_projections(&lowered, &honest, r0(4), &order).expect("an honest price table must page");
    budget_aware_greedy_order(&lowered, &honest, budget(4)).expect("...and must seed");
    let plan = page_stable(&lowered, &honest, r0(4));
    certify_paging_plan(&lowered, &honest, &plan).expect("...and must certify");

    // The same table with source 1 mis-priced as BF.
    let mut lying = honest;
    lying[1].width = ValueWidth::Bf;
    let expected = ScheduleError::PriceWidthMismatch {
        source: SourceId(1),
        price: ValueWidth::Bf,
        layer: FieldKind::Ext,
    };
    assert_eq!(
        page_projections(&lowered, &lying, r0(4), &order).expect_err("pager must reject"),
        expected
    );
    assert_eq!(
        budget_aware_greedy_order(&lowered, &lying, budget(4)).expect_err("seed must reject"),
        expected
    );
    // The certificate reads widths too, so it may not accept a plan priced by a
    // table it would itself reject — even a plan that is otherwise legal.
    assert_eq!(
        certify_paging_plan(&lowered, &lying, &plan).expect_err("certificate must reject"),
        PagingCertificateError::Structure(expected)
    );
}

// ── Production corpus: termination and capacity compliance ───────────────────

/// Every `(circuit, layer, regime)` coordinate, lowered and priced.
fn corpus_coordinates() -> Vec<(String, usize, BwdRegime, CoeffLayer, Vec<SourcePrice>)> {
    let mut out = Vec::new();
    for name in FIXTURES {
        for (li, canonical, cross) in layers_with_bwd_roots(name) {
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                let distilled = distill(&canonical, regime, &cross, None);
                let lowered = lower_coeff_layer(&canonical, &distilled)
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
fn corpus_paging_terminates_and_fits_every_budget() {
    let coordinates = corpus_coordinates();
    assert_eq!(coordinates.len(), 114, "57 backward-bearing layers x 2 regimes");

    let report: Vec<String> = coordinates
        .par_iter()
        .map(|(name, li, regime, lowered, prices)| {
            let tag = if *regime == BwdRegime::R0 { "R0" } else { "Ext" };
            let order = stable_normalized_order(lowered);
            let mut per_budget: Vec<(u8, u64, u64, u32)> = Vec::new();
            for budget in CellBudget::ALL {
                let request =
                    PagingRequest { budget, target_depth: default_target_depth(*regime) };
                let plan = page_projections(lowered, prices, request, &order)
                    .unwrap_or_else(|e| panic!("[{name} L{li} {tag} {}] {e:?}", budget.label()));
                assert!(
                    plan.cost.peak_resident_lanes <= budget.lanes(),
                    "[{name} L{li} {tag} {}] peak {} lanes exceeds capacity {}",
                    budget.label(),
                    plan.cost.peak_resident_lanes,
                    budget.lanes()
                );
                certify_paging_plan(lowered, prices, &plan).unwrap_or_else(|e| {
                    panic!("[{name} L{li} {tag} {}] certificate: {e:?}", budget.label())
                });
                per_budget.push((
                    budget.cells(),
                    plan.cost.source_read_bytes,
                    plan.cost.hits,
                    plan.cost.peak_resident_lanes,
                ));
            }
            // Read bytes are monotonically non-increasing in the budget: a wider
            // cell file can only turn misses into hits.
            for pair in per_budget.windows(2) {
                assert!(
                    pair[1].1 <= pair[0].1,
                    "[{name} L{li} {tag}] c{} spends more than c{}",
                    pair[1].0,
                    pair[0].0
                );
            }
            let (_, c2_bytes, c2_hits, _) = per_budget[0];
            let (_, c16_bytes, c16_hits, c16_lanes) = *per_budget.last().unwrap();
            let saved = if c2_bytes == 0 {
                0.0
            } else {
                100.0 * (c2_bytes - c16_bytes) as f64 / c2_bytes as f64
            };
            format!(
                "{saved:6.2}%  {name} L{li} {tag}: terms={} proj={} \
                 c2[bytes={c2_bytes} hits={c2_hits}] c16[bytes={c16_bytes} hits={c16_hits} \
                 peak_lanes={c16_lanes}]",
                lowered.terms.len(),
                lowered.sources.len() * 2,
            )
        })
        .collect();

    let mut report = report;
    report.sort();
    report.reverse();
    println!("== c2 -> c16 source-read reduction, stable order, per coordinate ==");
    for line in &report {
        println!("{line}");
    }
}

/// Seed selection and the ported greedy constructor, at production scale.
///
/// The other two corpus gates page the STABLE order only, which leaves
/// `select_paged_order` / `sweep_budgets` and the quadratic
/// `budget_aware_greedy_order` unmeasured on real layers. This runs the whole
/// bounded c2..c16 sweep — greedy constructor, seed selection, pager and
/// certificate — on the heaviest coordinates in the corpus.
///
/// Bounded and release-built: a fixed, deterministic coordinate set, three
/// candidate orders per budget, no search.
#[test]
fn corpus_seed_selection_runs_at_scale() {
    let coordinates = corpus_coordinates();

    // Select deterministically: every coordinate that SATURATES c16 (peak
    // residency pegged at 64 lanes, i.e. permanent eviction pressure) plus the
    // eight largest by term count. Saturation is read from a cheap stable-order
    // pass, so the selection itself costs nothing quadratic.
    let mut sized: Vec<(usize, bool, usize)> = coordinates
        .par_iter()
        .enumerate()
        .map(|(i, (_, _, regime, lowered, prices))| {
            let order = stable_normalized_order(lowered);
            let request = PagingRequest {
                budget: *CellBudget::ALL.last().unwrap(),
                target_depth: default_target_depth(*regime),
            };
            let plan = page_projections(lowered, prices, request, &order).expect("pager");
            (i, plan.cost.peak_resident_lanes == request.budget.lanes(), lowered.terms.len())
        })
        .collect();
    sized.sort_by_key(|(i, saturates, terms)| (std::cmp::Reverse(*terms), !*saturates, *i));
    let selected: BTreeSet<usize> = sized
        .iter()
        .enumerate()
        .filter(|(rank, (_, saturates, _))| *rank < 8 || *saturates)
        .map(|(_, (i, _, _))| *i)
        .collect();
    assert!(selected.len() >= 16, "the selection must cover the c16-saturating coordinates");

    let started = std::time::Instant::now();
    let report: Vec<String> = selected
        .par_iter()
        .map(|&i| {
            let (name, li, regime, lowered, prices) = &coordinates[i];
            let tag = if *regime == BwdRegime::R0 { "R0" } else { "Ext" };
            let depth = default_target_depth(*regime);
            let sweep = sweep_budgets(lowered, prices, depth)
                .unwrap_or_else(|e| panic!("[{name} L{li} {tag}] sweep: {e:?}"));
            assert_eq!(sweep.outcomes.len(), CellBudget::ALL.len());

            let mut greedy_wins = 0usize;
            for outcome in &sweep.outcomes {
                assert!(outcome.candidates.len() <= 3, "bounded seed selection");
                certify_paging_plan(lowered, prices, &outcome.plan).unwrap_or_else(|e| {
                    panic!(
                        "[{name} L{li} {tag} {}] certificate: {e:?}",
                        outcome.request.budget.label()
                    )
                });
                assert!(
                    outcome.plan.cost.peak_resident_lanes <= outcome.request.budget.lanes(),
                    "[{name} L{li} {tag} {}] over budget",
                    outcome.request.budget.label()
                );
                // The winner really is the exact best over the candidates.
                let best = outcome
                    .candidates
                    .iter()
                    .min_by(|a, b| (a.score, &a.order).cmp(&(b.score, &b.order)))
                    .expect("at least one candidate");
                assert_eq!(outcome.plan.order, best.order, "the exact best score wins");
                if outcome.winner != SeedKind::StableNormalized {
                    greedy_wins += 1;
                }
            }

            // The whole sweep is byte-reproducible, seed selection included.
            let again = sweep_budgets(lowered, prices, depth).expect("sweep");
            let bytes = |s: &gkr_eval_isa::bwd::coeff::schedule::BudgetSweep| {
                s.outcomes.iter().flat_map(|o| o.plan.canonical_bytes()).collect::<Vec<u8>>()
            };
            assert_eq!(bytes(&sweep), bytes(&again), "[{name} L{li} {tag}] sweep not deterministic");

            let stable = &sweep.outcomes[0];
            let widest = sweep.outcomes.last().unwrap();
            format!(
                "{name} L{li} {tag}: terms={} c2[bytes={}] c16[bytes={}] \
                 non-stable winners={greedy_wins}/15",
                lowered.terms.len(),
                stable.plan.cost.source_read_bytes,
                widest.plan.cost.source_read_bytes,
            )
        })
        .collect();

    let elapsed = started.elapsed();
    println!(
        "== seed selection over {} heaviest coordinates x 15 budgets x2 in {:.2?} ==",
        selected.len(),
        elapsed
    );
    let mut report = report;
    report.sort();
    for line in &report {
        println!("{line}");
    }
}

#[test]
fn corpus_paging_is_deterministic() {
    let coordinates = corpus_coordinates();
    let digests: Vec<(String, u64, u64)> = coordinates
        .par_iter()
        .map(|(name, li, regime, lowered, prices)| {
            let tag = if *regime == BwdRegime::R0 { "R0" } else { "Ext" };
            let order = stable_normalized_order(lowered);
            let request = PagingRequest {
                budget: CellBudget::new(8).unwrap(),
                target_depth: default_target_depth(*regime),
            };
            let a = page_projections(lowered, prices, request, &order).expect("pager");
            let b = page_projections(lowered, prices, request, &order).expect("pager");
            (
                format!("{name} L{li} {tag}"),
                fnv64(&a.canonical_bytes()),
                fnv64(&b.canonical_bytes()),
            )
        })
        .collect();

    for (coordinate, first, second) in &digests {
        assert_eq!(first, second, "{coordinate}: the pager is not deterministic");
    }
    let combined = digests.iter().fold(0xcbf2_9ce4_8422_2325u64, |h, (_, d, _)| {
        (h ^ d).wrapping_mul(0x100_0000_01b3)
    });
    println!("corpus c8 stable-order plan digest: {combined:#018x}");
}

fn fnv64(bytes: &[u8]) -> u64 {
    let mut h = 0xcbf2_9ce4_8422_2325u64;
    for b in bytes {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x100_0000_01b3);
    }
    h
}
