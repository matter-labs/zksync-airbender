//! Task 6 gates: final source binding (design §9.4, §10, §12.3).
//!
//! Two claims are gated here, and they pull in opposite directions:
//!
//!   * the FORWARD program's binding is byte-identical after the sequence core was
//!     lifted out of `fwd::binding::bind_final_sources` — pinned locally by
//!     `forward_binding_and_digest_are_unchanged` over the whole forward corpus,
//!     and by `tests/fwd_digest.rs` (release, `--ignored`) over the encoded
//!     programs and all five indexed context tables; and
//!   * the BACKWARD coefficient schedule binds ONE source coordinate per PHYSICAL
//!     source resolution, with `first_access` assigned dead last.
//!
//! Nothing here encodes a u16 (Task 7) or builds an artifact (Task 8).

mod common;

use std::collections::{BTreeMap, BTreeSet};

use common::{CrossFields, FIXTURES, layers_with_bwd_roots, load_dag_sched};
use cs::gkr_compiler::dag_ir::{BwdRegime, FieldKind, ReadPlace};
use gkr_eval_isa::bwd::coeff::bind::{
    CoeffSourceBinding, SourceCertificateError, bind_coeff_sources, certify_source_binding,
};
use gkr_eval_isa::bwd::coeff::stats::WindowFamily;
use gkr_eval_isa::bwd::coeff::limits::in_scope::MAX_SOURCE_WINDOWS_USED;
use gkr_eval_isa::bwd::coeff::place::{CoeffPlacement, ScheduledInstr, ValueUse, place_paging_plan};
use gkr_eval_isa::bwd::coeff::schedule::{
    CellBudget, OpCounts, PUBLISH_TARGET_DEPTH, PagingPlan, PagingRequest, SlotKind, SourcePrice,
    ValueWidth, default_target_depth, page_projections, source_prices, stable_normalized_order,
    term_slots,
};
use gkr_eval_isa::bwd::coeff::{
    CoeffLayer, CoeffSource, CoeffTerm, CoefficientRecipeId, ProjectionId, SourceId, TermId,
    lower_coeff_layer, source_window_count,
};
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::bwd::source::OriginLeaf;
use gkr_eval_isa::fwd::binding::BackingKey;
use gkr_eval_isa::fwd::compile::compile_circuit;
use gkr_eval_isa::fwd::isa::{Instr, OperandField, OperandLine, Program};
use rayon::prelude::*;

/// The forward-compilable corpus: the same 11 committed `b16` layouts
/// `fwd_digest.rs` and `source_window_census.rs` compile.
const FORWARD_FIXTURES: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_g_function_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "inits_and_teardowns_preprocessed_layout_gkr.json",
    "jump_branch_slt_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "mem_subword_only_layout_gkr.json",
    "mem_word_only_layout_gkr.json",
    "shift_binop_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
];

// ── Forward equivalence ──────────────────────────────────────────────────────

/// FNV-1a, 64-bit — the same hash `fwd_digest.rs` pins with.
fn fnv1a(bytes: &[u8]) -> u64 {
    const OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
    const PRIME: u64 = 0x0000_0100_0000_01b3;
    let mut h = OFFSET_BASIS;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(PRIME);
    }
    h
}

fn push_u64(buf: &mut Vec<u8>, v: u64) {
    buf.extend_from_slice(&v.to_le_bytes());
}

/// Explicit, hand-rolled serialization (never `Debug`): variant tag in declaration
/// order, then fields, `usize` widened to `u64` LE.
fn serialize_backing(buf: &mut Vec<u8>, key: &BackingKey) {
    let field_tag = |f: OperandField| match f {
        OperandField::Base => 0u8,
        OperandField::Ext => 1,
    };
    match key {
        BackingKey::BaseLayerMemory => buf.push(0),
        BackingKey::BaseLayerWitness => buf.push(1),
        BackingKey::Setup => buf.push(2),
        BackingKey::Scratch => buf.push(3),
        BackingKey::LayerOutput { layer, field } => {
            buf.push(4);
            push_u64(buf, *layer as u64);
            buf.push(field_tag(*field));
        }
        BackingKey::CacheOutput { layer, field } => {
            buf.push(5);
            push_u64(buf, *layer as u64);
            buf.push(field_tag(*field));
        }
    }
}

fn visit_operands(program: &Program, mut visit: impl FnMut(&OperandLine)) {
    for instr in &program.instrs {
        match instr {
            Instr::Mov { src: Some(operand), .. } => visit(operand),
            Instr::Mov { src: None, .. } => {}
            Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
                operands.iter().for_each(&mut visit);
            }
            Instr::Fma { pairs, .. } => {
                for (lhs, rhs) in pairs {
                    visit(lhs);
                    visit(rhs);
                }
            }
        }
    }
}

/// Everything final binding decides for one forward program: the window layout
/// (backing, free base, referenced columns, fold descriptors) and every bound
/// operand coordinate in program order.
fn forward_binding_bytes(name: &str) -> Vec<u8> {
    let (dag, schedule, artifact) = load_dag_sched(name);
    let compiled = compile_circuit(&dag, &schedule, &artifact)
        .unwrap_or_else(|e| panic!("[{name}] forward compile: {e:?}"));
    assert_eq!(compiled.budget, 16, "[{name}] expected the committed four-cell budget");
    let mut buf = Vec::new();
    for (li, layer) in compiled.layers.iter().enumerate() {
        push_u64(&mut buf, li as u64);
        let table = &layer.ctx.source_windows;
        push_u64(&mut buf, table.len() as u64);
        for window in table.windows() {
            serialize_backing(&mut buf, &window.backing);
            push_u64(&mut buf, window.first_column as u64);
            for column in window.referenced_columns() {
                push_u64(&mut buf, column as u64);
            }
            buf.push(0xff);
            for (column, desc) in window.fold_descriptors() {
                push_u64(&mut buf, column as u64);
                push_u64(&mut buf, u64::from(desc));
            }
            buf.push(0xfe);
        }
        visit_operands(&layer.program, |operand| match *operand {
            OperandLine::LogicalGlobal { .. } | OperandLine::LogicalFold { .. } => {
                panic!("[{name} L{li}] final forward program kept an unbound logical source")
            }
            OperandLine::Source { window, column, first_access } => {
                assert!(
                    !first_access,
                    "[{name} L{li}] the forward VM has no first-access semantics"
                );
                buf.push(window);
                buf.push(column);
                buf.push(u8::from(first_access));
            }
            _ => {}
        });
    }
    buf
}

/// The forward binding of every committed layout, digested.
///
/// The value was captured on the pre-extraction code and is NOT regenerated: it is
/// the whole point of the test. A drift here is a forward regression, not a stale
/// pin — the same rule `fwd_digest.rs` states for its own aggregate.
#[test]
fn forward_binding_and_digest_are_unchanged() {
    let mut all = Vec::new();
    for name in FORWARD_FIXTURES {
        let bytes = forward_binding_bytes(name);
        let digest = fnv1a(&bytes);
        println!("BINDING {name} {digest:016x}");
        push_u64(&mut all, digest);
    }
    let aggregate = fnv1a(&all);
    println!("BINDING-ALL {aggregate:016x}");
    assert_eq!(aggregate, 0x2cc4_eb9b_7757_69a7, "forward source binding drift");
}

// ── Backward: synthetic construction ─────────────────────────────────────────

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

/// A layer whose sources sit at CHOSEN backing columns — the free variable this
/// task's window partitioning is a function of.
fn synthetic_at(
    regime: BwdRegime,
    columns: &[(usize, FieldKind)],
    terms: Vec<CoeffTerm>,
) -> (CoeffLayer, Vec<SourcePrice>) {
    for (i, term) in terms.iter().enumerate() {
        assert_eq!(term.id(), TermId(i as u32), "synthetic terms must be dense and in order");
    }
    let layer = CoeffLayer {
        regime,
        c_init: None,
        coefficients: Vec::new(),
        sources: columns.iter().map(|&(c, f)| read_source(c, f)).collect(),
        terms,
    };
    let prices = columns.iter().map(|&(_, f)| price_of(f)).collect();
    (layer, prices)
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

/// Page, place and bind one layer at one budget, checking every certificate on
/// the way through.
fn page_place_bind(
    layer: &CoeffLayer,
    prices: &[SourcePrice],
    cells: u8,
) -> (PagingPlan, CoeffPlacement, CoeffSourceBinding) {
    let order = stable_normalized_order(layer);
    let request = PagingRequest {
        budget: CellBudget::new(cells).expect("c2..c16"),
        target_depth: default_target_depth(layer.regime),
    };
    let plan = page_projections(layer, prices, request, &order).expect("pager");
    let placement = place_paging_plan(layer, prices, &plan).expect("placement");
    let cross = CrossFields::new();
    let binding = bind_coeff_sources(layer, &cross, &placement).expect("binding");
    certify_source_binding(layer, &cross, &placement, &binding).expect("source certificate");
    (plan, placement, binding)
}

/// Every bound input of one source, in execution order.
fn inputs_of(binding: &CoeffSourceBinding, source: SourceId) -> Vec<bool> {
    binding
        .uses
        .iter()
        .filter(|u| u.source == source)
        .map(|u| u.first_access)
        .collect()
}

// ── Window partitioning ──────────────────────────────────────────────────────

/// Columns chosen so ONE logical backing needs three windows: `0..=127`,
/// `128..=255`, then a far column.
const SPREAD: &[(usize, FieldKind)] = &[
    (0, FieldKind::Base),
    (64, FieldKind::Base),
    (127, FieldKind::Base),
    (128, FieldKind::Base),
    (200, FieldKind::Base),
    (255, FieldKind::Base),
    (4000, FieldKind::Base),
];

fn spread_layer() -> (CoeffLayer, Vec<SourcePrice>) {
    let terms = (0..SPREAD.len() as u32).map(|i| c0(i, i, FieldKind::Base)).collect();
    synthetic_at(BwdRegime::R0, SPREAD, terms)
}

#[test]
fn large_sources_partition_only_during_final_binding() {
    let (layer, prices) = spread_layer();

    // One logical backing, seven sources, three windows: the split exists NOWHERE
    // before this call. The layer, the order, the plan and the placement all speak
    // SourceId/ProjectionId only.
    let (plan, placement, binding) = page_place_bind(&layer, &prices, 16);
    assert_eq!(
        binding.windows.iter().map(|w| w.family).collect::<BTreeSet<_>>().len(),
        1,
        "the fixture is a single logical backing"
    );
    assert_eq!(binding.windows.len(), 3, "and it must be partitioned into three windows");

    // Binding is a pure reader of the schedule: it decides nothing the pager or the
    // placer already decided.
    let before = plan.canonical_bytes();
    let placement_before = placement.clone();
    let again = bind_coeff_sources(&layer, &CrossFields::new(), &placement).expect("binding");
    assert_eq!(plan.canonical_bytes(), before, "binding mutated the paging plan");
    assert_eq!(placement, placement_before, "binding mutated the placement");
    assert_eq!(again.windows, binding.windows, "binding is not deterministic");

    // ...and the partition is a function of the FINAL source set alone, not of any
    // scheduling decision: every budget produces the same window layout.
    for cells in [2u8, 3, 5, 8, 16] {
        let (_, _, other) = page_place_bind(&layer, &prices, cells);
        assert_eq!(
            other.windows, binding.windows,
            "c{cells} partitioned the same backing differently"
        );
    }
}

#[test]
fn large_source_windows_cover_contiguous_ranges() {
    let (layer, prices) = spread_layer();
    let (_, _, binding) = page_place_bind(&layer, &prices, 16);

    let spans: Vec<(usize, Vec<usize>)> = binding
        .windows
        .iter()
        .map(|w| (w.first_column, w.columns.iter().map(|c| c.column).collect()))
        .collect();
    assert_eq!(
        spans,
        vec![
            (0, vec![0, 64, 127]),
            (128, vec![128, 200, 255]),
            (4000, vec![4000]),
        ]
    );

    assert_contiguous_windows(&binding);
}

/// Every window's invariants (§9.4): freely based at its own first referenced
/// column, ascending, at most 128 contiguous columns, and — within one backing —
/// non-overlapping and unmergeable.
fn assert_contiguous_windows(binding: &CoeffSourceBinding) {
    let mut previous: Option<(usize, usize)> = None; // (family index, first_column)
    let mut family_index = BTreeMap::new();
    for (index, window) in binding.windows.iter().enumerate() {
        let next = family_index.len();
        let family = *family_index.entry(window.family).or_insert(next);
        assert!(!window.columns.is_empty(), "window {index} is empty");
        assert_eq!(
            window.columns[0].column, window.first_column,
            "window {index} is not based at its first referenced column"
        );
        for pair in window.columns.windows(2) {
            assert!(pair[0].column < pair[1].column, "window {index} is not ascending");
        }
        let last = window.columns.last().expect("non-empty").column;
        assert!(
            last - window.first_column < 128,
            "window {index} spans {} columns", last - window.first_column + 1
        );
        if let Some((previous_family, previous_first)) = previous
            && previous_family == family
        {
            assert!(
                window.first_column >= previous_first + 128,
                "windows {} and {index} of one backing are mergeable", index - 1
            );
        }
        previous = Some((family, window.first_column));
    }
}

// ── The declared window family ───────────────────────────────────────────────

/// A window's `family` is what the descriptor reads to choose DRAM versus
/// procedural resolution and to size the backing's own field, so the certificate
/// has to RE-DERIVE it from the source rather than trust it.
///
/// Nothing else can catch a wrong one: `CoeffSourceBinding::resolve` is keyed by
/// `(window, column)` alone, so a window claiming the wrong family still resolves
/// every coordinate to the right `SourceId` and every other §12.3 clause passes.
/// This test flips one family and requires the rejection.
#[test]
fn a_window_may_not_declare_a_family_its_source_does_not_have() {
    let (layer, prices) = spread_layer();
    let (_, placement, binding) = page_place_bind(&layer, &prices, 4);
    let cross = CrossFields::new();

    // `SPREAD` is all `BaseLayerWitness`, so procedural is a genuine flip: it
    // changes `is_procedural`, which is exactly the decision the family drives.
    let true_family = binding.windows[0].family;
    assert_ne!(true_family, WindowFamily::VirtualSetup { kind: 0 });

    let mut tampered = binding.clone();
    tampered.windows[0].family = WindowFamily::VirtualSetup { kind: 0 };
    assert!(
        tampered.windows[0].is_procedural() && !binding.windows[0].is_procedural(),
        "the flip must change the DRAM/procedural decision, or it proves nothing"
    );
    // Everything else about the tampered binding is still perfectly consistent.
    for use_ in &tampered.uses {
        assert_eq!(
            tampered.resolve(use_.window, use_.column),
            binding.resolve(use_.window, use_.column),
            "the tamper must not disturb coordinate resolution"
        );
    }

    let error = certify_source_binding(&layer, &cross, &placement, &tampered)
        .expect_err("a wrong family must be rejected");
    assert_eq!(
        error,
        SourceCertificateError::WindowBackingMismatch {
            window: 0,
            column: binding.windows[0].columns[0].column,
            source: binding.windows[0].columns[0].source,
        }
    );
}

/// A wrong COLUMN address is caught too — by coordinate resolution first, since
/// a relabelled column no longer resolves the bound `(window, column)` pair, and
/// by the family/address comparison as the backstop when it does.
///
/// Kept separate from the test above because only that one is a real gap probe:
/// removing the family check leaves this case still rejected.
#[test]
fn a_window_may_not_relabel_a_column_address() {
    let (layer, prices) = spread_layer();
    let (_, placement, binding) = page_place_bind(&layer, &prices, 4);
    let cross = CrossFields::new();

    // Move an INTERIOR column of one window down by one. It stays ascending, in
    // span, based at the same `first_column` and inside the same window, so every
    // structural rule still holds — the only thing wrong is the address itself.
    let (window, slot) = binding
        .windows
        .iter()
        .enumerate()
        .find_map(|(w, entry)| {
            (1..entry.columns.len().saturating_sub(1))
                .find(|&i| entry.columns[i].column - 1 > entry.columns[i - 1].column)
                .map(|i| (w, i))
        })
        .expect("SPREAD gives window 0 the columns 0, 64, 127");
    let mut tampered = binding.clone();
    tampered.windows[window].columns[slot].column -= 1;

    let error = certify_source_binding(&layer, &cross, &placement, &tampered)
        .expect_err("a relabelled column must be rejected");
    assert!(
        matches!(
            error,
            SourceCertificateError::WindowBackingMismatch { .. }
                | SourceCertificateError::CoordinateMismatch { .. }
        ),
        "unexpected rejection: {error:?}"
    );
}

// ── First access ─────────────────────────────────────────────────────────────

#[test]
fn native_dual_has_one_first_access_bit() {
    use FieldKind::Ext as E;
    // A native dual factor consumes BOTH projections of its source through ONE
    // operand slot, so its pair resolution must consume ONE source coordinate and
    // ONE first-access bit — never one per projection.
    let columns: Vec<(usize, FieldKind)> = (0..5).map(|i| (i, E)).collect();
    let terms = vec![
        dual(0, 0, 0),
        dual(1, 0, 1),
        dual(2, 2, 3),
        dual(3, 4, 0),
        dual(4, 1, 2),
        dual(5, 3, 4),
        dual(6, 0, 2),
    ];
    let (layer, prices) = synthetic_at(BwdRegime::Ext, &columns, terms);

    // c2 holds two E4 values, so the pairs really are re-resolved; c16 holds all
    // five, so most factors read cells and resolve nothing.
    for cells in [2u8, 16] {
        let (_, placement, binding) = page_place_bind(&layer, &prices, cells);
        let mut pair_resolutions = 0usize;
        for (index, instr) in placement.instrs.iter().enumerate() {
            let ScheduledInstr::Term { term, uses, .. } = instr else { continue };
            let slots = term_slots(&layer, &layer.terms[term.0 as usize]).expect("slots");
            assert_eq!(uses.len(), slots.len(), "one value use per deduplicated slot");
            for (slot, use_) in uses.iter().enumerate() {
                assert!(
                    matches!(slots[slot], SlotKind::DualFactor(_)),
                    "the fixture is native duals only"
                );
                let bound = binding
                    .uses
                    .iter()
                    .filter(|u| u.instr as usize == index && u.slot as usize == slot)
                    .count();
                // A resident pair reads cells and resolves nothing; every other
                // form resolves the pair ONCE.
                let expected = usize::from(!matches!(use_, ValueUse::Cell(_)));
                assert_eq!(
                    bound, expected,
                    "c{cells} {term:?} slot {slot}: {use_:?} bound {bound} coordinates"
                );
                pair_resolutions += bound;
            }
        }
        assert!(pair_resolutions > 0, "c{cells}: no pair was resolved from source");
        assert_eq!(
            binding.uses.iter().filter(|u| u.first_access).count(),
            layer.sources.len(),
            "c{cells}: one first-access bit per source, not per projection"
        );
        for source in (0..layer.sources.len() as u32).map(SourceId) {
            let marks = inputs_of(&binding, source);
            assert_eq!(marks.iter().filter(|f| **f).count(), 1, "c{cells} {source:?}");
            assert!(marks[0], "c{cells} {source:?}: the earliest resolution carries the bit");
        }
    }
}

#[test]
fn unfused_repeated_source_marks_only_first_physical_resolution() {
    use FieldKind::Ext as E;
    // Six E4 sources over a two-cell file: source 5 is consumed by five terms that
    // no order can make adjacent (each pairs it with a different partner, and the
    // partners chain), so it cannot stay resident between them. Nothing fuses those
    // resolutions — they are separate terms, not one dual factor — and every one of
    // them is a physical resolution.
    let columns: Vec<(usize, FieldKind)> = (0..6).map(|i| (i, E)).collect();
    let mut terms = Vec::new();
    for i in 0..5u32 {
        terms.push(c2(2 * i, i, E, (i + 1) % 5, E));
        terms.push(c2(2 * i + 1, i, E, 5, E));
    }
    let (layer, prices) = synthetic_at(BwdRegime::R0, &columns, terms);

    let mut repeated = 0usize;
    for cells in 2u8..=16 {
        let (_, _, binding) = page_place_bind(&layer, &prices, cells);
        for source in (0..layer.sources.len() as u32).map(SourceId) {
            let marks = inputs_of(&binding, source);
            assert!(!marks.is_empty(), "c{cells} {source:?}: every source is resolved");
            assert_eq!(
                marks.iter().filter(|f| **f).count(),
                1,
                "c{cells} {source:?}: exactly one physical resolution is first"
            );
            assert!(marks[0], "c{cells} {source:?}: the EARLIEST resolution carries the bit");
            if marks.len() > 1 {
                repeated += 1;
            }
        }
    }
    println!("re-resolved (source, budget) pairs: {repeated}");
    assert!(
        repeated > 0,
        "the fixture never forced a second physical resolution — the test is vacuous"
    );
}

#[test]
fn materializing_source_has_exactly_one_first_access() {
    for name in ["add_sub_lui_auipc_mop_layout_gkr.json", "blake2_g_function_layout_gkr.json"] {
        for (li, canonical, cross) in layers_with_bwd_roots(name) {
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                let distilled = distill(&canonical, regime, &cross, None);
                let lowered = lower_coeff_layer(&canonical, &distilled)
                    .unwrap_or_else(|e| panic!("[{name} L{li}] lowering: {e:?}"));
                let depth = default_target_depth(regime);
                let prices = source_prices(&lowered, &distilled, depth);
                let order = stable_normalized_order(&lowered);
                let request = PagingRequest { budget: CellBudget::new(4).unwrap(), target_depth: depth };
                let plan = page_projections(&lowered, &prices, request, &order).expect("pager");
                let placement = place_paging_plan(&lowered, &prices, &plan).expect("placement");
                let binding = bind_coeff_sources(&lowered, &distilled.cross_fields, &placement)
                    .unwrap_or_else(|e| panic!("[{name} L{li} {regime:?}] binding: {e:?}"));
                certify_source_binding(&lowered, &distilled.cross_fields, &placement, &binding)
                    .unwrap_or_else(|e| panic!("[{name} L{li} {regime:?}] certificate: {e:?}"));

                // §10.2's static policy, and nothing else, decides materialization.
                assert_eq!(
                    binding.materialize,
                    depth >= PUBLISH_TARGET_DEPTH,
                    "[{name} L{li} {regime:?}] materialization is not the static policy"
                );

                let mut marks: BTreeMap<SourceId, usize> = BTreeMap::new();
                for use_ in &binding.uses {
                    *marks.entry(use_.source).or_default() += usize::from(use_.first_access);
                }
                assert!(!marks.is_empty(), "[{name} L{li} {regime:?}] no source was resolved");
                for (source, first) in &marks {
                    assert_eq!(
                        *first, 1,
                        "[{name} L{li} {regime:?}] {source:?} has {first} first accesses"
                    );
                }
                // The bit is INERT at R0, not absent: an unpublished source still
                // carries exactly one marked resolution.
                if !binding.materialize {
                    assert!(
                        binding.uses.iter().any(|u| u.first_access),
                        "[{name} L{li} {regime:?}] a non-materializing program dropped the marker"
                    );
                }
            }
        }
    }
}

// ── The production corpus ────────────────────────────────────────────────────

#[test]
fn window_and_column_fit_six_and_seven_bits() {
    #[allow(clippy::type_complexity)]
    let mut coordinates: Vec<(String, usize, BwdRegime)> = Vec::new();
    for name in FIXTURES {
        for (li, _, _) in layers_with_bwd_roots(name) {
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                coordinates.push((name.to_string(), li, regime));
            }
        }
    }
    assert_eq!(coordinates.len(), 114, "57 backward-bearing layers x 2 regimes");

    let rows: Vec<(String, usize, usize, usize)> = FIXTURES
        .par_iter()
        .flat_map(|name| {
            let mut out = Vec::new();
            for (li, canonical, cross) in layers_with_bwd_roots(name) {
                for regime in [BwdRegime::R0, BwdRegime::Ext] {
                    let distilled = distill(&canonical, regime, &cross, None);
                    let lowered = lower_coeff_layer(&canonical, &distilled)
                        .unwrap_or_else(|e| panic!("[{name} L{li}] lowering: {e:?}"));
                    let depth = default_target_depth(regime);
                    let prices = source_prices(&lowered, &distilled, depth);
                    let order = stable_normalized_order(&lowered);
                    let tag = format!(
                        "{name} L{li} {}",
                        if regime == BwdRegime::R0 { "R0" } else { "Ext" }
                    );
                    let mut windows = 0usize;
                    let mut max_column = 0usize;
                    for cells in [2u8, 16] {
                        let request = PagingRequest {
                            budget: CellBudget::new(cells).expect("c2..c16"),
                            target_depth: depth,
                        };
                        let plan =
                            page_projections(&lowered, &prices, request, &order).expect("pager");
                        let placement =
                            place_paging_plan(&lowered, &prices, &plan).expect("placement");
                        let binding =
                            bind_coeff_sources(&lowered, &distilled.cross_fields, &placement)
                                .unwrap_or_else(|e| panic!("[{tag} c{cells}] binding: {e:?}"));
                        certify_source_binding(&lowered, &distilled.cross_fields, &placement, &binding)
                            .unwrap_or_else(|e| panic!("[{tag} c{cells}] certificate: {e:?}"));
                        assert_contiguous_windows(&binding);
                        for use_ in &binding.uses {
                            assert!(use_.window < 64, "[{tag} c{cells}] window {}", use_.window);
                            assert!(use_.column < 128, "[{tag} c{cells}] column {}", use_.column);
                            max_column = max_column.max(use_.column as usize);
                        }
                        assert_eq!(
                            binding.windows.len(),
                            source_window_count(&lowered, &distilled),
                            "[{tag} c{cells}] binding disagrees with the Task 3 census"
                        );
                        windows = windows.max(binding.windows.len());
                    }
                    out.push((tag, li, windows, max_column));
                }
            }
            out
        })
        .collect();

    let mut ranked = rows.clone();
    ranked.sort_by(|a, b| b.2.cmp(&a.2).then(a.0.cmp(&b.0)));
    for (tag, _, windows, max_column) in ranked.iter().take(8) {
        println!("  {tag:<52} windows={windows:>2} highest column offset={max_column}");
    }
    let mut histogram: BTreeMap<usize, usize> = BTreeMap::new();
    for row in &rows {
        *histogram.entry(row.2).or_default() += 1;
    }
    println!("window-count histogram over {} coordinates: {histogram:?}", rows.len());

    let (worst, _, windows, _) =
        rows.iter().max_by_key(|r| r.2).expect("the corpus is not empty").clone();
    let max_column = rows.iter().map(|r| r.3).max().unwrap_or(0);
    println!("realized maximum: {windows} windows ({worst}), highest column offset {max_column}");
    assert!(windows <= 64, "the six-bit window field does not fit the corpus");
    assert!(max_column < 128, "the seven-bit column field does not fit the corpus");
    assert_eq!(
        windows, MAX_SOURCE_WINDOWS_USED,
        "realized window maximum drifted from the Task 3 census pin"
    );
}
