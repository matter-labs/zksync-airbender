//! Task-7 gate: the ENCODED interpreter against the SEMANTIC one (design §12.4:
//! "encoded CPU interpreter vs semantic interpreter").
//!
//! The central claim is corpus-wide, not synthetic: for every one of the 114
//! in-scope `(circuit, layer, regime)` coordinates, at several cell budgets, the
//! decoded u16 program run through a real cell file produces bit-identical
//! `(acc_c0, acc_c2)` to `interpret_coeff_layer` over the SAME
//! [`CoeffResolver`]. Both interpreters therefore see the same coefficients and
//! the same source pairs, so any difference is a codec, placement, or residency
//! defect and nothing else.
//!
//! The encoded interpreter is deliberately strict about the cell file: a read must
//! find a value of the width its OPCODE assigns at the lane it names, and a plan's
//! resident `Endpoint0` must equal what its source resolves to. Corpus parity
//! therefore also exercises §12.2's cell-liveness claim on every real program, not
//! only its certificate.
//!
//! Moves and the three execution rejections are synthetic: the production corpus
//! emits ZERO moves at every budget probed (placement's offline two-pass never
//! needs the repair), so hand-built programs are the only way to cover them.
//!
//! This file also pins the REALIZED encoded program size per coordinate against
//! Task 3's schedule-independent bounds. Read the scope carefully: those sizes are
//! measured on THIS file's pipeline — [`stable_normalized_order`] at the three
//! sampled budgets [`BUDGETS`] — which is a codec-stability gate, NOT the
//! production schedule. Production uses `select_paged_order`, which is larger at
//! every overlapping budget, and its corpus-wide maximum over all fifteen budgets
//! is Task 8's `in_scope::MAX_REALIZED_PROGRAM_BYTES`. The two numbers are
//! different quantities and neither contradicts the other; see
//! [`STABLE_ORDER_MAX_BYTES`].

mod common;

use std::collections::BTreeMap;

use common::{FIXTURES, layers_with_bwd_roots};
use cs::gkr_compiler::dag_ir::{Bf, BwdRegime, Ext, FieldKind, ReadPlace};
use field::{Field, FieldExtension, PrimeField};
use gkr_eval_isa::bwd::coeff::bind::{
    CoeffSourceBinding, bind_coeff_sources, certify_source_binding,
};
use gkr_eval_isa::bwd::coeff::encode::{
    CoeffCodecError, DecodedCell, DecodedInstr, DecodedUse, EncodedProgram, SourceCoord,
    certify_encoding, encode_instrs, encode_program,
};
use gkr_eval_isa::bwd::coeff::limits::{TermCategory, in_scope};
use gkr_eval_isa::bwd::coeff::place::{CoeffPlacement, PlanAction, place_paging_plan};
use gkr_eval_isa::bwd::coeff::schedule::{
    CellBudget, OpCounts, PagingRequest, SourcePrice, ValueWidth, default_target_depth,
    page_projections, source_prices, stable_normalized_order,
};
use gkr_eval_isa::bwd::coeff::{
    CoeffLayer, CoeffResolver, CoeffSource, CoeffTerm, CoefficientRecipeId, ProjectionId, SourceId,
    TermId, interpret_coeff_layer, interpret_encoded_program, lower_coeff_layer,
};
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::bwd::source::OriginLeaf;
use rayon::prelude::*;

/// Cell budgets every parity claim is made at. More than one on purpose: the
/// budget changes which forms placement emits (c2 is cell-starved and direct-heavy,
/// c16 is fill- and resident-heavy), so a codec bug in one form hides at a single
/// budget.
const BUDGETS: [u8; 3] = [2, 4, 16];
/// Rows sampled per coordinate.
const ROWS: [usize; 3] = [0, 1, 37];

// ── A deterministic resolver both interpreters share ─────────────────────────

const FNV_OFFSET: u32 = 0x811c_9dc5;
const FNV_PRIME: u32 = 0x0100_0193;

fn fnv(seed: u32, words: &[u32]) -> u32 {
    let mut h = seed;
    for w in words {
        for b in w.to_le_bytes() {
            h ^= u32::from(b);
            h = h.wrapping_mul(FNV_PRIME);
        }
    }
    h
}

fn bf(v: u32) -> Bf {
    Bf::from_u32_with_reduction(v)
}

fn lift(v: Bf) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(v)
}

/// Four independent base digits, so an `Ext` value is genuinely extension-valued
/// and a BF/E4 width confusion cannot pass unnoticed.
fn ext(tag: u32, a: u32, b: u32) -> Ext {
    let coeffs: [Bf; 4] = std::array::from_fn(|i| bf(fnv(FNV_OFFSET, &[tag, a, b, i as u32])));
    <Ext as FieldExtension<Bf>>::from_coeffs(coeffs)
}

struct Pseudo<'a> {
    layer: &'a CoeffLayer,
    seed: u32,
}

impl CoeffResolver for Pseudo<'_> {
    fn coefficient(&self, id: CoefficientRecipeId) -> Ext {
        ext(0xc0ef, self.seed, id.0)
    }

    fn source_pair(&self, id: SourceId, row: usize) -> (Ext, Ext) {
        let field = self.layer.sources[id.0 as usize].field;
        let s0 = ext(0x5000, self.seed ^ id.0, row as u32);
        let ds = ext(0x5001, self.seed ^ id.0, row as u32);
        match field {
            // A BF source stores ONE lane, so its value must be base-embedded or
            // the cell-file model would be lying about the width.
            FieldKind::Base => (
                lift(bf(fnv(FNV_OFFSET, &[0xb0, self.seed ^ id.0, row as u32]))),
                lift(bf(fnv(FNV_OFFSET, &[0xb1, self.seed ^ id.0, row as u32]))),
            ),
            FieldKind::Ext => (s0, ds),
        }
    }
}

// ── Pipeline ─────────────────────────────────────────────────────────────────

fn page_place_bind_encode(
    layer: &CoeffLayer,
    prices: &[SourcePrice],
    cross: &std::collections::HashMap<ReadPlace, FieldKind>,
    cells: u8,
    tag: &str,
) -> (CoeffPlacement, CoeffSourceBinding, EncodedProgram) {
    let order = stable_normalized_order(layer);
    let request = PagingRequest {
        budget: CellBudget::new(cells).expect("c2..c16"),
        target_depth: default_target_depth(layer.regime),
    };
    let plan = page_projections(layer, prices, request, &order)
        .unwrap_or_else(|e| panic!("[{tag}] pager: {e:?}"));
    let placement = place_paging_plan(layer, prices, &plan)
        .unwrap_or_else(|e| panic!("[{tag}] placement: {e:?}"));
    let binding = bind_coeff_sources(layer, cross, &placement)
        .unwrap_or_else(|e| panic!("[{tag}] binding: {e:?}"));
    certify_source_binding(layer, cross, &placement, &binding)
        .unwrap_or_else(|e| panic!("[{tag}] source certificate: {e:?}"));
    let program = encode_program(layer, &placement, &binding)
        .unwrap_or_else(|e| panic!("[{tag}] encode: {e:?}"));
    certify_encoding(layer, &placement, &binding, &program)
        .unwrap_or_else(|e| panic!("[{tag}] encoding certificate: {e:?}"));
    (placement, binding, program)
}

/// One `(coordinate, budget)`'s realized encoded size.
#[derive(Clone, Debug)]
struct Realized {
    tag: String,
    cells: u8,
    terms: usize,
    words: usize,
    bytes: usize,
    moves: usize,
    squared: usize,
}
// ── The corpus sweep both gates run on ───────────────────────────────────────

/// Page, place, bind and encode every in-scope coordinate at every sampled budget
/// on the [`stable_normalized_order`] path, asserting encoded/semantic parity as it
/// goes, and return each program's realized size sorted worst-first.
///
/// SCOPE, because the numbers this returns are easy to mistake for production
/// ones: the order is `stable_normalized_order`, not `select_paged_order`, and the
/// budgets are the three of [`BUDGETS`], not all fifteen. Both gates below are
/// therefore statements about *this* pipeline.
fn stable_order_corpus_sweep() -> Vec<Realized> {
    let rows: Vec<Vec<Realized>> = FIXTURES
        .par_iter()
        .map(|name| {
            let mut out = Vec::new();
            for (li, canonical, cross) in layers_with_bwd_roots(name) {
                for regime in [BwdRegime::R0, BwdRegime::Ext] {
                    let distilled = distill(&canonical, regime, &cross, None);
                    let layer = lower_coeff_layer(&canonical, &distilled)
                        .unwrap_or_else(|e| panic!("[{name} L{li}] lowering: {e:?}"));
                    let depth = default_target_depth(regime);
                    let prices = source_prices(&layer, &distilled, depth);
                    let label = if regime == BwdRegime::R0 { "R0" } else { "Ext" };
                    let resolver = Pseudo { layer: &layer, seed: (li as u32) << 8 | 0x5a };
                    for cells in BUDGETS {
                        let tag = format!("{name} L{li} {label} c{cells}");
                        let (placement, binding, program) = page_place_bind_encode(
                            &layer,
                            &prices,
                            &distilled.cross_fields,
                            cells,
                            &tag,
                        );
                        for row in ROWS {
                            let semantic = interpret_coeff_layer(&layer, row, &resolver)
                                .unwrap_or_else(|e| panic!("[{tag}] semantic: {e:?}"));
                            let encoded =
                                interpret_encoded_program(&program, &binding, row, &resolver)
                                    .unwrap_or_else(|e| panic!("[{tag} row {row}] encoded: {e:?}"));
                            assert_eq!(
                                encoded, semantic,
                                "[{tag} row {row}] encoded and semantic disagree"
                            );
                        }
                        let records = gkr_eval_isa::bwd::coeff::encode::program_records(
                            &layer,
                            &placement,
                            &binding,
                        )
                        .expect("records");
                        out.push(Realized {
                            tag: format!("{name} L{li} {label}"),
                            cells,
                            terms: layer.terms.len(),
                            words: program.words.len(),
                            bytes: program.bytes(),
                            moves: records
                                .iter()
                                .filter(|i| matches!(i, DecodedInstr::Move { .. }))
                                .count(),
                            squared: records.iter().filter(|i| i.is_squared()).count(),
                        });
                    }
                }
            }
            out
        })
        .collect();

    let mut realized: Vec<Realized> = rows.into_iter().flatten().collect();
    realized
        .sort_by(|a, b| b.bytes.cmp(&a.bytes).then(a.tag.cmp(&b.tag)).then(a.cells.cmp(&b.cells)));
    assert_eq!(
        realized.len(),
        in_scope::COORDINATES * BUDGETS.len(),
        "114 coordinates x {} budgets",
        BUDGETS.len()
    );
    realized
}

// ── The parity gate ──────────────────────────────────────────────────────────

#[test]
fn encoded_and_semantic_interpreters_agree_over_the_corpus() {
    // Every parity claim is an assertion inside the sweep, made per
    // `(coordinate, budget, row)`. Reaching this line means all of them held.
    let realized = stable_order_corpus_sweep();
    assert_eq!(realized.len(), in_scope::COORDINATES * BUDGETS.len());
}

// ── The codec-stability size gate ────────────────────────────────────────────

/// Realized encoded sizes on the [`stable_normalized_order`] path at the three
/// sampled budgets, pinned exactly.
///
/// **This is not a corpus-wide production maximum, and must never be read as one.**
/// It is a codec-stability regression gate: it fixes what THIS file's pipeline
/// emits so that a change in the encoder, the placer or the pager shows up as a
/// signal rather than as noise. Production compiles with `select_paged_order` over
/// all fifteen budgets, which is strictly larger at every overlapping budget
/// (c2 5,756 vs 5,013 words; c4 5,667 vs 5,076; c16 5,636 vs 5,099), and its
/// corpus-wide maximum is Task 8's `in_scope::MAX_REALIZED_PROGRAM_BYTES`
/// (11,518 B at c3). Even swept over all fifteen budgets, this file's own path
/// peaks at 5,164 words (`bigint_with_extended_control` L0 Ext at c7, measured) —
/// so nothing here was ever a maximum over budgets either.
#[test]
fn stable_order_encoded_program_sizes_are_pinned() {
    let realized = stable_order_corpus_sweep();

    println!(
        "realized encoded program size on the stable_normalized_order path, \
         worst 15 (coordinate, budget) pairs:"
    );
    for row in realized.iter().take(15) {
        println!(
            "  {:<58} c{:<3} terms={:<5} words={:<6} bytes={:<6} squared={:<4} moves={}",
            row.tag, row.cells, row.terms, row.words, row.bytes, row.squared, row.moves
        );
    }
    for cells in BUDGETS {
        let worst = realized.iter().find(|r| r.cells == cells).expect("a row per budget");
        println!(
            "  c{cells:<3} max = {} bytes / {} words ({})",
            worst.bytes, worst.words, worst.tag
        );
    }
    let worst = &realized[0];
    let total_moves: usize = realized.iter().map(|r| r.moves).sum();
    let squared_at_max: usize = realized
        .iter()
        .filter(|r| r.cells == *BUDGETS.last().unwrap())
        .map(|r| r.squared)
        .sum();
    println!(
        "MAX on this path = {} bytes ({} c{}); production maximum = {} bytes; \
         upper bound = {}, lower bound max = {}, cap = {}",
        worst.bytes,
        worst.tag,
        worst.cells,
        in_scope::MAX_REALIZED_PROGRAM_BYTES,
        in_scope::MAX_UPPER_BOUND_PROGRAM_BYTES,
        in_scope::MAX_LOWER_BOUND_PROGRAM_BYTES,
        gkr_eval_isa::bwd::coeff::limits::KERNEL_ARGUMENT_CEILING_BYTES,
    );
    println!("corpus totals: squared records = {squared_at_max} (per budget), moves = {total_moves}");
    let total_squared = squared_at_max;

    // Task 3's conservative maximum really does bound the real encoder.
    for row in &realized {
        assert!(
            row.bytes <= in_scope::MAX_UPPER_BOUND_PROGRAM_BYTES,
            "[{}] realized {} bytes exceeds the conservative maximum {}",
            row.tag,
            row.bytes,
            in_scope::MAX_UPPER_BOUND_PROGRAM_BYTES,
        );
    }

    // ── EXACT pins ───────────────────────────────────────────────────────
    //
    // Re-pin deliberately if the encoder, the placer or the corpus changes. Every
    // name below is prefixed `STABLE_ORDER_` so the scope travels with the number:
    // the constant, the assertion message and the test name all say the same thing
    // and cannot drift apart.
    const STABLE_ORDER_WORST: &str = "bigint_with_extended_control_layout_gkr.json L0 Ext";
    /// `(cells, words, bytes)` of the largest program at each sampled budget.
    const STABLE_ORDER_PER_BUDGET_MAX: [(u8, usize, usize); 3] =
        [(2, 5013, 10_026), (4, 5076, 10_152), (16, 5099, 10_198)];
    /// The largest program over the three SAMPLED budgets on THIS path. Not a
    /// corpus-wide maximum — see the test's doc comment.
    const STABLE_ORDER_MAX_BYTES: usize = 10_198;
    /// Squared records the whole corpus realizes, at every budget. `term_slots`
    /// deduplicates structurally, so the count does not depend on the budget.
    const STABLE_ORDER_SQUARED_RECORDS: usize = 804;
    /// Moves this path emits. ZERO: placement's offline two-pass never needs the
    /// event-scan repair. Task 8 re-measured the same zero over all fifteen budgets
    /// on the production path (`in_scope::REALIZED_MOVES`).
    const STABLE_ORDER_MOVES: usize = 0;

    for (cells, words, bytes) in STABLE_ORDER_PER_BUDGET_MAX {
        let worst = realized.iter().find(|r| r.cells == cells).expect("a row per budget");
        assert_eq!(
            (worst.tag.as_str(), worst.words, worst.bytes),
            (STABLE_ORDER_WORST, words, bytes),
            "c{cells} maximum on the stable_normalized_order path moved"
        );
    }
    assert_eq!(
        worst.bytes, STABLE_ORDER_MAX_BYTES,
        "the maximum over the three sampled budgets on the stable_normalized_order path moved"
    );
    assert_eq!(worst.tag, STABLE_ORDER_WORST);
    assert_eq!(worst.cells, 16);
    assert_eq!(total_moves, STABLE_ORDER_MOVES, "placement started emitting moves");
    for cells in BUDGETS {
        let squared: usize =
            realized.iter().filter(|r| r.cells == cells).map(|r| r.squared).sum();
        assert_eq!(squared, STABLE_ORDER_SQUARED_RECORDS, "c{cells} squared-record count moved");
    }
    assert_eq!(total_squared, STABLE_ORDER_SQUARED_RECORDS);

    // This path is a LOWER witness for the production maximum, never an upper one:
    // `select_paged_order` is larger at every overlapping budget, so a pin here can
    // only ever be at or below Task 8's number. Const-vs-const, so it is checked
    // when the file compiles rather than as a runtime assertion that cannot fail —
    // but stated, because it is what keeps the two suites' claims ordered.
    const _: () = assert!(STABLE_ORDER_MAX_BYTES < in_scope::MAX_REALIZED_PROGRAM_BYTES);
    /// The program array Task 9 embeds leaves over half the by-value cap for its
    /// own metadata.
    const _: () = assert!(
        in_scope::DESCRIPTOR_PROGRAM_BYTES * 2
            < gkr_eval_isa::bwd::coeff::limits::KERNEL_ARGUMENT_CEILING_BYTES
    );

    // ...and the measured maximum still sits inside every bound it must.
    assert!(worst.bytes <= in_scope::MAX_UPPER_BOUND_PROGRAM_BYTES);
    assert!(worst.bytes > in_scope::MAX_LOWER_BOUND_PROGRAM_BYTES, "a lower bound must be lower");
}

// ── Synthetic coverage the corpus cannot reach ───────────────────────────────

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

/// Two `C0Linear` terms over ONE source, with distinct coefficients — so a program
/// may legally fill the value once, relocate it, and read it back.
fn two_reads_of_one_source(field: FieldKind) -> (CoeffLayer, Vec<SourcePrice>, EncodedProgram) {
    let regime = if field == FieldKind::Base { BwdRegime::R0 } else { BwdRegime::Ext };
    let category =
        if field == FieldKind::Base { TermCategory::C0LinearBf } else { TermCategory::C0LinearE4 };
    let sources = vec![read_source(0, field)];
    let prices = sources.iter().map(|s| price_of(s.field)).collect();
    let layer = CoeffLayer {
        regime,
        c_init: None,
        coefficients: Vec::new(),
        sources,
        terms: vec![
            CoeffTerm::C0Linear {
                id: TermId(0),
                coefficient: CoefficientRecipeId::ONE,
                value: ProjectionId::endpoint0(SourceId(0)),
                field,
            },
            CoeffTerm::C0Linear {
                id: TermId(1),
                coefficient: CoefficientRecipeId::NEG_ONE,
                value: ProjectionId::endpoint0(SourceId(0)),
                field,
            },
        ],
    };
    // Fill lane 0, relocate it to lane 8, read it back: the two terms' values are
    // the same projection, so the semantic sum is `(+1 - 1) * e0` either way.
    let width = ValueWidth::of(field);
    let move_category =
        if width == ValueWidth::Bf { TermCategory::MoveBf } else { TermCategory::MoveE4 };
    let coord = SourceCoord { window: 0, column: 0, first_access: true };
    let instrs = vec![
        DecodedInstr::Term {
            category,
            coefficient: CoefficientRecipeId::ONE,
            uses: vec![DecodedUse::Fill { coord, dst_lane: 0 }],
        },
        DecodedInstr::Move { category: move_category, from_lane: 0, to_lane: 8 },
        DecodedInstr::Term {
            category,
            coefficient: CoefficientRecipeId::NEG_ONE,
            uses: vec![DecodedUse::Cell(DecodedCell::Single { lane: 8 })],
        },
    ];
    let budget = CellBudget::new(4).unwrap();
    let words = encode_instrs(regime, budget, &instrs).expect("encode");
    (layer, prices, EncodedProgram { regime, budget, c_init: None, words })
}

/// The bound source table `two_reads_of_one_source` addresses.
fn one_source_binding(layer: &CoeffLayer, prices: &[SourcePrice]) -> CoeffSourceBinding {
    let order = stable_normalized_order(layer);
    let request = PagingRequest {
        budget: CellBudget::new(4).unwrap(),
        target_depth: default_target_depth(layer.regime),
    };
    let plan = page_projections(layer, prices, request, &order).expect("pager");
    let placement = place_paging_plan(layer, prices, &plan).expect("placement");
    bind_coeff_sources(layer, &Default::default(), &placement).expect("binding")
}

#[test]
fn encoded_moves_relocate_a_value_without_changing_the_result() {
    for field in [FieldKind::Base, FieldKind::Ext] {
        let (layer, prices, program) = two_reads_of_one_source(field);
        let binding = one_source_binding(&layer, &prices);
        assert_eq!(program.bytes(), 4 + 2 + 6 + 4, "fill term + move + resident term");
        let resolver = Pseudo { layer: &layer, seed: 0x11 };
        for row in ROWS {
            let semantic = interpret_coeff_layer(&layer, row, &resolver).expect("semantic");
            let encoded =
                interpret_encoded_program(&program, &binding, row, &resolver).expect("encoded");
            assert_eq!(encoded, semantic, "{field:?} row {row}");
        }
    }
}

#[test]
fn a_resident_read_of_a_dead_lane_is_rejected() {
    let (layer, prices, program) = two_reads_of_one_source(FieldKind::Base);
    let binding = one_source_binding(&layer, &prices);
    let resolver = Pseudo { layer: &layer, seed: 0x22 };
    // Drop the move: lane 8 is then never written.
    let words = {
        let mut instrs = gkr_eval_isa::bwd::coeff::encode::decode_program(&program, &binding)
            .expect("decode");
        instrs.remove(1);
        encode_instrs(program.regime, program.budget, &instrs).expect("re-encode")
    };
    let broken = EncodedProgram { words, ..program };
    assert_eq!(
        interpret_encoded_program(&broken, &binding, 0, &resolver).expect_err("dead lane"),
        CoeffCodecError::CellNotResident { lane: 8 }
    );
}

#[test]
fn a_resident_read_at_the_wrong_width_is_rejected() {
    // A BF fill at lane 0 followed by an E4 resident read of lane 0: legal words,
    // impossible cell file. The widths come from the OPCODES, which is exactly the
    // rule that makes this detectable.
    let sources = vec![read_source(0, FieldKind::Base), read_source(1, FieldKind::Ext)];
    let prices: Vec<SourcePrice> = sources.iter().map(|s| price_of(s.field)).collect();
    let layer = CoeffLayer {
        regime: BwdRegime::R0,
        c_init: None,
        coefficients: Vec::new(),
        sources,
        terms: vec![
            CoeffTerm::C0Linear {
                id: TermId(0),
                coefficient: CoefficientRecipeId::ONE,
                value: ProjectionId::endpoint0(SourceId(0)),
                field: FieldKind::Base,
            },
            CoeffTerm::C0Linear {
                id: TermId(1),
                coefficient: CoefficientRecipeId::ONE,
                value: ProjectionId::endpoint0(SourceId(1)),
                field: FieldKind::Ext,
            },
        ],
    };
    let binding = one_source_binding(&layer, &prices);
    let coord = SourceCoord { window: 0, column: 0, first_access: true };
    let instrs = vec![
        DecodedInstr::Term {
            category: TermCategory::C0LinearBf,
            coefficient: CoefficientRecipeId::ONE,
            uses: vec![DecodedUse::Fill { coord, dst_lane: 0 }],
        },
        DecodedInstr::Term {
            category: TermCategory::C0LinearE4,
            coefficient: CoefficientRecipeId::ONE,
            uses: vec![DecodedUse::Cell(DecodedCell::Single { lane: 0 })],
        },
    ];
    let budget = CellBudget::new(4).unwrap();
    let words = encode_instrs(BwdRegime::R0, budget, &instrs).expect("encode");
    let program = EncodedProgram { regime: BwdRegime::R0, budget, c_init: None, words };
    let resolver = Pseudo { layer: &layer, seed: 0x33 };
    assert_eq!(
        interpret_encoded_program(&program, &binding, 0, &resolver).expect_err("width"),
        CoeffCodecError::CellWidthMismatch { lane: 0, expected: ValueWidth::E4 }
    );
}

#[test]
fn a_plan_whose_resident_endpoint_holds_another_value_is_rejected() {
    // Lane 0 is filled with `Endpoint0(s0)`, then a native dual factor over `s1`
    // claims lane 0 holds ITS `Endpoint0`. §12.2 says a `Cell` use reads the
    // intended live projection; the encoded interpreter proves it instead of
    // trusting it.
    let sources = vec![read_source(0, FieldKind::Ext), read_source(1, FieldKind::Ext)];
    let prices: Vec<SourcePrice> = sources.iter().map(|s| price_of(s.field)).collect();
    let layer = CoeffLayer {
        regime: BwdRegime::Ext,
        c_init: None,
        coefficients: Vec::new(),
        sources,
        terms: vec![
            CoeffTerm::C0Linear {
                id: TermId(0),
                coefficient: CoefficientRecipeId::ONE,
                value: ProjectionId::endpoint0(SourceId(0)),
                field: FieldKind::Ext,
            },
            CoeffTerm::DualProduct {
                id: TermId(1),
                coefficient: CoefficientRecipeId::ONE,
                lhs: SourceId(0),
                rhs: SourceId(1),
            },
        ],
    };
    let binding = one_source_binding(&layer, &prices);
    let s0 = SourceCoord { window: 0, column: 0, first_access: true };
    let s1 = SourceCoord { window: 0, column: 1, first_access: true };
    let instrs = vec![
        DecodedInstr::Term {
            category: TermCategory::C0LinearE4,
            coefficient: CoefficientRecipeId::ONE,
            uses: vec![DecodedUse::Fill { coord: s0, dst_lane: 0 }],
        },
        DecodedInstr::Term {
            category: TermCategory::DualProductE4,
            coefficient: CoefficientRecipeId::ONE,
            uses: vec![
                DecodedUse::Direct { coord: s0 },
                DecodedUse::Planned {
                    coord: s1,
                    endpoint0: PlanAction::UseResident { lane: 0 },
                    delta: PlanAction::Direct,
                },
            ],
        },
    ];
    let budget = CellBudget::new(4).unwrap();
    let words = encode_instrs(BwdRegime::Ext, budget, &instrs).expect("encode");
    let program = EncodedProgram { regime: BwdRegime::Ext, budget, c_init: None, words };
    let resolver = Pseudo { layer: &layer, seed: 0x44 };
    assert_eq!(
        interpret_encoded_program(&program, &binding, 0, &resolver).expect_err("wrong resident"),
        CoeffCodecError::ResidentValueMismatch { lane: 0 }
    );
}

/// `c_init` is descriptor metadata (§9.3), not a stream record — but both
/// interpreters must start `acc_c0` at the same place.
#[test]
fn c_init_starts_both_interpreters_at_the_same_value() {
    let (mut layer, prices, program) = two_reads_of_one_source(FieldKind::Base);
    let binding = one_source_binding(&layer, &prices);
    layer.coefficients = vec![gkr_eval_isa::bwd::coeff::NormalizedCoefficientRecipe::scalar(bf(9))];
    layer.c_init = Some(CoefficientRecipeId(2));
    let program = EncodedProgram { c_init: layer.c_init, ..program };
    let resolver = Pseudo { layer: &layer, seed: 0x55 };
    let semantic = interpret_coeff_layer(&layer, 3, &resolver).expect("semantic");
    let encoded = interpret_encoded_program(&program, &binding, 3, &resolver).expect("encoded");
    assert_eq!(encoded, semantic);
    assert_ne!(semantic.0, Ext::ZERO, "the fixture must make c_init observable");
}

/// A squared term must resolve its source ONCE, not twice — the wire says so, and
/// re-executing the repeated record would be wrong for a plan that overwrites the
/// lane it read.
#[test]
fn a_squared_term_resolves_its_source_exactly_once() {
    use std::cell::RefCell;

    struct Counting<'a> {
        inner: Pseudo<'a>,
        calls: RefCell<BTreeMap<u32, usize>>,
    }
    impl CoeffResolver for Counting<'_> {
        fn coefficient(&self, id: CoefficientRecipeId) -> Ext {
            self.inner.coefficient(id)
        }
        fn source_pair(&self, id: SourceId, row: usize) -> (Ext, Ext) {
            *self.calls.borrow_mut().entry(id.0).or_default() += 1;
            self.inner.source_pair(id, row)
        }
    }

    let sources = vec![read_source(0, FieldKind::Base)];
    let prices: Vec<SourcePrice> = sources.iter().map(|s| price_of(s.field)).collect();
    let layer = CoeffLayer {
        regime: BwdRegime::R0,
        c_init: None,
        coefficients: Vec::new(),
        sources,
        terms: vec![CoeffTerm::C2Product {
            id: TermId(0),
            coefficient: CoefficientRecipeId::ONE,
            lhs: ProjectionId::delta(SourceId(0)),
            rhs: ProjectionId::delta(SourceId(0)),
            lhs_field: FieldKind::Base,
            rhs_field: FieldKind::Base,
        }],
    };
    let order = stable_normalized_order(&layer);
    let request = PagingRequest {
        budget: CellBudget::new(4).unwrap(),
        target_depth: default_target_depth(BwdRegime::R0),
    };
    let plan = page_projections(&layer, &prices, request, &order).expect("pager");
    let placement = place_paging_plan(&layer, &prices, &plan).expect("placement");
    let binding = bind_coeff_sources(&layer, &Default::default(), &placement).expect("binding");
    let program = encode_program(&layer, &placement, &binding).expect("encode");

    let resolver = Counting {
        inner: Pseudo { layer: &layer, seed: 0x66 },
        calls: RefCell::new(BTreeMap::new()),
    };
    let encoded = interpret_encoded_program(&program, &binding, 5, &resolver).expect("encoded");
    assert_eq!(resolver.calls.borrow().get(&0), Some(&1), "one physical resolution");

    // ...and the value is still the square. The SEMANTIC interpreter resolves twice
    // (it has no notion of a physical resolution), so only the value is compared.
    let plain = Pseudo { layer: &layer, seed: 0x66 };
    let semantic = interpret_coeff_layer(&layer, 5, &plain).expect("semantic");
    assert_eq!(encoded, semantic);
    assert_ne!(semantic.1, Ext::ZERO, "the fixture must make the square observable");
}
