//! Task-7 gates: the canonical u16 wire format, its validator, and the
//! disassembler (design §9, §12.1).
//!
//! This file is the ABI's test surface. Three claims are gated:
//!
//!   1. **The bit layouts and numeric codes are what §9 says**, pinned as exact
//!      u16 values so Task 9's CUDA static assertions have a Rust-side twin that
//!      fails loudly on a renumber.
//!   2. **Canonical means exactly one encoding per semantic record.** Every
//!      accepted program re-encodes byte-for-byte, checked over an enumeration of
//!      every legal form, over seeded random programs, and — exhaustively — over
//!      every single-bit mutation of a small program.
//!   3. **Every rejection has its own typed variant**, each with its own test. A
//!      validator whose failures are indistinguishable is not a validator.
//!
//! Semantic equivalence of the encoded and the semantic interpreter lives in
//! `bwd_coeff_encoded_parity.rs`; nothing here builds a launch descriptor.

use std::collections::BTreeSet;

use cs::gkr_compiler::dag_ir::{Bf, BwdRegime, FieldKind, ReadPlace, VirtualSetupKind};
use field::PrimeField;
use gkr_eval_isa::bwd::coeff::bind::{
    BoundColumn, BoundSourceWindow, CoeffSourceBinding, bind_coeff_sources,
};
use gkr_eval_isa::bwd::coeff::encode::{
    ACTION_DIRECT, ACTION_FILL, ACTION_INVALID, ACTION_USE_RESIDENT, CELL_DELTA_LANE_SHIFT,
    CELL_ENDPOINT0_LANE_SHIFT, CoeffCodecError, DecodedCell, DecodedInstr, DecodedUse,
    EncodedProgram, HEADER_COEFFICIENT_MASK, HEADER_COEFFICIENT_SHIFT, HEADER_OPCODE_MASK,
    HEADER_OPCODE_SHIFT, INPUT_COLUMN_MASK, INPUT_COLUMN_SHIFT, INPUT_FIRST_ACCESS_SHIFT,
    INPUT_MODE_MASK, INPUT_MODE_SHIFT, INPUT_WINDOW_MASK, INPUT_WINDOW_SHIFT, LANE_BITS, LANE_MASK,
    LANE_WORD_SHIFT, MODE_CELL, MODE_DIRECT_SOURCE, MODE_FILL_SOURCE, MODE_PLANNED_SOURCE,
    OperandRole, PLAN_ACTION_MASK, PLAN_DELTA_ACTION_SHIFT, PLAN_DELTA_LANE_SHIFT,
    PLAN_ENDPOINT0_ACTION_SHIFT, PLAN_ENDPOINT0_LANE_SHIFT, ShortestForm, SourceCoord,
    category_arity, category_of, category_role, certify_encoding, decode_program, disassemble,
    encode_instrs, encode_program, is_move, move_width, opcode_of, opcode_table, operand_width,
    program_records, term_category, validate_program,
};
use gkr_eval_isa::bwd::coeff::limits::{
    CONTINUATION_OPCODE_TABLE, HEADER_COEFFICIENT_BITS, HEADER_OPCODE_BITS,
    KERNEL_ARGUMENT_CEILING_BYTES, MAX_COEFFICIENT_ENCODINGS, MAX_SOURCE_WINDOWS,
    R0_OPCODE_TABLE, SOURCE_WINDOW_COLUMNS, TermCategory,
};
use gkr_eval_isa::bwd::coeff::place::{
    CellRead, PlanAction, ScheduledInstr, ValueUse, place_paging_plan,
};
use gkr_eval_isa::bwd::coeff::schedule::{
    CellBudget, OpCounts, PagingRequest, SourcePrice, ValueWidth, default_target_depth,
    page_projections, stable_normalized_order,
};
use gkr_eval_isa::bwd::coeff::stats::WindowFamily;
use gkr_eval_isa::bwd::coeff::{
    CoeffLayer, CoeffSource, CoeffTerm, CoefficientRecipeId, NormalizedCoefficientRecipe,
    ProjectionId, SourceId, TermId,
};
use gkr_eval_isa::bwd::source::OriginLeaf;

// ── Fixtures ─────────────────────────────────────────────────────────────────

/// A dense one-window binding: `SourceId(c)` sits at column `c` of window 0.
fn dense_binding(columns: usize) -> CoeffSourceBinding {
    windowed_binding(&[(WindowFamily::BaseLayerWitness, 0, (0..columns).collect())])
}

/// A binding built from `(family, first_column, absolute columns)` triples, with
/// `SourceId` assigned in the order the columns are listed.
fn windowed_binding(spec: &[(WindowFamily, usize, Vec<usize>)]) -> CoeffSourceBinding {
    let mut next = 0u32;
    let windows = spec
        .iter()
        .map(|(family, first_column, columns)| BoundSourceWindow {
            family: *family,
            first_column: *first_column,
            columns: columns
                .iter()
                .map(|&column| {
                    let source = SourceId(next);
                    next += 1;
                    BoundColumn { column, source }
                })
                .collect(),
        })
        .collect();
    CoeffSourceBinding { target_depth: 0, materialize: false, windows, uses: Vec::new() }
}

fn coord(window: u8, column: u8, first_access: bool) -> SourceCoord {
    SourceCoord { window, column, first_access }
}

/// Encode `instrs` and wrap them, panicking on an encoder rejection.
fn encoded(regime: BwdRegime, cells: u8, instrs: &[DecodedInstr]) -> EncodedProgram {
    let budget = CellBudget::new(cells).expect("c2..c16");
    let words = encode_instrs(regime, budget, instrs)
        .unwrap_or_else(|e| panic!("encoding {instrs:?}: {e:?}"));
    EncodedProgram { regime, budget, c_init: None, words }
}

fn term(category: TermCategory, k: CoefficientRecipeId, uses: Vec<DecodedUse>) -> DecodedInstr {
    DecodedInstr::Term { category, coefficient: k, uses }
}

const ONE: CoefficientRecipeId = CoefficientRecipeId::ONE;

/// A non-literal recipe bank of `n` distinct scalars — none zero, none `±1`.
fn bank(n: usize) -> Vec<NormalizedCoefficientRecipe> {
    (0..n)
        .map(|i| NormalizedCoefficientRecipe::scalar(Bf::from_u32_with_reduction(7 + i as u32)))
        .collect()
}

// ── 1. The frozen bit geometry ───────────────────────────────────────────────

#[test]
fn header_layout_is_frozen() {
    assert_eq!(HEADER_COEFFICIENT_SHIFT, 0);
    assert_eq!(HEADER_COEFFICIENT_MASK, 0x1fff);
    assert_eq!(HEADER_OPCODE_SHIFT, 13);
    assert_eq!(HEADER_OPCODE_MASK, 0x7);
    assert_eq!(HEADER_COEFFICIENT_BITS, 13);
    assert_eq!(HEADER_OPCODE_BITS, 3);

    // The extremes, as literal u16s: coefficient 8191 with the highest live R0
    // opcode, and coefficient 0 with opcode 0.
    let binding = dense_binding(4);
    let top = encoded(
        BwdRegime::R0,
        16,
        &[term(
            TermCategory::C2ProductE4E4,
            CoefficientRecipeId(0x1fff),
            vec![
                DecodedUse::Direct { coord: coord(0, 0, false) },
                DecodedUse::Direct { coord: coord(0, 1, false) },
            ],
        )],
    );
    assert_eq!(top.words[0], 0x9fff, "opcode 4 | coefficient 8191");
    let low = encoded(
        BwdRegime::R0,
        16,
        &[term(
            TermCategory::C0LinearBf,
            CoefficientRecipeId(0),
            vec![DecodedUse::Direct { coord: coord(0, 0, false) }],
        )],
    );
    assert_eq!(low.words[0], 0x0000, "opcode 0 | coefficient 0");
    decode_program(&top, &binding).expect("decodes");
    decode_program(&low, &binding).expect("decodes");
}

#[test]
fn input_word_layout_is_frozen() {
    assert_eq!(INPUT_MODE_SHIFT, 0);
    assert_eq!(INPUT_MODE_MASK, 0x3);
    assert_eq!(INPUT_FIRST_ACCESS_SHIFT, 2);
    assert_eq!(INPUT_WINDOW_SHIFT, 3);
    assert_eq!(INPUT_WINDOW_MASK, 0x3f);
    assert_eq!(INPUT_COLUMN_SHIFT, 9);
    assert_eq!(INPUT_COLUMN_MASK, 0x7f);
    assert_eq!(MAX_SOURCE_WINDOWS, 64);
    assert_eq!(SOURCE_WINDOW_COLUMNS, 128);

    // window 63, column 127, first access, DirectSource:
    //   column 127 << 9 | window 63 << 3 | 1 << 2 | 0 = 0xfffc
    let program = encoded(
        BwdRegime::R0,
        16,
        &[term(
            TermCategory::C0LinearBf,
            ONE,
            vec![DecodedUse::Direct { coord: coord(63, 127, true) }],
        )],
    );
    assert_eq!(program.words[1], 0xfffc);
    // ...and column 0, window 0, later access is the mode alone.
    let program = encoded(
        BwdRegime::R0,
        16,
        &[term(
            TermCategory::C0LinearBf,
            ONE,
            vec![DecodedUse::Direct { coord: coord(0, 0, false) }],
        )],
    );
    assert_eq!(program.words[1], 0x0000);
}

#[test]
fn mode_and_action_codes_are_frozen() {
    assert_eq!((MODE_DIRECT_SOURCE, MODE_CELL, MODE_FILL_SOURCE, MODE_PLANNED_SOURCE), (0, 1, 2, 3));
    assert_eq!((ACTION_DIRECT, ACTION_USE_RESIDENT, ACTION_FILL, ACTION_INVALID), (0, 1, 2, 3));
    assert_eq!(PLAN_ACTION_MASK, 0x3);
    assert_eq!(LANE_BITS, 6);
    assert_eq!(LANE_MASK, 0x3f);
    assert_eq!(LANE_WORD_SHIFT, 0);
}

#[test]
fn cell_and_plan_words_share_one_lane_geometry() {
    assert_eq!(CELL_ENDPOINT0_LANE_SHIFT, 2);
    assert_eq!(CELL_DELTA_LANE_SHIFT, 10);
    assert_eq!(PLAN_ENDPOINT0_ACTION_SHIFT, 0);
    assert_eq!(PLAN_ENDPOINT0_LANE_SHIFT, 2);
    assert_eq!(PLAN_DELTA_ACTION_SHIFT, 8);
    assert_eq!(PLAN_DELTA_LANE_SHIFT, 10);
    assert_eq!(CELL_ENDPOINT0_LANE_SHIFT, PLAN_ENDPOINT0_LANE_SHIFT);
    assert_eq!(CELL_DELTA_LANE_SHIFT, PLAN_DELTA_LANE_SHIFT);

    // Cell, single form: lane 37 at bits 2..7, everything above zero.
    let single = encoded(
        BwdRegime::R0,
        16,
        &[term(
            TermCategory::C0LinearBf,
            ONE,
            vec![DecodedUse::Cell(DecodedCell::Single { lane: 37 })],
        )],
    );
    assert_eq!(single.words[1], 37 << 2 | MODE_CELL);
    // Cell, packed pair form: e0 lane 4 at bits 2..7, delta lane 60 at 10..15.
    let pair = encoded(
        BwdRegime::Ext,
        16,
        &[term(
            TermCategory::DualProductE4,
            ONE,
            vec![
                DecodedUse::Cell(DecodedCell::Pair { endpoint0_lane: 4, delta_lane: 60 }),
                DecodedUse::Cell(DecodedCell::Pair { endpoint0_lane: 8, delta_lane: 12 }),
            ],
        )],
    );
    assert_eq!(pair.words[1], 60 << 10 | 4 << 2 | MODE_CELL);
    // Plan word: {UseResident l8, Fill l40}.
    let planned = encoded(
        BwdRegime::Ext,
        16,
        &[term(
            TermCategory::DualProductE4,
            ONE,
            vec![
                DecodedUse::Planned {
                    coord: coord(0, 0, false),
                    endpoint0: PlanAction::UseResident { lane: 8 },
                    delta: PlanAction::Fill { lane: 40 },
                },
                DecodedUse::Direct { coord: coord(0, 4, false) },
            ],
        )],
    );
    assert_eq!(planned.words[2], 40 << 10 | ACTION_FILL << 8 | 8 << 2 | ACTION_USE_RESIDENT);
}

#[test]
fn opcode_tables_are_the_frozen_tables() {
    assert_eq!(opcode_table(BwdRegime::R0), R0_OPCODE_TABLE);
    assert_eq!(opcode_table(BwdRegime::Ext), CONTINUATION_OPCODE_TABLE);
    for regime in [BwdRegime::R0, BwdRegime::Ext] {
        for &(opcode, category) in opcode_table(regime) {
            assert_eq!(category_of(regime, opcode), Some(category));
            assert_eq!(opcode_of(regime, category), Some(opcode));
        }
        let live: BTreeSet<u16> = opcode_table(regime).iter().map(|(o, _)| *o).collect();
        for opcode in 0u16..8 {
            if !live.contains(&opcode) {
                assert_eq!(category_of(regime, opcode), None, "{regime:?} opcode {opcode}");
            }
        }
    }
    // The two dead-in-this-regime categories, spelled out.
    assert_eq!(opcode_of(BwdRegime::R0, TermCategory::DualProductE4), None);
    assert_eq!(opcode_of(BwdRegime::Ext, TermCategory::MoveBf), None);
}

/// The rule that makes a RESIDENT operand decodable at all: no window is
/// available for a `Cell` read, so the opcode alone carries the width.
#[test]
fn operand_width_is_a_function_of_opcode_and_position() {
    use TermCategory::*;
    use ValueWidth::{Bf as B, E4};
    let expected: &[(TermCategory, &[ValueWidth], Option<OperandRole>)] = &[
        (C0LinearBf, &[B], Some(OperandRole::Endpoint0)),
        (C0LinearE4, &[E4], Some(OperandRole::Endpoint0)),
        (C2ProductBfBf, &[B, B], Some(OperandRole::Delta)),
        (C2ProductBfE4, &[B, E4], Some(OperandRole::Delta)),
        (C2ProductE4E4, &[E4, E4], Some(OperandRole::Delta)),
        (DualProductE4, &[E4, E4], Some(OperandRole::Pair)),
        (MoveBf, &[], None),
        (MoveE4, &[], None),
    ];
    for &(category, widths, role) in expected {
        assert_eq!(category_arity(category), widths.len(), "{category:?} arity");
        assert_eq!(category_role(category), role, "{category:?} role");
        for (position, width) in widths.iter().enumerate() {
            assert_eq!(operand_width(category, position), Some(*width), "{category:?}[{position}]");
        }
        assert_eq!(operand_width(category, widths.len()), None, "{category:?} past the last");
        assert_eq!(is_move(category), role.is_none());
    }
    assert_eq!(move_width(MoveBf), Some(B));
    assert_eq!(move_width(MoveE4), Some(E4));
    assert_eq!(move_width(C0LinearBf), None);
}

/// §9.6's size table, as encoded bytes.
#[test]
fn common_encoded_sizes_match_the_design_table() {
    let unary = encoded(
        BwdRegime::R0,
        16,
        &[term(
            TermCategory::C0LinearBf,
            ONE,
            vec![DecodedUse::Direct { coord: coord(0, 0, false) }],
        )],
    );
    assert_eq!(unary.bytes(), 4, "unary direct term");

    let binary = encoded(
        BwdRegime::Ext,
        16,
        &[term(
            TermCategory::DualProductE4,
            ONE,
            vec![
                DecodedUse::Direct { coord: coord(0, 0, false) },
                DecodedUse::Direct { coord: coord(0, 4, false) },
            ],
        )],
    );
    assert_eq!(binary.bytes(), 6, "binary/direct dual term");

    let filled = encoded(
        BwdRegime::R0,
        16,
        &[term(
            TermCategory::C0LinearBf,
            ONE,
            vec![DecodedUse::Fill { coord: coord(0, 0, false), dst_lane: 3 }],
        )],
    );
    assert_eq!(filled.bytes(), unary.bytes() + 2, "ordinary fill extension");

    for category in [TermCategory::MoveBf, TermCategory::MoveE4] {
        let width = move_width(category).unwrap();
        let lane = if width == ValueWidth::E4 { 4 } else { 3 };
        let mv = encoded(
            BwdRegime::R0,
            16,
            &[DecodedInstr::Move { category, from_lane: 0, to_lane: lane }],
        );
        assert_eq!(mv.bytes(), 6, "{category:?}");
        assert_eq!(mv.words[0], opcode_of(BwdRegime::R0, category).unwrap() << 13);
    }
}

// ── 2. Canonical round-trip ──────────────────────────────────────────────────

/// Every legal `(category, form)` combination the format admits.
fn every_legal_form() -> Vec<(BwdRegime, DecodedInstr)> {
    let plans_for = |role: OperandRole| -> Vec<(PlanAction, PlanAction)> {
        let acts = |lane: u16| {
            [PlanAction::Direct, PlanAction::UseResident { lane }, PlanAction::Fill { lane }]
        };
        let mut out = Vec::new();
        if role == OperandRole::Endpoint0 {
            return out; // §8: no plan on an `Endpoint0`-only use.
        }
        for e0 in acts(4) {
            for d in acts(8) {
                let resident =
                    |a: PlanAction| matches!(a, PlanAction::UseResident { .. });
                let fill = |a: PlanAction| matches!(a, PlanAction::Fill { .. });
                if e0 == PlanAction::Direct && d == PlanAction::Direct {
                    continue; // -> DirectSource
                }
                if role == OperandRole::Pair && resident(e0) && resident(d) {
                    continue; // -> packed Cell
                }
                if role == OperandRole::Delta {
                    if e0 == PlanAction::Direct && fill(d) {
                        continue; // -> FillSource
                    }
                    if resident(d) && !fill(e0) {
                        continue; // -> Cell, single form
                    }
                }
                out.push((e0, d));
            }
        }
        out
    };

    let mut out = Vec::new();
    for regime in [BwdRegime::R0, BwdRegime::Ext] {
        for &(_, category) in opcode_table(regime) {
            if is_move(category) {
                let width = move_width(category).unwrap();
                let step = width.lanes() as u16;
                out.push((
                    regime,
                    DecodedInstr::Move { category, from_lane: 0, to_lane: step * 3 },
                ));
                continue;
            }
            let role = category_role(category).unwrap();
            let arity = category_arity(category);
            let mut forms: Vec<DecodedUse> =
                vec![DecodedUse::Direct { coord: coord(1, 5, true) }];
            match role {
                OperandRole::Pair => forms.push(DecodedUse::Cell(DecodedCell::Pair {
                    endpoint0_lane: 4,
                    delta_lane: 8,
                })),
                _ => {
                    forms.push(DecodedUse::Cell(DecodedCell::Single { lane: 4 }));
                    forms.push(DecodedUse::Fill { coord: coord(0, 2, false), dst_lane: 8 });
                }
            }
            for (e0, d) in plans_for(role) {
                forms.push(DecodedUse::Planned { coord: coord(0, 3, false), endpoint0: e0, delta: d });
            }
            // §9.1's squared form stands ONE record in for every position, so it
            // is only legal where every position has the same width. A mixed
            // category squared would have to be resolved at BF and consumed as an
            // E4; `encode_instrs` rejects it (`MixedProductNotMixed`) and
            // `rejects_a_squared_mixed_width_product` pins that. This enumeration
            // used to emit it, which made the shape look legal.
            let squarable = (1..arity)
                .all(|position| operand_width(category, position) == operand_width(category, 0));
            for form in forms {
                // One record per form, both as a lone operand and (for a binary
                // opcode) paired with a plain direct operand and — where the widths
                // permit — as a squared term.
                let mut uses = vec![form];
                if arity == 2 {
                    if squarable {
                        out.push((regime, term(category, CoefficientRecipeId(2), uses.clone())));
                    }
                    uses.push(DecodedUse::Direct { coord: coord(0, 12, false) });
                }
                out.push((regime, term(category, CoefficientRecipeId(3), uses)));
            }
        }
    }
    out
}

#[test]
fn every_legal_form_round_trips_byte_for_byte() {
    let binding = windowed_binding(&[
        (WindowFamily::BaseLayerWitness, 0, (0..64).collect()),
        (WindowFamily::Setup, 0, (0..64).collect()),
    ]);
    let bank = bank(8);
    let mut seen_forms = 0usize;
    for (regime, instr) in every_legal_form() {
        // Every operand of a legal record is E4-aligned at c16 by construction,
        // so both regimes can carry it.
        let program = encoded(regime, 16, std::slice::from_ref(&instr));
        let decoded = validate_program(&program, &binding, &bank)
            .unwrap_or_else(|e| panic!("{instr:?} rejected: {e:?}"));
        assert_eq!(decoded, vec![instr.clone()], "record did not survive the round trip");
        let again = encode_instrs(regime, program.budget, &decoded).expect("re-encode");
        assert_eq!(again, program.words, "{instr:?} did not re-encode byte-for-byte");
        assert_eq!(program.words.len(), instr.words(), "{instr:?} word count");
        seen_forms += 1;
    }
    println!("legal forms round-tripped: {seen_forms}");
    assert!(seen_forms >= 60, "the enumeration went stale: only {seen_forms} forms");
}

// ── Seeded randomized round-trip ─────────────────────────────────────────────

struct SplitMix64(u64);

impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn flip(&mut self) -> bool {
        self.next() & 1 == 1
    }
}

fn random_lane(rng: &mut SplitMix64, lanes: u32, width: ValueWidth) -> u16 {
    let slots = lanes / width.lanes();
    (rng.below(u64::from(slots)) as u16) * width.lanes() as u16
}

fn random_coord(rng: &mut SplitMix64) -> SourceCoord {
    coord(0, rng.below(64) as u8, rng.flip())
}

fn random_action(rng: &mut SplitMix64, lanes: u32, width: ValueWidth) -> PlanAction {
    let lane = random_lane(rng, lanes, width);
    match rng.below(3) {
        0 => PlanAction::Direct,
        1 => PlanAction::UseResident { lane },
        _ => PlanAction::Fill { lane },
    }
}

fn random_use(
    rng: &mut SplitMix64,
    role: OperandRole,
    lanes: u32,
    width: ValueWidth,
) -> DecodedUse {
    loop {
        match rng.below(4) {
            0 => return DecodedUse::Direct { coord: random_coord(rng) },
            1 if role == OperandRole::Pair => {
                return DecodedUse::Cell(DecodedCell::Pair {
                    endpoint0_lane: random_lane(rng, lanes, width),
                    delta_lane: random_lane(rng, lanes, width),
                });
            }
            1 => {
                return DecodedUse::Cell(DecodedCell::Single {
                    lane: random_lane(rng, lanes, width),
                });
            }
            // A fill on a native dual factor has to go through a plan (§9.5).
            2 if role == OperandRole::Pair => continue,
            2 => {
                return DecodedUse::Fill {
                    coord: random_coord(rng),
                    dst_lane: random_lane(rng, lanes, width),
                };
            }
            // No plan on an `Endpoint0`-only use (§8).
            _ if role == OperandRole::Endpoint0 => continue,
            _ => {
                return DecodedUse::Planned {
                    coord: random_coord(rng),
                    endpoint0: random_action(rng, lanes, width),
                    delta: random_action(rng, lanes, width),
                };
            }
        }
    }
}

/// One random record for a random category of `regime` at `cells`. Structurally
/// in range by construction; the plan halves may still be non-canonical, which the
/// encoder is entitled to refuse.
fn random_instr(rng: &mut SplitMix64, regime: BwdRegime, cells: u8, bank: usize) -> DecodedInstr {
    let table = opcode_table(regime);
    let (_, category) = table[rng.below(table.len() as u64) as usize];
    let lanes = u32::from(cells) * 4;
    if is_move(category) {
        let width = move_width(category).unwrap();
        return DecodedInstr::Move {
            category,
            from_lane: random_lane(rng, lanes, width),
            to_lane: random_lane(rng, lanes, width),
        };
    }
    let role = category_role(category).unwrap();
    let arity = category_arity(category);
    let k = CoefficientRecipeId(rng.below((bank + 2) as u64) as u32);
    let squared = arity == 2 && rng.below(5) == 0;
    let count = if squared { 1 } else { arity };
    let mut uses = Vec::with_capacity(count);
    for position in 0..count {
        let width = operand_width(category, position).unwrap();
        uses.push(random_use(rng, role, lanes, width));
    }
    term(category, k, uses)
}

#[test]
fn randomized_valid_programs_round_trip() {
    const SEED: u64 = 0x7a5c_0de1_2026_0725;
    println!("randomized_valid_programs_round_trip seed = {SEED:#018x}");
    let mut rng = SplitMix64(SEED);
    let binding = dense_binding(64);
    let bank = bank(30);
    let mut accepted = 0usize;
    let mut rejected = 0usize;
    let mut squared = 0usize;
    for case in 0..4_000u32 {
        let regime = if rng.flip() { BwdRegime::R0 } else { BwdRegime::Ext };
        let cells = 2 + rng.below(15) as u8;
        let count = 1 + rng.below(6) as usize;
        let instrs: Vec<DecodedInstr> =
            (0..count).map(|_| random_instr(&mut rng, regime, cells, bank.len())).collect();
        let budget = CellBudget::new(cells).unwrap();
        let words = match encode_instrs(regime, budget, &instrs) {
            Ok(words) => words,
            Err(_) => {
                // The generator can propose a non-canonical plan; the encoder is
                // entitled to refuse it. Those cases are covered by the explicit
                // canonicality tests.
                rejected += 1;
                continue;
            }
        };
        let program = EncodedProgram { regime, budget, c_init: None, words };
        let decoded = validate_program(&program, &binding, &bank)
            .unwrap_or_else(|e| panic!("case {case} (seed {SEED:#018x}) rejected: {e:?}"));
        assert_eq!(decoded, instrs, "case {case} (seed {SEED:#018x}) decoded differently");
        let again = encode_instrs(regime, budget, &decoded).expect("re-encode");
        assert_eq!(again, program.words, "case {case} (seed {SEED:#018x}) is not canonical");
        squared += decoded.iter().filter(|i| i.is_squared()).count();
        accepted += 1;
    }
    println!("accepted {accepted}, generator-rejected {rejected}, squared records {squared}");
    assert!(accepted > 2_000, "the generator produced too few valid programs");
    assert!(squared > 100, "the generator never exercised the squared form");
}

/// Exhaustive single-bit mutation. Every mutation either changes nothing, is
/// rejected with a SPECIFIC variant, or is itself a canonical program — the
/// generic [`CoeffCodecError::NonCanonicalEncoding`] backstop must stay
/// unreachable, because every reserved bit has an explicit rule.
#[test]
fn every_single_bit_mutation_is_classified() {
    let binding = dense_binding(64);
    let bank = bank(4);
    let base = encoded(
        BwdRegime::Ext,
        16,
        &[
            term(
                TermCategory::DualProductE4,
                CoefficientRecipeId(2),
                vec![
                    DecodedUse::Planned {
                        coord: coord(0, 5, true),
                        endpoint0: PlanAction::Fill { lane: 4 },
                        delta: PlanAction::Fill { lane: 8 },
                    },
                    DecodedUse::Cell(DecodedCell::Pair { endpoint0_lane: 12, delta_lane: 16 }),
                ],
            ),
            DecodedInstr::Move { category: TermCategory::MoveE4, from_lane: 4, to_lane: 20 },
            term(
                TermCategory::C0LinearE4,
                ONE,
                vec![DecodedUse::Fill { coord: coord(0, 9, false), dst_lane: 24 }],
            ),
        ],
    );
    validate_program(&base, &binding, &bank).expect("the base program is valid");

    let mut rejected = 0usize;
    let mut accepted = 0usize;
    for index in 0..base.words.len() {
        for bit in 0..16 {
            let mut words = base.words.clone();
            words[index] ^= 1 << bit;
            let mutant = EncodedProgram { words, ..base.clone() };
            match validate_program(&mutant, &binding, &bank) {
                Ok(decoded) => {
                    let again =
                        encode_instrs(mutant.regime, mutant.budget, &decoded).expect("re-encode");
                    assert_eq!(
                        again, mutant.words,
                        "word {index} bit {bit} was accepted but is not canonical"
                    );
                    accepted += 1;
                }
                Err(CoeffCodecError::NonCanonicalEncoding { at }) => panic!(
                    "word {index} bit {bit} fell through to the generic backstop at {at}"
                ),
                Err(_) => rejected += 1,
            }
        }
    }
    println!("single-bit mutants: {accepted} canonical, {rejected} rejected");
    assert!(rejected > 0 && accepted > 0, "the mutation sweep is vacuous");
}

// ── 3. One test per typed rejection ──────────────────────────────────────────

/// A three-word valid R0 program: `C2ProductBF_BF` over two direct operands.
fn valid_r0() -> EncodedProgram {
    encoded(
        BwdRegime::R0,
        4,
        &[term(
            TermCategory::C2ProductBfBf,
            ONE,
            vec![
                DecodedUse::Direct { coord: coord(0, 0, true) },
                DecodedUse::Direct { coord: coord(0, 1, false) },
            ],
        )],
    )
}

fn reject(program: &EncodedProgram, binding: &CoeffSourceBinding) -> CoeffCodecError {
    validate_program(program, binding, &bank(8)).expect_err("expected a rejection")
}

#[test]
fn rejects_an_invalid_opcode() {
    let binding = dense_binding(8);
    let mut program = valid_r0();
    program.words[0] = 7 << 13; // R0 opcode 7 is deliberately dead.
    assert_eq!(
        reject(&program, &binding),
        CoeffCodecError::InvalidOpcode { at: 0, opcode: 7, regime: BwdRegime::R0 }
    );
    // ...and continuation opcodes 3..7, which the zero standalone-product census
    // deliberately leaves dead.
    for opcode in 3u16..8 {
        let mut program = valid_r0();
        program.regime = BwdRegime::Ext;
        program.words[0] = opcode << 13;
        assert_eq!(
            reject(&program, &binding),
            CoeffCodecError::InvalidOpcode { at: 0, opcode, regime: BwdRegime::Ext }
        );
    }
}

/// The squared discriminator must never be reachable from two DISTINCT slots.
#[test]
fn rejects_two_distinct_slots_that_encode_identically() {
    assert_eq!(
        encode_instrs(
            BwdRegime::R0,
            CellBudget::new(4).unwrap(),
            &[term(
                TermCategory::C2ProductBfBf,
                ONE,
                vec![
                    DecodedUse::Cell(DecodedCell::Single { lane: 3 }),
                    DecodedUse::Cell(DecodedCell::Single { lane: 3 }),
                ],
            )],
        )
        .expect_err("ambiguous repeat"),
        CoeffCodecError::AmbiguousRepeatedRecord { at: 2 }
    );
}

#[test]
fn rejects_a_truncated_record() {
    let binding = dense_binding(8);
    let mut program = valid_r0();
    program.words.pop();
    assert_eq!(reject(&program, &binding), CoeffCodecError::TruncatedRecord { at: 2 });
}

#[test]
fn rejects_a_missing_extension() {
    let binding = dense_binding(8);
    let program = encoded(
        BwdRegime::R0,
        4,
        &[term(
            TermCategory::C0LinearBf,
            ONE,
            vec![DecodedUse::Fill { coord: coord(0, 0, false), dst_lane: 3 }],
        )],
    );
    let mut truncated = program.clone();
    truncated.words.pop();
    assert_eq!(
        reject(&truncated, &binding),
        CoeffCodecError::MissingExtension { at: 2, mode: MODE_FILL_SOURCE }
    );
}

#[test]
fn rejects_trailing_words() {
    let (layer, prices) = squared_r0_layer();
    let (placement, binding) = page_place_bind(&layer, &prices, 16);
    let mut program = encode_program(&layer, &placement, &binding).expect("encode");
    certify_encoding(&layer, &placement, &binding, &program).expect("the encoding certifies");
    let consumed = program.words.len();
    // A whole extra, individually legal record.
    program.words.extend(encoded(
        BwdRegime::R0,
        16,
        &[term(TermCategory::C0LinearBf, ONE, vec![DecodedUse::Cell(DecodedCell::Single { lane: 0 })])],
    )
    .words);
    let words = program.words.len();
    assert_eq!(
        certify_encoding(&layer, &placement, &binding, &program).expect_err("trailing"),
        CoeffCodecError::TrailingWords { consumed, words }
    );
}

#[test]
fn rejects_a_move_header_with_coefficient_bits() {
    let binding = dense_binding(8);
    let program = encoded(
        BwdRegime::R0,
        4,
        &[DecodedInstr::Move { category: TermCategory::MoveBf, from_lane: 0, to_lane: 5 }],
    );
    let mut mutated = program.clone();
    mutated.words[0] |= 1;
    assert_eq!(
        reject(&mutated, &binding),
        CoeffCodecError::MoveCoefficientNotZero { at: 0, bits: 1 }
    );
}

#[test]
fn rejects_reserved_payload_bits() {
    let binding = dense_binding(8);
    // Cell, single form: bits 8..15 are required zero.
    let mut program = encoded(
        BwdRegime::R0,
        4,
        &[term(
            TermCategory::C0LinearBf,
            ONE,
            vec![DecodedUse::Cell(DecodedCell::Single { lane: 3 })],
        )],
    );
    program.words[1] |= 1 << 8;
    let word = program.words[1];
    assert_eq!(reject(&program, &binding), CoeffCodecError::ReservedBitsSet { at: 1, word });

    // Cell, packed pair form: bits 8..9 are required zero.
    let mut program = encoded(
        BwdRegime::Ext,
        4,
        &[term(
            TermCategory::DualProductE4,
            ONE,
            vec![
                DecodedUse::Cell(DecodedCell::Pair { endpoint0_lane: 0, delta_lane: 4 }),
                DecodedUse::Cell(DecodedCell::Pair { endpoint0_lane: 8, delta_lane: 12 }),
            ],
        )],
    );
    program.words[1] |= 1 << 9;
    let word = program.words[1];
    assert_eq!(reject(&program, &binding), CoeffCodecError::ReservedBitsSet { at: 1, word });

    // A bare lane word: bits 6..15 are required zero.
    let mut program = encoded(
        BwdRegime::R0,
        4,
        &[DecodedInstr::Move { category: TermCategory::MoveBf, from_lane: 1, to_lane: 5 }],
    );
    program.words[2] |= 1 << 7;
    let word = program.words[2];
    assert_eq!(reject(&program, &binding), CoeffCodecError::ReservedBitsSet { at: 2, word });
}

#[test]
fn rejects_an_out_of_range_coefficient() {
    let binding = dense_binding(8);
    let program = encoded(
        BwdRegime::R0,
        4,
        &[term(
            TermCategory::C0LinearBf,
            CoefficientRecipeId(9),
            vec![DecodedUse::Direct { coord: coord(0, 0, false) }],
        )],
    );
    assert_eq!(
        validate_program(&program, &binding, &bank(3)).expect_err("out of range"),
        CoeffCodecError::CoefficientOutOfRange { at: 0, index: 9, bank: 3 }
    );
    // ...and thirteen bits is a hard encoder ceiling.
    assert_eq!(
        encode_instrs(
            BwdRegime::R0,
            CellBudget::new(4).unwrap(),
            &[term(
                TermCategory::C0LinearBf,
                CoefficientRecipeId(MAX_COEFFICIENT_ENCODINGS as u32),
                vec![DecodedUse::Direct { coord: coord(0, 0, false) }],
            )],
        )
        .expect_err("overflow"),
        CoeffCodecError::CoefficientIndexOverflow { index: 8192 }
    );
}

#[test]
fn rejects_a_zero_coefficient() {
    let binding = dense_binding(8);
    let program = encoded(
        BwdRegime::R0,
        4,
        &[term(
            TermCategory::C0LinearBf,
            CoefficientRecipeId(2),
            vec![DecodedUse::Direct { coord: coord(0, 0, false) }],
        )],
    );
    let bank = vec![NormalizedCoefficientRecipe::zero()];
    assert_eq!(
        validate_program(&program, &binding, &bank).expect_err("zero"),
        CoeffCodecError::EncodedZeroCoefficient { index: 2 }
    );
}

#[test]
fn rejects_an_ordinary_multiplication_by_one() {
    let binding = dense_binding(8);
    let program = encoded(
        BwdRegime::R0,
        4,
        &[term(
            TermCategory::C0LinearBf,
            CoefficientRecipeId(2),
            vec![DecodedUse::Direct { coord: coord(0, 0, false) }],
        )],
    );
    assert_eq!(
        validate_program(&program, &binding, &[NormalizedCoefficientRecipe::one()])
            .expect_err("banked +1"),
        CoeffCodecError::OrdinaryMultiplicationByOne { index: 2, negated: false }
    );
    assert_eq!(
        validate_program(&program, &binding, &[NormalizedCoefficientRecipe::neg_one()])
            .expect_err("banked -1"),
        CoeffCodecError::OrdinaryMultiplicationByOne { index: 2, negated: true }
    );
    // The reserved literals themselves need no bank entry at all.
    for k in [CoefficientRecipeId::ONE, CoefficientRecipeId::NEG_ONE] {
        let program = encoded(
            BwdRegime::R0,
            4,
            &[term(TermCategory::C0LinearBf, k, vec![DecodedUse::Direct { coord: coord(0, 0, false) }])],
        );
        validate_program(&program, &binding, &[]).expect("a reserved literal is always canonical");
    }
}

#[test]
fn rejects_an_out_of_range_source_window() {
    let binding = dense_binding(8);
    let mut program = valid_r0();
    program.words[1] |= 5 << INPUT_WINDOW_SHIFT;
    assert_eq!(
        reject(&program, &binding),
        CoeffCodecError::SourceWindowOutOfRange { at: 1, window: 5, windows: 1 }
    );
}

#[test]
fn rejects_an_unbound_source_column() {
    // Window 0 addresses columns {0, 2}: column 1 is a hole.
    let binding = windowed_binding(&[(WindowFamily::BaseLayerWitness, 0, vec![0, 2])]);
    let program = encoded(
        BwdRegime::R0,
        4,
        &[term(
            TermCategory::C0LinearBf,
            ONE,
            vec![DecodedUse::Direct { coord: coord(0, 1, false) }],
        )],
    );
    assert_eq!(
        reject(&program, &binding),
        CoeffCodecError::UnboundSourceCoordinate { at: 1, window: 0, column: 1 }
    );
}

#[test]
fn rejects_a_misaligned_e4_lane() {
    let binding = dense_binding(8);
    let mut program = encoded(
        BwdRegime::Ext,
        4,
        &[term(
            TermCategory::C0LinearE4,
            ONE,
            vec![DecodedUse::Cell(DecodedCell::Single { lane: 4 })],
        )],
    );
    program.words[1] = MODE_CELL | 5 << CELL_ENDPOINT0_LANE_SHIFT;
    assert_eq!(reject(&program, &binding), CoeffCodecError::MisalignedE4Lane { at: 1, lane: 5 });
    // A BF lane has no alignment rule.
    let odd = encoded(
        BwdRegime::R0,
        4,
        &[term(
            TermCategory::C0LinearBf,
            ONE,
            vec![DecodedUse::Cell(DecodedCell::Single { lane: 5 })],
        )],
    );
    validate_program(&odd, &binding, &bank(2)).expect("an odd BF lane is legal");
}

#[test]
fn rejects_an_out_of_budget_lane() {
    let binding = dense_binding(8);
    // c2 = 8 BF lanes: lane 8 is one past the file.
    let mut program = encoded(
        BwdRegime::R0,
        2,
        &[term(
            TermCategory::C0LinearBf,
            ONE,
            vec![DecodedUse::Cell(DecodedCell::Single { lane: 7 })],
        )],
    );
    program.words[1] = MODE_CELL | 8 << CELL_ENDPOINT0_LANE_SHIFT;
    assert_eq!(
        reject(&program, &binding),
        CoeffCodecError::LaneOutOfBudget { at: 1, lane: 8, lanes: 8 }
    );
    // An E4 QUAD must fit, not just its first lane: lane 4 of a c2 file (8 lanes)
    // is fine, lane 8 of a c2 file is not, and neither is a quad at lane 4 of a
    // file whose last lane is 6.
    let mut program = encoded(
        BwdRegime::Ext,
        2,
        &[term(
            TermCategory::C0LinearE4,
            ONE,
            vec![DecodedUse::Cell(DecodedCell::Single { lane: 4 })],
        )],
    );
    program.words[1] = MODE_CELL | 8 << CELL_ENDPOINT0_LANE_SHIFT;
    assert_eq!(
        reject(&program, &binding),
        CoeffCodecError::LaneOutOfBudget { at: 1, lane: 8, lanes: 8 }
    );
}

/// §9.1's squared form and a MIXED-width opcode are mutually exclusive.
///
/// A squared term repeats one record at every position, so `C2ProductBF_E4`
/// carrying a single use would ask a resolver to produce one coordinate at BF
/// width and at E4 width at the same time. Lowering cannot build it (the category
/// is derived from the operand fields), but nothing downstream would notice: the
/// words encode cleanly and both interpreters plus the GPU executor would read the
/// one record twice. This is the only rejection, so it is the one that matters.
#[test]
fn rejects_a_squared_mixed_width_product() {
    assert_eq!(
        encode_instrs(
            BwdRegime::R0,
            CellBudget::new(4).unwrap(),
            &[term(
                TermCategory::C2ProductBfE4,
                ONE,
                vec![DecodedUse::Direct { coord: coord(0, 0, false) }],
            )],
        )
        .expect_err("squared mixed product"),
        CoeffCodecError::MixedProductNotMixed { instr: 0 }
    );
    // The same-width squared forms stay legal — this must reject the MIXING, not
    // the squaring.
    for category in [TermCategory::C2ProductBfBf, TermCategory::C2ProductE4E4] {
        encode_instrs(
            BwdRegime::R0,
            CellBudget::new(4).unwrap(),
            &[term(category, ONE, vec![DecodedUse::Direct { coord: coord(0, 0, false) }])],
        )
        .unwrap_or_else(|e| panic!("{category:?} squared must encode: {e:?}"));
    }
}

#[test]
fn rejects_a_plan_on_an_endpoint0_only_use() {
    let binding = dense_binding(8);
    // Built by hand: the encoder refuses to build it in the first place.
    assert_eq!(
        encode_instrs(
            BwdRegime::R0,
            CellBudget::new(4).unwrap(),
            &[term(
                TermCategory::C0LinearBf,
                ONE,
                vec![DecodedUse::Planned {
                    coord: coord(0, 0, false),
                    endpoint0: PlanAction::Fill { lane: 1 },
                    delta: PlanAction::Direct,
                }],
            )],
        )
        .expect_err("planned endpoint0"),
        CoeffCodecError::PlannedOnEndpoint0 { at: 1 }
    );
    // ...and the decoder refuses to read one off the wire.
    let mut program = encoded(
        BwdRegime::R0,
        4,
        &[term(
            TermCategory::C0LinearBf,
            ONE,
            vec![DecodedUse::Direct { coord: coord(0, 0, false) }],
        )],
    );
    program.words[1] |= MODE_PLANNED_SOURCE;
    program.words.push(ACTION_FILL | 1 << PLAN_ENDPOINT0_LANE_SHIFT);
    assert_eq!(reject(&program, &binding), CoeffCodecError::PlannedOnEndpoint0 { at: 1 });
}

#[test]
fn rejects_a_fill_on_a_native_dual_factor() {
    let binding = dense_binding(8);
    assert_eq!(
        encode_instrs(
            BwdRegime::Ext,
            CellBudget::new(4).unwrap(),
            &[term(
                TermCategory::DualProductE4,
                ONE,
                vec![
                    DecodedUse::Fill { coord: coord(0, 0, false), dst_lane: 0 },
                    DecodedUse::Direct { coord: coord(0, 4, false) },
                ],
            )],
        )
        .expect_err("fill on a dual factor"),
        CoeffCodecError::FillOnDualFactor { at: 1 }
    );
    let mut program = encoded(
        BwdRegime::Ext,
        4,
        &[term(
            TermCategory::DualProductE4,
            ONE,
            vec![
                DecodedUse::Direct { coord: coord(0, 0, false) },
                DecodedUse::Direct { coord: coord(0, 4, false) },
            ],
        )],
    );
    program.words[1] |= MODE_FILL_SOURCE;
    assert_eq!(reject(&program, &binding), CoeffCodecError::FillOnDualFactor { at: 1 });
}

#[test]
fn rejects_a_cell_form_the_opcode_does_not_scope() {
    // The packed pair form on a single-projection use, and the single form on a
    // native dual factor. Neither is reachable from the wire (the decoder reads
    // the form the opcode scopes and the other bits are then reserved), so this is
    // an encoder-side rejection.
    assert_eq!(
        encode_instrs(
            BwdRegime::R0,
            CellBudget::new(4).unwrap(),
            &[term(
                TermCategory::C0LinearBf,
                ONE,
                vec![DecodedUse::Cell(DecodedCell::Pair { endpoint0_lane: 0, delta_lane: 1 })],
            )],
        )
        .expect_err("pair form on a single projection"),
        CoeffCodecError::CellFormNotOpcodeScoped { at: 1 }
    );
    assert_eq!(
        encode_instrs(
            BwdRegime::Ext,
            CellBudget::new(4).unwrap(),
            &[term(
                TermCategory::DualProductE4,
                ONE,
                vec![
                    DecodedUse::Cell(DecodedCell::Single { lane: 0 }),
                    DecodedUse::Direct { coord: coord(0, 4, false) },
                ],
            )],
        )
        .expect_err("single form on a dual factor"),
        CoeffCodecError::CellFormNotOpcodeScoped { at: 1 }
    );
}

#[test]
fn rejects_the_fourth_plan_action() {
    let binding = dense_binding(8);
    let mut program = encoded(
        BwdRegime::Ext,
        4,
        &[term(
            TermCategory::DualProductE4,
            ONE,
            vec![
                DecodedUse::Planned {
                    coord: coord(0, 0, false),
                    endpoint0: PlanAction::Fill { lane: 0 },
                    delta: PlanAction::Fill { lane: 4 },
                },
                DecodedUse::Direct { coord: coord(0, 4, false) },
            ],
        )],
    );
    // Endpoint0 action Fill(0) -> Invalid, lane already zero.
    program.words[2] = (program.words[2] & !PLAN_ACTION_MASK) | ACTION_INVALID;
    assert_eq!(reject(&program, &binding), CoeffCodecError::PlanActionInvalid { at: 2 });
    assert_eq!(
        encode_instrs(
            BwdRegime::Ext,
            CellBudget::new(4).unwrap(),
            &[term(
                TermCategory::DualProductE4,
                ONE,
                vec![
                    DecodedUse::Planned {
                        coord: coord(0, 0, false),
                        endpoint0: PlanAction::Invalid,
                        delta: PlanAction::Fill { lane: 4 },
                    },
                    DecodedUse::Direct { coord: coord(0, 4, false) },
                ],
            )],
        )
        .expect_err("invalid action"),
        CoeffCodecError::PlanActionInvalid { at: 2 }
    );
}

#[test]
fn rejects_a_nonzero_lane_on_a_direct_or_invalid_action() {
    let binding = dense_binding(8);
    let mut program = encoded(
        BwdRegime::Ext,
        4,
        &[term(
            TermCategory::DualProductE4,
            ONE,
            vec![
                DecodedUse::Planned {
                    coord: coord(0, 0, false),
                    endpoint0: PlanAction::Direct,
                    delta: PlanAction::Fill { lane: 4 },
                },
                DecodedUse::Direct { coord: coord(0, 4, false) },
            ],
        )],
    );
    program.words[2] |= 1 << PLAN_ENDPOINT0_LANE_SHIFT;
    assert_eq!(
        reject(&program, &binding),
        CoeffCodecError::NonZeroLaneOnAction { at: 2, action: ACTION_DIRECT, lane: 1 }
    );
}

#[test]
fn rejects_every_non_canonical_plan() {
    let budget = CellBudget::new(4).unwrap();
    let dual = |e0: PlanAction, d: PlanAction| {
        term(
            TermCategory::DualProductE4,
            ONE,
            vec![
                DecodedUse::Planned { coord: coord(0, 0, false), endpoint0: e0, delta: d },
                DecodedUse::Direct { coord: coord(0, 4, false) },
            ],
        )
    };
    let delta = |e0: PlanAction, d: PlanAction| {
        term(
            TermCategory::C2ProductBfBf,
            ONE,
            vec![
                DecodedUse::Planned { coord: coord(0, 0, false), endpoint0: e0, delta: d },
                DecodedUse::Direct { coord: coord(0, 1, false) },
            ],
        )
    };
    let cases: &[(BwdRegime, DecodedInstr, ShortestForm)] = &[
        // {Direct, Direct} is a DirectSource, on either role.
        (
            BwdRegime::Ext,
            dual(PlanAction::Direct, PlanAction::Direct),
            ShortestForm::DirectSource,
        ),
        (
            BwdRegime::R0,
            delta(PlanAction::Direct, PlanAction::Direct),
            ShortestForm::DirectSource,
        ),
        // A fully resident pair is the packed Cell form.
        (
            BwdRegime::Ext,
            dual(PlanAction::UseResident { lane: 0 }, PlanAction::UseResident { lane: 4 }),
            ShortestForm::CellPair,
        ),
        // A single requested-projection fill is a FillSource.
        (
            BwdRegime::R0,
            delta(PlanAction::Direct, PlanAction::Fill { lane: 2 }),
            ShortestForm::FillSource,
        ),
        // A resident Delta whose endpoint is touched for nothing is a Cell.
        (
            BwdRegime::R0,
            delta(PlanAction::Direct, PlanAction::UseResident { lane: 2 }),
            ShortestForm::CellSingle,
        ),
        (
            BwdRegime::R0,
            delta(PlanAction::UseResident { lane: 1 }, PlanAction::UseResident { lane: 2 }),
            ShortestForm::CellSingle,
        ),
    ];
    for (regime, instr, shortest) in cases {
        assert_eq!(
            encode_instrs(*regime, budget, std::slice::from_ref(instr)).expect_err("canonical"),
            CoeffCodecError::NonCanonicalPlan { at: 2, shortest: *shortest },
            "{instr:?}"
        );
    }
    // ...and the same forms are unreadable off the wire.
    let binding = dense_binding(8);
    let mut program = encoded(
        BwdRegime::Ext,
        4,
        &[dual(PlanAction::Fill { lane: 0 }, PlanAction::Fill { lane: 4 })],
    );
    program.words[2] = ACTION_DIRECT | ACTION_DIRECT << PLAN_DELTA_ACTION_SHIFT;
    assert_eq!(
        reject(&program, &binding),
        CoeffCodecError::NonCanonicalPlan { at: 2, shortest: ShortestForm::DirectSource }
    );
}

/// §12.2's `FillClobbersTermInput` scopes "later" to later BINDING slots
/// (`place.rs`'s `slot_read_lanes[slot + 1..]`), but `program_records` emits a
/// mixed product's BF factor FIRST — so a transposed term's fill can execute
/// before the read it reclaims and escape that clause entirely. The codec
/// therefore re-checks the hazard in EMITTED order, where the transposition is
/// introduced.
#[test]
fn rejects_a_fill_that_clobbers_a_later_operand() {
    let binding = dense_binding(8);
    let budget = CellBudget::new(4).unwrap();
    // The exact review probe: position 0 fills BF lane 4, position 1 reads the E4
    // quad at lane 4. Accepted before this check existed.
    let probe = term(
        TermCategory::C2ProductBfE4,
        ONE,
        vec![
            DecodedUse::Fill { coord: coord(0, 0, true), dst_lane: 4 },
            DecodedUse::Cell(DecodedCell::Single { lane: 4 }),
        ],
    );
    assert_eq!(
        encode_instrs(BwdRegime::R0, budget, std::slice::from_ref(&probe))
            .expect_err("the encoder must reject the clobber"),
        CoeffCodecError::FillClobbersLaterOperand { at: 1, lane: 4 }
    );

    // ...and so must the pure-wire validator, which never sees the placement. The
    // words are hand-assembled because the encoder now refuses to emit them.
    let words = vec![
        opcode_of(BwdRegime::R0, TermCategory::C2ProductBfE4).unwrap() << 13,
        MODE_FILL_SOURCE | 1 << INPUT_FIRST_ACCESS_SHIFT,
        4 << LANE_WORD_SHIFT,
        MODE_CELL | 4 << CELL_ENDPOINT0_LANE_SHIFT,
    ];
    let smuggled = EncodedProgram { regime: BwdRegime::R0, budget, c_init: None, words };
    assert_eq!(
        reject(&smuggled, &binding),
        CoeffCodecError::FillClobbersLaterOperand { at: 1, lane: 4 }
    );

    // The two shapes that look similar but are LEGAL stay legal:
    //   * a plan reading a lane and then reclaiming it, within ONE record (§8's
    //     read-then-write phases); and
    //   * the reverse order — a later operand's fill cannot clobber an earlier
    //     operand that has already been resolved.
    let reclaim = term(
        TermCategory::DualProductE4,
        ONE,
        vec![
            DecodedUse::Planned {
                coord: coord(0, 0, true),
                endpoint0: PlanAction::UseResident { lane: 4 },
                delta: PlanAction::Fill { lane: 4 },
            },
            DecodedUse::Direct { coord: coord(0, 4, false) },
        ],
    );
    encode_instrs(BwdRegime::Ext, budget, std::slice::from_ref(&reclaim))
        .expect("a plan may reclaim the lane it just read");
    let reverse = term(
        TermCategory::C2ProductBfE4,
        ONE,
        vec![
            DecodedUse::Cell(DecodedCell::Single { lane: 4 }),
            DecodedUse::Fill { coord: coord(0, 0, true), dst_lane: 4 },
        ],
    );
    encode_instrs(BwdRegime::R0, budget, std::slice::from_ref(&reverse))
        .expect("a later fill cannot clobber an already-resolved operand");
    // A squared term performs ONE resolution (§9.1 as amended), so its repeated
    // record is not a second reader either.
    let squared = term(
        TermCategory::C2ProductE4E4,
        ONE,
        vec![DecodedUse::Planned {
            coord: coord(0, 0, true),
            endpoint0: PlanAction::UseResident { lane: 4 },
            delta: PlanAction::Fill { lane: 4 },
        }],
    );
    encode_instrs(BwdRegime::R0, budget, std::slice::from_ref(&squared))
        .expect("a squared term resolves once, so it cannot clobber itself");
}

/// `program_records` surfaces `term_slots`' own rejections rather than swallowing
/// them.
#[test]
fn rejects_a_layer_term_slots_refuses() {
    let (layer, prices) = squared_r0_layer();
    let (placement, binding) = page_place_bind(&layer, &prices, 16);
    let mut corrupt = layer.clone();
    // A `C0Linear` whose value is a `Delta` projection: a role `term_slots`
    // rejects, reported through `CoeffCodecError::Schedule`.
    corrupt.terms[0] = CoeffTerm::C0Linear {
        id: TermId(0),
        coefficient: CoefficientRecipeId::ONE,
        value: ProjectionId::delta(SourceId(0)),
        field: FieldKind::Base,
    };
    let err = program_records(&corrupt, &placement, &binding).expect_err("bad projection role");
    assert!(matches!(err, CoeffCodecError::Schedule(_)), "{err:?}");
}

#[test]
fn rejects_a_program_past_the_kernel_argument_cap() {
    let budget = CellBudget::new(4).unwrap();
    let one = term(
        TermCategory::C0LinearBf,
        ONE,
        vec![DecodedUse::Direct { coord: coord(0, 0, false) }],
    );
    let count = KERNEL_ARGUMENT_CEILING_BYTES / 4 + 1;
    let instrs = vec![one; count];
    assert_eq!(
        encode_instrs(BwdRegime::R0, budget, &instrs).expect_err("cap"),
        CoeffCodecError::ProgramExceedsKernelArgumentCap { bytes: count * 4 }
    );
}

#[test]
fn rejects_a_category_its_regime_cannot_encode() {
    let budget = CellBudget::new(4).unwrap();
    assert_eq!(
        encode_instrs(
            BwdRegime::Ext,
            budget,
            &[DecodedInstr::Move { category: TermCategory::MoveBf, from_lane: 0, to_lane: 1 }],
        )
        .expect_err("no continuation MoveBF"),
        CoeffCodecError::CategoryNotEncodable {
            regime: BwdRegime::Ext,
            category: TermCategory::MoveBf,
        }
    );
    assert_eq!(
        encode_instrs(
            BwdRegime::R0,
            budget,
            &[term(
                TermCategory::DualProductE4,
                ONE,
                vec![
                    DecodedUse::Direct { coord: coord(0, 0, false) },
                    DecodedUse::Direct { coord: coord(0, 4, false) },
                ],
            )],
        )
        .expect_err("no R0 dual"),
        CoeffCodecError::CategoryNotEncodable {
            regime: BwdRegime::R0,
            category: TermCategory::DualProductE4,
        }
    );
}

// ── 4. The two spellings the wire fixes ──────────────────────────────────────

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

fn synthetic(
    regime: BwdRegime,
    sources: Vec<CoeffSource>,
    terms: Vec<CoeffTerm>,
) -> (CoeffLayer, Vec<SourcePrice>) {
    let prices = sources.iter().map(|s| price_of(s.field)).collect();
    let layer = CoeffLayer {
        regime,
        c_init: None,
        coefficients: Vec::new(),
        sources,
        terms,
    };
    (layer, prices)
}

fn page_place_bind(
    layer: &CoeffLayer,
    prices: &[SourcePrice],
    cells: u8,
) -> (gkr_eval_isa::bwd::coeff::place::CoeffPlacement, CoeffSourceBinding) {
    let order = stable_normalized_order(layer);
    let request = PagingRequest {
        budget: CellBudget::new(cells).expect("c2..c16"),
        target_depth: default_target_depth(layer.regime),
    };
    let plan = page_projections(layer, prices, request, &order).expect("pager");
    let placement = place_paging_plan(layer, prices, &plan).expect("placement");
    let binding =
        bind_coeff_sources(layer, &Default::default(), &placement).expect("binding");
    (placement, binding)
}

/// `k * d0 * d0` at R0 and `k * s0 * s0` in continuation: ONE deduplicated slot
/// for a binary opcode.
fn squared_r0_layer() -> (CoeffLayer, Vec<SourcePrice>) {
    synthetic(
        BwdRegime::R0,
        vec![read_source(0, FieldKind::Base), read_source(1, FieldKind::Base)],
        vec![
            CoeffTerm::C2Product {
                id: TermId(0),
                coefficient: CoefficientRecipeId::ONE,
                lhs: ProjectionId::delta(SourceId(0)),
                rhs: ProjectionId::delta(SourceId(0)),
                lhs_field: FieldKind::Base,
                rhs_field: FieldKind::Base,
            },
            CoeffTerm::C2Product {
                id: TermId(1),
                coefficient: CoefficientRecipeId::NEG_ONE,
                lhs: ProjectionId::delta(SourceId(0)),
                rhs: ProjectionId::delta(SourceId(1)),
                lhs_field: FieldKind::Base,
                rhs_field: FieldKind::Base,
            },
        ],
    )
}

#[test]
fn a_squared_term_repeats_one_record_and_resolves_once() {
    let (layer, prices) = squared_r0_layer();
    let (placement, binding) = page_place_bind(&layer, &prices, 16);
    let program = encode_program(&layer, &placement, &binding).expect("encode");
    certify_encoding(&layer, &placement, &binding, &program).expect("certificate");

    let records = program_records(&layer, &placement, &binding).expect("records");
    let squared: Vec<&DecodedInstr> = records.iter().filter(|i| i.is_squared()).collect();
    assert_eq!(squared.len(), 1, "the fixture has exactly one squared term");
    let DecodedInstr::Term { uses, .. } = squared[0] else { unreachable!() };
    assert_eq!(uses.len(), 1, "a squared term carries ONE resolution");

    // On the wire the record appears twice, byte-identically, so §9.1's "the
    // opcode determines arity" still holds and the decoder recovers one use.
    let decoded = decode_program(&program, &binding).expect("decode");
    assert_eq!(decoded, records);
    let index = decoded.iter().position(DecodedInstr::is_squared).expect("a squared record");
    let offset: usize = decoded[..index].iter().map(DecodedInstr::words).sum();
    let DecodedInstr::Term { uses, .. } = &decoded[index] else { panic!("term") };
    assert_eq!(uses.len(), 1, "the decoder recovers ONE resolution");
    let record = uses[0].words();
    assert_eq!(decoded[index].words(), 1 + 2 * record, "header + the record, twice");
    let first = offset + 1;
    assert_eq!(
        program.words[first..first + record],
        program.words[first + record..first + 2 * record],
        "the two input records are byte-identical"
    );
}

#[test]
fn a_mixed_product_emits_the_bf_factor_first() {
    // lhs is EXT and rhs is BASE, so a faithful slot-order emission would put the
    // E4 factor at position 0 — which `C2ProductBF_E4` cannot express.
    let (layer, prices) = synthetic(
        BwdRegime::R0,
        vec![read_source(0, FieldKind::Ext), read_source(1, FieldKind::Base)],
        vec![CoeffTerm::C2Product {
            id: TermId(0),
            coefficient: CoefficientRecipeId::ONE,
            lhs: ProjectionId::delta(SourceId(0)),
            rhs: ProjectionId::delta(SourceId(1)),
            lhs_field: FieldKind::Ext,
            rhs_field: FieldKind::Base,
        }],
    );
    let (placement, binding) = page_place_bind(&layer, &prices, 16);
    assert_eq!(term_category(&layer.terms[0]), TermCategory::C2ProductBfE4);
    let program = encode_program(&layer, &placement, &binding).expect("encode");
    certify_encoding(&layer, &placement, &binding, &program).expect("certificate");

    let records = program_records(&layer, &placement, &binding).expect("records");
    let DecodedInstr::Term { uses, .. } = &records[0] else { panic!("term") };
    let source_at = |position: usize| {
        let coord = uses[position].coord().expect("direct");
        binding.resolve(coord.window, coord.column).expect("bound")
    };
    assert_eq!(source_at(0), SourceId(1), "position 0 is the BF factor");
    assert_eq!(source_at(1), SourceId(0), "position 1 is the E4 factor");
    // ...which is exactly what `operand_width` promises the decoder.
    assert_eq!(operand_width(TermCategory::C2ProductBfE4, 0), Some(ValueWidth::Bf));
    assert_eq!(operand_width(TermCategory::C2ProductBfE4, 1), Some(ValueWidth::E4));
}

/// §9.6: "There are no generic LDC or special value operands. Procedural values
/// remain ordinary source coordinates whose window descriptor selects procedural
/// resolution."
#[test]
fn a_procedural_source_uses_an_ordinary_coordinate() {
    let (layer, prices) = synthetic(
        BwdRegime::R0,
        vec![
            CoeffSource {
                origin: OriginLeaf::VirtualSetup { kind: VirtualSetupKind::RangeCheck16Bits },
                field: FieldKind::Base,
            },
            read_source(0, FieldKind::Base),
        ],
        vec![
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
                field: FieldKind::Base,
            },
        ],
    );
    let (placement, binding) = page_place_bind(&layer, &prices, 16);
    let program = encode_program(&layer, &placement, &binding).expect("encode");
    certify_encoding(&layer, &placement, &binding, &program).expect("certificate");

    let procedural: Vec<usize> = binding
        .windows
        .iter()
        .enumerate()
        .filter(|(_, w)| w.is_procedural())
        .map(|(i, _)| i)
        .collect();
    assert_eq!(procedural.len(), 1, "one procedural window");
    let records = program_records(&layer, &placement, &binding).expect("records");
    let modes: Vec<u16> = program
        .words
        .iter()
        .skip(1)
        .step_by(2)
        .map(|w| w & INPUT_MODE_MASK)
        .collect();
    assert!(
        modes.iter().all(|m| *m == MODE_DIRECT_SOURCE),
        "a procedural value is an ORDINARY direct source read, not a special operand"
    );
    assert_eq!(records.len(), 2);
    // The disassembler names it, because only the descriptor knows.
    let text = disassemble(&program, &binding).expect("disassembly");
    assert!(text.contains(" proc"), "the disassembler must surface procedural resolution:\n{text}");
}

// ── 5. The disassembler ──────────────────────────────────────────────────────

/// The disassembler is a durable debugging asset, so its format is pinned: a
/// silent drift would break every downstream eyeball.
#[test]
fn disassembly_format_is_pinned() {
    let binding = windowed_binding(&[
        (WindowFamily::BaseLayerWitness, 0, vec![0, 4, 9]),
        (WindowFamily::VirtualSetup { kind: 0 }, 0, vec![0]),
    ]);
    let program = EncodedProgram {
        c_init: Some(CoefficientRecipeId(2)),
        ..encoded(
            BwdRegime::Ext,
            16,
            &[
                term(
                    TermCategory::C0LinearE4,
                    CoefficientRecipeId::ONE,
                    vec![DecodedUse::Direct { coord: coord(0, 0, true) }],
                ),
                term(
                    TermCategory::C0LinearE4,
                    CoefficientRecipeId::NEG_ONE,
                    vec![DecodedUse::Fill { coord: coord(1, 0, true), dst_lane: 8 }],
                ),
                DecodedInstr::Move {
                    category: TermCategory::MoveE4,
                    from_lane: 8,
                    to_lane: 20,
                },
                term(
                    TermCategory::DualProductE4,
                    CoefficientRecipeId(3),
                    vec![
                        DecodedUse::Planned {
                            coord: coord(0, 4, true),
                            endpoint0: PlanAction::UseResident { lane: 20 },
                            delta: PlanAction::Fill { lane: 24 },
                        },
                        DecodedUse::Cell(DecodedCell::Pair {
                            endpoint0_lane: 20,
                            delta_lane: 28,
                        }),
                    ],
                ),
                term(
                    TermCategory::DualProductE4,
                    CoefficientRecipeId(4),
                    vec![DecodedUse::Direct { coord: coord(0, 9, false) }],
                ),
            ],
        )
    };
    let text = disassemble(&program, &binding).expect("disassembly");
    println!("{text}");
    let expected = "\
; program regime=Ext budget=c16 lanes=64 words=15 bytes=30 c_init=#0
0000  C0LinearE4      k=+1     e0:e4 s0(w0c0)! direct
0002  C0LinearE4      k=-1     e0:e4 s3(w1c0)! proc fill l8
0005  MoveE4          l8 -> l20
0008  DualProductE4   k=#1     pair:e4 s1(w0c4)! plan e0=resident l20 d=fill l24  |  \
pair:e4 resident e0=l20 d=l28
0012  DualProductE4   k=#2     pair:e4 s2(w0c9). direct  [squared]
";
    assert_eq!(text, expected, "the disassembly format drifted");
}

// ── 6. The encoder against a real placement ──────────────────────────────────

#[test]
fn encode_program_certifies_against_its_placement_at_every_budget() {
    let (layer, prices) = squared_r0_layer();
    for cells in [2u8, 3, 4, 8, 16] {
        let (placement, binding) = page_place_bind(&layer, &prices, cells);
        let program = encode_program(&layer, &placement, &binding)
            .unwrap_or_else(|e| panic!("c{cells}: {e:?}"));
        assert_eq!(program.budget.cells(), cells);
        certify_encoding(&layer, &placement, &binding, &program)
            .unwrap_or_else(|e| panic!("c{cells} certificate: {e:?}"));
        // A record that does not come from the placement is caught.
        let mut wrong = program.clone();
        wrong.words[0] = opcode_of(BwdRegime::R0, TermCategory::C2ProductBfBf).unwrap() << 13 | 1;
        assert!(matches!(
            certify_encoding(&layer, &placement, &binding, &wrong),
            Err(CoeffCodecError::RecordMismatch { index: 0 }) | Err(CoeffCodecError::CoefficientOutOfRange { .. })
        ));
        // ...and so is a stream that stops a whole record early.
        let records = program_records(&layer, &placement, &binding).expect("records");
        let mut short = program.clone();
        short.words.truncate(records[0].words());
        let err = certify_encoding(&layer, &placement, &binding, &short).expect_err("short");
        assert_eq!(
            err,
            CoeffCodecError::TruncatedProgram { records: 1, expected: records.len() },
            "c{cells}"
        );
    }
}

/// The placement must be the one the program was encoded from.
#[test]
fn rejects_a_placement_from_another_regime() {
    let (layer, prices) = squared_r0_layer();
    let (placement, binding) = page_place_bind(&layer, &prices, 16);
    let mut other = layer.clone();
    other.regime = BwdRegime::Ext;
    assert_eq!(
        program_records(&other, &placement, &binding).expect_err("regime"),
        CoeffCodecError::RegimeMismatch { declared: BwdRegime::R0, found: BwdRegime::Ext }
    );
}

/// The placed use count must be the term's deduplicated slot count, and a
/// source-bearing use must have a bound coordinate.
#[test]
fn rejects_a_placement_the_binding_does_not_describe() {
    let (layer, prices) = squared_r0_layer();
    let (placement, binding) = page_place_bind(&layer, &prices, 16);

    let mut extra = placement.clone();
    if let Some(ScheduledInstr::Term { uses, .. }) = extra.instrs.first_mut() {
        uses.push(ValueUse::Cell(CellRead::Single {
            projection: ProjectionId::delta(SourceId(0)),
            lane: 0,
        }));
    }
    assert_eq!(
        program_records(&layer, &extra, &binding).expect_err("slot count"),
        CoeffCodecError::SlotCountMismatch { instr: 0, slots: 1, uses: 2 }
    );

    let mut unbound = binding.clone();
    unbound.uses.clear();
    let err = program_records(&layer, &placement, &unbound).expect_err("unbound");
    assert!(matches!(err, CoeffCodecError::UnboundInput { .. }), "{err:?}");
}

/// The wire names only "the role's projection", so a use about a DIFFERENT
/// projection or source would encode a record that silently means something else.
#[test]
fn rejects_a_use_that_names_another_slot() {
    let (layer, prices) = squared_r0_layer();
    let (placement, binding) = page_place_bind(&layer, &prices, 16);
    let mut wrong = placement.clone();
    let mut swapped = false;
    'outer: for instr in wrong.instrs.iter_mut() {
        let ScheduledInstr::Term { uses, .. } = instr else { continue };
        for use_ in uses.iter_mut() {
            if let ValueUse::Direct { source } = use_ {
                *source = SourceId(1 - source.0);
                swapped = true;
                break 'outer;
            }
        }
    }
    assert!(swapped, "the fixture must contain a direct use to corrupt");
    let err = program_records(&layer, &wrong, &binding).expect_err("mismatch");
    assert!(matches!(err, CoeffCodecError::UseSlotMismatch { .. }), "{err:?}");
}
