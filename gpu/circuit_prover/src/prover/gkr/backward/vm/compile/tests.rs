//! CPU-side gates on the add/sub layer-0 coefficient realizations the GPU parity
//! run consumes (design §9, §10.3, §12.1-§12.4).
//!
//! Everything here is host-only and runs without a GPU. Its job is to prove that
//! what `load_add_sub_l0_coeff_case` hands the device is a real, certified,
//! semantically faithful program — so that a GPU failure is a kernel failure and
//! not a malformed fixture.

use std::collections::BTreeMap;

use cs::gkr_compiler::dag_ir::{BwdRegime, FieldKind};
use gkr_eval_isa::bwd::coeff::encode::{decode_program, disassemble, DecodedInstr};
use gkr_eval_isa::bwd::coeff::interp::{
    interpret_coeff_layer, interpret_encoded_program, CoeffResolver,
};
use gkr_eval_isa::bwd::coeff::limits::SOURCE_WINDOW_COLUMNS;
use gkr_eval_isa::bwd::coeff::model::{CoeffLayer, CoefficientRecipeId, SourceId};

use super::{
    digit, load_add_sub_l0_coeff_case, pseudo_coefficient, pseudo_ext, AddSubCoeffCase,
    PROBED_BUDGETS,
};
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::vm::desc::{
    BWD_COEFF_PROGRAM_WORD_CAP, BWD_COEFF_SOURCE_WINDOW_CAP,
};
use crate::upstream::FieldExtension;

/// A source's `(Endpoint0, Delta)` pair, matching the crate's own corpus
/// resolver: a `FieldKind::Base` source must produce BASE-EMBEDDED values or the
/// cell file would be lying about the width it stores.
///
/// The GPU harness does NOT use this: there, a source's value comes from the
/// device backing behind its window, which is the whole point of the parity run.
fn pseudo_source_pair(field: FieldKind, id: SourceId, row: usize) -> (E4, E4) {
    match field {
        FieldKind::Base => (
            <E4 as FieldExtension<BF>>::from_base(digit(0xb0, id.0, row as u32)),
            <E4 as FieldExtension<BF>>::from_base(digit(0xb1, id.0, row as u32)),
        ),
        FieldKind::Ext => (
            pseudo_ext(0x5000, id.0, row as u32),
            pseudo_ext(0x5001, id.0, row as u32),
        ),
    }
}

struct Pseudo<'a> {
    layer: &'a CoeffLayer,
}

impl CoeffResolver for Pseudo<'_> {
    fn coefficient(&self, id: CoefficientRecipeId) -> E4 {
        pseudo_coefficient(id)
    }

    fn source_pair(&self, id: SourceId, row: usize) -> (E4, E4) {
        pseudo_source_pair(self.layer.sources[id.0 as usize].field, id, row)
    }
}

/// The `(regime, round)` coordinates the GPU ladder runs: R0 at round zero, and
/// the single continuation schedule bound at each of D0..D3.
fn probed_coordinates() -> Vec<(BwdRegime, u8)> {
    let mut out = vec![(BwdRegime::R0, 0u8)];
    out.extend((0..=3u8).map(|round| (BwdRegime::Ext, round)));
    out
}

fn every_case() -> Vec<AddSubCoeffCase> {
    probed_coordinates()
        .into_iter()
        .flat_map(|(regime, round)| {
            PROBED_BUDGETS
                .into_iter()
                .map(move |cells| load_add_sub_l0_coeff_case(regime, round, cells))
        })
        .collect()
}

fn label(case: &AddSubCoeffCase) -> String {
    format!(
        "add/sub L0 {:?} round {} c{}",
        case.regime, case.round, case.budget_cells
    )
}

/// Every realization fits the frozen descriptor and binds its sources the way
/// §10.3 requires.
///
/// `realize` already ran `certify_encoding` and `certify_source_binding`, so this
/// checks the two things those certificates deliberately do NOT: that the result
/// fits the GPU descriptor's MEASURED capacities (an encoding-legal program can
/// still overflow the by-value array), and that first access is one-per-source
/// from the binding's own use list rather than from the encoder's bookkeeping.
#[test]
fn add_sub_l0_realizations_fit_the_descriptor_and_bind_first_access_once() {
    for case in every_case() {
        let name = label(&case);
        assert!(
            case.program.words.len() <= BWD_COEFF_PROGRAM_WORD_CAP,
            "{name}: {} words exceeds the by-value cap {BWD_COEFF_PROGRAM_WORD_CAP}",
            case.program.words.len()
        );
        assert!(
            case.binding.windows.len() <= BWD_COEFF_SOURCE_WINDOW_CAP,
            "{name}: {} windows exceeds the descriptor cap {BWD_COEFF_SOURCE_WINDOW_CAP}",
            case.binding.windows.len()
        );
        assert_eq!(case.binding.target_depth, case.round, "{name}: target depth");
        assert_eq!(
            case.binding.materialize,
            case.round >= 3,
            "{name}: §10.2's materialization policy is static in the target depth"
        );

        for (index, window) in case.binding.windows.iter().enumerate() {
            let widest = window
                .columns
                .last()
                .map(|column| column.column - window.first_column)
                .unwrap_or(0);
            assert!(
                widest < SOURCE_WINDOW_COLUMNS,
                "{name}: window {index} spans {widest} columns"
            );
            assert!(
                !window.columns.is_empty(),
                "{name}: window {index} is bound but addresses no column"
            );
        }

        // §10.3: exactly one first access per materializing logical source, and
        // never more than one for any source.
        let mut firsts = BTreeMap::<SourceId, usize>::new();
        let mut uses = BTreeMap::<SourceId, usize>::new();
        for use_ in &case.binding.uses {
            *uses.entry(use_.source).or_default() += 1;
            if use_.first_access {
                *firsts.entry(use_.source).or_default() += 1;
            }
        }
        for (source, count) in &firsts {
            assert_eq!(
                *count, 1,
                "{name}: source {source:?} carries {count} first accesses"
            );
        }
        for source in uses.keys() {
            assert_eq!(
                firsts.get(source).copied().unwrap_or_default(),
                1,
                "{name}: source {source:?} has uses but no single first access"
            );
        }

        // The stream decodes back to the same instruction count the encoder
        // produced, with no trailing words.
        let instrs = decode_program(&case.program, &case.binding)
            .unwrap_or_else(|error| panic!("{name}: decode: {error:?}"));
        assert_eq!(
            instrs.iter().map(DecodedInstr::words).sum::<usize>(),
            case.program.words.len(),
            "{name}: decoded record widths must exactly cover the stream"
        );
    }
}

/// §12.4's first gate, on the exact programs the GPU runs: the encoded
/// interpreter and the semantic interpreter agree per row.
#[test]
fn the_encoded_and_semantic_interpreters_agree_on_add_sub_l0() {
    for case in every_case() {
        let name = label(&case);
        let resolver = Pseudo { layer: &case.layer };
        for row in [0usize, 1, 37, 200] {
            let semantic = interpret_coeff_layer(&case.layer, row, &resolver)
                .unwrap_or_else(|error| panic!("{name}: semantic row {row}: {error:?}"));
            let encoded =
                interpret_encoded_program(&case.program, &case.binding, row, &resolver)
                    .unwrap_or_else(|error| panic!("{name}: encoded row {row}: {error:?}"));
            assert_eq!(semantic.0, encoded.0, "{name}: acc_c0 row {row}");
            assert_eq!(semantic.1, encoded.1, "{name}: acc_c2 row {row}");
        }
    }
}

/// What the production corpus for this layer actually reaches, and what it does
/// NOT.
///
/// This is the coverage contract between the two GPU tests. The parity ladder
/// runs REAL programs, so whatever this census says is absent from them can only
/// be reached by `bwd_coeff_release_executor_covers_every_form`'s hand-built
/// fixtures — and if a future corpus change starts emitting one of the absent
/// forms, or stops emitting a present one, this test says so instead of letting
/// a kernel path go quietly untested.
///
/// Measured over R0 plus the four continuation bindings at c2/c5/c16:
///
/// | Form | add/sub L0 |
/// |---|---|
/// | every live term opcode of each regime | present |
/// | `Direct`, `Cell`, `FillSource` | present |
/// | `PlannedSource` | continuation only |
/// | squared terms (§9.1) | present, 19 per program |
/// | banked coefficient | present |
/// | reserved `+1` | R0 only, ONE term |
/// | reserved `-1` | ABSENT |
/// | `MoveBF` / `MoveE4` | ABSENT |
#[test]
fn the_add_sub_l0_form_census_matches_what_the_gpu_tests_assume() {
    let mut seen_plus_one = false;
    let mut seen_banked = false;
    let mut seen_squared = 0usize;
    let mut seen_moves = 0usize;
    let mut seen_minus_one = 0usize;
    let mut r0_categories = std::collections::BTreeSet::new();
    let mut ext_categories = std::collections::BTreeSet::new();
    for case in every_case() {
        for instr in decode_program(&case.program, &case.binding).expect("decode") {
            match &instr {
                DecodedInstr::Move { .. } => seen_moves += 1,
                DecodedInstr::Term {
                    category,
                    coefficient,
                    ..
                } => {
                    match case.regime {
                        BwdRegime::R0 => r0_categories.insert(format!("{category:?}")),
                        BwdRegime::Ext => ext_categories.insert(format!("{category:?}")),
                    };
                    if instr.is_squared() {
                        seen_squared += 1;
                    }
                    match coefficient.0 {
                        0 => seen_plus_one = true,
                        1 => seen_minus_one += 1,
                        _ => seen_banked = true,
                    }
                }
            }
        }
    }

    assert_eq!(
        r0_categories,
        [
            "C0LinearBf",
            "C0LinearE4",
            "C2ProductBfBf",
            "C2ProductBfE4",
            "C2ProductE4E4",
        ]
        .map(String::from)
        .into_iter()
        .collect(),
        "the R0 ladder must reach every live R0 term opcode"
    );
    assert_eq!(
        ext_categories,
        ["C0LinearE4", "DualProductE4"]
            .map(String::from)
            .into_iter()
            .collect(),
        "the continuation ladder must reach every live continuation term opcode"
    );
    assert!(seen_plus_one, "the reserved +1 fast path is unreachable");
    assert!(seen_banked, "the banked coefficient path is unreachable");
    assert!(
        seen_squared > 0,
        "§9.1's resolve-once rule is unreachable from real programs"
    );
    // The two forms the corpus does NOT emit. Asserted as ZERO rather than
    // ignored, so the day one appears the coverage story is re-read instead of
    // silently drifting.
    assert_eq!(
        seen_minus_one, 0,
        "add/sub L0 now emits a reserved -1; the ladder covers it too, so relax \
         this and drop the note in `bwd_coeff_release_executor_covers_every_form`"
    );
    assert_eq!(
        seen_moves, 0,
        "add/sub L0 now emits moves; the ladder covers them too, so relax this \
         and drop the note in `bwd_coeff_release_executor_covers_every_form`"
    );
}

/// Durable inspection tool: the readable decompile of add/sub layer-0 R0 at c2,
/// the budget the parity ladder selects in the middle of the range, and c16.
///
/// Ignored on purpose — it produces output rather than a verdict. Run it with:
///
/// ```text
/// cargo +nightly-2026-02-10 test -p gpu_circuit_prover --features bench --release \
///   add_sub_l0_r0_coefficient_decompile -- --ignored --nocapture
/// ```
#[test]
#[ignore = "inspection tool: prints the add/sub L0 R0 coefficient decompile; run with --ignored --nocapture"]
fn add_sub_l0_r0_coefficient_decompile() {
    for cells in PROBED_BUDGETS {
        let case = load_add_sub_l0_coeff_case(BwdRegime::R0, 0, cells);
        let text = disassemble(&case.program, &case.binding)
            .unwrap_or_else(|error| panic!("disassemble c{cells}: {error:?}"));
        println!(
            "===== add/sub L0 R0 c{cells}: {} terms, {} words ({} bytes), {} windows, \
             {} coefficients, digest 0x{:016x} =====",
            case.report.terms,
            case.program.words.len(),
            case.program.bytes(),
            case.binding.windows.len(),
            case.layer.coefficients.len(),
            case.report.program_digest,
        );
        println!("{text}");
        assert!(
            !text.is_empty(),
            "c{cells}: the decompile must not be empty"
        );
    }
}
