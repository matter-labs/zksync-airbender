//! The host-lowering gate for the SEGMENTED lean VM.
//!
//! Sibling of [`seg_abi_tests`](super::seg_abi_tests), which pins the descriptor
//! LAYOUT; this file pins what [`seg_lower`](super::seg_lower) puts INTO it. Every
//! pointer here is a fabricated host-side address: lowering performs address
//! ARITHMETIC and never a dereference, so a plan-and-validate pass is fully
//! testable on the CPU with no GPU and no allocator.
//!
//! Address map (chosen so any accidental overlap is a bug, not a coincidence):
//!
//! ```text
//! 0x1000_0000  parity buffer 0        0x2000_0000  parity buffer 1
//! 0x4000_0000  raw BF backings        0x5000_0000  raw E4 backings
//! 0x7000_0000  eq_low / contributions
//! ```

use gkr_eval_isa::bwd::coeff::lean::{
    decode_program, LeanProgram, LEAN_WORDS_PER_TERM, SOURCE_NONE,
};
use gkr_eval_isa::bwd::coeff::lean_artifact::LeanCoordinateArtifact;
use gkr_eval_isa::bwd::coeff::lean_bind::{
    LeanBoundColumn, LeanBoundWindow, LeanSourceBinding, LeanSourceSlot,
};
use gkr_eval_isa::bwd::coeff::limits::{in_scope, TermCategory, SOURCE_WINDOW_COLUMNS};
use gkr_eval_isa::bwd::coeff::model::CoefficientRecipeId;
use gkr_eval_isa::bwd::coeff::order::split_round_robin;
use gkr_eval_isa::bwd::coeff::stats::WindowFamily;
use gkr_eval_isa::bwd::coeff::ArtifactRegime;

use super::desc::{
    BWD_COEFF_ORIGIN_PROCEDURAL, BWD_COEFF_ORIGIN_READ_BASE, BWD_COEFF_ORIGIN_READ_EXT,
    BWD_COEFF_PROCEDURAL_NONE,
};
use super::lower::ResolvedBwdCoeffSourceWindow;
use super::seg_desc::{BwdSegDesc, BWD_SEG_CONST_BANK, BWD_SEG_MAX_K};
use super::seg_lower::{
    assign_class, chain_read_column, check_regions_disjoint, e4_limbs, lower_bwd_seg,
    plan_publish_scratch, static_term_work, window_columns, AnnotatedTerm, BwdSegLaunchDesc,
    BwdSegLowerError, BwdSegRoundBinding, BwdSegSetup, CoeffMode, D2Policy, ProgramMode,
    PublishRoundLayout, PublishScratchPlan, ResolvedPublishScratch, SourceClass, SourceOrigin,
    PUBLISH_WINDOW_ABSENT,
};
use crate::primitives::field::E4;
use crate::prover::gkr::backward::GkrEqSizes;
use crate::prover::gkr::forward::vm::lower::ResolvedColumn;
use crate::upstream::Field;

// ── Fixture vocabulary ───────────────────────────────────────────────────────

const PARITY0: usize = 0x1000_0000;
const PARITY1: usize = 0x2000_0000;
const BF_BACKING: usize = 0x4000_0000;
const E4_BACKING: usize = 0x5000_0000;
const RUNTIME: usize = 0x7000_0000;

const BF_BYTES: u32 = 4;
const E4_BYTES: u32 = 16;

/// Rows per round, halving. Index IS the round.
const ROWS: [usize; 6] = [128, 64, 32, 16, 8, 4];

fn bf_column(index: usize) -> ResolvedColumn {
    let base = BF_BACKING + index * 0x0010_0000;
    ResolvedColumn {
        is_e4: false,
        ptr: base as *const u8,
        matrix_base: base as *mut u8,
        stride_bytes: 1 << 20,
    }
}

fn e4_column(index: usize) -> ResolvedColumn {
    let base = E4_BACKING + index * 0x0010_0000;
    ResolvedColumn {
        is_e4: true,
        ptr: base as *const u8,
        matrix_base: base as *mut u8,
        stride_bytes: 1 << 20,
    }
}

/// A column at an explicit address — used by the alias tests.
fn column_at(address: usize, is_e4: bool, stride_bytes: u32) -> ResolvedColumn {
    ResolvedColumn {
        is_e4,
        ptr: address as *const u8,
        matrix_base: address as *mut u8,
        stride_bytes,
    }
}

fn bound(
    read: Option<ResolvedColumn>,
    backing_depth: u8,
    target_depth: u8,
    materialize: bool,
) -> ResolvedBwdCoeffSourceWindow {
    ResolvedBwdCoeffSourceWindow {
        read,
        publish: None,
        backing_depth,
        target_depth,
        materialize,
    }
}

/// One window over `columns` contiguous columns of `family`, whose columns are
/// the sources `first_source..first_source + columns`.
fn window(family: WindowFamily, first_column: usize, sources: &[u32]) -> LeanBoundWindow {
    LeanBoundWindow {
        family,
        first_column,
        columns: sources
            .iter()
            .enumerate()
            .map(|(offset, &source)| LeanBoundColumn {
                column: first_column + offset,
                source,
            })
            .collect(),
    }
}

fn base_witness(sources: &[u32]) -> LeanBoundWindow {
    window(WindowFamily::BaseLayerWitness, 0, sources)
}

fn ext_output(layer: usize, sources: &[u32]) -> LeanBoundWindow {
    window(WindowFamily::LayerOutput { layer, ext: true }, 0, sources)
}

fn virtual_setup(kind: u8, source: u32) -> LeanBoundWindow {
    window(WindowFamily::VirtualSetup { kind }, 0, &[source])
}

/// One `(window, column)` slot per source, in slot order.
fn slots(spec: &[(u8, u16)]) -> Vec<LeanSourceSlot> {
    spec.iter()
        .map(|&(window, column)| LeanSourceSlot { window, column })
        .collect()
}

/// One lean record, spelled independently of the encoder (mirrors
/// `lean.rs`'s test helper).
fn record(class: u16, coeff: u16, source_a: u16, source_b: u16) -> [u16; 4] {
    [(class << 13) | coeff, source_a, source_b, 0]
}

fn program(records: &[[u16; 4]]) -> LeanProgram {
    LeanProgram {
        words: records.iter().flatten().copied().collect(),
        term_count: records.len(),
    }
}

fn artifact(
    regime: ArtifactRegime,
    target_depth: u8,
    windows: Vec<LeanBoundWindow>,
    source_slots: Vec<LeanSourceSlot>,
    program: LeanProgram,
) -> LeanCoordinateArtifact {
    let order = (0..program.term_count as u32).collect();
    LeanCoordinateArtifact {
        layer: 0,
        regime,
        target_depth,
        order,
        program,
        binding: LeanSourceBinding {
            windows,
            source_slots,
        },
    }
}

/// The continuation fixture every round-shaped test starts from: ONE `Ext`
/// window of two columns, two `DualProduct` terms over its two sources.
fn ext_artifact() -> LeanCoordinateArtifact {
    artifact(
        ArtifactRegime::Ext,
        3,
        vec![ext_output(1, &[0, 1])],
        slots(&[(0, 0), (0, 1)]),
        program(&[record(1, 2, 0, 1), record(0, 0, 1, SOURCE_NONE)]),
    )
}

/// The same shape over a BASE window — the origin axis's other real value.
fn bf_artifact() -> LeanCoordinateArtifact {
    artifact(
        ArtifactRegime::Ext,
        3,
        vec![base_witness(&[0, 1])],
        slots(&[(0, 0), (0, 1)]),
        program(&[record(1, 2, 0, 1), record(0, 0, 1, SOURCE_NONE)]),
    )
}

fn r0_artifact() -> LeanCoordinateArtifact {
    artifact(
        ArtifactRegime::R0,
        0,
        vec![base_witness(&[0])],
        slots(&[(0, 0)]),
        program(&[record(0, 0, 0, SOURCE_NONE)]),
    )
}

/// A plan whose only round is `round`, built from one window set.
fn plan_for(
    round: usize,
    windows: &[ResolvedBwdCoeffSourceWindow],
    columns: &[usize],
) -> PublishScratchPlan {
    let empty_windows: Vec<ResolvedBwdCoeffSourceWindow> = Vec::new();
    let empty_columns: Vec<usize> = Vec::new();
    let mut window_sets: Vec<&[ResolvedBwdCoeffSourceWindow]> = Vec::new();
    let mut column_sets: Vec<&[usize]> = Vec::new();
    for index in 0..=round {
        if index == round {
            window_sets.push(windows);
            column_sets.push(columns);
        } else {
            window_sets.push(&empty_windows);
            column_sets.push(&empty_columns);
        }
    }
    plan_publish_scratch(&window_sets, &column_sets, &ROWS[..=round]).expect("a legal plan")
}

fn scratch_for(plan: PublishScratchPlan) -> ResolvedPublishScratch {
    ResolvedPublishScratch {
        parity_base: [PARITY0 as *mut u8, PARITY1 as *mut u8],
        plan,
    }
}

fn claim_point(entries: usize) -> Vec<E4> {
    (0..entries).map(|_| E4::ONE).collect()
}

fn coefficients(entries: usize) -> Vec<E4> {
    (0..entries).map(|_| E4::ONE).collect()
}

/// A round binding over `bounds`, with every runtime pointer valid and every
/// read span generous.
fn round_binding<'a>(
    round: u32,
    bounds: &'a [ResolvedBwdCoeffSourceWindow],
    read_elements: &'a [u32],
    claim: &'a [E4],
    coeffs: &'a [E4],
) -> BwdSegRoundBinding<'a> {
    BwdSegRoundBinding {
        round,
        rows: ROWS[round as usize],
        windows: bounds,
        window_read_elements: read_elements,
        claim_point: claim,
        coefficients: coeffs,
        c_init: None,
        eq_low: RUNTIME as *const E4,
        eq_sizes: GkrEqSizes::zeroed(),
        contributions: (RUNTIME + 0x0100_0000) as *mut E4,
        acc_size: ROWS[round as usize] as u32,
    }
}

/// Generous per-window readable element counts: past every pair total this
/// module can ask for.
fn generous(windows: usize) -> Vec<u32> {
    vec![u32::MAX / 2; windows]
}

fn inline_desc(setup: &BwdSegSetup) -> &BwdSegDesc {
    match &setup.desc {
        BwdSegLaunchDesc::Inline(desc) => desc,
        BwdSegLaunchDesc::ProgPtr(_) => panic!("expected the inline-program descriptor"),
    }
}

/// The one-window continuation lowering every simple test reuses:
/// `(artifact, bound-window)` at `round`, `k` lists, `d2` policy.
fn lower_one(
    artifact: &LeanCoordinateArtifact,
    round: u32,
    bound_window: ResolvedBwdCoeffSourceWindow,
    columns: usize,
    k: usize,
    d2: D2Policy,
) -> Result<BwdSegSetup, BwdSegLowerError> {
    let bounds = [bound_window];
    let scratch = scratch_for(plan_for(round as usize, &bounds, &[columns]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    let binding = round_binding(round, &bounds, &read_elements, &claim, &coeffs);
    lower_bwd_seg(
        artifact,
        &binding,
        &scratch,
        k,
        d2,
        ProgramMode::Inline,
        CoeffMode::Constant,
    )
}

// ── The class enum is the ABI authority ──────────────────────────────────────

/// [`seg_desc::BwdSegSourceRecord`]'s `class` byte is documented against these
/// five numbers and nothing enforces them there — the enum is the authority, so
/// the numbers live here.
#[test]
fn source_class_discriminants_are_the_documented_abi() {
    assert_eq!(SourceClass::BfDirect.code(), 0);
    assert_eq!(SourceClass::BfInlineD1.code(), 1);
    assert_eq!(SourceClass::BfInlineD2.code(), 2);
    assert_eq!(SourceClass::E4Direct.code(), 3);
    assert_eq!(SourceClass::ProceduralInline.code(), 4);
}

// ── The assignment matrix ────────────────────────────────────────────────────

/// Every cell of the `(origin, catch-up depth, D2 policy)` matrix, and the
/// foldability that comes with it. This is the whole per-round policy.
#[test]
fn class_assignment_covers_every_matrix_cell() {
    use D2Policy::{Inline, Materialize};
    use SourceClass::*;
    use SourceOrigin::{Bf, Procedural, E4 as E4Origin};

    let cells: &[(SourceOrigin, u8, D2Policy, SourceClass, bool)] = &[
        // BF: d0 reads raw, d1/d2 fold inline, d2-materialize and d3 publish.
        (Bf, 0, Inline, BfDirect, false),
        (Bf, 0, Materialize, BfDirect, false),
        (Bf, 1, Inline, BfInlineD1, false),
        (Bf, 1, Materialize, BfInlineD1, false),
        (Bf, 2, Inline, BfInlineD2, false),
        (Bf, 2, Materialize, E4Direct, true),
        (Bf, 3, Inline, E4Direct, true),
        (Bf, 3, Materialize, E4Direct, true),
        // E4: one chain step at every nonzero catch-up, nothing at zero.
        (E4Origin, 0, Inline, E4Direct, false),
        (E4Origin, 0, Materialize, E4Direct, false),
        (E4Origin, 1, Inline, E4Direct, true),
        (E4Origin, 1, Materialize, E4Direct, true),
        (E4Origin, 2, Inline, E4Direct, true),
        (E4Origin, 3, Inline, E4Direct, true),
        // Procedural: inline until the publish depth, then publish and chain.
        (Procedural, 0, Inline, ProceduralInline, false),
        (Procedural, 1, Inline, ProceduralInline, false),
        (Procedural, 2, Inline, ProceduralInline, false),
        (Procedural, 2, Materialize, ProceduralInline, false),
        (Procedural, 3, Inline, E4Direct, true),
        (Procedural, 3, Materialize, E4Direct, true),
    ];

    for &(origin, delta, policy, class, foldable) in cells {
        assert_eq!(
            assign_class(origin, delta, policy),
            (class, foldable),
            "{origin:?} d{delta} {policy:?}",
        );
    }
}

/// The matrix, END TO END: the class the descriptor's source record carries, the
/// window's materialize flag and the fold list all come from one decision.
#[test]
fn lowering_stamps_the_assigned_class_on_every_source() {
    let cases: &[(u32, u8, D2Policy, SourceClass, bool)] = &[
        (0, 0, D2Policy::Inline, SourceClass::BfDirect, false),
        (1, 0, D2Policy::Inline, SourceClass::BfInlineD1, false),
        (2, 0, D2Policy::Inline, SourceClass::BfInlineD2, false),
        (2, 0, D2Policy::Materialize, SourceClass::E4Direct, true),
        (3, 0, D2Policy::Inline, SourceClass::E4Direct, true),
    ];
    for &(round, backing_depth, d2, class, foldable) in cases {
        let target = round as u8;
        let setup = lower_one(
            &bf_artifact(),
            round,
            bound(Some(bf_column(0)), backing_depth, target, foldable),
            2,
            2,
            d2,
        )
        .unwrap_or_else(|error| panic!("round {round} {d2:?}: {error:?}"));
        let desc = inline_desc(&setup);
        assert_eq!(desc.num_sources, 2);
        for source in 0..2 {
            assert_eq!(
                desc.source[source].class,
                class.code(),
                "round {round} {d2:?} source {source}",
            );
        }
        assert_eq!(
            desc.window[0].materialize,
            u8::from(foldable),
            "round {round} {d2:?} materialize",
        );
        assert_eq!(
            desc.num_foldable,
            if foldable { 2 } else { 0 },
            "round {round} {d2:?} foldable sources",
        );
        assert_eq!(desc.window[0].origin, BWD_COEFF_ORIGIN_READ_BASE);
    }
}

/// The E4 and procedural rows of the matrix, end to end.
#[test]
fn lowering_stamps_the_e4_and_procedural_classes() {
    // An E4 backing already at target depth: no fold, no publish.
    let setup = lower_one(
        &ext_artifact(),
        2,
        bound(Some(e4_column(0)), 2, 2, false),
        2,
        1,
        D2Policy::Inline,
    )
    .expect("a legal E4 round");
    let desc = inline_desc(&setup);
    assert_eq!(desc.source[0].class, SourceClass::E4Direct.code());
    assert_eq!(desc.num_foldable, 0);
    assert_eq!(desc.window[0].origin, BWD_COEFF_ORIGIN_READ_EXT);

    // A procedural window below the publish depth: inline, no read backing.
    let procedural = artifact(
        ArtifactRegime::Ext,
        3,
        vec![virtual_setup(2, 0)],
        slots(&[(0, 0)]),
        program(&[record(0, 0, 0, SOURCE_NONE)]),
    );
    let setup = lower_one(
        &procedural,
        2,
        bound(None, 0, 2, false),
        1,
        1,
        D2Policy::Inline,
    )
    .expect("a legal procedural round");
    let desc = inline_desc(&setup);
    assert_eq!(desc.source[0].class, SourceClass::ProceduralInline.code());
    assert_eq!(desc.window[0].origin, BWD_COEFF_ORIGIN_PROCEDURAL);
    assert_eq!(desc.window[0].procedural_kind, 2);
    assert!(desc.window[0].read_base.is_null());
    assert_eq!(desc.num_foldable, 0);

    // At the publish depth it becomes an E4 source the prologue materializes.
    let setup = lower_one(
        &procedural,
        3,
        bound(None, 0, 3, true),
        1,
        1,
        D2Policy::Inline,
    )
    .expect("a legal procedural publish round");
    let desc = inline_desc(&setup);
    assert_eq!(desc.source[0].class, SourceClass::E4Direct.code());
    assert_eq!(desc.window[0].origin, BWD_COEFF_ORIGIN_PROCEDURAL);
    assert_eq!(desc.num_foldable, 1);
    assert_eq!(desc.fold_source[0], 0);
    assert_eq!(desc.window[0].materialize, 1);
}

/// **The landmine.** The old lowering read the ORIGIN off the compile-time
/// window family; a source the previous round materialized is physically E4 at
/// this round even though its family still says base / virtual setup. Deriving
/// from the family would refold raw data that is no longer where the fold
/// expects it.
#[test]
fn origin_comes_from_the_round_binding_not_the_compiled_family() {
    // Family says BASE, the round binding supplies an E4 backing: E4 wins, and
    // the class is the chain step, not an inline BF fold.
    // The chain step publishes again, which is the (E4, d>=1) row of the matrix.
    let setup = lower_one(
        &bf_artifact(),
        4,
        bound(Some(e4_column(0)), 3, 4, true),
        2,
        1,
        D2Policy::Inline,
    )
    .expect("a materialized base-family window is legal");
    let desc = inline_desc(&setup);
    assert_eq!(desc.window[0].origin, BWD_COEFF_ORIGIN_READ_EXT);
    assert_eq!(desc.source[0].class, SourceClass::E4Direct.code());

    // Family says VIRTUAL SETUP, the round binding supplies an E4 backing (the
    // round-3 materialization): the descriptor resolves it from DRAM, and the
    // per-round `procedural_kind` is cleared so no resolver can synthesize it.
    let procedural = artifact(
        ArtifactRegime::Ext,
        3,
        vec![virtual_setup(1, 0)],
        slots(&[(0, 0)]),
        program(&[record(0, 0, 0, SOURCE_NONE)]),
    );
    let setup = lower_one(
        &procedural,
        4,
        bound(Some(e4_column(1)), 3, 4, true),
        1,
        1,
        D2Policy::Inline,
    )
    .expect("a materialized virtual-setup window is legal");
    let desc = inline_desc(&setup);
    assert_eq!(desc.window[0].origin, BWD_COEFF_ORIGIN_READ_EXT);
    assert_eq!(desc.window[0].procedural_kind, BWD_COEFF_PROCEDURAL_NONE);
    assert_eq!(desc.source[0].class, SourceClass::E4Direct.code());

    // ...and the reverse mistake is rejected outright: a virtual-setup family
    // cannot be backed by a raw BASE matrix.
    assert_eq!(
        lower_one(
            &procedural,
            4,
            bound(Some(bf_column(1)), 3, 4, false),
            1,
            1,
            D2Policy::Inline,
        ),
        Err(BwdSegLowerError::ProceduralWindowWithMatrixRead { window: 0 }),
    );
}

// ── The K-list split ─────────────────────────────────────────────────────────

/// `list_offset` is the whole program-length story: monotone, `k + 1` live
/// entries, the last one the end of the stream, and each list exactly
/// `split_round_robin` of the committed order.
#[test]
fn k_lists_concatenate_in_round_robin_order() {
    let records: Vec<[u16; 4]> = (0..7)
        .map(|index| record(0, index as u16 % 4, index as u16 % 2, SOURCE_NONE))
        .collect();
    let artifact = artifact(
        ArtifactRegime::Ext,
        3,
        vec![ext_output(1, &[0, 1])],
        slots(&[(0, 0), (0, 1)]),
        program(&records),
    );
    let committed: Vec<usize> = (0..records.len()).collect();

    for k in [1usize, 2, 3, 7, 8] {
        let setup = lower_one(
            &artifact,
            2,
            bound(Some(e4_column(0)), 2, 2, false),
            2,
            k,
            D2Policy::Inline,
        )
        .unwrap_or_else(|error| panic!("k {k}: {error:?}"));
        let desc = inline_desc(&setup);
        assert_eq!(desc.k as usize, k);
        assert_eq!(desc.term_count as usize, records.len());

        let offsets = &desc.list_offset[..=k];
        assert!(
            offsets.windows(2).all(|pair| pair[0] <= pair[1]),
            "k {k}: offsets monotone: {offsets:?}",
        );
        assert_eq!(offsets[0], 0, "k {k}: list 0 starts at the stream head");
        assert_eq!(
            usize::from(offsets[k]),
            records.len() * LEAN_WORDS_PER_TERM,
            "k {k}: the last offset is the end of the stream",
        );
        for entry in &desc.list_offset[k + 1..] {
            assert_eq!(*entry, 0, "k {k}: entries past k stay zero");
        }

        let lists = split_round_robin(&committed, k);
        for (list, positions) in lists.iter().enumerate() {
            let lo = usize::from(offsets[list]);
            let hi = usize::from(offsets[list + 1]);
            assert_eq!(
                hi - lo,
                positions.len() * LEAN_WORDS_PER_TERM,
                "k {k} list {list}: length",
            );
            for (index, &position) in positions.iter().enumerate() {
                let at = lo + index * LEAN_WORDS_PER_TERM;
                assert_eq!(
                    &desc.program[at..at + LEAN_WORDS_PER_TERM],
                    &records[position][..],
                    "k {k} list {list} entry {index}: the committed record",
                );
            }
        }
    }
}

#[test]
fn a_list_count_outside_the_block_is_rejected() {
    for k in [0usize, BWD_SEG_MAX_K + 1] {
        assert_eq!(
            lower_one(
                &ext_artifact(),
                2,
                bound(Some(e4_column(0)), 2, 2, false),
                2,
                k,
                D2Policy::Inline,
            ),
            Err(BwdSegLowerError::InvalidListCount { k }),
        );
    }
}

// ── The publish-scratch plan ─────────────────────────────────────────────────

/// The plan's shape: a region per publishing window per round, the stride
/// `2 * rows_r * 16`, and the parity buffers sized by the MAX over the rounds
/// each one serves (not the sum) — that is what makes ping-pong two buffers
/// instead of one per round.
#[test]
fn the_plan_sizes_two_parity_buffers_by_their_worst_round() {
    let publishing = bound(Some(bf_column(0)), 0, 3, true);
    let quiet = bound(Some(e4_column(0)), 3, 3, false);
    let round3 = [publishing, quiet];
    let round4 = [bound(Some(e4_column(1)), 3, 4, true)];

    let plan = plan_publish_scratch(
        &[&[], &[], &[], &round3, &round4],
        &[&[], &[], &[], &[3, 1], &[2]],
        &ROWS[..5],
    )
    .expect("a legal plan");

    assert_eq!(plan.per_round.len(), 5);
    let stride3 = 2 * ROWS[3] * 16;
    let stride4 = 2 * ROWS[4] * 16;
    assert_eq!(plan.per_round[3].column_stride_bytes, stride3);
    assert_eq!(plan.per_round[4].column_stride_bytes, stride4);
    // Only the publishing window gets a region, and it gets one per column.
    assert_eq!(plan.per_round[3].window_base[0], 0);
    assert_eq!(plan.per_round[3].window_base[1], PUBLISH_WINDOW_ABSENT);
    assert_eq!(plan.per_round[3].bytes, 3 * stride3);
    assert_eq!(plan.per_round[4].window_base[0], 0);
    assert_eq!(plan.per_round[4].bytes, 2 * stride4);
    // Rounds 3 and 4 land in different parities; a round with nothing to publish
    // costs nothing.
    assert_eq!(
        plan.bytes_per_parity,
        [2 * stride4, 3 * stride3],
        "round 4 -> parity 0, round 3 -> parity 1",
    );
    assert_eq!(plan.total_bytes, 2 * stride4 + 3 * stride3);
}

/// Two publishing windows in one round get DISJOINT regions, packed in window
/// order.
#[test]
fn one_round_packs_its_publishing_windows_disjointly() {
    let windows = [
        bound(Some(bf_column(0)), 0, 3, true),
        bound(Some(bf_column(1)), 0, 3, true),
    ];
    let plan = plan_for(3, &windows, &[2, 5]);
    let stride = 2 * ROWS[3] * 16;
    assert_eq!(plan.per_round[3].window_base, vec![0, 2 * stride]);
    assert_eq!(plan.per_round[3].bytes, 7 * stride);
}

#[test]
fn the_plan_rejects_a_shape_that_does_not_line_up() {
    let windows = [bound(Some(bf_column(0)), 0, 3, true)];
    assert_eq!(
        plan_publish_scratch(&[&windows], &[&[1, 2]], &[ROWS[3]]),
        Err(BwdSegLowerError::PlanShapeMismatch {
            round: 0,
            windows: 1,
            entries: 2,
        }),
    );
    assert_eq!(
        plan_publish_scratch(&[&windows], &[&[1]], &[]),
        Err(BwdSegLowerError::PlanRoundCountMismatch {
            windows: 1,
            columns: 1,
            rows: 0,
        }),
    );
}

/// The disjointness checker itself, on input the planner cannot produce — the
/// planner packs with a cursor, so the check only ever fires for a plan built
/// some other way, and it is still what makes "disjoint" a checked property
/// rather than a comment.
#[test]
fn overlapping_regions_are_reported() {
    assert_eq!(
        check_regions_disjoint(&[(0, 0, 64), (1, 32, 96)]),
        Err(BwdSegLowerError::UnsafePublishAlias {
            window: 1,
            other: 0,
        }),
    );
    assert_eq!(
        check_regions_disjoint(&[(0, 0, 64), (1, 64, 96)]),
        Ok(()),
        "abutting regions do not overlap",
    );
}

// ── Pointer and span validation ──────────────────────────────────────────────

/// A publish region and a raw input may not overlap: a first access writes both
/// endpoint halves through the publish base, and a write racing a read of the
/// same bytes is a correctness bug the kernel cannot see.
#[test]
fn a_publish_region_overlapping_a_raw_input_is_rejected() {
    // Window 0 publishes at the head of parity 1; window 1 reads from inside
    // that very region.
    let bounds = [
        bound(Some(bf_column(0)), 0, 3, true),
        bound(Some(column_at(PARITY1 + 64, true, E4_BYTES)), 3, 3, false),
    ];
    let scratch = scratch_for(plan_for(3, &bounds, &[1, 1]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(2);
    let artifact = artifact(
        ArtifactRegime::Ext,
        3,
        vec![base_witness(&[0]), ext_output(1, &[1])],
        slots(&[(0, 0), (1, 0)]),
        program(&[record(1, 2, 0, 1)]),
    );
    assert_eq!(
        lower_bwd_seg(
            &artifact,
            &round_binding(3, &bounds, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::UnsafePublishAlias {
            window: 0,
            other: 1,
        }),
    );
}

/// The buffer this round publishes into is off limits to reads WHOLESALE, not
/// just at the regions this round happens to use: its stale tail is a previous
/// same-parity round's publishes, and the prologue owns the buffer for the
/// launch.
#[test]
fn a_read_inside_the_write_parity_buffer_is_rejected() {
    // Round 1 (parity 1, 64 rows) sizes parity 1 far past what round 3 (parity
    // 1, 8 rows) uses, so this read is inside the buffer and outside every
    // round-3 region.
    let round1 = [bound(Some(bf_column(0)), 0, 1, true)];
    let round3 = [
        bound(Some(bf_column(0)), 0, 3, true),
        bound(Some(column_at(PARITY1 + 1024, true, E4_BYTES)), 3, 3, false),
    ];
    let plan = plan_publish_scratch(
        &[&[], &round1[..], &[], &round3[..]],
        &[&[], &[1], &[], &[1, 1]],
        &ROWS[..4],
    )
    .expect("a legal plan");
    assert!(plan.bytes_per_parity[1] > plan.per_round[3].bytes);
    let scratch = scratch_for(plan);
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(2);
    let artifact = artifact(
        ArtifactRegime::Ext,
        3,
        vec![base_witness(&[0]), ext_output(1, &[1])],
        slots(&[(0, 0), (1, 0)]),
        program(&[record(1, 2, 0, 1)]),
    );
    assert_eq!(
        lower_bwd_seg(
            &artifact,
            &round_binding(3, &round3, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::ReadAliasesPublishBuffer { window: 1 }),
    );
}

#[test]
fn parity_buffers_that_overlap_are_rejected() {
    let bounds = [bound(Some(bf_column(0)), 0, 3, true)];
    let mut scratch = scratch_for(plan_for(3, &bounds, &[1]));
    // Both parities on one allocation: round 4's chain would read what round 3
    // is still writing.
    scratch.parity_base[0] = PARITY1 as *mut u8;
    scratch.plan.bytes_per_parity[0] = scratch.plan.bytes_per_parity[1];
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    let binding = round_binding(3, &bounds, &read_elements, &claim, &coeffs);
    assert_eq!(
        lower_bwd_seg(
            &bf_artifact(),
            &binding,
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::ParityBuffersAlias),
    );
}

/// The span totals are PAIR totals — both endpoint halves — so the boundary is
/// exactly one element below `2 * rows_r * 2^delta`. The off-by-one-HALF
/// regression (checking one endpoint's inputs) is the known failure shape, so
/// each case is pinned at `needed - 1`.
#[test]
fn a_read_span_one_element_short_is_rejected() {
    let cases: &[(&str, u32, u8, u8, bool, bool, u32)] = &[
        // (what, round, backing_depth, target_depth, read is e4, publishes, needed)
        ("bf d3 pyramid", 3, 0, 3, false, true, 16 * ROWS[3] as u32),
        (
            "bf d2 materialize",
            2,
            0,
            2,
            false,
            true,
            8 * ROWS[2] as u32,
        ),
        ("bf d1 inline", 1, 0, 1, false, false, 4 * ROWS[1] as u32),
        ("e4 chain step", 4, 3, 4, true, true, 4 * ROWS[4] as u32),
    ];
    for &(what, round, backing_depth, target_depth, is_e4, publishes, needed) in cases {
        let read = if is_e4 { e4_column(0) } else { bf_column(0) };
        let bounds = [bound(Some(read), backing_depth, target_depth, publishes)];
        let scratch = scratch_for(plan_for(round as usize, &bounds, &[2]));
        let claim = claim_point(8);
        let coeffs = coefficients(4);
        let artifact = if is_e4 { ext_artifact() } else { bf_artifact() };

        let short = [needed - 1];
        let binding = round_binding(round, &bounds, &short, &claim, &coeffs);
        assert_eq!(
            lower_bwd_seg(
                &artifact,
                &binding,
                &scratch,
                1,
                D2Policy::Materialize,
                ProgramMode::Inline,
                CoeffMode::Constant,
            ),
            Err(BwdSegLowerError::ReadSpanOverflow {
                window: 0,
                needed,
                have: needed - 1,
            }),
            "{what}: one element short must be rejected",
        );

        let exact = [needed];
        let binding = round_binding(round, &bounds, &exact, &claim, &coeffs);
        assert!(
            lower_bwd_seg(
                &artifact,
                &binding,
                &scratch,
                1,
                D2Policy::Materialize,
                ProgramMode::Inline,
                CoeffMode::Constant,
            )
            .is_ok(),
            "{what}: the exact pair total must be accepted",
        );
    }
}

// ── The two-round chain ──────────────────────────────────────────────────────

/// **d3 -> d4 ping-pong.** Round 3 materializes a source into parity 1; round 4
/// folds it one step further, reading round 3's region and publishing into
/// parity 0. A single round cannot prove this — the read base of one lowering
/// has to BE the publish base of the other.
#[test]
fn the_d3_to_d4_chain_reads_the_previous_round_publish() {
    for procedural in [false, true] {
        let (artifact, family_read) = if procedural {
            (
                artifact(
                    ArtifactRegime::Ext,
                    3,
                    vec![virtual_setup(0, 0)],
                    slots(&[(0, 0)]),
                    program(&[record(0, 0, 0, SOURCE_NONE)]),
                ),
                None,
            )
        } else {
            (
                artifact(
                    ArtifactRegime::Ext,
                    3,
                    vec![base_witness(&[0])],
                    slots(&[(0, 0)]),
                    program(&[record(0, 0, 0, SOURCE_NONE)]),
                ),
                Some(bf_column(0)),
            )
        };

        // ONE plan covering both rounds — the planner owns the whole sequence.
        let round3 = [bound(family_read, 0, 3, true)];
        let plan = plan_publish_scratch(
            &[&[], &[], &[], &round3[..], &round3[..]],
            &[&[], &[], &[], &[1], &[1]],
            &ROWS[..5],
        )
        .expect("a legal two-round plan");
        let scratch = scratch_for(plan);
        let claim = claim_point(8);
        let coeffs = coefficients(4);
        let read_elements = generous(1);

        let third = lower_bwd_seg(
            &artifact,
            &round_binding(3, &round3, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        )
        .unwrap_or_else(|error| panic!("procedural {procedural}: round 3: {error:?}"));
        let third_desc = inline_desc(&third);
        let published = third_desc.window[0].publish_base;
        assert_eq!(
            published as usize, PARITY1,
            "procedural {procedural}: round 3 publishes into parity 1",
        );
        assert_eq!(
            third_desc.window[0].publish_stride_bytes as usize,
            2 * ROWS[3] * 16,
        );
        assert_eq!(third_desc.num_foldable, 1);

        // Round 4's read IS round 3's publish region — and the helper the
        // caller uses to build it agrees.
        let (chain_ptr, chain_stride) =
            chain_read_column(&scratch, 4, 0).expect("round 3 published this window");
        assert_eq!(chain_ptr as usize, published as usize);
        let round4 = [bound(
            Some(column_at(chain_ptr as usize, true, chain_stride)),
            3,
            4,
            true,
        )];
        let fourth = lower_bwd_seg(
            &artifact,
            &round_binding(4, &round4, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        )
        .unwrap_or_else(|error| panic!("procedural {procedural}: round 4: {error:?}"));
        let fourth_desc = inline_desc(&fourth);
        assert_eq!(
            fourth_desc.window[0].read_base as usize, published as usize,
            "procedural {procedural}: round 4 chains off round 3's publish",
        );
        assert_eq!(
            fourth_desc.window[0].read_stride_bytes as usize,
            2 * ROWS[3] * 16,
            "the READ stride is the PREVIOUS round's",
        );
        assert_eq!(
            fourth_desc.window[0].publish_base as usize, PARITY0,
            "procedural {procedural}: round 4 publishes into the other parity",
        );
        assert_eq!(
            fourth_desc.window[0].publish_stride_bytes as usize,
            2 * ROWS[4] * 16,
            "the WRITE stride is THIS round's",
        );
        assert_eq!(fourth_desc.source[0].class, SourceClass::E4Direct.code());
        assert_eq!(fourth_desc.window[0].origin, BWD_COEFF_ORIGIN_READ_EXT);
    }
}

/// A chain read that points anywhere OTHER than the previous round's published
/// region is rejected: the parity rule is enforced, not assumed.
#[test]
fn a_chain_read_off_the_previous_publish_region_is_rejected() {
    let round3 = [bound(Some(bf_column(0)), 0, 3, true)];
    let plan = plan_publish_scratch(
        &[&[], &[], &[], &round3[..], &round3[..]],
        &[&[], &[], &[], &[1], &[1]],
        &ROWS[..5],
    )
    .expect("a legal two-round plan");
    let scratch = scratch_for(plan);
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    // The right parity, the wrong offset.
    let round4 = [bound(
        Some(column_at(PARITY1 + 16, true, (2 * ROWS[3] * 16) as u32)),
        3,
        4,
        true,
    )];
    assert_eq!(
        lower_bwd_seg(
            &bf_artifact(),
            &round_binding(4, &round4, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::ChainReadNotPriorPublish { window: 0 }),
    );
}

// ── One rejection per precondition ───────────────────────────────────────────

#[test]
fn an_r0_program_lowered_off_round_zero_is_rejected() {
    assert_eq!(
        lower_one(
            &r0_artifact(),
            1,
            bound(Some(bf_column(0)), 0, 1, false),
            1,
            1,
            D2Policy::Inline,
        ),
        Err(BwdSegLowerError::R0RoundMismatch { round: 1 }),
    );
}

/// R0 lowering DROPS the spine's scalar addends, so seeding one would
/// double-count them — the same rule the CPU oracle enforces.
#[test]
fn an_r0_program_carrying_a_c_init_is_rejected() {
    let artifact = r0_artifact();
    let bounds = [bound(Some(bf_column(0)), 0, 0, false)];
    let scratch = scratch_for(plan_for(0, &bounds, &[1]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    let mut binding = round_binding(0, &bounds, &read_elements, &claim, &coeffs);
    binding.c_init = Some(CoefficientRecipeId::ONE);
    assert_eq!(
        lower_bwd_seg(
            &artifact,
            &binding,
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::R0CarriesCInit {
            id: CoefficientRecipeId::ONE,
        }),
    );
}

/// A `c_init` resolves against the RESERVED-INCLUSIVE payload, and lands in the
/// descriptor as E4 limbs rather than a recipe index.
#[test]
fn c_init_resolves_to_e4_limbs() {
    let artifact = ext_artifact();
    let bounds = [bound(Some(e4_column(0)), 2, 2, false)];
    let scratch = scratch_for(plan_for(2, &bounds, &[2]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);

    // Absent: the seed is the additive identity, all-zero limbs.
    let plain = lower_bwd_seg(
        &artifact,
        &round_binding(2, &bounds, &read_elements, &claim, &coeffs),
        &scratch,
        1,
        D2Policy::Inline,
        ProgramMode::Inline,
        CoeffMode::Constant,
    )
    .expect("a legal round");
    assert_eq!(inline_desc(&plain).c_init, [0; 4]);

    // The reserved `-1` literal is materialized at the bank head, so it
    // resolves exactly like a banked id.
    let mut seeded = round_binding(2, &bounds, &read_elements, &claim, &coeffs);
    seeded.c_init = Some(CoefficientRecipeId::NEG_ONE);
    let setup = lower_bwd_seg(
        &artifact,
        &seeded,
        &scratch,
        1,
        D2Policy::Inline,
        ProgramMode::Inline,
        CoeffMode::Constant,
    )
    .expect("a legal round");
    let limbs = inline_desc(&setup).c_init;
    assert_eq!(limbs, e4_limbs(E4::MINUS_ONE));
    assert_eq!(limbs, e4_limbs(setup.coefficients[1]));
    assert_ne!(limbs, [0; 4], "the seed must be observable");

    // An id past the payload has no value to resolve to.
    let mut past = round_binding(2, &bounds, &read_elements, &claim, &coeffs);
    let index = (CoefficientRecipeId::RESERVED + coeffs.len() as u32) as u32;
    past.c_init = Some(CoefficientRecipeId(index));
    assert_eq!(
        lower_bwd_seg(
            &artifact,
            &past,
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::InvalidCInit { index }),
    );
}

#[test]
fn a_window_target_depth_that_is_not_the_round_is_rejected() {
    assert_eq!(
        lower_one(
            &ext_artifact(),
            2,
            bound(Some(e4_column(0)), 1, 1, false),
            2,
            1,
            D2Policy::Inline,
        ),
        Err(BwdSegLowerError::WindowTargetDepthMismatch {
            window: 0,
            round: 2,
            target_depth: 1,
        }),
    );
}

/// The runtime factor bank holds the depth-one pair and ONE depth-`fold_depth`
/// table, so a catch-up of two at round three has no weights.
#[test]
fn a_catch_up_the_factor_bank_cannot_weight_is_rejected() {
    assert_eq!(
        lower_one(
            &ext_artifact(),
            3,
            bound(Some(e4_column(0)), 1, 3, true),
            2,
            1,
            D2Policy::Inline,
        ),
        Err(BwdSegLowerError::UnsupportedFoldDelta {
            window: 0,
            delta: 2,
            fold_depth: 3,
        }),
    );
    // A backing DEEPER than its target is not a catch-up at all.
    assert_eq!(
        lower_one(
            &ext_artifact(),
            2,
            bound(Some(e4_column(0)), 3, 2, false),
            2,
            1,
            D2Policy::Inline,
        ),
        Err(BwdSegLowerError::InvalidDepths {
            window: 0,
            backing_depth: 3,
            target_depth: 2,
        }),
    );
}

/// The publish policy is lowering's, and a round binding that disagrees with it
/// has a scratch plan that does not match the classes — so it is a rejection,
/// never a silent override.
#[test]
fn a_materialize_flag_that_disagrees_with_the_policy_is_rejected() {
    assert_eq!(
        lower_one(
            &bf_artifact(),
            3,
            bound(Some(bf_column(0)), 0, 3, false),
            2,
            1,
            D2Policy::Inline,
        ),
        Err(BwdSegLowerError::MaterializePolicyMismatch {
            window: 0,
            declared: false,
            derived: true,
        }),
    );
    assert_eq!(
        lower_one(
            &bf_artifact(),
            1,
            bound(Some(bf_column(0)), 0, 1, true),
            2,
            1,
            D2Policy::Inline,
        ),
        Err(BwdSegLowerError::MaterializePolicyMismatch {
            window: 0,
            declared: true,
            derived: false,
        }),
    );
}

/// Publish geometry belongs to the scratch plan: a caller-supplied publish
/// backing would be silently ignored, so it is refused instead.
#[test]
fn a_caller_supplied_publish_backing_is_rejected() {
    let mut bound_window = bound(Some(bf_column(0)), 0, 3, true);
    bound_window.publish = Some(e4_column(3));
    assert_eq!(
        lower_one(&bf_artifact(), 3, bound_window, 2, 1, D2Policy::Inline),
        Err(BwdSegLowerError::UnexpectedPublishBacking { window: 0 }),
    );
}

#[test]
fn a_matrix_window_without_a_read_backing_is_rejected() {
    assert_eq!(
        lower_one(
            &bf_artifact(),
            1,
            bound(None, 0, 1, false),
            2,
            1,
            D2Policy::Inline,
        ),
        Err(BwdSegLowerError::MissingReadBacking { window: 0 }),
    );
}

#[test]
fn a_null_or_zero_stride_backing_is_rejected() {
    assert_eq!(
        lower_one(
            &bf_artifact(),
            1,
            bound(Some(column_at(0, false, BF_BYTES)), 0, 1, false),
            2,
            1,
            D2Policy::Inline,
        ),
        Err(BwdSegLowerError::NullWindowGeometry { window: 0 }),
    );
    assert_eq!(
        lower_one(
            &bf_artifact(),
            1,
            bound(Some(column_at(BF_BACKING, false, 0)), 0, 1, false),
            2,
            1,
            D2Policy::Inline,
        ),
        Err(BwdSegLowerError::NullWindowGeometry { window: 0 }),
    );
}

#[test]
fn a_stride_that_is_not_a_whole_number_of_elements_is_rejected() {
    assert_eq!(
        lower_one(
            &ext_artifact(),
            1,
            bound(Some(column_at(E4_BACKING, true, 20)), 1, 1, false),
            2,
            1,
            D2Policy::Inline,
        ),
        Err(BwdSegLowerError::WindowStrideMismatch {
            window: 0,
            is_e4: true,
            stride_bytes: 20,
        }),
    );
}

/// A procedural value comes from the row, so the resolver ignores the column
/// coordinate: every column past the first would silently resolve to column
/// zero.
#[test]
fn a_multi_column_procedural_window_is_rejected() {
    let artifact = artifact(
        ArtifactRegime::Ext,
        3,
        vec![window(WindowFamily::VirtualSetup { kind: 0 }, 0, &[0, 1])],
        slots(&[(0, 0), (0, 1)]),
        program(&[record(1, 2, 0, 1)]),
    );
    assert_eq!(
        lower_one(
            &artifact,
            1,
            bound(None, 0, 1, false),
            2,
            1,
            D2Policy::Inline,
        ),
        Err(BwdSegLowerError::MultiColumnProceduralWindow {
            window: 0,
            columns: 2,
        }),
    );
}

#[test]
fn an_unknown_procedural_kind_is_rejected() {
    let artifact = artifact(
        ArtifactRegime::Ext,
        3,
        vec![virtual_setup(4, 0)],
        slots(&[(0, 0)]),
        program(&[record(0, 0, 0, SOURCE_NONE)]),
    );
    assert_eq!(
        lower_one(
            &artifact,
            1,
            bound(None, 0, 1, false),
            1,
            1,
            D2Policy::Inline,
        ),
        Err(BwdSegLowerError::UnknownProceduralKind { window: 0, kind: 4 }),
    );
}

#[test]
fn a_window_wider_than_its_coordinate_is_rejected() {
    let wide: Vec<u32> = (0..2).collect();
    let mut window = base_witness(&wide);
    window.columns[1].column = SOURCE_WINDOW_COLUMNS;
    let artifact = artifact(
        ArtifactRegime::Ext,
        3,
        vec![window],
        slots(&[(0, 0), (0, 1)]),
        program(&[record(1, 2, 0, 1)]),
    );
    assert_eq!(
        window_columns(&artifact.binding),
        Err(BwdSegLowerError::WindowColumnOverflow {
            window: 0,
            offset: SOURCE_WINDOW_COLUMNS,
        }),
    );
}

#[test]
fn a_bound_window_count_that_is_not_the_compiled_one_is_rejected() {
    let artifact = ext_artifact();
    let bounds: [ResolvedBwdCoeffSourceWindow; 2] = [
        bound(Some(e4_column(0)), 2, 2, false),
        bound(Some(e4_column(1)), 2, 2, false),
    ];
    let scratch = scratch_for(plan_for(2, &bounds, &[2, 2]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(2);
    assert_eq!(
        lower_bwd_seg(
            &artifact,
            &round_binding(2, &bounds, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::SourceWindowCountMismatch {
            compiled: 1,
            bound: 2,
        }),
    );
}

#[test]
fn a_read_element_count_that_does_not_cover_every_window_is_rejected() {
    let artifact = ext_artifact();
    let bounds = [bound(Some(e4_column(0)), 2, 2, false)];
    let scratch = scratch_for(plan_for(2, &bounds, &[2]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    assert_eq!(
        lower_bwd_seg(
            &artifact,
            &round_binding(2, &bounds, &[], &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::ReadElementCountMismatch {
            compiled: 1,
            bound: 0,
        }),
    );
}

/// The kernel indexes the bank with no bound of its own, so the payload must
/// COVER the largest id the stream names.
#[test]
fn a_coefficient_id_past_the_payload_is_rejected() {
    let artifact = artifact(
        ArtifactRegime::Ext,
        3,
        vec![ext_output(1, &[0])],
        slots(&[(0, 0)]),
        program(&[record(0, 9, 0, SOURCE_NONE)]),
    );
    let bounds = [bound(Some(e4_column(0)), 2, 2, false)];
    let scratch = scratch_for(plan_for(2, &bounds, &[1]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    assert_eq!(
        lower_bwd_seg(
            &artifact,
            &round_binding(2, &bounds, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::CoefficientIndexPastBank {
            index: 9,
            entries: CoefficientRecipeId::RESERVED as usize + 4,
        }),
    );
}

#[test]
fn a_source_slot_past_the_source_table_is_rejected() {
    let artifact = artifact(
        ArtifactRegime::Ext,
        3,
        vec![ext_output(1, &[0])],
        slots(&[(0, 0)]),
        program(&[record(0, 0, 3, SOURCE_NONE)]),
    );
    assert_eq!(
        lower_one(
            &artifact,
            2,
            bound(Some(e4_column(0)), 2, 2, false),
            1,
            1,
            D2Policy::Inline,
        ),
        Err(BwdSegLowerError::SourceSlotOutOfRange { term: 0, slot: 3 }),
    );
}

#[test]
fn a_source_naming_a_window_or_column_it_cannot_have_is_rejected() {
    let past_window = artifact(
        ArtifactRegime::Ext,
        3,
        vec![ext_output(1, &[0])],
        slots(&[(1, 0)]),
        program(&[record(0, 0, 0, SOURCE_NONE)]),
    );
    assert_eq!(
        lower_one(
            &past_window,
            2,
            bound(Some(e4_column(0)), 2, 2, false),
            1,
            1,
            D2Policy::Inline,
        ),
        Err(BwdSegLowerError::SourceWindowOutOfRange {
            source: 0,
            window: 1,
        }),
    );
    let past_column = artifact(
        ArtifactRegime::Ext,
        3,
        vec![ext_output(1, &[0])],
        slots(&[(0, 4)]),
        program(&[record(0, 0, 0, SOURCE_NONE)]),
    );
    assert_eq!(
        lower_one(
            &past_column,
            2,
            bound(Some(e4_column(0)), 2, 2, false),
            1,
            1,
            D2Policy::Inline,
        ),
        Err(BwdSegLowerError::SourceColumnOutOfWindow {
            source: 0,
            window: 0,
            column: 4,
        }),
    );
}

#[test]
fn a_null_runtime_pointer_is_rejected() {
    let artifact = ext_artifact();
    let bounds = [bound(Some(e4_column(0)), 2, 2, false)];
    let scratch = scratch_for(plan_for(2, &bounds, &[2]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    for what in ["eq_low", "contributions"] {
        let mut binding = round_binding(2, &bounds, &read_elements, &claim, &coeffs);
        match what {
            "eq_low" => binding.eq_low = std::ptr::null(),
            _ => binding.contributions = std::ptr::null_mut(),
        }
        assert_eq!(
            lower_bwd_seg(
                &artifact,
                &binding,
                &scratch,
                1,
                D2Policy::Inline,
                ProgramMode::Inline,
                CoeffMode::Constant,
            ),
            Err(BwdSegLowerError::NullRuntimePointer { what }),
        );
    }
}

/// The fold prologue weights a catch-up with the challenges of rounds
/// `[round - delta, round)`, so the claim point has to reach `round - 1`.
#[test]
fn a_claim_point_shorter_than_the_round_is_rejected() {
    let artifact = ext_artifact();
    let bounds = [bound(Some(e4_column(0)), 2, 2, false)];
    let scratch = scratch_for(plan_for(2, &bounds, &[2]));
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    let short = claim_point(1);
    assert_eq!(
        lower_bwd_seg(
            &artifact,
            &round_binding(2, &bounds, &read_elements, &short, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::ClaimPointTooShort {
            round: 2,
            entries: 1,
        }),
    );
}

/// `logical_rows` is both the row count and the contribution half-stride; the
/// descriptor carries ONE field, so the two inputs must agree.
#[test]
fn an_acc_size_that_is_not_the_row_count_is_rejected() {
    let artifact = ext_artifact();
    let bounds = [bound(Some(e4_column(0)), 2, 2, false)];
    let scratch = scratch_for(plan_for(2, &bounds, &[2]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    let mut binding = round_binding(2, &bounds, &read_elements, &claim, &coeffs);
    binding.acc_size = ROWS[2] as u32 + 1;
    assert_eq!(
        lower_bwd_seg(
            &artifact,
            &binding,
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::AccSizeRowsMismatch {
            rows: ROWS[2],
            acc_size: ROWS[2] as u32 + 1,
        }),
    );
}

/// The inline family embeds the program by value, so a program past the array
/// is a rejection there and legal under the device-pointer family.
#[test]
fn a_program_past_the_inline_array_is_rejected_only_inline() {
    let records: Vec<[u16; 4]> = (0..2_000).map(|_| record(0, 0, 0, SOURCE_NONE)).collect();
    let artifact = artifact(
        ArtifactRegime::Ext,
        3,
        vec![ext_output(1, &[0])],
        slots(&[(0, 0)]),
        program(&records),
    );
    let bounds = [bound(Some(e4_column(0)), 2, 2, false)];
    let scratch = scratch_for(plan_for(2, &bounds, &[1]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    let words = records.len() * LEAN_WORDS_PER_TERM;
    assert_eq!(
        lower_bwd_seg(
            &artifact,
            &round_binding(2, &bounds, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::ProgramOverflow {
            words,
            cap: gkr_eval_isa::bwd::coeff::limits::LEAN_DESCRIPTOR_PROGRAM_WORDS,
        }),
    );
    let setup = lower_bwd_seg(
        &artifact,
        &round_binding(2, &bounds, &read_elements, &claim, &coeffs),
        &scratch,
        1,
        D2Policy::Inline,
        ProgramMode::DevPtr,
        CoeffMode::Constant,
    )
    .expect("the device-program family carries any length");
    match &setup.desc {
        BwdSegLaunchDesc::ProgPtr(desc) => {
            assert!(desc.program.is_null(), "the caller patches the pointer");
            assert_eq!(desc.program_words as usize, words);
            assert_eq!(setup.program_words.len(), words);
        }
        BwdSegLaunchDesc::Inline(_) => panic!("expected the progptr descriptor"),
    }
}

// ── Coefficient payload and modes ────────────────────────────────────────────

/// RR ruling 2026-07-27: the payload is RESERVED-INCLUSIVE — the kernel indexes
/// `bank[coeff_idx]` with no offset and no branch, so lowering materializes the
/// two literals at the head.
#[test]
fn the_coefficient_payload_materializes_the_reserved_literals() {
    let recipes = vec![E4::TWO, E4::ZERO, E4::ONE];
    let artifact = ext_artifact();
    let bounds = [bound(Some(e4_column(0)), 2, 2, false)];
    let scratch = scratch_for(plan_for(2, &bounds, &[2]));
    let claim = claim_point(8);
    let read_elements = generous(1);
    let setup = lower_bwd_seg(
        &artifact,
        &round_binding(2, &bounds, &read_elements, &claim, &recipes),
        &scratch,
        1,
        D2Policy::Inline,
        ProgramMode::Inline,
        CoeffMode::Constant,
    )
    .expect("a legal round");
    assert_eq!(setup.coefficients.len(), 2 + recipes.len());
    assert_eq!(setup.coefficients[0], E4::ONE);
    assert_eq!(setup.coefficients[1], E4::MINUS_ONE);
    assert_eq!(
        setup.coefficients[1],
        CoefficientRecipeId::NEG_ONE
            .literal()
            .expect("a reserved literal"),
        "the materialized head is the ISA's own literal",
    );
    assert_eq!(&setup.coefficients[2..], &recipes[..]);
    let desc = inline_desc(&setup);
    assert_eq!(desc.n_coefficients as usize, 2 + recipes.len());
    assert!(
        desc.coefficients.is_null(),
        "the constant loader reads the symbol; the pointer stays null",
    );
    // The claim point travels as an upload payload and NEVER into the desc.
    assert_eq!(setup.claim_point, claim);
    assert!(
        setup.program_words.is_empty(),
        "inline mode uploads nothing"
    );
}

/// The constant bank is sized from the census (2 + 1,138); a payload past it
/// cannot be uploaded to the symbol.
#[test]
fn a_payload_past_the_constant_bank_is_rejected() {
    let recipes = coefficients(BWD_SEG_CONST_BANK - 1);
    let artifact = ext_artifact();
    let bounds = [bound(Some(e4_column(0)), 2, 2, false)];
    let scratch = scratch_for(plan_for(2, &bounds, &[2]));
    let claim = claim_point(8);
    let read_elements = generous(1);
    assert_eq!(
        lower_bwd_seg(
            &artifact,
            &round_binding(2, &bounds, &read_elements, &claim, &recipes),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::CoefficientBankOverflow {
            coefficients: BWD_SEG_CONST_BANK + 1,
            cap: BWD_SEG_CONST_BANK,
        }),
    );
    // The corpus maximum fits with slack, which is the whole point of the pin.
    let census = coefficients(in_scope::MAX_COEFFICIENT_RECIPES);
    assert!(lower_bwd_seg(
        &artifact,
        &round_binding(2, &bounds, &read_elements, &claim, &census),
        &scratch,
        1,
        D2Policy::Inline,
        ProgramMode::Inline,
        CoeffMode::Constant,
    )
    .is_ok());
}

// ── Fold order and work stats ────────────────────────────────────────────────

/// §7's performance contract: the sources the eval loop touches EARLIEST are
/// folded LAST, so they are the warmest in L1 when eval starts.
#[test]
fn the_fold_list_is_reverse_first_touch_order() {
    // Three sources of one publishing window, first touched in the order
    // 2, 0, 1 — so the fold order is its reverse.
    let artifact = artifact(
        ArtifactRegime::Ext,
        3,
        vec![base_witness(&[0, 1, 2])],
        slots(&[(0, 0), (0, 1), (0, 2)]),
        program(&[
            record(0, 0, 2, SOURCE_NONE),
            record(0, 0, 0, SOURCE_NONE),
            record(0, 0, 1, SOURCE_NONE),
        ]),
    );
    let setup = lower_one(
        &artifact,
        3,
        bound(Some(bf_column(0)), 0, 3, true),
        3,
        1,
        D2Policy::Inline,
    )
    .expect("a legal publishing round");
    let desc = inline_desc(&setup);
    assert_eq!(desc.num_foldable, 3);
    assert_eq!(
        &desc.fold_source[..3],
        &[1u16, 0, 2],
        "latest first touch folded first, earliest folded last",
    );
    for entry in &desc.fold_source[3..] {
        assert_eq!(*entry, 0);
    }
}

/// The documented static cost model, one case per rule.
#[test]
fn static_term_work_prices_the_documented_model() {
    let term = |category, operands| AnnotatedTerm { category, operands };
    assert_eq!(
        static_term_work(&term(
            TermCategory::C0LinearE4,
            [Some(SourceClass::E4Direct), None]
        )),
        2,
    );
    assert_eq!(
        static_term_work(&term(
            TermCategory::C2ProductE4E4,
            [Some(SourceClass::E4Direct), Some(SourceClass::E4Direct)]
        )),
        6,
    );
    assert_eq!(
        static_term_work(&term(
            TermCategory::DualProductE4,
            [Some(SourceClass::E4Direct), Some(SourceClass::E4Direct)]
        )),
        10,
    );
    // Inline operands add their resolution cost, per operand.
    assert_eq!(
        static_term_work(&term(
            TermCategory::C0LinearBf,
            [Some(SourceClass::BfInlineD1), None]
        )),
        2 + 4,
    );
    assert_eq!(
        static_term_work(&term(
            TermCategory::C2ProductBfBf,
            [Some(SourceClass::BfInlineD2), Some(SourceClass::BfInlineD2)]
        )),
        6 + 10 + 10,
    );
    assert_eq!(
        static_term_work(&term(
            TermCategory::C2ProductBfE4,
            [
                Some(SourceClass::ProceduralInline),
                Some(SourceClass::E4Direct)
            ]
        )),
        6 + 3,
    );
    assert_eq!(
        static_term_work(&term(
            TermCategory::C0LinearBf,
            [Some(SourceClass::BfDirect), None]
        )),
        2,
        "a direct read costs nothing beyond the term",
    );
}

/// The per-launch stats are over the K LISTS, so an imbalanced split shows up
/// as a ratio above one.
#[test]
fn list_work_stats_measure_the_split() {
    // Four DualProduct terms over inline-D1 BF operands at k = 2: perfectly
    // balanced, ratio exactly one.
    let artifact = artifact(
        ArtifactRegime::Ext,
        3,
        vec![base_witness(&[0, 1])],
        slots(&[(0, 0), (0, 1)]),
        program(&[
            record(1, 0, 0, 1),
            record(1, 0, 0, 1),
            record(1, 0, 0, 1),
            record(1, 0, 0, 1),
        ]),
    );
    let per_term = 10 + 4 + 4;
    let balanced = lower_one(
        &artifact,
        1,
        bound(Some(bf_column(0)), 0, 1, false),
        2,
        2,
        D2Policy::Inline,
    )
    .expect("a legal round");
    assert_eq!(balanced.work.max_work, 2 * per_term);
    assert_eq!(balanced.work.mean_work, (2 * per_term) as f64);
    assert_eq!(balanced.work.max_over_mean, 1.0);

    // At k = 3 the lists are 2/1/1 and the ratio is 1.5.
    let skewed = lower_one(
        &artifact,
        1,
        bound(Some(bf_column(0)), 0, 1, false),
        2,
        3,
        D2Policy::Inline,
    )
    .expect("a legal round");
    assert_eq!(skewed.work.max_work, 2 * per_term);
    assert_eq!(skewed.work.mean_work, (4 * per_term) as f64 / 3.0);
    assert!((skewed.work.max_over_mean - 1.5).abs() < 1e-12);
}

// ── Descriptor hygiene ───────────────────────────────────────────────────────

/// The descriptor is a by-value kernel parameter, so its PADDING is launched
/// too. Lowering builds it zero-initialized in a box, which is what makes two
/// identical lowerings byte-identical.
#[test]
fn the_descriptor_bytes_are_deterministic() {
    let first = lower_one(
        &ext_artifact(),
        2,
        bound(Some(e4_column(0)), 2, 2, false),
        2,
        4,
        D2Policy::Inline,
    )
    .expect("a legal round");
    let second = lower_one(
        &ext_artifact(),
        2,
        bound(Some(e4_column(0)), 2, 2, false),
        2,
        4,
        D2Policy::Inline,
    )
    .expect("a legal round");
    assert_eq!(
        first.desc.launch_bytes(),
        second.desc.launch_bytes(),
        "two identical lowerings must produce identical launch bytes",
    );
    // Dead window slots carry the ABSENT procedural kind, never a live zero.
    let desc = inline_desc(&first);
    for window in &desc.window[1..] {
        assert_eq!(window.procedural_kind, BWD_COEFF_PROCEDURAL_NONE);
        assert!(window.read_base.is_null());
    }
    // Dead source records stay zero.
    for source in &desc.source[usize::from(desc.num_sources)..] {
        assert_eq!(source.window, 0);
        assert_eq!(source.class, 0);
        assert_eq!(source.column, 0);
    }
    assert_eq!(desc.pad, [0]);
}

/// The whole launch tail, in one place: what lowering copies through and what it
/// deliberately leaves for the caller.
#[test]
fn the_launch_tail_is_filled_from_the_round_binding() {
    let artifact = ext_artifact();
    let bounds = [bound(Some(e4_column(0)), 2, 2, false)];
    let scratch = scratch_for(plan_for(2, &bounds, &[2]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    let mut round = round_binding(2, &bounds, &read_elements, &claim, &coeffs);
    round.eq_sizes = GkrEqSizes {
        high: [8, 3],
        low: 5,
    };
    let setup = lower_bwd_seg(
        &artifact,
        &round,
        &scratch,
        1,
        D2Policy::Inline,
        ProgramMode::Inline,
        CoeffMode::Constant,
    )
    .expect("a legal round");
    let desc = inline_desc(&setup);
    assert_eq!(desc.eq_low as usize, RUNTIME);
    assert_eq!(desc.contributions as usize, RUNTIME + 0x0100_0000);
    assert_eq!(desc.eq_sizes.high, [8, 3]);
    assert_eq!(desc.eq_sizes.low, 5);
    assert_eq!(desc.logical_rows as usize, ROWS[2]);
    assert_eq!(desc.num_sources, 2);
    assert_eq!(desc.window[0].read_base as usize, E4_BACKING);
    assert_eq!(desc.window[0].read_stride_bytes, 1 << 20);
    assert_eq!(desc.window[0].backing_depth, 2);
    assert_eq!(desc.window[0].target_depth, 2);
    assert_eq!(desc.window[0].reserved, [0; 3]);
    // The source table is the binding's, slot for slot.
    for (slot, expected) in artifact.binding.source_slots.iter().enumerate() {
        assert_eq!(desc.source[slot].window, expected.window);
        assert_eq!(desc.source[slot].column, expected.column);
    }
}

/// The device-pointer coefficient mode leaves the pointer for the caller too —
/// the payload is the same reserved-inclusive vector either way.
#[test]
fn the_device_pointer_mode_leaves_the_pointer_null() {
    let setup = {
        let artifact = ext_artifact();
        let bounds = [bound(Some(e4_column(0)), 2, 2, false)];
        let scratch = scratch_for(plan_for(2, &bounds, &[2]));
        let claim = claim_point(8);
        let coeffs = coefficients(4);
        let read_elements = generous(1);
        lower_bwd_seg(
            &artifact,
            &round_binding(2, &bounds, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::DevPtr,
        )
        .expect("a legal round")
    };
    assert!(inline_desc(&setup).coefficients.is_null());
    assert_eq!(setup.coefficients.len(), 6);
}

/// `window_columns` is the artifact's own addressable width per window — the
/// number the publish plan and the alias check are both sized from.
#[test]
fn window_columns_counts_the_addressable_span() {
    let mut sparse = base_witness(&[0, 1]);
    sparse.columns[1].column = 5;
    let binding = LeanSourceBinding {
        windows: vec![sparse, ext_output(1, &[2])],
        source_slots: slots(&[(0, 0), (0, 5), (1, 0)]),
    };
    assert_eq!(window_columns(&binding), Ok(vec![6, 1]));
}

/// The decoded program is the source of the wire's own slot references, so a
/// malformed stream is reported as a codec error rather than mis-lowered.
#[test]
fn a_malformed_program_is_reported_as_a_codec_error() {
    let mut artifact = ext_artifact();
    artifact.program.words.pop();
    let error = lower_one(
        &artifact,
        2,
        bound(Some(e4_column(0)), 2, 2, false),
        2,
        1,
        D2Policy::Inline,
    )
    .expect_err("a truncated stream cannot be lowered");
    assert!(matches!(error, BwdSegLowerError::Codec(_)), "{error:?}",);
}

/// A round the plan does not cover has no publish geometry to hand out.
#[test]
fn a_round_the_plan_does_not_cover_is_rejected() {
    let artifact = ext_artifact();
    let bounds = [bound(Some(e4_column(0)), 2, 2, false)];
    let scratch = scratch_for(plan_for(2, &bounds, &[2]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    let mut round = round_binding(2, &bounds, &read_elements, &claim, &coeffs);
    round.round = 5;
    round.rows = ROWS[5];
    round.acc_size = ROWS[5] as u32;
    assert_eq!(
        lower_bwd_seg(
            &artifact,
            &round,
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::PlanMissingRound {
            round: 5,
            rounds: 3,
        }),
    );
}

/// The plan's stride is derived from the rows it was planned with; a round
/// binding that claims different rows would publish through the wrong stride.
#[test]
fn a_plan_stride_that_is_not_this_round_rows_is_rejected() {
    let bounds = [bound(Some(bf_column(0)), 0, 3, true)];
    let scratch = scratch_for(plan_for(3, &bounds, &[2]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    let mut round = round_binding(3, &bounds, &read_elements, &claim, &coeffs);
    round.rows = ROWS[3] / 2;
    round.acc_size = round.rows as u32;
    assert_eq!(
        lower_bwd_seg(
            &bf_artifact(),
            &round,
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::PublishStrideMismatch {
            round: 3,
            expected: 2 * (ROWS[3] / 2) * 16,
            actual: 2 * ROWS[3] * 16,
        }),
    );
}

/// `plan_publish_scratch`'s output is a pure function of its inputs, which is
/// what lets a caller plan once and lower every round against it.
#[test]
fn the_plan_is_a_pure_function_of_its_inputs() {
    let windows = [
        bound(Some(bf_column(0)), 0, 3, true),
        bound(Some(e4_column(0)), 3, 3, false),
    ];
    let first = plan_for(3, &windows, &[2, 1]);
    let second = plan_for(3, &windows, &[2, 1]);
    assert_eq!(first, second);
    assert_eq!(
        first.per_round[3],
        PublishRoundLayout {
            bytes: 2 * 2 * ROWS[3] * 16,
            window_base: vec![0, PUBLISH_WINDOW_ABSENT],
            column_stride_bytes: 2 * ROWS[3] * 16,
        },
    );
}

/// `chain_read_column` answers only for a window the PREVIOUS round published,
/// and it is the one place the parity-plus-offset arithmetic lives.
#[test]
fn chain_read_column_answers_only_for_a_published_window() {
    let round3 = [
        bound(Some(bf_column(0)), 0, 3, true),
        bound(Some(e4_column(0)), 3, 3, false),
    ];
    let plan = plan_publish_scratch(
        &[&[], &[], &[], &round3[..], &[]],
        &[&[], &[], &[], &[1, 1], &[]],
        &ROWS[..5],
    )
    .expect("a legal plan");
    let scratch = scratch_for(plan);
    let (ptr, stride) = chain_read_column(&scratch, 4, 0).expect("window 0 published at round 3");
    assert_eq!(ptr as usize, PARITY1);
    assert_eq!(stride as usize, 2 * ROWS[3] * 16);
    assert_eq!(
        chain_read_column(&scratch, 4, 1),
        None,
        "window 1 published nothing",
    );
    assert_eq!(
        chain_read_column(&scratch, 0, 0),
        None,
        "round 0 has no previous round"
    );
    assert_eq!(chain_read_column(&scratch, 4, 9), None, "no such window");
}

/// The lean wire's records ARE what the descriptor carries — decoding the
/// descriptor's stream back gives the artifact's own terms, list by list.
#[test]
fn the_descriptor_stream_decodes_to_the_artifact_terms() {
    let artifact = ext_artifact();
    let setup = lower_one(
        &artifact,
        2,
        bound(Some(e4_column(0)), 2, 2, false),
        2,
        2,
        D2Policy::Inline,
    )
    .expect("a legal round");
    let desc = inline_desc(&setup);
    let words = usize::from(desc.list_offset[usize::from(desc.k)]);
    let stream = LeanProgram {
        words: desc.program[..words].to_vec(),
        term_count: usize::from(desc.term_count),
    };
    let mut lowered = decode_program(&stream).expect("whole records");
    let mut committed = decode_program(&artifact.program).expect("whole records");
    lowered.sort_by_key(|term| (term.class, term.coeff, term.source_a, term.source_b));
    committed.sort_by_key(|term| (term.class, term.coeff, term.source_a, term.source_b));
    assert_eq!(lowered, committed, "the split permutes, never rewrites");
}

/// A plan and a round binding that disagree about WHO publishes are rejected in
/// both directions. The `materialize`-flag check catches the case where the two
/// were built from the same flags; these two are the case where they were not,
/// and they are what keeps a publish pointer from pointing at a region nobody
/// reserved (or a reserved region nobody writes).
#[test]
fn a_plan_that_disagrees_with_the_policy_about_publishing_is_rejected() {
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);

    // Planned as non-publishing, lowered as publishing: no region to hand out.
    let planned = [bound(Some(bf_column(0)), 0, 3, false)];
    let scratch = scratch_for(plan_for(3, &planned, &[2]));
    let publishing = [bound(Some(bf_column(0)), 0, 3, true)];
    assert_eq!(
        lower_bwd_seg(
            &bf_artifact(),
            &round_binding(3, &publishing, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::PlanMissingPublishRegion { window: 0 }),
    );

    // Planned as publishing, lowered as a direct read: a region nothing writes.
    // The direct read is an E4 backing already at target depth — a raw base one
    // at depth three is rejected by `BaseReadAtFoldedDepth` before it gets here.
    let scratch = scratch_for(plan_for(3, &publishing, &[2]));
    let direct = [bound(Some(e4_column(0)), 3, 3, false)];
    assert_eq!(
        lower_bwd_seg(
            &bf_artifact(),
            &round_binding(3, &direct, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::PlanPublishRegionUnused { window: 0 }),
    );
}

/// A parity buffer the plan needs but the caller did not allocate.
#[test]
fn an_unallocated_parity_buffer_is_rejected() {
    let bounds = [bound(Some(bf_column(0)), 0, 3, true)];
    let mut scratch = scratch_for(plan_for(3, &bounds, &[2]));
    scratch.parity_base[1] = std::ptr::null_mut();
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    assert_eq!(
        lower_bwd_seg(
            &bf_artifact(),
            &round_binding(3, &bounds, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::NullParityBase { parity: 1 }),
    );
}

/// A launch with no rows has no contribution stride, and every span total would
/// be zero.
#[test]
fn a_row_count_of_zero_is_rejected() {
    let bounds = [bound(Some(e4_column(0)), 2, 2, false)];
    let scratch = scratch_for(plan_for(2, &bounds, &[2]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    let mut round = round_binding(2, &bounds, &read_elements, &claim, &coeffs);
    round.rows = 0;
    round.acc_size = 0;
    assert_eq!(
        lower_bwd_seg(
            &ext_artifact(),
            &round,
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::RowsOutOfRange { rows: 0 }),
    );
}

/// **The landmine's inverse.** Deriving the origin from the round binding trusts
/// the binding, so a binding that LIES about physical state must be rejected
/// rather than lowered. A raw base matrix is only ever at depth zero — a fold
/// weights with E4 challenges and produces E4 — so a nonzero `backing_depth` on
/// one claims raw data was folded in place and silently shortens the catch-up.
#[test]
fn a_base_read_at_a_folded_depth_is_rejected() {
    assert_eq!(
        lower_one(
            &bf_artifact(),
            3,
            bound(Some(bf_column(0)), 2, 3, false),
            2,
            1,
            D2Policy::Inline,
        ),
        Err(BwdSegLowerError::BaseReadAtFoldedDepth {
            window: 0,
            backing_depth: 2,
        }),
    );
    // The legal shape it is one step away from: depth zero, folded by the round.
    assert!(lower_one(
        &bf_artifact(),
        3,
        bound(Some(bf_column(0)), 0, 3, true),
        2,
        1,
        D2Policy::Inline,
    )
    .is_ok());
}

/// The read-LESS half of the same lie. A procedural source is row-synthesized at
/// depth zero, so a nonzero `backing_depth` on one is the same silently-shortened
/// catch-up — and the delta rules do NOT bound it: at round 2 (`fold_depth = 2`)
/// `backing_depth = 1` gives `delta = 1`, a legal catch-up distance, so nothing
/// else in the precondition set objects. `RawReadOverPriorPublish` cannot cover it
/// either: at round 2 no previous round reserved a region for this window.
#[test]
fn a_procedural_window_at_a_folded_depth_is_rejected() {
    let procedural = artifact(
        ArtifactRegime::Ext,
        3,
        vec![virtual_setup(1, 0)],
        slots(&[(0, 0)]),
        program(&[record(0, 0, 0, SOURCE_NONE)]),
    );
    assert_eq!(
        lower_one(
            &procedural,
            2,
            bound(None, 1, 2, false),
            1,
            1,
            D2Policy::Inline,
        ),
        Err(BwdSegLowerError::BaseReadAtFoldedDepth {
            window: 0,
            backing_depth: 1,
        }),
    );
    // Synthesis at depth zero, folded by the round, is the legal shape.
    assert!(lower_one(
        &procedural,
        2,
        bound(None, 0, 2, false),
        1,
        1,
        D2Policy::Inline,
    )
    .is_ok());
    // ...and so is the publish-then-chain pair, whose second half reads the
    // scratch region as E4 and so is exempt from the depth guard by taking its E4
    // arm rather than by an exemption.
    let round3 = [bound(None, 0, 3, true)];
    let plan = plan_publish_scratch(
        &[&[], &[], &[], &round3[..], &round3[..]],
        &[&[], &[], &[], &[1], &[1]],
        &ROWS[..5],
    )
    .expect("a legal two-round plan");
    let scratch = scratch_for(plan);
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    assert!(lower_bwd_seg(
        &procedural,
        &round_binding(3, &round3, &read_elements, &claim, &coeffs),
        &scratch,
        1,
        D2Policy::Inline,
        ProgramMode::Inline,
        CoeffMode::Constant,
    )
    .is_ok());
    let (chain_ptr, chain_stride) =
        chain_read_column(&scratch, 4, 0).expect("round 3 published this window");
    let round4 = [bound(
        Some(column_at(chain_ptr as usize, true, chain_stride)),
        3,
        4,
        true,
    )];
    assert!(lower_bwd_seg(
        &procedural,
        &round_binding(4, &round4, &read_elements, &claim, &coeffs),
        &scratch,
        1,
        D2Policy::Inline,
        ProgramMode::Inline,
        CoeffMode::Constant,
    )
    .is_ok());
}

/// The other half of the inverse: a window the PREVIOUS round published must
/// chain off that region. Binding it back to its raw source refolds data the
/// chain has already moved past — and at `backing_depth = 0` the depth guard
/// above cannot see it, which is why both guards exist.
#[test]
fn a_raw_read_where_the_previous_round_published_is_rejected() {
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    // Round 2 materialized window 0 (the D2 policy's other arm), so round 3's
    // folded values live in parity 0.
    let round2 = [bound(Some(bf_column(0)), 0, 2, true)];
    let plan = plan_publish_scratch(
        &[&[], &[], &round2[..], &round2[..]],
        &[&[], &[], &[2], &[2]],
        &ROWS[..4],
    )
    .expect("a legal two-round plan");
    let scratch = scratch_for(plan);

    // A raw BF read at depth 0 is a legal-looking (BF, d3) pyramid in isolation.
    let raw = [bound(Some(bf_column(0)), 0, 3, true)];
    assert_eq!(
        lower_bwd_seg(
            &bf_artifact(),
            &round_binding(3, &raw, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::RawReadOverPriorPublish { window: 0 }),
    );

    // A procedural window is the virtual-setup shape of the same mistake.
    let procedural = artifact(
        ArtifactRegime::Ext,
        3,
        vec![virtual_setup(0, 0)],
        slots(&[(0, 0)]),
        program(&[record(0, 0, 0, SOURCE_NONE)]),
    );
    let synthesized = [bound(None, 0, 3, true)];
    let plan = plan_publish_scratch(
        &[&[], &[], &synthesized[..], &synthesized[..]],
        &[&[], &[], &[1], &[1]],
        &ROWS[..4],
    )
    .expect("a legal two-round plan");
    let scratch = scratch_for(plan);
    assert_eq!(
        lower_bwd_seg(
            &procedural,
            &round_binding(3, &synthesized, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::RawReadOverPriorPublish { window: 0 }),
    );

    // The route that IS legal at round 3: chain off round 2's region.
    let (chain_ptr, chain_stride) =
        chain_read_column(&scratch, 3, 0).expect("round 2 published this window");
    let chained = [bound(
        Some(column_at(chain_ptr as usize, true, chain_stride)),
        2,
        3,
        true,
    )];
    assert!(lower_bwd_seg(
        &procedural,
        &round_binding(3, &chained, &read_elements, &claim, &coeffs),
        &scratch,
        1,
        D2Policy::Inline,
        ProgramMode::Inline,
        CoeffMode::Constant,
    )
    .is_ok());
}

/// A previous round planned for a NARROWER artifact would make
/// `chain_read_column` answer `None` for the windows it does not reach, which
/// reads exactly like "published nothing" — so the chain check would go quiet
/// instead of failing. The prior round's shape is therefore checked like this
/// round's.
#[test]
fn a_previous_round_planned_for_fewer_windows_is_rejected() {
    let narrow = [bound(Some(bf_column(0)), 0, 3, true)];
    let wide = [
        bound(Some(e4_column(0)), 3, 4, true),
        bound(Some(e4_column(1)), 3, 4, true),
    ];
    let plan = plan_publish_scratch(
        &[&[], &[], &[], &narrow[..], &wide[..]],
        &[&[], &[], &[], &[1], &[1, 1]],
        &ROWS[..5],
    )
    .expect("a legal plan");
    let scratch = scratch_for(plan);
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(2);
    let artifact = artifact(
        ArtifactRegime::Ext,
        3,
        vec![ext_output(1, &[0]), ext_output(2, &[1])],
        slots(&[(0, 0), (1, 0)]),
        program(&[record(1, 2, 0, 1)]),
    );
    assert_eq!(
        lower_bwd_seg(
            &artifact,
            &round_binding(4, &wide, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::PlanShapeMismatch {
            round: 3,
            windows: 2,
            entries: 1,
        }),
    );
}
