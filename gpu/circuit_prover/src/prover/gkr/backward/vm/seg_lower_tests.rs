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
    decode_program, LeanProgram, LEAN_GROUP_FLAG_C0, LEAN_GROUP_FLAG_C2, LEAN_WORDS_PER_TERM,
    SOURCE_NONE,
};
use gkr_eval_isa::bwd::coeff::lean_artifact::LeanCoordinateArtifact;
use gkr_eval_isa::bwd::coeff::lean_bind::{
    LeanBoundColumn, LeanBoundWindow, LeanSourceBinding, LeanSourceSlot,
};
use gkr_eval_isa::bwd::coeff::limits::{
    in_scope, TermCategory, LEAN_CONT_GROUP_HEADER_CLASS, LEAN_DESCRIPTOR_PROGRAM_WORDS,
    LEAN_MAX_IMMEDIATES, SOURCE_WINDOW_COLUMNS,
};
use gkr_eval_isa::bwd::coeff::model::CoefficientRecipeId;
use gkr_eval_isa::bwd::coeff::order::split_round_robin;
use gkr_eval_isa::bwd::coeff::stats::WindowFamily;
use gkr_eval_isa::bwd::coeff::ArtifactRegime;

use super::seg_desc::{
    BWD_SEG_ADDR_NONE,
    BwdSegDesc, BwdSegSourceRecord, BWD_COEFF_ORIGIN_PROCEDURAL, BWD_COEFF_ORIGIN_READ_BASE,
    BWD_COEFF_ORIGIN_READ_EXT, BWD_COEFF_PROCEDURAL_NONE, BWD_SEG_CONST_BANK, BWD_SEG_C_INIT_NONE,
    BWD_SEG_FOLD_WEIGHT_BASE_D1, BWD_SEG_FOLD_WEIGHT_BASE_D2, BWD_SEG_FOLD_WEIGHT_BASE_D3,
    BWD_SEG_FOLD_WEIGHT_SLOTS, BWD_SEG_MAX_K, BWD_SEG_MAX_SOURCES, BWD_SEG_ADDR_SLOTS,
};
// The walk and its soft bound live in `seg_lower.rs`; the tests consume them.
use super::seg_lower::{
    assign_class, atom_work, bwd_seg_floor_soft_bound, bwd_seg_traffic_floor, chain_read_column,
    check_regions_disjoint, chop_atoms, deal_atoms, lower_bwd_seg, member_work,
    plan_publish_scratch, static_term_work, AnnotatedTerm, BwdSegLaunchDesc,
    BwdSegLowerError, BwdSegRoundBinding, BwdSegSetup, CoeffMode, D2Policy, ProgramMode,
    PublishRoundLayout, PublishScratchPlan, ResolvedAddrSlot, ResolvedPublishScratch,
    ResolvedSourceAddr,
    SegAtom, SegMember, SegUnitEmit, SourceClass, SourceOrigin, PUBLISH_WINDOW_ABSENT,
};
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::GkrEqSizes;
use crate::prover::gkr::forward::vm::lower::ResolvedColumn;
use crate::upstream::{Field, PrimeField};

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

/// The per-WINDOW bound these fixtures describe, which is how an ARTIFACT
/// describes its binding — one entry per artifact window, carrying both sides.
///
/// The descriptor's own shape is flatter (an address table keyed by backing, two
/// lanes per source), so [`addresses`] converts. Keeping the fixture shape means
/// a test still says "this window reads here at this depth" rather than spelling
/// out a slot table, and the conversion is the same one-slot-per-window mapping
/// the old lowering did implicitly.
#[derive(Clone, Copy, Debug)]
struct FixtureWindow {
    read: Option<ResolvedColumn>,
    publish: Option<ResolvedColumn>,
    backing_depth: u8,
    target_depth: u8,
    materialize: bool,
}

fn bound(
    read: Option<ResolvedColumn>,
    backing_depth: u8,
    target_depth: u8,
    materialize: bool,
) -> FixtureWindow {
    FixtureWindow {
        read,
        publish: None,
        backing_depth,
        target_depth,
        materialize,
    }
}

/// The byte stride a slot addresses its columns at.
fn slot_stride(slot: &super::seg_desc::BwdSegAddrSlot) -> usize {
    let element = if slot.origin == BWD_COEFF_ORIGIN_READ_EXT { 16 } else { 4 };
    element << slot.log2_stride
}

/// Source `source`'s READ slot.
fn read_slot_of(desc: &BwdSegDesc, source: usize) -> &super::seg_desc::BwdSegAddrSlot {
    &desc.slot[super::seg_desc::bwd_seg_lane_slot(desc.source[source].src)]
}

/// Source `source`'s DESTINATION slot, or `None` when it publishes nothing.
fn destination_of(desc: &BwdSegDesc, source: usize) -> Option<&super::seg_desc::BwdSegAddrSlot> {
    let cache = desc.source[source].cache;
    (cache != BWD_SEG_ADDR_NONE).then(|| &desc.slot[super::seg_desc::bwd_seg_lane_slot(cache)])
}

/// Per-window addressable column counts, from the artifact's own binding — the
/// count the lowering used to derive itself.
fn fixture_columns(binding: &LeanSourceBinding) -> Vec<usize> {
    binding
        .windows
        .iter()
        .map(|window| {
            window
                .columns
                .last()
                .map(|column| column.column.saturating_sub(window.first_column) + 1)
                .unwrap_or(1)
        })
        .collect()
}

/// Convert per-window fixture bounds into the descriptor's slots and lanes: one
/// slot per window, each source addressing its own window's slot at its own
/// column, and a publishing window's destination as a slot of its own.
fn addresses(
    artifact: &LeanCoordinateArtifact,
    bounds: &[FixtureWindow],
    read_elements: &[u32],
) -> (Vec<ResolvedAddrSlot>, Vec<ResolvedSourceAddr>) {
    let columns = fixture_columns(&artifact.binding);
    let mut slots: Vec<ResolvedAddrSlot> = bounds
        .iter()
        .enumerate()
        .map(|(index, bound)| ResolvedAddrSlot {
            base: bound.read,
            procedural_kind: artifact
                .binding
                .windows
                .get(index)
                .and_then(|window| window.procedural_kind()),
            read_elements: read_elements.get(index).copied().unwrap_or(0),
            columns: columns.get(index).copied().unwrap_or(1),
            deferred_base: false,
        })
        .collect();
    // Explicitly backed destinations become their own slots, appended so the read
    // slots keep their fixture indices.
    let mut publish_slot: Vec<Option<usize>> = vec![None; bounds.len()];
    for (index, bound) in bounds.iter().enumerate() {
        if let Some(publish) = bound.publish {
            slots.push(ResolvedAddrSlot {
                base: Some(publish),
                procedural_kind: None,
                read_elements: u32::MAX,
                columns: columns.get(index).copied().unwrap_or(1),
                deferred_base: false,
            });
            publish_slot[index] = Some(slots.len() - 1);
        }
    }
    let sources = artifact
        .binding
        .source_slots
        .iter()
        .map(|slot| {
            let window = usize::from(slot.window);
            ResolvedSourceAddr {
                read_slot: window,
                read_column: usize::from(slot.column),
                publish: publish_slot
                    .get(window)
                    .copied()
                    .flatten()
                    .map(|target| (target, usize::from(slot.column))),
                backing_depth: bounds
                    .get(window)
                    .map(|bound| bound.backing_depth)
                    .unwrap_or(0),
            }
        })
        .collect();
    (slots, sources)
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

/// One GROUP HEADER record (spec §4.4): the continuation control code, the core
/// recipe id, the member count, and the accumulator-side flags. Spelled
/// independently of the encoder, exactly like [`record`].
fn header(core: u16, members: u16, flags: u16) -> [u16; 4] {
    [
        (LEAN_CONT_GROUP_HEADER_CLASS << 13) | core,
        members,
        flags,
        0,
    ]
}

/// A program whose record list contains headers, so its TERM count is NOT its
/// record count — the counting invariant `words == 4 * (terms + headers)`.
fn grouped_program(records: &[[u16; 4]], terms: usize) -> LeanProgram {
    LeanProgram {
        words: records.iter().flatten().copied().collect(),
        term_count: terms,
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

/// [`plan_publish_scratch`] over fixture windows: it takes the "publishes into
/// scratch" flag per slot, which for a fixture is `materialize` without an
/// explicit backing.
fn plan_scratch(
    window_sets: &[&[FixtureWindow]],
    columns: &[&[usize]],
    rows: &[usize],
) -> Result<PublishScratchPlan, BwdSegLowerError> {
    let owned: Vec<Vec<bool>> = window_sets
        .iter()
        .map(|set| {
            set.iter()
                .map(|window| window.materialize && window.publish.is_none())
                .chain(set.iter().filter(|window| window.publish.is_some()).map(|_| false))
                .collect()
        })
        .collect();
    let flags: Vec<&[bool]> = owned.iter().map(|set| set.as_slice()).collect();
    // Columns for the appended destination slots mirror their read slot's.
    let owned_columns: Vec<Vec<usize>> = window_sets
        .iter()
        .zip(columns)
        .map(|(set, columns)| {
            columns
                .iter()
                .copied()
                .chain(
                    set.iter()
                        .enumerate()
                        .filter(|(_, window)| window.publish.is_some())
                        .map(|(index, _)| columns.get(index).copied().unwrap_or(1)),
                )
                .collect()
        })
        .collect();
    let columns: Vec<&[usize]> = owned_columns.iter().map(|set| set.as_slice()).collect();
    plan_publish_scratch(&flags, &columns, rows)
}

/// A plan whose only round is `round`, built from one window set.
fn plan_for(
    round: usize,
    windows: &[FixtureWindow],
    columns: &[usize],
) -> PublishScratchPlan {
    // The plan reserves for windows that publish WITHOUT an explicit backing;
    // `plan_publish_scratch` takes exactly that flag now. It must cover the whole
    // slot table, which `addresses` extends with one slot per explicit
    // destination — those reserve nothing.
    let flags: Vec<bool> = windows
        .iter()
        .map(|window| window.materialize && window.publish.is_none())
        .chain(windows.iter().filter(|window| window.publish.is_some()).map(|_| false))
        .collect();
    let extended_columns: Vec<usize> = columns
        .iter()
        .copied()
        .chain(
            windows
                .iter()
                .enumerate()
                .filter(|(_, window)| window.publish.is_some())
                .map(|(index, _)| columns.get(index).copied().unwrap_or(1)),
        )
        .collect();
    let windows = &flags[..];
    let empty_windows: Vec<bool> = Vec::new();
    let empty_columns: Vec<usize> = Vec::new();
    let mut window_sets: Vec<&[bool]> = Vec::new();
    let mut column_sets: Vec<&[usize]> = Vec::new();
    for index in 0..=round {
        if index == round {
            window_sets.push(windows);
            column_sets.push(&extended_columns);
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
    artifact: &LeanCoordinateArtifact,
    bounds: &[FixtureWindow],
    read_elements: &[u32],
    claim: &'a [E4],
    coeffs: &'a [E4],
) -> BwdSegRoundBinding<'a> {
    let (slots, sources) = addresses(artifact, bounds, read_elements);
    // Test-only leak: the converted tables must outlive this call so a fixture
    // can keep describing per-window bounds inline at the call site.
    let slots: &'static [ResolvedAddrSlot] = Box::leak(slots.into_boxed_slice());
    let sources: &'static [ResolvedSourceAddr] = Box::leak(sources.into_boxed_slice());
    BwdSegRoundBinding {
        round,
        rows: ROWS[round as usize],
        slots,
        sources,
        claim_point: claim,
        coefficients: coeffs,
        c_init: None,
        // The grouped-layer table is per-test: the immediates gates below set this
        // field on the returned binding, and every other fixture is ungrouped.
        immediates: &[],
        eq_low: RUNTIME as *const E4,
        eq_sizes: GkrEqSizes::zeroed(),
        contributions: (RUNTIME + 0x0100_0000) as *mut E4,
        acc_size: ROWS[round as usize] as u32,
        output: super::seg_desc::BWD_SEG_OUTPUT_ROWS,
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

/// The floor walk is a function of the lowered SETUP — the descriptor plus the
/// host-side endpoint spans (`BwdSegSetup::source_endpoints`) — so the floor
/// tests EDIT the descriptor to isolate one property instead of hunting a
/// fixture that happens to exhibit it. A slot added past `source_endpoints`
/// prices both halves (the documented fallback), which is what these edits want.
fn inline_desc_mut(setup: &mut BwdSegSetup) -> &mut BwdSegDesc {
    match &mut setup.desc {
        BwdSegLaunchDesc::Inline(desc) => desc,
        BwdSegLaunchDesc::ProgPtr(_) => panic!("expected the inline-program descriptor"),
    }
}

/// The floor's eq term, from the descriptor's OWN `eq_sizes.low` and `logical_rows`:
/// `min(logical_rows, 1 << low) * 16`. Never a hardcoded byte count, which would not
/// survive a fixture change.
fn eq_term(desc: &BwdSegDesc) -> u64 {
    let rows = u64::from(desc.logical_rows);
    let entries = if desc.eq_sizes.low >= 63 {
        rows
    } else {
        rows.min(1u64 << desc.eq_sizes.low)
    };
    entries * u64::from(E4_BYTES)
}

/// The one-window continuation lowering every simple test reuses:
/// `(artifact, bound-window)` at `round`, `k` lists, `d2` policy.
fn lower_one(
    artifact: &LeanCoordinateArtifact,
    round: u32,
    bound_window: FixtureWindow,
    columns: usize,
    k: usize,
    d2: D2Policy,
) -> Result<BwdSegSetup, BwdSegLowerError> {
    let bounds = [bound_window];
    let scratch = scratch_for(plan_for(round as usize, &bounds, &[columns]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    let binding = round_binding(round, artifact, &bounds, &read_elements, &claim, &coeffs);
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
            u8::from(desc.source[0].cache != BWD_SEG_ADDR_NONE),
            u8::from(foldable),
            "round {round} {d2:?} materialize",
        );
        assert_eq!(
            desc.num_foldable,
            if foldable { 2 } else { 0 },
            "round {round} {d2:?} foldable sources",
        );
        assert_eq!(desc.slot[0].origin, BWD_COEFF_ORIGIN_READ_BASE);
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
    assert_eq!(desc.slot[0].origin, BWD_COEFF_ORIGIN_READ_EXT);

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
    assert_eq!(desc.slot[0].origin, BWD_COEFF_ORIGIN_PROCEDURAL);
    assert_eq!(desc.slot[0].procedural_kind, 2);
    assert!(desc.slot[0].base.is_null());
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
    assert_eq!(desc.slot[0].origin, BWD_COEFF_ORIGIN_PROCEDURAL);
    assert_eq!(desc.num_foldable, 1);
    assert_eq!(desc.fold_source[0], 0);
    assert!(desc.source[0].cache != BWD_SEG_ADDR_NONE);
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
    assert_eq!(desc.slot[0].origin, BWD_COEFF_ORIGIN_READ_EXT);
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
    assert_eq!(desc.slot[0].origin, BWD_COEFF_ORIGIN_READ_EXT);
    assert_eq!(desc.slot[0].procedural_kind, BWD_COEFF_PROCEDURAL_NONE);
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
        assert_eq!(desc.record_count as usize, records.len());

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

    let plan = plan_scratch(
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
        plan_scratch(&[&windows], &[&[1, 2]], &[ROWS[3]]),
        Err(BwdSegLowerError::PlanShapeMismatch {
            round: 0,
            windows: 1,
            entries: 2,
        }),
    );
    assert_eq!(
        plan_scratch(&[&windows], &[&[1]], &[]),
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
            &round_binding(3, &artifact, &bounds, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::UnsafePublishAlias {
            window: 2,
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
    let plan = plan_scratch(
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
            &round_binding(3, &artifact, &round3, &read_elements, &claim, &coeffs),
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
    let binding = round_binding(3, &bf_artifact(), &bounds, &read_elements, &claim, &coeffs);
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
        let binding = round_binding(round, &artifact, &bounds, &short, &claim, &coeffs);
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
        let binding = round_binding(round, &artifact, &bounds, &exact, &claim, &coeffs);
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
        let plan = plan_scratch(
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
            &round_binding(3, &artifact, &round3, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        )
        .unwrap_or_else(|error| panic!("procedural {procedural}: round 3: {error:?}"));
        let third_desc = inline_desc(&third);
        let published = destination_of(third_desc, 0)
            .expect("round 3 publishes")
            .base;
        assert_eq!(
            published as usize, PARITY1,
            "procedural {procedural}: round 3 publishes into parity 1",
        );
        assert_eq!(
            slot_stride(destination_of(third_desc, 0).expect("round 3 publishes")),
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
            &round_binding(4, &artifact, &round4, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        )
        .unwrap_or_else(|error| panic!("procedural {procedural}: round 4: {error:?}"));
        let fourth_desc = inline_desc(&fourth);
        assert_eq!(
            fourth_desc.slot[0].base as usize, published as usize,
            "procedural {procedural}: round 4 chains off round 3's publish",
        );
        assert_eq!(
            slot_stride(read_slot_of(fourth_desc, 0)),
            2 * ROWS[3] * 16,
            "the READ stride is the PREVIOUS round's",
        );
        assert_eq!(
            destination_of(fourth_desc, 0).expect("round 4 publishes").base as usize,
            PARITY0,
            "procedural {procedural}: round 4 publishes into the other parity",
        );
        assert_eq!(
            slot_stride(destination_of(fourth_desc, 0).expect("round 4 publishes")),
            2 * ROWS[4] * 16,
            "the WRITE stride is THIS round's",
        );
        assert_eq!(fourth_desc.source[0].class, SourceClass::E4Direct.code());
        assert_eq!(fourth_desc.slot[0].origin, BWD_COEFF_ORIGIN_READ_EXT);
    }
}

/// A chain read that points anywhere OTHER than the previous round's published
/// region is rejected: the parity rule is enforced, not assumed.
#[test]
fn a_chain_read_off_the_previous_publish_region_is_rejected() {
    let round3 = [bound(Some(bf_column(0)), 0, 3, true)];
    let plan = plan_scratch(
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
            &round_binding(4, &bf_artifact(), &round4, &read_elements, &claim, &coeffs),
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

/// One past the descriptor's window CAPACITY is rejected.
///
/// `BWD_SEG_ADDR_SLOTS` sizes `BwdSegDesc::window`, a FIXED-length array, so
/// this rejection is what stands between a wider layer and a descriptor write past
/// its end. It is deliberately NOT the corpus measurement
/// (`in_scope::MAX_SOURCE_WINDOWS_USED`): sizing the array by the largest count
/// anyone had observed is what made blake2's 18th window a rejection instead of a
/// fact. The cell-era lineage covered exactly this in
/// `abi_tests::more_windows_than_the_measured_maximum_are_rejected`, which was
/// deleted with it; this is that coverage restored against the seg lowering.
#[test]
fn more_windows_than_the_capacity_are_rejected() {
    let cap = BWD_SEG_ADDR_SLOTS;
    // One window per source, one column each, one past the cap. Distinct layers so
    // no two windows share a backing.
    let windows: Vec<LeanBoundWindow> = (0..=cap)
        .map(|index| ext_output(index + 1, &[index as u32]))
        .collect();
    let slot_spec: Vec<(u8, u16)> = (0..=cap).map(|index| (index as u8, 0u16)).collect();
    let artifact = artifact(
        ArtifactRegime::Ext,
        2,
        windows,
        slots(&slot_spec),
        program(&[record(0, 0, 0, SOURCE_NONE)]),
    );

    let bounds: Vec<FixtureWindow> = (0..=cap)
        .map(|_| bound(Some(e4_column(0)), 2, 2, false))
        .collect();
    let columns = vec![1usize; cap + 1];
    let scratch = scratch_for(plan_for(2, &bounds, &columns));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(cap + 1);
    let binding = round_binding(2, &artifact, &bounds, &read_elements, &claim, &coeffs);

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
        Err(BwdSegLowerError::SourceWindowOverflow {
            windows: cap + 1,
            cap,
        }),
    );
}

/// One past the source-table capacity is rejected.
///
/// `BWD_SEG_MAX_SOURCES` sizes BOTH source-indexed descriptor arrays
/// (`fold_source` and `source`), so the same argument applies: without this
/// rejection a layer with more sources than the census measured writes past two
/// fixed-length arrays. Spread over the fewest legal windows — a window spans at
/// most `SOURCE_WINDOW_COLUMNS` columns, so `ceil(1073 / 128) = 9` of them, well
/// inside the window cap this must NOT trip instead.
#[test]
fn more_sources_than_the_table_capacity_are_rejected() {
    let cap = BWD_SEG_MAX_SOURCES;
    let total = cap + 1;
    let per_window = SOURCE_WINDOW_COLUMNS;
    let window_count = total.div_ceil(per_window);
    assert!(
        window_count <= in_scope::MAX_SOURCE_WINDOWS_USED,
        "the source overflow must be reachable without also overflowing the window cap"
    );

    let windows: Vec<LeanBoundWindow> = (0..window_count)
        .map(|index| {
            let first = index * per_window;
            let last = ((index + 1) * per_window).min(total);
            let sources: Vec<u32> = (first..last).map(|source| source as u32).collect();
            ext_output(index + 1, &sources)
        })
        .collect();
    let slot_spec: Vec<(u8, u16)> = (0..total)
        .map(|source| ((source / per_window) as u8, (source % per_window) as u16))
        .collect();
    let artifact = artifact(
        ArtifactRegime::Ext,
        2,
        windows,
        slots(&slot_spec),
        program(&[record(0, 0, 0, SOURCE_NONE)]),
    );

    let bounds: Vec<FixtureWindow> = (0..window_count)
        .map(|_| bound(Some(e4_column(0)), 2, 2, false))
        .collect();
    let columns: Vec<usize> = (0..window_count)
        .map(|index| (total - index * per_window).min(per_window))
        .collect();
    let scratch = scratch_for(plan_for(2, &bounds, &columns));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(window_count);
    let binding = round_binding(2, &artifact, &bounds, &read_elements, &claim, &coeffs);

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
        Err(BwdSegLowerError::SourceOverflow {
            sources: total,
            cap,
        }),
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
    let mut binding = round_binding(0, &artifact, &bounds, &read_elements, &claim, &coeffs);
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

/// A `c_init` is BOUNDS-CHECKED against the reserved-inclusive payload and lands in
/// the descriptor as the coefficient id, for the device to resolve.
#[test]
fn c_init_travels_as_a_bounds_checked_coefficient_id() {
    let artifact = ext_artifact();
    let bounds = [bound(Some(e4_column(0)), 2, 2, false)];
    let scratch = scratch_for(plan_for(2, &bounds, &[2]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);

    // Absent: the sentinel, not a zero id — `0` is the live `ONE`.
    let plain = lower_bwd_seg(
        &artifact,
        &round_binding(2, &artifact, &bounds, &read_elements, &claim, &coeffs),
        &scratch,
        1,
        D2Policy::Inline,
        ProgramMode::Inline,
        CoeffMode::Constant,
    )
    .expect("a legal round");
    assert_eq!(inline_desc(&plain).c_init_coeff, BWD_SEG_C_INIT_NONE);

    // The reserved `-1` literal is materialized at the bank head, so it
    // resolves exactly like a banked id.
    let mut seeded = round_binding(2, &artifact, &bounds, &read_elements, &claim, &coeffs);
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
    let id = inline_desc(&setup).c_init_coeff;
    assert_eq!(id, CoefficientRecipeId::NEG_ONE.0);
    assert_eq!(
        setup.coefficients[id as usize],
        E4::MINUS_ONE,
        "the id must address the payload entry the device will read"
    );
    assert_ne!(id, BWD_SEG_C_INIT_NONE, "the seed must be observable");

    // An id past the payload has no value to resolve to.
    let mut past = round_binding(2, &artifact, &bounds, &read_elements, &claim, &coeffs);
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


/// A publish backing on a window that does not publish would be silently
/// ignored, so it is refused instead.
#[test]
fn a_publish_backing_on_a_non_publishing_window_is_rejected() {
    let mut bound_window = bound(Some(bf_column(0)), 0, 1, false);
    bound_window.publish = Some(e4_column(3));
    assert_eq!(
        lower_one(&bf_artifact(), 1, bound_window, 2, 1, D2Policy::Inline),
        Err(BwdSegLowerError::UnexpectedPublishBacking { window: 0 }),
    );
}

// ── Explicit publish backings ────────────────────────────────────────────────
//
// Production publishes into the layer's OWN fold storage (the cascade — see
// `production_bind::CascadeRegion`), not into a parity buffer: the binder
// supplies the region per window and the plan reserves nothing for it. The
// stride is the backing's per-poly stride, usually WIDER than the round's
// per-column extent.

/// The publish extent per column at `ROWS[3]`: both endpoint halves, as E4.
const ROUND3_PUBLISH_EXTENT: u32 = (2 * ROWS[3] * 16) as u32;

/// An explicitly backed publish lowers at the BACKING's stride, and the plan —
/// built from the same bound windows — reserves no parity region for it.
#[test]
fn an_explicitly_backed_publish_lowers_at_the_backing_stride() {
    let mut bound_window = bound(Some(bf_column(0)), 0, 3, true);
    bound_window.publish = Some(column_at(E4_BACKING, true, 4096));
    let setup = lower_one(&bf_artifact(), 3, bound_window, 2, 1, D2Policy::Inline)
        .expect("an explicitly backed publish must lower");
    let desc = inline_desc(&setup);
    let publish = destination_of(desc, 0).expect("an explicit backing publishes");
    assert_eq!(publish.base as usize, E4_BACKING);
    assert_eq!(slot_stride(publish), 4096);
    assert_eq!(read_slot_of(desc, 0).base as usize, BF_BACKING);
}

/// The cascade's normal state at a chained round: the window READS slot
/// `r - 1` and PUBLISHES slot `r` of the SAME per-poly regions, so the two
/// strided column sets interleave — their hulls overlap while their actual
/// per-column extents are disjoint. The alias check must judge extents, not
/// hulls.
#[test]
fn a_cascade_shaped_round_lowers_with_interleaved_read_and_publish() {
    // Two columns of an ext-origin poly, folded from N = 256: per-poly region
    // 4096 B; at round 3 the chain reads slot 2 (1024 B at +2048) and
    // publishes slot 3 (512 B at +3072).
    let mut bound_window = bound(Some(column_at(E4_BACKING + 2048, true, 4096)), 2, 3, true);
    bound_window.publish = Some(column_at(E4_BACKING + 3072, true, 4096));
    let setup = lower_one(&ext_artifact(), 3, bound_window, 2, 1, D2Policy::Inline)
        .expect("the cascade's read/publish interleave is not an alias");
    let desc = inline_desc(&setup);
    assert_eq!(read_slot_of(desc, 0).base as usize, E4_BACKING + 2048);
    let publish = destination_of(desc, 0).expect("the cascade round publishes");
    assert_eq!(publish.base as usize, E4_BACKING + 3072);
    assert_eq!(slot_stride(publish), 4096);
}

/// An explicit backing AND a planned parity region for the same window is a
/// plan built from different windows than the lowering was handed — ambiguous,
/// so refused rather than picking one.
#[test]
fn an_explicit_publish_with_a_planned_region_is_ambiguous() {
    let mut bound_window = bound(Some(bf_column(0)), 0, 3, true);
    let planned = plan_for(3, std::slice::from_ref(&bound_window), &[2]);
    bound_window.publish = Some(column_at(E4_BACKING, true, 4096));
    let bounds = [bound_window];
    let scratch = scratch_for(planned);
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    let binding = round_binding(3, &bf_artifact(), &bounds, &read_elements, &claim, &coeffs);
    assert_eq!(
        lower_bwd_seg(
            &bf_artifact(),
            &binding,
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        )
        .err(),
        Some(BwdSegLowerError::AmbiguousPublishBacking { window: 0 }),
    );
}

/// A publish is always E4, and a stride narrower than the round's per-column
/// extent would make consecutive columns overwrite each other.
#[test]
fn a_non_e4_or_narrow_explicit_publish_region_is_rejected() {
    let mut bound_window = bound(Some(bf_column(0)), 0, 3, true);
    bound_window.publish = Some(column_at(E4_BACKING, false, 4096));
    assert_eq!(
        lower_one(&bf_artifact(), 3, bound_window, 2, 1, D2Policy::Inline),
        Err(BwdSegLowerError::ExplicitPublishGeometry {
            window: 0,
            is_e4: false,
            stride_bytes: 4096,
        }),
    );

    // Half the extent: still a power of two in E4 elements (a lane indexes
    // `column << log2_stride`, so a non-power-of-two stride is rejected earlier as
    // `StrideNotPowerOfTwo`), and still too narrow for the round's per-column
    // write.
    let narrow = ROUND3_PUBLISH_EXTENT / 2;
    let mut bound_window = bound(Some(bf_column(0)), 0, 3, true);
    bound_window.publish = Some(column_at(E4_BACKING, true, narrow));
    assert_eq!(
        lower_one(&bf_artifact(), 3, bound_window, 2, 1, D2Policy::Inline),
        Err(BwdSegLowerError::ExplicitPublishGeometry {
            window: 0,
            is_e4: true,
            stride_bytes: narrow,
        }),
    );

    // And a stride that is not a whole power of two cannot be indexed at all.
    let mut bound_window = bound(Some(bf_column(0)), 0, 3, true);
    bound_window.publish = Some(column_at(E4_BACKING, true, ROUND3_PUBLISH_EXTENT - 16));
    assert_eq!(
        lower_one(&bf_artifact(), 3, bound_window, 2, 1, D2Policy::Inline),
        Err(BwdSegLowerError::StrideNotPowerOfTwo {
            window: 1,
            stride_bytes: ROUND3_PUBLISH_EXTENT - 16,
        }),
    );
}

/// The extent-aware alias check still rejects a REAL overlap: two windows
/// explicitly publishing into ranges that collide.
#[test]
fn overlapping_explicit_publish_regions_are_rejected() {
    let two_windows = artifact(
        ArtifactRegime::Ext,
        3,
        vec![ext_output(1, &[0]), ext_output(2, &[1])],
        slots(&[(0, 0), (1, 0)]),
        program(&[record(1, 2, 0, 1), record(0, 0, 1, SOURCE_NONE)]),
    );
    let mut first = bound(Some(column_at(E4_BACKING + 0x0100_0000, true, 4096)), 2, 3, true);
    first.publish = Some(column_at(E4_BACKING, true, 4096));
    let mut second = bound(Some(column_at(E4_BACKING + 0x0200_0000, true, 4096)), 2, 3, true);
    second.publish = Some(column_at(
        E4_BACKING + (ROUND3_PUBLISH_EXTENT / 2) as usize,
        true,
        4096,
    ));
    let bounds = [first, second];
    let scratch = scratch_for(plan_for(3, &bounds, &[1, 1]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(2);
    let binding = round_binding(3, &two_windows, &bounds, &read_elements, &claim, &coeffs);
    assert_eq!(
        lower_bwd_seg(
            &two_windows,
            &binding,
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        )
        .err(),
        Some(BwdSegLowerError::UnsafePublishAlias {
            window: 2,
            other: 3,
        }),
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
    // The span is computable; the LOWERING is what refuses a slot wider than a
    // lane's seven-bit column field.
    assert_eq!(
        fixture_columns(&artifact.binding),
        vec![SOURCE_WINDOW_COLUMNS + 1]
    );
    assert_eq!(
        lower_one(
            &artifact,
            3,
            bound(Some(bf_column(0)), 0, 3, false),
            SOURCE_WINDOW_COLUMNS + 1,
            1,
            D2Policy::Inline
        ),
        Err(BwdSegLowerError::WindowColumnOverflow {
            window: 0,
            offset: SOURCE_WINDOW_COLUMNS + 1,
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
            &round_binding(2, &artifact, &bounds, &read_elements, &claim, &coeffs),
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
        let mut binding = round_binding(2, &artifact, &bounds, &read_elements, &claim, &coeffs);
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
            &round_binding(2, &artifact, &bounds, &read_elements, &short, &coeffs),
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
    let mut binding = round_binding(2, &artifact, &bounds, &read_elements, &claim, &coeffs);
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
    // ONE record past what the array holds, derived from the capacity rather than
    // written out: a literal count stops overflowing the moment the array grows.
    let over = LEAN_DESCRIPTOR_PROGRAM_WORDS / LEAN_WORDS_PER_TERM + 1;
    let records: Vec<[u16; 4]> = (0..over).map(|_| record(0, 0, 0, SOURCE_NONE)).collect();
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
            &round_binding(2, &artifact, &bounds, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            ProgramMode::Inline,
            CoeffMode::Constant,
        ),
        Err(BwdSegLowerError::ProgramOverflow {
            words,
            cap: LEAN_DESCRIPTOR_PROGRAM_WORDS,
        }),
    );
    let setup = lower_bwd_seg(
        &artifact,
        &round_binding(2, &artifact, &bounds, &read_elements, &claim, &coeffs),
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
        &round_binding(2, &artifact, &bounds, &read_elements, &claim, &recipes),
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
            &round_binding(2, &artifact, &bounds, &read_elements, &claim, &recipes),
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
        &round_binding(2, &artifact, &bounds, &read_elements, &claim, &census),
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
    for slot in &desc.slot[1..] {
        assert_eq!(slot.procedural_kind, BWD_COEFF_PROCEDURAL_NONE);
        assert!(slot.base.is_null());
    }
    // Dead source records stay zero.
    for source in &desc.source[usize::from(desc.num_sources)..] {
        assert_eq!(source.src, BWD_SEG_ADDR_NONE);
        assert_eq!(source.cache, BWD_SEG_ADDR_NONE);
        assert_eq!(source.class, 0);
        assert_eq!(source.delta, 0);
    }
    assert_eq!(desc.output, super::seg_desc::BWD_SEG_OUTPUT_ROWS);
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
    let mut round = round_binding(2, &artifact, &bounds, &read_elements, &claim, &coeffs);
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
    assert_eq!(desc.slot[0].base as usize, E4_BACKING);
    assert_eq!(slot_stride(read_slot_of(desc, 0)), 1 << 20);
    assert_eq!(desc.source[0].delta, 0);
    assert_eq!(desc.slot[0].reserved, [0; 5]);
    // The source table is the binding's, slot for slot.
    for (slot, expected) in artifact.binding.source_slots.iter().enumerate() {
        let lane = desc.source[slot].src;
        assert_eq!(
            super::seg_desc::bwd_seg_lane_slot(lane),
            usize::from(expected.window)
        );
        assert_eq!(
            super::seg_desc::bwd_seg_lane_column(lane),
            usize::from(expected.column)
        );
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
            &round_binding(2, &artifact, &bounds, &read_elements, &claim, &coeffs),
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
    assert_eq!(fixture_columns(&binding), vec![6, 1]);
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
    let mut round = round_binding(2, &artifact, &bounds, &read_elements, &claim, &coeffs);
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
    let mut round = round_binding(3, &bf_artifact(), &bounds, &read_elements, &claim, &coeffs);
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
    let plan = plan_scratch(
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
    // `decode_program` reads `words` only, and the descriptor carries a RECORD
    // count rather than a term count, so that is what the reconstruction states.
    let stream = LeanProgram {
        words: desc.program[..words].to_vec(),
        term_count: usize::from(desc.record_count),
    };
    let regime = artifact.regime.regime();
    let mut lowered = decode_program(&stream, regime).expect("whole records");
    let mut committed = decode_program(&artifact.program, regime).expect("whole records");
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
            &round_binding(3, &bf_artifact(), &publishing, &read_elements, &claim, &coeffs),
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
            &round_binding(3, &bf_artifact(), &direct, &read_elements, &claim, &coeffs),
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
            &round_binding(3, &bf_artifact(), &bounds, &read_elements, &claim, &coeffs),
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
    let mut round = round_binding(2, &ext_artifact(), &bounds, &read_elements, &claim, &coeffs);
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
    let plan = plan_scratch(
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
        &round_binding(3, &procedural, &round3, &read_elements, &claim, &coeffs),
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
        &round_binding(4, &procedural, &round4, &read_elements, &claim, &coeffs),
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
    let plan = plan_scratch(
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
            &round_binding(3, &bf_artifact(), &raw, &read_elements, &claim, &coeffs),
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
    let plan = plan_scratch(
        &[&[], &[], &synthesized[..], &synthesized[..]],
        &[&[], &[], &[1], &[1]],
        &ROWS[..4],
    )
    .expect("a legal two-round plan");
    let scratch = scratch_for(plan);
    assert_eq!(
        lower_bwd_seg(
            &procedural,
            &round_binding(3, &procedural, &synthesized, &read_elements, &claim, &coeffs),
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
        &round_binding(3, &procedural, &chained, &read_elements, &claim, &coeffs),
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
    let plan = plan_scratch(
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
            &round_binding(4, &artifact, &wide, &read_elements, &claim, &coeffs),
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

// ── The flat fold-weight algebra ─────────────────────────────────────────────

/// Host recomputation of the fold-weight bank (spec §3.3): slot layout
/// [0] = D1, [1..4) = D2 q=1..3, [4..11) = D3 q=1..7, physical-offset order —
/// challenge j pairs with bit (delta-1-j) of q. delta > round groups are ZERO.
pub(crate) fn expected_fold_weights(
    round: u32,
    claim_point: &[E4],
) -> [E4; BWD_SEG_FOLD_WEIGHT_SLOTS] {
    let mut slots = [E4::ZERO; BWD_SEG_FOLD_WEIGHT_SLOTS];
    let mut slot = 0usize;
    for delta in 1u32..=3 {
        for q in 1u32..(1 << delta) {
            if delta <= round {
                let mut w = E4::ONE;
                for j in 0..delta {
                    let c = claim_point[(round - delta + j) as usize];
                    let factor = if (q >> (delta - 1 - j)) & 1 == 1 {
                        c
                    } else {
                        let mut one_minus = E4::ONE;
                        one_minus.sub_assign(&c);
                        one_minus
                    };
                    w.mul_assign(&factor);
                }
                slots[slot] = w;
            }
            slot += 1;
        }
    }
    slots
}

/// The retired pyramid's exact recursion (segmented_vm.cu's seg_fold_level,
/// pre-flat lineage), kept as the INDEPENDENT oracle for the weight tables: the
/// flat kernel is pinned against it through them. Over a physical leaf array
/// with span 1: level L weights with challenges[L-1], stride 1 << (delta - L).
fn fold_level_reference(
    leaves: &[E4],
    challenges: &[E4],
    level: u32,
    delta: u32,
    index: u32,
) -> E4 {
    let challenge = challenges[(level - 1) as usize];
    let stride = 1u32 << (delta - level);
    let node = |f0: E4, f1: E4| {
        let mut d = f1;
        d.sub_assign(&f0);
        d.mul_assign(&challenge);
        d.add_assign(&f0);
        d
    };
    if level == 1 {
        node(leaves[index as usize], leaves[(index + stride) as usize])
    } else {
        node(
            fold_level_reference(leaves, challenges, level - 1, delta, index),
            fold_level_reference(leaves, challenges, level - 1, delta, index + stride),
        )
    }
}

/// Deterministic non-trivial field elements without a rand dependency:
/// x <- x^2 + x + g. An algebraic identity must hold for every value, so
/// distribution quality is irrelevant; variety is enough.
fn next_e4(state: &mut E4, g: &E4) -> E4 {
    let mut next = *state;
    next.mul_assign(state);
    next.add_assign(state);
    next.add_assign(g);
    *state = next;
    next
}

#[test]
fn the_flat_fold_weights_reproduce_the_pyramid_and_sum_to_one() {
    let mut state = E4::ONE;
    let mut g = E4::ONE;
    g.add_assign(&E4::ONE); // g = 2
    for round in 1u32..=3 {
        let claim_point: Vec<E4> = (0..round).map(|_| next_e4(&mut state, &g)).collect();
        let weights = expected_fold_weights(round, &claim_point);
        for delta in 1u32..=round {
            let base = match delta {
                1 => BWD_SEG_FOLD_WEIGHT_BASE_D1,
                2 => BWD_SEG_FOLD_WEIGHT_BASE_D2,
                _ => BWD_SEG_FOLD_WEIGHT_BASE_D3,
            };
            let challenges = &claim_point[(round - delta) as usize..round as usize];
            for _ in 0..100 {
                let leaves: Vec<E4> = (0..1u32 << delta)
                    .map(|_| next_e4(&mut state, &g))
                    .collect();
                // (a) the live pyramid
                let pyramid = fold_level_reference(&leaves, challenges, delta, delta, 0);
                // (b) partition-of-unity difference form over the stored slots
                let mut flat = leaves[0];
                for q in 1..leaves.len() {
                    let mut d = leaves[q];
                    d.sub_assign(&leaves[0]);
                    d.mul_assign(&weights[base + q - 1]);
                    flat.add_assign(&d);
                }
                // (c) naive Lagrange dot product, w_0 recomputed inline
                let mut w0 = E4::ONE;
                for j in 0..delta {
                    let mut one_minus = E4::ONE;
                    one_minus.sub_assign(&challenges[j as usize]);
                    w0.mul_assign(&one_minus);
                }
                let mut dot = leaves[0];
                dot.mul_assign(&w0);
                let mut weight_sum = w0;
                for q in 1..leaves.len() {
                    let mut term = leaves[q];
                    term.mul_assign(&weights[base + q - 1]);
                    dot.add_assign(&term);
                    weight_sum.add_assign(&weights[base + q - 1]);
                }
                assert_eq!(pyramid, flat, "pyramid != difference form at delta {delta}");
                assert_eq!(pyramid, dot, "pyramid != Lagrange dot at delta {delta}");
                assert_eq!(
                    weight_sum,
                    E4::ONE,
                    "partition of unity broken at delta {delta}"
                );
            }
        }
    }
}

#[test]
fn fold_weights_zero_the_deltas_a_round_cannot_reach() {
    let mut state = E4::ONE;
    let mut g = E4::ONE;
    g.add_assign(&E4::ONE);
    let claim_point: Vec<E4> = (0..2).map(|_| next_e4(&mut state, &g)).collect();
    let weights = expected_fold_weights(2, &claim_point);
    for slot in BWD_SEG_FOLD_WEIGHT_BASE_D3..BWD_SEG_FOLD_WEIGHT_SLOTS {
        assert_eq!(
            weights[slot],
            E4::ZERO,
            "delta-3 slot {slot} must be zero at round 2"
        );
    }
    assert_ne!(weights[BWD_SEG_FOLD_WEIGHT_BASE_D1], E4::ZERO);
}

// ── Per-launch DRAM traffic floors (measurement-trust pass §7.2.2) ────────────

/// **Dedupe and span, each pinned EXACTLY — "the read floor rises" would pass on any
/// monotone bug.** The walk is a pure function of the descriptor, so both properties
/// are testable by CONSTRUCTING the descriptor rather than hoping a fixture exhibits
/// them.
#[test]
fn the_traffic_floor_dedupes_by_backing_and_scales_with_fold_depth() {
    let floor_of = |setup: &BwdSegSetup| {
        bwd_seg_traffic_floor(setup, CoeffMode::Constant, ProgramMode::Inline)
    };
    // Two E4 sources of one window, already at target depth: delta 0, no publish.
    let lower = || {
        lower_one(
            &ext_artifact(),
            2,
            bound(Some(e4_column(0)), 2, 2, false),
            2,
            1,
            D2Policy::Inline,
        )
        .expect("a legal E4 round")
    };

    // (a) DEDUPE. Two slots naming the SAME `(window, column)` read the same bytes,
    // and under perfect caching the second reference is a hit.
    let mut duplicated = lower();
    {
        let desc = inline_desc_mut(&mut duplicated);
        desc.source[1] = desc.source[0];
        assert_eq!(desc.num_sources, 2, "both slots stay live");
    }
    let mut single = lower();
    {
        let desc = inline_desc_mut(&mut single);
        desc.num_sources = 1;
    }
    assert_eq!(
        floor_of(&duplicated).read_bytes,
        floor_of(&single).read_bytes,
        "a byte read by two slots of one backing counts ONCE",
    );
    // ...and a THIRD, DISTINCT column raises it by exactly that column's span.
    let mut three = lower();
    let third_span;
    {
        let desc = inline_desc_mut(&mut three);
        desc.source[1] = desc.source[0];
        desc.source[2] = BwdSegSourceRecord {
            src: super::seg_desc::bwd_seg_lane(0, 1).expect("slot 0 column 1"),
            cache: BWD_SEG_ADDR_NONE,
            class: desc.source[0].class,
            delta: desc.source[0].delta,
        };
        desc.num_sources = 3;
        // The window is E4 at delta 0: `16 B x 2^0 x 2 x logical_rows`.
        third_span = u64::from(E4_BYTES) * 2 * u64::from(desc.logical_rows);
    }
    assert_eq!(
        floor_of(&three).read_bytes,
        floor_of(&duplicated).read_bytes + third_span,
        "a distinct column adds exactly `element_width * 2^delta * 2 * logical_rows`",
    );

    // (b) SPAN. One descriptor, delta 0 then delta 3, everything else held fixed.
    let mut flat = lower();
    let mut deep = lower();
    let eq = eq_term(inline_desc(&flat));
    assert_eq!(eq, eq_term(inline_desc(&deep)), "the eq term is held fixed");
    {
        let desc = inline_desc_mut(&mut flat);
        for record in desc.source.iter_mut() {
            record.delta = 0;
        }
    }
    {
        let desc = inline_desc_mut(&mut deep);
        for record in desc.source.iter_mut() {
            record.delta = 3;
        }
    }
    assert_eq!(
        floor_of(&deep).read_bytes - eq,
        8 * (floor_of(&flat).read_bytes - eq),
        "the source term scales by exactly 2^3 / 2^0 while the eq term does not scale",
    );

    // (c) The WRITE floor, against the descriptor's own two fields — on a launch that
    // publishes as well as on one that does not.
    for setup in [
        lower(),
        lower_one(
            &bf_artifact(),
            3,
            bound(Some(bf_column(0)), 0, 3, true),
            2,
            1,
            D2Policy::Inline,
        )
        .expect("a legal d3 pyramid round"),
    ] {
        let desc = inline_desc(&setup);
        assert_eq!(
            floor_of(&setup).write_bytes,
            (u64::from(desc.num_foldable) * 2 + 2)
                * u64::from(desc.logical_rows)
                * u64::from(E4_BYTES),
            "two published e4 per foldable source plus the two contributions, per row",
        );
    }
    assert_eq!(
        inline_desc(
            &lower_one(
                &bf_artifact(),
                3,
                bound(Some(bf_column(0)), 0, 3, true),
                2,
                1,
                D2Policy::Inline,
            )
            .expect("a legal d3 pyramid round")
        )
        .num_foldable,
        2,
        "the publishing case is non-vacuous",
    );
}

#[test]
fn the_eq_term_uses_a_bit_width_not_a_length() {
    // `eq_sizes.low` is a LOG2 LENGTH. An earlier draft's `eq_sizes.low * 16 B`
    // understated this term by `(1 << low)/low` — at `low = 16` that is 4,096x,
    // which would have made the eq term invisible instead of, plausibly, one of the
    // floor's larger entries. It is also the only non-source DRAM read on the path,
    // so nothing else absorbed the error.
    let floor_of = |setup: &BwdSegSetup| {
        bwd_seg_traffic_floor(setup, CoeffMode::Constant, ProgramMode::Inline).read_bytes
    };
    let with_low = |low: u32| {
        let mut setup = lower_one(
            &ext_artifact(),
            2,
            bound(Some(e4_column(0)), 2, 2, false),
            2,
            1,
            D2Policy::Inline,
        )
        .expect("a legal E4 round");
        inline_desc_mut(&mut setup).eq_sizes.low = low;
        setup
    };
    // `low = 0` is one entry, so it isolates the source term without re-deriving it.
    let base = with_low(0);
    let rows = u64::from(inline_desc(&base).logical_rows);
    let sources = floor_of(&base) - u64::from(E4_BYTES);
    assert!(rows > 8, "the fixture must straddle both sides of the min");
    for low in [3u32, 10] {
        let setup = with_low(low);
        assert_eq!(
            floor_of(&setup),
            sources + rows.min(1u64 << low) * u64::from(E4_BYTES),
            "the eq term is `min(logical_rows, 1 << low) * 16` at low = {low}",
        );
    }
    // Both directions of the `min` were exercised: a table narrower than the launch
    // and one wider than it.
    assert!((1u64 << 3) < rows && (1u64 << 10) > rows);
}

#[test]
fn procedural_sources_contribute_no_read_traffic() {
    // `seg_raw_synthesized` produces the value from the backing INDEX, so a
    // procedural leaf reads no DRAM at all.
    let floor_of = |setup: &BwdSegSetup| {
        bwd_seg_traffic_floor(setup, CoeffMode::Constant, ProgramMode::Inline).read_bytes
    };
    let one_source = program(&[record(0, 0, 0, SOURCE_NONE)]);
    let procedural = artifact(
        ArtifactRegime::Ext,
        3,
        vec![virtual_setup(2, 0)],
        slots(&[(0, 0)]),
        one_source.clone(),
    );
    let matrix_backed = artifact(
        ArtifactRegime::Ext,
        3,
        vec![base_witness(&[0])],
        slots(&[(0, 0)]),
        one_source,
    );
    let virtual_only = lower_one(
        &procedural,
        2,
        bound(None, 0, 2, false),
        1,
        1,
        D2Policy::Inline,
    )
    .expect("a legal procedural round");
    let raw = lower_one(
        &matrix_backed,
        2,
        bound(Some(bf_column(0)), 0, 2, false),
        1,
        1,
        D2Policy::Inline,
    )
    .expect("a legal inline-d2 round");
    let desc = inline_desc(&virtual_only);
    assert_eq!(desc.slot[0].origin, BWD_COEFF_ORIGIN_PROCEDURAL);
    // The procedural launch's whole read floor IS its eq term: no source contributes.
    assert_eq!(floor_of(&virtual_only), eq_term(desc));
    // And the difference against the matrix-backed twin is exactly the raw source's
    // span at its own fold depth (`bf`, delta 2) — ONE endpoint's worth: the only
    // reference is a `C0Linear` term, and `seg_project` resolves Endpoint0 from
    // the low halves alone.
    let raw_desc = inline_desc(&raw);
    assert_eq!(eq_term(desc), eq_term(raw_desc), "same round, same eq");
    assert_eq!(
        floor_of(&raw) - floor_of(&virtual_only),
        u64::from(BF_BYTES) * 4 * u64::from(raw_desc.logical_rows),
    );
}

/// **The §7.3 fix, pinned at both promotion edges.** `seg_project` resolves ONLY
/// the halves a projection needs, so the read floor prices each backing at the
/// MAX endpoint factor over the slots that share it: the low halves alone while
/// every reader is a `C0Linear*` term, the full pair set as soon as ONE
/// `DualProduct`/`C2Product` reference — or the fold-and-publish pass — touches
/// it. Pricing every backing at both halves is the R0 headline overstatement the
/// measurement-trust pass caught (331.8 B/row, 4 of 4 captures below the soft
/// bound).
#[test]
fn endpoint0_only_backings_price_one_half() {
    let floor_of = |setup: &BwdSegSetup| {
        bwd_seg_traffic_floor(setup, CoeffMode::Constant, ProgramMode::Inline).read_bytes
    };
    // Two backings of one raw `bf` window at delta 2; slots 0 and 1 SHARE the
    // first backing, slot 2 is the second.
    let lower_with = |records: &[[u16; 4]]| {
        let shape = artifact(
            ArtifactRegime::Ext,
            3,
            vec![base_witness(&[0, 1])],
            slots(&[(0, 0), (0, 0), (0, 1)]),
            program(records),
        );
        lower_one(
            &shape,
            2,
            bound(Some(bf_column(0)), 0, 2, false),
            2,
            1,
            D2Policy::Inline,
        )
        .expect("a legal inline-d2 round")
    };
    // Every reference `C0Linear` -> both backings price ONE endpoint each.
    let c0_only = lower_with(&[
        record(0, 0, 0, SOURCE_NONE),
        record(0, 0, 1, SOURCE_NONE),
        record(0, 0, 2, SOURCE_NONE),
    ]);
    // One `DualProduct` over slots 1 and 2 -> BOTH backings promote to the full
    // pair set: slot 1 promotes the backing it shares with the still-`C0Linear`
    // slot 0 (per-backing MAX, not per-slot), slot 2 promotes its own.
    let mixed = lower_with(&[record(0, 0, 0, SOURCE_NONE), record(1, 0, 1, 2)]);
    let half_span =
        |setup: &BwdSegSetup| u64::from(BF_BYTES) * 4 * u64::from(inline_desc(setup).logical_rows);
    assert_eq!(
        floor_of(&c0_only) - eq_term(inline_desc(&c0_only)),
        2 * half_span(&c0_only),
        "two Endpoint0-only backings, one endpoint each",
    );
    assert_eq!(
        floor_of(&mixed) - floor_of(&c0_only),
        2 * half_span(&mixed),
        "one DualProduct reference promotes both backings to the pair set",
    );
    // The fold promotes too: `bf_artifact`'s materializing twin publishes, and
    // `the_materializing_launch_reads_alike_and_writes_more` holds its read floor
    // equal to the inline twin's BECAUSE that fixture's `DualProduct` already
    // spans both halves. An Endpoint0-only program under a materializing policy
    // is the same promotion through `fold_source`, asserted here at delta 2.
    let single_c0 = |materialize: bool, d2: D2Policy| {
        let shape = artifact(
            ArtifactRegime::Ext,
            3,
            vec![base_witness(&[0])],
            slots(&[(0, 0)]),
            program(&[record(0, 0, 0, SOURCE_NONE)]),
        );
        lower_one(
            &shape,
            2,
            bound(Some(bf_column(0)), 0, 2, materialize),
            1,
            1,
            d2,
        )
        .expect("a legal d2 round")
    };
    let inline = single_c0(false, D2Policy::Inline);
    let materializing = single_c0(true, D2Policy::Materialize);
    assert_eq!(inline_desc(&materializing).num_foldable, 1);
    assert_eq!(
        floor_of(&materializing) - floor_of(&inline),
        half_span(&inline),
        "the fold-and-publish pass reads the halves the Endpoint0 eval never touches",
    );
}

/// The two D2 policy paths have DIFFERENT floors — but **the difference is in the
/// WRITE in the materializing launch, not in that launch's reads.** Spec §7.2.2 is
/// explicit: "A **prologue materializing fold** counts both: the raw read once, at the
/// launch that folds it, **and** the publish write", and the delta-1 `e4` read is what
/// "then ... per later round" refers to. So in the launch that materializes, BOTH
/// paths read the same raw delta-2 backing; only `Materialize` also publishes.
///
/// An earlier draft asserted the delta-1 `e4` read against `Inline`'s raw read *in the
/// same launch*, which contradicts the frozen formula and would have failed the very
/// walk it was meant to pin.
#[test]
fn the_materializing_launch_reads_alike_and_writes_more() {
    // The SAME `(circuit, layer, round)` coordinate under both policies: one base
    // window two folds behind, at round 2. `materialize` is the policy's own ABI
    // representation, so it moves with the policy and nothing else does.
    let lower = |d2: D2Policy, materialize: bool| {
        lower_one(
            &bf_artifact(),
            2,
            bound(Some(bf_column(0)), 0, 2, materialize),
            2,
            1,
            d2,
        )
        .unwrap_or_else(|error| panic!("{d2:?}: {error:?}"))
    };
    let inline = lower(D2Policy::Inline, false);
    let materialize = lower(D2Policy::Materialize, true);
    let floor_of = |setup: &BwdSegSetup| {
        bwd_seg_traffic_floor(setup, CoeffMode::Constant, ProgramMode::Inline)
    };
    let (inline_desc_ref, materialize_desc) = (inline_desc(&inline), inline_desc(&materialize));
    // The policies really did diverge, and only in the publish.
    assert_eq!(
        inline_desc_ref.source[0].class,
        SourceClass::BfInlineD2.code()
    );
    assert_eq!(
        materialize_desc.source[0].class,
        SourceClass::E4Direct.code()
    );
    assert_eq!(inline_desc_ref.num_foldable, 0);
    assert_eq!(materialize_desc.num_foldable, 2);
    // Both walk the same raw delta-2 backing IN THIS LAUNCH: equality, exactly.
    assert_eq!(
        floor_of(&inline).read_bytes,
        floor_of(&materialize).read_bytes,
        "the materializing launch reads the same raw delta-2 backing",
    );
    // The write differs by exactly the publish `Inline` does not perform.
    assert_eq!(
        floor_of(&materialize).write_bytes - floor_of(&inline).write_bytes,
        (u64::from(materialize_desc.num_foldable) - u64::from(inline_desc_ref.num_foldable))
            * 2
            * u64::from(materialize_desc.logical_rows)
            * u64::from(E4_BYTES),
    );
}

/// The delta-1 `e4` read belongs to the LATER round, and that is where it must be
/// asserted — by constructing the materialized state and lowering round `r + 1`.
#[test]
fn the_later_round_reads_the_published_pair_rather_than_recomputing() {
    let single = artifact(
        ArtifactRegime::Ext,
        3,
        vec![base_witness(&[0])],
        slots(&[(0, 0)]),
        program(&[record(0, 0, 0, SOURCE_NONE)]),
    );
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    let floor_read = |setup: &BwdSegSetup| {
        bwd_seg_traffic_floor(setup, CoeffMode::Constant, ProgramMode::Inline).read_bytes
    };

    // ── The MATERIALIZED arm: round 2 publishes, round 3 chains off it ────────
    let publishing = [bound(Some(bf_column(0)), 0, 2, true)];
    let scratch = scratch_for(
        plan_scratch(
            &[&[], &[], &publishing[..], &publishing[..]],
            &[&[], &[], &[1], &[1]],
            &ROWS[..4],
        )
        .expect("a legal two-round plan"),
    );
    lower_bwd_seg(
        &single,
        &round_binding(2, &single, &publishing, &read_elements, &claim, &coeffs),
        &scratch,
        1,
        D2Policy::Materialize,
        ProgramMode::Inline,
        CoeffMode::Constant,
    )
    .expect("round 2 materializes");
    let (chain_ptr, chain_stride) =
        chain_read_column(&scratch, 3, 0).expect("round 2 published this window");
    let chained = [bound(
        Some(column_at(chain_ptr as usize, true, chain_stride)),
        2,
        3,
        true,
    )];
    let later = lower_bwd_seg(
        &single,
        &round_binding(3, &single, &chained, &read_elements, &claim, &coeffs),
        &scratch,
        1,
        D2Policy::Materialize,
        ProgramMode::Inline,
        CoeffMode::Constant,
    )
    .expect("round 3 chains off round 2's publish");
    let later_desc = inline_desc(&later);
    assert_eq!(later_desc.slot[0].origin, BWD_COEFF_ORIGIN_READ_EXT);
    assert_eq!(
        later_desc.source[0].delta,
        1,
        "the chain step is delta 1",
    );
    assert_eq!(
        floor_read(&later) - eq_term(later_desc),
        u64::from(E4_BYTES) * 2 * 2 * u64::from(later_desc.logical_rows),
        "a materialized source contributes `16 B x 2^1 x 2 x logical_rows`",
    );

    // ── The INLINE arm: nothing published, so round 3 refolds the RAW backing ─
    let raw = [bound(Some(bf_column(0)), 0, 3, true)];
    let inline_scratch = scratch_for(
        plan_scratch(
            &[&[], &[], &[], &raw[..]],
            &[&[], &[], &[], &[1]],
            &ROWS[..4],
        )
        .expect("a legal plan whose round 2 published nothing"),
    );
    let recomputed = lower_bwd_seg(
        &single,
        &round_binding(3, &single, &raw, &read_elements, &claim, &coeffs),
        &inline_scratch,
        1,
        D2Policy::Inline,
        ProgramMode::Inline,
        CoeffMode::Constant,
    )
    .expect("round 3 refolds the raw backing");
    let recomputed_desc = inline_desc(&recomputed);
    assert_eq!(recomputed_desc.slot[0].origin, BWD_COEFF_ORIGIN_READ_BASE);
    assert_eq!(
        floor_read(&recomputed) - eq_term(recomputed_desc),
        u64::from(BF_BYTES) * 8 * 2 * u64::from(recomputed_desc.logical_rows),
        "the recompute is RE-COUNTED here at its own fold span, not amortized away",
    );
    // **The POLICY-LEVEL comparison — summing these over the affected rounds — stays
    // with P3** (spec §7.2.2, §8): this pass emits per-launch floors only, and this
    // test pins the two per-launch shapes, not their aggregate.
}

#[test]
fn the_loader_variants_have_different_floors_and_that_is_correct() {
    // `ptr` carries `n_coefficients * 16 B` and `progptr` `program_words * 2 B` of
    // real device traffic their `const`/inline twins route through constant space.
    let artifact = ext_artifact();
    let bounds = [bound(Some(e4_column(0)), 2, 2, false)];
    let scratch = scratch_for(plan_for(2, &bounds, &[2]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    let lower = |prog: ProgramMode, coeff: CoeffMode| {
        lower_bwd_seg(
            &artifact,
            &round_binding(2, &artifact, &bounds, &read_elements, &claim, &coeffs),
            &scratch,
            1,
            D2Policy::Inline,
            prog,
            coeff,
        )
        .expect("a legal E4 round in every loader family")
    };

    let production = lower(ProgramMode::Inline, CoeffMode::Constant);
    let base = bwd_seg_traffic_floor(&production, CoeffMode::Constant, ProgramMode::Inline);
    let inline_view = inline_desc(&production);
    // The loader cannot be sniffed from the descriptor: the pointer is NULL here
    // because lowering leaves it null and staging patches it later.
    assert!(inline_view.coefficients.is_null());
    let coefficient_bytes = u64::from(inline_view.n_coefficients) * u64::from(E4_BYTES);
    assert!(coefficient_bytes > 0, "the payload is non-vacuous");
    assert_eq!(
        bwd_seg_traffic_floor(&production, CoeffMode::DevPtr, ProgramMode::Inline).read_bytes
            - base.read_bytes,
        coefficient_bytes,
        "`ptr` carries the coefficient payload through DRAM",
    );

    // **ProgPtr needs its OWN lowering.** The inline family's descriptor carries
    // `program_words = 0`, so asking it for a `ProgramMode::DevPtr` floor would add
    // `0 x 2 B` and prove nothing.
    let device_program = lower(ProgramMode::DevPtr, CoeffMode::Constant);
    let program_bytes = match &device_program.desc {
        BwdSegLaunchDesc::ProgPtr(desc) => u64::from(desc.program_words) * 2,
        BwdSegLaunchDesc::Inline(_) => panic!("expected the progptr descriptor"),
    };
    assert!(program_bytes > 0, "the stream is non-vacuous");
    assert_eq!(
        bwd_seg_traffic_floor(&production, CoeffMode::Constant, ProgramMode::DevPtr).read_bytes,
        base.read_bytes,
        "the inline descriptor carries no device stream to read",
    );
    assert_eq!(
        bwd_seg_traffic_floor(&device_program, CoeffMode::Constant, ProgramMode::DevPtr).read_bytes
            - base.read_bytes,
        program_bytes,
        "`progptr` carries the lean stream through DRAM",
    );
    // The same `setup` therefore gives three different floors, which is why the
    // loader is a PARAMETER and not a property the walk could have read off.
    assert_ne!(coefficient_bytes, 0);
    assert_eq!(
        bwd_seg_traffic_floor(&device_program, CoeffMode::DevPtr, ProgramMode::DevPtr).read_bytes
            - base.read_bytes,
        coefficient_bytes + program_bytes,
    );
}

#[test]
fn the_soft_bound_saturates_rather_than_underflowing() {
    assert_eq!(bwd_seg_floor_soft_bound(1_000, 4_000), 0);
    assert_eq!(bwd_seg_floor_soft_bound(10_000, 4_000), 6_000);
}

// ── The whole-atom deal and the immediates payload (spec §4.5) ────────────────

/// The mixed continuation fixture the deal tests use: two dual singletons, one
/// three-member group and one linear singleton, over one two-column `Ext` window.
/// Costs are deliberately UNEQUAL, so a round-robin split and the least-loaded
/// deal disagree.
fn grouped_ext_artifact() -> LeanCoordinateArtifact {
    artifact(
        ArtifactRegime::Ext,
        3,
        vec![ext_output(1, &[0, 1])],
        slots(&[(0, 0), (0, 1)]),
        grouped_program(
            &[
                record(1, 2, 0, 1),
                header(3, 3, LEAN_GROUP_FLAG_C0),
                record(0, 0, 0, SOURCE_NONE),
                record(0, 1, 1, SOURCE_NONE),
                record(0, 2, 0, SOURCE_NONE),
                record(0, 4, 1, SOURCE_NONE),
                record(1, 5, 0, 1),
            ],
            6,
        ),
    )
}

/// [`lower_one`] with an explicit immediate table on the round binding.
fn lower_with_immediates(
    artifact: &LeanCoordinateArtifact,
    round: u32,
    bound_window: FixtureWindow,
    columns: usize,
    k: usize,
    immediates: &[u32],
) -> Result<BwdSegSetup, BwdSegLowerError> {
    let bounds = [bound_window];
    let scratch = scratch_for(plan_for(round as usize, &bounds, &[columns]));
    let claim = claim_point(8);
    let coeffs = coefficients(4);
    let read_elements = generous(1);
    let mut binding = round_binding(round, &artifact, &bounds, &read_elements, &claim, &coeffs);
    binding.immediates = immediates;
    lower_bwd_seg(
        artifact,
        &binding,
        &scratch,
        k,
        D2Policy::Inline,
        ProgramMode::Inline,
        CoeffMode::Constant,
    )
}

/// Every record of one list span, as `(class, coefficient field)` pairs.
fn list_records(desc: &BwdSegDesc, list: usize) -> Vec<(u16, u16)> {
    let lo = usize::from(desc.list_offset[list]);
    let hi = usize::from(desc.list_offset[list + 1]);
    desc.program[lo..hi]
        .chunks_exact(LEAN_WORDS_PER_TERM)
        .map(|record| (record[0] >> 13, record[0] & 0x1fff))
        .collect()
}

/// The deal's two structural promises: it is a deterministic function of the
/// program (same bytes twice), and it never lets a group straddle a `list_offset`
/// boundary — a header and its `N` members always land in one list, contiguously.
#[test]
fn deal_is_deterministic_and_whole_atom() {
    let artifact = grouped_ext_artifact();
    let immediates = [7u32];
    for k in [1usize, 2, 3, 4, 8] {
        let lower = || {
            lower_with_immediates(
                &artifact,
                2,
                bound(Some(e4_column(0)), 2, 2, false),
                2,
                k,
                &immediates,
            )
            .unwrap_or_else(|error| panic!("k {k}: {error:?}"))
        };
        let setup = lower();
        assert_eq!(
            setup.desc.launch_bytes(),
            lower().desc.launch_bytes(),
            "k {k}: the deal is a pure function of the program",
        );

        let desc = inline_desc(&setup);
        // RECORDS, headers included: seven records for six terms.
        assert_eq!(desc.record_count, 7, "k {k}: the count field is records");
        assert_eq!(
            usize::from(desc.list_offset[k]),
            7 * LEAN_WORDS_PER_TERM,
            "k {k}: every record is emitted exactly once",
        );

        let mut seen_headers = 0;
        let mut seen_records = 0;
        for list in 0..k {
            let records = list_records(desc, list);
            seen_records += records.len();
            let mut index = 0;
            while index < records.len() {
                let (class, _) = records[index];
                if class != LEAN_CONT_GROUP_HEADER_CLASS {
                    index += 1;
                    continue;
                }
                seen_headers += 1;
                // The header's own word1 is the member count; re-read it from the
                // stream rather than trusting the fixture.
                let lo = usize::from(desc.list_offset[list]);
                let members = usize::from(desc.program[lo + index * LEAN_WORDS_PER_TERM + 1]);
                assert_eq!(members, 3, "k {k} list {list}: the fixture's group");
                assert!(
                    index + members < records.len(),
                    "k {k} list {list}: the group's members are inside the list",
                );
                for member in 1..=members {
                    assert_ne!(
                        records[index + member].0,
                        LEAN_CONT_GROUP_HEADER_CLASS,
                        "k {k} list {list}: a member is not a header",
                    );
                }
                index += 1 + members;
            }
        }
        assert_eq!(seen_headers, 1, "k {k}: exactly one header, in one list");
        assert_eq!(seen_records, 7, "k {k}: every record placed once");
    }
}

/// The balance property spec §4.5 rests on: because every atom lands on a list at
/// or below the current mean, the busiest list ends within one MAX-ATOM cost of the
/// average. Randomized costs, so the bound is tested against shapes no fixture
/// spells out.
#[test]
fn deal_balance_bound() {
    // A deterministic LCG: randomized inputs, reproducible failures.
    let mut state = 0x2545_F491_4F6C_DD1Du64;
    let mut next = |bound: u64| {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (state >> 33) % bound
    };
    for case in 0..200 {
        let atoms = 1 + (case % 37);
        let k = 1 + (case % 8);
        let costs: Vec<u64> = (0..atoms).map(|_| next(140)).collect();
        let lists = deal_atoms(&costs, k);

        // A partition: every atom exactly once, and lists in ascending order.
        let mut placed: Vec<usize> = lists.iter().flatten().copied().collect();
        placed.sort_unstable();
        assert_eq!(placed, (0..atoms).collect::<Vec<_>>(), "case {case}");
        for list in &lists {
            assert!(list.windows(2).all(|pair| pair[0] < pair[1]), "case {case}");
        }

        // The deal's own currency is `cost.max(1)`, so the bound is stated in it.
        let charged = |atom: usize| costs[atom].max(1);
        let loads: Vec<u64> = lists
            .iter()
            .map(|list| list.iter().copied().map(charged).sum())
            .collect();
        let total: u64 = (0..atoms).map(charged).sum();
        let max_atom = (0..atoms).map(charged).max().unwrap_or(0);
        let max_load = loads.iter().copied().max().unwrap_or(0);
        let average = total as f64 / k as f64;
        assert!(
            max_load as f64 <= average + max_atom as f64 + 1e-9,
            "case {case}: k {k} max {max_load} > avg {average} + max atom {max_atom}: {loads:?}",
        );
    }
}

/// The deal is a GENERALIZATION of the incumbent split, not a different policy:
/// with equal costs, least-loaded-with-lowest-index-ties IS round-robin. That is
/// what keeps a uniform-cost program's stream (and the R0 regime, which uses
/// `split_round_robin` directly) unchanged.
#[test]
fn deal_uniform_costs_degenerate_to_round_robin() {
    for atoms in 0..12usize {
        let positions: Vec<usize> = (0..atoms).collect();
        for k in 1..6usize {
            for cost in [0u64, 1, 7, 1_000] {
                assert_eq!(
                    deal_atoms(&vec![cost; atoms], k),
                    split_round_robin(&positions, k),
                    "atoms {atoms} k {k} cost {cost}",
                );
            }
        }
    }
}

// ── The K-aware group chop ────────────────────────────────────────────────────

/// The record capacity production hands the chop: the inline descriptor's.
const CHOP_RECORD_CAPACITY: usize = LEAN_DESCRIPTOR_PROGRAM_WORDS / LEAN_WORDS_PER_TERM;

/// A `+1` linear member over a direct read: `member_work` 1, the chop tests'
/// unit currency.
fn chop_linear_member() -> SegMember {
    SegMember {
        annotated: AnnotatedTerm {
            category: TermCategory::C0LinearE4,
            operands: [Some(SourceClass::E4Direct), None],
        },
        immediate: 0,
    }
}

/// A dual singleton over direct reads: `static_term_work` 10.
fn chop_dual_term() -> SegAtom {
    SegAtom::Term(AnnotatedTerm {
        category: TermCategory::DualProductE4,
        operands: [Some(SourceClass::E4Direct), Some(SourceClass::E4Direct)],
    })
}

/// `(first record, records)` spans in committed order, the shape
/// `lower_bwd_seg` computes for its atoms.
fn chop_spans(atoms: &[SegAtom]) -> Vec<(usize, usize)> {
    let mut spans = Vec::with_capacity(atoms.len());
    let mut record = 0usize;
    for atom in atoms {
        let span = match atom {
            SegAtom::Term(_) => 1,
            SegAtom::Group { members, .. } => 1 + members.len(),
        };
        spans.push((record, span));
        record += span;
    }
    spans
}

/// An atom at or below the chop threshold passes through whole — the units are
/// the atoms one-for-one, groups included, and nothing about the deal changes.
#[test]
fn chop_leaves_light_atoms_whole() {
    let atoms = vec![
        chop_dual_term(),
        SegAtom::Group {
            core: 2,
            has_c0: true,
            has_c2: false,
            members: vec![chop_linear_member(); 4],
        },
        chop_dual_term(),
        chop_dual_term(),
    ];
    let spans = chop_spans(&atoms);
    // total 36, k 1: the threshold is 9 and the group costs 6.
    let units = chop_atoms(&atoms, &spans, 1, CHOP_RECORD_CAPACITY);
    assert_eq!(units.len(), atoms.len(), "one unit per atom");
    for ((unit, atom), &(first, span)) in units.iter().zip(&atoms).zip(&spans) {
        assert_eq!(unit.cost, atom_work(atom), "a whole atom keeps its cost");
        assert_eq!(unit.emit, SegUnitEmit::Atom { first, span });
    }
}

/// The chop rule itself: a group above `total / (4 k)` splits into
/// `ceil(work / threshold)` even whole-member chunks, first chunks taking the
/// remainder, every chunk sharing the header's core and flags by construction.
#[test]
fn chop_splits_a_dominant_group_into_even_whole_member_chunks() {
    let atoms = vec![
        SegAtom::Group {
            core: 2,
            has_c0: true,
            has_c2: false,
            members: vec![chop_linear_member(); 12],
        },
        chop_dual_term(),
    ];
    let spans = chop_spans(&atoms);
    // total 24, k 3: threshold 2, the group costs 14 -> ceil(14 / 2) = 7 chunks,
    // amortized to 12 / (2 * 2) = 3 of four members each.
    let units = chop_atoms(&atoms, &spans, 3, CHOP_RECORD_CAPACITY);
    assert_eq!(units.len(), 3 + 1);
    for (chunk, unit) in units[..3].iter().enumerate() {
        assert_eq!(
            unit.emit,
            SegUnitEmit::GroupChunk {
                header: 0,
                first_member: 1 + 4 * chunk,
                members: 4,
            },
            "chunk {chunk}: consecutive whole members after the header",
        );
        assert_eq!(
            unit.cost,
            4 + 2,
            "chunk {chunk}: four members plus the core"
        );
    }
    assert_eq!(units[3].emit, SegUnitEmit::Atom { first: 13, span: 1 });
    assert_eq!(units[3].cost, 10);
}

/// Chunk costs are computed over the chunk's OWN members — heterogeneous members
/// land where they land — and each chunk repays the core multiply in full, which
/// is the only work the chop adds.
#[test]
fn chop_prices_each_chunk_by_its_own_members() {
    let dual_member = SegMember {
        annotated: AnnotatedTerm {
            category: TermCategory::DualProductE4,
            operands: [Some(SourceClass::E4Direct), Some(SourceClass::E4Direct)],
        },
        immediate: 1,
    };
    let group = SegAtom::Group {
        core: 3,
        has_c0: true,
        has_c2: true,
        members: vec![
            dual_member.clone(),
            dual_member,
            chop_linear_member(),
            chop_linear_member(),
        ],
    };
    let group_work = atom_work(&group);
    assert_eq!(group_work, 8 + 8 + 2 + 4, "the fixture's arithmetic");
    let atoms = vec![group, chop_dual_term()];
    let spans = chop_spans(&atoms);
    // total 32, k 2: threshold 4, ceil(22 / 4) = 6 amortized to
    // 18 / (2 * 4) = 2 chunks.
    let units = chop_atoms(&atoms, &spans, 2, CHOP_RECORD_CAPACITY);
    assert_eq!(units.len(), 2 + 1);
    assert_eq!(units[0].cost, 8 + 8 + 4, "the dual-heavy front chunk");
    assert_eq!(units[1].cost, 1 + 1 + 4, "the linear tail chunk");
    assert_eq!(
        units[0].cost + units[1].cost,
        group_work + 4,
        "the chop's whole overhead is one repaid core",
    );
}

/// The chop's floor is AMORTIZATION, not a member count: at most one chunk per
/// `2 * core_work` of member work, so the repaid cores never inflate a group's
/// work by more than half its members'. Light members bundle up to reach that
/// bar; a group whose members cannot amortize even one extra core stays whole
/// no matter what the threshold wants.
#[test]
fn chop_amortizes_headers_against_member_work() {
    let group = |members: usize| SegAtom::Group {
        core: 2,
        has_c0: true,
        has_c2: false,
        members: vec![chop_linear_member(); members],
    };

    // Five light members against a core of 2: member work 5 affords
    // 5 / 4 = 1 chunk — no chop at all, though threshold 1 wants seven.
    let atoms = vec![group(5)];
    let units = chop_atoms(&atoms, &chop_spans(&atoms), 8, CHOP_RECORD_CAPACITY);
    assert_eq!(units.len(), 1);
    assert_eq!(units[0].emit, SegUnitEmit::Atom { first: 0, span: 6 });
    assert_eq!(units[0].cost, 5 + 2);

    // Sixteen light members afford 16 / 4 = 4 chunks of four — each chunk's
    // members outweigh its repaid core two to one.
    let atoms = vec![group(16)];
    let units = chop_atoms(&atoms, &chop_spans(&atoms), 8, CHOP_RECORD_CAPACITY);
    assert_eq!(units.len(), 4);
    for (chunk, unit) in units.iter().enumerate() {
        assert_eq!(
            unit.emit,
            SegUnitEmit::GroupChunk {
                header: 0,
                first_member: 1 + 4 * chunk,
                members: 4,
            },
            "chunk {chunk}",
        );
        assert_eq!(unit.cost, 4 + 2, "chunk {chunk}");
    }
}

/// A two-member group of HEAVY members chops to single-member chunks: the floor
/// is work amortization, not a member count. A dual pair is the corpus's worst
/// deal spike (a thin layer's whole imbalance in one atom), and each dual repays
/// its own core many times over — so the pair splits.
#[test]
fn chop_splits_a_heavy_pair_into_single_member_chunks() {
    let dual_member = SegMember {
        annotated: AnnotatedTerm {
            category: TermCategory::DualProductE4,
            operands: [Some(SourceClass::E4Direct), Some(SourceClass::E4Direct)],
        },
        immediate: 0,
    };
    let atoms = vec![
        SegAtom::Group {
            core: 2,
            has_c0: true,
            has_c2: false,
            members: vec![dual_member; 2],
        },
        chop_dual_term(),
    ];
    let spans = chop_spans(&atoms);
    // total 28, k 8: threshold 1; the pair costs 18, member work 16 against a
    // core of 2 -> the amortization cap 16 / 4 = 4 allows every member its own
    // chunk, clamped to the two members there are.
    let units = chop_atoms(&atoms, &spans, 8, CHOP_RECORD_CAPACITY);
    assert_eq!(units.len(), 2 + 1);
    for (chunk, unit) in units[..2].iter().enumerate() {
        assert_eq!(
            unit.emit,
            SegUnitEmit::GroupChunk {
                header: 0,
                first_member: 1 + chunk,
                members: 1,
            },
            "chunk {chunk}: one heavy member each",
        );
        assert_eq!(unit.cost, 8 + 2, "chunk {chunk}: its dual plus the core");
    }
    assert_eq!(units[2].emit, SegUnitEmit::Atom { first: 3, span: 1 });
}

/// Every chunk header the chop adds is a record the descriptor must hold, so the
/// chop spends a RECORD BUDGET — capacity minus the artifact's own records — in
/// committed order, degrading each group's chunk count before dropping the chop
/// entirely. A program already at capacity chops nothing and lowers exactly as
/// before.
#[test]
fn chop_spends_the_record_budget_in_committed_order() {
    let dual_member = SegMember {
        annotated: AnnotatedTerm {
            category: TermCategory::DualProductE4,
            operands: [Some(SourceClass::E4Direct), Some(SourceClass::E4Direct)],
        },
        immediate: 0,
    };
    let group = |members: usize| SegAtom::Group {
        core: 2,
        has_c0: true,
        has_c2: false,
        members: vec![dual_member.clone(); members],
    };
    // Two eight-dual groups: 18 records, and at k 8 (threshold 4) each wants
    // ceil(66 / 4) = 17 chunks, member-clamped to 8 — seven extra headers
    // apiece if the budget allowed them.
    let atoms = vec![group(8), group(8)];
    let spans = chop_spans(&atoms);

    // Budget 4: the first group takes the 5 chunks four headers buy — the even
    // split hands the remainder forward, three pairs then two singles — and the
    // second group's chop is dropped entirely.
    let units = chop_atoms(&atoms, &spans, 8, 18 + 4);
    let shapes: Vec<_> = units.iter().map(|unit| unit.emit).collect();
    assert_eq!(
        shapes,
        vec![
            SegUnitEmit::GroupChunk {
                header: 0,
                first_member: 1,
                members: 2,
            },
            SegUnitEmit::GroupChunk {
                header: 0,
                first_member: 3,
                members: 2,
            },
            SegUnitEmit::GroupChunk {
                header: 0,
                first_member: 5,
                members: 2,
            },
            SegUnitEmit::GroupChunk {
                header: 0,
                first_member: 7,
                members: 1,
            },
            SegUnitEmit::GroupChunk {
                header: 0,
                first_member: 8,
                members: 1,
            },
            SegUnitEmit::Atom { first: 9, span: 9 },
        ],
    );

    // Budget 0: no chop at all — the whole atoms, verbatim.
    let units = chop_atoms(&atoms, &spans, 8, 18);
    let shapes: Vec<_> = units.iter().map(|unit| unit.emit).collect();
    assert_eq!(
        shapes,
        vec![
            SegUnitEmit::Atom { first: 0, span: 9 },
            SegUnitEmit::Atom { first: 9, span: 9 },
        ],
    );
}

/// The chop end to end: a group that dominates its program is emitted as SEVERAL
/// headers sharing the original's core and flags, every member exactly once, and
/// the lists it used to unbalance come out even.
#[test]
fn a_dominant_group_chops_across_lists_and_rebalances() {
    // One eight-member group (work 10) and two dual singletons (work 10 each):
    // whole atoms at k 2 deal 20 against 10; chopped, both lists load 16.
    let members: Vec<[u16; 4]> = (0..8)
        .map(|index| record(0, index % 2, index % 2, SOURCE_NONE))
        .collect();
    let mut records = vec![header(3, 8, LEAN_GROUP_FLAG_C0)];
    records.extend(&members);
    records.push(record(1, 2, 0, 1));
    records.push(record(1, 4, 0, 1));
    let artifact = artifact(
        ArtifactRegime::Ext,
        3,
        vec![ext_output(1, &[0, 1])],
        slots(&[(0, 0), (0, 1)]),
        grouped_program(&records, 10),
    );
    let k = 2;
    let setup = lower_with_immediates(
        &artifact,
        2,
        bound(Some(e4_column(0)), 2, 2, false),
        2,
        k,
        &[],
    )
    .expect("a legal round");
    let desc = inline_desc(&setup);

    // total 30, k 2: threshold 3, the group (10) wants ceil(10 / 3) = 4 chunks,
    // amortized to 8 / (2 * 2) = 2 of four members — two headers where the
    // original had one.
    assert_eq!(
        desc.record_count, 12,
        "8 members + 2 headers + 2 singletons"
    );
    assert_eq!(usize::from(desc.list_offset[k]), 12 * LEAN_WORDS_PER_TERM);

    let mut seen_headers = 0usize;
    let mut seen_members: Vec<[u16; 4]> = Vec::new();
    let mut singletons = 0usize;
    for list in 0..k {
        let lo = usize::from(desc.list_offset[list]);
        let hi = usize::from(desc.list_offset[list + 1]);
        let records: Vec<&[u16]> = desc.program[lo..hi]
            .chunks_exact(LEAN_WORDS_PER_TERM)
            .collect();
        let mut index = 0usize;
        while index < records.len() {
            let word0 = records[index][0];
            if (word0 >> 13) != LEAN_CONT_GROUP_HEADER_CLASS {
                singletons += 1;
                index += 1;
                continue;
            }
            seen_headers += 1;
            assert_eq!(
                word0,
                (LEAN_CONT_GROUP_HEADER_CLASS << 13) | 3,
                "list {list}: a chunk header keeps the original core",
            );
            let count = usize::from(records[index][1]);
            assert_eq!(count, 4, "list {list}: even four-member chunks");
            assert_eq!(records[index][2], LEAN_GROUP_FLAG_C0, "list {list}: flags");
            assert_eq!(records[index][3], 0, "list {list}: the reserved zero");
            assert!(index + count < records.len(), "list {list}: members inside");
            for member in &records[index + 1..=index + count] {
                seen_members.push([member[0], member[1], member[2], member[3]]);
            }
            index += 1 + count;
        }
    }
    assert_eq!(seen_headers, 2);
    assert_eq!(singletons, 2);
    let mut expected = members;
    expected.sort_unstable();
    seen_members.sort_unstable();
    assert_eq!(
        seen_members, expected,
        "every member exactly once, verbatim"
    );

    // Chunk costs 6 each, duals 10: the deal loads both lists to 16.
    assert!(
        (setup.work.max_over_mean - 1.0).abs() < 1e-9,
        "the chopped deal is balanced: {:?}",
        setup.work,
    );
}

/// The chop never grows a stream past the inline descriptor: a program one record
/// short of the 8,624-word capacity gets exactly one extra header's worth of
/// chop — two chunks — and lowers AT capacity, never over it.
#[test]
fn chop_clamps_to_the_descriptor_capacity() {
    // 2155 records = 8620 words; at k 8 the threshold alone would want 33
    // chunks, but the budget is ONE record.
    let mut records = vec![header(2, 2154, LEAN_GROUP_FLAG_C0)];
    records.extend(std::iter::repeat_n(record(0, 0, 0, SOURCE_NONE), 2154));
    let artifact = artifact(
        ArtifactRegime::Ext,
        3,
        vec![ext_output(1, &[0, 1])],
        slots(&[(0, 0), (0, 1)]),
        grouped_program(&records, 2154),
    );
    assert_eq!(artifact.program.words.len(), 8620, "the fixture's premise");
    let setup = lower_with_immediates(
        &artifact,
        2,
        bound(Some(e4_column(0)), 2, 2, false),
        2,
        8,
        &[],
    )
    .expect("the chop clamps instead of overflowing");
    let desc = inline_desc(&setup);
    assert_eq!(
        usize::from(desc.list_offset[8]),
        LEAN_DESCRIPTOR_PROGRAM_WORDS,
        "the emitted stream lands exactly at capacity",
    );
    assert_eq!(usize::from(desc.record_count), 2156);
    let headers: Vec<u16> = desc.program[..LEAN_DESCRIPTOR_PROGRAM_WORDS]
        .chunks_exact(LEAN_WORDS_PER_TERM)
        .filter(|record| (record[0] >> 13) == LEAN_CONT_GROUP_HEADER_CLASS)
        .map(|record| record[1])
        .collect();
    assert_eq!(headers, vec![1077, 1077], "two even chunks from one header");
}

/// **R0 is untouched.** Its split is `split_round_robin` over positions, and this
/// pins the emitted stream against that rule directly — over a program whose costs
/// are UNEQUAL, so a stream produced by the Ext deal would differ and the pin has
/// teeth.
#[test]
fn r0_stream_is_byte_identical() {
    let records = [
        record(0, 0, 0, SOURCE_NONE),
        record(2, 1, 0, 1),
        record(0, 2, 1, SOURCE_NONE),
        record(2, 3, 0, 1),
        record(0, 4, 0, SOURCE_NONE),
    ];
    let artifact = artifact(
        ArtifactRegime::R0,
        0,
        vec![base_witness(&[0, 1])],
        slots(&[(0, 0), (0, 1)]),
        program(&records),
    );
    // `C0LinearBf` costs 2, `C2ProductBfBf` costs 6 — the deal and round-robin
    // genuinely disagree on this program.
    let costs = [2u64, 6, 2, 6, 2];
    let positions: Vec<usize> = (0..records.len()).collect();
    for k in [1usize, 2, 3, 5] {
        let setup = lower_one(
            &artifact,
            0,
            bound(Some(bf_column(0)), 0, 0, false),
            2,
            k,
            D2Policy::Inline,
        )
        .unwrap_or_else(|error| panic!("k {k}: {error:?}"));
        let desc = inline_desc(&setup);

        let lists = split_round_robin(&positions, k);
        let mut expected: Vec<u16> = Vec::new();
        for list in &lists {
            for &position in list {
                expected.extend_from_slice(&records[position]);
            }
        }
        assert_eq!(
            &desc.program[..expected.len()],
            &expected[..],
            "k {k}: the R0 stream is round-robin over positions",
        );
        assert_eq!(usize::from(desc.list_offset[k]), expected.len());
        assert_eq!(desc.record_count as usize, records.len());
        // At `k >= records` every split is one-atom-per-list and the two rules
        // coincide trivially; below that they genuinely disagree on these costs,
        // which is what makes the pin above a statement about the R0 path.
        if k > 1 && k < records.len() {
            assert_ne!(
                deal_atoms(&costs, k),
                lists,
                "k {k}: the deal would have produced a different stream",
            );
        }
    }
}

/// Grouping moves no bytes: a header carries no sources, so the read floor, the
/// endpoint spans and the write floor of a grouped coordinate are those of the same
/// terms ungrouped — by construction, and pinned here.
#[test]
fn grouped_fixture_floor_matches_ungrouped() {
    let windows = vec![ext_output(1, &[0, 1])];
    let source_slots = slots(&[(0, 0), (0, 1)]);
    let grouped = artifact(
        ArtifactRegime::Ext,
        3,
        windows.clone(),
        source_slots.clone(),
        grouped_program(
            &[
                header(2, 2, LEAN_GROUP_FLAG_C0),
                record(0, 0, 0, SOURCE_NONE),
                record(0, 1, 1, SOURCE_NONE),
            ],
            2,
        ),
    );
    let ungrouped = artifact(
        ArtifactRegime::Ext,
        3,
        windows,
        source_slots,
        program(&[record(0, 2, 0, SOURCE_NONE), record(0, 2, 1, SOURCE_NONE)]),
    );

    let lower = |shape: &LeanCoordinateArtifact| {
        lower_one(
            shape,
            2,
            bound(Some(e4_column(0)), 2, 2, false),
            2,
            2,
            D2Policy::Inline,
        )
        .expect("a legal round")
    };
    let grouped = lower(&grouped);
    let ungrouped = lower(&ungrouped);

    assert_eq!(
        grouped.source_endpoints, ungrouped.source_endpoints,
        "a header projects nothing, so no slot changes its endpoint span",
    );
    assert_eq!(grouped.dead_sources, ungrouped.dead_sources);
    assert_eq!(
        bwd_seg_traffic_floor(&grouped, CoeffMode::Constant, ProgramMode::Inline),
        bwd_seg_traffic_floor(&ungrouped, CoeffMode::Constant, ProgramMode::Inline),
        "the floor is unchanged by grouping",
    );
    // The RECORD count is what does change: one header on top of two terms.
    assert_eq!(inline_desc(&grouped).record_count, 3);
    assert_eq!(inline_desc(&ungrouped).record_count, 2);
}

/// The one cost rule grouping exists for: a member pays NO coefficient base.
/// `static_term_work`'s `C0Linear` 2 is "one E4 multiply-add against the
/// coefficient" — work a grouped member does not do, because the group's single
/// core multiply (priced per active side on the atom) replaced every member's.
#[test]
fn atom_work_prices_members_without_coefficient_base() {
    let annotated = |category, operands| AnnotatedTerm { category, operands };
    let member = |category, operands, immediate| SegMember {
        annotated: annotated(category, operands),
        immediate,
    };

    let linear = member(
        TermCategory::C0LinearE4,
        [Some(SourceClass::E4Direct), None],
        0,
    );
    assert_eq!(member_work(&linear), 1, "a +1 C0 member over a direct read");
    assert_eq!(
        static_term_work(&linear.annotated),
        2,
        "the same record as a SINGLETON keeps its coefficient FMA",
    );
    // `-1` is the other literal, and just as free.
    assert_eq!(
        member_work(&member(
            TermCategory::C0LinearE4,
            [Some(SourceClass::E4Direct), None],
            1,
        )),
        1,
    );
    // A non-±1 immediate costs one BF x E4 per active side: one linear, two dual.
    assert_eq!(
        member_work(&member(
            TermCategory::C0LinearE4,
            [Some(SourceClass::E4Direct), None],
            2,
        )),
        1 + 1,
    );
    let dual = member(
        TermCategory::DualProductE4,
        [Some(SourceClass::E4Direct), Some(SourceClass::E4Direct)],
        1,
    );
    assert_eq!(member_work(&dual), 8, "a dual member keeps both products");
    assert_eq!(
        member_work(&member(
            TermCategory::DualProductE4,
            [Some(SourceClass::E4Direct), Some(SourceClass::E4Direct)],
            5,
        )),
        8 + 2,
    );
    // Operand resolution is the member's in full — it reads the same sources.
    assert_eq!(
        member_work(&member(
            TermCategory::C0LinearE4,
            [Some(SourceClass::BfInlineD1), None],
            0,
        )),
        1 + 4,
    );

    // The atom adds two per ACTIVE side for the core multiply, and nothing else.
    let group = |has_c0, has_c2| SegAtom::Group {
        core: 2,
        has_c0,
        has_c2,
        members: vec![linear, dual],
    };
    assert_eq!(atom_work(&group(true, false)), 1 + 8 + 2);
    assert_eq!(atom_work(&group(false, true)), 1 + 8 + 2);
    assert_eq!(atom_work(&group(true, true)), 1 + 8 + 4);
    // A plain record's cost is `static_term_work` verbatim.
    assert_eq!(
        atom_work(&SegAtom::Term(linear.annotated)),
        static_term_work(&linear.annotated),
    );
}

/// A table past the wire cap is rejected HERE, where the walk sees it — the
/// descriptor's inline capacity (Task 8) only mirror-asserts the same bound.
#[test]
fn immediate_table_overflow_rejected() {
    let over = vec![1u32; LEAN_MAX_IMMEDIATES + 1];
    assert_eq!(
        lower_with_immediates(
            &ext_artifact(),
            2,
            bound(Some(e4_column(0)), 2, 2, false),
            2,
            2,
            &over,
        ),
        Err(BwdSegLowerError::ImmediateTableOverflow {
            len: LEAN_MAX_IMMEDIATES + 1,
        }),
    );
    // The cap itself is legal.
    assert!(lower_with_immediates(
        &ext_artifact(),
        2,
        bound(Some(e4_column(0)), 2, 2, false),
        2,
        2,
        &over[..LEAN_MAX_IMMEDIATES],
    )
    .is_ok());
}

/// A member id the table cannot answer is a rejection, not a device-side read past
/// the array. `record` is the member's own RECORD index, headers included.
#[test]
fn immediate_out_of_range_rejected() {
    let shape = artifact(
        ArtifactRegime::Ext,
        3,
        vec![ext_output(1, &[0, 1])],
        slots(&[(0, 0), (0, 1)]),
        grouped_program(
            &[
                header(2, 2, LEAN_GROUP_FLAG_C0),
                record(0, 2, 0, SOURCE_NONE),
                record(0, 3, 1, SOURCE_NONE),
            ],
            2,
        ),
    );
    // One entry: ids 0 and 1 are the literals, id 2 is the entry, id 3 is past it.
    let one = [11u32];
    assert_eq!(
        lower_with_immediates(
            &shape,
            2,
            bound(Some(e4_column(0)), 2, 2, false),
            2,
            2,
            &one,
        ),
        Err(BwdSegLowerError::ImmediateOutOfRange { record: 2, id: 3 }),
    );
    // Two entries and the same program is legal, so the reject is about the BOUND.
    assert!(lower_with_immediates(
        &shape,
        2,
        bound(Some(e4_column(0)), 2, 2, false),
        2,
        2,
        &[11u32, 13],
    )
    .is_ok());
}

/// **The conversion the kernel will trust (Task 9).** The immediate table travels
/// as canonical base-field integers and is converted ONCE, host-side, into the
/// in-memory (Montgomery) representation a device `bf` load sees — never in the
/// eval loop. Pinned against the Montgomery definition computed independently
/// (`value * 2^32 mod p`), not against the conversion under test.
#[test]
fn immediate_montgomery_conversion_pin() {
    let montgomery =
        |value: u32| -> u32 { (((u64::from(value)) << 32) % u64::from(BF::ORDER)) as u32 };
    // The literal for canonical one is `2^32 mod p`, spelled out so a change of
    // representation cannot pass as a change of formula.
    assert_eq!(montgomery(1), 0x0fff_fffe);
    assert_eq!(
        BF::from_u32_with_reduction(1).as_u32_raw_repr_reduced(),
        montgomery(1)
    );

    let canonical = [1u32, 0x1234_5678, BF::ORDER - 1, 0];
    let expected: Vec<u32> = canonical.iter().copied().map(montgomery).collect();
    // Round-trip: the stored form still reads back as the canonical value.
    for &value in &canonical {
        assert_eq!(BF::from_u32_with_reduction(value).as_u32_reduced(), value);
    }

    let setup = lower_with_immediates(
        &ext_artifact(),
        2,
        bound(Some(e4_column(0)), 2, 2, false),
        2,
        2,
        &canonical,
    )
    .expect("a legal round");
    assert_eq!(
        setup.immediates, expected,
        "lowering stores the kernel-ready form, in table order",
    );
    // An ungrouped coordinate carries none.
    let bare = lower_one(
        &ext_artifact(),
        2,
        bound(Some(e4_column(0)), 2, 2, false),
        2,
        2,
        D2Policy::Inline,
    )
    .expect("a legal round");
    assert!(bare.immediates.is_empty());
}
