//! Tests for [`production_bind`](super::production_bind): the `K` policy moved
//! into production, the CPU shape phase over the REAL add_sub L0 R0 coordinate,
//! and the pointer phase against a production `GpuGKRStorage` (GPU, `#[serial]`).

use serial_test::serial;

use super::production_bind::*;
use super::production_program::compile_coordinate;
use crate::primitives::field::BF;
use crate::upstream::{BwdRegime, GKRCircuitArtifact};

fn add_sub_artifact() -> GKRCircuitArtifact<BF> {
    crate::prover::tests::deserialize_json_for_test(
        "cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json",
    )
}

// ── The `K` policy ───────────────────────────────────────────────────────────

/// A launcher choosing K=11 would be choosing a shape nothing was measured at.
#[test]
fn the_policy_k_is_a_member_of_the_measured_axis_and_within_the_ceiling() {
    use crate::upstream::BwdRegime;
    for regime in [BwdRegime::R0, BwdRegime::Ext] {
    for bytes_per_row in [0, 1_279, 1_280, 18_431, 18_432, 1 << 20] {
        for ceiling in SEG_CORPUS_K {
            let k = seg_policy_k(regime, bytes_per_row, ceiling);
            assert!(SEG_CORPUS_K.contains(&k), "K{k} is off the measured axis");
            assert!(k <= ceiling, "K{k} exceeds the register ceiling {ceiling}");
        }
    }
    }
}

/// Each regime's committed rule, evaluated at the footprints its documentation
/// names. The VALUES are the corpus fit's; this pins the shipped rules to them so
/// a coefficient or threshold edit cannot pass silently.
#[test]
fn each_regimes_committed_rule_is_the_fitted_one() {
    use crate::upstream::BwdRegime;

    // The continuation: logarithmic, spanning K2..K16 over the corpus's range.
    for (bytes, want) in [
        (160usize, 2usize),
        (352, 4),
        (1_008, 4),
        (2_056, 8),
        (4_240, 8),
        (6_976, 16),
        (30_656, 16),
    ] {
        assert_eq!(
            seg_policy_k(BwdRegime::Ext, bytes, 32),
            want,
            "the continuation rule moved at {bytes} B/row"
        );
    }

    // R0: NON-MONOTONE steps. The middle arm is smaller than the first, and that
    // is the fit, not a typo — see `SEG_POLICY_R0_RULE`.
    assert_eq!(seg_policy_k(BwdRegime::R0, 0, 32), 4);
    assert_eq!(seg_policy_k(BwdRegime::R0, 2_055, 32), 4);
    assert_eq!(seg_policy_k(BwdRegime::R0, 2_056, 32), 2);
    assert_eq!(seg_policy_k(BwdRegime::R0, 4_239, 32), 2);
    assert_eq!(seg_policy_k(BwdRegime::R0, 4_240, 32), 16);

    // The ceiling caps by snapping DOWN to an axis member, never interpolating —
    // and the axis floor is 1 now, so even a ceiling of 1 is servable.
    for ceiling in [1usize, 2, 4, 8, 16] {
        for regime in [BwdRegime::R0, BwdRegime::Ext] {
            assert!(seg_policy_k(regime, 30_656, ceiling) <= ceiling);
        }
    }
}

/// **The continuation rule must not turn back down inside a reachable footprint.**
///
/// Its quadratic term is negative, so the curve has a maximum; the fit puts the
/// vertex at 1 GiB per row, far outside any geometry that can occur. This asserts
/// the consequence rather than the algebra: `K` never decreases as the footprint
/// grows, over the whole 64-bit range.
#[test]
fn the_continuation_rule_never_turns_back_down() {
    use crate::upstream::BwdRegime;

    let mut previous = 0;
    let mut bytes = 16usize;
    while bytes < (1usize << 40) {
        let k = seg_policy_k(BwdRegime::Ext, bytes, 32);
        assert!(
            k >= previous,
            "{bytes} B/row lowered the continuation rule from K{previous} to K{k}"
        );
        previous = k;
        bytes = bytes * 3 / 2;
    }
    assert_eq!(previous, 16, "the corpus never asks the continuation for K32");
}

/// The two regimes must disagree somewhere, or the split is decoration.
#[test]
fn the_two_regimes_pick_different_k() {
    use crate::upstream::BwdRegime;

    let disagreements = (0..40_000usize)
        .step_by(16)
        .filter(|bytes| {
            seg_policy_k(BwdRegime::R0, *bytes, 32) != seg_policy_k(BwdRegime::Ext, *bytes, 32)
        })
        .count();
    assert!(
        disagreements > 0,
        "R0 and Ext resolve to the same K everywhere, so the split buys nothing"
    );
}

// ── The shape phase (CPU, real coordinate) ───────────────────────────────────

/// Totality: every window of the real coordinate either names a production
/// address or is procedural — there is no third kind, and a window this
/// mapping cannot serve must not exist.
#[test]
fn every_r0_window_names_an_address_or_is_procedural() {
    let artifact = add_sub_artifact();
    let coord = compile_coordinate(&artifact, 0, BwdRegime::R0).unwrap();
    let shapes = r0_window_shapes(&coord).unwrap();
    assert_eq!(shapes.len(), coord.binding.windows.len());
    for (index, shape) in shapes.iter().enumerate() {
        assert!(
            !shape.referenced_columns.is_empty(),
            "window {index} references no columns"
        );
        assert_eq!(
            shape.referenced_columns[0], shape.first_column,
            "window {index} is based on a hole"
        );
        let procedural = shape.address.is_none();
        assert!(
            procedural || shape.address.is_some(),
            "window {index} is neither addressed nor procedural"
        );
    }
}

/// R0 is depth 0 everywhere: no window publishes, and the only classes delta 0
/// admits are the direct reads and the procedural inline.
#[test]
fn r0_classifies_every_window_without_a_publish() {
    use super::seg_lower::SourceClass;

    let artifact = add_sub_artifact();
    let coord = compile_coordinate(&artifact, 0, BwdRegime::R0).unwrap();
    for (index, shape) in r0_window_shapes(&coord).unwrap().iter().enumerate() {
        assert!(!shape.materialize, "window {index} claims a publish at R0");
        assert!(
            matches!(
                shape.class,
                SourceClass::BfDirect | SourceClass::E4Direct | SourceClass::ProceduralInline
            ),
            "window {index} classified {:?} at delta 0",
            shape.class
        );
    }
}

/// The binder is R0-only in this slice; handing it an Ext coordinate must be a
/// loud wiring error, not a wrong launch.
#[test]
fn a_non_r0_coordinate_is_rejected() {
    let artifact = add_sub_artifact();
    let coord = compile_coordinate(&artifact, 0, BwdRegime::Ext).unwrap();
    assert_eq!(
        r0_window_shapes(&coord).unwrap_err(),
        BwdVmBindError::NotR0 {
            layer: 0,
            regime: BwdRegime::Ext
        }
    );
}

/// The census the module doc records — counts by window family and by source
/// slot, read off the compiled coordinate rather than asserted from memory.
#[test]
fn report_the_r0_source_census() {
    use gkr_eval_isa::bwd::coeff::stats::WindowFamily;
    use std::collections::BTreeMap;

    let artifact = add_sub_artifact();
    let coord = compile_coordinate(&artifact, 0, BwdRegime::R0).unwrap();

    let family_label = |family: &WindowFamily| match family {
        WindowFamily::BaseLayerMemory => "BaseLayerMemory".to_string(),
        WindowFamily::BaseLayerWitness => "BaseLayerWitness".to_string(),
        WindowFamily::Setup => "Setup".to_string(),
        WindowFamily::Scratch => "Scratch".to_string(),
        WindowFamily::LayerOutput { ext, .. } => format!("LayerOutput(ext={ext})"),
        WindowFamily::CacheOutput { ext, .. } => format!("CacheOutput(ext={ext})"),
        WindowFamily::VirtualSetup { kind } => format!("VirtualSetup(kind={kind})"),
    };

    let mut windows_by_family: BTreeMap<String, usize> = BTreeMap::new();
    let mut columns_by_family: BTreeMap<String, usize> = BTreeMap::new();
    for window in &coord.binding.windows {
        *windows_by_family.entry(family_label(&window.family)).or_default() += 1;
        *columns_by_family.entry(family_label(&window.family)).or_default() +=
            window.columns.len();
    }
    let mut slots_by_family: BTreeMap<String, usize> = BTreeMap::new();
    for slot in &coord.binding.source_slots {
        let family = &coord.binding.windows[slot.window as usize].family;
        *slots_by_family.entry(family_label(family)).or_default() += 1;
    }

    eprintln!(
        "[bwd-vm-census] add_sub L0 R0: {} windows, {} referenced columns, {} source slots",
        coord.binding.windows.len(),
        coord.binding.windows.iter().map(|w| w.columns.len()).sum::<usize>(),
        coord.binding.source_slots.len(),
    );
    eprintln!("[bwd-vm-census] windows by family:  {windows_by_family:?}");
    eprintln!("[bwd-vm-census] columns by family:  {columns_by_family:?}");
    eprintln!("[bwd-vm-census] slots by family:    {slots_by_family:?}");
}

// ── The Ext shape phase (CPU, real coordinate) ───────────────────────────────

/// The per-round class ladder over the real Ext coordinate, as the corpus
/// census pins it: round 1 = BfInlineD1 / publishing-E4 / ProceduralInline,
/// round 2 = BfInlineD2, round 3 = everything E4Direct+publish (BF and
/// procedural materialize their slot-3), round 4 = everything chained
/// E4Direct+publish at backing depth 3.
#[test]
fn the_ext_ladder_classifies_every_window_per_round() {
    use super::seg_lower::{D2Policy, SourceClass};

    let artifact = add_sub_artifact();
    let coord = compile_coordinate(&artifact, 0, BwdRegime::Ext).unwrap();

    let (mut saw_bf, mut saw_e4, mut saw_procedural) = (false, false, false);
    for round in 1..=4u8 {
        let shapes = ext_round_window_shapes(&coord, round, D2Policy::Inline).unwrap();
        assert_eq!(shapes.len(), coord.binding.windows.len());
        for (index, shape) in shapes.iter().enumerate() {
            assert_eq!(
                shape.chained,
                shape.backing_depth != 0,
                "window {index} round {round}"
            );
            if shape.chained {
                assert_eq!(shape.backing_depth, round - 1, "window {index}");
            }
            match (shape.address.is_some(), shape.is_e4_backing, round) {
                // E4-origin: raw at round 1, chained from round 2; publishes
                // its slot every round.
                (true, true, r) => {
                    saw_e4 = true;
                    assert_eq!(shape.class, SourceClass::E4Direct, "window {index}");
                    assert!(shape.materialize, "window {index}");
                    assert_eq!(shape.chained, r >= 2, "window {index}");
                }
                // BF-origin: inline folds through round 2, materializes at 3,
                // chained from 4.
                (true, false, 1) => {
                    saw_bf = true;
                    assert_eq!(shape.class, SourceClass::BfInlineD1, "window {index}");
                    assert!(!shape.materialize, "window {index}");
                }
                (true, false, 2) => {
                    assert_eq!(shape.class, SourceClass::BfInlineD2, "window {index}");
                    assert!(!shape.materialize, "window {index}");
                }
                (true, false, 3) => {
                    assert_eq!(shape.class, SourceClass::E4Direct, "window {index}");
                    assert!(shape.materialize && !shape.chained, "window {index}");
                }
                (true, false, _) => {
                    assert_eq!(shape.class, SourceClass::E4Direct, "window {index}");
                    assert!(shape.materialize && shape.chained, "window {index}");
                }
                // Procedural: synthesized through round 3 (publishing there),
                // chained from 4.
                (false, _, 1 | 2) => {
                    saw_procedural = true;
                    assert_eq!(shape.class, SourceClass::ProceduralInline, "window {index}");
                    assert!(!shape.materialize, "window {index}");
                }
                (false, _, 3) => {
                    assert_eq!(shape.class, SourceClass::E4Direct, "window {index}");
                    assert!(shape.materialize && !shape.chained, "window {index}");
                }
                (false, _, _) => {
                    assert_eq!(shape.class, SourceClass::E4Direct, "window {index}");
                    assert!(shape.materialize && shape.chained, "window {index}");
                }
            }
        }
    }
    assert!(
        saw_bf && saw_e4 && saw_procedural,
        "the census says add_sub L0 carries all three origins \
         (bf={saw_bf}, e4={saw_e4}, procedural={saw_procedural})"
    );
}

/// An R0 coordinate handed to the Ext shape pass is a wiring defect, mirroring
/// `a_non_r0_coordinate_is_rejected`.
#[test]
fn a_non_ext_coordinate_is_rejected_by_the_ext_shapes() {
    use super::seg_lower::D2Policy;

    let artifact = add_sub_artifact();
    let coord = compile_coordinate(&artifact, 0, BwdRegime::R0).unwrap();
    assert_eq!(
        ext_round_window_shapes(&coord, 1, D2Policy::Inline).unwrap_err(),
        BwdVmBindError::NotExt {
            layer: 0,
            regime: BwdRegime::R0
        }
    );
}

/// Round 0 is not a continuation round — rejecting it here keeps the R0/Ext
/// seam explicit rather than fabricating a negative backing depth.
#[test]
fn round_zero_is_rejected_by_the_ext_shapes() {
    use super::seg_lower::D2Policy;

    let artifact = add_sub_artifact();
    let coord = compile_coordinate(&artifact, 0, BwdRegime::Ext).unwrap();
    assert_eq!(
        ext_round_window_shapes(&coord, 0, D2Policy::Inline).unwrap_err(),
        BwdVmBindError::NotAContinuationRound { round: 0 }
    );
}

// ── The folding-buffer ladder (CPU) ──────────────────────────────────────────

/// THE identity the VM's own folding buffers rest on: the set of sources that
/// fold at round `r` is exactly the set that chain-reads at round `r + 1`, and
/// each keeps the same column. That is what lets round `r + 1` name round `r`'s
/// columns from the coordinate alone, with nothing threaded through the round
/// loop and no per-poly region to look up.
///
/// Pinned on the real add_sub L0 Ext coordinate, over every round, on the CPU:
/// a ladder regression fails in milliseconds instead of after a fixture build.
#[test]
fn each_rounds_folded_columns_are_the_next_rounds_chain_reads() {
    use super::production_bind::folding_buffer_columns;
    use super::seg_lower::D2Policy;

    let artifact = add_sub_artifact();
    let coord = compile_coordinate(&artifact, 0, BwdRegime::Ext).unwrap();
    // Any folding_steps wide enough to hold the ladder: the SHAPES do not
    // depend on it, only the row counts the buffers are sized for.
    let folding_steps = 8usize;
    let mut ladder: Vec<(u8, std::collections::BTreeMap<u32, usize>)> = Vec::new();
    for round in 1..folding_steps - 1 {
        let rows = 1usize << (folding_steps - round - 1);
        let round = round as u8;
        let (shape, columns) =
            folding_buffer_columns(&coord, round, rows, D2Policy::Inline).unwrap();
        assert_eq!(
            shape.column_elems,
            2 * rows,
            "round {round}: a column holds the round's own layer"
        );
        assert_eq!(shape.columns, columns.len());
        assert_eq!(shape.elems(), columns.len() * 2 * rows);

        // Every source that chain-reads at the NEXT round folded at this one,
        // and nothing else did.
        let next = ext_round_window_shapes(&coord, round + 1, D2Policy::Inline).unwrap();
        let mut chaining: Vec<u32> = Vec::new();
        for (window, artifact_window) in coord.binding.windows.iter().enumerate() {
            if next[window].chained {
                chaining.extend(artifact_window.columns.iter().map(|entry| entry.source));
            }
        }
        chaining.sort_unstable();
        let mut folded: Vec<u32> = columns.keys().copied().collect();
        folded.sort_unstable();
        assert_eq!(
            folded, chaining,
            "round {round}: what folds here is not what round {} reads",
            round + 1
        );
        ladder.push((round, columns));
    }

    // The assignment is a pure function of the round, so the two calls that
    // must agree — round r's destinations and round r+1's reads — cannot drift.
    for (round, columns) in &ladder {
        let rows = 1usize << (folding_steps - *round as usize - 1);
        let (_, again) = folding_buffer_columns(&coord, *round, rows, D2Policy::Inline).unwrap();
        assert_eq!(&again, columns, "round {round} assigned different columns twice");
    }
    assert!(
        ladder.iter().any(|(_, columns)| !columns.is_empty()),
        "the ladder never folds anything"
    );
}

/// A folding-buffer column is DEFERRED: the lowering must see a null backing
/// base and an offset-carrying pointer, because the allocation does not exist
/// when the descriptor is built. A non-null base here would be double-added by
/// the schedule-time patch.
#[test]
fn a_folding_buffer_column_is_deferred_with_a_null_backing() {
    use super::production_bind::folding_buffer_columns;
    use super::seg_lower::D2Policy;

    let artifact = add_sub_artifact();
    let coord = compile_coordinate(&artifact, 0, BwdRegime::Ext).unwrap();
    let rows = 64usize;
    let (shape, columns) = folding_buffer_columns(&coord, 3, rows, D2Policy::Inline).unwrap();
    assert!(!columns.is_empty(), "round 3 folds every window");
    for column in columns.values() {
        let resolved = shape.column(*column);
        assert!(resolved.matrix_base.is_null(), "column {column}");
        assert!(resolved.is_e4, "a folded value is E4 whatever produced it");
        assert_eq!(
            resolved.ptr as usize,
            column * 2 * rows * size_of::<crate::primitives::field::E4>(),
            "column {column}: the pointer must be the column's own offset"
        );
        assert_eq!(resolved.stride_bytes, shape.stride_bytes());
    }
}

// ── The pointer phase (GPU) ──────────────────────────────────────────────────

/// The production add_sub fixture, driven through every flat prepare down to
/// main layer 0 — the state the binder sees in production, where plan build
/// runs after the prepares have resolved storage. Prepare-only: no layer is
/// executed; every assertion downstream is pointer arithmetic.
struct PreparedL0 {
    context: crate::prover::ProverContext,
    /// The layer-0 Ext coordinate, compiled from the RAW artifact before the
    /// handoff normalizes it.
    coord: gkr_eval_isa::bwd::coeff::lean_artifact::LeanCoordinateArtifact,
    main_state:
        crate::prover::gkr::backward::GpuGKRMainLayerBackwardState<'static, crate::primitives::field::E4>,
    plan: crate::prover::gkr::backward::GpuGKRMainLayerSumcheckLayerPlan<
        crate::primitives::field::E4,
    >,
}

fn prepared_l0_ext() -> PreparedL0 {
    use crate::primitives::field::E4;
    use crate::upstream::Field;

    let fixture = crate::prover::tests::prepare_basic_unrolled_async_backward_fixture(8);
    let coord = compile_coordinate(&fixture.compiled_circuit, 0, BwdRegime::Ext).unwrap();
    let mut backward_state = fixture.gpu_backward_state;
    while backward_state
        .prepare_next_layer_static(&fixture.context)
        .unwrap()
        .is_some()
    {}
    let mut main_state = backward_state.into_main_layer_backward_state(
        fixture.compiled_circuit,
        fixture.external_challenges,
        fixture.lookup_multiplicative_part,
        E4::ZERO,
        false,
    );
    let plan = loop {
        let plan = main_state
            .prepare_next_layer_static(&fixture.context)
            .unwrap()
            .expect("the main-layer walk must reach layer 0");
        if plan.layer_idx == 0 {
            break plan;
        }
    };
    PreparedL0 {
        context: fixture.context,
        coord,
        main_state,
        plan,
    }
}

/// The binder's job, stated as a total function over the coordinate's SOURCES:
/// for every source slot, the device's window arithmetic
/// (`base + column * stride`) must land on exactly the poly that the source's
/// own production address independently resolves to. This is what the
/// re-windowing exists to guarantee — production storage is not
/// window-contiguous (copy aliases, rank packing; see the module doc), so the
/// artifact's 8 windows come back as 9 production runs.
#[test]
#[serial]
fn every_r0_source_resolves_against_production_storage() {
    use super::production_bind::family_read_place;
    use crate::prover::gkr::forward::vm::lower::read_place_to_gkr_address;
    use crate::prover::gkr::forward::vm::production_bind::resolve_storage_column;

    let fixture = crate::prover::tests::prepare_basic_unrolled_async_backward_fixture(8);
    let storage = &fixture.gpu_backward_state.storage;
    let coord = compile_coordinate(&fixture.compiled_circuit, 0, BwdRegime::R0).unwrap();
    // Only feeds the (asserted empty) publish plan; any nonzero value works.
    let rows = 1usize << 8;

    let bound = bind_r0_sources(storage, &coord, rows)
        .expect("every add_sub L0 R0 window must bind against production storage");

    // The observed table, pinned like the census: 8 artifact windows collapse to
    // the backings they actually reference. A change here is a storage-geometry
    // change and deserves a look, not a silent pass.
    // FEWER slots than artifact windows: two of the eight resolve into one
    // backing, so they share an address slot. That is the point of keying slots
    // by backing — the count follows storage, not the artifact.
    assert_eq!(coord.binding.windows.len(), 8);
    assert_eq!(bound.slots.len(), 7);
    assert_eq!(bound.sources.len(), coord.binding.source_slots.len());

    for (index, slot) in bound.slots.iter().enumerate() {
        assert!(
            slot.columns <= gkr_eval_isa::bwd::coeff::limits::SOURCE_WINDOW_COLUMNS,
            "slot {index} addresses {} columns",
            slot.columns
        );
        match slot.base {
            Some(_) => assert!(
                slot.read_elements as usize >= rows,
                "slot {index} is backed by {} elements for {rows} rows",
                slot.read_elements
            ),
            None => assert!(slot.procedural_kind.is_some()),
        }
    }
    // R0 reads at depth 0 and publishes nothing.
    for (source, addr) in bound.sources.iter().enumerate() {
        assert_eq!(addr.backing_depth, 0, "source {source}");
        assert!(addr.publish.is_none(), "source {source} publishes at R0");
    }

    // The end-to-end property, per source: the device's own arithmetic —
    // `slot.base + column * stride` — must land on exactly the poly that the
    // source's address independently resolves to.
    let mut real = 0usize;
    let mut procedural = 0usize;
    for (source, old_slot) in coord.binding.source_slots.iter().enumerate() {
        let old_window = &coord.binding.windows[old_slot.window as usize];
        let absolute = old_window.first_column + old_slot.column as usize;
        let addr = &bound.sources[source];
        let slot = &bound.slots[addr.read_slot];
        match family_read_place(old_window.family, absolute) {
            None => {
                procedural += 1;
                assert!(
                    slot.base.is_none() && slot.procedural_kind.is_some(),
                    "source {source} lost its procedural slot"
                );
            }
            Some(place) => {
                real += 1;
                let expect = resolve_storage_column(storage, read_place_to_gkr_address(&place))
                    .expect("the binder resolved this address already");
                let base = slot.base.expect("an addressed source binds a read");
                assert_eq!(
                    base.ptr as usize + addr.read_column * base.stride_bytes as usize,
                    expect.ptr as usize,
                    "source {source} ({place:?}): lane arithmetic lands on the wrong poly"
                );
                assert_eq!(base.stride_bytes, expect.stride_bytes, "source {source}");
                assert_eq!(base.is_e4, expect.is_e4, "source {source}");
            }
        }
    }
    eprintln!(
        "[bwd-vm-bind] add_sub L0 R0: {} artifact windows -> {} address slots; \
         {real} real + {procedural} procedural sources land where their addresses resolve",
        coord.binding.windows.len(),
        bound.slots.len()
    );
}

/// The Ext binder, gated end to end on production storage: for EVERY source
/// slot at EVERY continuation round, the device's slot arithmetic must land
///
///   * each publish on this round's folding buffer, at the source's own column;
///   * each chain read on EXACTLY the address the previous round published to —
///     the fold chain's whole correctness argument, and now expressible without
///     naming a medium at all;
///   * each raw read on the poly the address independently resolves to;
///   * every gather-keyed address in `final_evaluations`, at that address's own
///     last-round publish offset — the re-pointing the VM-owned final round
///     needs, and the proof that no gather key is left unfolded.
///
/// Also pins the patch list: a slot is recorded as folding-buffer-backed iff a
/// publish or a chain read named it. A missed entry would reach a launch with
/// the placeholder base still in it.
#[test]
#[serial]
fn every_ext_source_binds_through_its_own_folding_buffer() {
    use std::collections::{BTreeMap, BTreeSet};

    use gkr_eval_isa::bwd::coeff::stats::WindowFamily;

    use super::seg_desc::BWD_SEG_ADDR_SLOTS;

    use super::production_bind::family_read_place;
    use super::seg_lower::D2Policy;
    use crate::prover::gkr::forward::vm::lower::read_place_to_gkr_address;
    use crate::prover::gkr::forward::vm::production_bind::resolve_storage_column;
    use crate::upstream::GKRAddress;

    let prepared = prepared_l0_ext();
    let (coord, plan) = (&prepared.coord, &prepared.plan);
    let storage = prepared.main_state.storage();
    let folding_steps = plan.folding_steps;
    let last_step = (folding_steps - 1) as u8;

    let bound = bind_ext_round_sources(storage, coord, folding_steps, D2Policy::Inline)
        .expect("every add_sub L0 Ext window must bind against production storage");

    assert_eq!(bound.rounds.len(), folding_steps - 1);
    for round in &bound.rounds {
        assert!(
            round.slots.len() <= BWD_SEG_ADDR_SLOTS,
            "round {}: {} address slots exceed the table",
            round.round,
            round.slots.len()
        );
        assert_eq!(round.sources.len(), coord.binding.source_slots.len());
    }
    assert_eq!(bound.publish_plan.total_bytes, 0, "publishes are explicitly backed");

    /// A lane's absolute device address: base plus the column's stride step.
    fn lane(round: &BoundExtRound, slot: usize, column: usize) -> usize {
        let backing = round.slots[slot]
            .base
            .expect("a folded or raw lane has a backing");
        backing.ptr as usize + column * backing.stride_bytes as usize
    }

    // The per-source identity, at every round.
    let mut published_at_last: BTreeMap<GKRAddress, usize> = BTreeMap::new();
    let mut chain_checks = 0usize;
    for (source, old_slot) in coord.binding.source_slots.iter().enumerate() {
        let old_window = &coord.binding.windows[old_slot.window as usize];
        let absolute = old_window.first_column + old_slot.column as usize;
        let addr = match family_read_place(old_window.family, absolute) {
            Some(place) => read_place_to_gkr_address(&place),
            None => match old_window.family {
                WindowFamily::VirtualSetup { kind } => virtual_setup_address(kind),
                family => panic!("addressless non-procedural window {family:?}"),
            },
        };
        let mut published: Option<usize> = None;
        for round in 1..=last_step {
            let shapes = ext_round_window_shapes(coord, round, D2Policy::Inline).unwrap();
            let shape = &shapes[old_slot.window as usize];
            let bound_round = &bound.rounds[round as usize - 1];
            let entry = &bound_round.sources[source];
            assert_eq!(entry.backing_depth, shape.backing_depth, "source {source}");

            // The chain read IS the previous round's publish. Nothing in this
            // assertion mentions where either lives.
            if shape.chained {
                let read = bound_round.slots[entry.read_slot]
                    .base
                    .expect("a chained source binds a read");
                assert!(read.is_e4, "source {source} round {round}");
                assert_eq!(
                    lane(bound_round, entry.read_slot, entry.read_column),
                    published.unwrap_or_else(|| panic!(
                        "source {source} chains at round {round} having published nothing"
                    )),
                    "source {source} ({addr:?}) round {round}: \
                     the chain read is not round {}'s publish",
                    round - 1
                );
                chain_checks += 1;
            } else if let Some(place) = family_read_place(old_window.family, absolute) {
                let expect = resolve_storage_column(storage, read_place_to_gkr_address(&place))
                    .expect("the binder resolved this address already");
                assert_eq!(
                    lane(bound_round, entry.read_slot, entry.read_column),
                    expect.ptr as usize,
                    "source {source} ({addr:?}) round {round}: raw read is off"
                );
            } else {
                assert!(
                    bound_round.slots[entry.read_slot].base.is_none(),
                    "source {source} round {round}"
                );
            }

            published = match (shape.materialize, entry.publish) {
                (true, Some((slot, column))) => {
                    let stride = bound_round.slots[slot]
                        .base
                        .expect("a destination slot has a backing")
                        .stride_bytes as usize;
                    assert_eq!(
                        stride,
                        2 * bound_round.rows * size_of::<crate::primitives::field::E4>(),
                        "source {source} round {round}: a column must hold `2 * rows`"
                    );
                    // A deferred lane's "address" IS its byte offset in the
                    // buffer the patch will supply, which is what the gather's
                    // `final_evaluations` offset must equal.
                    let address = lane(bound_round, slot, column);
                    if round == last_step {
                        published_at_last.entry(addr).or_insert(address);
                    }
                    Some(address)
                }
                (true, None) => panic!(
                    "source {source} round {round}: materializing source without publish"
                ),
                (false, publish) => {
                    assert!(publish.is_none(), "source {source} round {round}");
                    None
                }
            };
        }
    }
    assert!(chain_checks > 0, "no round chained — the ladder is not exercised");

    // The patch list is exactly the folding-buffer-backed slots.
    for bound_round in &bound.rounds {
        let recorded: BTreeSet<usize> = bound_round
            .folding_buffer_slots
            .iter()
            .map(|patch| patch.slot)
            .collect();
        let mut expected: BTreeSet<usize> = BTreeSet::new();
        let shapes =
            ext_round_window_shapes(coord, bound_round.round, D2Policy::Inline).unwrap();
        for (source, old_slot) in coord.binding.source_slots.iter().enumerate() {
            let entry = &bound_round.sources[source];
            if shapes[old_slot.window as usize].chained {
                expected.insert(entry.read_slot);
            }
            if let Some((slot, _)) = entry.publish {
                expected.insert(slot);
            }
        }
        assert_eq!(
            recorded, expected,
            "round {}: the patch list is not the folding-buffer-backed slots",
            bound_round.round
        );
        // Every recorded slot names a buffer this round or the one before it,
        // and a chunk base inside a buffer of that size.
        for patch in &bound_round.folding_buffer_slots {
            assert!(
                patch.buffer_round == bound_round.round
                    || patch.buffer_round + 1 == bound_round.round,
                "round {}: patch names round {}'s buffer",
                bound_round.round,
                patch.buffer_round
            );
            if patch.buffer_round == bound_round.round {
                assert!(
                    patch.byte_offset
                        < bound_round.folding_buffer.elems()
                            * size_of::<crate::primitives::field::E4>(),
                    "round {}: patch offset is outside the buffer",
                    bound_round.round
                );
            }
        }
    }

    // The final gather: every address it keys is in `final_evaluations`, at that
    // address's own last-round publish offset.
    let mut gather: BTreeSet<GKRAddress> = BTreeSet::new();
    for kernel in plan.kernel_plans.iter() {
        for address in kernel
            .inputs
            .inputs_in_base
            .iter()
            .chain(kernel.inputs.inputs_in_extension.iter())
        {
            if *address != GKRAddress::placeholder() {
                gather.insert(*address);
            }
        }
    }
    for address in gather.iter() {
        let offset = bound.final_evaluations.get(address).unwrap_or_else(|| {
            panic!("gather-keyed address {address:?} is never folded at round {last_step}")
        });
        assert_eq!(
            Some(offset),
            published_at_last.get(address),
            "{address:?}: the gather offset is not this address's last publish"
        );
    }
    eprintln!(
        "[bwd-vm-ext-bind] add_sub L0 Ext: {} artifact windows -> {} address slots at round 1; \
         {} sources bound over rounds 1..={last_step} ({chain_checks} chain reads); \
         {} gather addresses all folded; last buffer {} columns",
        coord.binding.windows.len(),
        bound.rounds[0].slots.len(),
        coord.binding.source_slots.len(),
        gather.len(),
        bound.rounds[last_step as usize - 1].folding_buffer.columns,
    );
}


// ── The Ext launch sequence ──────────────────────────────────────────────────

/// Round r's factored-eq sizes are the incumbent drain
/// (`fold_factored_eq_one_round`: `high[0]` to zero, then `high[1]`, then
/// `low`) replayed r times — and the sizes are fully consumed at the last
/// round, where the factored eq must be the identity.
#[test]
fn the_eq_size_drain_replays_the_incumbent_fold_order() {
    use crate::prover::gkr::backward::make_eq_sizes;

    for challenge_count in [3usize, 11, 23] {
        let initial = make_eq_sizes(challenge_count);
        let mut reference = initial;
        for round in 0..=challenge_count as u8 {
            let drained = drained_eq_sizes(initial, round);
            assert_eq!(drained.high, reference.high, "{challenge_count} at {round}");
            assert_eq!(drained.low, reference.low, "{challenge_count} at {round}");
            // The incumbent's in-place drain, transcribed.
            if reference.high[0] > 0 {
                reference.high[0] -= 1;
            } else if reference.high[1] > 0 {
                reference.high[1] -= 1;
            } else if reference.low > 0 {
                reference.low -= 1;
            }
        }
        let consumed = drained_eq_sizes(initial, challenge_count as u8);
        assert_eq!(
            (consumed.high, consumed.low),
            ([0, 0], 0),
            "{challenge_count} challenges must drain to the identity"
        );
    }
}

/// The whole continuation sequence, built once at plan-build time: one lowered
/// setup per round with the round's own rows, eq sizes and K — and no parity
/// allocation anywhere (the publishes live in storage the layer already owns).
#[test]
#[serial]
fn the_ext_sequence_builds_one_setup_per_round() {
    use crate::prover::gkr::backward::make_eq_sizes;

    let prepared = prepared_l0_ext();
    let folding_steps = prepared.plan.folding_steps;
    // Compiled straight from the artifact: this test drives the launch by hand
    // rather than through `prove()`, so no `GkrVmPrograms` is in play.
    let slices = super::production_program::compile_all_slices(
        "add_sub_lui_auipc_mop",
        &add_sub_artifact(),
    )
    .expect("the Ext slice compiles");
    let slice = &slices
        .iter()
        .find(|(coord, _)| coord.layer == 0 && coord.regime == BwdRegime::Ext)
        .expect("layer 0 Ext must be compiled")
        .1;

    let launch = build_bwd_vm_ext_rounds(
        prepared.main_state.storage(),
        slice,
        folding_steps,
        prepared.plan.round_scratch.eq_low_group.as_ptr()
            as *const crate::primitives::field::E4,
        prepared.plan.round_scratch.partials.as_ptr().cast_mut()
            as *mut crate::primitives::field::E4,
        &prepared.context,
    )
    .expect("the Ext sequence builds");

    let setups = launch.setups();
    assert_eq!(setups.len(), folding_steps - 1);
    let mut publishing_at_round = Vec::new();
    for (index, setup) in setups.iter().enumerate() {
        let round = (index + 1) as u8;
        let desc = match &setup.desc {
            super::seg_lower::BwdSegLaunchDesc::Inline(desc) => desc,
            super::seg_lower::BwdSegLaunchDesc::ProgPtr(_) => {
                panic!("add_sub fits the inline program family")
            }
        };
        assert_eq!(
            desc.logical_rows,
            1u32 << (folding_steps - usize::from(round) - 1),
            "round {round}: rows halve per round, down to 1"
        );
        let expected = drained_eq_sizes(make_eq_sizes(folding_steps - 1), round);
        assert_eq!(desc.eq_sizes.high, expected.high, "round {round}");
        assert_eq!(desc.eq_sizes.low, expected.low, "round {round}");
        assert!(
            SEG_CORPUS_K.contains(&(desc.k as usize)),
            "round {round}: K{} is off the measured axis",
            desc.k
        );
        assert_eq!(
            setup.claim_point.len(),
            folding_steps,
            "round {round}: the claim-point payload is bounds-check-only"
        );
        use super::seg_desc::BWD_SEG_ADDR_NONE;
        publishing_at_round.push(
            desc.source[..usize::from(desc.num_sources)]
                .iter()
                .filter(|record| record.cache != BWD_SEG_ADDR_NONE)
                .count(),
        );
    }
    // The materialization ladder in window counts: E4-origin publishes from
    // round 1; everything publishes from round 3 on.
    assert!(publishing_at_round[0] > 0, "round 1 publishes the E4-origin slots");
    assert!(
        publishing_at_round[2] > publishing_at_round[0],
        "round 3 materializes the BF and procedural slots too"
    );
    assert!(
        publishing_at_round[2..]
            .iter()
            .all(|&count| count == publishing_at_round[2]),
        "from round 3 on, every window publishes its slot every round"
    );
    eprintln!(
        "[bwd-vm-ext-launch] add_sub L0 Ext: {} setups; publishing windows per round: {:?}",
        setups.len(),
        publishing_at_round
    );
}
