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
    for bytes_per_row in [0, 1_279, 1_280, 18_431, 18_432, 1 << 20] {
        for ceiling in SEG_CORPUS_K {
            let k = seg_policy_k(bytes_per_row, ceiling);
            assert!(SEG_CORPUS_K.contains(&k), "K{k} is off the measured axis");
            assert!(k <= ceiling, "K{k} exceeds the register ceiling {ceiling}");
        }
    }
}

/// The three arms and the snap-down, at the committed thresholds. The VALUES
/// are the corpus fit's; this pins the shipped rule to them so a threshold
/// edit cannot pass silently.
#[test]
fn the_policy_arms_are_the_fitted_ones() {
    assert_eq!(seg_policy_k(0, 32), 4);
    assert_eq!(seg_policy_k(SEG_POLICY_NARROW_BYTES_PER_ROW - 1, 32), 4);
    assert_eq!(seg_policy_k(SEG_POLICY_NARROW_BYTES_PER_ROW, 32), 8);
    assert_eq!(seg_policy_k(SEG_POLICY_WIDE_BYTES_PER_ROW - 1, 32), 8);
    assert_eq!(seg_policy_k(SEG_POLICY_WIDE_BYTES_PER_ROW, 32), 16);
    // The ceiling caps by snapping DOWN to an axis member, never interpolating.
    assert_eq!(seg_policy_k(SEG_POLICY_WIDE_BYTES_PER_ROW, 8), 8);
    assert_eq!(seg_policy_k(SEG_POLICY_WIDE_BYTES_PER_ROW, 4), 4);
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

// ── The cascade resolver (CPU walk) ──────────────────────────────────────────

/// The incumbent ext fold-buffer walk, transcribed from
/// `GpuExtensionFieldPolyIntermediateFoldingStorage::pointer_for_sumcheck_continuation`
/// (element offsets instead of pointers). Returns (slot step-1, slot step).
fn ext_walk(size_after_one_fold: usize, step: usize) -> (usize, usize) {
    assert!(step >= 2);
    let mut input_offset = 0usize;
    let mut input_size = size_after_one_fold;
    let mut next_offset = input_size;
    for _ in 2..step {
        input_offset = next_offset;
        input_size /= 2;
        next_offset += input_size;
    }
    (input_offset, next_offset)
}

/// The incumbent base fold-buffer walk, transcribed from
/// `GpuBaseFieldPolyIntermediateFoldingStorage::pointers_for_sumcheck_accessor_step`.
fn base_walk(size_after_two_folds: usize, step: usize) -> (usize, usize) {
    assert!(step > 2);
    let mut input_offset = 0usize;
    let mut input_size = size_after_two_folds;
    let mut next_offset = input_size;
    for _ in 3..step {
        input_offset = next_offset;
        input_size /= 2;
        next_offset += input_size;
    }
    (input_offset, next_offset)
}

/// The resolver's closed-form slot walk IS the incumbents' iterative
/// fold-buffer walk, across both region shapes and every continuation round.
/// The GPU test pins the same identity against the real prepared plans; this
/// pins the arithmetic alone, so a formula regression fails in milliseconds
/// rather than after a fixture build.
#[test]
fn the_cascade_slot_walk_matches_the_incumbent_fold_buffer_walks() {
    for folding_steps in 4..=10usize {
        let n = 1usize << folding_steps;
        let backing = vec![0u8; n * 16];
        let base_ptr = backing.as_ptr().cast_mut();

        // Ext-origin: region = the whole per-poly buffer (2 * size_after_one_fold
        // = N elements); round 1 writes the first slot at offset 0.
        let ext = CascadeRegion {
            base: base_ptr,
            region_elems: n,
            first_slot: 1,
        };
        assert_eq!(ext.slot_elem_offset(1), 0, "N={n}: slot 1 heads the region");
        assert_eq!(ext.slot_elems(1), n / 2);
        for step in 2..folding_steps {
            let (prev, this) = ext_walk(n / 2, step);
            assert_eq!(ext.slot_elem_offset(step as u8 - 1), prev, "N={n} step {step}");
            assert_eq!(ext.slot_elem_offset(step as u8), this, "N={n} step {step}");
            // `this_layer_size = size_after_one_fold >> (step - 1)`.
            assert_eq!(ext.slot_elems(step as u8), (n / 2) >> (step - 1));
        }

        // Base-origin: region = 2 * size_after_two_folds = N/2 elements; the
        // first slot belongs to round 2 (`initial_pointer`); the VM's first
        // write is round 3 under `D2Policy::Inline`.
        let base = CascadeRegion {
            base: base_ptr,
            region_elems: n / 2,
            first_slot: 2,
        };
        assert_eq!(base.slot_elem_offset(2), 0, "N={n}: slot 2 heads the region");
        for step in 3..folding_steps {
            let (prev, this) = base_walk(n / 4, step);
            assert_eq!(base.slot_elem_offset(step as u8 - 1), prev, "N={n} step {step}");
            assert_eq!(base.slot_elem_offset(step as u8), this, "N={n} step {step}");
            // `this_layer_size = size_after_two_folds >> (step - 2)`.
            assert_eq!(base.slot_elems(step as u8), (n / 4) >> (step - 2));
        }

        // The VM identity that makes the publish ABI line up: slot r holds the
        // round-r layer, `2 * rows_r` values at `rows_r = 1 << (folding_steps - r - 1)`.
        for region in [&ext, &base] {
            for round in region.first_slot as usize..folding_steps {
                assert_eq!(
                    region.slot_elems(round as u8),
                    2 * (1usize << (folding_steps - round - 1)),
                    "N={n} round {round}"
                );
            }
        }

        // Byte pointers: base + elem offset * 16 (the cascade is E4-wide).
        assert_eq!(
            ext.slot_ptr(2) as usize,
            base_ptr as usize + (n / 2) * 16,
            "N={n}: slot 2 sits one half-region in"
        );
    }
}

/// A round below the region's first slot has no cascade slot — asking for one
/// is a binder wiring bug and must stop the proof, not alias slot data.
#[test]
#[should_panic(expected = "no cascade slot")]
fn a_round_below_the_first_slot_has_no_cascade_slot() {
    let region = CascadeRegion {
        base: core::ptr::null_mut(),
        region_elems: 128,
        first_slot: 2,
    };
    let _ = region.slot_elem_offset(1);
}

// ── The pointer phase (GPU) ──────────────────────────────────────────────────

/// The binder's job, stated as a total function over the coordinate's SOURCES:
/// for every source slot, the device's window arithmetic
/// (`base + column * stride`) must land on exactly the poly that the source's
/// own production address independently resolves to. This is what the
/// re-windowing exists to guarantee — production storage is not
/// window-contiguous (copy aliases, rank packing; see the module doc), so the
/// artifact's 8 windows must come back as 13 production runs.
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

    // The observed re-partition, pinned like the census: 8 artifact windows,
    // 13 production runs. A change here is a storage-geometry change and
    // deserves a look, not a silent pass.
    assert_eq!(coord.binding.windows.len(), 8);
    assert_eq!(bound.windows.len(), 13);
    assert_eq!(bound.coord.binding.windows.len(), bound.windows.len());
    assert_eq!(bound.window_read_elements.len(), bound.windows.len());
    assert_eq!(bound.window_columns.len(), bound.windows.len());
    assert_eq!(
        bound.coord.binding.source_slots.len(),
        coord.binding.source_slots.len()
    );
    assert_eq!(bound.coord.program, coord.program, "the program never changes");
    assert_eq!(bound.coord.order, coord.order, "the order never changes");

    for (index, window) in bound.windows.iter().enumerate() {
        assert!(window.publish.is_none(), "window {index} carries a publish at R0");
        assert_eq!((window.backing_depth, window.target_depth), (0, 0));
        assert!(!window.materialize);
        match window.read {
            Some(_) => assert!(
                bound.window_read_elements[index] as usize >= rows,
                "window {index} is backed by {} elements for {rows} rows",
                bound.window_read_elements[index]
            ),
            None => assert_eq!(bound.window_read_elements[index], 0),
        }
    }

    // The end-to-end property, per source.
    let mut real = 0usize;
    let mut procedural = 0usize;
    for (source, old_slot) in coord.binding.source_slots.iter().enumerate() {
        let old_window = &coord.binding.windows[old_slot.window as usize];
        let absolute = old_window.first_column + old_slot.column as usize;
        let new_slot = &bound.coord.binding.source_slots[source];
        let window = &bound.windows[new_slot.window as usize];
        match family_read_place(old_window.family, absolute) {
            None => {
                procedural += 1;
                assert!(window.read.is_none(), "source {source} lost its procedural window");
            }
            Some(place) => {
                real += 1;
                let expect = resolve_storage_column(storage, read_place_to_gkr_address(&place))
                    .expect("the binder resolved this address already");
                let base = window.read.expect("an addressed source binds a read");
                assert_eq!(
                    base.ptr as usize + new_slot.column as usize * base.stride_bytes as usize,
                    expect.ptr as usize,
                    "source {source} ({place:?}): window arithmetic lands on the wrong poly"
                );
                assert_eq!(base.stride_bytes, expect.stride_bytes, "source {source}");
                assert_eq!(base.is_e4, expect.is_e4, "source {source}");
            }
        }
    }
    eprintln!(
        "[bwd-vm-bind] add_sub L0 R0: {} -> {} windows; {real} real + {procedural} procedural \
         sources land where their addresses resolve",
        coord.binding.windows.len(),
        bound.windows.len()
    );
}

/// The Ext binder's storage contract, pinned pointer-for-pointer: for every
/// (address, continuation round) the flat prepare planned at layer 0, the
/// cascade resolver lands on EXACTLY the prepared plan's pointers — the
/// written slot (`this_layer_start`, which the VM's round-r publish must
/// alias), the read slot (`previous_layer_start`, the VM's chain read), and
/// the layer size. At the last prepared step, `this_layer_start` is what the
/// final gather consumes (`final_evaluation_sources_for_last_step` is the same
/// zip) — so this is also the proof that the VM's final-round publish feeds
/// the gather with no re-pointing. The lean-window sweep at the end proves the
/// SAME lookup serves every window the binder will bind, procedurals included.
#[test]
#[serial]
fn every_prepared_fold_pointer_is_the_cascade_slot() {
    use gkr_eval_isa::bwd::coeff::stats::WindowFamily;

    use super::seg_lower::D2Policy;
    use crate::primitives::field::E4;
    use crate::upstream::{Field, GKRAddress};

    let fixture = crate::prover::tests::prepare_basic_unrolled_async_backward_fixture(8);
    let context = &fixture.context;
    let coord = compile_coordinate(&fixture.compiled_circuit, 0, BwdRegime::Ext).unwrap();

    // Drain the dimension-reducing layers (prepare only — the maps this test
    // reads are geometry; no layer is executed), then hand off and prepare
    // main layers down to layer 0. This is the same ordering production
    // guarantees the binder: every flat prepare has run when the VM builds.
    let mut backward_state = fixture.gpu_backward_state;
    while backward_state
        .prepare_next_layer_static(context)
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
            .prepare_next_layer_static(context)
            .unwrap()
            .expect("the main-layer walk must reach layer 0");
        if plan.layer_idx == 0 {
            break plan;
        }
    };
    let storage = main_state.storage();
    let request_layer = 0usize;
    let folding_steps = plan.folding_steps;

    let (mut checked_ext, mut checked_base) = (0usize, 0usize);
    for (kernel, kp) in plan.kernel_plans.iter().enumerate() {
        let steps: Vec<usize> = kp
            .round3_and_beyond_prepared
            .iter()
            .map(|prepared| prepared.step)
            .collect();
        assert_eq!(
            steps,
            (3..folding_steps).collect::<Vec<_>>(),
            "kernel {kernel}: every continuation step is prepared exactly once"
        );

        // Ext-origin: slot 1 at round 1, then the continuation walk.
        for (index, addr) in kp.inputs.inputs_in_extension.iter().enumerate() {
            if *addr == GKRAddress::placeholder() {
                continue;
            }
            let region = resolve_cascade_region(storage, request_layer, *addr, true)
                .unwrap_or_else(|| panic!("no cascade region for ext input {addr:?}"));
            assert_eq!(region.first_slot, 1, "{addr:?}");
            let round1 = &kp.round1_prepared.extension_field_inputs[index];
            assert_eq!(
                round1.this_layer_start as usize,
                region.slot_ptr(1) as usize,
                "{addr:?} round 1"
            );
            assert_eq!(round1.this_layer_size, region.slot_elems(1), "{addr:?} round 1");
            let round2 = &kp.round2_prepared.extension_field_inputs[index];
            assert_eq!(
                round2.this_layer_start as usize,
                region.slot_ptr(2) as usize,
                "{addr:?} round 2"
            );
            assert_eq!(
                round2.previous_layer_start as usize,
                region.slot_ptr(1) as usize,
                "{addr:?} round 2 reads slot 1"
            );
            assert_eq!(round2.this_layer_size, region.slot_elems(2), "{addr:?} round 2");
            for prepared in kp.round3_and_beyond_prepared.iter() {
                let step = prepared.step as u8;
                let source = &prepared.prepared.extension_field_inputs[index];
                assert_eq!(
                    source.this_layer_start as usize,
                    region.slot_ptr(step) as usize,
                    "{addr:?} round {step}"
                );
                assert_eq!(
                    source.previous_layer_start as usize,
                    region.slot_ptr(step - 1) as usize,
                    "{addr:?} round {step} reads slot {}",
                    step - 1
                );
                assert_eq!(
                    source.this_layer_size,
                    region.slot_elems(step),
                    "{addr:?} round {step}"
                );
            }
            checked_ext += 1;
        }

        // Base-origin (virtuals included): rounds 3+ walk the cascade; the
        // round-3 `previous_layer_start` is slot 2 at the region head, which
        // the Inline-policy VM never writes — its first write is slot 3.
        for (index, addr) in kp.inputs.inputs_in_base.iter().enumerate() {
            if *addr == GKRAddress::placeholder() {
                continue;
            }
            let region = resolve_cascade_region(storage, request_layer, *addr, false)
                .unwrap_or_else(|| panic!("no cascade region for base input {addr:?}"));
            assert_eq!(region.first_slot, 2, "{addr:?}");
            for prepared in kp.round3_and_beyond_prepared.iter() {
                let step = prepared.step as u8;
                let source = &prepared.prepared.base_field_inputs[index];
                assert_eq!(
                    source.this_layer_start as usize,
                    region.slot_ptr(step) as usize,
                    "{addr:?} round {step}"
                );
                assert_eq!(
                    source.previous_layer_start as usize,
                    region.slot_ptr(step - 1) as usize,
                    "{addr:?} round {step} reads slot {}",
                    step - 1
                );
                assert_eq!(
                    source.this_layer_size,
                    region.slot_elems(step),
                    "{addr:?} round {step}"
                );
            }
            checked_base += 1;
        }
    }
    assert!(
        checked_ext > 0 && checked_base > 0,
        "the identity must be pinned on both region shapes \
         (ext {checked_ext}, base {checked_base})"
    );

    // Every lean window resolves through the SAME lookup the binder will use —
    // round 3 is where all three origins publish, so coverage there is total.
    let shapes = ext_round_window_shapes(&coord, 3, D2Policy::Inline).unwrap();
    for ((index, window), shape) in coord.binding.windows.iter().enumerate().zip(&shapes) {
        assert!(shape.materialize, "window {index} must publish at round 3");
        let addr = match (shape.address, window.family) {
            (Some(addr), _) => addr,
            (None, WindowFamily::VirtualSetup { kind }) => virtual_setup_address(kind),
            (None, family) => panic!("addressless non-procedural window {family:?}"),
        };
        let region = resolve_cascade_region(storage, request_layer, addr, shape.is_e4_backing)
            .unwrap_or_else(|| panic!("lean window {index} ({addr:?}) has no cascade region"));
        assert_eq!(
            region.first_slot,
            if shape.is_e4_backing { 1 } else { 2 },
            "window {index} ({addr:?})"
        );
    }
    eprintln!(
        "[bwd-vm-cascade] add_sub L0: {checked_ext} ext + {checked_base} base fold pointers \
         match the cascade resolver across rounds 1..{}; all {} lean windows resolve",
        folding_steps - 1,
        coord.binding.windows.len()
    );
}

