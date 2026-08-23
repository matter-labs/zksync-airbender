use std::collections::{BTreeMap, BTreeSet};

use gpu_gkr_compiler::{lower_dr_window_program, project_dr_window_inputs, DrWindowInputOutput};

use crate::backward::{
    derive_dimension_reducing_inputs, legacy_dimension_reducing_slots_for_test,
    GpuGKRDimensionReducingLayerSlots, CONTINUATION_GOLDEN_CORPUS,
};
use crate::gkr_address_audit::AddressClass;
use crate::storage_layout::{address_storage_layer, FieldType, GpuGKRStorageLayout};
use crate::upstream::{GKRAddress, OutputType};
use crate::{DrWindowLayerProgram, DrWindowProgramBundle};

const CORPUS_FINAL_TRACE_LOG: u32 = 4;

type BackingObservation = (usize, AddressClass, u32);
type ResolvedLaneObservation = (usize, usize, BackingObservation, u32);

#[derive(Clone, Debug, PartialEq, Eq)]
struct PortMutationObservation {
    slots: Vec<usize>,
    endpoints: [u32; 5],
    lanes: Vec<(usize, usize, u16)>,
    batch_exponents: Vec<[u16; 2]>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PortObservationMismatch {
    Slot,
    Endpoint,
    Lane,
    BatchExponent,
}

fn compare_port_observations(
    expected: &PortMutationObservation,
    observed: &PortMutationObservation,
) -> Result<(), PortObservationMismatch> {
    if observed.slots != expected.slots {
        return Err(PortObservationMismatch::Slot);
    }
    if observed.endpoints != expected.endpoints {
        return Err(PortObservationMismatch::Endpoint);
    }
    if observed.lanes != expected.lanes {
        return Err(PortObservationMismatch::Lane);
    }
    if observed.batch_exponents != expected.batch_exponents {
        return Err(PortObservationMismatch::BatchExponent);
    }
    Ok(())
}

struct LayerCensus {
    mask: u32,
    operand_backings: usize,
    input_backings: usize,
    canonical_inputs: usize,
    alias_occurrences: usize,
    folding_steps: usize,
    epilogue_publication_order_mismatch: bool,
    canonical_input_merge: bool,
}

fn address(offset: usize) -> GKRAddress {
    GKRAddress::InnerLayer { layer: 7, offset }
}

fn resolve_ext_lane(
    layout: &GpuGKRStorageLayout,
    address: GKRAddress,
) -> (BackingObservation, u32) {
    let logical_layer = address_storage_layer(address);
    let (canonical_layer, class, field, poly_idx) = layout
        .lookup(logical_layer, &address)
        .unwrap_or_else(|| panic!("missing storage layout entry for {address:?}"));
    assert_eq!(field, FieldType::Ext, "{address:?} must resolve as E4");
    (
        (
            canonical_layer,
            class,
            layout.layers[canonical_layer].log2_stride,
        ),
        poly_idx,
    )
}

fn assert_program_matches_legacy_slots(
    label: &str,
    layout: &GpuGKRStorageLayout,
    legacy: &GpuGKRDimensionReducingLayerSlots,
    layer: &DrWindowLayerProgram,
) -> (PortMutationObservation, LayerCensus) {
    let program = layer.program();
    assert_eq!(
        program.enabled_mask(),
        legacy.enabled_mask(),
        "{label}: mask"
    );

    let legacy_enabled = legacy.iter_enabled().collect::<Vec<_>>();
    assert_eq!(
        program
            .slots()
            .iter()
            .map(|slot| slot.slot())
            .collect::<Vec<_>>(),
        legacy_enabled
            .iter()
            .map(|(slot, _)| *slot)
            .collect::<Vec<_>>(),
        "{label}: enabled slot order",
    );

    let mut expected_endpoints = [0u32; 5];
    let mut endpoint = 0u32;
    for (slot, expected_endpoint) in expected_endpoints.iter_mut().enumerate() {
        endpoint += u32::from(legacy.slots[slot].is_some());
        *expected_endpoint = endpoint;
    }
    assert_eq!(
        program.section_endpoints(),
        &expected_endpoints,
        "{label}: section endpoints",
    );

    let mut expected_sources = Vec::new();
    let mut expected_source_ids = BTreeMap::new();
    let mut expected_lanes = Vec::new();
    let mut expected_resolved_lanes = Vec::new();
    let mut expected_input_backings = BTreeSet::new();
    let mut expected_raw_inputs = Vec::new();

    for (dense_slot, (slot_index, legacy_slot)) in legacy_enabled.iter().enumerate() {
        let lowered_slot = &program.slots()[dense_slot];
        assert_eq!(lowered_slot.slot(), *slot_index, "{label}: slot index");
        assert_eq!(
            lowered_slot.batch_exponents(),
            &legacy_slot.batch_exp,
            "{label}: dense batch exponents for slot {slot_index}",
        );

        let legacy_addresses = legacy_slot
            .inputs
            .iter()
            .chain(legacy_slot.outputs.iter())
            .copied()
            .collect::<Vec<_>>();
        let lowered_addresses = lowered_slot
            .source_ids()
            .iter()
            .map(|source_id| program.sources()[usize::from(*source_id)])
            .collect::<Vec<_>>();
        assert_eq!(
            lowered_addresses, legacy_addresses,
            "{label}: input/output addresses for slot {slot_index}",
        );

        for (operand, address) in legacy_addresses.into_iter().enumerate() {
            let source_id = if let Some(source_id) = expected_source_ids.get(&address) {
                *source_id
            } else {
                let source_id = u16::try_from(expected_sources.len()).unwrap();
                expected_sources.push(address);
                expected_source_ids.insert(address, source_id);
                source_id
            };
            expected_lanes.push((dense_slot, operand, source_id));
            let (backing, column) = resolve_ext_lane(layout, address);
            expected_resolved_lanes.push((dense_slot, operand, backing, column));
            if operand < 2 {
                expected_input_backings.insert(backing);
                expected_raw_inputs.push((dense_slot, operand, address));
            }
        }
    }

    assert_eq!(
        program.sources(),
        expected_sources,
        "{label}: semantic source identities",
    );
    let observed_lanes = program
        .source_lanes()
        .iter()
        .map(|lane| (lane.dense_slot(), lane.operand(), lane.source_id()))
        .collect::<Vec<_>>();
    assert_eq!(observed_lanes, expected_lanes, "{label}: source lanes");

    let observed_resolved_lanes = program
        .source_lanes()
        .iter()
        .map(|lane| {
            let address = program.sources()[usize::from(lane.source_id())];
            let (backing, column) = resolve_ext_lane(layout, address);
            (lane.dense_slot(), lane.operand(), backing, column)
        })
        .collect::<Vec<ResolvedLaneObservation>>();
    assert_eq!(
        observed_resolved_lanes, expected_resolved_lanes,
        "{label}: resolved E4 backing/column lanes",
    );

    assert_eq!(
        program.slot_count(),
        legacy_enabled.len(),
        "{label}: enabled slot count",
    );
    assert_eq!(
        program.source_count(),
        expected_sources.len(),
        "{label}: semantic source count",
    );
    assert_eq!(
        program.source_lane_count(),
        expected_lanes.len(),
        "{label}: source lane count",
    );

    let expected_canonical_inputs = expected_raw_inputs
        .iter()
        .map(|(_, _, address)| layout.aliases.get(address).copied().unwrap_or(*address))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let expected_publication_indices = expected_canonical_inputs
        .iter()
        .copied()
        .enumerate()
        .map(|(index, address)| (address, u16::try_from(index).unwrap()))
        .collect::<BTreeMap<_, _>>();
    let expected_occurrences = expected_raw_inputs
        .iter()
        .map(|(dense_slot, input_operand, address)| {
            let canonical = layout.aliases.get(address).copied().unwrap_or(*address);
            (
                *dense_slot,
                *input_operand,
                expected_publication_indices[&canonical],
            )
        })
        .collect::<Vec<_>>();
    let projection = layer.input_projection();
    assert_eq!(
        projection.canonical_sources(),
        expected_canonical_inputs,
        "{label}: canonical input-only publication identities",
    );
    assert_eq!(
        projection
            .occurrences()
            .iter()
            .map(|occurrence| (
                occurrence.dense_slot(),
                occurrence.input_operand(),
                occurrence.publication_index(),
            ))
            .collect::<Vec<_>>(),
        expected_occurrences,
        "{label}: input occurrence publication mapping",
    );

    let observed_input_backings = projection
        .occurrences()
        .iter()
        .map(|occurrence| {
            let address =
                projection.canonical_sources()[usize::from(occurrence.publication_index())];
            resolve_ext_lane(layout, address).0
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        observed_input_backings, expected_input_backings,
        "{label}: input-only resolved backings",
    );

    let expected_mutation_observation = PortMutationObservation {
        slots: legacy_enabled.iter().map(|(slot, _)| *slot).collect(),
        endpoints: expected_endpoints,
        lanes: expected_lanes,
        batch_exponents: legacy_enabled
            .iter()
            .map(|(_, slot)| slot.batch_exp)
            .collect(),
    };
    let observed_mutation_observation = PortMutationObservation {
        slots: program.slots().iter().map(|slot| slot.slot()).collect(),
        endpoints: *program.section_endpoints(),
        lanes: observed_lanes,
        batch_exponents: program
            .slots()
            .iter()
            .map(|slot| *slot.batch_exponents())
            .collect(),
    };
    assert_eq!(
        compare_port_observations(
            &expected_mutation_observation,
            &observed_mutation_observation,
        ),
        Ok(()),
        "{label}: mutation-sensitive port observation",
    );

    let raw_inputs_sorted = expected_raw_inputs
        .iter()
        .map(|(_, _, address)| *address)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let canonical_in_raw_epilogue_order = raw_inputs_sorted
        .iter()
        .map(|address| layout.aliases.get(address).copied().unwrap_or(*address))
        .collect::<Vec<_>>();
    let operand_backings = expected_resolved_lanes
        .iter()
        .map(|(_, _, backing, _)| *backing)
        .collect::<BTreeSet<_>>()
        .len();
    let alias_occurrences = expected_raw_inputs
        .iter()
        .filter(|(_, _, address)| {
            layout
                .aliases
                .get(address)
                .is_some_and(|alias| alias != address)
        })
        .count();
    let census = LayerCensus {
        mask: legacy.enabled_mask(),
        operand_backings,
        input_backings: expected_input_backings.len(),
        canonical_inputs: expected_canonical_inputs.len(),
        alias_occurrences,
        folding_steps: layer.folding_steps(),
        epilogue_publication_order_mismatch: canonical_in_raw_epilogue_order
            != expected_canonical_inputs,
        canonical_input_merge: raw_inputs_sorted.len() != expected_canonical_inputs.len(),
    };

    (observed_mutation_observation, census)
}

fn assert_port_mutations_are_detected(expected: &PortMutationObservation) {
    let mut slot_mutation = expected.clone();
    slot_mutation.slots[0] += 1;
    assert_eq!(
        compare_port_observations(expected, &slot_mutation),
        Err(PortObservationMismatch::Slot),
    );

    let mut endpoint_mutation = expected.clone();
    endpoint_mutation.endpoints[0] ^= 1;
    assert_eq!(
        compare_port_observations(expected, &endpoint_mutation),
        Err(PortObservationMismatch::Endpoint),
    );

    let mut lane_mutation = expected.clone();
    lane_mutation.lanes[0].1 ^= 1;
    assert_eq!(
        compare_port_observations(expected, &lane_mutation),
        Err(PortObservationMismatch::Lane),
    );

    let mut exponent_mutation = expected.clone();
    exponent_mutation.batch_exponents[0][0] += 1;
    assert_eq!(
        compare_port_observations(expected, &exponent_mutation),
        Err(PortObservationMismatch::BatchExponent),
    );
}

#[test]
fn cpu_dr_window_program_bundle_accessors_use_absolute_layer_keys() {
    let program = lower_dr_window_program(&BTreeMap::from([(
        OutputType::PermutationProduct,
        DrWindowInputOutput::new([address(2), address(0)], [address(3), address(4)]),
    )]))
    .unwrap();
    let projection = project_dr_window_inputs(&program, &BTreeMap::new());
    let absolute_layer = 19;
    let layer = DrWindowLayerProgram::new(absolute_layer, 11, program, projection);
    let bundle = DrWindowProgramBundle::new(6, BTreeMap::from([(absolute_layer, layer)]));

    assert_eq!(bundle.final_trace_log(), 6);
    assert_eq!(
        bundle.layer(absolute_layer).unwrap().layer(),
        absolute_layer
    );
    assert_eq!(bundle.layer(absolute_layer).unwrap().folding_steps(), 11);
    assert_eq!(
        bundle
            .layer(absolute_layer)
            .unwrap()
            .program()
            .enabled_mask(),
        1
    );
    assert_eq!(
        bundle
            .layer(absolute_layer)
            .unwrap()
            .input_projection()
            .canonical_sources(),
        &[address(0), address(2)]
    );
    assert!(bundle.layer(0).is_none());
}

#[test]
fn cpu_dr_window_program_success_is_cached_per_final_trace_log() {
    let (programs, main_layers) =
        crate::backward::compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    let initial_trace_log = programs.runtime_circuit().trace_len.trailing_zeros();
    let final_trace_log = initial_trace_log - 2;

    assert!(!programs.dr_window_programs_ready(final_trace_log));
    let first = programs
        .resolve_dr_window_programs(final_trace_log)
        .unwrap();
    let second = programs
        .resolve_dr_window_programs(final_trace_log)
        .unwrap();
    assert!(std::sync::Arc::ptr_eq(&first, &second));
    assert_eq!(first.final_trace_log(), final_trace_log);
    assert!(programs.dr_window_programs_ready(final_trace_log));

    let first_layer = first.layer(main_layers).unwrap();
    assert_eq!(first_layer.layer(), main_layers);
    assert_eq!(first_layer.folding_steps(), initial_trace_log as usize - 1);
    assert_eq!(
        first_layer.input_projection().occurrences().len(),
        first_layer.program().slot_count() * 2
    );
    let second_layer = first.layer(main_layers + 1).unwrap();
    assert_eq!(second_layer.layer(), main_layers + 1);
    assert_eq!(second_layer.folding_steps(), final_trace_log as usize);
    assert!(first.layer(main_layers - 1).is_none());
    assert!(first.layer(main_layers + 2).is_none());

    let other_final_trace_log = initial_trace_log - 1;
    assert!(!programs.dr_window_programs_ready(other_final_trace_log));
    let other_key = programs
        .resolve_dr_window_programs(other_final_trace_log)
        .unwrap();
    assert!(!std::sync::Arc::ptr_eq(&other_key, &first));
    assert_eq!(other_key.final_trace_log(), other_final_trace_log);
    assert!(programs.dr_window_programs_ready(other_final_trace_log));

    let invalid_final_trace_log = initial_trace_log + 1;
    let first_rejection = programs
        .resolve_dr_window_programs(invalid_final_trace_log)
        .unwrap_err();
    let second_rejection = programs
        .resolve_dr_window_programs(invalid_final_trace_log)
        .unwrap_err();
    assert_eq!(first_rejection, second_rejection);
    assert_eq!(first_rejection.circuit(), "add_sub_lui_auipc_mop");
    assert!(!programs.dr_window_programs_ready(invalid_final_trace_log));
}

#[test]
fn cpu_dr_window_program_concurrent_success_returns_one_canonical_arc() {
    let (programs, _) =
        crate::backward::compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    let programs = std::sync::Arc::new(programs);
    let final_trace_log = programs.runtime_circuit().trace_len.trailing_zeros() - 2;
    let worker_count = 8;
    let start = std::sync::Arc::new(std::sync::Barrier::new(worker_count));
    let handles = (0..worker_count)
        .map(|_| {
            let programs = programs.clone();
            let start = start.clone();
            std::thread::spawn(move || {
                start.wait();
                programs
                    .resolve_dr_window_programs(final_trace_log)
                    .unwrap()
            })
        })
        .collect::<Vec<_>>();
    let bundles = handles
        .into_iter()
        .map(|handle| handle.join().unwrap())
        .collect::<Vec<_>>();

    for bundle in &bundles[1..] {
        assert!(std::sync::Arc::ptr_eq(&bundles[0], bundle));
    }
    assert!(programs.dr_window_programs_ready(final_trace_log));
}

#[test]
fn cpu_dr_window_legacy_port_corpus() {
    assert_eq!(CONTINUATION_GOLDEN_CORPUS.len(), 12);
    let mut checked_layers = 0usize;
    let mut mask_counts = BTreeMap::new();
    let mut operand_backing_counts = BTreeMap::new();
    let mut input_backing_counts = BTreeMap::new();
    let mut canonical_input_counts = BTreeMap::new();
    let mut alias_occurrences = 0usize;
    let mut folding_steps = BTreeSet::new();
    let mut epilogue_publication_order_mismatches = 0usize;
    let mut canonical_input_merge_layers = 0usize;
    let mut mutation_observation = None;

    for (layout_name, _) in CONTINUATION_GOLDEN_CORPUS {
        let (programs, main_layers) = crate::backward::compile_corpus_layout(layout_name);
        let runtime = programs.runtime_circuit();
        assert_eq!(main_layers, runtime.layers.len(), "{layout_name}");
        let initial_trace_log = runtime.trace_len.trailing_zeros();
        let initial_trace_log_usize = usize::try_from(initial_trace_log)
            .unwrap_or_else(|_| panic!("{layout_name}: initial trace log does not fit usize"));
        let legacy_layers = derive_dimension_reducing_inputs(
            main_layers,
            &runtime.global_output_map,
            initial_trace_log,
            CORPUS_FINAL_TRACE_LOG,
        );
        let layout =
            GpuGKRStorageLayout::from_artifact_with_tower(runtime, CORPUS_FINAL_TRACE_LOG as usize);
        let bundle = programs
            .resolve_dr_window_programs(CORPUS_FINAL_TRACE_LOG)
            .unwrap_or_else(|error| panic!("{layout_name}: {error}"));

        assert_eq!(bundle.final_trace_log(), CORPUS_FINAL_TRACE_LOG);
        for (absolute_layer, legacy_description) in &legacy_layers {
            let label = format!("{layout_name} layer {absolute_layer}");
            let legacy_slots = legacy_dimension_reducing_slots_for_test(legacy_description);
            let lowered_layer = bundle
                .layer(*absolute_layer)
                .unwrap_or_else(|| panic!("{label}: bundle layer missing"));
            let layer_offset = absolute_layer.checked_sub(main_layers).unwrap_or_else(|| {
                panic!("{label}: absolute DR layer precedes main-layer count {main_layers}",)
            });
            let expected_folding_steps = initial_trace_log_usize
                .checked_sub(1)
                .and_then(|steps| steps.checked_sub(layer_offset))
                .unwrap_or_else(|| {
                    panic!(
                        "{label}: cannot derive folding steps from initial trace log {initial_trace_log_usize} and DR offset {layer_offset}",
                    )
                });
            assert_eq!(
                lowered_layer.folding_steps(),
                expected_folding_steps,
                "{label}: folding steps",
            );
            let (observation, census) =
                assert_program_matches_legacy_slots(&label, &layout, &legacy_slots, lowered_layer);
            mutation_observation.get_or_insert(observation);
            *mask_counts.entry(census.mask).or_insert(0usize) += 1;
            *operand_backing_counts
                .entry(census.operand_backings)
                .or_insert(0usize) += 1;
            *input_backing_counts
                .entry(census.input_backings)
                .or_insert(0usize) += 1;
            *canonical_input_counts
                .entry(census.canonical_inputs)
                .or_insert(0usize) += 1;
            alias_occurrences += census.alias_occurrences;
            folding_steps.insert(census.folding_steps);
            epilogue_publication_order_mismatches +=
                usize::from(census.epilogue_publication_order_mismatch);
            canonical_input_merge_layers += usize::from(census.canonical_input_merge);
            checked_layers += 1;
        }
        assert!(
            bundle.layer(main_layers - 1).is_none(),
            "{layout_name}: lookup must use absolute DR layers",
        );
        assert!(
            bundle.layer(main_layers + legacy_layers.len()).is_none(),
            "{layout_name}: bundle has an unexpected trailing layer",
        );
    }

    assert_eq!(checked_layers, 229);
    assert_eq!(
        mask_counts,
        BTreeMap::from([(1, 20), (13, 52), (15, 138), (31, 19)]),
    );
    assert_eq!(
        operand_backing_counts,
        BTreeMap::from([(2, 220), (3, 6), (4, 3)]),
    );
    assert_eq!(
        input_backing_counts,
        BTreeMap::from([(1, 220), (2, 6), (3, 3)]),
    );
    assert_eq!(
        canonical_input_counts,
        BTreeMap::from([(2, 20), (6, 52), (8, 138), (10, 19)]),
    );
    assert_eq!(alias_occurrences, 42);
    assert_eq!(folding_steps, (4usize..=23).collect::<BTreeSet<_>>());
    assert_eq!(epilogue_publication_order_mismatches, 9);
    assert_eq!(canonical_input_merge_layers, 0);
    assert_port_mutations_are_detected(
        mutation_observation
            .as_ref()
            .expect("the production corpus must contain a mutation baseline"),
    );
}
