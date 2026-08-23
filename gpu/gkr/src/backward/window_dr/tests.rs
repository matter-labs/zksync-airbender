use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::field::E4;
use gpu_gkr_compiler::{lower_dr_window_program, project_dr_window_inputs, DrWindowInputOutput};

use super::binding::{DrCompactSourceTableBuilder, DrWindowBindError};
use super::composition::{build_raw_input_owner, DrWindowRawInputKeepalive};
use crate::backward::kernels::{pack_cache_u16, pack_source_u16, FoldingArenaBinding};
use crate::backward::{
    derive_dimension_reducing_inputs, legacy_dimension_reducing_slots_for_test,
    GpuGKRDimensionReducingLayerSlots, CONTINUATION_GOLDEN_CORPUS,
};
use crate::gkr_address_audit::AddressClass;
use crate::storage_layout::{
    address_storage_layer, FieldType, GpuGKRLayerLayout, GpuGKRStorageLayout,
};
use crate::upstream::{GKRAddress, OutputType};
use crate::{DrWindowLayerProgram, DrWindowProgramBundle, GpuGKRStorage};

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

fn test_storage_layout(
    entries: impl IntoIterator<Item = (GKRAddress, AddressClass, FieldType, u32)>,
    log2_stride: u32,
) -> GpuGKRStorageLayout {
    let mut layers = vec![GpuGKRLayerLayout::default(); 8];
    for (address, class, field, poly_index) in entries {
        layers[7].index.insert(address, (class, field, poly_index));
    }
    layers[7].log2_stride = log2_stride;
    GpuGKRStorageLayout {
        trace_len: 1 << log2_stride,
        artifact_log2_stride: log2_stride,
        layers,
        aliases: BTreeMap::new(),
        scratch_space_mapping_rev: BTreeMap::new(),
    }
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
fn cpu_dr_compact_source_table_emits_first_use_slots_and_arena_records() {
    let first = FoldingArenaBinding::new(0x1000usize as *const u8, 6);
    let second = FoldingArenaBinding::new(0x2000usize as *const u8, 4);
    let mut builder = DrCompactSourceTableBuilder::new();

    assert_eq!(
        builder.intern_arena_e4(first, 17).unwrap(),
        pack_cache_u16(0, 17)
    );
    assert_eq!(
        builder.intern_arena_e4(first, 17).unwrap(),
        pack_source_u16(false, 0, 17)
    );
    assert_eq!(
        builder.intern_arena_e4(first, 17).unwrap() | (1u16 << 15),
        pack_source_u16(true, 0, 17)
    );
    assert_eq!(
        builder.intern_arena_e4(first, 3).unwrap(),
        pack_cache_u16(0, 3)
    );
    assert_eq!(
        builder.intern_arena_e4(second, 9).unwrap(),
        pack_cache_u16(1, 9)
    );

    let tables = builder.finish();
    assert_eq!(tables.bases[0], first.base);
    assert_eq!(tables.log2_stride[0], first.log2_stride);
    assert_eq!(tables.bases[1], second.base);
    assert_eq!(tables.log2_stride[1], second.log2_stride);
    assert!(tables.bases[2..].iter().all(|base| base.is_null()));
    assert!(tables.log2_stride[2..].iter().all(|stride| *stride == 0));
}

#[test]
fn cpu_dr_compact_source_table_rejects_every_typed_binding_failure() {
    let source = address(0);
    let mut builder = DrCompactSourceTableBuilder::new();
    let storage = GpuGKRStorage::<(), E4>::default();
    assert_eq!(
        builder.intern_storage_e4(&storage, source),
        Err(DrWindowBindError::MissingStorageLayout { address: source }),
    );

    let mut storage = GpuGKRStorage::<(), E4>::default();
    storage.set_layout(Arc::new(test_storage_layout([], 4)));
    assert_eq!(
        builder.intern_storage_e4(&storage, source),
        Err(DrWindowBindError::MissingSource {
            address: source,
            logical_layer: 7,
        }),
    );

    let mut storage = GpuGKRStorage::<(), E4>::default();
    storage.set_layout(Arc::new(test_storage_layout(
        [(
            source,
            AddressClass::ThisLayerInnerLayerWrite,
            FieldType::Base,
            0,
        )],
        4,
    )));
    assert_eq!(
        builder.intern_storage_e4(&storage, source),
        Err(DrWindowBindError::NonE4Source {
            address: source,
            field: FieldType::Base,
        }),
    );

    let class = AddressClass::ThisLayerCachedWrite;
    let mut storage = GpuGKRStorage::<(), E4>::default();
    storage.set_layout(Arc::new(test_storage_layout(
        [(source, class, FieldType::Ext, 0)],
        4,
    )));
    assert_eq!(
        builder.intern_storage_e4(&storage, source),
        Err(DrWindowBindError::MissingE4Backing {
            address: source,
            canonical_layer: 7,
            class,
        }),
    );

    let first = FoldingArenaBinding::new(0x3000usize as *const u8, 5);
    let conflicting = FoldingArenaBinding::new(first.base, 6);
    let mut builder = DrCompactSourceTableBuilder::new();
    builder.intern_arena_e4(first, 0).unwrap();
    assert_eq!(
        builder.intern_arena_e4(conflicting, 0),
        Err(DrWindowBindError::StrideMismatch {
            backing: first.base as usize,
            expected_log2_stride: 5,
            observed_log2_stride: 6,
        }),
    );

    let mut builder = DrCompactSourceTableBuilder::new();
    assert_eq!(
        builder.intern_arena_e4(first, 1 << 11),
        Err(DrWindowBindError::PolyIndexOverflow {
            poly_index: 1 << 11,
            capacity: 1 << 11,
        }),
    );

    let mut builder = DrCompactSourceTableBuilder::new();
    for slot in 0..16usize {
        let arena = FoldingArenaBinding::new((0x10_000 + slot * 0x1000) as *const u8, 4);
        assert_eq!(
            builder.intern_arena_e4(arena, slot).unwrap(),
            pack_cache_u16(slot as u8, slot as u16),
        );
    }
    let overflow = FoldingArenaBinding::new(0x20_000usize as *const u8, 4);
    assert_eq!(
        builder.intern_arena_e4(overflow, 0),
        Err(DrWindowBindError::BaseSlotOverflow {
            required: 17,
            capacity: 16,
        }),
    );
}

#[test]
fn cpu_dr_raw_input_keepalive_helper_deduplicates_inputs_and_excludes_outputs() {
    let program = lower_dr_window_program(&BTreeMap::from([(
        OutputType::PermutationProduct,
        DrWindowInputOutput::new([address(2), address(0)], [address(1), address(3)]),
    )]))
    .unwrap();
    let projection = project_dr_window_inputs(&program, &BTreeMap::new());
    assert_eq!(projection.canonical_sources(), &[address(0), address(2)]);

    let shared_input = Arc::new(vec![1u8, 2, 3]);
    let output_only = Arc::new(vec![9u8]);
    let shared_input_weak = Arc::downgrade(&shared_input);
    let output_only_weak = Arc::downgrade(&output_only);
    let shared_input_ptr = Arc::as_ptr(&shared_input);
    let output_only_ptr = Arc::as_ptr(&output_only);
    let mut storage_layers = vec![BTreeMap::new(); 8];
    storage_layers[7] = BTreeMap::from([
        (address(0), Arc::clone(&shared_input)),
        (address(1), Arc::clone(&output_only)),
        (address(2), Arc::clone(&shared_input)),
        (address(3), Arc::clone(&output_only)),
    ]);
    let mut requested = Vec::new();
    let owner = build_raw_input_owner(&projection, |source| {
        requested.push(source);
        Ok::<_, ()>(Arc::clone(&storage_layers[7][&source]))
    })
    .unwrap();
    assert_eq!(owner.canonical_sources, projection.canonical_sources());
    assert_eq!(requested, projection.canonical_sources());
    assert_eq!(owner.backings.len(), 1);
    assert_eq!(Arc::as_ptr(&owner.backings[0]), shared_input_ptr);
    assert!(owner
        .backings
        .iter()
        .all(|backing| Arc::as_ptr(backing) != output_only_ptr));

    storage_layers.truncate(1);
    assert_eq!(storage_layers.len(), 1);
    drop(shared_input);
    drop(output_only);

    assert_eq!(
        Arc::as_ptr(&shared_input_weak.upgrade().unwrap()),
        shared_input_ptr
    );
    assert!(output_only_weak.upgrade().is_none());
    assert_eq!(Arc::as_ptr(&owner.backings[0]), shared_input_ptr);
}

#[test]
#[ignore = "requires CUDA allocation; run through .agents/bin/with_gpu_lock.sh"]
fn gpu_dr_raw_input_keepalive_owns_actual_storage_backings_across_purge() {
    let input = address(0);
    let output_a = address(1);
    let input_alias = address(2);
    let output_b = address(3);
    let program = lower_dr_window_program(&BTreeMap::from([(
        OutputType::PermutationProduct,
        DrWindowInputOutput::new([input_alias, input], [output_a, output_b]),
    )]))
    .unwrap();
    let aliases = BTreeMap::from([(input_alias, input)]);
    let projection = project_dr_window_inputs(&program, &aliases);
    assert_eq!(projection.canonical_sources(), &[input]);
    assert_eq!(projection.occurrences().len(), 2);
    assert!(projection
        .occurrences()
        .iter()
        .all(|occurrence| occurrence.publication_index() == 0));
    assert!(!projection.canonical_sources().contains(&output_a));
    assert!(!projection.canonical_sources().contains(&output_b));

    let input_class = AddressClass::ThisLayerInnerLayerWrite;
    let output_class = AddressClass::ThisLayerCachedWrite;
    let mut layout = test_storage_layout(
        [
            (input, input_class, FieldType::Ext, 0),
            (output_a, output_class, FieldType::Ext, 0),
            (output_b, output_class, FieldType::Ext, 1),
        ],
        4,
    );
    layout.aliases = aliases;

    let context = crate::test_utils::make_test_context(64, 16);
    let input_backing = Arc::new(context.alloc::<E4>(16, AllocationPlacement::Top).unwrap());
    let output_backing = Arc::new(context.alloc::<E4>(32, AllocationPlacement::Top).unwrap());
    let input_pointer = input_backing.as_ptr();
    let output_pointer = output_backing.as_ptr();
    let input_weak = Arc::downgrade(&input_backing);
    let output_weak = Arc::downgrade(&output_backing);

    let mut storage = GpuGKRStorage::<(), E4>::default();
    storage.set_layout(Arc::new(layout));
    storage.layers.resize_with(8, Default::default);
    storage.layers[7]
        .ext_class_backings
        .insert(input_class, Arc::clone(&input_backing));
    storage.layers[7]
        .ext_class_backings
        .insert(output_class, Arc::clone(&output_backing));

    let owner = DrWindowRawInputKeepalive::from_projection(&storage, &projection).unwrap();
    assert_eq!(owner.canonical_sources, vec![input]);
    assert_eq!(owner.backings.len(), 1);
    assert_eq!(owner.backings[0].as_ptr(), input_pointer);
    assert_ne!(owner.backings[0].as_ptr(), output_pointer);

    storage.purge_up_to_layer(0);
    assert_eq!(storage.layers.len(), 1);
    drop(input_backing);
    drop(output_backing);

    assert_eq!(input_weak.upgrade().unwrap().as_ptr(), input_pointer);
    assert!(output_weak.upgrade().is_none());
    assert_eq!(owner.backings[0].as_ptr(), input_pointer);
    drop(owner);
    assert!(input_weak.upgrade().is_none());
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
