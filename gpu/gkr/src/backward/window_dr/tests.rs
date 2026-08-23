use std::collections::{BTreeMap, BTreeSet};
use std::mem::{align_of, offset_of, size_of};
use std::sync::Arc;

use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::field::E4;
use gpu_gkr_compiler::{
    lower_dr_window_program, project_dr_window_inputs, DrWindowInputOutput,
    DR_WINDOWED_R0_BLOCK_THREADS, DR_WINDOWED_R0_KERNEL_SYMBOL, KERNEL_ARGUMENT_CEILING_BYTES,
};

use super::binding::{
    dr_window_partials_len, dr_window_row_tiles, resolve_dr_window_kernel,
    validate_dr_r0_eq_contract, validate_dr_window_folding_steps, DrCompactSourceTableBuilder,
    DrWindowBindError, DrWindowLaunchBinding,
};
use super::composition::{
    build_raw_input_owner, continuation_window_count, megakernel_entry_round,
    DrWindowRawInputKeepalive,
};
use super::generated_registry::{DR_WINDOWED_R0_DEFINED_MASK, DR_WINDOWED_R0_UNIVERSAL_KERNEL};
use crate::backward::kernels::{
    make_eq_sizes, pack_cache_u16, pack_source_u16, FoldingArenaBinding,
    GpuGKRDimensionReducingBatch, GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN,
};
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

#[test]
fn cpu_dr_window_r0_abi_and_linked_symbol_contract() {
    assert_eq!(size_of::<GpuGKRDimensionReducingBatch<E4>>(), 336);
    assert_eq!(size_of::<DrWindowLaunchBinding>(), 352);
    assert_eq!(align_of::<DrWindowLaunchBinding>(), 16);
    assert_eq!(KERNEL_ARGUMENT_CEILING_BYTES, 32_764);
    assert!(size_of::<DrWindowLaunchBinding>() <= KERNEL_ARGUMENT_CEILING_BYTES);
    assert_eq!(offset_of!(DrWindowLaunchBinding, batch), 0);
    assert_eq!(offset_of!(DrWindowLaunchBinding, partials), 336);
    assert_eq!(offset_of!(DrWindowLaunchBinding, log_rows), 344);
    assert_eq!(offset_of!(DrWindowLaunchBinding, reserved), 348);

    let binding = DrWindowLaunchBinding {
        batch: GpuGKRDimensionReducingBatch::default(),
        partials: std::ptr::null_mut(),
        log_rows: 1,
        reserved: 0,
    };
    assert!(binding.batch.contributions.is_null());
    assert_eq!(DR_WINDOWED_R0_BLOCK_THREADS, 288);
    assert_eq!(DR_WINDOWED_R0_BLOCK_THREADS / 32, 9);
    assert_eq!(GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN, 10);
    assert_eq!(
        DR_WINDOWED_R0_UNIVERSAL_KERNEL.symbol_name,
        DR_WINDOWED_R0_KERNEL_SYMBOL
    );
}

#[test]
fn cpu_dr_window_r0_dispatch_is_universal_and_typed() {
    for mask in 1..=DR_WINDOWED_R0_DEFINED_MASK {
        assert_eq!(
            resolve_dr_window_kernel(mask).unwrap().symbol_name,
            DR_WINDOWED_R0_KERNEL_SYMBOL,
            "mask {mask:#04x}",
        );
    }
    assert_eq!(
        resolve_dr_window_kernel(0).err().unwrap(),
        DrWindowBindError::ZeroMask,
    );
    for bit in 5..32 {
        let undefined = 1u32 << bit;
        assert_eq!(
            resolve_dr_window_kernel(undefined).err().unwrap(),
            DrWindowBindError::UndefinedMaskBits { bits: undefined },
        );
    }
}

#[test]
fn cpu_dr_window_r0_geometry_eq_and_composition_policy_are_pass_local() {
    assert_eq!(
        validate_dr_window_folding_steps(3),
        Err(DrWindowBindError::UnsupportedFoldingSteps { folding_steps: 3 }),
    );
    assert_eq!(validate_dr_window_folding_steps(4), Ok(()));
    assert_eq!(validate_dr_window_folding_steps(24), Ok(()));
    assert_eq!(
        validate_dr_window_folding_steps(25),
        Err(DrWindowBindError::UnsupportedFoldingSteps { folding_steps: 25 }),
    );
    assert_eq!(dr_window_row_tiles(4), 1);
    assert_eq!(dr_window_partials_len(4), 54);
    assert_eq!(dr_window_row_tiles(8), 1);
    assert_eq!(dr_window_row_tiles(9), 2);
    assert_eq!(dr_window_row_tiles(24), 65_536);
    assert_eq!(dr_window_partials_len(24), 27 * (65_536 + 1));

    for folding_steps in 4..=24 {
        let sizes = make_eq_sizes(folding_steps - 3);
        assert_eq!(validate_dr_r0_eq_contract(folding_steps, 3, sizes), Ok(()),);
        assert_eq!(
            validate_dr_r0_eq_contract(folding_steps, 2, sizes),
            Err(DrWindowBindError::EqBuildOffset {
                expected: 3,
                observed: 2,
            }),
        );
        assert_eq!(
            validate_dr_r0_eq_contract(folding_steps, 3, make_eq_sizes(folding_steps - 4)),
            Err(DrWindowBindError::EqSizeMismatch),
        );
    }

    let expected = [
        (4, 0, 3),
        (7, 1, 6),
        (10, 2, 9),
        (13, 3, 12),
        (16, 4, 15),
        (24, 4, 15),
    ];
    for (folding_steps, count, entry) in expected {
        assert_eq!(continuation_window_count(folding_steps), count);
        assert_eq!(megakernel_entry_round(folding_steps), entry);
    }
}

#[test]
fn cpu_dr_window_r0_native_source_pins_tensor_and_constant_eq_contracts() {
    const R0: &str = include_str!("../../../native/gkr/backward/window_dr/r0.cuh");
    const WINDOW_GEOMETRY: &str =
        include_str!("../../../native/gkr/backward/window/window_geometry.cuh");
    const TU: &str =
        include_str!("../../../native/gkr/backward/generated/dr_r0_window_universal.cu");
    const BINDING: &str = include_str!("binding.rs");

    assert!(R0.contains("2u * y_index + gate_bit"));
    assert!(R0.contains("load<e4, ld_modifier::ca>"));
    assert!(!R0.contains("load<e4, ld_modifier::cs>(column"));
    assert!(R0.contains("bwd_window_product_tensor"));
    assert!(R0.contains("gkr_load_slot_batch_challenges"));
    assert!(R0.contains("tower < GKR_DIM_REDUCING_OUTPUTS_PER_SLOT"));
    assert!(!R0.contains("tower < GKR_DIM_REDUCING_INPUTS_PER_SLOT"));
    assert!(R0.contains("if (!selector.has_infinity())"));
    assert!(R0.contains("9 * x2 + cell_base"));
    assert_eq!(R0.matches("gkr_compute_eq_inline<e4>").count(), 1);
    assert_eq!(
        WINDOW_GEOMETRY.matches("gkr_compute_eq_inline<e4>").count(),
        1
    );
    assert!(!R0.contains("store<e4, st_modifier::cs>(inputs"));
    assert!(!R0.contains("batch.contributions"));
    assert!(!R0.contains("ab_gkr_eq_high"));
    assert!(R0.contains("gkr_compute_eq_inline_global"));
    assert_eq!(
        TU.matches("ab_gkr_dr_r0_window3_universal_kernel").count(),
        1,
    );
    assert_eq!(
        BINDING
            .matches("launch_build_eq_high_and_low_groups_from_point(")
            .count(),
        1,
    );
    assert!(!BINDING.contains("launch_build_eq_values_from_point("));

    // DR owns a different descriptor, so it cannot call bwd_window_publish
    // directly. Keep the shared publish tail byte-for-byte identical from the
    // cell index through inactive-row zeroing, warp reduction, and row-tile
    // store. The Eq expressions above are separately pinned to one call each.
    fn publish_tail(source: &str) -> &str {
        let start = source
            .find(PUBLISH_TAIL_START)
            .expect("publish tail starts at the canonical cell index");
        let end = source[start..]
            .find(PUBLISH_TAIL_END)
            .map(|offset| start + offset + PUBLISH_TAIL_END.len())
            .expect("publish tail ends after the row-tile store");
        &source[start..end]
    }

    const PUBLISH_TAIL_START: &str = "  const u32 cell_base = 3 * selector.x1 + selector.x0;";
    const PUBLISH_TAIL_END: &str = "  }\n}";
    assert_eq!(publish_tail(R0), publish_tail(WINDOW_GEOMETRY));
    assert!(R0.contains("const u32 row = row_tile * BWD_WINDOW_ROWS_PER_TILE + lane;",));
    assert!(R0.contains("const u32 safe_row = active ? row : 0;"));
    assert!(
        R0.contains("gkr_compute_eq_inline<e4>(desc.batch.eq_low, desc.batch.eq_sizes, safe_row)",)
    );
    assert!(WINDOW_GEOMETRY.contains(
        "gkr_compute_eq_inline<e4>(desc.eq_low, desc.eq_sizes, active ? row_tile * BWD_WINDOW_ROWS_PER_TILE + lane : 0)",
    ));

    let mut seen = BTreeSet::new();
    for x0 in 0..3usize {
        for x1 in 0..3usize {
            for x2 in 0..3usize {
                seen.insert(9 * x2 + 3 * x1 + x0);
            }
        }
    }
    assert_eq!(seen, (0..27).collect());
}

mod cpu_dr_window_tensor_oracle {
    use prover::gkr::prover::dimension_reduction::lsb_backward::{
        lsb_dim_reducing_sumcheck_prove, LsbDimReducingRelation,
    };

    use super::*;
    use crate::backward::window::reference::tensor_round_tail_reference;
    use crate::backward::window_dr::reference::{
        batch_challenge_power, compare_dr_tensors, dr_r0_tensor_reference, DrTensorMismatch,
        DrTensorOracleError, DrTensorOracleProgram,
    };
    use crate::upstream::{BabyBearField, Field, FieldExtension, PrimeField};
    use gpu_core::primitives::field::BF;

    const OUTPUT_TYPES: [OutputType; 5] = [
        OutputType::PermutationProduct,
        OutputType::Lookup16Bits,
        OutputType::LookupTimestamps,
        OutputType::GenericLookup,
        OutputType::InitsAndTeardownsProduct,
    ];
    const INERT_TAIL_CELL: usize = 13;

    fn tensor_cell(low: usize, middle: usize, high: usize) -> usize {
        9 * low + 3 * middle + high
    }

    fn add(mut left: E4, right: E4) -> E4 {
        left.add_assign(&right);
        left
    }

    fn mul(mut left: E4, right: E4) -> E4 {
        left.mul_assign(&right);
        left
    }

    fn eq_weight(bit: usize, coordinate: E4) -> E4 {
        if bit == 0 {
            let mut result = E4::ONE;
            result.sub_assign(&coordinate);
            result
        } else {
            coordinate
        }
    }

    fn splitmix64(mut value: u64) -> u64 {
        value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
        value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        value ^ (value >> 31)
    }

    struct Rng(u64);

    impl Rng {
        fn next_u32(&mut self) -> u32 {
            self.0 = splitmix64(self.0);
            (self.0 >> 32) as u32
        }

        fn next_e4(&mut self) -> E4 {
            E4::from_array_of_base(core::array::from_fn(|_| {
                BF::from_u32_with_reduction(self.next_u32())
            }))
        }
    }

    fn input_address(slot: usize, operand: usize) -> GKRAddress {
        GKRAddress::InnerLayer {
            layer: 7,
            offset: 2 * slot + operand,
        }
    }

    fn output_address(slot: usize, operand: usize) -> GKRAddress {
        GKRAddress::InnerLayer {
            layer: 8,
            offset: 2 * slot + operand,
        }
    }

    struct Fixture {
        program: DrTensorOracleProgram,
        columns: BTreeMap<GKRAddress, Vec<E4>>,
        batch_base: E4,
        rho: [E4; 3],
        suffix_point: Vec<E4>,
        seed: [u32; 8],
    }

    impl Fixture {
        fn new(suffix_bits: usize) -> Self {
            let mut rng = Rng(splitmix64(
                0xd12f_00d5_1ab5_0001 ^ ((suffix_bits as u64) << 48),
            ));
            let suffix_rows = 1usize << suffix_bits;
            let mut rows = BTreeMap::new();
            let mut columns = BTreeMap::<GKRAddress, Vec<E4>>::new();

            for (slot, output_type) in OUTPUT_TYPES.into_iter().enumerate() {
                let inputs = [input_address(slot, 0), input_address(slot, 1)];
                let outputs = [output_address(slot, 0), output_address(slot, 1)];
                rows.insert(output_type, DrWindowInputOutput::new(inputs, outputs));

                for input in inputs {
                    columns.insert(
                        input,
                        (0..16 * suffix_rows).map(|_| rng.next_e4()).collect(),
                    );
                }

                if slot == 0 || slot == 4 {
                    for tower in 0..2 {
                        let input = &columns[&inputs[tower]];
                        let output = (0..8 * suffix_rows)
                            .map(|y| mul(input[2 * y], input[2 * y + 1]))
                            .collect();
                        columns.insert(outputs[tower], output);
                    }
                } else {
                    let numerator = &columns[&inputs[0]];
                    let denominator = &columns[&inputs[1]];
                    let output_num = (0..8 * suffix_rows)
                        .map(|y| {
                            add(
                                mul(numerator[2 * y], denominator[2 * y + 1]),
                                mul(numerator[2 * y + 1], denominator[2 * y]),
                            )
                        })
                        .collect();
                    let output_den = (0..8 * suffix_rows)
                        .map(|y| mul(denominator[2 * y], denominator[2 * y + 1]))
                        .collect();
                    columns.insert(outputs[0], output_num);
                    columns.insert(outputs[1], output_den);
                }
            }

            let lowered = lower_dr_window_program(&rows).expect("five-slot DR program lowers");
            Self {
                program: DrTensorOracleProgram::from_production(&lowered),
                columns,
                batch_base: rng.next_e4(),
                rho: core::array::from_fn(|_| rng.next_e4()),
                suffix_point: (0..suffix_bits).map(|_| rng.next_e4()).collect(),
                seed: core::array::from_fn(|_| rng.next_u32()),
            }
        }

        fn tensor(&self) -> [E4; 27] {
            dr_r0_tensor_reference(
                &self.program,
                &self.columns,
                self.batch_base,
                &self.suffix_point,
            )
            .expect("valid oracle fixture")
        }

        fn gate_at_boolean(&self, y: usize) -> E4 {
            let mut total = E4::ZERO;
            for slot in &self.program.slots {
                let addresses = slot
                    .source_ids
                    .map(|source_id| self.program.sources[usize::from(source_id)]);
                let weights = slot
                    .batch_exponents
                    .map(|exponent| batch_challenge_power(self.batch_base, exponent));
                if slot.slot == 0 || slot.slot == 4 {
                    for tower in 0..2 {
                        let input = &self.columns[&addresses[tower]];
                        total.add_assign(&mul(weights[tower], mul(input[2 * y], input[2 * y + 1])));
                    }
                } else {
                    let numerator = &self.columns[&addresses[0]];
                    let denominator = &self.columns[&addresses[1]];
                    let num = add(
                        mul(numerator[2 * y], denominator[2 * y + 1]),
                        mul(numerator[2 * y + 1], denominator[2 * y]),
                    );
                    let den = mul(denominator[2 * y], denominator[2 * y + 1]);
                    total.add_assign(&mul(weights[0], num));
                    total.add_assign(&mul(weights[1], den));
                }
            }
            total
        }

        fn initial_claim(&self) -> E4 {
            (0..8 * (1usize << self.suffix_point.len())).fold(E4::ZERO, |mut claim, y| {
                let mut weight = (0..3).fold(E4::ONE, |weight, bit| {
                    mul(weight, eq_weight((y >> bit) & 1, self.rho[bit]))
                });
                for (suffix_bit, coordinate) in self.suffix_point.iter().enumerate() {
                    weight.mul_assign(&eq_weight((y >> (3 + suffix_bit)) & 1, *coordinate));
                }
                claim.add_assign(&mul(weight, self.gate_at_boolean(y)));
                claim
            })
        }

        fn relations(&self) -> Vec<LsbDimReducingRelation<E4>> {
            let mut relations = Vec::new();
            for slot in &self.program.slots {
                let addresses = slot
                    .source_ids
                    .map(|source_id| self.program.sources[usize::from(source_id)]);
                let weights = slot
                    .batch_exponents
                    .map(|exponent| batch_challenge_power(self.batch_base, exponent));
                if slot.slot == 0 || slot.slot == 4 {
                    for tower in 0..2 {
                        relations.push(LsbDimReducingRelation::PairwiseProduct {
                            input: addresses[tower],
                            output: addresses[2 + tower],
                            alpha: weights[tower],
                        });
                    }
                } else {
                    relations.push(LsbDimReducingRelation::LogupPair {
                        num: addresses[0],
                        den: addresses[1],
                        num_output: addresses[2],
                        den_output: addresses[3],
                        alpha_num: weights[0],
                        alpha_den: weights[1],
                    });
                }
            }
            relations
        }
    }

    type TailObservation = ([E4; 12], [E4; 3], [u32; 8], E4, E4);

    fn run_tail(fixture: &Fixture, tensor: [E4; 27]) -> TailObservation {
        let mut seed = fixture.seed;
        let mut claim = fixture.initial_claim();
        let mut eq_prefactor = E4::ONE;
        let (coefficients, challenges) = tensor_round_tail_reference(
            tensor,
            &fixture.rho,
            &mut seed,
            &mut claim,
            &mut eq_prefactor,
        );
        (coefficients, challenges, seed, claim, eq_prefactor)
    }

    #[test]
    fn cpu_dr_window_r0_tensor_oracle_matches_upstream_and_tail() {
        let fixture = Fixture::new(0);
        assert_eq!(fixture.program.enabled_mask, 0x1f);
        assert_eq!(
            fixture
                .program
                .slots
                .iter()
                .map(|slot| slot.batch_exponents)
                .collect::<Vec<_>>(),
            vec![[0, 1], [2, 3], [4, 5], [6, 7], [8, 9]],
        );

        let tensor = fixture.tensor();
        let tail = run_tail(&fixture, tensor);
        let input_polys = fixture
            .program
            .slots
            .iter()
            .flat_map(|slot| slot.source_ids[..2].iter().copied())
            .map(|source_id| {
                let address = fixture.program.sources[usize::from(source_id)];
                (address, fixture.columns[&address].as_slice())
            })
            .collect::<BTreeMap<_, _>>();
        let worker = worker::Worker::new_with_num_threads(2);
        let upstream = lsb_dim_reducing_sumcheck_prove::<BabyBearField, E4>(
            &input_polys,
            &fixture.relations(),
            &fixture.rho,
            fixture.initial_claim(),
            &tail.1,
            &worker,
        );
        let upstream_coefficients = upstream
            .round_coefficients
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        assert_eq!(tail.0.as_slice(), upstream_coefficients.as_slice());
        assert_eq!(tail.3, upstream.final_claim);
        assert_eq!(tail.4, upstream.eq_factor);

        for low in 0..2 {
            for middle in 0..2 {
                for high in 0..2 {
                    let y = low | (middle << 1) | (high << 2);
                    assert_eq!(
                        tensor[tensor_cell(low, middle, high)],
                        fixture.gate_at_boolean(y),
                        "materialized output constant term at ({low},{middle},{high})",
                    );
                }
            }
        }
    }

    #[test]
    fn cpu_dr_window_r0_tensor_oracle_contracts_suffix_eq_before_tail() {
        let fixture = Fixture::new(2);
        let tensor = fixture.tensor();
        for low in 0..2 {
            for middle in 0..2 {
                for high in 0..2 {
                    let low_y = low | (middle << 1) | (high << 2);
                    let expected = (0..4).fold(E4::ZERO, |mut total, suffix_row| {
                        let suffix_weight = fixture.suffix_point.iter().enumerate().fold(
                            E4::ONE,
                            |weight, (bit, coordinate)| {
                                mul(weight, eq_weight((suffix_row >> bit) & 1, *coordinate))
                            },
                        );
                        total.add_assign(&mul(
                            suffix_weight,
                            fixture.gate_at_boolean((suffix_row << 3) | low_y),
                        ));
                        total
                    });
                    assert_eq!(tensor[tensor_cell(low, middle, high)], expected);
                }
            }
        }

        let tail = run_tail(&fixture, tensor);
        let input_polys = fixture
            .program
            .slots
            .iter()
            .flat_map(|slot| slot.source_ids[..2].iter().copied())
            .map(|source_id| {
                let address = fixture.program.sources[usize::from(source_id)];
                (address, fixture.columns[&address].as_slice())
            })
            .collect::<BTreeMap<_, _>>();
        let tau = fixture
            .rho
            .into_iter()
            .chain(fixture.suffix_point.iter().copied())
            .collect::<Vec<_>>();
        let challenges = tail
            .1
            .into_iter()
            .chain(fixture.suffix_point.iter().copied())
            .collect::<Vec<_>>();
        let worker = worker::Worker::new_with_num_threads(2);
        let upstream = lsb_dim_reducing_sumcheck_prove::<BabyBearField, E4>(
            &input_polys,
            &fixture.relations(),
            &tau,
            fixture.initial_claim(),
            &challenges,
            &worker,
        );
        let first_three = upstream
            .round_coefficients
            .into_iter()
            .take(3)
            .flatten()
            .collect::<Vec<_>>();
        assert_eq!(tail.0.as_slice(), first_three.as_slice());
    }

    #[test]
    fn cpu_dr_window_r0_tensor_oracle_rejects_wire_mutations() {
        let fixture = Fixture::new(0);
        let expected = fixture.tensor();

        let mut section = fixture.program.clone();
        section.section_endpoints[2] -= 1;
        assert_eq!(
            dr_r0_tensor_reference(&section, &fixture.columns, fixture.batch_base, &[]),
            Err(DrTensorOracleError::SectionEndpointMismatch {
                section: 2,
                expected: 3,
                observed: 2,
            }),
        );

        let mut lane = fixture.program.clone();
        lane.slots[0].source_ids[0] = lane.slots[0].source_ids[1];
        lane.source_lanes[0].source_id = lane.slots[0].source_ids[0];
        let observed = dr_r0_tensor_reference(&lane, &fixture.columns, fixture.batch_base, &[])
            .expect("coherent lane mutation remains structurally valid");
        assert!(matches!(
            compare_dr_tensors(&expected, &observed),
            Err(DrTensorMismatch::Cell { .. })
        ));

        let mut exponent = fixture.program.clone();
        exponent.slots[0].batch_exponents[0] += 1;
        let observed = dr_r0_tensor_reference(&exponent, &fixture.columns, fixture.batch_base, &[])
            .expect("batch exponent mutation remains structurally valid");
        assert!(matches!(
            compare_dr_tensors(&expected, &observed),
            Err(DrTensorMismatch::Cell { .. })
        ));

        let mut mask = fixture.program.clone();
        mask.enabled_mask ^= 1;
        assert_eq!(
            dr_r0_tensor_reference(&mask, &fixture.columns, fixture.batch_base, &[]),
            Err(DrTensorOracleError::EnabledMaskMismatch {
                expected: 0x1f,
                observed: 0x1e,
            }),
        );
    }

    #[test]
    fn cpu_dr_window_r0_tensor_oracle_detects_value_axis_and_output_mutations() {
        let fixture = Fixture::new(0);
        let expected = fixture.tensor();

        for index in 0..27 {
            let mut one_cell = expected;
            one_cell[index].add_assign(&E4::ONE);
            assert!(matches!(
                compare_dr_tensors(&expected, &one_cell),
                Err(DrTensorMismatch::Cell {
                    index: observed,
                    ..
                }) if observed == index
            ));
        }

        let transposed: [E4; 27] = core::array::from_fn(|index| {
            let low = index / 9;
            let middle = (index / 3) % 3;
            let high = index % 3;
            expected[tensor_cell(high, middle, low)]
        });
        assert!(matches!(
            compare_dr_tensors(&expected, &transposed),
            Err(DrTensorMismatch::Cell { .. })
        ));

        let mut interleave = fixture.columns.clone();
        let input = fixture.program.sources[usize::from(fixture.program.slots[0].source_ids[0])];
        interleave.get_mut(&input).unwrap().swap(0, 1);
        let observed =
            dr_r0_tensor_reference(&fixture.program, &interleave, fixture.batch_base, &[])
                .expect("2*Y+b mutation preserves shape");
        assert!(matches!(
            compare_dr_tensors(&expected, &observed),
            Err(DrTensorMismatch::Cell { .. })
        ));

        let mut materialized_output = fixture.columns.clone();
        let output = fixture.program.sources[usize::from(fixture.program.slots[1].source_ids[2])];
        materialized_output.get_mut(&output).unwrap()[0].add_assign(&E4::ONE);
        let observed = dr_r0_tensor_reference(
            &fixture.program,
            &materialized_output,
            fixture.batch_base,
            &[],
        )
        .expect("materialized-output mutation preserves shape");
        assert!(matches!(
            compare_dr_tensors(&expected, &observed),
            Err(DrTensorMismatch::Cell { .. })
        ));

        let baseline_tail = run_tail(&fixture, expected);
        let inert = (0..27)
            .filter(|index| {
                let mut perturbed = expected;
                perturbed[*index].add_assign(&E4::ONE);
                run_tail(&fixture, perturbed) == baseline_tail
            })
            .collect::<Vec<_>>();
        assert_eq!(inert, vec![INERT_TAIL_CELL]);
    }
}
