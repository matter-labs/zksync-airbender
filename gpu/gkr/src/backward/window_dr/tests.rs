use std::collections::{BTreeMap, BTreeSet};
use std::mem::{align_of, offset_of, size_of};
use std::sync::Arc;

use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::field::E4;
use gpu_gkr_compiler::{
    lower_dr_window_program, project_dr_window_inputs, DrWindowInputOutput,
    DR_WINDOWED_CONT_BLOCK_THREADS, DR_WINDOWED_CONT_KERNEL_SYMBOL, DR_WINDOWED_R0_BLOCK_THREADS,
    DR_WINDOWED_R0_KERNEL_SYMBOL, KERNEL_ARGUMENT_CEILING_BYTES,
};

use super::binding::{
    assemble_dr_window_continuation_batch, bind_dr_window_continuation_launch,
    dr_window_partials_len, dr_window_partials_maximum, dr_window_row_tiles,
    resolve_dr_global_active_eq_slot, resolve_dr_window_continuation_kernel,
    resolve_dr_window_kernel, validate_dr_r0_eq_contract,
    validate_dr_window_continuation_eq_contract, validate_dr_window_folding_steps,
    DrCompactSourceTableBuilder, DrContinuationFactoredEqView, DrWindowBindError,
    DrWindowContinuationLaunchBinding, DrWindowLaunchBinding, DrWindowRuntimeScratch,
};
use super::composition::{
    build_raw_input_owner, continuation_window_count, dr_window_continuation_pass_geometry,
    megakernel_entry_round, plan_dr_window_continuations, DrWindowContinuationParity,
    DrWindowContinuationPlannedSource, DrWindowRawInputKeepalive,
};
use super::generated_registry::{
    DR_WINDOWED_CONT_DEFINED_MASK, DR_WINDOWED_CONT_UNIVERSAL_KERNEL, DR_WINDOWED_R0_DEFINED_MASK,
    DR_WINDOWED_R0_UNIVERSAL_KERNEL,
};
use crate::backward::kernels::{
    make_eq_sizes, pack_cache_u16, pack_source_u16, FoldingArenaBinding,
    GpuGKRDimensionReducingBatch, GpuGKRSourceRecord, GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN,
};
use crate::backward::GKR_EQ_GROUP_TABLE_LEN;
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

#[test]
fn cpu_dr_window_continuation_d2_abi_registry_binder_and_native_contract() {
    const BINDING: &str = include_str!("binding.rs");
    const MODULE: &str = include_str!("mod.rs");
    const REGISTRY: &str = include_str!("generated_registry.rs");
    const CMAKE: &str = include_str!("../../../native/gkr/backward/CMakeLists.txt");
    const WINDOW_GEOMETRY: &str =
        include_str!("../../../native/gkr/backward/window/window_geometry.cuh");
    const LOOKUP_HELPERS: &str = include_str!("../../../native/gkr/support/lookup_helpers.cuh");

    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("resolve repository root from gpu/gkr");
    let continuation_path = "gpu/gkr/native/gkr/backward/window_dr/continuation.cuh";
    let manifest_path = "gpu/gkr/native/gkr/backward/generated/dr_windowed_cont_manifest.cuh";
    let translation_unit_path = "gpu/gkr/native/gkr/backward/generated/dr_cont_window_universal.cu";
    let continuation = std::fs::read_to_string(root.join(continuation_path)).unwrap_or_default();
    let manifest = std::fs::read_to_string(root.join(manifest_path)).unwrap_or_default();
    let translation_unit =
        std::fs::read_to_string(root.join(translation_unit_path)).unwrap_or_default();

    assert_eq!(size_of::<DrWindowContinuationLaunchBinding>(), 384);
    assert_eq!(align_of::<DrWindowContinuationLaunchBinding>(), 16);
    assert!(size_of::<DrWindowContinuationLaunchBinding>() <= KERNEL_ARGUMENT_CEILING_BYTES);
    assert_eq!(offset_of!(DrWindowContinuationLaunchBinding, batch), 0);
    assert_eq!(
        offset_of!(DrWindowContinuationLaunchBinding, eq_high_0),
        336
    );
    assert_eq!(
        offset_of!(DrWindowContinuationLaunchBinding, eq_high_1),
        344
    );
    assert_eq!(offset_of!(DrWindowContinuationLaunchBinding, partials), 352);
    assert_eq!(
        offset_of!(DrWindowContinuationLaunchBinding, claim_point),
        360
    );
    assert_eq!(offset_of!(DrWindowContinuationLaunchBinding, log_rows), 368);
    assert_eq!(
        offset_of!(DrWindowContinuationLaunchBinding, start_round),
        372
    );
    assert_eq!(offset_of!(DrWindowContinuationLaunchBinding, reserved), 376);
    assert_eq!(DR_WINDOWED_CONT_BLOCK_THREADS, 288);
    assert_eq!(DR_WINDOWED_CONT_DEFINED_MASK, 0x1f);
    assert_eq!(
        DR_WINDOWED_CONT_UNIVERSAL_KERNEL.symbol_name,
        DR_WINDOWED_CONT_KERNEL_SYMBOL
    );
    for mask in 1..=DR_WINDOWED_CONT_DEFINED_MASK {
        assert_eq!(
            resolve_dr_window_continuation_kernel(mask)
                .unwrap()
                .symbol_name,
            DR_WINDOWED_CONT_KERNEL_SYMBOL,
        );
    }
    assert_eq!(
        resolve_dr_window_continuation_kernel(0).err().unwrap(),
        DrWindowBindError::ZeroMask,
    );
    for bit in 5..32 {
        let undefined = 1u32 << bit;
        assert_eq!(
            resolve_dr_window_continuation_kernel(undefined)
                .err()
                .unwrap(),
            DrWindowBindError::UndefinedMaskBits { bits: undefined },
        );
    }

    let folding_steps = 10;
    let start_round = 3;
    let suffix_log = folding_steps - start_round;
    let challenge_offset = start_round + 3;
    let challenge_count = folding_steps - challenge_offset;
    let high_0 = 0x10_000usize as *mut E4;
    let high_1 = (high_0 as usize + GKR_EQ_GROUP_TABLE_LEN * size_of::<E4>()) as *mut E4;
    let low = 0x30_000usize as *mut E4;
    let eq = DrContinuationFactoredEqView::new(
        high_0,
        high_1,
        low,
        make_eq_sizes(challenge_count),
        challenge_offset as u32,
        challenge_count as u32,
    );
    assert_eq!(
        validate_dr_window_continuation_eq_contract(folding_steps, start_round, eq),
        Ok(()),
    );

    let mut batch = GpuGKRDimensionReducingBatch::<E4> {
        enabled_mask: 1,
        eq_low: low,
        eq_sizes: eq.sizes,
        ..Default::default()
    };
    batch.tables.bases[0] = 0x40_000usize as *const u8;
    batch.tables.bases[1] = 0x50_000usize as *const u8;
    batch.tables.log2_stride[0] = 11;
    batch.tables.log2_stride[1] = 8;
    for input_operand in 0..2 {
        batch.slots[0].io[input_operand] = GpuGKRSourceRecord::new(
            pack_source_u16(input_operand == 0, 0, input_operand as u16),
            pack_cache_u16(1, input_operand as u16),
        );
    }
    let required = dr_window_partials_len(suffix_log);
    assert_eq!(required, 54);
    match std::panic::catch_unwind(|| dr_window_partials_len(1usize << suffix_log)) {
        Ok(count_as_log) => assert_ne!(count_as_log, required),
        Err(_) => {}
    }
    let mut partials_backing = vec![E4::default(); required];
    let scratch = DrWindowRuntimeScratch {
        partials: partials_backing.as_mut_ptr(),
        partials_capacity: required,
    };
    let claim_point_backing = vec![E4::default(); folding_steps];
    let claim_point = claim_point_backing.as_ptr();
    let launch = bind_dr_window_continuation_launch(
        batch,
        folding_steps,
        start_round,
        eq,
        scratch,
        claim_point,
    )
    .expect("the exact continuation descriptor geometry binds");
    assert_eq!(launch.selected_symbol(), DR_WINDOWED_CONT_KERNEL_SYMBOL);
    assert_eq!(launch.row_tiles, 1);
    assert_eq!(launch.binding.log_rows, 4);
    assert_eq!(launch.binding.start_round, 3);
    assert_eq!(launch.binding.eq_high_0, high_0);
    assert_eq!(launch.binding.eq_high_1, high_1);
    assert_eq!(launch.binding.batch.eq_low, low);
    assert_eq!(launch.binding.reserved, [0; 2]);
    assert!(launch.binding.batch.contributions.is_null());

    let wrong_offset = DrContinuationFactoredEqView::new(
        high_0,
        high_1,
        low,
        eq.sizes,
        (challenge_offset - 1) as u32,
        challenge_count as u32,
    );
    assert_eq!(
        validate_dr_window_continuation_eq_contract(folding_steps, start_round, wrong_offset,),
        Err(DrWindowBindError::EqBuildOffset {
            expected: challenge_offset,
            observed: challenge_offset - 1,
        }),
    );
    let wrong_count = DrContinuationFactoredEqView::new(
        high_0,
        high_1,
        low,
        eq.sizes,
        challenge_offset as u32,
        (challenge_count - 1) as u32,
    );
    assert_eq!(
        validate_dr_window_continuation_eq_contract(folding_steps, start_round, wrong_count,),
        Err(DrWindowBindError::EqSizeMismatch),
    );
    let wrong_sizes = DrContinuationFactoredEqView::new(
        high_0,
        high_1,
        low,
        make_eq_sizes(challenge_count - 1),
        challenge_offset as u32,
        challenge_count as u32,
    );
    assert_eq!(
        validate_dr_window_continuation_eq_contract(folding_steps, start_round, wrong_sizes,),
        Err(DrWindowBindError::EqSizeMismatch),
    );
    let noncontiguous = DrContinuationFactoredEqView::new(
        high_0,
        (high_1 as usize + size_of::<E4>()) as *mut E4,
        low,
        eq.sizes,
        challenge_offset as u32,
        challenge_count as u32,
    );
    assert!(matches!(
        validate_dr_window_continuation_eq_contract(folding_steps, start_round, noncontiguous,),
        Err(DrWindowBindError::ContinuationEqHighLayout { .. })
    ));
    let null_high = DrContinuationFactoredEqView::new(
        std::ptr::null_mut(),
        high_1,
        low,
        eq.sizes,
        challenge_offset as u32,
        challenge_count as u32,
    );
    assert_eq!(
        validate_dr_window_continuation_eq_contract(folding_steps, start_round, null_high),
        Err(DrWindowBindError::NullContinuationPointer {
            pointer: "eq_high_0",
        }),
    );

    let bind_error = |batch, scratch, claim_point| {
        bind_dr_window_continuation_launch(
            batch,
            folding_steps,
            start_round,
            eq,
            scratch,
            claim_point,
        )
        .err()
        .expect("mutation must reject")
    };
    assert_eq!(
        bind_error(
            batch,
            DrWindowRuntimeScratch {
                partials_capacity: required - 1,
                ..scratch
            },
            claim_point,
        ),
        DrWindowBindError::ScratchCapacity {
            required,
            capacity: required - 1,
        },
    );
    assert_eq!(
        bind_error(
            batch,
            DrWindowRuntimeScratch {
                partials: std::ptr::null_mut(),
                ..scratch
            },
            claim_point,
        ),
        DrWindowBindError::NullContinuationPointer {
            pointer: "partials",
        },
    );
    assert_eq!(
        bind_error(batch, scratch, std::ptr::null()),
        DrWindowBindError::NullContinuationPointer {
            pointer: "claim_point",
        },
    );
    let mut null_source = batch;
    null_source.tables.bases[0] = std::ptr::null();
    assert!(matches!(
        bind_error(null_source, scratch, claim_point),
        DrWindowBindError::NullContinuationTableBase {
            destination: false,
            ..
        }
    ));
    let mut null_destination = batch;
    null_destination.tables.bases[1] = std::ptr::null();
    assert!(matches!(
        bind_error(null_destination, scratch, claim_point),
        DrWindowBindError::NullContinuationTableBase {
            destination: true,
            ..
        }
    ));
    let mut contributions = batch;
    contributions.contributions = 0x80_000usize as *mut E4;
    assert_eq!(
        bind_error(contributions, scratch, claim_point),
        DrWindowBindError::ContinuationContributionsMustBeNull,
    );
    let mut wrong_low = batch;
    wrong_low.eq_low = 0x90_000usize as *const E4;
    assert_eq!(
        bind_error(wrong_low, scratch, claim_point),
        DrWindowBindError::ContinuationEqLowMismatch,
    );

    let mut missing = Vec::<String>::new();
    let mut require = |surface: &str, label: &str, needle: &str| {
        if !surface.contains(needle) {
            missing.push(format!("{label}: {needle}"));
        }
    };

    for needle in [
        "DrWindowContinuationLaunchBinding",
        "DrWindowContinuationLaunch",
        "launch_dr_window_continuation",
    ] {
        require(MODULE, "Rust module exports", needle);
    }
    for needle in [
        "DrWindowContinuationKernelEntry",
        "GkrDrContinuationWindow3",
        "DR_WINDOWED_CONT_BLOCK_THREADS",
        "ab_gkr_dr_cont_window3_universal_kernel",
    ] {
        require(REGISTRY, "generated Rust registry", needle);
    }
    for needle in [
        "window_dr/continuation.cuh",
        "generated/dr_windowed_cont_manifest.cuh",
        "generated/dr_cont_window_universal.cu",
    ] {
        require(CMAKE, "CMake target_sources", needle);
    }

    for needle in [
        "struct alignas(16) gkr_dr_cont_window3_desc",
        "gkr_dim_reducing_batch<e4> batch",
        "const e4 *eq_high_0",
        "const e4 *eq_high_1",
        "e4 *partials",
        "const e4 *claim_point",
        "u32 log_rows",
        "u32 start_round",
        "u32 reserved[2]",
        "sizeof(gkr_dr_cont_window3_desc) == 384",
        "alignof(gkr_dr_cont_window3_desc) == 16",
        "__builtin_offsetof(gkr_dr_cont_window3_desc, eq_high_0) == 336",
        "__builtin_offsetof(gkr_dr_cont_window3_desc, eq_high_1) == 344",
        "__builtin_offsetof(gkr_dr_cont_window3_desc, partials) == 352",
        "__builtin_offsetof(gkr_dr_cont_window3_desc, claim_point) == 360",
        "__builtin_offsetof(gkr_dr_cont_window3_desc, log_rows) == 368",
        "__builtin_offsetof(gkr_dr_cont_window3_desc, start_round) == 372",
        "__builtin_offsetof(gkr_dr_cont_window3_desc, reserved) == 376",
        "std::is_standard_layout_v<gkr_dr_cont_window3_desc>",
        "std::is_trivially_copyable_v<gkr_dr_cont_window3_desc>",
        "dr_window_load_e4_pair_guarded",
        "DR_CONTINUATION_FIRST_ACCESS_BIT",
        "__syncthreads()",
        "gkr_load_slot_batch_challenges",
        "gkr_pairwise_continuation_accumulate",
        "gkr_lookup_continuation_accumulate",
        "gkr_compute_eq_inline_global",
        "9 * x2 + cell_base",
    ] {
        require(&continuation, continuation_path, needle);
    }
    for needle in [
        "DR_WINDOW_CONT_DEFINED_MASK",
        "DR_WINDOW_CONT_BLOCK_THREADS",
        "DR_WINDOW_CONT_KERNEL_COUNT = 1",
    ] {
        require(&manifest, manifest_path, needle);
    }
    for needle in [
        "ab_gkr_dr_cont_window3_universal_kernel",
        "__launch_bounds__(DR_WINDOW_CONT_BLOCK_THREADS)",
        "gkr_dr_cont_window3_desc",
        "dr_window_continuation(desc)",
    ] {
        require(&translation_unit, translation_unit_path, needle);
    }

    assert!(
        missing.is_empty(),
        "D2 continuation ABI/generator/registry/binder/native contract is missing:\n{}",
        missing.join("\n"),
    );
    assert_eq!(continuation.matches("__syncthreads()").count(), 1);
    assert_eq!(continuation.matches("gkr_get_continuing_value(").count(), 0);
    assert!(continuation.contains("source.first_access && output_pair < output_pair_count"));
    assert!(!continuation.contains("bwd_window_product_tensor"));
    assert_eq!(
        continuation
            .matches("dr_window_continuation_add_product(total")
            .count(),
        4,
    );
    for shared_publish_semantic in [
        "const u32 cell_base = 3 * selector.x1 + selector.x0;",
        "active ? e4::mul(equality, values[x2]) : e4::ZERO()",
        "value = bwd_window_warp_sum(value);",
        "static_cast<size_t>(row_tile) * BWD_WINDOW_TENSOR_CELLS + 9 * x2 + cell_base",
    ] {
        assert!(
            WINDOW_GEOMETRY.contains(shared_publish_semantic),
            "shared publish semantic drift: {shared_publish_semantic}",
        );
        assert!(
            continuation.contains(shared_publish_semantic),
            "DR continuation publish semantic drift: {shared_publish_semantic}",
        );
    }
    assert!(LOOKUP_HELPERS.contains("gkr_pairwise_continuation_accumulate"));
    assert!(LOOKUP_HELPERS.contains("gkr_lookup_continuation_accumulate"));
    assert!(LOOKUP_HELPERS.contains("const E num0 = E::fma(a0, d0, E::mul(c0, b0));"));
    assert!(LOOKUP_HELPERS.contains("const E den0 = E::mul(b0, d0);"));
    let launch_source = &BINDING[BINDING
        .find("pub(crate) fn launch_dr_window_continuation")
        .expect("continuation launcher is present")..];
    assert!(launch_source.contains("launch_build_eq_high_and_low_groups_from_point("));
    assert!(!launch_source.contains("get_eq_high_constant_device_ptr()"));
    assert!(!continuation.contains("ab_gkr_eq_high"));
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum D3Parity {
    Even,
    Odd,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum D3ContinuationSource {
    Raw,
    Arena(D3Parity),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct D3ContinuationPassPlan {
    pass_index: usize,
    start_round: usize,
    source: D3ContinuationSource,
    destination: D3Parity,
    per_poly_len: usize,
    log2_stride: usize,
    challenge_offset: usize,
    challenge_count: usize,
    entry_sizes: crate::backward::GkrEqSizes,
    one_fold_boundary_sizes: crate::backward::GkrEqSizes,
    partials_len: usize,
    claim_point_offset: usize,
    coeffs_offset: usize,
}

fn expected_d3_continuation_passes(
    folding_steps: usize,
    landed_window_count: usize,
    landed_entry_round: usize,
) -> Vec<D3ContinuationPassPlan> {
    use crate::backward::kernels::record_active_eq_slot_fold;

    assert!(landed_window_count <= 4);
    assert_eq!(landed_entry_round, 3 + 3 * landed_window_count);
    (0..landed_window_count)
        .map(|pass_index| {
            let start_round = 3 + 3 * pass_index;
            assert!(start_round + 3 < folding_steps);
            let log2_stride = folding_steps + 1 - start_round;
            let challenge_offset = start_round + 3;
            let challenge_count = folding_steps - challenge_offset;
            let entry_sizes = make_eq_sizes(challenge_count);
            let mut one_fold_boundary_sizes = entry_sizes;
            record_active_eq_slot_fold(&mut one_fold_boundary_sizes);
            let destination = if pass_index % 2 == 0 {
                D3Parity::Even
            } else {
                D3Parity::Odd
            };
            let source = if pass_index == 0 {
                D3ContinuationSource::Raw
            } else {
                D3ContinuationSource::Arena(if pass_index % 2 == 0 {
                    D3Parity::Odd
                } else {
                    D3Parity::Even
                })
            };
            D3ContinuationPassPlan {
                pass_index,
                start_round,
                source,
                destination,
                per_poly_len: 1usize << log2_stride,
                log2_stride,
                challenge_offset,
                challenge_count,
                entry_sizes,
                one_fold_boundary_sizes,
                partials_len: dr_window_partials_len(folding_steps - start_round),
                claim_point_offset: start_round,
                coeffs_offset: 4 * start_round,
            }
        })
        .collect()
}

#[test]
fn cpu_dr_window_hook_composes_landed_r0() {
    const COMPOSITION: &str = include_str!("composition.rs");
    const BINDING: &str = include_str!("binding.rs");

    let hook_start = COMPOSITION
        .find("pub(crate) struct DrWindowLayerCompositionHook")
        .expect("landed R0 composition hook must remain present");
    let hook_end = COMPOSITION[hook_start..]
        .find("impl DrWindowLayerCompositionHook")
        .map(|offset| hook_start + offset)
        .expect("landed R0 composition hook implementation must remain present");
    let hook = &COMPOSITION[hook_start..hook_end];
    for landed_field in [
        "r0_launch:",
        "continuation_window_count:",
        "megakernel_entry_round:",
        "r0_eq:",
        "raw_inputs:",
        "partials_capacity:",
        "continuation_program:",
        "continuation_projection:",
    ] {
        assert!(
            hook.contains(landed_field),
            "D3 must preserve landed hook field {landed_field}",
        );
    }

    let anchors = [(6usize, 0usize), (7, 1), (10, 2), (13, 3), (16, 4)];
    for (folding_steps, window_count) in anchors {
        assert_eq!(continuation_window_count(folding_steps), window_count);
        let entry_round = 3 + 3 * window_count;
        let passes = expected_d3_continuation_passes(folding_steps, window_count, entry_round);
        let production =
            plan_dr_window_continuations(folding_steps, window_count, entry_round).unwrap();
        assert_eq!(production.len(), passes.len());
        for (expected, observed) in passes.iter().zip(&production) {
            assert_eq!(observed.pass_index, expected.pass_index);
            assert_eq!(observed.start_round, expected.start_round);
            assert_eq!(observed.per_poly_len, expected.per_poly_len);
            assert_eq!(observed.log2_stride as usize, expected.log2_stride);
            assert_eq!(observed.challenge_offset, expected.challenge_offset);
            assert_eq!(observed.challenge_count, expected.challenge_count);
            assert_eq!(observed.eq_entry_sizes, expected.entry_sizes);
            assert_eq!(
                observed.one_fold_boundary_sizes,
                expected.one_fold_boundary_sizes,
            );
            assert_eq!(observed.partials_len, expected.partials_len);
            assert_eq!(
                observed.destination,
                match expected.destination {
                    D3Parity::Even => DrWindowContinuationParity::Even,
                    D3Parity::Odd => DrWindowContinuationParity::Odd,
                },
            );
            assert_eq!(
                observed.source,
                match expected.source {
                    D3ContinuationSource::Raw => DrWindowContinuationPlannedSource::Raw,
                    D3ContinuationSource::Arena(D3Parity::Even) => {
                        DrWindowContinuationPlannedSource::Arena(DrWindowContinuationParity::Even)
                    }
                    D3ContinuationSource::Arena(D3Parity::Odd) => {
                        DrWindowContinuationPlannedSource::Arena(DrWindowContinuationParity::Odd)
                    }
                },
            );
        }
        let arena_count = passes
            .iter()
            .map(|pass| pass.destination)
            .collect::<BTreeSet<_>>()
            .len();
        assert_eq!(arena_count, window_count.min(2));
        if window_count == 0 {
            assert!(passes.is_empty(), "W'=0 must allocate and bind no arena");
            continue;
        }
        assert_eq!(passes[0].destination, D3Parity::Even);
        assert_eq!(passes[0].per_poly_len, 1usize << (folding_steps - 2));
        if window_count > 1 {
            assert_eq!(passes[1].destination, D3Parity::Odd);
            assert_eq!(passes[1].per_poly_len, 1usize << (folding_steps - 5));
        }
        for parity in [D3Parity::Even, D3Parity::Odd] {
            let same_parity = passes
                .iter()
                .filter(|pass| pass.destination == parity)
                .collect::<Vec<_>>();
            for pair in same_parity.windows(2) {
                assert_eq!(pair[0].per_poly_len, 64 * pair[1].per_poly_len);
                assert_eq!(pair[0].log2_stride, pair[1].log2_stride + 6);
            }
        }
    }

    // A deliberately shorter, internally consistent landed plan for f=20
    // proves that D3 consumes the hook's W'/entry pair instead of recomputing
    // the formula's W'=4/entry=15 in a competing planner.
    let folding_steps = 20usize;
    let landed_window_count = 2usize;
    let landed_entry_round = 9usize;
    assert_ne!(
        landed_window_count,
        continuation_window_count(folding_steps)
    );
    assert_ne!(landed_entry_round, megakernel_entry_round(folding_steps));
    let landed =
        expected_d3_continuation_passes(folding_steps, landed_window_count, landed_entry_round);
    let landed_production =
        plan_dr_window_continuations(folding_steps, landed_window_count, landed_entry_round)
            .unwrap();
    assert_eq!(landed.len(), landed_window_count);
    assert_eq!(landed_production.len(), landed_window_count);
    assert_eq!(landed.last().unwrap().start_round + 3, landed_entry_round);
    assert_eq!(
        landed_production.last().unwrap().start_round + 3,
        landed_entry_round,
    );

    let mut legal_boundary_count = 0usize;
    for folding_steps in 4usize..=23 {
        for start_round in (3..folding_steps).step_by(3) {
            if start_round + 3 >= folding_steps {
                continue;
            }
            let geometry =
                dr_window_continuation_pass_geometry(folding_steps, start_round).unwrap();
            assert_eq!(geometry.start_round, start_round);
            assert_eq!(geometry.pass_index, (start_round - 3) / 3);
            assert_eq!(
                geometry.per_poly_len,
                1usize << (folding_steps + 1 - start_round),
            );
            assert_eq!(
                geometry.eq_entry_sizes,
                make_eq_sizes(folding_steps - start_round - 3),
            );
            let mut boundary = geometry.eq_entry_sizes;
            crate::backward::kernels::record_active_eq_slot_fold(&mut boundary);
            assert_eq!(geometry.one_fold_boundary_sizes, boundary);
            legal_boundary_count += 1;
        }
    }
    assert_eq!(legal_boundary_count, 57);

    let required_hook_state = [
        "DrWindowContinuationPass",
        "DrContinuationFactoredEqScratch",
        "DrWindowContinuationArena",
        "continuation_keepalives:",
    ];
    let missing_hook_state = required_hook_state
        .into_iter()
        .filter(|needle| !hook.contains(needle))
        .collect::<Vec<_>>();
    assert!(
        missing_hook_state.is_empty(),
        "RED D3 hook lacks continuation owners/keepalives: {missing_hook_state:?}",
    );

    let binder_start = BINDING
        .find("fn bind_dr_window_continuations")
        .expect("RED D3 lacks bind_dr_window_continuations");
    let binder = &BINDING[binder_start..];
    assert!(binder.contains("hook.continuation_window_count"));
    assert!(binder.contains("hook.megakernel_entry_round"));
    assert!(!binder.contains("continuation_window_count(hook.r0_launch.folding_steps)"));
    assert!(!binder.contains("megakernel_entry_round(hook.r0_launch.folding_steps)"));
}

#[test]
fn cpu_dr_window_partials_retain_maximum() {
    let mut checked = 0usize;
    for folding_steps in 4usize..=23 {
        let r0 = dr_window_partials_len(folding_steps);
        let continuation = expected_d3_continuation_passes(
            folding_steps,
            continuation_window_count(folding_steps),
            megakernel_entry_round(folding_steps),
        )
        .into_iter()
        .map(|pass| pass.partials_len)
        .collect::<Vec<_>>();
        for legacy in [0usize, r0.saturating_sub(1), r0 + 7] {
            let expected = std::iter::once(legacy)
                .chain(std::iter::once(r0))
                .chain(continuation.iter().copied())
                .max()
                .unwrap();
            let observed = dr_window_partials_maximum(legacy, r0, continuation.iter().copied());
            assert_eq!(observed, expected);
            assert!(expected >= legacy);
            assert!(expected >= r0);
            assert!(continuation.iter().all(|&len| expected >= len));

            if legacy > r0 {
                assert_ne!(r0, expected, "R0-only replacement mutation survived");
            }
            if legacy < r0 {
                assert_ne!(
                    legacy, expected,
                    "legacy-only replacement mutation survived"
                );
            }
            if let Some(&last) = continuation.last().filter(|&&last| last < expected) {
                assert_ne!(
                    last, expected,
                    "last-pass replacement mutation survived at f={folding_steps}",
                );
            }
            checked += 1;
        }
    }
    assert_eq!(checked, 60);
}

#[test]
fn cpu_dr_window_continuation_host_chain_contract_is_closed() {
    const BINDING: &str = include_str!("binding.rs");
    const SUMCHECK_PLAN: &str = include_str!("../dim_reducing_sumcheck_plan.rs");

    let mut pass_count = 0usize;
    for folding_steps in 4usize..=23 {
        let window_count = continuation_window_count(folding_steps);
        let entry_round = megakernel_entry_round(folding_steps);
        let passes = expected_d3_continuation_passes(folding_steps, window_count, entry_round);
        assert_eq!(passes.len(), window_count);
        assert_eq!(entry_round, 3 + 3 * passes.len());
        if passes.is_empty() {
            assert_eq!(entry_round, 3);
            continue;
        }

        for (pass_index, pass) in passes.iter().enumerate() {
            assert_eq!(pass.pass_index, pass_index);
            assert_eq!(pass.start_round, 3 + 3 * pass_index);
            assert_eq!(pass.challenge_offset, pass.start_round + 3);
            assert_eq!(pass.challenge_count, folding_steps - pass.start_round - 3,);
            assert_eq!(pass.entry_sizes, make_eq_sizes(pass.challenge_count));
            let mut boundary = pass.entry_sizes;
            crate::backward::kernels::record_active_eq_slot_fold(&mut boundary);
            assert_eq!(pass.one_fold_boundary_sizes, boundary);
            assert_ne!(
                pass.entry_sizes, pass.one_fold_boundary_sizes,
                "one-fold boundary mutation survived",
            );
            assert_eq!(pass.claim_point_offset, pass.start_round);
            assert_eq!(pass.coeffs_offset, 4 * pass.start_round);
            assert_eq!(
                pass.source,
                if pass_index == 0 {
                    D3ContinuationSource::Raw
                } else {
                    D3ContinuationSource::Arena(passes[pass_index - 1].destination)
                },
            );
            assert_eq!(
                pass.destination,
                if pass_index % 2 == 0 {
                    D3Parity::Even
                } else {
                    D3Parity::Odd
                },
            );

            let prior_view_reuse = if pass_index == 0 {
                make_eq_sizes(folding_steps - 3)
            } else {
                passes[pass_index - 1].one_fold_boundary_sizes
            };
            assert_ne!(
                prior_view_reuse, pass.entry_sizes,
                "prior-view reuse mutation survived at f={folding_steps}, r={}",
                pass.start_round,
            );
            let cumulative_drain = {
                let mut sizes = make_eq_sizes(folding_steps - 3);
                for _ in 0..=pass_index {
                    crate::backward::kernels::record_active_eq_slot_fold(&mut sizes);
                }
                sizes
            };
            assert_ne!(
                cumulative_drain, pass.entry_sizes,
                "cumulative-drain mutation survived at f={folding_steps}, r={}",
                pass.start_round,
            );
            pass_count += 1;
        }
    }
    assert_eq!(pass_count, 50);

    let binding_contract = [
        "bind_dr_window_continuations",
        "launch_dr_window_continuation",
        "resolve_dr_global_active_eq_slot",
    ];
    let plan_contract = [
        "launch_window_tensor_round_tail",
        "claim_point.add(start_round)",
        "coeffs.add(4 * start_round)",
    ];
    let missing = binding_contract
        .into_iter()
        .filter(|needle| !BINDING.contains(needle))
        .chain(
            plan_contract
                .into_iter()
                .filter(|needle| !SUMCHECK_PLAN.contains(needle)),
        )
        .collect::<Vec<_>>();
    assert!(
        missing.is_empty(),
        "RED D3 closed continuation chain is absent: {missing:?}",
    );
}

mod d1_cpu_oracles {
    use prover::gkr::prover::dimension_reduction::lsb_backward::{
        lsb_dim_reducing_sumcheck_prove, LsbDimReducingRelation,
    };

    use super::*;
    use crate::backward::kernels::record_active_eq_slot_fold;
    use crate::backward::window::reference::tensor_round_tail_reference;
    use crate::backward::window_dr::reference::{
        dr_continuation_eq_reference, dr_continuation_geometry_reference,
        dr_continuation_tensor_reference, dr_final_lookup_four_cells, fold_dr_continuation_depth3,
        DrTensorOracleProgram,
    };
    use crate::upstream::{BabyBearField, Field};

    const OUTPUT_TYPES: [OutputType; 5] = [
        OutputType::PermutationProduct,
        OutputType::Lookup16Bits,
        OutputType::LookupTimestamps,
        OutputType::GenericLookup,
        OutputType::InitsAndTeardownsProduct,
    ];

    fn add(mut left: E4, right: E4) -> E4 {
        left.add_assign(&right);
        left
    }

    fn mul(mut left: E4, right: E4) -> E4 {
        left.mul_assign(&right);
        left
    }

    fn field_sequence(len: usize, offset: usize) -> Vec<E4> {
        let mut value = E4::ONE;
        for _ in 0..offset {
            value.add_assign(&E4::ONE);
        }
        (0..len)
            .map(|_| {
                let current = value;
                value.add_assign(&E4::ONE);
                current
            })
            .collect()
    }

    #[test]
    fn cpu_dr_window_continuation_geometry_uses_log_suffix() {
        let mut checked = 0usize;
        for folding_steps in 4usize..=23 {
            for start_round in (3..folding_steps).step_by(3) {
                if start_round + 3 >= folding_steps {
                    continue;
                }
                let suffix_log = folding_steps - start_round;
                let geometry =
                    dr_continuation_geometry_reference(folding_steps, start_round).unwrap();
                let high_rows = 1usize << (suffix_log - 3);
                let row_tiles = high_rows.div_ceil(32).max(1);
                assert_eq!(
                    geometry.published_values_per_source,
                    1usize << (folding_steps + 1 - start_round)
                );
                assert_eq!(geometry.high_rows, high_rows);
                assert_eq!(geometry.row_tiles, row_tiles);
                assert_eq!(geometry.partials_len, 27 * (row_tiles + 1));
                assert_eq!(dr_window_row_tiles(suffix_log), row_tiles);
                assert_eq!(dr_window_partials_len(suffix_log), geometry.partials_len);

                let count_as_log = 1usize << suffix_log;
                let mutation = std::panic::catch_unwind(|| {
                    (
                        dr_window_row_tiles(count_as_log),
                        dr_window_partials_len(count_as_log),
                    )
                });
                assert!(
                    mutation.is_err()
                        || mutation.unwrap() != (geometry.row_tiles, geometry.partials_len),
                    "count-as-log mutation survived for f={folding_steps}, r={start_round}",
                );
                checked += 1;
            }
        }
        assert_eq!(checked, 57);
    }

    fn record_fixture() -> (
        gpu_gkr_compiler::DrWindowProgram,
        gpu_gkr_compiler::DrWindowInputProjection,
    ) {
        let canonical_0 = address(10);
        let canonical_1 = address(20);
        let alias_0 = address(30);
        let rows = BTreeMap::from([
            (
                OutputType::PermutationProduct,
                DrWindowInputOutput::new([alias_0, canonical_1], [address(40), address(41)]),
            ),
            (
                OutputType::GenericLookup,
                DrWindowInputOutput::new([canonical_0, canonical_1], [address(42), address(43)]),
            ),
        ]);
        let program = lower_dr_window_program(&rows).unwrap();
        let projection =
            project_dr_window_inputs(&program, &BTreeMap::from([(alias_0, canonical_0)]));
        (program, projection)
    }

    fn first_access_pattern<Key: Ord>(keys: impl IntoIterator<Item = Key>) -> Vec<bool> {
        let mut seen = BTreeSet::new();
        keys.into_iter().map(|key| seen.insert(key)).collect()
    }

    fn synthetic_storage_poly(address: GKRAddress) -> usize {
        match address {
            value if value == super::address(30) => 17,
            value if value == super::address(20) => 3,
            value if value == super::address(10) => 5,
            _ => unreachable!("record fixture contains only three raw input addresses"),
        }
    }

    #[test]
    fn cpu_dr_window_continuation_records_match_builder_first_access() {
        let (program, projection) = record_fixture();
        assert_eq!(projection.canonical_sources(), &[address(10), address(20)]);
        assert_eq!(projection.occurrences().len(), 4);
        assert_eq!(projection.occurrences()[0].publication_index(), 0);
        assert_eq!(projection.occurrences()[2].publication_index(), 0);

        let raw_backing = FoldingArenaBinding::new(0x10_000usize as *const u8, 8);
        let destination = FoldingArenaBinding::new(0x20_000usize as *const u8, 6);
        let eq = DrContinuationFactoredEqView::new(
            0x30_000usize as *mut E4,
            0x31_000usize as *mut E4,
            0x32_000usize as *mut E4,
            make_eq_sizes(5),
            9,
            5,
        );

        let assemble = || {
            assemble_dr_window_continuation_batch(
                &program,
                &projection,
                eq,
                destination,
                |builder, address, publication_index| {
                    let storage_poly = synthetic_storage_poly(address);
                    assert_ne!(storage_poly, usize::from(publication_index));
                    builder.intern_arena_e4(raw_backing, storage_poly)
                },
            )
            .unwrap()
        };

        let first_launch = assemble();
        let second_launch = assemble();
        assert_eq!(first_launch.enabled_mask, program.enabled_mask());
        assert_eq!(first_launch.eq_low, eq.low.cast_const());
        assert_eq!(first_launch.eq_sizes, eq.sizes);
        assert!(first_launch.contributions.is_null());

        let mut occurrences = Vec::new();
        for (dense_slot, slot) in program.slots().iter().enumerate() {
            let record_slot = first_launch.slots[slot.slot()];
            let reset_slot = second_launch.slots[slot.slot()];
            assert_eq!(record_slot.batch_exp, *slot.batch_exponents());
            assert_eq!(record_slot.io[2], Default::default());
            assert_eq!(record_slot.io[3], Default::default());
            for input_operand in 0..2 {
                let publication_index = projection
                    .publication_index(dense_slot, input_operand)
                    .unwrap();
                let source_id = slot.source_ids()[input_operand];
                let address = program.sources()[usize::from(source_id)];
                let record = record_slot.io[input_operand];
                let reset = reset_slot.io[input_operand];
                assert_eq!(record, reset, "first-access state must reset per launch");
                let builder_base = pack_source_u16(
                    false,
                    0,
                    u16::try_from(synthetic_storage_poly(address)).unwrap(),
                );
                assert_eq!(record.src & 0x7fff, builder_base);
                assert_eq!(record.cache & 0x8000, 0);
                assert_eq!(record.cache, pack_cache_u16(1, publication_index));
                occurrences.push((
                    publication_index,
                    address,
                    builder_base,
                    (record.src & 0x8000) != 0,
                ));
            }
        }
        let correct = occurrences
            .iter()
            .map(|(_, _, _, first)| *first)
            .collect::<Vec<_>>();
        assert_eq!(correct, vec![true, true, false, false]);
        assert_eq!(
            correct,
            first_access_pattern(
                occurrences
                    .iter()
                    .map(|(publication, _, _, _)| *publication)
            ),
        );
        assert_eq!(
            occurrences
                .iter()
                .filter(|(publication, _, _, first)| *publication == 0 && *first)
                .count(),
            1,
        );
        assert_eq!(
            occurrences
                .iter()
                .filter(|(publication, _, _, first)| *publication == 1 && *first)
                .count(),
            1,
        );
        assert_eq!(first_launch.tables.bases[0], raw_backing.base);
        assert_eq!(first_launch.tables.bases[1], destination.base);

        // Two canonical publications intentionally share one source backing,
        // while the raw alias and canonical address share publication zero.
        assert_eq!(
            first_launch
                .tables
                .bases
                .iter()
                .filter(|base| **base == raw_backing.base)
                .count(),
            1,
        );

        // Each forbidden ownership key changes the observable publication
        // pattern. In particular, publication zero's alias/canonical records
        // intentionally resolve to different raw poly bases (17 and 5), while
        // publication one uses poly 3 on the same backing.
        let poly_key = first_access_pattern(
            occurrences
                .iter()
                .map(|(_, _, base, _)| base & ((1 << 11) - 1)),
        );
        let slot_key = first_access_pattern(
            occurrences
                .iter()
                .map(|(_, _, base, _)| (base >> 11) & 0x0f),
        );
        let raw_address_key =
            first_access_pattern(occurrences.iter().map(|(_, address, _, _)| *address));
        assert_ne!(poly_key, correct, "poly-index ownership mutation survived");
        assert_ne!(
            slot_key, correct,
            "backing/slot ownership mutation survived"
        );
        assert_ne!(
            raw_address_key, correct,
            "raw-address ownership mutation survived"
        );

        let missing_first = vec![false; occurrences.len()];
        let repeated_later = vec![true; occurrences.len()];
        assert_ne!(missing_first, correct);
        assert_ne!(repeated_later, correct);

        let retained_seen = occurrences
            .iter()
            .map(|(publication, _, _, _)| *publication)
            .collect::<BTreeSet<_>>();
        let cross_launch = occurrences
            .iter()
            .scan(retained_seen, |seen, (publication, _, _, _)| {
                Some(seen.insert(*publication))
            })
            .collect::<Vec<_>>();
        assert_ne!(
            cross_launch, correct,
            "cross-launch state mutation survived"
        );

        let repacked = occurrences
            .iter()
            .map(|(publication, _, _, _)| pack_source_u16(false, 0, *publication))
            .collect::<Vec<_>>();
        let builder_bases = occurrences
            .iter()
            .map(|(_, _, base, _)| *base)
            .collect::<Vec<_>>();
        assert_ne!(
            repacked, builder_bases,
            "slot/poly repack mutation survived"
        );

        let prior_arena = FoldingArenaBinding::new(0x40_000usize as *const u8, 7);
        let arena_launch = assemble_dr_window_continuation_batch(
            &program,
            &projection,
            eq,
            destination,
            |builder, _, publication_index| {
                builder.intern_arena_e4(prior_arena, usize::from(publication_index))
            },
        )
        .unwrap();
        for (dense_slot, slot) in program.slots().iter().enumerate() {
            for input_operand in 0..2 {
                let publication_index = projection
                    .publication_index(dense_slot, input_operand)
                    .unwrap();
                let record = arena_launch.slots[slot.slot()].io[input_operand];
                assert_eq!(
                    record.src & 0x7fff,
                    pack_source_u16(false, 0, publication_index),
                );
                assert_eq!(record.cache, pack_cache_u16(1, publication_index));
            }
        }
        assert_eq!(arena_launch.tables.bases[0], prior_arena.base);
        assert_eq!(arena_launch.tables.bases[1], destination.base);

        // The actual Storage/Arena wrapper requires pool-backed
        // DeviceAllocation owners and therefore is not constructed in this
        // GPU-free test. This pure assembler seam exercises both storage-like
        // raw poly mapping and exact source/destination arena mapping.
    }

    fn dense_fold_once(source: &[E4], challenge: E4) -> Vec<E4> {
        assert_eq!(source.len() % 4, 0);
        let mut folded = Vec::with_capacity(source.len() / 2);
        for y in 0..source.len() / 4 {
            for gate_bit in 0..2 {
                let low = source[4 * y + gate_bit];
                let high = source[4 * y + 2 + gate_bit];
                let mut value = high;
                value.sub_assign(&low);
                value.mul_assign(&challenge);
                value.add_assign(&low);
                folded.push(value);
            }
        }
        folded
    }

    #[test]
    fn cpu_dr_window_continuation_fold_matches_three_dense_folds() {
        // Output-pair counts cover a minimal alias fixture, one full 32-row
        // tile (256 pairs), multiple tiles, and a synthetic partial tile.
        let geometry_classes = [1usize, 256, 640, 37];
        for (geometry_class, output_pairs) in geometry_classes.into_iter().enumerate() {
            for state in 0..32usize {
                let source = field_sequence(16 * output_pairs, 97 * geometry_class + 13 * state);
                let challenges: [E4; 3] = field_sequence(3, 7 * state + geometry_class)
                    .try_into()
                    .unwrap();
                let expected = challenges
                    .into_iter()
                    .fold(source.clone(), |values, challenge| {
                        dense_fold_once(&values, challenge)
                    });
                let observed = fold_dr_continuation_depth3(&source, challenges).unwrap();
                assert_eq!(observed, expected, "class={geometry_class}, state={state}");
                assert_eq!(observed.len(), 2 * output_pairs);

                if geometry_class == 0 {
                    let aliases = [source.as_slice(), source.as_slice()];
                    assert!(core::ptr::eq(aliases[0].as_ptr(), aliases[1].as_ptr()));
                    assert_eq!(
                        fold_dr_continuation_depth3(aliases[0], challenges).unwrap(),
                        fold_dr_continuation_depth3(aliases[1], challenges).unwrap(),
                    );
                }
            }
        }
    }

    fn tensor_fixture(
        mask: u32,
        suffix_bits: usize,
    ) -> (DrTensorOracleProgram, BTreeMap<GKRAddress, Vec<E4>>) {
        let mut rows = BTreeMap::new();
        let mut columns = BTreeMap::new();
        let column_len = 16usize << suffix_bits;
        for (slot, output_type) in OUTPUT_TYPES.into_iter().enumerate() {
            if mask & (1 << slot) == 0 {
                continue;
            }
            let inputs = [address(100 + 4 * slot), address(101 + 4 * slot)];
            let outputs = [address(102 + 4 * slot), address(103 + 4 * slot)];
            rows.insert(output_type, DrWindowInputOutput::new(inputs, outputs));
            for (operand, input) in inputs.into_iter().enumerate() {
                columns.insert(
                    input,
                    field_sequence(column_len, 31 * slot + 11 * operand + 7 * suffix_bits),
                );
            }
        }
        let program = lower_dr_window_program(&rows).unwrap();
        (DrTensorOracleProgram::from_production(&program), columns)
    }

    fn selector_weight(selector: usize, bit: usize) -> E4 {
        match (selector, bit) {
            (0, 0) | (1, 1) | (2, 1) => E4::ONE,
            (0, 1) | (1, 0) => E4::ZERO,
            (2, 0) => {
                let mut minus_one = E4::ZERO;
                minus_one.sub_assign(&E4::ONE);
                minus_one
            }
            _ => unreachable!(),
        }
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

    fn eq_coordinate_weight(left: E4, right: E4) -> E4 {
        let mut one_minus_left = E4::ONE;
        one_minus_left.sub_assign(&left);
        let mut one_minus_right = E4::ONE;
        one_minus_right.sub_assign(&right);
        one_minus_left.mul_assign(&one_minus_right);
        let mut both_one = left;
        both_one.mul_assign(&right);
        one_minus_left.add_assign(&both_one);
        one_minus_left
    }

    fn upstream_batch_power(base: E4, exponent: u16) -> E4 {
        (0..exponent).fold(E4::ONE, |mut power, _| {
            power.mul_assign(&base);
            power
        })
    }

    fn upstream_extension_cell(
        column: &[E4],
        suffix_row: usize,
        selectors: [usize; 3],
        gate_bit: usize,
    ) -> E4 {
        let mut total = E4::ZERO;
        for boolean_y in 0..8usize {
            let mut weight = E4::ONE;
            for axis in 0..3 {
                weight.mul_assign(&selector_weight(selectors[axis], (boolean_y >> axis) & 1));
            }
            let mut value = column[2 * ((suffix_row << 3) | boolean_y) + gate_bit];
            value.mul_assign(&weight);
            total.add_assign(&value);
        }
        total
    }

    fn upstream_continuation_tensor(
        program: &DrTensorOracleProgram,
        columns: &BTreeMap<GKRAddress, Vec<E4>>,
        batch_base: E4,
        suffix_point: &[E4],
    ) -> [E4; 27] {
        core::array::from_fn(|cell| {
            let selectors = [cell / 9, (cell / 3) % 3, cell % 3];
            let mut total = E4::ZERO;
            for suffix_row in 0..(1usize << suffix_point.len()) {
                let mut row_value = E4::ZERO;
                for slot in &program.slots {
                    let inputs = slot.source_ids[..2]
                        .iter()
                        .map(|source_id| &columns[&program.sources[usize::from(*source_id)]])
                        .collect::<Vec<_>>();
                    let values = inputs
                        .iter()
                        .map(|column| {
                            [
                                upstream_extension_cell(column, suffix_row, selectors, 0),
                                upstream_extension_cell(column, suffix_row, selectors, 1),
                            ]
                        })
                        .collect::<Vec<_>>();
                    let weights = slot
                        .batch_exponents
                        .map(|exponent| upstream_batch_power(batch_base, exponent));
                    if slot.slot == 0 || slot.slot == 4 {
                        for tower in 0..2 {
                            row_value.add_assign(&mul(
                                weights[tower],
                                mul(values[tower][0], values[tower][1]),
                            ));
                        }
                    } else {
                        row_value.add_assign(&mul(
                            weights[0],
                            add(
                                mul(values[0][0], values[1][1]),
                                mul(values[0][1], values[1][0]),
                            ),
                        ));
                        row_value.add_assign(&mul(weights[1], mul(values[1][0], values[1][1])));
                    }
                }
                let mut suffix_weight = E4::ONE;
                for (bit, coordinate) in suffix_point.iter().copied().enumerate() {
                    suffix_weight.mul_assign(&eq_weight((suffix_row >> bit) & 1, coordinate));
                }
                row_value.mul_assign(&suffix_weight);
                total.add_assign(&row_value);
            }
            total
        })
    }

    fn continuation_gate_at_boolean(
        program: &DrTensorOracleProgram,
        columns: &BTreeMap<GKRAddress, Vec<E4>>,
        batch_base: E4,
        y: usize,
    ) -> E4 {
        let mut total = E4::ZERO;
        for slot in &program.slots {
            let addresses = slot
                .source_ids
                .map(|source_id| program.sources[usize::from(source_id)]);
            let weights = slot
                .batch_exponents
                .map(|exponent| upstream_batch_power(batch_base, exponent));
            if slot.slot == 0 || slot.slot == 4 {
                for tower in 0..2 {
                    total.add_assign(&mul(
                        weights[tower],
                        mul(
                            columns[&addresses[tower]][2 * y],
                            columns[&addresses[tower]][2 * y + 1],
                        ),
                    ));
                }
            } else {
                let numerator = &columns[&addresses[0]];
                let denominator = &columns[&addresses[1]];
                total.add_assign(&mul(
                    weights[0],
                    add(
                        mul(numerator[2 * y], denominator[2 * y + 1]),
                        mul(numerator[2 * y + 1], denominator[2 * y]),
                    ),
                ));
                total.add_assign(&mul(
                    weights[1],
                    mul(denominator[2 * y], denominator[2 * y + 1]),
                ));
            }
        }
        total
    }

    fn continuation_initial_claim(
        program: &DrTensorOracleProgram,
        columns: &BTreeMap<GKRAddress, Vec<E4>>,
        batch_base: E4,
        tau: &[E4],
    ) -> E4 {
        (0..(1usize << tau.len())).fold(E4::ZERO, |mut claim, y| {
            let mut weight = E4::ONE;
            for (bit, coordinate) in tau.iter().copied().enumerate() {
                weight.mul_assign(&eq_weight((y >> bit) & 1, coordinate));
            }
            let mut value = continuation_gate_at_boolean(program, columns, batch_base, y);
            value.mul_assign(&weight);
            claim.add_assign(&value);
            claim
        })
    }

    fn continuation_relations(
        program: &DrTensorOracleProgram,
        batch_base: E4,
    ) -> Vec<LsbDimReducingRelation<E4>> {
        let mut relations = Vec::new();
        for slot in &program.slots {
            let addresses = slot
                .source_ids
                .map(|source_id| program.sources[usize::from(source_id)]);
            let weights = slot
                .batch_exponents
                .map(|exponent| upstream_batch_power(batch_base, exponent));
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

    fn final_gate_from_upstream_values(
        program: &DrTensorOracleProgram,
        batch_base: E4,
        values: &BTreeMap<GKRAddress, [E4; 2]>,
    ) -> E4 {
        let columns = values
            .iter()
            .map(|(address, pair)| (*address, pair.to_vec()))
            .collect::<BTreeMap<_, _>>();
        continuation_gate_at_boolean(program, &columns, batch_base, 0)
    }

    #[test]
    fn cpu_dr_window_continuation_tensor_matches_legacy() {
        let masks = [0x01u32, 0x0d, 0x0f, 0x1f, 0x02];
        let worker = worker::Worker::new_with_num_threads(2);
        for mask in masks {
            for suffix_bits in [0usize, 1] {
                let (program, columns) = tensor_fixture(mask, suffix_bits);
                assert_eq!(program.enabled_mask, mask);
                let batch_base = field_sequence(1, 200 + usize::try_from(mask).unwrap())[0];
                assert_ne!(batch_base, E4::ZERO);
                assert_ne!(batch_base, E4::ONE);
                let tau = field_sequence(3 + suffix_bits, 300 + usize::try_from(mask).unwrap());
                let expected =
                    upstream_continuation_tensor(&program, &columns, batch_base, &tau[3..]);
                let observed =
                    dr_continuation_tensor_reference(&program, &columns, batch_base, &tau[3..])
                        .unwrap();
                assert_eq!(observed, expected, "mask={mask:#04x}, suffix={suffix_bits}");

                let initial_claim =
                    continuation_initial_claim(&program, &columns, batch_base, &tau);
                let mut seed = [0x1234_5678u32.wrapping_add(mask); 8];
                let mut tail_claim = initial_claim;
                let mut tail_eq = E4::ONE;
                let rho: [E4; 3] = tau[..3].try_into().unwrap();
                let (tail_coefficients, tail_challenges) = tensor_round_tail_reference(
                    expected,
                    &rho,
                    &mut seed,
                    &mut tail_claim,
                    &mut tail_eq,
                );
                let mut challenges = tail_challenges.to_vec();
                challenges.extend(field_sequence(
                    suffix_bits,
                    500 + usize::try_from(mask).unwrap(),
                ));
                assert_eq!(&challenges[..3], tail_challenges.as_slice());

                let input_polys = program
                    .slots
                    .iter()
                    .flat_map(|slot| slot.source_ids[..2].iter().copied())
                    .map(|source_id| {
                        let address = program.sources[usize::from(source_id)];
                        (address, columns[&address].as_slice())
                    })
                    .collect::<BTreeMap<_, _>>();
                let upstream = lsb_dim_reducing_sumcheck_prove::<BabyBearField, E4>(
                    &input_polys,
                    &continuation_relations(&program, batch_base),
                    &tau,
                    initial_claim,
                    &challenges,
                    &worker,
                );
                for (address, column) in &columns {
                    let folded = challenges
                        .iter()
                        .copied()
                        .fold(column.clone(), |values, challenge| {
                            dense_fold_once(&values, challenge)
                        });
                    assert_eq!(
                        upstream.final_values[address],
                        <[E4; 2]>::try_from(folded).unwrap(),
                        "upstream consumed every supplied challenge for {address:?}",
                    );
                }
                let upstream_first_three = upstream
                    .round_coefficients
                    .iter()
                    .take(3)
                    .flatten()
                    .copied()
                    .collect::<Vec<_>>();
                assert_eq!(
                    tail_coefficients.as_slice(),
                    upstream_first_three.as_slice(),
                    "upstream cubic messages mask={mask:#04x}, suffix={suffix_bits}",
                );
                assert_eq!(
                    tail_eq,
                    eq_coordinate_weight(tau[2], tail_challenges[2]),
                    "three-round Eq factor mask={mask:#04x}, suffix={suffix_bits}",
                );
                if suffix_bits == 0 {
                    assert_eq!(tail_claim, upstream.final_claim);
                    assert_eq!(tail_eq, upstream.eq_factor);
                }
                let expected_final_eq =
                    eq_coordinate_weight(*tau.last().unwrap(), *challenges.last().unwrap());
                let mut expected_final_claim =
                    final_gate_from_upstream_values(&program, batch_base, &upstream.final_values);
                expected_final_claim.mul_assign(&expected_final_eq);
                assert_eq!(upstream.eq_factor, expected_final_eq);
                assert_eq!(upstream.final_claim, expected_final_claim);

                let mut exponent_mutation = program.clone();
                exponent_mutation.slots[0].batch_exponents[0] += 1;
                let exponent_tensor = dr_continuation_tensor_reference(
                    &exponent_mutation,
                    &columns,
                    batch_base,
                    &tau[3..],
                )
                .unwrap();
                assert_ne!(
                    exponent_tensor, expected,
                    "batch-exponent mutation survived"
                );

                if suffix_bits > 0 {
                    let mut suffix_mutation = tau[3..].to_vec();
                    suffix_mutation[0].add_assign(&E4::ONE);
                    let suffix_tensor = dr_continuation_tensor_reference(
                        &program,
                        &columns,
                        batch_base,
                        &suffix_mutation,
                    )
                    .unwrap();
                    assert_ne!(
                        suffix_tensor, expected,
                        "suffix contraction mutation survived"
                    );
                }
            }
        }

        for mask in [0x01u32, 0x02] {
            let (program, columns) = tensor_fixture(mask, 1);
            let batch_base = field_sequence(1, 700 + usize::try_from(mask).unwrap())[0];
            let suffix = field_sequence(1, 800 + usize::try_from(mask).unwrap());
            let full =
                dr_continuation_tensor_reference(&program, &columns, batch_base, &suffix).unwrap();
            assert_ne!(
                full[0],
                E4::ZERO,
                "Boolean mutation control must be nonzero"
            );
            let mut r0_product_excess = full;
            for a0 in 0..2 {
                for a1 in 0..2 {
                    for a2 in 0..2 {
                        r0_product_excess[9 * a0 + 3 * a1 + a2] = E4::ZERO;
                    }
                }
            }
            assert_ne!(r0_product_excess, full, "mask={mask:#04x}");
        }
    }

    #[test]
    fn cpu_dr_window_continuation_eq_views_are_pass_local() {
        let high_0 = 0x40_000usize as *mut E4;
        let high_1 = 0x50_000usize as *mut E4;
        let low = 0x60_000usize as *mut E4;
        let mut checked = 0usize;
        for folding_steps in 4usize..=23 {
            let tau = field_sequence(folding_steps, 5 * folding_steps);
            let mut prior = None;
            for start_round in (3..folding_steps).step_by(3) {
                if start_round + 3 >= folding_steps {
                    continue;
                }
                let expected =
                    dr_continuation_eq_reference(&tau, folding_steps, start_round).unwrap();
                assert_eq!(expected.challenge_offset, start_round + 3);
                assert_eq!(expected.challenge_count, folding_steps - start_round - 3);
                assert_eq!(expected.suffix, tau[start_round + 3..folding_steps],);
                assert_eq!(
                    expected.entry_sizes,
                    make_eq_sizes(expected.challenge_count)
                );
                let mut once_folded = expected.entry_sizes;
                record_active_eq_slot_fold(&mut once_folded);
                assert_eq!(expected.one_fold_boundary_sizes, once_folded);

                let view = DrContinuationFactoredEqView::for_pass(
                    high_0,
                    high_1,
                    low,
                    folding_steps,
                    start_round,
                )
                .unwrap();
                assert_eq!(view.sizes, expected.entry_sizes);
                assert_eq!(view.challenge_offset, expected.challenge_offset as u32);
                assert_eq!(view.challenge_count, expected.challenge_count as u32);
                let (active, size) = resolve_dr_global_active_eq_slot(&view);
                let (expected_active, expected_size) = if view.sizes.low > 0 {
                    (low, view.sizes.low)
                } else if view.sizes.high[1] > 0 {
                    (high_1, view.sizes.high[1])
                } else {
                    (high_0, view.sizes.high[0])
                };
                assert_eq!((active, size), (expected_active, expected_size));

                if let Some(prior) = &prior {
                    assert_ne!(prior, &expected, "prior Eq view was reused");
                }
                prior = Some(expected.clone());

                let pass_index = (start_round - 3) / 3;
                let mut cumulative = make_eq_sizes(folding_steps - 3);
                for _ in 0..=pass_index {
                    record_active_eq_slot_fold(&mut cumulative);
                }
                assert_ne!(
                    cumulative, expected.entry_sizes,
                    "cumulative drain survived"
                );
                assert_ne!(
                    start_round + 1,
                    expected.challenge_offset,
                    "r+1 mutation survived"
                );
                assert_ne!(
                    start_round + 4,
                    expected.challenge_offset,
                    "r+4 mutation survived"
                );
                assert_ne!(
                    &tau[start_round + 1..folding_steps],
                    expected.suffix.as_slice(),
                    "r+1 suffix mutation survived",
                );
                assert_ne!(
                    &tau[start_round + 4..folding_steps],
                    expected.suffix.as_slice(),
                    "r+4 suffix mutation survived",
                );
                checked += 1;
            }
        }
        assert_eq!(checked, 57);

        let mut priority_sizes = make_eq_sizes(17);
        let priority_view =
            DrContinuationFactoredEqView::new(high_0, high_1, low, priority_sizes, 6, 17);
        assert_eq!(resolve_dr_global_active_eq_slot(&priority_view).0, low);
        priority_sizes.low = 0;
        let priority_view =
            DrContinuationFactoredEqView::new(high_0, high_1, low, priority_sizes, 6, 17);
        assert_eq!(resolve_dr_global_active_eq_slot(&priority_view).0, high_1);
        priority_sizes.high[1] = 0;
        let priority_view =
            DrContinuationFactoredEqView::new(high_0, high_1, low, priority_sizes, 6, 17);
        assert_eq!(resolve_dr_global_active_eq_slot(&priority_view).0, high_0);
    }

    #[test]
    fn cpu_dr_window_final_order_mismatch_seam_matches_legacy() {
        let mut checked_layers = 0usize;
        let mut mismatch_layers = 0usize;
        let mut merge_layers = 0usize;
        let mut two_cell_mutations = 0usize;
        let mut four_cell_mutations = 0usize;
        for (layout_name, _) in CONTINUATION_GOLDEN_CORPUS {
            let (programs, main_layers) = crate::backward::compile_corpus_layout(layout_name);
            let runtime = programs.runtime_circuit();
            let initial_trace_log = runtime.trace_len.trailing_zeros();
            let legacy_layers = derive_dimension_reducing_inputs(
                main_layers,
                &runtime.global_output_map,
                initial_trace_log,
                CORPUS_FINAL_TRACE_LOG,
            );
            let layout = GpuGKRStorageLayout::from_artifact_with_tower(
                runtime,
                CORPUS_FINAL_TRACE_LOG as usize,
            );
            let bundle = programs
                .resolve_dr_window_programs(CORPUS_FINAL_TRACE_LOG)
                .unwrap();
            for (absolute_layer, legacy_description) in legacy_layers {
                let legacy_slots = legacy_dimension_reducing_slots_for_test(&legacy_description);
                let layer = bundle.layer(absolute_layer).unwrap();
                let canonical = layer.input_projection().canonical_sources();
                let raw = legacy_slots.input_addresses().collect::<Vec<_>>();
                let canonical_cells = field_sequence(4 * canonical.len(), checked_layers * 47);
                let lookup =
                    dr_final_lookup_four_cells(canonical, &raw, &layout.aliases, &canonical_cells)
                        .unwrap();
                let raw_sorted = raw
                    .into_iter()
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect::<Vec<_>>();
                let expected_indices = raw_sorted
                    .iter()
                    .map(|address| {
                        let canonical_address =
                            layout.aliases.get(address).copied().unwrap_or(*address);
                        canonical.binary_search(&canonical_address).unwrap()
                    })
                    .collect::<Vec<_>>();
                let expected_cells = expected_indices
                    .iter()
                    .flat_map(|index| canonical_cells[4 * index..4 * index + 4].iter().copied())
                    .collect::<Vec<_>>();
                assert_eq!(lookup.publication_indices, expected_indices);
                assert_eq!(lookup.cells, expected_cells);

                mismatch_layers += usize::from(
                    lookup.publication_indices != (0..canonical.len()).collect::<Vec<_>>(),
                );
                merge_layers += usize::from(raw_sorted.len() != canonical.len());
                if lookup.publication_indices != (0..canonical.len()).collect::<Vec<_>>() {
                    assert_ne!(
                        lookup.cells, canonical_cells,
                        "canonical-order mutation survived"
                    );
                }

                let two_cells = field_sequence(2 * canonical.len(), checked_layers * 53);
                assert!(dr_final_lookup_four_cells(
                    canonical,
                    &raw_sorted,
                    &layout.aliases,
                    &two_cells,
                )
                .is_err());
                two_cell_mutations += 1;

                let mut permuted_four_cells = canonical_cells.clone();
                for cells in permuted_four_cells.chunks_exact_mut(4) {
                    cells.swap(1, 2);
                }
                let permuted = dr_final_lookup_four_cells(
                    canonical,
                    &raw_sorted,
                    &layout.aliases,
                    &permuted_four_cells,
                )
                .unwrap();
                assert_ne!(permuted.cells, lookup.cells);
                four_cell_mutations += 1;
                checked_layers += 1;
            }
        }
        assert_eq!(checked_layers, 229);
        assert_eq!(mismatch_layers, 9);
        assert_eq!(merge_layers, 0);
        assert_eq!(two_cell_mutations, 229);
        assert_eq!(four_cell_mutations, 229);
    }
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
