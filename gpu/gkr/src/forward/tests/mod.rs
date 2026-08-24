use super::*;
use helpers::*;

use super::dimension_reducing::{
    prepare_dimension_reduction_forward, schedule_prepared_dimension_reduction_forward,
    LoweredSlotOutput,
};
use super::vm::desc::FUSED_REDUCTION_ROUNDS;
use super::vm::lower::LoweredFwdVm;
use super::vm::production_bind::schedule_vm;
use crate::setup::schedule_forward_setup_for_shape;
use crate::test_utils::make_test_context;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::field::E4;

#[test]
fn dimension_reducing_forward_tower_matches_reference() {
    let context = make_test_context(1024, 32);
    let initial_trace_log_2 = 11u32;
    let final_trace_log_2 = 0u32;
    let initial_trace_len = 1usize << initial_trace_log_2;
    let current_layer_idx = 3usize;

    let read_set = GKRAddress::InnerLayer {
        layer: current_layer_idx,
        offset: 0,
    };
    let write_set = GKRAddress::InnerLayer {
        layer: current_layer_idx,
        offset: 1,
    };
    let lookup16_num = GKRAddress::InnerLayer {
        layer: current_layer_idx,
        offset: 2,
    };
    let lookup16_den = GKRAddress::InnerLayer {
        layer: current_layer_idx,
        offset: 3,
    };
    let timestamp_num = GKRAddress::InnerLayer {
        layer: current_layer_idx,
        offset: 4,
    };
    let timestamp_den = GKRAddress::InnerLayer {
        layer: current_layer_idx,
        offset: 5,
    };
    let generic_num = GKRAddress::InnerLayer {
        layer: current_layer_idx,
        offset: 6,
    };
    let generic_den = GKRAddress::InnerLayer {
        layer: current_layer_idx,
        offset: 7,
    };

    let read_values = (0..initial_trace_len)
        .map(|idx| sample_ext(100 + idx as u32))
        .collect::<Vec<_>>();
    let write_values = (0..initial_trace_len)
        .map(|idx| sample_ext(200 + idx as u32))
        .collect::<Vec<_>>();
    let lookup16_num_values = (0..initial_trace_len)
        .map(|idx| sample_ext(300 + idx as u32))
        .collect::<Vec<_>>();
    let lookup16_den_values = (0..initial_trace_len)
        .map(|idx| sample_ext(400 + idx as u32))
        .collect::<Vec<_>>();
    let timestamp_num_values = (0..initial_trace_len)
        .map(|idx| sample_ext(500 + idx as u32))
        .collect::<Vec<_>>();
    let timestamp_den_values = (0..initial_trace_len)
        .map(|idx| sample_ext(600 + idx as u32))
        .collect::<Vec<_>>();
    let generic_num_values = (0..initial_trace_len)
        .map(|idx| sample_ext(700 + idx as u32))
        .collect::<Vec<_>>();
    let generic_den_values = (0..initial_trace_len)
        .map(|idx| sample_ext(800 + idx as u32))
        .collect::<Vec<_>>();

    let mut storage = GpuGKRStorage::<BF, E4>::default();
    for (address, values) in [
        (read_set, &read_values),
        (write_set, &write_values),
        (lookup16_num, &lookup16_num_values),
        (lookup16_den, &lookup16_den_values),
        (timestamp_num, &timestamp_num_values),
        (timestamp_den, &timestamp_den_values),
        (generic_num, &generic_num_values),
        (generic_den, &generic_den_values),
    ] {
        storage.insert_extension_at_layer(
            current_layer_idx,
            address,
            upload_ext_poly(values, &context),
        );
    }

    let initial_output_map = BTreeMap::from([
        (OutputType::PermutationProduct, vec![read_set, write_set]),
        (OutputType::Lookup16Bits, vec![lookup16_num, lookup16_den]),
        (
            OutputType::LookupTimestamps,
            vec![timestamp_num, timestamp_den],
        ),
        (OutputType::GenericLookup, vec![generic_num, generic_den]),
    ]);

    attach_test_dim_reducing_tower_layout(
        &mut storage,
        current_layer_idx,
        &initial_output_map,
        initial_trace_log_2,
        final_trace_log_2,
    );

    let prepared = prepare_dimension_reduction_forward::<E4>(
        &mut storage,
        current_layer_idx,
        &initial_output_map,
        initial_trace_log_2,
        final_trace_log_2,
        None,
        &context,
    )
    .unwrap();
    schedule_prepared_dimension_reduction_forward(&prepared, 0, &context).unwrap();

    let stream = context.get_exec_stream();
    for (round_idx, outputs) in prepared.per_round_slot_outputs.iter().enumerate().skip(7) {
        let output_len = 1usize << (initial_trace_log_2 - round_idx as u32 - 1);
        for output in outputs {
            let pointers = match *output {
                LoweredSlotOutput::PairwiseProduct { output } => [output, std::ptr::null_mut()],
                LoweredSlotOutput::LookupPair {
                    output_num,
                    output_den,
                } => [output_num, output_den],
            };
            for pointer in pointers.into_iter().filter(|pointer| !pointer.is_null()) {
                let output = unsafe { DeviceSlice::from_raw_parts_mut(pointer, output_len) };
                era_cudart::memory::memory_set_async(
                    unsafe { output.transmute_mut::<u8>() },
                    0,
                    stream,
                )
                .unwrap();
            }
        }
    }
    schedule_prepared_dimension_reduction_forward(&prepared, 7, &context).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    let final_layer_idx = prepared.final_layer_idx;
    let dim_reducing_inputs = prepared.dimension_reduction_description;

    let total_rounds = initial_trace_log_2 - final_trace_log_2;
    assert_eq!(
        final_layer_idx,
        current_layer_idx + total_rounds as usize - 1
    );

    let mut expected_read = read_values.clone();
    let mut expected_write = write_values.clone();
    let mut expected_lookup16 = (lookup16_num_values.clone(), lookup16_den_values.clone());
    let mut expected_timestamp = (timestamp_num_values.clone(), timestamp_den_values.clone());
    let mut expected_generic = (generic_num_values.clone(), generic_den_values.clone());

    for round_idx in 0..total_rounds {
        expected_read = expected_pairwise_reduction(&expected_read);
        expected_write = expected_pairwise_reduction(&expected_write);
        expected_lookup16 =
            expected_lookup_pair_reduction(&expected_lookup16.0, &expected_lookup16.1);
        expected_timestamp =
            expected_lookup_pair_reduction(&expected_timestamp.0, &expected_timestamp.1);
        expected_generic = expected_lookup_pair_reduction(&expected_generic.0, &expected_generic.1);

        let layer_description = dim_reducing_inputs
            .get(&(current_layer_idx + round_idx as usize))
            .expect("dim reducing description present for round");

        let permutation_outputs = &layer_description[&OutputType::PermutationProduct].output;
        assert_eq!(
            read_ext_poly(storage.get_ext_poly(permutation_outputs[0]), &context),
            expected_read,
            "read chain mismatch at round {round_idx}"
        );
        assert_eq!(
            read_ext_poly(storage.get_ext_poly(permutation_outputs[1]), &context),
            expected_write,
            "write chain mismatch at round {round_idx}"
        );

        for (argument, expected) in [
            (OutputType::Lookup16Bits, &expected_lookup16),
            (OutputType::LookupTimestamps, &expected_timestamp),
            (OutputType::GenericLookup, &expected_generic),
        ] {
            let lookup_outputs = &layer_description[&argument].output;
            assert_eq!(
                read_ext_poly(storage.get_ext_poly(lookup_outputs[0]), &context),
                expected.0,
                "{argument:?} num chain mismatch at round {round_idx}"
            );
            assert_eq!(
                read_ext_poly(storage.get_ext_poly(lookup_outputs[1]), &context),
                expected.1,
                "{argument:?} den chain mismatch at round {round_idx}"
            );
        }
    }
}

const PROBE_LAYER_IDX: usize = 3;
const PROBE_TRACE_LOG_2: u32 = 11;

/// The standalone dimension-reducing tower binds adjacent pairs: every round's
/// output cell `j` is the CPU value for the input pair `(2 * j, 2 * j + 1)`.
#[test]
fn forward_tower_binds_adjacent_pairs_vs_cpu() {
    let context = make_test_context(1024, 32);
    let initial_trace_len = 1usize << PROBE_TRACE_LOG_2;
    let label = "random";
    let columns = random_probe(initial_trace_len, 0x1eaf_f00d);

    let mut storage = GpuGKRStorage::<BF, E4>::default();
    let output_map = install_probe_columns(&mut storage, PROBE_LAYER_IDX, &columns, &context);
    attach_test_dim_reducing_tower_layout(
        &mut storage,
        PROBE_LAYER_IDX,
        &output_map,
        PROBE_TRACE_LOG_2,
        0,
    );

    let prepared = prepare_dimension_reduction_forward::<E4>(
        &mut storage,
        PROBE_LAYER_IDX,
        &output_map,
        PROBE_TRACE_LOG_2,
        0,
        None,
        &context,
    )
    .unwrap();
    schedule_prepared_dimension_reduction_forward(&prepared, 0, &context).unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let mut expected = columns;
    for round_idx in 0..prepared.total_rounds {
        expected = expected_round_reduction(&expected);
        let round_len = 1usize << (PROBE_TRACE_LOG_2 - round_idx - 1);
        let outputs = read_and_pin_round_outputs(
            &storage,
            &prepared.dimension_reduction_description,
            PROBE_LAYER_IDX + round_idx as usize,
            round_len,
            &context,
            label,
        );
        assert_eq!(outputs, expected, "{label}: round {round_idx}");
    }
}

/// The production forward VM's fused reduction prefix binds adjacent pairs: its
/// round zero reads `(2 * j, 2 * j + 1)` of the layer inputs and its in-shared-
/// memory rounds keep halving on the low coordinate.
#[test]
fn forward_production_vm_binds_adjacent_pairs_vs_cpu() {
    let context = make_test_context(1024, 32);
    let initial_trace_len = 1usize << PROBE_TRACE_LOG_2;
    // The VM owns exactly the fused rounds, so no round is left unwritten.
    let final_trace_log_2 = PROBE_TRACE_LOG_2 - FUSED_REDUCTION_ROUNDS as u32;

    let label = "random";
    let columns = random_probe(initial_trace_len, 0xfeed_face);

    let mut storage = GpuGKRStorage::<BF, E4>::default();
    let output_map = install_probe_columns(&mut storage, PROBE_LAYER_IDX, &columns, &context);
    attach_test_dim_reducing_tower_layout(
        &mut storage,
        PROBE_LAYER_IDX,
        &output_map,
        PROBE_TRACE_LOG_2,
        final_trace_log_2,
    );

    let prepared = prepare_dimension_reduction_forward::<E4>(
        &mut storage,
        PROBE_LAYER_IDX,
        &output_map,
        PROBE_TRACE_LOG_2,
        final_trace_log_2,
        None,
        &context,
    )
    .unwrap();
    assert_eq!(prepared.total_rounds, FUSED_REDUCTION_ROUNDS as u32);

    let forward_setup = schedule_forward_setup_for_shape(
        None,
        initial_trace_len,
        0,
        0,
        false,
        context
            .alloc::<E4>(2, AllocationPlacement::BestFit)
            .unwrap(),
        &context,
    )
    .unwrap();

    // A single empty layer program keeps the VM's own arithmetic out of the
    // way; the reduction prefix under test runs after `vm_body` regardless.
    let mut lowered = LoweredFwdVm {
        // SAFETY: the descriptor is plain data and all pointer fields may be null.
        desc: unsafe { core::mem::zeroed() },
        lookup_additive_slot: None,
        decoder_fill_slot: None,
    };
    lowered.desc.count = initial_trace_len as u32;
    lowered.desc.layer_count = 1;
    schedule_vm(&mut lowered, &prepared, &forward_setup, &context).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    assert_eq!(
        lowered.desc.reduction_pair_count as usize,
        PROBE_OUTPUT_TYPES.len(),
        "{label}: every probe output type must ride the descriptor"
    );

    let mut expected = columns;
    for round_idx in 0..FUSED_REDUCTION_ROUNDS as u32 {
        expected = expected_round_reduction(&expected);
        let round_len = 1usize << (PROBE_TRACE_LOG_2 - round_idx - 1);
        let outputs = read_and_pin_round_outputs(
            &storage,
            &prepared.dimension_reduction_description,
            PROBE_LAYER_IDX + round_idx as usize,
            round_len,
            &context,
            label,
        );
        assert_eq!(outputs, expected, "{label}: round {round_idx}");
    }
}

mod helpers;
