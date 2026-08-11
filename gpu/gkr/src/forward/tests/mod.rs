use super::*;
use helpers::*;

use super::dimension_reducing::{
    prepare_dimension_reduction_forward, schedule_prepared_dimension_reduction_forward,
    LoweredSlotOutput,
};
use crate::test_utils::make_test_context;
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
    let mut tracing_ranges = Vec::new();
    schedule_prepared_dimension_reduction_forward(&prepared, 0, &mut tracing_ranges, &context)
        .unwrap();

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
    schedule_prepared_dimension_reduction_forward(&prepared, 7, &mut tracing_ranges, &context)
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    let (final_layer_idx, dim_reducing_inputs) = prepared.into_result();

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

mod helpers;
