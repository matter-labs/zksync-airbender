use std::collections::BTreeMap;
use std::sync::Arc;

use crate::storage_layout::{FieldType, GpuGKRLayerLayout, GpuGKRStorageLayout, StorageSlot};
use crate::upstream::{Field, GKRAddress, OutputType};
use crate::{GpuExtensionFieldPoly, GpuGKRStorage};
use era_cudart::memory::memory_copy_async;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;

pub(super) fn sample_ext(seed: u32) -> E4 {
    E4::from_array_of_base([
        BF::new(seed),
        BF::new(seed + 1),
        BF::new(seed + 2),
        BF::new(seed + 3),
    ])
}

pub(super) fn upload_ext_poly(values: &[E4], context: &ProverContext) -> GpuExtensionFieldPoly<E4> {
    let mut device = context
        .alloc(values.len(), AllocationPlacement::Top)
        .unwrap();
    memory_copy_async(&mut device, values, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    GpuExtensionFieldPoly::new(device)
}

pub(super) fn read_ext_poly(poly: &GpuExtensionFieldPoly<E4>, context: &ProverContext) -> Vec<E4> {
    let mut host = vec![E4::ZERO; poly.len()];
    memory_copy_async(&mut host, poly.as_device_slice(), context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

pub(super) fn attach_test_dim_reducing_tower_layout(
    storage: &mut GpuGKRStorage<BF, E4>,
    initial_layer_idx: usize,
    initial_output_map: &BTreeMap<OutputType, Vec<GKRAddress>>,
    initial_trace_log_2: u32,
    final_trace_log_2: u32,
) {
    use crate::gkr_address_audit::AddressClass;

    let trace_len = 1usize << initial_trace_log_2;
    let total_rounds = initial_trace_log_2.saturating_sub(final_trace_log_2);
    let total_layers = initial_layer_idx + total_rounds as usize + 1;
    let mut layers = vec![GpuGKRLayerLayout::default(); total_layers];

    let mut initial_layer_layout = GpuGKRLayerLayout {
        log2_stride: initial_trace_log_2,
        ..GpuGKRLayerLayout::default()
    };
    let mut initial_poly_count = 0u32;
    for input in initial_output_map.values().flatten() {
        initial_layer_layout.index.insert(
            *input,
            (
                AddressClass::ThisLayerInnerLayerWrite,
                FieldType::Ext,
                initial_poly_count,
            ),
        );
        initial_poly_count += 1;
    }
    initial_layer_layout.slot_poly_counts.insert(
        StorageSlot {
            class: AddressClass::ThisLayerInnerLayerWrite,
            field: FieldType::Ext,
        },
        initial_poly_count,
    );
    layers[initial_layer_idx] = initial_layer_layout;

    let mut layer_inputs = initial_output_map.clone();
    for (layer_offset, round) in (0..total_rounds).enumerate() {
        let output_layer = initial_layer_idx + layer_offset + 1;
        let mut layout = GpuGKRLayerLayout {
            log2_stride: initial_trace_log_2 - round - 1,
            ..GpuGKRLayerLayout::default()
        };
        let mut output_idx = 0u32;
        let mut next_inputs = BTreeMap::new();
        for (argument, inputs) in &layer_inputs {
            assert_eq!(inputs.len(), 2);
            let outputs = [
                GKRAddress::InnerLayer {
                    layer: output_layer,
                    offset: output_idx as usize,
                },
                GKRAddress::InnerLayer {
                    layer: output_layer,
                    offset: output_idx as usize + 1,
                },
            ];
            for output in outputs {
                layout.index.insert(
                    output,
                    (
                        AddressClass::ThisLayerInnerLayerWrite,
                        FieldType::Ext,
                        output_idx,
                    ),
                );
                output_idx += 1;
            }
            next_inputs.insert(*argument, outputs.to_vec());
        }
        layout.slot_poly_counts.insert(
            StorageSlot {
                class: AddressClass::ThisLayerInnerLayerWrite,
                field: FieldType::Ext,
            },
            output_idx,
        );
        layers[output_layer] = layout;
        layer_inputs = next_inputs;
    }

    storage.set_layout(Arc::new(GpuGKRStorageLayout {
        trace_len,
        artifact_log2_stride: initial_trace_log_2,
        layers,
        aliases: BTreeMap::new(),
        scratch_space_mapping_rev: BTreeMap::new(),
    }));
}

pub(super) fn expected_pairwise_reduction(values: &[E4]) -> Vec<E4> {
    values
        .as_chunks::<2>()
        .0
        .iter()
        .map(|chunk| {
            let mut value = chunk[0];
            value.mul_assign(&chunk[1]);
            value
        })
        .collect()
}

pub(super) fn expected_lookup_pair_reduction(num: &[E4], den: &[E4]) -> (Vec<E4>, Vec<E4>) {
    let mut reduced_num = Vec::with_capacity(num.len() / 2);
    let mut reduced_den = Vec::with_capacity(den.len() / 2);

    for (num_pair, den_pair) in num
        .as_chunks::<2>()
        .0
        .iter()
        .zip(den.as_chunks::<2>().0.iter())
    {
        let mut left_term = num_pair[0];
        left_term.mul_assign(&den_pair[1]);
        let mut right_term = num_pair[1];
        right_term.mul_assign(&den_pair[0]);
        left_term.add_assign(&right_term);
        reduced_num.push(left_term);

        let mut den_value = den_pair[0];
        den_value.mul_assign(&den_pair[1]);
        reduced_den.push(den_value);
    }

    (reduced_num, reduced_den)
}
