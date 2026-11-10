use std::collections::BTreeMap;
use std::sync::Arc;

use era_cudart::slice::DeviceSlice;
use field::Field;
use gpu_prover_context::ProverContext;
use prover::gkr::sumcheck::access_and_fold::{ExtensionFieldPoly, GKRStorage as CpuStorage};
use prover::transcript::{Keccak256Transcript, Transcript};
use worker::Worker;

use crate::forward::{
    prepare_dimension_reduction_forward, schedule_prepared_dimension_reduction_forward,
    ForwardOutputSlabTarget, GpuGKRForwardOutput, PreparedDimensionReductionForward,
};
use crate::gkr_address_audit::AddressClass;
use crate::proth120::forward::{prepare_backward_handoff_pr, schedule_forward_challenge_banks};
use crate::proth120::packed_challenges::split_challenges;
use crate::storage_layout::GpuGKRStorageLayout;
use crate::upstream::{DimensionReducingInputOutput, GKRAddress, PR};
use crate::{GpuExtensionFieldPoly, GpuGKRStorage};

use super::{deterministic_columns, make_context, read_back, upload};

fn mul(mut lhs: PR, rhs: PR) -> PR {
    lhs.mul_assign(&rhs);
    lhs
}

fn compare(actual: &[PR], expected: &[PR], label: &str) {
    assert_eq!(actual.len(), expected.len(), "{label} length");
    if let Some(index) = actual.iter().zip(expected).position(|(a, e)| a != e) {
        panic!(
            "{label} mismatch at row {index}: actual={:?} expected={:?}",
            actual[index], expected[index]
        );
    }
}

#[test]
#[cfg(not(no_cuda))]
fn pr_challenge_banks_match_host_powers() {
    let context = make_context();
    let programs = super::cpu_abi::programs();
    let mode = super::deterministic_mode(0x2_0000_0003);
    let top = upload(&super::transcript_prefix_words(&mode, &[1u32, 2]), &context);
    let setup = upload(&super::deterministic_words(8, 31), &context);
    let base = upload(&super::deterministic_words(8, 71), &context);
    let mut seed = upload(&[0u8; 32], &context);
    let challenges = super::derive(
        &mut seed,
        &top,
        &setup,
        &base,
        &super::PackedChallengeConfig {
            pow_bits: 0,
            cap_log: 0,
            top_bits_len: 2,
            setup_present: true,
        },
        &context,
    )
    .unwrap();
    let banks =
        schedule_forward_challenge_banks(&challenges, &programs.challenge_plan, &context).unwrap();
    let host = read_back(challenges.challenges(), PR::ZERO, &context);
    assert!(host.iter().any(|value| value.to_u128() > u32::MAX as u128));
    let actual = read_back(&banks.arg_derived, PR::ZERO, &context);
    let (external, [lookup_alpha, lookup_additive_part]) =
        split_challenges(host.as_slice().try_into().unwrap());
    for index in 0..actual.len() {
        let expected = programs.challenge_plan.arg_refs.get(index).map_or(PR::ZERO, |reference| {
            use gkr_eval_ir::{ChallengeKey, ChallengePower, PermutationSlot};
            let base = match reference.key {
                ChallengeKey::PermutationAdditive => external.permutation_argument_additive_part,
                ChallengeKey::PermutationLinearization(slot) => {
                    let column = match slot {
                        PermutationSlot::AddressLow => cs::definitions::PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                        PermutationSlot::AddressHigh => cs::definitions::PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
                        PermutationSlot::TimestampLow => cs::definitions::PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
                        PermutationSlot::TimestampHigh => cs::definitions::PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
                        PermutationSlot::ValueLow => cs::definitions::PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                        PermutationSlot::ValueHigh => cs::definitions::PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                    };
                    external.permutation_argument_linearization_challenges[column]
                }
                ChallengeKey::LookupAdditive => lookup_additive_part,
                ChallengeKey::LookupMultiplicative => lookup_alpha,
                ChallengeKey::ClaimBatching => panic!("Proth120 forward fixture cannot use ClaimBatching"),
            };
            base.pow(match reference.power { ChallengePower::One => 1, ChallengePower::Static(power) => power })
        });
        assert_eq!(actual[index], expected, "argument power {index}");
    }
    let actual = read_back(&banks.lookup_alpha_powers, PR::ZERO, &context);
    let expected: Vec<_> = (0..11).map(|power| lookup_alpha.pow(power)).collect();
    compare(&actual, &expected, "lookup alpha powers");
    let mut expected = [PR::ZERO; 8];
    let plan = &programs.challenge_plan.desc;
    expected[plan.lookup_slot as usize] = lookup_additive_part;
    expected[plan.decoder_slot as usize] = mul(
        lookup_alpha.pow(plan.table_width - 1),
        PR::new(plan.decoder_table_id as u128),
    );
    compare(
        &read_back(&banks.const_derived, PR::ZERO, &context),
        &expected,
        "constant powers",
    );
}

#[allow(clippy::arc_with_non_send_sync)]
fn dr_fixture(context: &ProverContext) -> (GpuGKRForwardOutput<PR, PR>, Vec<PR>) {
    let mut artifact = (*super::cpu_abi::programs().runtime_circuit).clone();
    artifact.trace_len = 1 << 12;
    let worker = Worker::new_with_num_threads(4);
    let columns = deterministic_columns(12, 10);
    let mut cpu = CpuStorage::<PR, PR>::default();
    cpu.layers.resize_with(6, Default::default);
    let mut gpu = GpuGKRStorage::<PR, PR>::default();
    gpu.set_layout(Arc::new(GpuGKRStorageLayout::from_artifact_with_tower(
        &artifact,
        crate::proth120::backward::dr_tail::PR_DR_FINAL_TRACE_LOG_2 as usize,
    )));
    for (address, values) in artifact.global_output_map.values().flatten().zip(&columns) {
        cpu.layers[5].extension_field_inputs.insert(
            *address,
            ExtensionFieldPoly::new(values.clone().into_boxed_slice()),
        );
        gpu.insert_extension_at_layer(
            5,
            *address,
            GpuExtensionFieldPoly::from_arc(Arc::new(upload(values, context)), 0, values.len()),
        );
    }
    let pool = prover::allocation_pool::GenericAllocationPool::<PR, PR>::with_retain(false);
    let final_log = crate::proth120::backward::dr_tail::PR_DR_FINAL_TRACE_LOG_2;
    let (last, description) =
        prover::gkr::prover::dimension_reduction::forward::evaluate_dimension_reduction_forward(
            &mut cpu,
            &artifact,
            12,
            final_log as usize,
            &pool,
            &worker,
        );
    let slab = ForwardOutputSlabTarget {
        backing: Arc::new(
            context
                .alloc(
                    10 << final_log,
                    gpu_core::allocator::tracker::AllocationPlacement::BestFit,
                )
                .unwrap(),
        ),
        len: 10 << final_log,
    };
    let prepared = prepare_dimension_reduction_forward(
        &mut gpu,
        5,
        &artifact.global_output_map,
        12,
        final_log,
        Some(&slab),
        context,
    )
    .unwrap();
    schedule_prepared_dimension_reduction_forward(&prepared, 0, context).unwrap();
    for (layer, outputs) in &description {
        for address in outputs.values().flat_map(|io| &io.output) {
            let expected = cpu.get_ext_poly(*address);
            let poly = gpu.get_ext_poly(*address);
            let actual = read_back(
                unsafe { DeviceSlice::from_raw_parts(poly.as_ptr(), poly.len()) },
                PR::ZERO,
                context,
            );
            compare(&actual, expected, &format!("DR layer {layer} {address:?}"));
        }
    }
    assert_eq!(last, prepared.final_layer_idx);
    assert_eq!(description, prepared.dimension_reduction_description);
    let expected = description[&last]
        .values()
        .flat_map(|io| &io.output)
        .flat_map(|address| cpu.get_ext_poly(*address).iter().copied())
        .collect();
    (
        GpuGKRForwardOutput::new(vec![], gpu, last, prepared.dimension_reduction_description),
        expected,
    )
}

#[test]
#[cfg(not(no_cuda))]
fn pr_dr_tower_matches_cpu() {
    let context = make_context();
    let (output, expected) = dr_fixture(&context);
    compare(
        &read_back(
            output.transcript_handoff().device_flat_evaluations(),
            PR::ZERO,
            &context,
        ),
        &expected,
        "DR final prefix",
    );
}

#[test]
#[cfg(not(no_cuda))]
fn pr_handoff_transcript_matches_cpu() {
    let context = make_context();
    let final_log = crate::proth120::backward::dr_tail::PR_DR_FINAL_TRACE_LOG_2;
    let rows = 1usize << final_log;
    let values: Vec<_> = deterministic_columns(final_log, 10)
        .into_iter()
        .flatten()
        .collect();
    #[allow(clippy::arc_with_non_send_sync)]
    let backing = Arc::new(upload(&values, &context));
    let mut storage = GpuGKRStorage::<PR, PR>::default();
    storage.layers.resize_with(2, Default::default);
    storage.layers[1]
        .ext_class_backings
        .insert(AddressClass::ThisLayerInnerLayerWrite, Arc::clone(&backing));
    let mut outputs = BTreeMap::new();
    let programs = super::cpu_abi::programs();
    for (index, kind) in programs
        .runtime_circuit
        .global_output_map
        .keys()
        .enumerate()
    {
        let addresses: Vec<_> = (index * 2..index * 2 + 2)
            .map(|offset| GKRAddress::InnerLayer { layer: 1, offset })
            .collect();
        for (local, address) in addresses.iter().enumerate() {
            storage.insert_extension_at_layer(
                1,
                *address,
                GpuExtensionFieldPoly::from_arc(
                    Arc::clone(&backing),
                    (index * 2 + local) * rows,
                    rows,
                ),
            );
        }
        outputs.insert(
            *kind,
            DimensionReducingInputOutput {
                inputs: vec![],
                output: addresses,
            },
        );
    }
    let output = GpuGKRForwardOutput::new(vec![], storage, 0, BTreeMap::from([(0, outputs)]));
    let seed_bytes = std::array::from_fn::<_, 32, _>(|index| (index * 7 + 3) as u8);
    let mut seed = <Keccak256Transcript as Transcript<PR, PR>>::commit_initial_u32(&[]);
    seed.0 = seed_bytes;
    <Keccak256Transcript as Transcript<PR, PR>>::commit_base_field_elements(&mut seed, &values);
    let committed_seed = seed.0;
    let mut expected_draws = vec![PR::ZERO; final_log as usize + 1];
    <Keccak256Transcript as Transcript<PR, PR>>::draw_random_field_elements(
        &mut seed,
        &mut expected_draws,
    );
    let mut device_seed = upload(&seed_bytes, &context);
    gpu_hash::keccak256::transcript_commit_fields(
        &mut device_seed,
        &backing,
        context.get_exec_stream(),
    )
    .unwrap();
    assert_eq!(read_back(&device_seed, 0u8, &context), committed_seed);
    drop(device_seed);
    let handoff =
        prepare_backward_handoff_pr(output, upload(&seed_bytes, &context), final_log, &context)
            .unwrap();
    compare(
        &read_back(&handoff.d_evaluation_point_and_batching, PR::ZERO, &context),
        &expected_draws,
        "handoff draws",
    );
    assert_eq!(read_back(&handoff.d_seed, 0u8, &context), seed.0);
    let expected: Vec<_> = values
        .chunks_exact(rows)
        .map(|poly| {
            poly.iter()
                .enumerate()
                .fold(PR::ZERO, |sum, (index, value)| {
                    let weight = expected_draws[..final_log as usize]
                        .iter()
                        .enumerate()
                        .fold(PR::ONE, |weight, (bit, coordinate)| {
                            mul(
                                weight,
                                if index & (1 << bit) == 0 {
                                    PR::ONE - *coordinate
                                } else {
                                    *coordinate
                                },
                            )
                        });
                    sum + mul(*value, weight)
                })
        })
        .collect();
    compare(
        &read_back(&handoff.initial_d_claims, PR::ZERO, &context),
        &expected,
        "handoff initial claims",
    );
}

// One committed wrap layer, evaluated independently through the CPU prover.
// The row-local program reads the lookup-additive constant, but needs no table
// lookup or argument-derived challenges at this reduced row count.
struct ProductionVmColumn {
    address: GKRAddress,
    field: gpu_gkr_compiler::ForwardOperandField,
    input: Option<Vec<PR>>,
    expected: Option<Vec<PR>>,
}

fn production_vm_fixture() -> (gpu_gkr_compiler::CompiledLayer, Vec<ProductionVmColumn>, PR) {
    use gpu_gkr_compiler::{ForwardDstLine, ForwardInstr, ForwardOperandField, ForwardOperandLine};
    use prover::gkr::sumcheck::access_and_fold::BaseFieldPoly;
    let programs = super::cpu_abi::programs();
    let layer_index = 2;
    let layer = programs.forward.layers[layer_index].clone();
    assert_eq!(layer.specials.len(), 0);
    assert!(layer.consts.values().is_empty());
    assert!(layer.derived_e4.arg_refs().is_empty());
    assert!(layer.derived_e4.uses_lookup_additive());
    let mut inputs = BTreeMap::new();
    let mut outputs = BTreeMap::new();
    for instruction in &layer.program.instrs {
        let mut record = |operand: &ForwardOperandLine, field| {
            if let ForwardOperandLine::Source { window, column } = *operand {
                let place = layer
                    .source_windows
                    .resolve_read_place(window, column)
                    .unwrap();
                inputs.insert(
                    crate::proth120::forward::lower::read_place_to_gkr_address(&place),
                    field,
                );
            }
        };
        match instruction {
            ForwardInstr::Add {
                field, operands, ..
            }
            | ForwardInstr::Mul {
                field, operands, ..
            } => {
                for operand in operands {
                    record(operand, *field);
                }
            }
            ForwardInstr::Fma {
                field_lhs,
                field_rhs,
                pairs,
                ..
            } => {
                for (lhs, rhs) in pairs {
                    record(lhs, *field_lhs);
                    record(rhs, *field_rhs);
                }
            }
            ForwardInstr::Mov {
                field, src, dst, ..
            } => {
                if let Some(src) = src {
                    record(src, *field);
                }
                if let Some(ForwardDstLine::GlobalMaterialize { slot, col }) = dst {
                    let place = layer.backings.slot_col_to_read_place(*slot, *col).unwrap();
                    outputs.insert(
                        crate::proth120::forward::lower::read_place_to_gkr_address(&place),
                        *field,
                    );
                }
            }
        }
    }
    let mut artifact = (*programs.runtime_circuit).clone();
    artifact.trace_len = 256;
    // The compiler eliminates copy-only outputs and resolves their aliases.
    // They are outside this layer's materialized VM writes and need no CPU
    // evaluation for this oracle.
    artifact.layers[layer_index]
        .gates
        .retain(|gate| match &gate.enforced_relation {
            cs::gkr_compiler::GKRRelation::CopyInBaseField { output, .. }
            | cs::gkr_compiler::GKRRelation::CopyInExtensionField { output, .. } => {
                outputs.contains_key(output)
            }
            _ => true,
        });
    let cpu_address = |address| match address {
        GKRAddress::ScratchSpace(slot) => artifact.scratch_space_mapping_rev[&slot],
        address => address,
    };
    let storage_layer = |address| match address {
        GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => layer,
        _ => 0,
    };
    let mut cpu = CpuStorage::<PR, PR>::default();
    cpu.layers
        .resize_with(artifact.layers.len() + 1, Default::default);
    let mut columns = BTreeMap::new();
    let values = deterministic_columns(8, inputs.len());
    for ((address, field), mut values) in inputs.into_iter().zip(values) {
        if field == ForwardOperandField::Base {
            for (row, value) in values.iter_mut().enumerate() {
                *value = PR::new((row & 1) as u128);
            }
        }
        let cpu_addr = cpu_address(address);
        let storage = &mut cpu.layers[storage_layer(cpu_addr)];
        if field == ForwardOperandField::Ext {
            storage.extension_field_inputs.insert(
                cpu_addr,
                ExtensionFieldPoly::new(values.clone().into_boxed_slice()),
            );
        } else {
            storage.base_field_inputs.insert(
                cpu_addr,
                BaseFieldPoly::new(values.clone().into_boxed_slice()),
            );
        }
        columns.insert(
            address,
            ProductionVmColumn {
                address,
                field,
                input: Some(values),
                expected: None,
            },
        );
    }
    // CPU copy relations retain logical aliases; the compiled VM resolves
    // those aliases directly to the canonical input matrix.
    for (&alias, &canonical) in &programs.storage_layout.aliases {
        if storage_layer(alias) > layer_index {
            continue;
        }
        if let Some(column) = columns.get(&canonical) {
            let values = column.input.as_ref().unwrap().clone().into_boxed_slice();
            let storage = &mut cpu.layers[storage_layer(alias)];
            if column.field == ForwardOperandField::Ext {
                storage
                    .extension_field_inputs
                    .insert(alias, ExtensionFieldPoly::new(values));
            } else {
                storage
                    .base_field_inputs
                    .insert(alias, BaseFieldPoly::new(values));
            }
        }
    }
    let mut witness = prover::gkr::witness_gen::family_circuits::GKRFullWitnessTrace {
        column_major_memory_trace: vec![],
        column_major_witness_trace: vec![],
        column_major_scratch_space_trace: vec![],
        generic_lookup_mapping: vec![],
        range_check_16_lookup_mapping: vec![],
        timestamp_range_check_lookup_mapping: vec![],
    };
    let challenges = std::array::from_fn(|i| PR::new(i as u128 + 3));
    let (external, [lookup_alpha, lookup_additive]) = split_challenges(&challenges);
    let pool = prover::allocation_pool::GenericAllocationPool::<PR, PR>::with_retain(false);
    prover::gkr::prover::forward_loop::evaluate_layer(
        layer_index,
        &artifact.layers[layer_index],
        &mut cpu,
        &artifact,
        &external,
        &mut witness,
        &[],
        256,
        &[],
        lookup_alpha,
        lookup_additive,
        PR::ONE,
        &pool,
        &Worker::new_with_num_threads(2),
    );
    for (address, field) in outputs {
        let cpu_addr = cpu_address(address);
        let expected = if field == ForwardOperandField::Ext {
            cpu.get_ext_poly(cpu_addr).to_vec()
        } else {
            cpu.try_get_base_poly(cpu_addr).unwrap().to_vec()
        };
        let column = columns.entry(address).or_insert(ProductionVmColumn {
            address,
            field,
            input: None,
            expected: None,
        });
        assert_eq!(column.field, field);
        column.expected = Some(expected);
    }
    let columns: Vec<_> = columns.into_values().collect();
    assert!(columns.iter().any(|column| column
        .expected
        .as_ref()
        .is_some_and(|v| v.iter().any(|&v| v != PR::ZERO))));
    (layer, columns, lookup_additive)
}

#[test]
#[cfg(not(no_cuda))]
fn pr_partial_block_vm_and_tower_are_guarded() {
    use era_cudart::execution::KernelFunction;
    let context = make_context();
    let function = crate::proth120::forward::kernels::vm_function();
    let mut attributes = std::mem::MaybeUninit::<era_cudart_sys::CudaFuncAttributes>::zeroed();
    assert_eq!(
        unsafe {
            era_cudart_sys::cudaFuncGetAttributes(attributes.as_mut_ptr(), function.as_ptr())
        },
        era_cudart_sys::CudaError::Success
    );
    let attributes = unsafe { attributes.assume_init() };
    let blocks =
        era_cudart::occupancy::max_active_blocks_per_multiprocessor(&function, 128, 0).unwrap();
    assert!(blocks > 0);
    assert_eq!(attributes.localSizeBytes, 0);
    let (layer, columns, lookup_additive) = production_vm_fixture();
    let const_derived = upload(&[lookup_additive], &context);
    let sentinel = PR::new(0xfedc_ba98);
    let stride = 258;
    // Group the same physical matrices the production lowerer resolves. Each
    // column has two guards and room for 256 rows; only 129 rows are launched.
    let group_key = |column: &ProductionVmColumn| {
        let (kind, index) = match column.address {
            GKRAddress::BaseLayerMemory(_) => (0, 0),
            GKRAddress::BaseLayerWitness(_) => (1, 0),
            GKRAddress::Setup(_) => (2, 0),
            GKRAddress::ScratchSpace(_) => (3, 0),
            GKRAddress::InnerLayer { layer, .. } => (4, layer),
            GKRAddress::Cached { layer, .. } => (5, layer),
            _ => panic!("unexpected committed VM address {:?}", column.address),
        };
        (
            kind,
            index,
            column.field == gpu_gkr_compiler::ForwardOperandField::Ext,
        )
    };
    let mut groups = BTreeMap::<_, Vec<usize>>::new();
    for (i, column) in columns.iter().enumerate() {
        groups.entry(group_key(column)).or_default().push(i);
    }
    let mut buffers = Vec::new();
    let mut resolved = BTreeMap::new();
    for indexes in groups.into_values() {
        let mut values = vec![sentinel; indexes.len() * stride];
        for (slot, &index) in indexes.iter().enumerate() {
            if let Some(input) = &columns[index].input {
                values[slot * stride + 1..slot * stride + 257].copy_from_slice(input);
            }
        }
        let mut device = upload(&values, &context);
        let base = unsafe { device.as_mut_ptr().add(1) };
        for (slot, &index) in indexes.iter().enumerate() {
            resolved.insert(
                columns[index].address,
                crate::proth120::forward::lower::ResolvedColumn {
                    is_e4: columns[index].field == gpu_gkr_compiler::ForwardOperandField::Ext,
                    ptr: unsafe { base.add(slot * stride) }.cast(),
                    matrix_base: base.cast(),
                    stride_bytes: (stride * 16) as u32,
                },
            );
        }
        buffers.push((device, indexes, values));
    }
    let header = crate::proth120::forward::lower::FwdVmInputs {
        mapping_arena: [std::ptr::null(); 3],
        decoder_mapping_col: None,
        table: std::ptr::null(),
        decoder_mapping: std::ptr::null(),
        table_len: 0,
        count: 129,
        inits_and_teardowns_top_bits: &[],
    };
    let mut lowered = crate::proth120::forward::lower::lower_desc(&[layer], &header, &|address| {
        resolved.get(&address).copied()
    });
    lowered.desc.const_derived = const_derived.as_ptr();
    assert_eq!(lowered.lookup_additive_slot, Some(0));
    assert!(lowered.decoder_fill_slot.is_none());
    assert!(!lowered.desc.const_derived.is_null());
    let prepared = PreparedDimensionReductionForward {
        initial_trace_log_2: 8,
        total_rounds: 1,
        final_layer_idx: 1,
        dimension_reduction_description: BTreeMap::new(),
        slot_initial_inputs: vec![],
        slot_output_types: vec![],
        per_round_slot_outputs: vec![],
    };
    assert_eq!(
        crate::proth120::forward::bind::schedule_vm(&mut lowered, &prepared, &context).unwrap(),
        0
    );
    assert_eq!(lowered.desc.reduction_pair_count, 0);
    for (device, indexes, initial) in &buffers {
        let actual = read_back(device, PR::ZERO, &context);
        for (slot, &index) in indexes.iter().enumerate() {
            let start = slot * stride;
            assert_eq!(actual[start], sentinel);
            assert_eq!(actual[start + 257], sentinel);
            if let Some(expected) = &columns[index].expected {
                compare(
                    &actual[start + 1..start + 130],
                    &expected[..129],
                    "committed production VM",
                );
                compare(
                    &actual[start + 130..start + 257],
                    &initial[start + 130..start + 257],
                    "inactive VM rows",
                );
            } else {
                compare(
                    &actual[start..start + stride],
                    &initial[start..start + stride],
                    "VM input preservation",
                );
            }
        }
    }
    let values = deterministic_columns(8, 1).pop().unwrap();
    let input = upload(&values[..129], &context);
    let mut reduced = upload(&vec![sentinel; 66], &context);
    let mut batch = crate::forward::kernels::GpuGKRDimensionReducingForwardTowerBatch::<PR> {
        pair_count: 1,
        input_len: 129,
        round_count: 1,
        pairwise_mask: 1,
        ..Default::default()
    };
    batch.pairs[0].input = [input.as_ptr(); 2];
    batch.pairs[0].round_outputs[0] = [unsafe { reduced.as_mut_ptr().add(1) }; 2];
    crate::forward::kernels::launch_dimension_reducing_forward_tower(
        batch,
        context.get_exec_stream(),
    )
    .unwrap();
    let actual = read_back(&reduced, PR::ZERO, &context);
    assert_eq!(actual[0], sentinel);
    assert_eq!(actual[65], sentinel);
    let expected: Vec<_> = values[..128]
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| mul(pair[0], pair[1]))
        .collect();
    compare(&actual[1..65], &expected, "partial tower");
}
