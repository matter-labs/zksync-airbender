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
use crate::proth120::forward::desc::{FwdVmDesc, FwdVmLayer};
use crate::proth120::forward::lower::LoweredFwdVm;
use crate::proth120::forward::{prepare_backward_handoff_pr, schedule_forward_challenge_banks};
use crate::proth120::packed_challenges::split_challenges;
use crate::storage_layout::GpuGKRStorageLayout;
use crate::upstream::{DimensionReducingInputOutput, GKRAddress, PR};
use crate::{GpuExtensionFieldPoly, GpuGKRStorage};

use super::{deterministic_columns, make_context, read_back, upload};

pub(crate) fn forward_context() -> ProverContext {
    ProverContext::new(&gpu_prover_context::ProverContextConfig {
        device_allocation_blocks_count: Some(64 * 1024),
        host_allocator_blocks_count: 4096,
        proth120_ntt_log_max_domain: Some(26),
        ..Default::default()
    })
    .unwrap()
}

pub(crate) fn small_programs() -> (
    Arc<crate::upstream::GKRCircuitArtifact<PR>>,
    Arc<crate::proth120::programs::GkrProgramsPr>,
) {
    let artifact = Arc::new(
        cs::gkr_circuits::unified_reduced_machine::build_unified_artifact_core::<
            PR,
            field::baby_bear::base::BabyBearField,
        >(true, 21, 1, prover::common_constants::rom::L1_WRAP_ROM),
    );
    let minimum_log = (artifact
        .total_tables_size
        .next_power_of_two()
        .trailing_zeros() as usize)
        .max(19)
        .max(12);
    assert_eq!(
        minimum_log, 21,
        "Proth120 small forward shape minimum changed"
    );
    assert_eq!(artifact.trace_len, 1 << minimum_log);
    let dag = gkr_eval_ir::lower_dag(&artifact).unwrap();
    let schedule = gpu_gkr_compiler::search_forward(gpu_gkr_compiler::ForwardSearchRequest {
        circuit: "unified_reduced_machine",
        dag: &dag,
        cache_buckets: crate::proth120::forward::desc::PR_FWD_VM_BUCKETS as usize,
        config: gpu_gkr_compiler::SearchConfig {
            population: 8,
            evaluations: 64,
            ..gpu_gkr_compiler::SearchConfig::production()
        },
        seed: 0x120,
        incumbent: None,
    })
    .unwrap();
    let programs = Arc::new(
        crate::proth120::programs::GkrProgramsPr::compile_with_schedule(
            Arc::clone(&artifact),
            &serde_json::to_vec(&schedule).unwrap(),
        )
        .unwrap(),
    );
    println!("M6_SMALL_FORWARD log_rows={minimum_log} tables={} search_population=8 search_evaluations=64 budget=4 geometry={}", artifact.total_tables_size, serde_json::to_string(&programs.geometry).unwrap());
    (artifact, programs)
}

pub(crate) struct ForwardFixturePr {
    pub programs: Arc<crate::proth120::programs::GkrProgramsPr>,
    pub artifact: Arc<crate::upstream::GKRCircuitArtifact<PR>>,
    pub gpu: GpuGKRForwardOutput<PR, PR>,
    pub cpu: CpuStorage<PR, PR>,
    pub proof: crate::proth120::proof_layout::ProofSlabPr,
    pub challenges: crate::proth120::packed_challenges::PackedChallenges,
    pub seed: gpu_core::primitives::context::DeviceAllocation<u8>,
    pub external: prover::definitions::GKRExternalChallenges<PR, PR>,
    pub lookup: [PR; 2],
    pub top_bits: Vec<u32>,
    pub config: prover::gkr::prover_config::ProverConfig,
}

pub(crate) fn forward_fixture(
    context: &ProverContext,
) -> (
    Arc<crate::proth120::programs::GkrProgramsPr>,
    GpuGKRForwardOutput<PR, PR>,
    CpuStorage<PR, PR>,
) {
    let fixture = forward_fixture_full(context);
    (fixture.programs, fixture.gpu, fixture.cpu)
}

pub(crate) fn forward_fixture_full(context: &ProverContext) -> ForwardFixturePr {
    use era_cudart::memory::memory_copy_async;
    use gpu_core::allocator::tracker::AllocationPlacement;
    use gpu_core::primitives::device_structures::DeviceMatrix;
    use gpu_trace::trace::holder::{TraceHolder, TreesCacheMode};
    use gpu_trace::trace::packed::{PackedCommitConfig, PackedCosetRecomputeOracle};
    use prover::gkr::sumcheck::access_and_fold::BaseFieldPoly;
    let (artifact, programs) = small_programs();
    let rows = artifact.trace_len;
    let log_rows = rows.trailing_zeros();
    let worker = Worker::new_with_num_threads(4);
    let cfg = PackedCommitConfig {
        log_lde_factor: 0,
        log_values_per_leaf: 2,
        cap_log: 0,
        skip_bottom: 5,
    };
    let setup = {
        let binary = vec![0u32; artifact.total_tables_size - artifact.offset_for_decoder_table];
        let driver = prover::gkr::witness_gen::family_circuits::build_unified_table_driver_with_rom::<
            PR,
            { prover::common_constants::rom::L1_WRAP_ROM.second_word_bits() },
        >(&binary);
        let decoder = vec![None; artifact.total_tables_size - artifact.offset_for_decoder_table];
        prover::gkr::prover::setup::GKRSetup::<PR>::construct(&driver, &decoder, rows, &artifact)
    };
    let setup_host = Arc::new(
        crate::setup::L1WrapSetupHost::precompute(
            &setup,
            prover::gkr::prover_config::example_configs::l1_wrap_2p21::PACK_LOG2 as u32,
            cfg,
            context,
        )
        .unwrap(),
    );
    let mut d_setup = crate::setup::PackedSetupSource::new(
        setup_host,
        gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
        context,
    )
    .unwrap();
    let transfer = gpu_prover_context::transfer::single_shot_h2d(
        |transfer| d_setup.schedule_transfer(transfer, context),
        context,
    )
    .unwrap();
    transfer.ensure_transferred(context).unwrap();
    let top_bits = vec![1u32; artifact.memory_layout.teardown_sets.len()];
    let mode = super::deterministic_mode(0x2_0000_0003);
    let d_top = upload(&super::transcript_prefix_words(&mode, &top_bits), context);
    let cap = upload(&super::deterministic_words(8, 73), context);
    let mut seed = upload(&[0u8; 32], context);
    let challenges = super::derive(
        &mut seed,
        &d_top,
        &cap,
        &cap,
        &super::PackedChallengeConfig {
            pow_bits: 0,
            cap_log: 0,
            top_bits_len: top_bits.len(),
            setup_present: true,
        },
        context,
    )
    .unwrap();
    let banks =
        schedule_forward_challenge_banks(&challenges, &programs.challenge_plan, context).unwrap();
    let host_challenges = read_back(challenges.challenges(), PR::ZERO, context);
    let (external, [lookup_alpha, lookup_additive_part]) =
        split_challenges(host_challenges.as_slice().try_into().unwrap());
    let mut cpu = CpuStorage::<PR, PR>::default();
    let (lookup, decoder_fill) =
        setup.preprocess_generic_lookups(&artifact, lookup_alpha, rows, &mut cpu, &worker);
    for (kind, values) in [
        (
            cs::definitions::VirtualSetupPoly::RangeCheck16Bits,
            (0..rows)
                .map(|row| PR::new(if row < 1 << 16 { row as u128 } else { 0 }))
                .collect::<Vec<_>>(),
        ),
        (
            cs::definitions::VirtualSetupPoly::RangeCheckTimestamp,
            (0..rows)
                .map(|row| PR::new(if row < 1 << 19 { row as u128 } else { 0 }))
                .collect::<Vec<_>>(),
        ),
        (
            cs::definitions::VirtualSetupPoly::InitsAndTeardownsLow,
            (0..rows)
                .map(|row| PR::new(((row << 2) & 0xffff) as u128))
                .collect::<Vec<_>>(),
        ),
        (
            cs::definitions::VirtualSetupPoly::InitsAndTeardownsHigh,
            (0..rows)
                .map(|row| PR::new((row >> 14) as u128))
                .collect::<Vec<_>>(),
        ),
    ] {
        cpu.layers[0].base_field_inputs.insert(
            GKRAddress::VirtualSetup(kind),
            BaseFieldPoly::new(values.into_boxed_slice()),
        );
    }
    let mut memory = deterministic_columns(log_rows, artifact.memory_layout.total_width);
    let mut witness = deterministic_columns(log_rows, artifact.witness_layout.total_width);
    memory[21]
        .iter_mut()
        .enumerate()
        .for_each(|(row, value)| *value = PR::new((row & 1) as u128));
    for (timestamps, values) in &artifact.memory_layout.teardown_sets {
        for address in timestamps.iter().chain(values) {
            let GKRAddress::BaseLayerMemory(column) = address else {
                panic!("Proth120 fixture I&T address is not memory")
            };
            memory[*column].fill(PR::ZERO);
        }
    }
    for (column, value) in [(30, 7u128), (31, 11), (33, 13)] {
        memory[column][129] = PR::new(value);
    }
    witness[12][129] = PR::ONE;
    witness[26][129] = PR::new((1u128 << 80) + 19);
    let generic: Vec<Vec<u32>> = (0..artifact.generic_lookups.len())
        .map(|index| (0..rows).map(|row| ((row + index) & 3) as u32).collect())
        .collect();
    let decoder = vec![artifact.offset_for_decoder_table as u32; rows];
    let range16: Vec<Vec<u16>> = (0..artifact.range_check_16_lookup_expressions.len())
        .map(|index| (0..rows).map(|row| ((row + index) & 15) as u16).collect())
        .collect();
    let timestamp: Vec<Vec<u32>> = (0..artifact.timestamp_range_check_lookup_expressions.len())
        .map(|index| (0..rows).map(|row| ((row + index) & 31) as u32).collect())
        .collect();
    for column in artifact
        .witness_layout
        .multiplicities_columns_for_range_check_16
        .clone()
        .chain(
            artifact
                .witness_layout
                .multiplicities_columns_for_timestamp_range_check
                .clone(),
        )
        .chain(
            artifact
                .witness_layout
                .multiplicities_columns_for_generic_lookup
                .clone(),
        )
    {
        witness[column].fill(PR::ZERO);
    }
    for index in range16.iter().flatten() {
        witness[artifact
            .witness_layout
            .multiplicities_columns_for_range_check_16
            .start][*index as usize]
            .add_assign(&PR::ONE);
    }
    for index in timestamp.iter().flatten() {
        witness[artifact
            .witness_layout
            .multiplicities_columns_for_timestamp_range_check
            .start][*index as usize]
            .add_assign(&PR::ONE);
    }
    for index in generic.iter().flatten() {
        witness[artifact
            .witness_layout
            .multiplicities_columns_for_generic_lookup
            .start][*index as usize]
            .add_assign(&PR::ONE);
    }
    witness[65][artifact.offset_for_decoder_table].add_assign(&PR::new((rows / 2) as u128));
    let mut raw = TraceHolder::new_without_cosets(
        log_rows,
        cfg.log_lde_factor,
        cfg.log_values_per_leaf,
        cfg.cap_log,
        memory.len() + witness.len(),
        TreesCacheMode::CacheNone,
        gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
        context,
    )
    .unwrap();
    for (index, column) in memory.iter().chain(&witness).enumerate() {
        memory_copy_async(
            &mut raw.get_uninit_hypercube_evals_mut()[index * rows..(index + 1) * rows],
            column.as_slice(),
            context.get_exec_stream(),
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();
    }
    let base = PackedCosetRecomputeOracle::from_uploaded(
        raw,
        prover::gkr::prover_config::example_configs::l1_wrap_2p21::PACK_LOG2 as u32,
        cfg,
        context,
    )
    .unwrap();
    let scratch = deterministic_columns(log_rows, artifact.scratch_space_size);
    let mut d_scratch = context
        .alloc(rows * scratch.len(), AllocationPlacement::BestFit)
        .unwrap();
    for (index, column) in scratch.iter().enumerate() {
        memory_copy_async(
            &mut d_scratch[index * rows..(index + 1) * rows],
            column.as_slice(),
            context.get_exec_stream(),
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();
    }
    let mut d_generic = context
        .alloc(rows * generic.len(), AllocationPlacement::BestFit)
        .unwrap();
    for (index, column) in generic.iter().enumerate() {
        memory_copy_async(
            &mut d_generic[index * rows..(index + 1) * rows],
            column.as_slice(),
            context.get_exec_stream(),
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();
    }
    let d_decoder = upload(&decoder, context);
    let mut d_range16 = context
        .alloc(rows * range16.len(), AllocationPlacement::BestFit)
        .unwrap();
    for (index, column) in range16.iter().enumerate() {
        let column: Vec<_> = column.iter().map(|value| u32::from(*value)).collect();
        memory_copy_async(
            &mut d_range16[index * rows..(index + 1) * rows],
            column.as_slice(),
            context.get_exec_stream(),
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();
    }
    let mut d_timestamp = context
        .alloc(rows * timestamp.len(), AllocationPlacement::BestFit)
        .unwrap();
    for (index, column) in timestamp.iter().enumerate() {
        memory_copy_async(
            &mut d_timestamp[index * rows..(index + 1) * rows],
            column.as_slice(),
            context.get_exec_stream(),
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();
    }
    let raw = base.raw().get_hypercube_evals();
    #[allow(clippy::arc_with_non_send_sync)]
    let inputs = crate::proth120::inputs::Proth120GkrWitnessInputs::new(
        &artifact,
        Arc::new(d_scratch),
        artifact.scratch_space_size,
        rows,
        DeviceMatrix::new(&d_generic, rows),
        DeviceMatrix::new(&d_range16, rows),
        DeviceMatrix::new(&d_timestamp, rows),
        &d_decoder,
        DeviceMatrix::new(
            &raw[(artifact.memory_layout.total_width
                + artifact
                    .witness_layout
                    .multiplicities_columns_for_range_check_16
                    .start)
                * rows
                ..(artifact.memory_layout.total_width
                    + artifact
                        .witness_layout
                        .multiplicities_columns_for_generic_lookup
                        .end)
                    * rows],
            rows,
        ),
    );
    let mut config = prover::gkr::prover_config::ProofProfile::L1Wrap
        .prover_config(21, crate::upstream::SecurityLevel::Sec100);
    config.trace_len_log2 = log_rows as usize;
    let proof = crate::proth120::proof_layout::ProofSlabPr::new(
        Arc::new(crate::proth120::proof_layout::ProofLayoutPr::new(
            &programs, &config,
        )),
        context,
    )
    .unwrap();
    let mut parity_storage =
        crate::proth120::forward::bootstrap_storage(&base, &d_setup, &inputs, &programs);
    let forward_setup = crate::proth120::forward::setup::schedule_setup(
        &d_setup,
        &programs.runtime_circuit,
        &banks,
        context,
    )
    .unwrap();
    let lowered = crate::proth120::forward::bind::prepare_vm(
        &programs,
        &mut parity_storage,
        &inputs,
        &forward_setup,
        &banks,
        &top_bits,
        context,
    )
    .unwrap();
    assert_eq!(lowered.constant_count, programs.geometry.constants);
    assert_eq!(
        lowered.source_window_count,
        programs.geometry.source_windows
    );
    assert_eq!(
        lowered.destination_slot_count,
        programs.geometry.destination_slots
    );
    assert_eq!(
        lowered.desc.layers[..lowered.desc.layer_count as usize]
            .iter()
            .map(|layer| layer.instruction_count as usize)
            .sum::<usize>(),
        programs
            .forward
            .layers
            .iter()
            .map(|layer| layer.program.instrs.len())
            .sum::<usize>()
    );
    println!(
        "M6_BOUND_FORWARD constants={} sources={} destinations={}",
        lowered.constant_count, lowered.source_window_count, lowered.destination_slot_count
    );
    drop(parity_storage);
    drop(forward_setup);
    let gpu = crate::proth120::forward::schedule_forward_pass_pr(
        &base,
        &d_setup,
        &inputs,
        &banks,
        &top_bits,
        crate::proth120::backward::dr_tail::PR_DR_FINAL_TRACE_LOG_2,
        proof.output_evaluations_target(),
        &programs,
        context,
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    drop(inputs);
    drop(base);
    drop(d_setup);
    let mut generic = generic;
    generic.push(decoder);
    let mut trace = prover::gkr::witness_gen::family_circuits::GKRFullWitnessTrace {
        column_major_memory_trace: memory,
        column_major_witness_trace: witness,
        column_major_scratch_space_trace: scratch,
        generic_lookup_mapping: generic,
        range_check_16_lookup_mapping: range16,
        timestamp_range_check_lookup_mapping: timestamp,
    };
    let pool = prover::allocation_pool::GenericAllocationPool::<PR, PR>::with_retain(false);
    for (index, layer) in artifact.layers.iter().enumerate() {
        prover::gkr::prover::forward_loop::evaluate_layer(
            index,
            layer,
            &mut cpu,
            &artifact,
            &external,
            &mut trace,
            &top_bits,
            rows,
            &lookup,
            lookup_alpha,
            lookup_additive_part,
            decoder_fill,
            &pool,
            &worker,
        );
    }
    ForwardFixturePr {
        programs,
        artifact,
        gpu,
        cpu,
        proof,
        challenges,
        seed,
        external,
        lookup: [lookup_alpha, lookup_additive_part],
        top_bits,
        config,
    }
}

#[test]
#[cfg(not(no_cuda))]
fn pr_fwd_vm_matches_cpu_forward_small() {
    let context = forward_context();
    let (programs, output, cpu) = forward_fixture(&context);
    let (_, gpu, _, _) = output.into_parts();
    let mut compared = 0usize;
    for layer in &cpu.layers {
        for address in layer
            .base_field_inputs
            .keys()
            .chain(layer.extension_field_inputs.keys())
        {
            if !matches!(
                address,
                GKRAddress::InnerLayer { .. } | GKRAddress::Cached { .. }
            ) {
                continue;
            }
            let address_on_gpu = programs
                .runtime_circuit
                .scratch_space_mapping
                .get(address)
                .map_or(*address, |slot| GKRAddress::ScratchSpace(*slot));
            let (pointer, len) = if let Some(poly) = gpu.try_get_base_poly(address_on_gpu) {
                (poly.as_ptr(), poly.len())
            } else {
                let poly = gpu.get_ext_poly(address_on_gpu);
                (poly.as_ptr(), poly.len())
            };
            let expected = cpu
                .try_get_base_poly(*address)
                .or_else(|| cpu.try_get_ext_poly(*address))
                .unwrap();
            let actual = read_back(
                unsafe { DeviceSlice::from_raw_parts(pointer, len) },
                PR::ZERO,
                &context,
            );
            compare(&actual, expected, &format!("forward {address:?}"));
            compared += 1;
        }
    }
    assert!(compared >= 89);
    println!(
        "M6_FORWARD_PARITY columns={compared} rows={}",
        programs.runtime_circuit.trace_len
    );
}

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

#[test]
#[cfg(not(no_cuda))]
fn pr_partial_block_vm_and_tower_are_guarded() {
    use era_cudart::execution::KernelFunction;
    use gpu_gkr_compiler::{
        encode_forward_runtime_program, ForwardDstLine, ForwardInstr, ForwardMovDir,
        ForwardOperandField, ForwardOperandLine, ForwardProgram,
    };
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
    println!("M6_FWD_ATTRIBUTES registers={} static_smem_bytes={} local_bytes={} blocks_per_sm_128={} binary_version={}", attributes.numRegs, attributes.sharedSizeBytes, attributes.localSizeBytes, blocks, attributes.binaryVersion);
    let values = deterministic_columns(8, 1).pop().unwrap();
    let input = upload(&values[..129], &context);
    let sentinel = PR::new(0xfedc_ba98);
    let mut output = upload(&vec![sentinel; 131], &context);
    let program = encode_forward_runtime_program(&ForwardProgram {
        instrs: vec![ForwardInstr::Mov {
            dir: ForwardMovDir::DstFromSrc,
            field: ForwardOperandField::Base,
            dst: Some(ForwardDstLine::GlobalMaterialize { slot: 0, col: 0 }),
            src: Some(ForwardOperandLine::Source {
                window: 0,
                column: 0,
            }),
        }],
    })
    .unwrap();
    let mut desc: FwdVmDesc = unsafe { std::mem::zeroed() };
    desc.source_base[0] = input.as_ptr().cast_mut().cast();
    desc.source_stride_bytes[0] = 129 * 16;
    desc.dst_base[0] = unsafe { output.as_mut_ptr().add(1).cast() };
    desc.dst_stride_bytes[0] = 129 * 16;
    desc.count = 129;
    desc.layer_count = 1;
    desc.layers[0] = FwdVmLayer {
        program_offset: 0,
        instruction_count: 1,
    };
    desc.program[..program.len()].copy_from_slice(&program);
    let mut lowered = LoweredFwdVm {
        desc,
        lookup_additive_slot: None,
        decoder_fill_slot: None,
        constant_count: 0,
        source_window_count: 1,
        destination_slot_count: 1,
    };
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
    let actual = read_back(&output, PR::ZERO, &context);
    assert_eq!(actual[0], sentinel);
    assert_eq!(actual[130], sentinel);
    compare(&actual[1..130], &values[..129], "partial VM");
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
