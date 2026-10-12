use std::collections::BTreeMap;
use std::sync::Arc;

use era_cudart::memory::memory_copy_async;
use field::Field;
use gpu_core::allocator::tracker::AllocationPlacement;
use prover::transcript::{Keccak256Seed, Keccak256Transcript, Transcript};
use worker::Worker;

use crate::proth120::base_layer_claims::{dense_claim_indices, schedule_gather_base_claims_pr};
use crate::proth120::packed_challenges::split_challenges;
use crate::proth120::packed_merge::{
    launch_merge_claims_pr, schedule_packed_merge_pr_with_snapshots,
};
use crate::proth120::proof_layout::tests::{programs, HostSlab};
use crate::proth120::proof_layout::{ProofLayoutPr, ProofSlabPr};
use crate::upstream::{GKRAddress, SecurityLevel, PR};

use super::{deterministic_columns, make_context, read_back, upload};

fn cpu_merge(input: &[PR], extra: &[PR]) -> Vec<PR> {
    input
        .chunks(1 << extra.len())
        .map(|chunk| {
            let mut values = chunk.to_vec();
            values.resize(1 << extra.len(), PR::ZERO);
            for coordinate in extra {
                values = values
                    .as_chunks::<2>()
                    .0
                    .iter()
                    .map(|pair| {
                        let mut value = pair[1];
                        value.sub_assign(&pair[0]);
                        value.mul_assign(coordinate);
                        value.add_assign(&pair[0]);
                        value
                    })
                    .collect();
            }
            assert_eq!(values.len(), 1);
            values[0]
        })
        .collect()
}

fn claim_map(
    programs: &crate::proth120::programs::GkrProgramsPr,
) -> (Vec<GKRAddress>, Vec<PR>, BTreeMap<GKRAddress, PR>) {
    let config = prover::gkr::prover_config::example_configs::evm_production_packed_prover_config(
        SecurityLevel::Sec100,
    );
    let layout = ProofLayoutPr::new(programs, &config);
    let layer = layout
        .backward_layers
        .iter()
        .find(|layer| layer.layer_idx == 0)
        .unwrap();
    let addresses: Vec<_> = layer
        .final_step_eval_addresses
        .iter()
        .chain(&layer.extra_evaluations_addresses)
        .copied()
        .collect();
    assert_eq!(layer.final_step_eval_addresses.len(), 119);
    assert_eq!(layer.extra_evaluations_addresses.len(), 15);
    let values: Vec<_> = deterministic_columns(0, addresses.len())
        .into_iter()
        .flatten()
        .collect();
    let map = addresses
        .iter()
        .copied()
        .zip(values.iter().copied())
        .collect();
    (addresses, values, map)
}

fn cpu_dense(
    map: &BTreeMap<GKRAddress, PR>,
    memory: usize,
    witness: usize,
    setup: usize,
) -> Vec<PR> {
    (0..memory)
        .map(|column| map[&GKRAddress::BaseLayerMemory(column)])
        .chain((0..witness).map(|column| map[&GKRAddress::BaseLayerWitness(column)]))
        .chain((0..setup).map(|column| map[&GKRAddress::Setup(column)]))
        .collect()
}

#[test]
#[cfg(not(no_cuda))]
fn pr_merge_claims_matches_cpu() {
    let context = make_context();
    let values: Vec<_> = deterministic_columns(0, 118)
        .into_iter()
        .flatten()
        .collect();
    let coordinates = [values[114], values[115], values[116], values[117]];
    for extra in [
        coordinates,
        [
            PR::ZERO,
            PR::ONE,
            PR::new(PR::ORDER - 1),
            PR::new((1u128 << 80) + 19),
        ],
    ] {
        let d_extra = upload(&extra, &context);
        for count in [1usize, 10, 15, 16, 17, 104] {
            let d_claims = upload(&values[..count], &context);
            let expected = cpu_merge(&values[..count], &extra);
            let canary = PR::new((1u128 << 90) + 37);
            let mut out = upload(&vec![canary; expected.len() + 2], &context);
            launch_merge_claims_pr(
                &d_claims,
                &d_extra,
                4,
                &mut out[1..expected.len() + 1],
                &context,
            )
            .unwrap();
            let actual = read_back(&out, PR::ZERO, &context);
            assert_eq!(actual[0], canary);
            assert_eq!(actual[actual.len() - 1], canary);
            assert_eq!(&actual[1..actual.len() - 1], &expected, "count={count}");
        }
    }
}

#[test]
#[cfg(not(no_cuda))]
fn pr_gather_base_claims_small() {
    let context = make_context();
    let (_, programs) = super::forward_vm::small_programs();
    let circuit = &programs.runtime_circuit;
    let (addresses, values, map) = claim_map(&programs);
    let d_claims = upload(&values, &context);
    let gathered = schedule_gather_base_claims_pr(
        &d_claims,
        &addresses,
        circuit.memory_layout.total_width,
        circuit.witness_layout.total_width,
        circuit.generic_lookup_tables_width,
        &context,
    )
    .unwrap();
    let expected = cpu_dense(&map, 38, 66, 10);
    assert_eq!(read_back(&gathered.values, PR::ZERO, &context), expected);
    assert_eq!(gathered.memory_witness_count, 104);
    assert_eq!(gathered.setup_count, 10);
    let missing = std::panic::catch_unwind(|| dense_claim_indices(&[], 1, 0, 0)).unwrap_err();
    let message = missing.downcast_ref::<String>().unwrap();
    assert!(message.contains("Proth120 base claim is missing"));
    let duplicate = std::panic::catch_unwind(|| {
        dense_claim_indices(&[GKRAddress::Setup(0), GKRAddress::Setup(0)], 0, 0, 1)
    })
    .unwrap_err();
    let message = duplicate
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| duplicate.downcast_ref::<&str>().copied())
        .unwrap();
    assert!(message.contains("Proth120 claim map has duplicate addresses"));
    println!("M6_GATHER claim_map=119+15 dense=38+66+10");
}

#[test]
#[cfg(not(no_cuda))]
fn pr_packed_merge_transcript_matches_cpu() {
    let context = make_context();
    let programs = programs();
    let config = prover::gkr::prover_config::example_configs::evm_production_packed_prover_config(
        SecurityLevel::Sec100,
    );
    let layout = Arc::new(ProofLayoutPr::new(&programs, &config));
    let (addresses, values, map) = claim_map(&programs);
    let dense = cpu_dense(&map, 38, 66, 10);
    let point: Vec<_> = deterministic_columns(0, 22).into_iter().flatten().collect();
    let d_claims = upload(&values, &context);
    let d_point = upload(&point, &context);
    let worker = Worker::new_with_num_threads(4);
    assert_eq!(programs.runtime_circuit.trace_len.trailing_zeros(), 22);
    let raw_columns =
        prover::gkr::prover_config::pow_bits::total_base_oracle_columns(&programs.runtime_circuit);
    assert_eq!(raw_columns, 114);
    let cpu_bits = prover::gkr::prover_config::pow_bits::batched_proximity_check_pow_bits(
        config.security_level.security_bits(),
        22,
        5,
        raw_columns,
    );
    assert_eq!(cpu_bits, 11);
    for initial_seed in [[0u8; 32], [0xffu8; 32]] {
        for bits in [0, cpu_bits] {
            let mut host_seed = Keccak256Seed(initial_seed);
            let extra = prover::gkr::prover::transcript_utils::draw_random_field_els::<
                PR,
                PR,
                Keccak256Transcript,
            >(&mut host_seed, 4);
            let mut expected_seeds = vec![host_seed.0];
            let (next_seed, expected_nonce) =
                <Keccak256Transcript as Transcript<PR, PR>>::search_pow(&host_seed, bits, &worker);
            host_seed = next_seed;
            expected_seeds.push(host_seed.0);
            let batching = prover::gkr::prover::transcript_utils::draw_random_field_els::<
                PR,
                PR,
                Keccak256Transcript,
            >(&mut host_seed, 1);
            expected_seeds.push(host_seed.0);
            let mut expected_claims = cpu_merge(&dense[..104], &extra);
            expected_claims.extend(cpu_merge(&dense[104..], &extra));
            let mut expected_point = point.clone();
            expected_point.extend_from_slice(&extra);
            let mut seed = upload(&initial_seed, &context);
            let gathered =
                schedule_gather_base_claims_pr(&d_claims, &addresses, 38, 66, 10, &context)
                    .unwrap();
            let mut proof = ProofSlabPr::new(Arc::clone(&layout), &context).unwrap();
            let mut snapshots: Vec<_> = (0..3)
                .map(|_| {
                    context
                        .alloc::<u8>(32, AllocationPlacement::BestFit)
                        .unwrap()
                })
                .collect();
            let mut output = schedule_packed_merge_pr_with_snapshots(
                gathered,
                &mut seed,
                &d_point,
                4,
                bits,
                &mut proof,
                &context,
                |index, seed| {
                    memory_copy_async(&mut snapshots[index], seed, context.get_exec_stream())
                },
            )
            .unwrap();
            for (index, snapshot) in snapshots.iter().enumerate() {
                assert_eq!(
                    read_back(snapshot, 0u8, &context),
                    expected_seeds[index],
                    "seed transition {index}, bits={bits}"
                );
            }
            assert_eq!(
                read_back(output.merged_claims(), PR::ZERO, &context),
                expected_claims
            );
            assert_eq!(
                read_back(output.evaluation_point(), PR::ZERO, &context),
                expected_point
            );
            assert_eq!(
                read_back(output.batching_challenge(), PR::ZERO, &context),
                batching
            );
            assert_eq!(read_back(output.seed(), 0u8, &context), host_seed.0);
            assert_eq!(output.setup_claims().as_ptr(), unsafe {
                output.memory_claims().as_ptr().add(7)
            });
            let mut host = HostSlab::new(layout.bytes_len());
            memory_copy_async(
                host.bytes_mut(),
                unsafe { proof.backing.transmute::<u8>() },
                context.get_exec_stream(),
            )
            .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            assert_eq!(
                layout.host_fields(host.bytes(), &layout.memory_claims),
                &expected_claims[..7]
            );
            assert_eq!(
                layout.host_fields(host.bytes(), &layout.setup_claims),
                &expected_claims[7..]
            );
            assert_eq!(
                layout.host_fields(host.bytes(), &layout.evaluation_point),
                expected_point
            );
            assert_eq!(
                layout.host_fields(host.bytes(), &layout.batching_challenge),
                batching
            );
            assert_eq!(
                &host.bytes()[layout.intermediate_transcript_seed.clone()],
                &host_seed.0
            );
            assert_eq!(
                u64::from_ne_bytes(
                    host.bytes()[layout.batched_proximity_check_pow_nonce.clone()]
                        .try_into()
                        .unwrap()
                ),
                expected_nonce
            );
            let handoff = output.whir_handoff();
            assert_eq!(handoff.claims.len(), 8);
            assert_eq!(handoff.base_layer_point.len(), 26);
            assert_eq!(handoff.batching_challenge.len(), 1);
            assert_eq!(handoff.seed.len(), 32);
            println!("M6_PACKED_MERGE bits={bits} nonce={expected_nonce} claim_map=134 dense=114 merged=7+1 point=26 seed_transitions=3");
        }
    }
}

use super::forward_vm::{forward_context, small_programs};
use prover::gkr::prover::gkr_backend::{GKRBackend, NaiveGKRBackend};
use prover::gkr::prover::sumcheck_loop::flatten_claim_point;
use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
use prover::gkr::prover::EvaluationPointEntry;
use prover::gkr::sumcheck::access_and_fold::GKRStorage as CpuStorage;

struct ScheduleFixturePr {
    artifact: Arc<crate::upstream::GKRCircuitArtifact<PR>>,
    cpu: CpuStorage<PR, PR>,
    proof: ProofSlabPr,
    seed_bytes: [u8; 32],
    host_challenges: Vec<PR>,
    lookup_nonce: u64,
    external: prover::definitions::GKRExternalChallenges<PR, PR>,
    lookup: [PR; 2],
    top_bits: Vec<u32>,
    config: prover::gkr::prover_config::ProverConfig,
    output: crate::proth120::GkrOutputPr,
}
fn schedule_fixture_full(context: &gpu_prover_context::ProverContext) -> ScheduleFixturePr {
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
        let driver =
            prover::gkr::witness_gen::family_circuits::build_unified_table_driver::<PR>(&binary);
        let decoder = vec![None; artifact.total_tables_size - artifact.offset_for_decoder_table];
        prover::gkr::prover::setup::GKRSetup::<PR>::construct(&driver, &decoder, rows, &artifact)
    };
    let setup_host =
        Arc::new(crate::setup::L1WrapSetupHost::precompute(&setup, 4, cfg, context).unwrap());
    let mut d_setup = crate::setup::PackedSetupSource::new(setup_host, context).unwrap();
    let transfer = gpu_prover_context::transfer::single_shot_h2d(
        |transfer| d_setup.schedule_transfer(transfer, context),
        context,
    )
    .unwrap();
    transfer.ensure_transferred(context).unwrap();
    let top_bits = vec![1u32; artifact.memory_layout.teardown_sets.len()];
    let d_top = upload(&top_bits, context);
    let cap = upload(&super::deterministic_words(8, 73), context);
    let mut seed = upload(&[0u8; 32], context);
    let challenges = super::derive(
        &mut seed,
        &super::deterministic_mode(0x2_0000_0003),
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
        witness[63][*index as usize].add_assign(&PR::ONE);
    }
    for index in timestamp.iter().flatten() {
        witness[64][*index as usize].add_assign(&PR::ONE);
    }
    for index in generic.iter().flatten() {
        witness[65][*index as usize].add_assign(&PR::ONE);
    }
    witness[65][artifact.offset_for_decoder_table].add_assign(&PR::new((rows / 2) as u128));
    let mut raw = TraceHolder::new_without_cosets(
        log_rows,
        cfg.log_lde_factor,
        cfg.log_values_per_leaf,
        cfg.cap_log,
        memory.len() + witness.len(),
        TreesCacheMode::CacheNone,
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
    let base = PackedCosetRecomputeOracle::from_uploaded(raw, 4, cfg, context).unwrap();
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
        DeviceMatrix::new(&raw[(38 + 63) * rows..(38 + 66) * rows], rows),
    );
    let mut config =
        prover::gkr::prover_config::example_configs::evm_production_packed_prover_config(
            crate::upstream::SecurityLevel::Sec100,
        );
    config.trace_len_log2 = log_rows as usize;
    let mut proof = crate::proth120::proof_layout::ProofSlabPr::new(
        Arc::new(crate::proth120::proof_layout::ProofLayoutPr::new(
            &programs, &config,
        )),
        context,
    )
    .unwrap();
    let seed_bytes = read_back(&seed, 0u8, context).try_into().unwrap();
    let lookup_nonce = read_back(challenges.nonce(), 0u64, context)[0];
    let dr_tail_plan =
        crate::proth120::backward::preflight_dr_tail_resources_pr(&programs, 4, context);
    let mut callbacks = gpu_core::primitives::callbacks::Callbacks::new();
    let batching_pow_bits = prover::gkr::prover_config::pow_bits::batched_proximity_check_pow_bits(
        config.security_level.security_bits(),
        log_rows as usize,
        config.whir_schedule.base_lde_factor.trailing_zeros() as usize,
        prover::gkr::prover_config::pow_bits::total_base_oracle_columns(&artifact),
    );
    assert_eq!(batching_pow_bits, 11);
    let output = crate::proth120::schedule_gkr(
        Arc::clone(&programs),
        &base,
        &d_setup,
        inputs,
        &top_bits,
        &challenges,
        &config,
        batching_pow_bits,
        seed,
        &mut proof,
        &dr_tail_plan,
        None,
        &mut callbacks,
        context,
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    drop(callbacks);
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
    ScheduleFixturePr {
        artifact,
        cpu,
        proof,
        seed_bytes,
        host_challenges,
        lookup_nonce,
        external,
        lookup: [lookup_alpha, lookup_additive_part],
        top_bits,
        config,
        output,
    }
}
fn mul(lhs: PR, rhs: PR) -> PR {
    *lhs.clone().mul_assign(&rhs)
}

fn add(lhs: PR, rhs: PR) -> PR {
    *lhs.clone().add_assign(&rhs)
}

fn sub(lhs: PR, rhs: PR) -> PR {
    *lhs.clone().sub_assign(&rhs)
}

#[test]
#[cfg(not(no_cuda))]
fn pr_schedule_gkr_small_shape() {
    let context = forward_context();
    let mut fixture = schedule_fixture_full(&context);
    let artifact = Arc::clone(&fixture.artifact);
    let seed_bytes = fixture.seed_bytes;
    let worker = Worker::new_with_num_threads(8);
    let pool = prover::allocation_pool::GenericAllocationPool::<PR, PR>::with_retain(false);
    let backend = NaiveGKRBackend;
    let mut cpu = fixture.cpu;
    let trace_len = artifact.trace_len;
    let trace_log = trace_len.trailing_zeros() as usize;
    let (initial_layer, dr_inputs) =
        <NaiveGKRBackend as GKRBackend<PR, PR>>::dimension_reduction_forward(
            &backend, &mut cpu, &artifact, trace_log, 4, &pool, &worker,
        );
    let output_map = &dr_inputs[&initial_layer];
    let final_explicit_evaluations: BTreeMap<_, _> = output_map
        .iter()
        .map(|(kind, io)| {
            let values: Vec<Vec<PR>> = io
                .output
                .iter()
                .map(|address| cpu.get_ext_poly(*address).to_vec())
                .collect();
            (*kind, <[Vec<PR>; 2]>::try_from(values).unwrap())
        })
        .collect();
    let explicit: Vec<PR> = output_map
        .values()
        .flat_map(|io| io.output.iter())
        .flat_map(|address| cpu.get_ext_poly(*address).iter().copied())
        .collect();
    assert_eq!(explicit.len(), 160);
    let mut seed = <Keccak256Transcript as Transcript<PR, PR>>::commit_initial_u32(&[]);
    seed.0 = seed_bytes;
    commit_field_els::<PR, PR, Keccak256Transcript>(&mut seed, &explicit);
    let mut draws = draw_random_field_els::<PR, PR, Keccak256Transcript>(&mut seed, 5);
    let mut batching = draws.pop().unwrap();
    let point = draws;
    let mut claims: BTreeMap<usize, BTreeMap<GKRAddress, PR>> = BTreeMap::new();
    let mut points: BTreeMap<usize, Vec<EvaluationPointEntry<PR>>> = BTreeMap::new();
    let top_claims = output_map
        .values()
        .flat_map(|io| io.output.iter().copied())
        .map(|address| {
            let value =
                cpu.get_ext_poly(address)
                    .iter()
                    .enumerate()
                    .fold(PR::ZERO, |sum, (row, value)| {
                        let weight = point.iter().enumerate().fold(PR::ONE, |weight, (bit, x)| {
                            mul(
                                weight,
                                if row & (1 << bit) == 0 {
                                    sub(PR::ONE, *x)
                                } else {
                                    *x
                                },
                            )
                        });
                        add(sum, mul(*value, weight))
                    });
            (address, value)
        })
        .collect::<BTreeMap<_, _>>();
    claims.insert(initial_layer + 1, top_claims.clone());
    points.insert(
        initial_layer + 1,
        point
            .iter()
            .map(|point| EvaluationPointEntry::Coordinate { point: *point })
            .collect(),
    );
    let mut host_values = BTreeMap::new();
    let dr_max_rounds = 4 + dr_inputs.len() - 1;
    let dr_max_polys = dr_inputs
        .values()
        .map(|layer| {
            let mut addresses: Vec<_> = layer.values().flat_map(|io| io.inputs.iter()).collect();
            addresses.sort();
            addresses.dedup();
            addresses.len()
        })
        .max()
        .unwrap();
    let mut buffers = <NaiveGKRBackend as GKRBackend<PR, PR>>::make_dim_reducing_work_buffers(
        &backend,
        dr_max_rounds,
        dr_max_polys,
        &pool,
        &worker,
    );
    let mut reduced_log = 4usize;
    for (layer_idx, layer) in dr_inputs.into_iter().rev() {
        let values = <NaiveGKRBackend as GKRBackend<PR, PR>>::dimension_reducing_sumcheck_for_layer::<
            Keccak256Transcript,
        >(
            &backend,
            &[],
            layer_idx,
            &layer,
            &mut points,
            &mut claims,
            &mut cpu,
            &mut batching,
            &mut seed,
            1 << reduced_log,
            &pool,
            &worker,
            &mut buffers,
        );
        host_values.insert(layer_idx, values);
        reduced_log += 1;
    }
    assert_eq!(1 << reduced_log, trace_len);
    let shift = if fixture.top_bits.is_empty() {
        0
    } else {
        prover::gkr::high_bits_offset_for_inits_and_teardowns::<2>(trace_len)
    };
    for (layer_idx, layer) in artifact.layers.iter().enumerate().rev() {
        let values = <NaiveGKRBackend as GKRBackend<PR, PR>>::evaluate_same_size_sumcheck_for_layer::<
            Keccak256Transcript,
        >(
            &backend,
            layer_idx,
            layer,
            &mut points,
            &mut claims,
            &mut cpu,
            &mut batching,
            trace_len,
            fixture.lookup[0],
            fixture.lookup[1],
            &fixture.top_bits,
            shift,
            &fixture.external,
            &fixture.config,
            &mut seed,
            &pool,
            &worker,
        );
        host_values.insert(layer_idx, values);
    }

    let point = flatten_claim_point(&points[&0]);
    let extra = draw_random_field_els::<PR, PR, Keccak256Transcript>(&mut seed, 4);
    let memory_claims: Vec<_> = (0..artifact.memory_layout.total_width)
        .map(GKRAddress::BaseLayerMemory)
        .chain((0..artifact.witness_layout.total_width).map(GKRAddress::BaseLayerWitness))
        .map(|address| claims[&0][&address])
        .collect();
    let setup_claims: Vec<_> = (0..artifact.generic_lookup_tables_width)
        .map(GKRAddress::Setup)
        .map(|address| claims[&0][&address])
        .collect();
    let merged_claims = (
        cpu_merge(&memory_claims, &extra),
        cpu_merge(&setup_claims, &extra),
    );
    assert_eq!(
        prover::gkr::prover_config::pow_bits::batched_proximity_check_pow_bits(
            SecurityLevel::Sec100.security_bits(),
            trace_log,
            5,
            prover::gkr::prover_config::pow_bits::total_base_oracle_columns(&artifact)
        ),
        11
    );
    let (next_seed, nonce) =
        <Keccak256Transcript as Transcript<PR, PR>>::search_pow(&seed, 11, &worker);
    seed = next_seed;
    let batching_challenge = draw_random_field_els::<PR, PR, Keccak256Transcript>(&mut seed, 1)[0];
    let products: Vec<[PR; 2]> = [
        crate::upstream::OutputType::PermutationProduct,
        crate::upstream::OutputType::InitsAndTeardownsProduct,
    ]
    .map(|kind| {
        final_explicit_evaluations[&kind]
            .each_ref()
            .map(|values| values.iter().copied().fold(PR::ONE, mul))
    })
    .into_iter()
    .collect();
    let grand_product = mul(
        mul(products[0][1], products[0][0].inverse().unwrap()),
        mul(products[1][1], products[1][0].inverse().unwrap()),
    );
    let expected = crate::proth120::proof_layout::M6ProofFields {
        external_challenges: fixture.external,
        lookup_challenges_pow_nonce: fixture.lookup_nonce,
        final_explicit_evaluations,
        sumcheck_intermediate_values: host_values,
        grand_product_accumulator_computed: grand_product,
        batched_proximity_check_pow_nonce: nonce,
        merged_claims,
        evaluation_point: point.into_iter().chain(extra).collect(),
        batching_challenge,
        intermediate_transcript_seed: seed.0,
    };
    let layout = &fixture.proof.layout;
    let mut host = HostSlab::new(layout.bytes_len());
    memory_copy_async(
        host.bytes_mut(),
        unsafe { fixture.proof.backing.transmute::<u8>() },
        context.get_exec_stream(),
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    let actual = layout.parse_m6_fields(host.bytes());
    crate::proth120::proof_layout::tests::assert_m6_fields_equal(&actual, &expected);
    assert_eq!(
        layout.host_fields(host.bytes(), &layout.external_challenges),
        fixture.host_challenges
    );
    assert_eq!(
        read_back(fixture.output.memory_claims(), PR::ZERO, &context),
        expected.merged_claims.0
    );
    assert_eq!(
        read_back(fixture.output.setup_claims(), PR::ZERO, &context),
        expected.merged_claims.1
    );
    assert_eq!(
        read_back(fixture.output.evaluation_point(), PR::ZERO, &context),
        expected.evaluation_point
    );
    assert_eq!(
        read_back(fixture.output.batching_challenge(), PR::ZERO, &context),
        [expected.batching_challenge]
    );
    assert_eq!(
        read_back(fixture.output.seed(), 0u8, &context),
        expected.intermediate_transcript_seed
    );
    println!(
        "M6_FACADE layers={} outputs=160 claims=8 point=26 nonce={} seed={:?}",
        expected.sumcheck_intermediate_values.len(),
        nonce,
        seed.0
    );
}
