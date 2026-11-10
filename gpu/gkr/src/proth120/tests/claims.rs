use std::collections::BTreeMap;
use std::sync::Arc;

use era_cudart::memory::memory_copy_async;
use field::Field;
use gpu_core::allocator::tracker::AllocationPlacement;
use prover::transcript::{Keccak256Seed, Keccak256Transcript, Transcript};
use worker::Worker;

use crate::proth120::base_layer_claims::{schedule_gather_base_claims_pr, BaseClaimGatherPr};
use crate::proth120::packed_merge::{
    launch_merge_claims_pr, schedule_packed_merge_pr_with_snapshots,
};
use crate::proth120::proof_layout::tests::{programs, HostSlab};
use crate::proth120::proof_layout::{ProofLayoutPr, ProofSlabPr};
use crate::upstream::{GKRAddress, PR};

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
    let config = prover::gkr::prover_config::ProofProfile::L1Wrap.prover_config(
        21,
        prover::definitions::SoundnessMode::PessimisticConjecture,
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
    assert_eq!(layer.final_step_eval_addresses.len(), 111);
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
    for full_extra in [
        coordinates,
        [
            PR::ZERO,
            PR::ONE,
            PR::new(PR::ORDER - 1),
            PR::new((1u128 << 80) + 19),
        ],
    ] {
        for pack_log2 in [3u32] {
            let extra = &full_extra[..pack_log2 as usize];
            let d_extra = upload(extra, &context);
            for count in [96usize, 10] {
                let d_claims = upload(&values[..count], &context);
                let expected = cpu_merge(&values[..count], extra);
                let canary = PR::new((1u128 << 90) + 37);
                let mut out = upload(&vec![canary; expected.len() + 2], &context);
                launch_merge_claims_pr(
                    &d_claims,
                    &d_extra,
                    pack_log2,
                    &mut out[1..expected.len() + 1],
                    &context,
                )
                .unwrap();
                let actual = read_back(&out, PR::ZERO, &context);
                assert_eq!(actual[0], canary);
                assert_eq!(actual[actual.len() - 1], canary);
                assert_eq!(
                    &actual[1..actual.len() - 1],
                    &expected,
                    "pack_log2={pack_log2} count={count}"
                );
            }
        }
    }
}

#[test]
#[cfg(not(no_cuda))]
fn pr_packed_merge_transcript_matches_cpu() {
    let context = make_context();
    let programs = programs();
    let config = prover::gkr::prover_config::ProofProfile::L1Wrap.prover_config(
        21,
        prover::definitions::SoundnessMode::PessimisticConjecture,
    );
    let layout = Arc::new(ProofLayoutPr::new(&programs, &config));
    let (addresses, values, map) = claim_map(&programs);
    let circuit = &programs.runtime_circuit;
    let memory_witness_count =
        circuit.memory_layout.total_width + circuit.witness_layout.total_width;
    let packed_memory_count = memory_witness_count.div_ceil(1 << config.pack_log2());
    let dense = cpu_dense(
        &map,
        circuit.memory_layout.total_width,
        circuit.witness_layout.total_width,
        circuit.generic_lookup_tables_width,
    );
    let point: Vec<_> = deterministic_columns(0, config.trace_len_log2)
        .into_iter()
        .flatten()
        .collect();
    let d_claims = upload(&values, &context);
    let d_point = upload(&point, &context);
    let worker = Worker::new_with_num_threads(4);
    assert_eq!(programs.runtime_circuit.trace_len.trailing_zeros(), 21);
    let raw_columns =
        prover::gkr::prover_config::pow_bits::total_base_oracle_columns(&programs.runtime_circuit);
    assert_eq!(raw_columns, 106);
    let cpu_bits = config.base_round().batching_pow_bits::<PR, PR>(
        config.security_level.security_bits(),
        config.whir_message_size_log2(),
        prover::gkr::prover_config::pow_bits::committed_base_oracle_columns(
            &programs.runtime_circuit,
            config.pack_log2(),
            config.merged_memory_and_witness(),
        ),
    );
    assert_eq!(cpu_bits, 13);
    for initial_seed in [[0u8; 32], [0xffu8; 32]] {
        for bits in [0, cpu_bits] {
            let mut host_seed = Keccak256Seed(initial_seed);
            let extra = prover::gkr::prover::transcript_utils::draw_random_field_els::<
                PR,
                PR,
                Keccak256Transcript,
            >(&mut host_seed, config.pack_log2());
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
            let mut expected_claims = cpu_merge(&dense[..memory_witness_count], &extra);
            expected_claims.extend(cpu_merge(&dense[memory_witness_count..], &extra));
            let mut expected_point = point.clone();
            expected_point.extend_from_slice(&extra);
            let mut seed = upload(&initial_seed, &context);
            let indices = BaseClaimGatherPr::new(
                &programs,
                &layout,
                circuit.memory_layout.total_width,
                circuit.witness_layout.total_width,
                circuit.generic_lookup_tables_width,
            );
            let gathered = schedule_gather_base_claims_pr(&d_claims, indices, &context).unwrap();
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
                u32::try_from(config.pack_log2()).expect("packing log exceeds u32"),
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
                output.memory_claims().as_ptr().add(packed_memory_count)
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
                &expected_claims[..packed_memory_count]
            );
            assert_eq!(
                layout.host_fields(host.bytes(), &layout.setup_claims),
                &expected_claims[packed_memory_count..]
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
            assert_eq!(handoff.claims.len(), expected_claims.len());
            assert_eq!(
                handoff.base_layer_point.len(),
                config.whir_message_size_log2()
            );
            assert_eq!(handoff.batching_challenge.len(), 1);
            assert_eq!(handoff.seed.len(), 32);
            println!("GKR_PACKED_MERGE bits={bits} nonce={expected_nonce} claim_map={} dense={} merged={} point={} seed_transitions=3", addresses.len(), dense.len(), expected_claims.len(), config.whir_message_size_log2());
        }
    }
}
