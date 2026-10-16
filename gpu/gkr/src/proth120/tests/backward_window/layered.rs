use std::collections::BTreeMap;
use std::sync::Arc;

use field::Field;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::UnsafeMutAccessor;
use prover::gkr::prover::gkr_backend::{GKRBackend, NaiveGKRBackend};
use prover::gkr::prover::sumcheck_loop::flatten_claim_point;
use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
use prover::gkr::prover::{EvaluationPointEntry, SumcheckRoundCoefficients};
use prover::transcript::{Keccak256Transcript, Transcript};
use worker::Worker;

use super::super::forward_vm::{forward_context, forward_fixture_full};
use super::super::read_back;
use crate::proth120::backward::{
    preflight_dr_tail_resources_pr, schedule_backward_pr, GKRBackwardStageSnapshotSinkPr,
};
use crate::proth120::forward::prepare_backward_handoff_pr;
use crate::upstream::{GKRAddress, PR};

fn mul(lhs: PR, rhs: PR) -> PR {
    *lhs.clone().mul_assign(&rhs)
}

fn add(lhs: PR, rhs: PR) -> PR {
    *lhs.clone().add_assign(&rhs)
}

fn sub(lhs: PR, rhs: PR) -> PR {
    *lhs.clone().sub_assign(&rhs)
}

fn slab_fields(slab: &[PR], range: &std::ops::Range<usize>) -> Vec<PR> {
    assert_eq!(range.start % 16, 0);
    assert_eq!(range.len() % 16, 0);
    slab[range.start / 16..range.end / 16].to_vec()
}

struct HostLayer {
    seed: [u8; 32],
    point: Vec<PR>,
    batching: PR,
    claims: BTreeMap<GKRAddress, PR>,
}

#[test]
#[cfg(not(no_cuda))]
fn pr_backward_layered_small() {
    let context = forward_context();
    let fixture = forward_fixture_full(&context);
    let programs = Arc::clone(&fixture.programs);
    let artifact = Arc::clone(&fixture.artifact);
    let seed_bytes: [u8; 32] = read_back(&fixture.seed, 0u8, &context).try_into().unwrap();
    let mut proof = fixture.proof;
    let handoff = prepare_backward_handoff_pr(fixture.gpu, fixture.seed, 4, &context).unwrap();
    let dr_tail_plan = preflight_dr_tail_resources_pr(&programs, 4, &context);
    let mut sink = GKRBackwardStageSnapshotSinkPr::default();
    let mut callbacks = Callbacks::new();
    let mut execution = schedule_backward_pr(
        handoff,
        fixture.top_bits.clone(),
        Arc::clone(&programs),
        &dr_tail_plan,
        &fixture.challenges,
        &mut proof,
        Some(UnsafeMutAccessor::new(&mut sink)),
        None,
        &mut callbacks,
        &context,
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    drop(callbacks);
    let slab = read_back(&proof.backing, PR::ZERO, &context);
    let (device_seed, device_point) = execution.final_device_seed_and_claim_point_mut();
    let final_seed = read_back(device_seed, 0u8, &context);
    let final_point = read_back(device_point, PR::ZERO, &context);
    let final_claims: BTreeMap<GKRAddress, PR> = execution
        .final_claim_addresses()
        .iter()
        .copied()
        .zip(read_back(execution.final_claims(), PR::ZERO, &context))
        .collect();
    drop(execution);
    let snapshots = sink.into_snapshots();

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
    let mut host_layers: Vec<(usize, HostLayer)> = vec![(
        initial_layer + 1,
        HostLayer {
            seed: seed.0,
            point: point.clone(),
            batching,
            claims: top_claims,
        },
    )];
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
        host_layers.push((
            layer_idx,
            HostLayer {
                seed: seed.0,
                point: flatten_claim_point(&points[&layer_idx]),
                batching,
                claims: claims[&layer_idx].clone(),
            },
        ));
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
        host_layers.push((
            layer_idx,
            HostLayer {
                seed: seed.0,
                point: flatten_claim_point(&points[&layer_idx]),
                batching,
                claims: claims[&layer_idx].clone(),
            },
        ));
    }

    let mut compared = 0usize;
    for layout in &proof.layout.backward_layers {
        let layer = layout.layer_idx;
        let host = &host_values[&layer];
        let coefficients = slab_fields(&slab, &layout.internal_round_coefficients);
        assert_eq!(
            host.internal_round_coefficients.len(),
            layout.sumcheck_num_rounds
        );
        for (round, expected) in host.internal_round_coefficients.iter().enumerate() {
            let SumcheckRoundCoefficients::Multilinear(expected) = expected else {
                panic!("Proth120 layer {layer} round {round} is not multilinear");
            };
            assert_eq!(
                &coefficients[4 * round..4 * round + 4],
                expected,
                "layer {layer} round {round} coefficients"
            );
        }
        let finals = slab_fields(&slab, &layout.final_step_evaluations);
        assert_eq!(
            layout.final_step_eval_addresses,
            host.final_step_evaluations
                .keys()
                .copied()
                .collect::<Vec<_>>(),
            "layer {layer} final evaluation addresses"
        );
        for (index, (address, expected)) in host.final_step_evaluations.iter().enumerate() {
            let degree = layout.final_step_eval_degree;
            assert_eq!(
                &finals[degree * index..degree * index + degree],
                expected.as_slice(),
                "layer {layer} final evaluation {address:?}"
            );
        }
        let extras = slab_fields(&slab, &layout.extra_evaluations);
        assert_eq!(
            layout.extra_evaluations_addresses,
            host.extra_evaluations_from_caching_relations
                .keys()
                .copied()
                .collect::<Vec<_>>(),
            "layer {layer} extra addresses"
        );
        assert_eq!(
            extras,
            host.extra_evaluations_from_caching_relations
                .values()
                .copied()
                .collect::<Vec<_>>(),
            "layer {layer} extra evaluations"
        );
        compared += coefficients.len() + finals.len() + extras.len();
    }
    assert_eq!(snapshots.len(), host_layers.len());
    for (snapshot, (layer_idx, host)) in snapshots.iter().zip(&host_layers) {
        assert_eq!(snapshot.layer_idx, *layer_idx, "snapshot order");
        assert_eq!(snapshot.seed, host.seed, "layer {layer_idx} seed");
        assert_eq!(snapshot.claim_point, host.point, "layer {layer_idx} point");
        assert_eq!(
            snapshot.batching_challenge, host.batching,
            "layer {layer_idx} batching"
        );
        assert_eq!(snapshot.claims, host.claims, "layer {layer_idx} claims");
    }
    assert_eq!(final_seed, seed.0, "seed after MAIN0");
    assert_eq!(
        final_point,
        flatten_claim_point(&points[&0]),
        "layer-0 point"
    );
    assert_eq!(final_claims.len(), 134);
    assert_eq!(final_claims, claims[&0], "layer-0 claim map");
    println!(
        "M6_BACKWARD_LAYERED layers={} snapshots={} slab_values={compared} final_claims={}",
        proof.layout.backward_layers.len(),
        snapshots.len(),
        final_claims.len()
    );
}
