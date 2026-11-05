use std::collections::BTreeMap;

use era_cudart::slice::DeviceSlice;
use field::Field;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::PR;
use gpu_gkr_compiler::backward::R0Kernel;
use gpu_gkr_compiler::window::partition::R0PartitionPlan;
use gpu_prover_context::ProverContext;
use prover::gkr::prover::{
    EvaluationPointEntry, GKRBackend, NaiveGKRBackend, SumcheckRoundCoefficients,
};
use prover::transcript::{Keccak256Transcript, Transcript};
use rand::rngs::StdRng;
use rand::SeedableRng;
use worker::Worker;

use super::super::forward_vm::{forward_context, forward_fixture_full, ForwardFixturePr};
use super::super::{read_back, upload};
use super::random_canonical;
use crate::backward::{make_eq_sizes, GKR_EQ_GROUP_TABLE_LEN};
use crate::proth120::backward::banks::{
    schedule_coefficient_bank_fill_pr, schedule_coefficient_tables_upload_pr, CoefficientBankPr,
    CoefficientTablesHostPr, CoefficientTablesPr,
};
use crate::proth120::backward::eq::{
    launch_eq_high_low_pr, resolve_active_eq_slot_pr, BackwardScratchPr,
};
use crate::proth120::backward::window::binding::WindowRuntimeScratchPr;
use crate::proth120::backward::window::{
    bind_r0_pr, launch_r0_pr_with, launch_window_tail_pr, r0_partials_len_pr, WindowTailStatePr,
    PR_WINDOW_TAIL_TENSOR_CELLS,
};
use crate::proth120::programs::GkrProgramsPr;
use crate::upstream::GKRAddress;
use crate::GpuGKRStorage;

const FOLDING_STEPS: usize =
    prover::gkr::prover_config::example_configs::l1_wrap_2p21::TRACE_LEN_LOG2;
const WINDOW_ROUNDS: usize = 3;

#[derive(Debug, PartialEq)]
struct WindowRun {
    tensor: Vec<PR>,
    coeffs: Vec<PR>,
    challenges: Vec<PR>,
    seed: Vec<u8>,
    claim: PR,
    eq_prefactor: PR,
    eq_low_before: Vec<PR>,
    eq_low_after: Vec<PR>,
}

struct LayerInputs {
    layer: usize,
    point: Vec<PR>,
    batching: PR,
    seed: [u8; 32],
    claims: BTreeMap<GKRAddress, PR>,
    combined_claim: PR,
}

fn mul(lhs: PR, rhs: &PR) -> PR {
    *lhs.clone().mul_assign(rhs)
}

fn host_eq(point: &[PR]) -> Vec<PR> {
    let mut eq = vec![PR::ONE];
    for coordinate in point {
        let one_minus = *PR::ONE.clone().sub_assign(coordinate);
        let half = eq.len();
        let mut next = vec![PR::ZERO; 2 * half];
        for (index, value) in eq.iter().enumerate() {
            next[index] = mul(*value, &one_minus);
            next[index + half] = mul(*value, coordinate);
        }
        eq = next;
    }
    eq
}

fn host_mle_many(columns: &[&[PR]], eq: &[PR]) -> Vec<PR> {
    let threads = std::thread::available_parallelism()
        .map_or(4, |count| count.get())
        .min(32);
    let mut results = vec![PR::ZERO; columns.len()];
    std::thread::scope(|scope| {
        for (chunk_index, chunk) in results
            .chunks_mut(columns.len().div_ceil(threads).max(1))
            .enumerate()
        {
            let start = chunk_index * columns.len().div_ceil(threads).max(1);
            scope.spawn(move || {
                for (offset, result) in chunk.iter_mut().enumerate() {
                    let column = columns[start + offset];
                    assert_eq!(column.len(), eq.len());
                    let mut sum = PR::ZERO;
                    for (value, weight) in column.iter().zip(eq) {
                        sum.add_assign(&mul(*value, weight));
                    }
                    *result = sum;
                }
            });
        }
    });
    results
}

fn layer_inputs(
    programs: &GkrProgramsPr,
    fixture_cpu: &prover::gkr::sumcheck::access_and_fold::GKRStorage<PR, PR>,
    layer: usize,
    rng: &mut StdRng,
) -> LayerInputs {
    let point: Vec<PR> = (0..FOLDING_STEPS).map(|_| random_canonical(rng)).collect();
    let batching = random_canonical(rng);
    let seed = std::array::from_fn(|index| (index * 13 + layer * 7 + 1) as u8);
    let eq = host_eq(&point);
    let addresses: Vec<GKRAddress> = programs.backward_layers[layer]
        .claims
        .iter()
        .map(|(_, address)| *address)
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect();
    let columns: Vec<&[PR]> = addresses
        .iter()
        .map(|address| {
            fixture_cpu
                .try_get_base_poly(*address)
                .or_else(|| fixture_cpu.try_get_ext_poly(*address))
                .unwrap_or_else(|| panic!("CPU storage lacks {address:?}"))
        })
        .collect();
    let values = host_mle_many(&columns, &eq);
    let claims: BTreeMap<GKRAddress, PR> = addresses.into_iter().zip(values).collect();
    let mut combined_claim = PR::ZERO;
    for (offset, address) in &programs.backward_layers[layer].claims {
        combined_claim.add_assign(&mul(batching.pow(*offset as u32), &claims[address]));
    }
    LayerInputs {
        layer,
        point,
        batching,
        seed,
        claims,
        combined_claim,
    }
}

#[allow(clippy::too_many_arguments)]
fn run_window(
    context: &ProverContext,
    storage: &GpuGKRStorage<PR, PR>,
    programs: &GkrProgramsPr,
    tables: &CoefficientTablesPr,
    challenges: *const PR,
    inputs: &LayerInputs,
    plan: Option<&R0PartitionPlan>,
    kernel: R0Kernel,
    poison: u128,
) -> WindowRun {
    let mut point_and_batching = inputs.point.clone();
    point_and_batching.push(inputs.batching);
    let point = upload(&point_and_batching, context);
    let mut bank = CoefficientBankPr::new(tables, inputs.layer, context).unwrap();
    schedule_coefficient_bank_fill_pr(
        tables,
        &mut bank,
        challenges,
        unsafe { point.as_ptr().add(FOLDING_STEPS) },
        context,
    )
    .unwrap();
    let mut scratch = BackwardScratchPr::new(context).unwrap();
    let mut eq_low: DeviceAllocation<PR> = context
        .alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::BestFit)
        .unwrap();
    let parts = plan.map_or(1, |plan| plan.parts.len());
    let mut partials = upload(
        &vec![PR::from_u128_with_reduction(poison); r0_partials_len_pr(1 << FOLDING_STEPS, parts)],
        context,
    );
    let challenge_count = FOLDING_STEPS - WINDOW_ROUNDS;
    launch_eq_high_low_pr(
        point.as_ptr(),
        WINDOW_ROUNDS as u32,
        challenge_count as u32,
        scratch.eq_high_0(),
        scratch.eq_high_1(),
        eq_low.as_mut_ptr(),
        context,
    )
    .unwrap();
    let eq_low_before = read_back(&eq_low, PR::ZERO, context);
    let window = bind_r0_pr(
        &programs.r0[inputs.layer],
        plan,
        storage,
        FOLDING_STEPS,
        WindowRuntimeScratchPr {
            eq_high: scratch.eq_high.as_ptr(),
            eq_low: eq_low.as_ptr(),
            partials: partials.as_mut_ptr(),
            partials_capacity: partials.len(),
        },
        bank.r0(),
    )
    .unwrap();
    launch_r0_pr_with(&window, kernel, context).unwrap();
    let mut seed = upload(&inputs.seed, context);
    let mut claim = upload(&[inputs.combined_claim], context);
    let mut eq_prefactor = upload(&[PR::ONE], context);
    let mut coeffs = upload(&[PR::ZERO; 4 * WINDOW_ROUNDS], context);
    let mut challenges_out = upload(&[PR::ZERO; WINDOW_ROUNDS], context);
    let eq_sizes = make_eq_sizes(challenge_count);
    let (active_eq_slot_base, active_eq_size_before_fold) = resolve_active_eq_slot_pr(
        &eq_sizes,
        eq_low.as_mut_ptr(),
        scratch.eq_high_0(),
        scratch.eq_high_1(),
    );
    launch_window_tail_pr(
        &WindowTailStatePr {
            partials: partials.as_ptr(),
            row_tiles: window.reduction_tiles,
            reduced_tensor: window.reduced_tensor,
            prev_claim_coords: point.as_ptr(),
            seed: seed.as_mut_ptr(),
            claim: claim.as_mut_ptr(),
            eq_prefactor: eq_prefactor.as_mut_ptr(),
            coeffs_out: coeffs.as_mut_ptr(),
            challenges_out: challenges_out.as_mut_ptr(),
            active_eq_slot_base,
            active_eq_size_before_fold,
        },
        context,
    )
    .unwrap();
    let tensor = read_back(
        unsafe { DeviceSlice::from_raw_parts(window.reduced_tensor, PR_WINDOW_TAIL_TENSOR_CELLS) },
        PR::ZERO,
        context,
    );
    WindowRun {
        tensor,
        coeffs: read_back(&coeffs, PR::ZERO, context),
        challenges: read_back(&challenges_out, PR::ZERO, context),
        seed: read_back(&seed, 0u8, context),
        claim: read_back(&claim, PR::ZERO, context)[0],
        eq_prefactor: read_back(&eq_prefactor, PR::ZERO, context)[0],
        eq_low_before,
        eq_low_after: read_back(&eq_low, PR::ZERO, context),
    }
}

fn check_window_against_host(inputs: &LayerInputs, run: &WindowRun) {
    let mut seed = <Keccak256Transcript as Transcript<PR, PR>>::commit_initial_u32(&[]);
    seed.0 = inputs.seed;
    for round in 0..WINDOW_ROUNDS {
        <Keccak256Transcript as Transcript<PR, PR>>::commit_extension_field_elements(
            &mut seed,
            &run.coeffs[4 * round..4 * round + 4],
        );
        let mut drawn = [PR::ZERO];
        <Keccak256Transcript as Transcript<PR, PR>>::draw_random_field_elements(
            &mut seed, &mut drawn,
        );
        assert_eq!(
            drawn[0], run.challenges[round],
            "layer {} round {round} challenge",
            inputs.layer
        );
    }
    assert_eq!(run.seed, seed.0.to_vec(), "layer {} seed", inputs.layer);
    let last = &run.coeffs[4 * (WINDOW_ROUNDS - 1)..];
    let challenge = run.challenges[WINDOW_ROUNDS - 1];
    let mut claim = last[3];
    for coefficient in last[..3].iter().rev() {
        claim = mul(claim, &challenge);
        claim.add_assign(coefficient);
    }
    assert_eq!(run.claim, claim, "layer {} claim", inputs.layer);
    let previous = inputs.point[WINDOW_ROUNDS - 1];
    let mut eq = mul(challenge, &previous);
    eq.add_assign(&mul(
        *PR::ONE.clone().sub_assign(&challenge),
        PR::ONE.clone().sub_assign(&previous),
    ));
    assert_eq!(run.eq_prefactor, eq, "layer {} eq prefactor", inputs.layer);
    let eq_sizes = make_eq_sizes(FOLDING_STEPS - WINDOW_ROUNDS);
    assert!(eq_sizes.low > 0);
    let folded = 1usize << (eq_sizes.low - 1);
    for index in 0..folded {
        let mut expected = run.eq_low_before[2 * index];
        expected.add_assign(&run.eq_low_before[2 * index + 1]);
        assert_eq!(
            run.eq_low_after[index], expected,
            "layer {} eq fold {index}",
            inputs.layer
        );
    }
}

#[test]
#[cfg(not(no_cuda))]
fn pr_r0_window_matches_host_sumcheck_small() {
    let context = forward_context();
    let ForwardFixturePr {
        programs,
        artifact,
        gpu,
        mut cpu,
        proof,
        challenges,
        seed: _,
        external,
        lookup,
        top_bits,
        config,
    } = forward_fixture_full(&context);
    let (_, storage, _, _) = gpu.into_parts();
    let host_tables = CoefficientTablesHostPr::build(&programs, &top_bits);
    let (tables, keepalive) =
        schedule_coefficient_tables_upload_pr(&host_tables, &context).unwrap();
    let mut rng = StdRng::seed_from_u64(0x7e0);
    let layers: Vec<LayerInputs> = [1usize, 0]
        .into_iter()
        .map(|layer| layer_inputs(&programs, &cpu, layer, &mut rng))
        .collect();
    let pool = prover::allocation_pool::GenericAllocationPool::<PR, PR>::with_retain(false);
    let worker = Worker::new_with_num_threads(
        std::thread::available_parallelism().map_or(4, |count| count.get().min(32)),
    );
    let trace_len = 1usize << FOLDING_STEPS;
    let shift = if top_bits.is_empty() {
        0
    } else {
        prover::gkr::high_bits_offset_for_inits_and_teardowns::<2>(trace_len)
    };
    let mut launched = Vec::new();
    for inputs in &layers {
        let program = &programs.r0[inputs.layer];
        let reference = run_window(
            &context,
            &storage,
            &programs,
            &tables,
            challenges.challenges().as_ptr(),
            inputs,
            None,
            program.kernel,
            0x5a5a,
        );
        check_window_against_host(inputs, &reference);
        let partitioned = program
            .partition_candidates
            .plans
            .iter()
            .filter(|plan| plan.parts.len() > 1)
            .max_by_key(|plan| plan.parts.len())
            .expect("Proth120 R0 layer has a multi-part candidate");
        let kernels: &[R0Kernel] = match program.kernel {
            R0Kernel::Unit4 => &[R0Kernel::Unit4, R0Kernel::General3, R0Kernel::Tails4],
            R0Kernel::Tails4 => &[R0Kernel::Tails4],
            R0Kernel::General3 => &[R0Kernel::General3, R0Kernel::Tails4],
        };
        for &kernel in kernels {
            for (index, plan) in [None, Some(partitioned)].into_iter().enumerate() {
                let run = run_window(
                    &context,
                    &storage,
                    &programs,
                    &tables,
                    challenges.challenges().as_ptr(),
                    inputs,
                    plan,
                    kernel,
                    0xa5a5 + index as u128,
                );
                assert_eq!(
                    run,
                    reference,
                    "layer {} kernel {kernel:?} parts {}",
                    inputs.layer,
                    plan.map_or(1, |plan| plan.parts.len())
                );
                launched.push((
                    inputs.layer,
                    kernel,
                    plan.map_or(1, |plan| plan.parts.len()),
                ));
            }
        }
        let mut claim_points = BTreeMap::from([(
            inputs.layer + 1,
            inputs
                .point
                .iter()
                .map(|&point| EvaluationPointEntry::Coordinate { point })
                .collect::<Vec<_>>(),
        )]);
        let mut claims_storage = BTreeMap::from([(inputs.layer + 1, inputs.claims.clone())]);
        let mut batching = inputs.batching;
        let mut seed = <Keccak256Transcript as Transcript<PR, PR>>::commit_initial_u32(&[]);
        seed.0 = inputs.seed;
        let proof_values =
            <NaiveGKRBackend as GKRBackend<PR, PR>>::evaluate_same_size_sumcheck_for_layer::<
                Keccak256Transcript,
            >(
                &NaiveGKRBackend,
                inputs.layer,
                &artifact.layers[inputs.layer],
                &mut claim_points,
                &mut claims_storage,
                &mut cpu,
                &mut batching,
                trace_len,
                lookup[0],
                lookup[1],
                &top_bits,
                shift,
                &external,
                &config,
                &mut seed,
                &pool,
                &worker,
            );
        for round in 0..WINDOW_ROUNDS {
            let SumcheckRoundCoefficients::Multilinear(expected) =
                &proof_values.internal_round_coefficients[round]
            else {
                panic!("Proth120 CPU round {round} is not multilinear");
            };
            assert_eq!(
                &reference.coeffs[4 * round..4 * round + 4],
                expected.as_slice(),
                "layer {} round {round} coefficients",
                inputs.layer
            );
            let EvaluationPointEntry::Coordinate { point } = claim_points[&inputs.layer][round]
            else {
                panic!("Proth120 CPU point entry {round} is not a coordinate");
            };
            assert_eq!(
                reference.challenges[round], point,
                "layer {} round {round} challenge",
                inputs.layer
            );
        }
        println!(
            "GKR_T5_R0 layer={} kernel={:?} shape={:#x} records={} plans={} parts_tested={} claims={}",
            inputs.layer,
            program.kernel,
            program.window.shape.bits(),
            program.window.sections[0],
            program.window.coefficient_plans.len(),
            partitioned.parts.len(),
            inputs.claims.len()
        );
    }
    println!("GKR_T5_R0_LAUNCHES {launched:?}");
    context.get_exec_stream().synchronize().unwrap();
    drop(keepalive);
    drop(proof);
}
