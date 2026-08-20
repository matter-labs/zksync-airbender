//! The claim point across a layer transition.
//!
//! Both `schedule_execute_main_layer` and
//! `schedule_execute_dimension_reducing_layer` build their output claim-point
//! view over the SAME `__constant__` symbol their input view reads, so round
//! `step` overwrites the coordinate slot it has just consumed and the
//! end-of-layer squeeze overwrites the batching slot the layer read at its
//! start. This drives that sequence twice over identical inputs — once in
//! place over the symbol, once with distinct input and output buffers — reads
//! both back through the production stage-snapshot path, and pins every
//! coordinate against the live CPU transcript.

use era_cudart::memory::memory_copy_async;
use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use crate::backward::kernels::{
    get_dim_reducing_layer_claim_point_device_ptr, get_eq_high_constant_device_ptr,
    get_main_layer_claim_point_device_ptr, launch_backward_dual_finalize_from_partials,
    launch_build_eq_high_and_low_groups_from_point, make_eq_sizes, record_active_eq_slot_fold,
    resolve_active_eq_slot, ClaimBufferLayout, DeviceClaimPointAndBatching, GKR_EQ_GROUP_TABLE_LEN,
    MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN, MAX_MAIN_LAYER_CLAIM_POINT_LEN,
};
use crate::backward::stage_snapshots::{schedule_stage_snapshot, GKRBackwardStageSnapshotSink};
use crate::test_utils::make_test_context;
use crate::upstream::{Field, GKRAddress, PrimeField, Seed};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::{DeviceAllocation, UnsafeMutAccessor};
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;

const SEED_WORDS: usize = 8;

fn poison() -> E4 {
    E4::from_array_of_base(std::array::from_fn(|i| {
        BF::from_u32_with_reduction(0x0bad_beef + i as u32)
    }))
}

fn random_e4(rng: &mut StdRng) -> E4 {
    E4::from_array_of_base(std::array::from_fn(|_| {
        BF::from_u32_with_reduction(rng.random())
    }))
}

/// One layer's footprint on a shared claim-point symbol: the input point is
/// `rounds` coordinate slots plus the batching slot, and the end-of-layer
/// squeeze appends `tail` slots past the round challenges.
struct LayerShape {
    label: &'static str,
    symbol: *mut E4,
    capacity: usize,
    tail: usize,
}

struct Transition {
    /// What the stage snapshot reports, batching challenge split off.
    point: Vec<E4>,
    batching: E4,
    /// The per-round univariate coefficient quadruples, in round order.
    coeffs: Vec<[E4; 4]>,
    /// The batching slot the layer read before any round wrote.
    batching_seen: E4,
    /// The input point as it stands once the layer has run.
    input_after: Vec<E4>,
}

/// Runs one layer's claim-point traffic: read the batching slot, build the
/// factored eq over `point[1..]`, draw one challenge per round out of the
/// coordinate slot the round consumes, then squeeze the layer's tail.
fn run_transition(
    context: &ProverContext,
    shape: &LayerShape,
    point: &[E4],
    seed_init: &[u32; SEED_WORDS],
    source: &DeviceAllocation<E4>,
    in_place: bool,
) -> Transition {
    let stream = context.get_exec_stream();
    let rounds = point.len() - 1;
    assert!(rounds >= 2);
    let out_len = rounds + shape.tail;
    assert!(out_len <= shape.capacity);

    let (in_view, mut out_view) = if in_place {
        let mut host = vec![poison(); shape.capacity];
        host[..point.len()].copy_from_slice(point);
        // SAFETY: the symbol holds `capacity` E4 elements.
        let symbol = unsafe { DeviceSlice::from_raw_parts_mut(shape.symbol, shape.capacity) };
        memory_copy_async(symbol, &host, stream).unwrap();
        // SAFETY: both views stay inside the symbol's capacity, exactly as the
        // per-layer schedulers construct them.
        unsafe {
            (
                DeviceClaimPointAndBatching::from_raw_symbol_parts(shape.symbol, point.len()),
                DeviceClaimPointAndBatching::from_raw_symbol_parts(shape.symbol, out_len),
            )
        }
    } else {
        let mut d_in: DeviceAllocation<E4> = context
            .alloc(point.len(), AllocationPlacement::Top)
            .unwrap();
        memory_copy_async(&mut d_in, point, stream).unwrap();
        let mut d_out: DeviceAllocation<E4> =
            context.alloc(out_len, AllocationPlacement::Top).unwrap();
        memory_copy_async(&mut d_out, &vec![poison(); out_len], stream).unwrap();
        (
            DeviceClaimPointAndBatching::from_allocation(d_in),
            DeviceClaimPointAndBatching::from_allocation(d_out),
        )
    };

    // Mirrors `build_combined_claim`'s read of the batching slot: it is the
    // layer's first claim-point access, before any round has written.
    let mut batching_seen = [E4::ZERO];
    memory_copy_async(&mut batching_seen[..], in_view.slice(rounds, 1), stream).unwrap();

    let challenge_count = rounds - 1;
    let mut d_eq_low: DeviceAllocation<E4> = context
        .alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)
        .unwrap();
    launch_build_eq_high_and_low_groups_from_point(
        in_view.as_ptr(),
        1,
        challenge_count,
        get_eq_high_constant_device_ptr(),
        d_eq_low.as_mut_ptr(),
        context,
    )
    .unwrap();
    let mut eq_sizes = make_eq_sizes(challenge_count);

    let mut d_seed: DeviceAllocation<u32> =
        context.alloc(SEED_WORDS, AllocationPlacement::Top).unwrap();
    memory_copy_async(&mut d_seed, &seed_init[..], stream).unwrap();
    let mut d_claim: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
    let mut d_eq_prefactor: DeviceAllocation<E4> =
        context.alloc(1, AllocationPlacement::Top).unwrap();
    let mut d_coeffs: DeviceAllocation<E4> =
        context.alloc(4 * rounds, AllocationPlacement::Top).unwrap();
    let one = [E4::ONE];

    for step in 0..rounds {
        memory_copy_async(&mut d_claim, &one[..], stream).unwrap();
        memory_copy_async(&mut d_eq_prefactor, &one[..], stream).unwrap();
        // The last round folds nothing, matching both schedulers' final tail.
        let folds = step + 1 < rounds;
        let (slot_base, size_before) = if folds {
            resolve_active_eq_slot(&eq_sizes, d_eq_low.as_mut_ptr())
        } else {
            (d_eq_low.as_mut_ptr(), 0)
        };
        let prev_coord = in_view.slice(step, 1).as_ptr();
        let challenge_out = out_view.slice_mut(step, 1).as_mut_ptr();
        launch_backward_dual_finalize_from_partials(
            source.as_ptr(),
            source.len() / 2,
            prev_coord,
            d_seed.as_mut_ptr(),
            d_claim.as_mut_ptr(),
            d_eq_prefactor.as_mut_ptr(),
            // SAFETY: `d_coeffs` holds four elements per round.
            unsafe { d_coeffs.as_mut_ptr().add(4 * step) },
            challenge_out,
            slot_base,
            size_before,
            context,
        )
        .unwrap();
        if folds {
            record_active_eq_slot_fold(&mut eq_sizes);
        }
    }
    // Both schedulers commit their final evaluations between the last round and
    // the end-of-layer squeeze; without that commit the squeeze would reproduce
    // the last round's challenge.
    let final_evaluations = [E4::ONE, E4::ZERO];
    let mut d_final_evaluations: DeviceAllocation<E4> = context
        .alloc(final_evaluations.len(), AllocationPlacement::Top)
        .unwrap();
    memory_copy_async(&mut d_final_evaluations, &final_evaluations[..], stream).unwrap();
    // SAFETY: E4 is four packed BF limbs, matching transcript word order.
    let d_final_evaluations_u32 = unsafe { d_final_evaluations[..].transmute::<u32>() };
    gpu_hash::blake2s::transcript_commit(&mut d_seed, d_final_evaluations_u32, stream).unwrap();
    gpu_hash::blake2s::transcript_squeeze_e4(
        &mut d_seed,
        out_view.slice_mut(rounds, shape.tail),
        stream,
    )
    .unwrap();

    let mut coeffs_flat = vec![E4::ZERO; 4 * rounds];
    memory_copy_async(&mut coeffs_flat[..], &d_coeffs, stream).unwrap();
    let mut input_after = vec![E4::ZERO; point.len()];
    memory_copy_async(&mut input_after[..], in_view.slice(0, point.len()), stream).unwrap();

    let layout = ClaimBufferLayout::from_addresses(vec![GKRAddress::Setup(0)]);
    let mut d_claims: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
    memory_copy_async(&mut d_claims, &one[..], stream).unwrap();
    let mut sink = GKRBackwardStageSnapshotSink::default();
    let mut callbacks = Callbacks::new();
    schedule_stage_snapshot(
        0,
        &out_view,
        &d_claims,
        &layout,
        UnsafeMutAccessor::new(&mut sink),
        &mut callbacks,
        context,
    )
    .unwrap();
    stream.synchronize().unwrap();

    let mut snapshots = sink.into_snapshots();
    assert_eq!(
        snapshots.len(),
        1,
        "{}: the stage snapshot did not fire",
        shape.label
    );
    let snapshot = snapshots.pop().unwrap();
    Transition {
        point: snapshot.claim_point,
        batching: snapshot.batching_challenge,
        coeffs: (0..rounds)
            .map(|step| {
                let mut quad = [E4::ZERO; 4];
                quad.copy_from_slice(&coeffs_flat[4 * step..4 * step + 4]);
                quad
            })
            .collect(),
        batching_seen: batching_seen[0],
        input_after,
    }
}

/// Replays the transcript the fused tail runs on the host: each round commits
/// its four coefficients and draws one challenge, so coordinate slot `step`
/// must hold round `step`'s challenge.
fn assert_protocol_order(label: &str, seed_init: &[u32; SEED_WORDS], run: &Transition) {
    use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};

    let mut seed = Seed(*seed_init);
    for (step, coeffs) in run.coeffs.iter().enumerate() {
        commit_field_els::<BF, E4, prover::transcript::Blake2sTranscript>(&mut seed, coeffs);
        let expected =
            draw_random_field_els::<BF, E4, prover::transcript::Blake2sTranscript>(&mut seed, 1)[0];
        assert_eq!(
            run.point[step], expected,
            "{label}: coordinate slot {step} does not hold round {step}'s challenge",
        );
    }
}

fn run_shape(context: &ProverContext, shape: &LayerShape, rounds: usize, seed: u64) {
    let mut rng = StdRng::seed_from_u64(seed);
    let point: Vec<E4> = (0..rounds + 1).map(|_| random_e4(&mut rng)).collect();
    let seed_init: [u32; SEED_WORDS] = std::array::from_fn(|_| rng.random());
    let source_host: Vec<E4> = (0..16).map(|_| random_e4(&mut rng)).collect();
    let mut source: DeviceAllocation<E4> = context
        .alloc(source_host.len(), AllocationPlacement::Top)
        .unwrap();
    memory_copy_async(&mut source, &source_host, context.get_exec_stream()).unwrap();

    let label = &format!("{} rounds={rounds}", shape.label);
    let shared = run_transition(context, shape, &point, &seed_init, &source, true);
    let split = run_transition(context, shape, &point, &seed_init, &source, false);

    assert_eq!(
        split.input_after, point,
        "{label}: the layer mutated its input claim point",
    );
    assert_eq!(
        split.batching_seen, point[rounds],
        "{label}: the layer read a batching challenge its predecessor did not hand it",
    );
    assert_eq!(
        shared.batching_seen, split.batching_seen,
        "{label}: the shared symbol perturbed the batching challenge the layer reads",
    );
    assert_eq!(
        shared.coeffs, split.coeffs,
        "{label}: the shared symbol perturbed a round's univariate coefficients",
    );
    assert_eq!(
        shared.point, split.point,
        "{label}: the claim point handed to the next layer differs in place",
    );
    assert_eq!(
        shared.batching, split.batching,
        "{label}: the batching challenge handed to the next layer differs in place",
    );

    // Non-vacuity: a degenerate challenge sequence would make the comparisons
    // above blind to a slot permutation.
    for (i, left) in shared.point.iter().enumerate() {
        for right in &shared.point[i + 1..] {
            assert_ne!(
                left, right,
                "{label}: the drawn coordinates must be distinct"
            );
        }
        assert_ne!(
            *left,
            poison(),
            "{label}: coordinate slot {i} was never written",
        );
        assert_ne!(
            *left, shared.batching,
            "{label}: coordinate slot {i} aliases the batching challenge",
        );
    }
    assert_ne!(
        shared.point[..rounds],
        point[..rounds],
        "{label}: the layer reproduced its input point instead of drawing challenges",
    );

    assert_protocol_order(label, &seed_init, &shared);
    assert_protocol_order(&format!("{label} split"), &seed_init, &split);
}

#[test]
fn claim_point_survives_a_layer_transition() {
    let context = make_test_context(256, 64);
    let shapes = [
        LayerShape {
            label: "main layer",
            symbol: get_main_layer_claim_point_device_ptr(),
            capacity: MAX_MAIN_LAYER_CLAIM_POINT_LEN,
            tail: 1,
        },
        LayerShape {
            label: "dimension-reducing layer",
            symbol: get_dim_reducing_layer_claim_point_device_ptr(),
            capacity: MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN,
            tail: 2,
        },
    ];
    for shape in &shapes {
        for (index, rounds) in [4usize, 9].into_iter().enumerate() {
            run_shape(&context, shape, rounds, 0x0c_1a_10_00 + index as u64);
        }
    }
}

/// The point a dimension-reducing layer hands on must be in plain variable
/// order — the end-of-layer challenge (which binds the gate bit, coordinate 0
/// of the polys the next layer reads) FIRST, then the round challenges, then
/// the batching challenge. CPU authority:
/// `prover/src/gkr/prover/sumcheck_loop/mod.rs:306-310`.
///
/// The layer's own scratch (the `__constant__` symbol) stays in DRAW order
/// because the continuation kernels index it by round
/// (`native/gkr/support/lookup_helpers.cuh:288`), so this reorder happens on
/// the way out and must not disturb the symbol.
#[test]
#[cfg(not(no_cuda))]
fn dim_reducing_next_layer_claim_point_is_variable_order() {
    use crate::backward::dim_reducing_sumcheck_plan::schedule_dim_reducing_next_layer_claim_point;

    let context = make_test_context(256, 64);
    let mut rng = StdRng::seed_from_u64(0x0c_1a_10_5b);

    for folding_steps in [2usize, 4, 9] {
        let len = folding_steps + 2;
        // Draw order, as the layer's rounds and end-of-layer squeeze write it.
        let draw_order: Vec<E4> = (0..len).map(|_| random_e4(&mut rng)).collect();
        let mut symbol_host = vec![poison(); MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN];
        symbol_host[..len].copy_from_slice(&draw_order);
        // SAFETY: the symbol is MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN E4 long.
        let symbol_view = unsafe {
            DeviceSlice::from_raw_parts_mut(
                get_dim_reducing_layer_claim_point_device_ptr(),
                symbol_host.len(),
            )
        };
        memory_copy_async(symbol_view, &symbol_host, context.get_exec_stream()).unwrap();
        // SAFETY: `len <= MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN`.
        let layer_out = unsafe {
            DeviceClaimPointAndBatching::from_raw_symbol_parts(
                get_dim_reducing_layer_claim_point_device_ptr(),
                len,
            )
        };

        let next =
            schedule_dim_reducing_next_layer_claim_point(&layer_out, folding_steps, &context)
                .unwrap();
        let mut actual = vec![poison(); len];
        memory_copy_async(&mut actual[..], &next[..], context.get_exec_stream()).unwrap();
        let mut symbol_after = vec![poison(); MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN];
        // SAFETY: same symbol extent as above.
        let symbol_read = unsafe {
            DeviceSlice::from_raw_parts(
                get_dim_reducing_layer_claim_point_device_ptr(),
                symbol_after.len(),
            )
        };
        memory_copy_async(
            &mut symbol_after[..],
            symbol_read,
            context.get_exec_stream(),
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        let mut expected = Vec::with_capacity(len);
        expected.push(draw_order[folding_steps]);
        expected.extend_from_slice(&draw_order[..folding_steps]);
        expected.push(draw_order[folding_steps + 1]);
        assert_eq!(
            actual, expected,
            "folding_steps={folding_steps}: handed-on point is not in variable order",
        );
        // Non-vacuity: the reorder must not be a no-op at these widths, and the
        // layer's own draw-order scratch must survive it.
        assert_ne!(
            actual, draw_order,
            "folding_steps={folding_steps}: the reorder degenerated to a copy",
        );
        assert_eq!(
            &symbol_after[..len],
            &draw_order[..],
            "folding_steps={folding_steps}: the layer's draw-order symbol was disturbed",
        );
    }
}
