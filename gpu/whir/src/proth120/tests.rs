use std::panic::{catch_unwind, AssertUnwindSafe};

use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use field::Field;
use gpu_core::primitives::field::PR;
use gpu_prover_context::{ProverContext, ProverContextConfig};
use gpu_trace::trace::holder::{TraceHolder, TreesCacheMode};
use prover::definitions::SecurityLevel;
use prover::gkr::prover::gkr_backend::{accumulate_base_columns_into_scalar, BatchedBaseColumn};
use prover::gkr::prover::WhirSchedule;
use prover::gkr::prover_config::ProofProfile;
use prover::gkr::sumcheck::eq_poly::fill_eq_table_lsb_first_uninit;
use prover::gkr::whir::{
    evaluate_monomial_form, fold_eq_poly, fold_evaluation_form, fold_monomial_form,
    special_three_point_eval,
};
use transcript::{Keccak256Seed, Keccak256Transcript, Transcript};
use worker::Worker;

use std::alloc::Global;
use std::time::Instant;

use fft::Twiddles;
use prover::allocation_pool::GenericAllocationPool;
use prover::gkr::prover::backend::{Backend, ExtCoeffConversion, Proth120WorkStealingLazyBackend};
use prover::gkr::whir::coset_commit::CosetByCosetExtCommitment;
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use prover::merkle_trees::{ColumnMajorMerkleTreeConstructor, PathQueryable};

use gpu_hash::keccak256::{
    transcript_commit_fields, transcript_commit_u32, transcript_draw_fields,
};
use prover::gkr::whir::hypercube_to_monomial::multivariate_coeffs_into_hypercube_evals;

use super::commit::{
    schedule_commit_intermediate, schedule_coset_offsets, schedule_lde_convert_pass,
};
use super::schedule::{
    query_words, schedule_delinearization, schedule_eq_update, schedule_pow_and_query_indexes,
};
use super::shape::{L1WhirShape, OracleShape, L1_WHIR_TILE_BYTES};
use super::state::*;

pub(super) fn worker() -> Worker {
    Worker::new_with_num_threads(4)
}

pub(super) struct TestRng(u64);
impl TestRng {
    pub(super) fn new(seed: u64) -> Self {
        Self(seed | 1)
    }
    pub(super) fn next_u64(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    pub(super) fn field(&mut self) -> PR {
        let value = ((self.next_u64() as u128) << 64) | self.next_u64() as u128;
        PR::from_u128_with_reduction(value)
    }
    pub(super) fn fields(&mut self, count: usize) -> Vec<PR> {
        (0..count)
            .map(|i| match i % 31 {
                0 => PR::ZERO,
                1 => PR::ONE,
                2 => PR::new(PR::ORDER - 1),
                _ => self.field(),
            })
            .collect()
    }
}

pub(super) fn context(arena_mb: usize, log_domain: Option<u32>) -> ProverContext {
    ProverContext::new(&ProverContextConfig {
        device_allocation_blocks_count: Some(arena_mb),
        host_allocator_blocks_count: 2048,
        proth120_ntt_log_max_domain: log_domain,
        ..Default::default()
    })
    .unwrap()
}

pub(super) fn upload<T: Copy>(values: &[T], stream: &CudaStream) -> DeviceAllocation<T> {
    let mut device = DeviceAllocation::alloc(values.len()).unwrap();
    memory_copy_async(&mut device, values, stream).unwrap();
    device
}

pub(super) fn download<T: Copy + Default>(values: &DeviceSlice<T>, stream: &CudaStream) -> Vec<T> {
    let mut host = vec![T::default(); values.len()];
    memory_copy_async(&mut host, values, stream).unwrap();
    stream.synchronize().unwrap();
    host
}

pub(super) fn assert_fields(actual: &[PR], expected: &[PR]) {
    assert_eq!(actual.len(), expected.len());
    for (i, (a, b)) in actual.iter().zip(expected).enumerate() {
        assert!(a.0 < PR::ORDER, "noncanonical output at {i}");
        assert_eq!(a.0, b.0, "field at {i}");
    }
}

pub(super) fn small_schedule() -> WhirSchedule {
    let mut schedule = WhirSchedule::from_legacy_arrays(
        32,
        8,
        0,
        &[2, 4, 4],
        &[5, 4, 3],
        &[128, 2048],
        &[4, 0, 3],
    );
    schedule.base_round.batching_pow_bits = Some(0);
    schedule
}

fn small_pack3_schedule() -> WhirSchedule {
    let mut schedule = WhirSchedule::from_legacy_arrays(
        64,
        8,
        0,
        &[1, 4, 4],
        &[5, 4, 3],
        &[128, 2048],
        &[4, 0, 3],
    );
    schedule.base_round.batching_pow_bits = Some(0);
    schedule
}

/// The pack-4 L1 wrap WHIR schedule (message 2^25, base LDE 64), kept for the 2^8 oracle on a 2^23 LDE.
fn pack4_wrap_schedule() -> WhirSchedule {
    let mut schedule = WhirSchedule::from_legacy_arrays(
        64,
        8,
        4,
        &[2, 4, 4, 4, 3, 4],
        &[14, 11, 8, 6, 5, 4],
        &[1 << 8, 1 << 12, 1 << 16, 1 << 20, 1 << 23],
        &[30, 27, 20, 20, 17, 24],
    );
    schedule.base_round.batching_pow_bits = Some(0);
    schedule
}

#[test]
fn cpu_shape_l1_values() {
    let schedule = ProofProfile::L1Wrap
        .prover_config(21, SecurityLevel::Sec100)
        .whir_schedule;
    let shape = L1WhirShape::from_schedule(&schedule, 24, 7, 1, L1_WHIR_TILE_BYTES);
    assert_eq!(
        (
            shape.log_message,
            shape.log_base_lde,
            shape.cap_log,
            shape.term_capacity,
            shape.total_sumcheck_polys,
            shape.log_final
        ),
        (24, 7, 3, 36, 17, 7)
    );
    let round_rows = [
        (1, 12, 30, 23, 30),
        (4, 11, 27, 19, 27),
        (4, 7, 30, 15, 27),
        (4, 6, 20, 11, 27),
        (4, 5, 17, 7, 27),
    ];
    let oracle_rows = [
        (23, 8, 31, 4, 19, 5, 3, 3, 32767, 24),
        (19, 12, 31, 4, 15, 5, 3, 7, 2047, 24),
        (15, 16, 31, 4, 11, 5, 3, 11, 127, 24),
        (11, 20, 31, 4, 7, 5, 3, 15, 7, 24),
    ];
    for (r, round) in shape.rounds.iter().enumerate() {
        assert_eq!(
            (
                round.folds,
                round.queries,
                round.pow_bits,
                round.log_poly_after,
                round.query_domain_log2
            ),
            round_rows[r]
        );
        if let Some(o) = round.oracle {
            assert_eq!(
                (
                    o.log_n,
                    o.log_lde,
                    o.log_domain,
                    o.log_v,
                    o.log_leaves,
                    o.skip_bottom,
                    o.cap_log,
                    o.tile_cosets_log2,
                    o.retained_per_coset,
                    o.path_len
                ),
                oracle_rows[r]
            );
            assert_eq!(
                o.retained_per_coset,
                gpu_hash::keccak256::retained_layer_offset(
                    o.log_leaves,
                    o.skip_bottom,
                    o.log_leaves
                ) + 1
            );
        } else {
            assert_eq!(r, 4);
        }
    }
    let s = L1WhirShape::from_schedule(&small_schedule(), 14, 5, 2, 16 << 14);
    assert_eq!(s.rounds[0].oracle.unwrap().tile_cosets_log2, 2);
    assert_eq!(s.rounds[1].oracle.unwrap().tile_cosets_log2, 6);
    assert_eq!(s.log_final, 4);
    let one = L1WhirShape::from_schedule(&small_schedule(), 14, 5, 2, 16 << 19);
    for r in &one.rounds[..2] {
        let o = r.oracle.unwrap();
        assert_eq!(o.tile_cosets_log2, o.log_lde);
    }
}

fn rejection(
    schedule: &WhirSchedule,
    log_message: u32,
    log_lde: u32,
    log_v: u32,
    tile: usize,
    expected: &str,
) {
    let err = catch_unwind(AssertUnwindSafe(|| {
        L1WhirShape::from_schedule(schedule, log_message, log_lde, log_v, tile)
    }))
    .unwrap_err();
    let text = err
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| err.downcast_ref::<&str>().copied())
        .unwrap();
    assert!(
        text.contains("Proth120 WHIR:") && text.contains(expected),
        "unexpected panic: {text}"
    );
}

#[test]
fn cpu_shape_rejects_invalid() {
    let s = small_schedule();
    let tile = L1_WHIR_TILE_BYTES;
    let mut bad = s.clone();
    bad.base_round.fold_log2 = 0;
    rejection(&bad, 14, 5, 2, tile, "requires explicit packing");
    let mut bad = s.clone();
    bad.base_round.folding_pow_bits = 1;
    rejection(&bad, 14, 5, 2, tile, "does not implement folding PoW");
    for (index, expected) in [
        (0, "does not implement OOD PoW"),
        (1, "does not implement folding PoW"),
        (2, "requires one OOD sample"),
    ] {
        let mut bad = s.clone();
        match index {
            0 => bad.internal_rounds[0].ood_pow_bits = 1,
            1 => bad.internal_rounds[0].folding_pow_bits = 1,
            _ => bad.internal_rounds[0].num_ood_samples = 2,
        }
        rejection(&bad, 14, 5, 2, tile, expected);
    }
    rejection(&s, 14, 5, 3, tile, "first folds");
    rejection(&s, 11, 5, 2, tile, "oracle log_n below 8");
    rejection(&s, 9, 5, 2, tile, "sum of folds exceeds");
    let mut bad = s.clone();
    bad.internal_rounds[0].lde_factor_log2 = 20;
    rejection(&bad, 14, 5, 2, tile, "oracle log_domain exceeds 31");
    let mut bad = s.clone();
    bad.internal_rounds[0].lde_factor_log2 = 2;
    rejection(&bad, 14, 5, 2, tile, "cap_log exceeds oracle");
    let mut bad = s.clone();
    bad.internal_rounds[0].lde_factor_log2 = 3;
    rejection(&bad, 14, 5, 2, tile, "earlier query domain");
    let mut bad = s.clone();
    bad.internal_rounds.clear();
    rejection(&bad, 14, 5, 2, tile, "at least two rounds");
    let mut bad = s.clone();
    bad.cap_size = 7;
    rejection(&bad, 14, 5, 2, tile, "cap_size must be a power");
    rejection(&s, 14, 4, 2, tile, "base LDE factor differs");
    let mut bad = s.clone();
    bad.internal_rounds[0].folding_log2 = 0;
    rejection(&bad, 14, 5, 2, tile, "log_v outside");
    let mut bad = s.clone();
    bad.internal_rounds[0].folding_log2 = 5;
    rejection(&bad, 14, 5, 2, tile, "log_v outside");
    let mut bad = s.clone();
    bad.base_round.num_queries = 0;
    rejection(&bad, 14, 5, 2, tile, "queries outside");
    rejection(&s, 14, 5, 2, 16 << 11, "below one coset");
    rejection(&s, 14, 5, 2, 123, "tile_bytes must be a power");
    let bad = WhirSchedule::from_legacy_arrays(
        32,
        8,
        0,
        &[2, 4, 4, 4, 4],
        &[1; 5],
        &[1 << 15; 4],
        &[0; 5],
    );
    rejection(&bad, 26, 5, 2, tile, "oracle log_domain exceeds 31");
    let final_zero = WhirSchedule::from_legacy_arrays(
        32,
        8,
        0,
        &[2, 4, 4, 4],
        &[1; 4],
        &[128, 2048, 32768],
        &[0; 4],
    );
    rejection(&final_zero, 14, 5, 2, tile, "oracle log_n below 8");
}

fn accumulate_reference(
    memory: &[PR],
    setup: &[PR],
    rows: usize,
    pack_log2: u32,
    powers: &[PR],
) -> Vec<PR> {
    let pack = 1 << pack_log2;
    let p = (memory.len() / rows).div_ceil(pack);
    let terms: Vec<_> = memory
        .chunks_exact(rows)
        .enumerate()
        .map(|(c, column)| BatchedBaseColumn {
            column,
            power: powers[c / pack],
            dst_offset: (c % pack) * rows,
        })
        .chain(
            setup
                .chunks_exact(rows)
                .enumerate()
                .map(|(c, column)| BatchedBaseColumn {
                    column,
                    power: powers[p + c / pack],
                    dst_offset: (c % pack) * rows,
                }),
        )
        .collect();
    let mut out = Vec::<PR>::with_capacity(rows * pack);
    accumulate_base_columns_into_scalar::<PR, PR>(
        &mut out.spare_capacity_mut()[..rows * pack],
        &terms,
        &worker(),
    );
    unsafe {
        out.set_len(rows * pack);
    }
    out
}

#[test]
fn pr_accumulate_base_matches_cpu() {
    let ctx = context(512, None);
    let stream = ctx.get_exec_stream();
    let mut rng = TestRng::new(0x7101);
    for (log_rows, memory_cols, setup_cols, pack) in [
        (8u32, 20usize, 3usize, 0u32),
        (8, 20, 3, 2),
        (8, 20, 3, 4),
        (8, 104, 10, 3),
        (10, 104, 10, 4),
    ] {
        let rows = 1 << log_rows;
        let mut memory = rng.fields(rows * memory_cols);
        let mut setup = rng.fields(rows * setup_cols);
        for c in [15, 16, 31, 32, 95, 96, 103]
            .into_iter()
            .filter(|c| *c < memory_cols)
        {
            for (r, v) in [PR::ZERO, PR::ONE, PR::new(PR::ORDER - 1), rng.field()]
                .iter()
                .enumerate()
            {
                memory[c * rows + r] = *v;
            }
        }
        setup[(setup_cols - 1) * rows] = PR::new(PR::ORDER - 1);
        let beta = rng.field();
        let count = memory_cols.div_ceil(1 << pack) + setup_cols.div_ceil(1 << pack);
        let mut powers = vec![PR::ONE; count];
        for i in 1..count {
            powers[i] = powers[i - 1];
            powers[i].mul_assign(&beta);
        }
        let beta_dev = upload(&[beta], stream);
        let mut powers_dev = upload(&vec![PR::ZERO; count], stream);
        gpu_ops::powers::get_powers_by_ref(
            unsafe { DeviceVariable::from_raw_parts(beta_dev.as_ptr()) },
            0,
            &mut powers_dev,
            stream,
        )
        .unwrap();
        let mut base = TraceHolder::new_without_cosets(
            log_rows,
            5,
            2,
            3,
            memory_cols,
            TreesCacheMode::CacheNone,
            gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
            &ctx,
        )
        .unwrap();
        let mut setup_raw = TraceHolder::new_without_cosets(
            log_rows,
            5,
            2,
            3,
            setup_cols,
            TreesCacheMode::CacheNone,
            gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
            &ctx,
        )
        .unwrap();
        memory_copy_async(base.get_uninit_hypercube_evals_mut(), &memory, stream).unwrap();
        memory_copy_async(setup_raw.get_uninit_hypercube_evals_mut(), &setup, stream).unwrap();
        let mut state = L1WhirState::new(log_rows + pack, 0, &ctx).unwrap();
        schedule_accumulate_base(&base, &setup_raw, &powers_dev, &mut state, &ctx).unwrap();
        let expected = accumulate_reference(&memory, &setup, rows, pack, &powers);
        if log_rows == 10 {
            let shape = L1WhirShape::from_schedule(&small_schedule(), 14, 5, 2, 16 << 14);
            let outputs = super::outputs::L1WhirProofDevice::new(&shape, 7, 1, &ctx).unwrap();
            let _host = super::outputs::L1WhirProofHost::new(&shape, &outputs, &ctx);
            assert_eq!(outputs.memory.leaves.len(), 5 * 4 * 7);
            assert_eq!(outputs.setup.leaves.len(), 5 * 4);
            assert_eq!(outputs.memory.paths.len(), 5 * 14);
            assert_eq!(outputs.intermediate[0].leaves.len(), 4 * 16);
            assert_eq!(outputs.intermediate[1].leaves.len(), 3 * 16);
            assert_eq!(outputs.sumcheck_polys.len(), 10 * 3);
            assert_eq!(outputs.final_monomials.len(), 16);
        }
        assert_fields(&download(&state.evals, stream), &expected);
        schedule_monomials(&mut state, &ctx).unwrap();
        let mut monomials = expected.clone();
        prover::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs_radix4(
            &mut monomials,
            state.current_len.trailing_zeros(),
        );
        assert_fields(&download(&state.monomials, stream), &monomials);
        if pack > 0 {
            let wrong_powers = rng.fields(memory_cols + setup_cols);
            let mut wrong = vec![PR::ZERO; rows << pack];
            for (c, col) in memory
                .chunks_exact(rows)
                .chain(setup.chunks_exact(rows))
                .enumerate()
            {
                for (r, value) in col.iter().enumerate() {
                    let mut v = *value;
                    v.mul_assign(&wrong_powers[c]);
                    wrong[(c % (1 << pack)) * rows + r].add_assign(&v);
                }
            }
            assert_ne!(wrong, expected, "per-raw-column power negative control");
            let wrong_coordinate: Vec<_> = expected
                .chunks_exact(rows)
                .rev()
                .flatten()
                .copied()
                .collect();
            assert_ne!(
                wrong_coordinate, expected,
                "pack-coordinate negative control"
            );
        }
        let claims = rng.fields(count);
        let claims_dev = upload(&claims, stream);
        let mut out = upload(&[PR::ZERO], stream);
        schedule_batched_opening(&powers_dev, &claims_dev, &mut out, &ctx).unwrap();
        let expected_opening = powers
            .iter()
            .zip(&claims)
            .fold(PR::ZERO, |mut acc, (p, c)| {
                let mut v = *p;
                v.mul_assign(c);
                acc.add_assign(&v);
                acc
            });
        assert_fields(&download(&out, stream), &[expected_opening]);
    }
}

#[test]
fn pr_eq_from_point_matches_cpu() {
    let ctx = context(6144, None);
    let stream = ctx.get_exec_stream();
    let mut rng = TestRng::new(0x7102);
    for log_n in [1, 8, 13, 14, 20, 26] {
        let point = rng.fields(log_n as usize);
        let point_dev = upload(&point, stream);
        let mut state = L1WhirState::new(log_n, 0, &ctx).unwrap();
        schedule_eq_from_point(&point_dev, &mut state, &ctx).unwrap();
        let mut expected = Vec::<PR>::with_capacity(1 << log_n);
        fill_eq_table_lsb_first_uninit(
            &point,
            &mut expected.spare_capacity_mut()[..1 << log_n],
            &worker(),
        );
        unsafe {
            expected.set_len(1 << log_n);
        }
        assert_fields(&download(&state.eq, stream), &expected);
    }
}

#[test]
fn pr_fold_state_matches_cpu() {
    let ctx = context(256, None);
    let stream = ctx.get_exec_stream();
    let mut rng = TestRng::new(0x7103);
    let mut monomials = rng.fields(1 << 12);
    let mut evals = rng.fields(1 << 12);
    let mut eq = rng.fields(1 << 12);
    let mut state = L1WhirState::new(12, 0, &ctx).unwrap();
    memory_copy_async(&mut state.monomials, &monomials, stream).unwrap();
    memory_copy_async(&mut state.evals, &evals, stream).unwrap();
    memory_copy_async(&mut state.eq, &eq, stream).unwrap();
    for _ in 0..5 {
        let challenge = rng.field();
        let challenge_dev = upload(&[challenge], stream);
        let mut wrong = monomials.clone();
        let wrong_len = fold_evaluation_form::<PR, PR>(&mut wrong, &challenge, &worker()).len();
        wrong.truncate(wrong_len);
        let mut buffer = Vec::with_capacity(monomials.len() / 2);
        fold_monomial_form(&mut monomials, &mut buffer, &challenge, &worker());
        assert_ne!(
            wrong, monomials,
            "evaluation fold on monomials negative control"
        );
        let len = fold_evaluation_form::<PR, PR>(&mut evals, &challenge, &worker()).len();
        evals.truncate(len);
        let len = fold_eq_poly::<PR, PR>(&mut eq, &challenge, &worker()).len();
        eq.truncate(len);
        schedule_fold_state(&mut state, &challenge_dev, &ctx).unwrap();
        assert_fields(&download(&state.monomials, stream), &monomials);
        assert_fields(&download(&state.evals, stream), &evals);
        assert_fields(&download(&state.eq, stream), &eq);
    }
}

#[test]
fn pr_three_point_matches_cpu() {
    let ctx = context(256, None);
    let stream = ctx.get_exec_stream();
    let mut rng = TestRng::new(0x7104);
    for log_n in [1, 4, 9, 14, 20] {
        let evals = rng.fields(1 << log_n);
        let eq = rng.fields(1 << log_n);
        let mut state = L1WhirState::new(log_n, 0, &ctx).unwrap();
        memory_copy_async(&mut state.evals, &evals, stream).unwrap();
        memory_copy_async(&mut state.eq, &eq, stream).unwrap();
        schedule_three_point(&mut state, &ctx).unwrap();
        let (a, b, mut half) = special_three_point_eval::<PR, PR>(&evals, &eq, &worker());
        half.double();
        half.double();
        assert_fields(&download(&state.reduce_out, stream), &[a, b, half]);
    }
}

#[test]
fn pr_monomial_eval_matches_cpu() {
    let ctx = context(256, None);
    let stream = ctx.get_exec_stream();
    let mut rng = TestRng::new(0x7105);
    for log_n in [1, 4, 9, 14, 20] {
        let monomials = rng.fields(1 << log_n);
        let state = L1WhirState::new(log_n, 0, &ctx).unwrap();
        let mut state = state;
        memory_copy_async(&mut state.monomials, &monomials, stream).unwrap();
        for point in [PR::ZERO, PR::ONE, rng.field()] {
            let point_dev = upload(&[point], stream);
            let mut out = upload(&[PR::ZERO], stream);
            schedule_monomial_eval(&state, &point_dev, &mut out, &ctx).unwrap();
            assert_fields(
                &download(&out, stream),
                &[evaluate_monomial_form(&monomials, &point, &worker())],
            );
        }
    }
}

#[test]
fn pr_round_update_matches_cpu() {
    let ctx = context(256, None);
    let stream = ctx.get_exec_stream();
    let mut rng = TestRng::new(0x7106);
    for _ in 0..16 {
        let [a, b, d] = [rng.field(), rng.field(), rng.field()];
        let seed: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
        let mut state = L1WhirState::new(1, 0, &ctx).unwrap();
        memory_copy_async(&mut state.reduce_out, &[a, b, d], stream).unwrap();
        let mut seed_dev = upload(&seed, stream);
        let mut coeffs = upload(&[PR::ZERO; 3], stream);
        let mut challenge = upload(&[PR::ZERO], stream);
        schedule_round_update(&mut state, &mut seed_dev, &mut coeffs, &mut challenge, &ctx)
            .unwrap();
        let got = download(&coeffs, stream);
        let mut half = PR::ONE;
        half.double();
        half = half.inverse().unwrap();
        let mut expected_half = d;
        let mut quarter = half;
        quarter.square();
        expected_half.mul_assign(&quarter);
        for (x, expected) in [(PR::ZERO, a), (PR::ONE, b), (half, expected_half)] {
            assert_fields(&[evaluate_monomial_form(&got, &x, &worker())], &[expected]);
        }
        let mut host_seed = Keccak256Seed(seed);
        <Keccak256Transcript as Transcript<PR, PR>>::commit_extension_field_elements(
            &mut host_seed,
            &got,
        );
        let mut host_challenge = [PR::ZERO];
        <Keccak256Transcript as Transcript<PR, PR>>::draw_random_field_elements(
            &mut host_seed,
            &mut host_challenge,
        );
        assert_fields(&download(&challenge, stream), &host_challenge);
        assert_eq!(download(&seed_dev, stream), host_seed.0);
    }
}

type ExtCommitment = CosetByCosetExtCommitment<PR, PR, Keccak256MerkleTreeWithCap>;

pub(super) fn small_oracle(log_n: u32, log_lde: u32, tile_bytes: usize) -> OracleShape {
    let schedule =
        WhirSchedule::from_legacy_arrays(32, 8, 0, &[2, 4], &[1, 1], &[1 << log_lde], &[0, 0]);
    L1WhirShape::from_schedule(&schedule, log_n + 2, 5, 2, tile_bytes).rounds[0]
        .oracle
        .unwrap()
}

pub(super) fn cpu_ext_commit(monomials: &[PR], log_lde: u32, worker: &Worker) -> ExtCommitment {
    let twiddles = Twiddles::<PR, Global>::new(monomials.len(), worker);
    ExtCommitment::commit(monomials, &twiddles, 1 << log_lde, 16, 8, worker)
}

pub(super) fn cap_words(cap: &[[u32; 8]]) -> Vec<u32> {
    cap.iter().flatten().copied().collect()
}

struct GpuCommit {
    cap: Vec<[u32; 8]>,
    cap_dst: Vec<[u32; 8]>,
    roots: Vec<[u32; 8]>,
    seed: [u8; 32],
}

fn gpu_commit(
    monomials: &[PR],
    shape: &OracleShape,
    seed: [u8; 32],
    ctx: &ProverContext,
) -> GpuCommit {
    let stream = ctx.get_exec_stream();
    let monomials_dev = upload(monomials, stream);
    let mut cap_dst = upload(&[[0u32; 8]; 8], stream);
    let mut seed_dev = upload(&seed, stream);
    let oracle =
        schedule_commit_intermediate(&monomials_dev, shape, &mut cap_dst, &mut seed_dev, ctx)
            .unwrap();
    let r = shape.retained_per_coset;
    assert_eq!(oracle.retained.len(), (1 << shape.log_lde) * r);
    assert_eq!(oracle.roots.len(), 1 << shape.log_lde);
    assert_eq!(oracle.top_nodes.len(), (1 << shape.log_lde) - 8);
    assert_eq!(oracle.monomials.len(), monomials.len());
    assert_fields(&download(&oracle.monomials, stream), monomials);
    GpuCommit {
        cap: download(&oracle.cap, stream),
        cap_dst: download(&cap_dst, stream),
        roots: download(&oracle.roots, stream),
        seed: download(&seed_dev, stream).try_into().unwrap(),
    }
}

fn cpu_tile_pass(monomials: &[PR], log_lde: u32, k0: usize, cosets: usize) -> Vec<PR> {
    let worker = worker();
    let n = monomials.len();
    let twiddles = Twiddles::<PR, Global>::new(n, &worker);
    let backend = Proth120WorkStealingLazyBackend;
    let pool = GenericAllocationPool::<PR, PR>::proxy();
    let (mut all, offsets) = backend.lde_ext_poly_from_monomial_form_continuous(
        monomials,
        &twiddles,
        1 << log_lde,
        &pool,
        &worker,
    );
    let conv =
        <Proth120WorkStealingLazyBackend as Backend<PR, PR>>::ext_coeff_conv(&backend, n, 16);
    for k in k0..k0 + cosets {
        conv.apply_serial(&mut all[k * n..(k + 1) * n], offsets[k]);
    }
    all[k0 * n..(k0 + cosets) * n].to_vec()
}

#[test]
fn pr_commit_intermediate_matches_cpu_small() {
    let ctx = context(512, Some(19));
    let stream = ctx.get_exec_stream();
    let worker = worker();
    let mut rng = TestRng::new(0x7201);
    for (log_n, log_lde, passes) in [
        (12u32, 7u32, 32usize),
        (8, 11, 8),
        (10, 9, 1),
        (8, 11, 2048),
        (8, 11, 1024),
        (8, 11, 512),
        (11, 8, 256),
        (11, 8, 64),
    ] {
        let cosets = 1usize << log_lde;
        let tile_bytes = (cosets / passes) << (log_n + 4);
        let shape = small_oracle(log_n, log_lde, tile_bytes);
        assert_eq!(cosets >> shape.tile_cosets_log2, passes);
        assert_eq!(shape.log_domain, log_n + log_lde);
        let monomials = rng.fields(1 << log_n);
        let seed: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
        let cpu = cpu_ext_commit(&monomials, log_lde, &worker);
        let cpu_cap = cpu.get_cap().cap;
        let gpu = gpu_commit(&monomials, &shape, seed, &ctx);
        assert_eq!(gpu.cap, cpu_cap, "cap ({log_n}, {log_lde})");
        assert_eq!(gpu.cap_dst, cpu_cap, "cap destination ({log_n}, {log_lde})");
        let mut host_seed = Keccak256Seed(seed);
        <Keccak256Transcript as Transcript<PR, PR>>::commit_u32_with_seed(
            &mut host_seed,
            &cap_words(&cpu_cap),
        );
        assert_eq!(gpu.seed, host_seed.0, "seed ({log_n}, {log_lde})");
        let physical = <Keccak256MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<
            PR,
        >>::build_over_leaf_hashes(gpu.roots.clone(), 8, &worker);
        assert_eq!(physical.get_cap().cap, cpu_cap);
        let natural: Vec<_> = (0..cosets)
            .map(|k| gpu.roots[fft::bitreverse_index(k, log_lde)])
            .collect();
        let inverted = <Keccak256MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<
            PR,
        >>::build_over_leaf_hashes(natural, 8, &worker);
        assert_ne!(
            inverted.get_cap().cap,
            cpu_cap,
            "inverted root placement negative control"
        );
        let mut flipped = monomials.clone();
        flipped[5].add_assign(&PR::ONE);
        let gpu_flipped = gpu_commit(&flipped, &shape, seed, &ctx);
        assert_ne!(
            gpu_flipped.cap, cpu_cap,
            "flipped monomial negative control"
        );
        let tile_cosets = 1usize << shape.tile_cosets_log2;
        let k0 = cosets - tile_cosets;
        let monomials_dev = upload(&monomials, stream);
        let offsets = schedule_coset_offsets(&shape, &ctx).unwrap();
        let expected = cpu_tile_pass(&monomials, log_lde, k0, tile_cosets);
        for offsets in [Some(&offsets[..]), None] {
            let mut tile = upload(&vec![PR::ZERO; tile_cosets << log_n], stream);
            schedule_lde_convert_pass(&monomials_dev, &shape, offsets, k0 as u32, &mut tile, &ctx)
                .unwrap();
            assert_fields(&download(&tile, stream), &expected);
        }
    }
}

#[test]
#[ignore]
fn pr_commit_intermediate_n8_production() {
    let ctx = context(4096, Some(31));
    let stream = ctx.get_exec_stream();
    let worker = Worker::new();
    let schedule = pack4_wrap_schedule();
    let shape = L1WhirShape::from_schedule(&schedule, 25, 6, 2, L1_WHIR_TILE_BYTES).rounds[4]
        .oracle
        .unwrap();
    assert_eq!(
        (shape.log_n, shape.log_lde, shape.tile_cosets_log2),
        (8, 23, 18)
    );
    let mut rng = TestRng::new(0x7202);
    let monomials = rng.fields(1 << 8);
    let seed: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
    stream.synchronize().unwrap();
    let start = Instant::now();
    let gpu = gpu_commit(&monomials, &shape, seed, &ctx);
    println!(
        "pr_commit_intermediate_n8_production: GPU commit + readback wall {:.1} ms",
        start.elapsed().as_secs_f64() * 1e3
    );
    let start = Instant::now();
    let cpu_cap = cpu_ext_commit(&monomials, 23, &worker).get_cap().cap;
    println!(
        "pr_commit_intermediate_n8_production: CPU commit wall {:.1} s",
        start.elapsed().as_secs_f64()
    );
    assert_eq!(gpu.cap, cpu_cap);
    assert_eq!(gpu.cap_dst, cpu_cap);
    let tile_cosets = 1usize << shape.tile_cosets_log2;
    let k0 = (1usize << 23) - tile_cosets;
    let monomials_dev = upload(&monomials, stream);
    let mut tile = upload(&vec![PR::ZERO; tile_cosets << 8], stream);
    schedule_lde_convert_pass(&monomials_dev, &shape, None, k0 as u32, &mut tile, &ctx).unwrap();
    let twiddles = Twiddles::<PR, Global>::new(1 << 8, &worker);
    let conv = <Proth120WorkStealingLazyBackend as Backend<PR, PR>>::ext_coeff_conv(
        &Proth120WorkStealingLazyBackend,
        1 << 8,
        16,
    );
    let nu = fft::domain_generator_for_size::<PR>(1u64 << 31);
    for local in [65534usize, 65535, 65536] {
        let k = k0 + local;
        let offset = nu.pow(k as u32);
        let mut expected = vec![PR::ZERO; 1 << 8];
        fft::column_major::proth120_lazy::lde_coset_lazy_r8_into(
            &monomials,
            offset,
            &twiddles.forward_twiddles[..],
            &mut expected,
        );
        conv.apply_serial(&mut expected, offset);
        assert_fields(
            &download(&tile[local << 8..(local + 1) << 8], stream),
            &expected,
        );
    }
}

fn opening_oracle(log_n: u32, log_lde: u32, tile_log: u32, log_v: u32) -> OracleShape {
    let schedule = WhirSchedule::from_legacy_arrays(
        32,
        8,
        0,
        &[2, log_v as usize],
        &[1, 1],
        &[1 << log_lde],
        &[0, 0],
    );
    L1WhirShape::from_schedule(&schedule, log_n + 2, 5, 2, 16usize << (log_n + tile_log)).rounds[0]
        .oracle
        .unwrap()
}

fn opening_output(
    shape: &OracleShape,
    queries: usize,
    ctx: &ProverContext,
) -> super::outputs::IntermediateProofDevice {
    use gpu_core::allocator::tracker::AllocationPlacement::BestFit;
    super::outputs::IntermediateProofDevice {
        cap: ctx.alloc(1 << shape.cap_log, BestFit).unwrap(),
        leaves: ctx.alloc(queries << shape.log_v, BestFit).unwrap(),
        paths: ctx.alloc(queries * shape.path_len, BestFit).unwrap(),
        tree_indexes: ctx.alloc(queries, BestFit).unwrap(),
    }
}

fn opening_queries(shape: &OracleShape, count: usize) -> Vec<u32> {
    let c = 1u32 << shape.log_lde;
    let l = 1u32 << shape.log_leaves;
    let k = 1u32 << shape.skip_bottom;
    let q = [
        c * (l - 1) + c - 1,
        0,
        c * (k - 1) + 3,
        c * (k - 2) + 3,
        c * (l - 1) + c - 1,
        c - 1,
        c * (l / 2) + 7,
        c * (l / 2 + 1) + 7,
        c * (l - 2) + 1,
        c + 1,
        c * (l / 2) + c - 1,
        c * (k / 2) + 3,
        c * (l - 1),
    ];
    q[..count].to_vec()
}

fn host_keccak(bytes: &[u8]) -> [u32; 8] {
    use sha3::{Digest, Keccak256};
    let bytes = Keccak256::digest(bytes);
    let mut digest =
        std::array::from_fn(|i| u32::from_be_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap()));
    prover::merkle_trees::keccak256_hash_leafs::truncate_keccak_merkle_digest(&mut digest);
    digest
}

fn reconstruct_cap(values: &[PR], path: &[[u32; 8]], index: u32) -> (usize, [u32; 8]) {
    let bytes: Vec<u8> = values
        .iter()
        .flat_map(|x| x.to_u128().to_be_bytes())
        .collect();
    let mut digest = host_keccak(&bytes);
    let mut index = index;
    for sibling in path {
        let (left, right) = if index & 1 == 0 {
            (&digest, sibling)
        } else {
            (sibling, &digest)
        };
        let bytes: Vec<u8> = left
            .iter()
            .chain(right)
            .flat_map(|x| x.to_be_bytes())
            .collect();
        digest = host_keccak(&bytes);
        index >>= 1;
    }
    (index as usize, digest)
}

fn assert_openings(
    shape: &OracleShape,
    queries: &[u32],
    cpu: &ExtCommitment,
    twiddles: &Twiddles<PR, Global>,
    out: &super::outputs::IntermediateProofDevice,
    ctx: &ProverContext,
    worker: &Worker,
) {
    let stream = ctx.get_exec_stream();
    let leaves = download(&out.leaves, stream);
    let paths = download(&out.paths, stream);
    let indexes = download(&out.tree_indexes, stream);
    let expected = cpu.query_many(
        &queries.iter().map(|&q| q as usize).collect::<Vec<_>>(),
        twiddles,
        worker,
    );
    let cap = cpu.get_cap();
    let cap = cap.cap.as_slice();
    for (i, (coset, values, proof)) in expected.iter().enumerate() {
        assert_eq!(*coset as u32, queries[i] & ((1 << shape.log_lde) - 1));
        let values_gpu = &leaves[i << shape.log_v..(i + 1) << shape.log_v];
        let path_gpu = &paths[i * shape.path_len..(i + 1) * shape.path_len];
        assert_fields(values_gpu, values);
        assert_fields(values_gpu, &proof.leaf_values_concatenated);
        assert_eq!(indexes[i] as usize, proof.index, "query {i} index");
        assert_eq!(path_gpu, &proof.path, "query {i} path");
        let (cap_index, digest) = reconstruct_cap(values_gpu, path_gpu, indexes[i]);
        assert_eq!(digest, cap[cap_index], "query {i} cap reconstruction");
        let mut wrong_path = path_gpu.to_vec();
        wrong_path[0][0] ^= 1;
        assert_ne!(
            reconstruct_cap(values_gpu, &wrong_path, indexes[i]).1,
            cap[cap_index]
        );
    }
}

fn assert_l1_2p21_oracle_sampled(round: usize, expected: (u32, u32, u32)) {
    use super::openings::schedule_open_intermediate;

    let config = ProofProfile::L1Wrap.prover_config(21, SecurityLevel::Sec100);
    let whir = L1WhirShape::from_schedule(&config.whir_schedule, 24, 7, 1, L1_WHIR_TILE_BYTES);
    let shape = whir.rounds[round].oracle.expect("committed 2p21 oracle");
    assert_eq!((shape.log_n, shape.log_lde, shape.log_v), expected);
    assert_eq!(shape.log_domain, 31);

    assert_eq!(shape.cap_log, 3);
    assert_eq!(
        shape.path_len,
        (shape.log_domain - shape.log_v - shape.cap_log) as usize
    );
    assert_eq!(shape.tile_cosets_log2, [3, 7, 11, 15][round]);
    assert_eq!(shape.skip_bottom, [5, 5, 5, 5][round]);
    assert_eq!(shape.retained_per_coset, [32767, 2047, 127, 7][round]);
    let started = Instant::now();
    let mut rng = TestRng::new(0x0021_7200 + round as u64);
    let monomials = rng.fields(1 << shape.log_n);
    let query_log = shape.log_domain - shape.log_v;
    let query_mask = (1u32 << query_log) - 1;
    let mut queries = vec![0, query_mask];
    while queries.len() < 10 {
        let query = rng.next_u64() as u32 & query_mask;
        if !queries.contains(&query) {
            queries.push(query);
        }
    }
    // A WHIR leaf contains the coefficients of f(X) modulo X^V - y,
    // where V = 2^log_v and y = generator^(query * V). Evaluate the V
    // interleaved monomial polynomials by Horner, without building an LDE/tree.
    let generator = fft::domain_generator_for_size::<PR>(1u64 << shape.log_domain);
    let expected_leaves = std::thread::scope(|scope| {
        let handles: Vec<_> = queries
            .iter()
            .map(|&query| {
                let monomials = &monomials;
                scope.spawn(move || {
                    let y = generator.pow(query << shape.log_v);
                    let mut values = vec![PR::ZERO; 1 << shape.log_v];
                    for coefficients in monomials.chunks_exact(values.len()).rev() {
                        for (value, coefficient) in values.iter_mut().zip(coefficients) {
                            value.mul_assign(&y).add_assign(coefficient);
                        }
                    }
                    values
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|handle| handle.join().unwrap())
            .collect::<Vec<_>>()
    });
    let cpu_seconds = started.elapsed().as_secs_f64();

    let ctx = context(4096, Some(shape.log_domain));
    let stream = ctx.get_exec_stream();
    let monomials_dev = upload(&monomials, stream);
    let seed_bytes: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
    let mut seed_dev = upload(&seed_bytes, stream);
    let mut cap_dst = upload(&vec![[0u32; 8]; 1 << shape.cap_log], stream);
    let oracle =
        schedule_commit_intermediate(&monomials_dev, &shape, &mut cap_dst, &mut seed_dev, &ctx)
            .unwrap();
    let queries_dev = upload(&queries, stream);
    let mut out = opening_output(&shape, queries.len(), &ctx);
    schedule_open_intermediate(&oracle, &queries_dev, query_log, &mut out, &ctx).unwrap();
    assert_eq!(oracle.shape, shape);
    assert_eq!(oracle.monomials.len(), monomials.len());
    assert_eq!(oracle.roots.len(), 1 << shape.log_lde);
    assert_eq!(
        oracle.top_nodes.len(),
        (1 << shape.log_lde) - (1 << shape.cap_log)
    );
    assert_eq!(
        oracle.retained.len(),
        (1 << shape.log_lde) * shape.retained_per_coset
    );
    let cap = download(&oracle.cap, stream);
    assert_eq!(cap.len(), 1 << shape.cap_log);
    assert_eq!(download(&cap_dst, stream), cap);
    let mut cpu_seed = Keccak256Seed(seed_bytes);
    <Keccak256Transcript as Transcript<PR, PR>>::commit_u32_with_seed(
        &mut cpu_seed,
        &cap_words(&cap),
    );
    assert_eq!(download(&seed_dev, stream), cpu_seed.0);
    let leaves = download(&out.leaves, stream);
    let paths = download(&out.paths, stream);
    let indexes = download(&out.tree_indexes, stream);
    assert_eq!(leaves.len(), queries.len() << shape.log_v);
    assert_eq!(paths.len(), queries.len() * shape.path_len);
    assert_eq!(indexes.len(), queries.len());
    for (i, &query) in queries.iter().enumerate() {
        let values = &leaves[i << shape.log_v..(i + 1) << shape.log_v];
        assert_fields(values, &expected_leaves[i]);
        let coset = query as usize & ((1 << shape.log_lde) - 1);
        let leaf = query as usize >> shape.log_lde;
        let tree_index = (fft::bitreverse_index(coset, shape.log_lde) << shape.log_leaves) | leaf;
        assert_eq!(indexes[i] as usize, tree_index, "query {i} index");
        let path = &paths[i * shape.path_len..(i + 1) * shape.path_len];
        let (cap_index, digest) = reconstruct_cap(values, path, indexes[i]);
        assert_eq!(digest, cap[cap_index], "query {i} cap reconstruction");
        let mut wrong_path = path.to_vec();
        wrong_path[0][0] ^= 1;
        assert_ne!(
            reconstruct_cap(values, &wrong_path, indexes[i]).1,
            cap[cap_index]
        );
    }
    eprintln!(
        "L1_2P21_ORACLE sampled={} shape={expected:?} cpu_horner_s={cpu_seconds:.3} total_s={:.3}",
        queries.len(),
        started.elapsed().as_secs_f64()
    );
}

#[test]
fn pr_l1_2p21_oracle_sampled_23_8_4() {
    assert_l1_2p21_oracle_sampled(0, (23, 8, 4));
}

#[test]
fn pr_l1_2p21_oracle_sampled_19_12_4() {
    assert_l1_2p21_oracle_sampled(1, (19, 12, 4));
}

#[test]
fn pr_l1_2p21_oracle_sampled_15_16_4() {
    assert_l1_2p21_oracle_sampled(2, (15, 16, 4));
}

#[test]
fn pr_l1_2p21_oracle_sampled_11_20_4() {
    assert_l1_2p21_oracle_sampled(3, (11, 20, 4));
}

fn host_sibling_offset(log_leaves: u32, skip_bottom: u32, level: u32, j: u32) -> usize {
    gpu_hash::keccak256::retained_layer_offset(log_leaves, skip_bottom, level)
        + ((j >> level) ^ 1) as usize
}

#[test]
fn pr_open_intermediate_matches_cpu_small() {
    use super::openings::schedule_open_intermediate;
    let ctx = context(128, Some(19));
    let stream = ctx.get_exec_stream();
    let worker = worker();
    let mut rng = TestRng::new(0x7130_7eaf);
    for (log_n, log_lde, tile_log, log_v) in [
        (12, 7, 2, 4),
        (8, 11, 8, 4),
        (10, 9, 9, 4),
        (10, 9, 9, 2),
        (8, 11, 1, 4),
        (11, 8, 0, 4),
        (11, 8, 3, 3),
    ] {
        let shape = opening_oracle(log_n, log_lde, tile_log, log_v);
        let monomials = rng.fields(1 << log_n);
        let twiddles = Twiddles::new(monomials.len(), &worker);
        let cpu =
            ExtCommitment::commit(&monomials, &twiddles, 1 << log_lde, 1 << log_v, 8, &worker);
        let mut state = L1WhirState::new(log_n, 0, &ctx).unwrap();
        memory_copy_async(&mut state.monomials, &monomials, stream).unwrap();
        memory_copy_async(&mut state.evals, &monomials, stream).unwrap();
        memory_copy_async(&mut state.eq, &monomials, stream).unwrap();
        let mut cap = upload(&[[0u32; 8]; 8], stream);
        let mut seed = upload(&[0u8; 32], stream);
        let mut oracle =
            schedule_commit_intermediate(&state.monomials, &shape, &mut cap, &mut seed, &ctx)
                .unwrap();
        let challenge = upload(&[rng.field()], stream);
        schedule_fold_state(&mut state, &challenge, &ctx).unwrap();
        schedule_fold_state(&mut state, &challenge, &ctx).unwrap();
        assert_eq!(state.current_len, monomials.len() / 4);
        assert_fields(&download(&oracle.monomials, stream), &monomials);
        assert_ne!(
            download(&state.monomials, stream),
            monomials[..monomials.len() / 4]
        );
        assert_eq!(download(&oracle.cap, stream), cpu.get_cap().cap.as_slice());
        for count in [1, 5, 13] {
            let queries = opening_queries(&shape, count);
            let queries_dev = upload(&queries, stream);
            let mut out = opening_output(&shape, count, &ctx);
            schedule_open_intermediate(
                &oracle,
                &queries_dev,
                shape.log_domain - shape.log_v,
                &mut out,
                &ctx,
            )
            .unwrap();
            assert_openings(&shape, &queries, &cpu, &twiddles, &out, &ctx, &worker);
            let retained = download(&oracle.retained, stream);
            let paths = download(&out.paths, stream);
            for (i, &q) in queries.iter().enumerate() {
                for level in shape.skip_bottom..shape.log_leaves {
                    let c = q & ((1 << shape.log_lde) - 1);
                    let j = q >> shape.log_lde;
                    let offset = c as usize * shape.retained_per_coset
                        + host_sibling_offset(shape.log_leaves, shape.skip_bottom, level, j);
                    assert_eq!(paths[i * shape.path_len + level as usize], retained[offset]);
                }
            }
        }
        let queries = upload(&[0u32], stream);
        let mut out = opening_output(&shape, 1, &ctx);
        oracle.shape.skip_bottom = shape.log_leaves.min(5) + 1;
        let error = catch_unwind(AssertUnwindSafe(|| {
            schedule_open_intermediate(
                &oracle,
                &queries,
                shape.log_domain - shape.log_v,
                &mut out,
                &ctx,
            )
        }))
        .unwrap_err();
        assert!(panic_text(error).contains("Proth120 WHIR: skip_bottom exceeds min(5, h)"));
        oracle.shape = shape;
        let error = catch_unwind(AssertUnwindSafe(|| {
            schedule_open_intermediate(&oracle, &queries, shape.log_domain + 1, &mut out, &ctx)
        }))
        .unwrap_err();
        assert!(panic_text(error).contains("Proth120 WHIR: log_domain below query_domain_log2"));
        let mut empty = opening_output(&shape, 0, &ctx);
        schedule_open_intermediate(
            &oracle,
            &queries[..0],
            shape.log_domain - shape.log_v,
            &mut empty,
            &ctx,
        )
        .unwrap();
    }
}

#[test]
fn pr_horner_leaves_match_cpu_small() {
    use super::openings::schedule_horner_leaves;
    let ctx = context(128, Some(19));
    let stream = ctx.get_exec_stream();
    let worker = worker();
    let mut rng = TestRng::new(0x7130_80a1);
    for (log_n, log_lde, log_v) in [(12, 7, 4), (8, 11, 4), (10, 9, 4), (10, 9, 2)] {
        let shape = opening_oracle(log_n, log_lde, log_lde, log_v);
        let monomials = rng.fields(1 << log_n);
        let twiddles = Twiddles::new(monomials.len(), &worker);
        let cpu =
            ExtCommitment::commit(&monomials, &twiddles, 1 << log_lde, 1 << log_v, 8, &worker);
        let queries = opening_queries(&shape, 13);
        let generator = fft::domain_generator_for_size::<PR>(1 << shape.log_domain);
        let points: Vec<_> = queries.iter().map(|&q| generator.pow(q << log_v)).collect();
        let points_dev = upload(&points, stream);
        let monomials_dev = upload(&monomials, stream);
        let mut leaves = upload(&vec![PR::ZERO; queries.len() << log_v], stream);
        schedule_horner_leaves(
            &monomials_dev,
            log_n,
            log_v,
            &points_dev,
            &mut leaves,
            0,
            &ctx,
        )
        .unwrap();
        let actual = download(&leaves, stream);
        for (i, &q) in queries.iter().enumerate() {
            assert_fields(
                &actual[i << log_v..(i + 1) << log_v],
                &cpu.query(q as usize, &twiddles, &worker).1,
            );
        }
    }
}

#[test]
fn pr_subtree_points_wide_context_match_cpu() {
    use gpu_ntt::proth120::DeviceContext;
    let ntt = DeviceContext::create(33).unwrap();
    let stream = CudaStream::create().unwrap();
    let mut rng = TestRng::new(0x7133_0d01);
    for (log_domain, log_v, log_lde, skip_bottom) in [(33, 1, 9, 5), (33, 4, 9, 5), (31, 2, 6, 5)] {
        let query_domain_log2 = log_domain - log_v;
        let domain = 1u64 << query_domain_log2;
        let mut queries = vec![(domain - 1) as u32, 0, (domain >> 1) as u32];
        queries.extend((0..5).map(|_| (rng.next_u64() % domain) as u32));
        let queries_dev = upload(&queries, &stream);
        let mut points = upload(&vec![PR::ZERO; queries.len() << skip_bottom], &stream);
        super::kernels::subtree_points(
            &queries_dev,
            query_domain_log2,
            log_lde,
            skip_bottom,
            ntt.descriptor(),
            log_domain,
            &mut points,
            &stream,
        )
        .unwrap();
        let actual = download(&points, &stream);
        let generator = fft::domain_generator_for_size::<PR>(1u64 << log_domain);
        let k = 1u64 << skip_bottom;
        let expected: Vec<PR> = queries
            .iter()
            .flat_map(|&q| {
                let q = q as u64;
                let c = q & ((1 << log_lde) - 1);
                let j = q >> log_lde;
                (0..k).map(move |t| {
                    let q_m = c + (((j & !(k - 1)) + t) << log_lde);
                    generator.pow_u128(((q_m << log_v) as u128) % (1u128 << log_domain))
                })
            })
            .collect();
        assert_fields(&actual, &expected);
    }
}

fn invalid_opening_query_traps(extract: bool) {
    use std::mem::ManuallyDrop;
    let ctx = ManuallyDrop::new(context(32, Some(19)));
    let stream = ctx.get_exec_stream();
    let shape = small_oracle(8, 11, 16 << 16);
    let queries = ManuallyDrop::new(upload(&[1u32 << 15], stream));
    let mut points = ManuallyDrop::new(upload(&[PR::ZERO; 16], stream));
    let leaves = ManuallyDrop::new(upload(&[PR::ZERO; 256], stream));
    let towers = ManuallyDrop::new(upload(&[[0u32; 8]; 31], stream));
    let retained = ManuallyDrop::new(upload(&vec![[0u32; 8]; 2048], stream));
    let mut out = ManuallyDrop::new(opening_output(&shape, 1, &ctx));
    if extract {
        let out = &mut *out;
        super::kernels::extract_paths(
            &leaves,
            &towers,
            &retained,
            1,
            11,
            4,
            4,
            4,
            &queries,
            &mut out.leaves,
            &mut out.paths,
            12,
            stream,
        )
        .unwrap();
    } else {
        super::kernels::subtree_points(
            &queries,
            15,
            11,
            4,
            ctx.proth120_ntt_device_context().descriptor(),
            19,
            &mut points,
            stream,
        )
        .unwrap();
    }
    let error = stream
        .synchronize()
        .expect_err("invalid query must trap before deriving a pointer");
    assert_eq!(error, era_cudart_sys::CudaError::ErrorLaunchFailure);
    eprintln!("invalid_opening_query_traps: extract={extract} expected device error {error:?}");
}

#[test]
fn pr_open_intermediate_rejects_invalid_query() {
    invalid_opening_query_traps(false);
}

#[test]
fn pr_extract_paths_rejects_invalid_query() {
    invalid_opening_query_traps(true);
}

#[test]
#[ignore]
fn pr_horner_open_n24_production() {
    use super::openings::{schedule_horner_leaves, schedule_open_intermediate};
    use era_cudart::event::{elapsed_time, CudaEvent};
    let preflight = std::process::Command::new("nvidia-smi")
        .args(["--query-gpu=name,uuid,driver_version,memory.total,pstate,clocks.current.sm,clocks.current.memory,power.limit,temperature.gpu", "--format=csv"])
        .output().unwrap();
    assert!(
        preflight.status.success(),
        "GPU measurement preflight failed"
    );
    eprintln!(
        "pr_horner_open_n24_production: preflight\n{}",
        String::from_utf8_lossy(&preflight.stdout)
    );
    let processes = std::process::Command::new("nvidia-smi")
        .args([
            "--query-compute-apps=pid,process_name,used_gpu_memory",
            "--format=csv",
        ])
        .output()
        .unwrap();
    assert!(processes.status.success(), "GPU process preflight failed");
    eprintln!("{}", String::from_utf8_lossy(&processes.stdout));
    let worker = Worker::new_with_num_threads(48);
    let mut rng = TestRng::new(0x0071_3024);
    let monomials = rng.fields(1 << 24);
    let twiddles = Twiddles::new(monomials.len(), &worker);
    let start = Instant::now();
    let cpu = ExtCommitment::commit(&monomials, &twiddles, 128, 16, 8, &worker);
    eprintln!(
        "pr_horner_open_n24_production: CPU commit wall {:.3} s",
        start.elapsed().as_secs_f64()
    );
    let ctx = context(4096, Some(31));
    let stream = ctx.get_exec_stream();
    let shape = small_oracle(24, 7, L1_WHIR_TILE_BYTES);
    assert_eq!(shape.tile_cosets_log2, 2);
    let mut cap = upload(&[[0u32; 8]; 8], stream);
    let mut seed = upload(&[0u8; 32], stream);
    let monomials_dev = upload(&monomials, stream);
    let oracle =
        schedule_commit_intermediate(&monomials_dev, &shape, &mut cap, &mut seed, &ctx).unwrap();
    let queries = [((1u32 << shape.log_leaves) - 19) * 128 + 37];
    let queries_dev = upload(&queries, stream);
    let mut out = opening_output(&shape, 1, &ctx);
    schedule_open_intermediate(&oracle, &queries_dev, 27, &mut out, &ctx).unwrap();
    assert_eq!(download(&oracle.cap, stream), cpu.get_cap().cap.as_slice());
    assert_openings(&shape, &queries, &cpu, &twiddles, &out, &ctx, &worker);
    let k = 1usize << shape.skip_bottom;
    let mut points = upload(&vec![PR::ZERO; k], stream);
    let mut leaves = upload(&vec![PR::ZERO; k << shape.log_v], stream);
    super::kernels::subtree_points(
        &queries_dev,
        27,
        7,
        shape.skip_bottom,
        ctx.proth120_ntt_device_context().descriptor(),
        31,
        &mut points,
        stream,
    )
    .unwrap();
    let start = CudaEvent::create().unwrap();
    let end = CudaEvent::create().unwrap();
    start.record(stream).unwrap();
    schedule_horner_leaves(
        &oracle.monomials,
        24,
        4,
        &points,
        &mut leaves,
        shape.skip_bottom,
        &ctx,
    )
    .unwrap();
    end.record(stream).unwrap();
    stream.synchronize().unwrap();
    eprintln!("pr_horner_open_n24_production: Horner CUDA-event {:.3} ms; log_n=24 log_v=4 Q=1 K=32 blocks=32 threads=256 warmed=true", elapsed_time(&start, &end).unwrap());
    let actual = download(&leaves, stream);
    let c = queries[0] & 127;
    let j = (queries[0] >> 7) & !(k as u32 - 1);
    let nu = fft::domain_generator_for_size::<PR>(1u64 << 31);
    let offset = nu.pow(c);
    let mut expected = vec![PR::ZERO; monomials.len()];
    fft::column_major::proth120_lazy::lde_coset_lazy_r8_into(
        &monomials,
        offset,
        &twiddles.forward_twiddles,
        &mut expected,
    );
    let conv = <Proth120WorkStealingLazyBackend as Backend<PR, PR>>::ext_coeff_conv(
        &Proth120WorkStealingLazyBackend,
        monomials.len(),
        16,
    );
    conv.apply_serial(&mut expected, offset);
    for a in 0..k {
        for t in 0..16usize {
            let slot = t.reverse_bits() >> (usize::BITS - 4);
            assert_fields(
                &actual[a + slot * k..][..1],
                &expected[j as usize + a + (slot << shape.log_leaves)..][..1],
            );
        }
    }
}

#[allow(clippy::needless_pass_by_value)]
fn panic_text(error: Box<dyn std::any::Any + Send>) -> String {
    if let Some(message) = error.downcast_ref::<String>() {
        message.clone()
    } else if let Some(message) = error.downcast_ref::<&str>() {
        (*message).to_owned()
    } else {
        panic!("unexpected panic payload")
    }
}

fn folded_query_index(tree_index: usize, log_leaves: u32, log_lde: u32) -> u32 {
    let coset = fft::bitreverse_index(tree_index >> log_leaves, log_lde);
    let leaf = tree_index & ((1 << log_leaves) - 1);
    (coset + (leaf << log_lde)) as u32
}

struct HostReplay {
    seed: Keccak256Seed,
}

impl HostReplay {
    fn commit_fields(&mut self, values: &[PR]) {
        <Keccak256Transcript as Transcript<PR, PR>>::commit_extension_field_elements(
            &mut self.seed,
            values,
        );
    }
    fn commit_u32(&mut self, words: &[u32]) {
        <Keccak256Transcript as Transcript<PR, PR>>::commit_u32_with_seed(&mut self.seed, words);
    }
    fn draw_fields(&mut self, count: usize) -> Vec<PR> {
        let mut out = vec![PR::ZERO; count];
        <Keccak256Transcript as Transcript<PR, PR>>::draw_random_field_elements(
            &mut self.seed,
            &mut out,
        );
        out
    }
}

#[test]
fn pr_transcript_phases_match_cpu_small() {
    let schedule = small_schedule();
    let initial = [0x47; 32];
    let mut rng = TestRng::new(0x5748_4952);
    let memory = vec![rng.fields(1 << 10), rng.fields(1 << 10)];
    let setup = vec![rng.fields(1 << 10)];
    let point = rng.fields(10);
    let (proof, _, _, initial) =
        cpu_whir_small(&memory, &setup, &point, initial, &schedule, 4, &worker());
    let whir = &proof;
    let shape = L1WhirShape::from_schedule(&schedule, 14, 5, 2, 16 << 14);
    assert_whir_transcript_phases(whir, initial, &shape);
}

#[test]
#[ignore = "production L1 WHIR query PoW and transcript draws on GPU"]
fn pr_transcript_phases_match_reference() {
    #[derive(serde::Deserialize)]
    struct Bundle {
        proof: verifier_evm::seed::Proof,
        operation_mode: prover::gkr::prover::OperationMode,
    }
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let directory = std::env::var_os("AB_PROTH120_REFERENCE_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| root.join("prover_pipeline/fixtures/l1_reference_2p21"));
    let bundle: Bundle =
        serde_json::from_reader(std::fs::File::open(directory.join("l1_bundle.json")).unwrap())
            .unwrap();
    let circuit: verifier_evm::seed::Circuit = serde_json::from_reader(
        std::fs::File::open(
            root.join("cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120_2p21.json"),
        )
        .unwrap(),
    )
    .unwrap();
    let config = ProofProfile::L1Wrap.prover_config(21, SecurityLevel::Sec100);
    let whir = &bundle.proof.whir_proof;
    assert_eq!(whir.whir_schedule, config.whir_schedule);
    assert_eq!(config.whir_message_size_log2(), 24);
    assert_eq!(config.lde_factor(), 128);
    assert_eq!(config.cap_size, 8);
    assert_eq!(config.whir_schedule.fold_steps(), [1, 4, 4, 4, 4]);
    assert_eq!(config.whir_schedule.queries_per_round(), [12, 11, 7, 6, 5]);
    assert_eq!(
        config.whir_schedule.queries_pow_bits_per_round(),
        [30, 27, 30, 20, 17]
    );
    // This CPU encoder oracle is independent of the GPU stage-test GKR replay.
    let cpu = verifier_evm::encoding::replay_gkr_points(
        &circuit,
        &bundle.proof,
        &bundle.operation_mode,
        &config,
    );
    let shape = L1WhirShape::from_schedule(&config.whir_schedule, 24, 7, 1, L1_WHIR_TILE_BYTES);
    assert_whir_transcript_phases(whir, cpu.handoff_seed, &shape);
}

fn assert_whir_transcript_phases(
    whir: &super::L1WhirProof,
    initial: [u8; 32],
    shape: &L1WhirShape,
) {
    let ctx = context(256, None);
    let stream = ctx.get_exec_stream();
    let whir_polys: Vec<_> = whir.all_sumcheck_polys().copied().collect();
    let whir_ood: Vec<_> = whir.all_ood_samples().copied().collect();
    let whir_nonces = whir.queries_pow_nonces();
    let mut host = HostReplay {
        seed: Keccak256Seed(initial),
    };
    let mut seed = upload(&initial, stream);
    let mut nonces = upload(&vec![0u64; shape.rounds.len()], stream);
    let mut polys = whir_polys.iter();
    for (r, round) in shape.rounds.iter().enumerate() {
        for _ in 0..round.folds {
            let poly = polys.next().unwrap();
            transcript_commit_fields(&mut seed, &upload(poly, stream), stream).unwrap();
            let mut alpha = upload(&[PR::ZERO], stream);
            transcript_draw_fields(&mut seed, &mut alpha, stream).unwrap();
            host.commit_fields(poly);
            assert_fields(&download(&alpha, stream), &host.draw_fields(1));
        }
        if round.oracle.is_some() {
            let words = cap_words(&whir.intermediate_whir_oracles[r].commitment.cap.cap);
            transcript_commit_u32(&mut seed, &upload(&words, stream), stream).unwrap();
            let mut ood_point = upload(&[PR::ZERO], stream);
            transcript_draw_fields(&mut seed, &mut ood_point, stream).unwrap();
            transcript_commit_fields(&mut seed, &upload(&[whir_ood[r]], stream), stream).unwrap();
            host.commit_u32(&words);
            assert_fields(&download(&ood_point, stream), &host.draw_fields(1));
            host.commit_fields(&[whir_ood[r]]);
        } else {
            transcript_commit_fields(&mut seed, &upload(&whir.final_monomials, stream), stream)
                .unwrap();
            host.commit_fields(&whir.final_monomials);
        }
        stream.synchronize().unwrap();
        let start = Instant::now();
        let indexes = schedule_pow_and_query_indexes(
            &mut seed,
            round.queries,
            round.pow_bits,
            round.query_domain_log2,
            unsafe { DeviceVariable::from_raw_parts_mut(nonces[r..].as_mut_ptr()) },
            &ctx,
        )
        .unwrap();
        let got = download(&indexes, stream);
        let seconds = start.elapsed().as_secs_f64();
        let (queries, log_leaves, log_lde) = if r == 0 {
            let memory: Vec<usize> = whir
                .memory_commitment
                .queries
                .iter()
                .map(|q| q.index)
                .collect();
            let setup: Vec<usize> = whir
                .setup_commitment
                .queries
                .iter()
                .map(|q| q.index)
                .collect();
            assert_eq!(memory, setup);
            (
                memory,
                round.query_domain_log2 - shape.log_base_lde,
                shape.log_base_lde,
            )
        } else {
            let oracle = shape.rounds[r - 1].oracle.unwrap();
            (
                whir.intermediate_whir_oracles[r - 1]
                    .queries
                    .iter()
                    .map(|q| q.index)
                    .collect(),
                oracle.log_leaves,
                oracle.log_lde,
            )
        };
        let expected: Vec<u32> = queries
            .iter()
            .map(|&index| folded_query_index(index, log_leaves, log_lde))
            .collect();
        assert_eq!(got, expected, "round {r} folded query indexes");
        let nonce = download(&nonces[r..r + 1], stream)[0];
        assert_eq!(nonce, whir_nonces[r], "round {r} nonce");
        println!(
            "pr_transcript_phases_match_reference round {r} pow bits={} nonce={nonce} seconds={seconds:.3}",
            round.pow_bits
        );
        <Keccak256Transcript as Transcript<PR, PR>>::verify_pow(
            &mut host.seed,
            nonce,
            round.pow_bits,
        );
        let mut words = vec![0u32; query_words(round.queries, round.query_domain_log2)];
        <Keccak256Transcript as Transcript<PR, PR>>::draw_randomness(&mut host.seed, &mut words);
        if round.oracle.is_some() {
            let powers = schedule_delinearization(&mut seed, round.queries, &ctx).unwrap();
            let delta = host.draw_fields(1)[0];
            let mut expected = vec![delta];
            for i in 1..=round.queries {
                let mut next = expected[i - 1];
                next.mul_assign(&delta);
                expected.push(next);
            }
            assert_fields(&download(&powers, stream), &expected);
        }
        assert_eq!(download(&seed, stream), host.seed.0, "round {r} seed");
    }
    assert!(polys.next().is_none());
    assert_eq!(download(&nonces, stream), whir_nonces);
}

fn host_three(evals: &[PR], eq: &[PR]) -> [PR; 3] {
    let (a, b, mut d) = special_three_point_eval::<PR, PR>(evals, eq, &worker());
    d.double();
    d.double();
    [a, b, d]
}

fn host_interpolate([a, b, d]: [PR; 3]) -> [PR; 3] {
    let mut three_a = a;
    three_a.double();
    three_a.add_assign(&a);
    let mut c1 = d;
    c1.sub_assign(&three_a);
    c1.sub_assign(&b);
    let mut c2 = a;
    c2.add_assign(&b);
    c2.double();
    c2.sub_assign(&d);
    [a, c1, c2]
}

fn add3(x: [PR; 3], y: [PR; 3]) -> [PR; 3] {
    std::array::from_fn(|i| {
        let mut v = x[i];
        v.add_assign(&y[i]);
        v
    })
}

struct DenseModel {
    monomials: Vec<PR>,
    evals: Vec<PR>,
    eq: Vec<PR>,
    query_eq: Vec<PR>,
    seed: Keccak256Seed,
}

impl DenseModel {
    fn add_terms(&mut self, indexes: &[u32], weights: &[PR], query_domain_log2: u32) {
        let generator = fft::domain_generator_for_size::<PR>(1u64 << query_domain_log2);
        let samples: Vec<(PR, PR)> = indexes
            .iter()
            .zip(weights)
            .map(|(&index, &weight)| (generator.pow(index), weight))
            .collect();
        <Proth120WorkStealingLazyBackend as Backend<PR, PR>>::update_eq_poly(
            &Proth120WorkStealingLazyBackend,
            &mut self.query_eq,
            &[],
            &samples,
            &worker(),
        );
    }

    fn step(&mut self) -> ([PR; 3], [PR; 3], [PR; 3], PR) {
        let dense = host_three(&self.evals, &self.eq);
        let query = host_three(&self.evals, &self.query_eq);
        let coeffs = host_interpolate(add3(dense, query));
        <Keccak256Transcript as Transcript<PR, PR>>::commit_extension_field_elements(
            &mut self.seed,
            &coeffs,
        );
        let mut alpha = [PR::ZERO];
        <Keccak256Transcript as Transcript<PR, PR>>::draw_random_field_elements(
            &mut self.seed,
            &mut alpha,
        );
        let worker = worker();
        let mut buffer = Vec::with_capacity(self.monomials.len() / 2);
        fold_monomial_form(&mut self.monomials, &mut buffer, &alpha[0], &worker);
        let len = fold_evaluation_form::<PR, PR>(&mut self.evals, &alpha[0], &worker).len();
        self.evals.truncate(len);
        let len = fold_eq_poly::<PR, PR>(&mut self.eq, &alpha[0], &worker).len();
        self.eq.truncate(len);
        let len = fold_eq_poly::<PR, PR>(&mut self.query_eq, &alpha[0], &worker).len();
        self.query_eq.truncate(len);
        (dense, query, coeffs, alpha[0])
    }
}

fn gpu_terms(
    state: &mut L1WhirState,
    model: &mut DenseModel,
    indexes: &[u32],
    weights: &[PR],
    query_domain_log2: u32,
    ctx: &ProverContext,
) {
    let stream = ctx.get_exec_stream();
    state
        .in_domain
        .append(
            &upload(indexes, stream),
            &upload(weights, stream),
            query_domain_log2,
            fft::domain_generator_for_size::<PR>(1u64 << query_domain_log2),
            ctx,
        )
        .unwrap();
    model.add_terms(indexes, weights, query_domain_log2);
}

fn run_symbolic_group(
    state: &mut L1WhirState,
    model: &mut DenseModel,
    seed: &mut DeviceAllocation<u8>,
    folds: u32,
    ctx: &ProverContext,
) {
    let stream = ctx.get_exec_stream();
    for step in 0..folds {
        schedule_three_point(state, ctx).unwrap();
        let dense = download(&state.reduce_out, stream);
        let mut coeffs = upload(&[PR::ZERO; 3], stream);
        let mut alpha = upload(&[PR::ZERO], stream);
        schedule_round_update(state, seed, &mut coeffs, &mut alpha, ctx).unwrap();
        let corrected = download(&state.reduce_out, stream);
        let (host_dense, host_query, host_coeffs, host_alpha) = model.step();
        assert_fields(&dense, &host_dense);
        assert_fields(&corrected, &add3(host_dense, host_query));
        let corrections: Vec<PR> = corrected
            .iter()
            .zip(&dense)
            .map(|(c, d)| {
                let mut v = *c;
                v.sub_assign(d);
                v
            })
            .collect();
        assert_fields(&corrections, &host_query);
        assert_fields(&download(&coeffs, stream), &host_coeffs);
        assert_fields(&download(&alpha, stream), &[host_alpha]);
        assert_eq!(download(seed, stream), model.seed.0, "step {step} seed");
        schedule_fold_state(state, &alpha, ctx).unwrap();
        assert_fields(&download(&state.monomials, stream), &model.monomials);
        assert_fields(&download(&state.evals, stream), &model.evals);
        assert_fields(&download(&state.eq, stream), &model.eq);
    }
}

#[test]
fn pr_in_domain_symbolic_matches_dense() {
    let ctx = context(1024, Some(19));
    let stream = ctx.get_exec_stream();
    let mut rng = TestRng::new(0x7401);
    let shape = L1WhirShape::from_schedule(&small_schedule(), 14, 5, 2, 16 << 14);
    let oracle0 = shape.rounds[0].oracle.unwrap();
    let oracle1 = shape.rounds[1].oracle.unwrap();
    assert_eq!((oracle0.log_n, oracle1.log_n), (12, 8));
    let monomials = rng.fields(1 << 12);
    let mut evals = monomials.clone();
    multivariate_coeffs_into_hypercube_evals(&mut evals, 12);
    let eq = rng.fields(1 << 12);
    let seed_bytes: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
    let mut model = DenseModel {
        monomials: monomials.clone(),
        evals: evals.clone(),
        eq: eq.clone(),
        query_eq: vec![PR::ZERO; 1 << 12],
        seed: Keccak256Seed(seed_bytes),
    };
    let mut state = L1WhirState::new(12, shape.term_capacity, &ctx).unwrap();
    memory_copy_async(&mut state.monomials, &monomials, stream).unwrap();
    memory_copy_async(&mut state.evals, &evals, stream).unwrap();
    memory_copy_async(&mut state.eq, &eq, stream).unwrap();
    let mut seed = upload(&seed_bytes, stream);
    let mut cap = upload(&[[0u32; 8]; 8], stream);
    let mut commit_seed = upload(&[0u8; 32], stream);
    let oracle_a =
        schedule_commit_intermediate(&state.monomials, &oracle0, &mut cap, &mut commit_seed, &ctx)
            .unwrap();
    let qlog0 = shape.rounds[0].query_domain_log2;
    let first: Vec<u32> = [
        0,
        (1 << qlog0) - 1,
        5,
        5,
        (rng.next_u64() as u32) & ((1 << qlog0) - 1),
    ]
    .to_vec();
    let first_weights = rng.fields(first.len());
    gpu_terms(&mut state, &mut model, &first, &first_weights, qlog0, &ctx);
    state
        .in_domain
        .start_round(&oracle_a, state.current_len, oracle0.log_v, &ctx)
        .unwrap();
    run_symbolic_group(&mut state, &mut model, &mut seed, oracle0.log_v, &ctx);
    drop(oracle_a);
    let oracle_b =
        schedule_commit_intermediate(&state.monomials, &oracle1, &mut cap, &mut commit_seed, &ctx)
            .unwrap();
    let qlog1 = shape.rounds[1].query_domain_log2;
    let second: Vec<u32> = (0..4)
        .map(|_| (rng.next_u64() as u32) & ((1 << qlog1) - 1))
        .collect();
    let second_weights = rng.fields(second.len());
    gpu_terms(
        &mut state,
        &mut model,
        &second,
        &second_weights,
        qlog1,
        &ctx,
    );
    let [ood_point, ood_weight] = [rng.field(), rng.field()];
    schedule_eq_update(
        &mut state,
        &upload(&[ood_point], stream),
        &upload(&[ood_weight], stream),
        &ctx,
    )
    .unwrap();
    <Proth120WorkStealingLazyBackend as Backend<PR, PR>>::update_eq_poly(
        &Proth120WorkStealingLazyBackend,
        &mut model.eq,
        &[(ood_point, ood_weight)],
        &[],
        &worker(),
    );
    assert_fields(&download(&state.eq, stream), &model.eq);
    assert_eq!(state.in_domain.count(), 9);
    state
        .in_domain
        .start_round(&oracle_b, state.current_len, oracle1.log_v, &ctx)
        .unwrap();
    run_symbolic_group(&mut state, &mut model, &mut seed, oracle1.log_v, &ctx);
    assert_eq!(state.current_len, 16);

    let mut full = super::in_domain::InDomainState::new(48, &ctx).unwrap();
    let indexes = upload(&(0..48).collect::<Vec<u32>>(), stream);
    let weights = upload(&rng.fields(48), stream);
    full.append(
        &indexes,
        &weights,
        17,
        fft::domain_generator_for_size::<PR>(1 << 17),
        &ctx,
    )
    .unwrap();
    assert_eq!(full.count(), 48);
    let err = catch_unwind(AssertUnwindSafe(|| {
        full.append(&indexes[..1], &weights[..1], 17, PR::ONE, &ctx)
    }))
    .unwrap_err();
    let text = err
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| err.downcast_ref::<&str>().copied())
        .unwrap();
    assert!(
        text.contains("Proth120 WHIR: in-domain term capacity exceeded"),
        "{text}"
    );
}

fn cpu_whir_small(
    memory: &[Vec<PR>],
    setup: &[Vec<PR>],
    point: &[PR],
    seed: [u8; 32],
    schedule: &WhirSchedule,
    pack_log2: usize,
    worker: &Worker,
) -> (super::L1WhirProof, Vec<PR>, PR, [u8; 32]) {
    use prover::cs::definitions::GKRAddress;
    use prover::gkr::prover::{gkr_backend::NaiveGKRBackend, SetupCommitment};
    use prover::gkr::sumcheck::access_and_fold::{BaseFieldPoly, GKRLayerSource, GKRStorage};
    use prover::gkr::whir::coset_commit::CosetByCosetBaseCommitment;
    use prover::gkr::whir::{whir_fold, ColumnMajorBaseOracleForLDE, WhirIntermediateOracleMode};
    let mut config = prover::gkr::prover_config::ProverConfig {
        trace_len_log2: 10,
        cap_size: schedule.cap_size,
        whir_schedule: schedule.clone(),
        ..ProofProfile::L1Wrap.prover_config(21, SecurityLevel::Sec100)
    };
    config.whir_schedule.base_round.physical_packing_log2 = pack_log2;
    config.whir_schedule.base_round.batching_pow_bits = Some(0);
    assert_eq!(config.whir_message_size_log2(), 10 + pack_log2);
    assert_eq!(config.lde_factor(), if pack_log2 == 4 { 32 } else { 64 });
    assert_eq!(config.cap_size, 8);
    assert_eq!(
        config.base_oracles_values_per_leaf(),
        1 << schedule.fold_steps()[0]
    );
    assert_eq!(
        config.base_oracles_values_per_leaf().trailing_zeros(),
        if pack_log2 == 4 { 2 } else { 1 }
    );
    assert_eq!(
        config.commitment_mode,
        prover::gkr::prover::CommitmentMode::MergedMemoryAndWitness,
    );
    let twiddles = Twiddles::<PR, Global>::new(1 << config.whir_message_size_log2(), worker);
    let commit = |columns: &[Vec<PR>]| {
        CosetByCosetBaseCommitment::<PR, Keccak256MerkleTreeWithCap>::commit_packed(
            &columns.iter().map(Vec::as_slice).collect::<Vec<_>>(),
            &twiddles,
            schedule.base_lde_factor(),
            schedule.fold_steps()[0],
            8,
            10,
            pack_log2,
            worker,
        )
    };
    let memory_oracle = ColumnMajorBaseOracleForLDE::CosetRecompute(commit(memory));
    let setup_oracle =
        SetupCommitment::InMemory(ColumnMajorBaseOracleForLDE::CosetRecompute(commit(setup)));
    let mut layer = GKRLayerSource::default();
    for (i, column) in memory.iter().enumerate() {
        layer.base_field_inputs.insert(
            GKRAddress::BaseLayerMemory(i),
            BaseFieldPoly::new(column.clone().into_boxed_slice()),
        );
    }
    for (i, column) in setup.iter().enumerate() {
        layer.base_field_inputs.insert(
            GKRAddress::Setup(i),
            BaseFieldPoly::new(column.clone().into_boxed_slice()),
        );
    }
    let raw_claims = |columns: &[Vec<PR>]| {
        columns
            .iter()
            .map(|column| prover::gkr::whir::evaluate_multivariate(column, point, worker))
            .collect()
    };
    let proof = whir_fold::<
        PR,
        PR,
        Keccak256MerkleTreeWithCap,
        Keccak256Transcript,
        Proth120WorkStealingLazyBackend,
        NaiveGKRBackend,
    >(
        memory_oracle,
        raw_claims(memory),
        ColumnMajorBaseOracleForLDE::empty(
            1 << schedule.fold_steps()[0],
            10 + pack_log2,
            schedule.base_lde_factor(),
        ),
        vec![],
        &setup_oracle,
        raw_claims(setup),
        GKRStorage {
            layers: vec![layer],
        },
        &config,
        point.to_vec(),
        &twiddles,
        Keccak256Seed(seed),
        &Proth120WorkStealingLazyBackend,
        &NaiveGKRBackend,
        WhirIntermediateOracleMode::CosetByCoset,
        &GenericAllocationPool::<PR, PR>::proxy(),
        worker,
    );
    let mut replay = HostReplay {
        seed: Keccak256Seed(seed),
    };
    let mut extended_point = point.to_vec();
    extended_point.extend(replay.draw_fields(pack_log2));
    <Keccak256Transcript as Transcript<PR, PR>>::verify_pow(
        &mut replay.seed,
        proof.batching_challenge_pow_nonce,
        0,
    );
    let beta = replay.draw_fields(1)[0];
    (proof, extended_point, beta, replay.seed.0)
}

fn whir_end_seed(proof: &super::L1WhirProof, log_message: u32, initial: [u8; 32]) -> [u8; 32] {
    let schedule = &proof.whir_schedule;
    let shape = L1WhirShape::from_schedule(
        schedule,
        log_message,
        schedule.base_lde_factor().trailing_zeros(),
        schedule.fold_steps()[0] as u32,
        16 << log_message,
    );
    let mut replay = HostReplay {
        seed: Keccak256Seed(initial),
    };
    let sumcheck_polys: Vec<_> = proof.all_sumcheck_polys().copied().collect();
    let ood_samples: Vec<_> = proof.all_ood_samples().copied().collect();
    let pow_nonces = proof.queries_pow_nonces();
    let mut polys = sumcheck_polys.iter();
    for (r, round) in shape.rounds.iter().enumerate() {
        for _ in 0..round.folds {
            replay.commit_fields(polys.next().unwrap());
            replay.draw_fields(1);
        }
        if round.oracle.is_some() {
            replay.commit_u32(&cap_words(
                &proof.intermediate_whir_oracles[r].commitment.cap.cap,
            ));
            replay.draw_fields(1);
            replay.commit_fields(&ood_samples[r..r + 1]);
        } else {
            replay.commit_fields(&proof.final_monomials);
        }
        <Keccak256Transcript as Transcript<PR, PR>>::verify_pow(
            &mut replay.seed,
            pow_nonces[r],
            round.pow_bits,
        );
        let mut words = vec![0u32; query_words(round.queries, round.query_domain_log2)];
        <Keccak256Transcript as Transcript<PR, PR>>::draw_randomness(&mut replay.seed, &mut words);
        if round.oracle.is_some() {
            replay.draw_fields(1);
        }
    }
    replay.seed.0
}

fn json_difference(
    expected: &serde_json::Value,
    actual: &serde_json::Value,
    path: &str,
) -> Option<String> {
    if expected == actual {
        return None;
    }
    match (expected, actual) {
        (serde_json::Value::Object(expected), serde_json::Value::Object(actual)) => {
            for (key, value) in expected {
                match actual.get(key) {
                    Some(other) => {
                        if let Some(diff) = json_difference(value, other, &format!("{path}.{key}"))
                        {
                            return Some(diff);
                        }
                    }
                    None => return Some(format!("{path}.{key} missing")),
                }
            }
        }
        (serde_json::Value::Array(expected), serde_json::Value::Array(actual)) => {
            if expected.len() != actual.len() {
                return Some(format!(
                    "{path} length {} != {}",
                    expected.len(),
                    actual.len()
                ));
            }
            for (i, (value, other)) in expected.iter().zip(actual).enumerate() {
                if let Some(diff) = json_difference(value, other, &format!("{path}[{i}]")) {
                    return Some(diff);
                }
            }
        }
        _ => {}
    }
    Some(format!("{path}: {expected} != {actual}"))
}

#[test]
fn pr_l1_whir_fold_matches_cpu_small() {
    assert_l1_whir_fold_matches_cpu_small(4, &small_schedule(), (7, 1), 10);
}

#[test]
fn pr_l1_whir_fold_matches_cpu_small_pack3() {
    assert_l1_whir_fold_matches_cpu_small(3, &small_pack3_schedule(), (13, 2), 9);
}

fn assert_l1_whir_fold_matches_cpu_small(
    pack_log2: usize,
    schedule: &WhirSchedule,
    packed_columns: (usize, usize),
    sumcheck_polys: usize,
) {
    use super::{schedule_l1_whir_fold, L1WhirInputs};
    use gpu_gkr::setup::proth120::{L1WrapSetupHost, PackedSetupSource};
    use gpu_prover_context::transfer::single_shot_h2d;
    use gpu_trace::trace::packed::{PackedCommitConfig, PackedCosetRecomputeOracle};
    use prover::allocation_pool::AllocationType;
    use prover::gkr::prover::setup::GKRSetup;
    use std::sync::Arc;
    let ctx = context(256, Some(19));
    let stream = ctx.get_exec_stream();
    let worker = worker();
    let mut rng = TestRng::new(0x7501_5eed);
    let mut memory: Vec<_> = (0..104).map(|_| rng.fields(1 << 10)).collect();
    let mut setup: Vec<_> = (0..10).map(|_| rng.fields(1 << 10)).collect();
    for c in [15, 16, 31, 32, 95, 96, 103] {
        memory[c][0] = PR::ZERO;
        memory[c][1] = PR::ONE;
        memory[c][2] = PR::new(PR::ORDER - 1);
        memory[c][3] = PR::from_u128_with_reduction(u128::MAX - c as u128);
    }
    setup[9][0] = PR::ZERO;
    setup[9][1] = PR::ONE;
    setup[9][2] = PR::new(PR::ORDER - 1);
    setup[9][3] = PR::from_u128_with_reduction(u128::MAX);
    let log_message = 10 + pack_log2 as u32;
    let cfg = PackedCommitConfig {
        log_lde_factor: schedule.base_lde_factor().trailing_zeros(),
        log_values_per_leaf: schedule.fold_steps()[0] as u32,
        cap_log: 3,
        skip_bottom: 5,
    };
    let setup_cpu = GKRSetup {
        hypercube_evals: setup
            .iter()
            .cloned()
            .map(|column| Arc::new(AllocationType::from(column.into_boxed_slice())))
            .collect(),
    };
    let setup_host =
        Arc::new(L1WrapSetupHost::precompute(&setup_cpu, pack_log2 as u32, cfg, &ctx).unwrap());
    let flat: Vec<_> = memory.iter().flatten().copied().collect();
    let cpu_jobs: Vec<_> = (0..2)
        .map(|_| {
            let base_point = rng.fields(10);
            let initial_seed: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
            let (proof, point, beta, seed) = cpu_whir_small(
                &memory,
                &setup,
                &base_point,
                initial_seed,
                schedule,
                pack_log2,
                &worker,
            );
            let mut claims = proof.memory_commitment.evals.clone();
            claims.extend_from_slice(&proof.setup_commitment.evals);
            (point, beta, seed, claims, proof)
        })
        .collect();
    assert_ne!(cpu_jobs[0].2, cpu_jobs[1].2);
    assert_eq!(log_message + cfg.log_lde_factor, 19);
    for tile_bytes in [16usize << log_message, 16usize << 19] {
        let shape = L1WhirShape::from_schedule(
            schedule,
            log_message,
            cfg.log_lde_factor,
            cfg.log_values_per_leaf,
            tile_bytes,
        );
        assert_eq!(shape.total_sumcheck_polys, sumcheck_polys);
        let mut prepared = Vec::new();
        for (point, beta, seed, claims, _) in &cpu_jobs {
            let mut raw = TraceHolder::new_without_cosets(
                10,
                cfg.log_lde_factor,
                cfg.log_values_per_leaf,
                cfg.cap_log,
                104,
                TreesCacheMode::CacheNone,
                gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
                &ctx,
            )
            .unwrap();
            memory_copy_async(raw.get_uninit_hypercube_evals_mut(), &flat, stream).unwrap();
            let mut base =
                PackedCosetRecomputeOracle::pack_from_columns(raw, pack_log2 as u32, &ctx).unwrap();
            base.commit(&cfg, &ctx).unwrap();
            let mut setup = PackedSetupSource::new(
                Arc::clone(&setup_host),
                gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
                &ctx,
            )
            .unwrap();
            let transfer =
                single_shot_h2d(|transfer| setup.schedule_transfer(transfer, &ctx), &ctx).unwrap();
            transfer.ensure_transferred(&ctx).unwrap();
            let seed_dev = upload(seed, stream);
            let point_dev = upload(point, stream);
            let challenge_dev = upload(&[*beta], stream);
            let claims_dev = upload(claims, stream);
            prepared.push((
                base,
                setup,
                transfer,
                seed_dev,
                point_dev,
                challenge_dev,
                claims_dev,
            ));
        }
        let mut jobs = Vec::new();
        for (
            job_index,
            (mut base, mut setup, transfer, mut seed_dev, point_dev, challenge_dev, claims_dev),
        ) in prepared.into_iter().enumerate()
        {
            let scheduled = schedule_l1_whir_fold(
                &mut base,
                &mut setup,
                &mut seed_dev,
                L1WhirInputs {
                    claims: &claims_dev,
                    base_layer_point: &point_dev,
                    batching_challenge: &challenge_dev,
                },
                schedule,
                &shape,
                &ctx,
            )
            .unwrap()
            .schedule_readback_and_assemble(
                base.cap_digests(),
                L1WhirInputs {
                    claims: &claims_dev,
                    base_layer_point: &point_dev,
                    batching_challenge: &challenge_dev,
                },
                cpu_jobs[job_index].4.batching_challenge_pow_nonce,
                &ctx,
            )
            .unwrap();
            jobs.push((
                scheduled,
                transfer,
                base,
                setup,
                seed_dev,
                point_dev,
                challenge_dev,
                claims_dev,
            ));
        }
        stream.synchronize().unwrap();
        for (
            job,
            (scheduled, transfer, base, setup, seed_dev, point_dev, challenge_dev, claims_dev),
        ) in jobs.into_iter().enumerate()
        {
            let expected = &cpu_jobs[job].4;
            let times = scheduled.phase_times_after_completion().unwrap();
            assert_eq!(times.len(), 17);
            assert!(times.iter().all(|(_, ms)| *ms >= 0.0));
            let proof = scheduled.into_proof_after_completion();
            let expected_bytes = serde_json::to_vec(expected).unwrap();
            let actual_bytes = serde_json::to_vec(&proof).unwrap();
            if expected_bytes != actual_bytes {
                let expected_json = serde_json::to_value(expected).unwrap();
                let actual_json = serde_json::to_value(&proof).unwrap();
                let diff = json_difference(&expected_json, &actual_json, "whir_proof").unwrap();
                std::fs::write(
                    format!("target/proth120-m7/t5-expected-p{pack_log2}-{tile_bytes}-{job}.json"),
                    &expected_bytes,
                )
                .unwrap();
                std::fs::write(
                    format!("target/proth120-m7/t5-actual-p{pack_log2}-{tile_bytes}-{job}.json"),
                    &actual_bytes,
                )
                .unwrap();
                panic!("pack_log2={pack_log2} tile_bytes={tile_bytes} job={job}: {diff}");
            }
            assert_eq!(
                download(&seed_dev, stream),
                whir_end_seed(expected, log_message, cpu_jobs[job].2)
            );
            assert_eq!(
                (
                    proof.memory_commitment.num_columns,
                    proof.setup_commitment.num_columns
                ),
                packed_columns
            );
            assert_eq!(proof.all_sumcheck_polys().count(), sumcheck_polys);
            assert_eq!(proof.all_ood_samples().count(), 2);
            assert_eq!(proof.queries_pow_nonces().len(), 3);
            assert_eq!(proof.final_monomials.len(), 16);
            assert!(proof.witness_commitment.queries.is_empty());
            eprintln!("pr_l1_whir_fold_matches_cpu_small: pack_log2={pack_log2} tile_bytes={tile_bytes} job={job} proof_bytes={} identical", actual_bytes.len());
            drop((
                transfer,
                base,
                setup,
                seed_dev,
                point_dev,
                challenge_dev,
                claims_dev,
            ));
        }
    }
}
