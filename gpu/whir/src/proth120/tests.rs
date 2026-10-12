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
use prover::gkr::prover_config::example_configs::evm_production_packed_prover_config;
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

use super::commit::{
    schedule_commit_intermediate, schedule_coset_offsets, schedule_lde_convert_pass,
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
    WhirSchedule {
        base_lde_factor: 32,
        cap_size: 8,
        whir_steps_schedule: vec![2, 4, 4],
        whir_queries_schedule: vec![5, 4, 3],
        whir_steps_lde_factors: vec![128, 2048],
        whir_pow_schedule: vec![4, 0, 3],
    }
}

#[test]
fn cpu_shape_l1_values() {
    let schedule = evm_production_packed_prover_config(SecurityLevel::Sec100).whir_schedule;
    let shape = L1WhirShape::from_schedule(&schedule, 26, 5, 2, L1_WHIR_TILE_BYTES);
    assert_eq!(
        (
            shape.log_message,
            shape.log_base_lde,
            shape.cap_log,
            shape.term_capacity,
            shape.total_sumcheck_polys,
            shape.log_final
        ),
        (26, 5, 3, 48, 22, 4)
    );
    let round_rows = [
        (2, 17, 30, 24, 29),
        (4, 12, 30, 20, 27),
        (4, 8, 27, 16, 27),
        (4, 6, 25, 12, 27),
        (4, 5, 21, 8, 27),
        (4, 4, 24, 4, 27),
    ];
    let oracle_rows = [
        (24, 7, 31, 4, 20, 5, 3, 2, 65535, 24),
        (20, 11, 31, 4, 16, 5, 3, 6, 4095, 24),
        (16, 15, 31, 4, 12, 5, 3, 10, 255, 24),
        (12, 19, 31, 4, 8, 5, 3, 14, 15, 24),
        (8, 23, 31, 4, 4, 4, 3, 18, 1, 24),
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
            assert_eq!(r, 5);
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
    rejection(&s, 14, 5, 3, tile, "first folds");
    rejection(&s, 11, 5, 2, tile, "oracle log_n below 8");
    rejection(&s, 9, 5, 2, tile, "sum of folds exceeds");
    let mut bad = s.clone();
    bad.whir_steps_lde_factors[0] = 1 << 20;
    rejection(&bad, 14, 5, 2, tile, "oracle log_domain exceeds 31");
    let mut bad = s.clone();
    bad.whir_steps_lde_factors[0] = 4;
    rejection(&bad, 14, 5, 2, tile, "cap_log exceeds oracle");
    let mut bad = s.clone();
    bad.whir_steps_lde_factors[0] = 8;
    rejection(&bad, 14, 5, 2, tile, "earlier query domain");
    let mut bad = s.clone();
    bad.whir_steps_schedule.clear();
    rejection(&bad, 14, 5, 2, tile, "at least two rounds");
    let mut bad = s.clone();
    bad.whir_queries_schedule.pop();
    rejection(&bad, 14, 5, 2, tile, "schedule lengths");
    let mut bad = s.clone();
    bad.cap_size = 7;
    rejection(&bad, 14, 5, 2, tile, "cap_size must be a power");
    let mut bad = s.clone();
    bad.base_lde_factor = 31;
    rejection(&bad, 14, 5, 2, tile, "base LDE factor must be a power");
    rejection(&s, 14, 4, 2, tile, "base LDE factor differs");
    let mut bad = s.clone();
    bad.whir_steps_lde_factors[0] = 127;
    rejection(&bad, 14, 5, 2, tile, "oracle LDE factor must be a power");
    let mut bad = s.clone();
    bad.whir_steps_schedule[1] = 0;
    rejection(&bad, 14, 5, 2, tile, "log_v outside");
    let mut bad = s.clone();
    bad.whir_steps_schedule[1] = 5;
    rejection(&bad, 14, 5, 2, tile, "log_v outside");
    let mut bad = s.clone();
    bad.whir_queries_schedule[0] = 0;
    rejection(&bad, 14, 5, 2, tile, "queries outside");
    rejection(&s, 14, 5, 2, 16 << 11, "below one coset");
    rejection(&s, 14, 5, 2, 123, "tile_bytes must be a power");
    let mut bad = s.clone();
    bad.whir_steps_schedule = vec![2, 4, 4, 4, 4];
    bad.whir_queries_schedule = vec![1; 5];
    bad.whir_pow_schedule = vec![0; 5];
    bad.whir_steps_lde_factors = vec![1 << 15; 4];
    rejection(&bad, 26, 5, 2, tile, "oracle log_domain exceeds 31");
    let final_zero = WhirSchedule {
        whir_steps_schedule: vec![2, 4, 4, 4],
        whir_queries_schedule: vec![1; 4],
        whir_pow_schedule: vec![0; 4],
        whir_steps_lde_factors: vec![128, 2048, 32768],
        ..s.clone()
    };
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
            &ctx,
        )
        .unwrap();
        memory_copy_async(base.get_uninit_hypercube_evals_mut(), &memory, stream).unwrap();
        memory_copy_async(setup_raw.get_uninit_hypercube_evals_mut(), &setup, stream).unwrap();
        let mut state = L1WhirState::new(log_rows + pack, &ctx).unwrap();
        schedule_accumulate_base(&base, &setup_raw, &powers_dev, &mut state, &ctx).unwrap();
        let expected = accumulate_reference(&memory, &setup, rows, pack, &powers);
        if log_rows == 10 {
            let shape = L1WhirShape::from_schedule(&small_schedule(), 14, 5, 2, 16 << 14);
            let outputs = super::outputs::L1WhirProofDevice::new(&shape, 7, 1, &ctx).unwrap();
            let _host = super::outputs::L1WhirProofHost::new(&shape, &outputs, 7, 1, &ctx);
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
        let mut state = L1WhirState::new(log_n, &ctx).unwrap();
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
    let mut state = L1WhirState::new(12, &ctx).unwrap();
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
        let mut state = L1WhirState::new(log_n, &ctx).unwrap();
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
        let state = L1WhirState::new(log_n, &ctx).unwrap();
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
        let mut state = L1WhirState::new(1, &ctx).unwrap();
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
    let schedule = WhirSchedule {
        base_lde_factor: 32,
        cap_size: 8,
        whir_steps_schedule: vec![2, 4],
        whir_queries_schedule: vec![1, 1],
        whir_steps_lde_factors: vec![1 << log_lde],
        whir_pow_schedule: vec![0, 0],
    };
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
    for (log_n, log_lde, passes) in [(12u32, 7u32, 32usize), (8, 11, 8), (10, 9, 1)] {
        let cosets = 1usize << log_lde;
        let tile_bytes = (cosets / passes) << (log_n + 4);
        let shape = small_oracle(log_n, log_lde, tile_bytes);
        assert_eq!(cosets >> shape.tile_cosets_log2, passes);
        assert_eq!(shape.log_domain, 19);
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
        let mut tile = upload(&vec![PR::ZERO; tile_cosets << log_n], stream);
        schedule_lde_convert_pass(
            &monomials_dev,
            &shape,
            offsets.as_deref(),
            k0 as u32,
            &mut tile,
            &ctx,
        )
        .unwrap();
        assert_fields(
            &download(&tile, stream),
            &cpu_tile_pass(&monomials, log_lde, k0, tile_cosets),
        );
    }
}

#[test]
#[ignore]
fn pr_commit_intermediate_n8_production() {
    let ctx = context(4096, Some(31));
    let stream = ctx.get_exec_stream();
    let worker = Worker::new();
    let schedule = evm_production_packed_prover_config(SecurityLevel::Sec100).whir_schedule;
    let shape = L1WhirShape::from_schedule(&schedule, 26, 5, 2, L1_WHIR_TILE_BYTES).rounds[4]
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
    let schedule = WhirSchedule {
        base_lde_factor: 32,
        cap_size: 8,
        whir_steps_schedule: vec![2, log_v as usize],
        whir_queries_schedule: vec![1, 1],
        whir_steps_lde_factors: vec![1 << log_lde],
        whir_pow_schedule: vec![0, 0],
    };
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
        paths: ctx
            .alloc(queries * shape.path_len as usize, BestFit)
            .unwrap(),
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
    std::array::from_fn(|i| u32::from_be_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap()))
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
        let path_gpu = &paths[i * shape.path_len as usize..(i + 1) * shape.path_len as usize];
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
    for (log_n, log_lde, tile_log, log_v) in
        [(12, 7, 2, 4), (8, 11, 8, 4), (10, 9, 9, 4), (10, 9, 9, 2)]
    {
        let shape = opening_oracle(log_n, log_lde, tile_log, log_v);
        let monomials = rng.fields(1 << log_n);
        let twiddles = Twiddles::new(monomials.len(), &worker);
        let cpu =
            ExtCommitment::commit(&monomials, &twiddles, 1 << log_lde, 1 << log_v, 8, &worker);
        let mut state = L1WhirState::new(log_n, &ctx).unwrap();
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
                    assert_eq!(
                        paths[i * shape.path_len as usize + level as usize],
                        retained[offset]
                    );
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
    let mut rng = TestRng::new(0x7130_24);
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

fn panic_text(error: Box<dyn std::any::Any + Send>) -> String {
    if let Some(message) = error.downcast_ref::<String>() {
        message.clone()
    } else if let Some(message) = error.downcast_ref::<&str>() {
        (*message).to_owned()
    } else {
        panic!("unexpected panic payload")
    }
}
