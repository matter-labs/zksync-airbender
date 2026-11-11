use crate::pow::query_words;
use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use field::Field;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::field::PR;
use gpu_prover_context::{ProverContext, ProverContextConfig};
use gpu_trace::trace::holder::{TraceHolder, TreesCacheMode};
use prover::gkr::prover::gkr_backend::{accumulate_base_columns_into_scalar, BatchedBaseColumn};
use prover::gkr::prover_config::ProofProfile;
use prover::gkr::whir::{
    evaluate_monomial_form, fold_eq_poly, fold_evaluation_form, fold_monomial_form,
    special_three_point_eval,
};
use transcript::{Keccak256Seed, Keccak256Transcript, Transcript};
use worker::Worker;

use std::alloc::Global;
use std::time::Instant;

use fft::Twiddles;
use prover::gkr::prover::backend::{Backend, Proth120WorkStealingLazyBackend};
use prover::gkr::whir::coset_commit::CosetByCosetExtCommitment;
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use prover::merkle_trees::{ColumnMajorMerkleTreeConstructor, PathQueryable};

use gpu_hash::keccak256::{
    transcript_commit_fields, transcript_commit_u32, transcript_draw_fields,
};
use prover::gkr::whir::hypercube_to_monomial::multivariate_coeffs_into_hypercube_evals;

use super::commit::schedule_commit_intermediate;
use super::schedule::{
    schedule_delinearization, schedule_eq_update, schedule_pow_and_query_indexes,
};
use super::shape::{L1WhirShape, OracleShape};
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

pub(super) fn context(arena_mb: usize) -> ProverContext {
    ProverContext::new(&ProverContextConfig {
        device_allocation_blocks_count: Some(arena_mb),
        host_allocator_blocks_count: 2048,
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
    let ctx = context(512);
    let stream = ctx.get_exec_stream();
    let mut rng = TestRng::new(0x7101);
    // Diagnostic row count, production packing and column counts.
    for (log_rows, memory_cols, setup_cols, pack) in [(12u32, 96usize, 10usize, 3u32)] {
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
    let ctx = context(6144);
    for log_n in [1, 8, 13, 14, 20, 26] {
        crate::primitive_tests::eq_case::<PR>(log_n, &ctx);
    }
}

#[test]
fn pr_fold_state_matches_cpu() {
    let ctx = context(256);
    crate::primitive_tests::fold_case::<PR>(12, 5, &ctx);
}

#[test]
fn pr_three_point_matches_cpu() {
    let ctx = context(256);
    for log_n in [1, 4, 9, 14, 20] {
        crate::primitive_tests::three_point_case::<PR>(log_n, &ctx);
    }
}

#[test]
fn pr_monomial_eval_matches_cpu() {
    let ctx = context(256);
    for log_n in [1, 4, 9, 14, 20] {
        crate::primitive_tests::monomial_case::<PR>(log_n, &ctx);
    }
}

#[test]
fn pr_round_update_matches_cpu() {
    let ctx = context(256);
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
    // Diagnostic shape: same v4/depth5 routes, fewer rows/cosets for an exact CPU cap.
    let log_v = 4;
    let log_leaves = log_n - log_v;
    let skip_bottom = 5;
    OracleShape {
        log_n,
        log_lde,
        log_domain: log_n + log_lde,
        log_v,
        log_leaves,
        skip_bottom,
        cap_log: 3,
        tile_cosets_log2: ((tile_bytes / 16).trailing_zeros() - log_n).min(log_lde),
        retained_per_coset: 2 * (1 << (log_leaves - skip_bottom)) - 1,
        path_len: (log_leaves + log_lde - 3) as usize,
    }
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
    let mut twiddle_tables = ctx
        .alloc::<PR>(gpu_ntt::proth120::TABLE_LEN, AllocationPlacement::Bottom)
        .unwrap();
    let mut twiddle_factors = ctx
        .alloc::<PR>(gpu_ntt::proth120::FACTOR_LEN, AllocationPlacement::BestFit)
        .unwrap();
    let proof_twiddles = gpu_ntt::proth120::prepare_proof_twiddles(
        &mut twiddle_tables,
        &mut twiddle_factors,
        ctx.get_exec_stream(),
    )
    .unwrap();
    drop(twiddle_factors);
    let monomials_dev = upload(monomials, stream);
    let mut cap_dst = upload(&[[0u32; 8]; 8], stream);
    let mut seed_dev = upload(&seed, stream);
    let oracle = schedule_commit_intermediate(
        &monomials_dev,
        shape,
        &mut cap_dst,
        &mut seed_dev,
        proof_twiddles,
        ctx,
    )
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

#[test]
fn pr_commit_intermediate_matches_cpu_small() {
    let ctx = context(512);
    let worker = worker();
    let mut rng = TestRng::new(0x7201);
    // Diagnostic fused suffix 8_4 and n11 residue, both with independent CPU caps.
    for (log_n, log_lde, passes) in [(15u32, 4u32, 4usize), (11, 8, 4)] {
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
    }
}

fn opening_oracle(log_n: u32, log_lde: u32, tile_log: u32, log_v: u32) -> OracleShape {
    assert_eq!(log_v, 4);
    small_oracle(log_n, log_lde, 16usize << (log_n + tile_log))
}

fn opening_output(
    shape: &OracleShape,
    queries: usize,
    ctx: &ProverContext,
) -> super::outputs::IntermediateProofDevice {
    use gpu_core::allocator::tracker::AllocationPlacement::BestFit;
    use gpu_gkr::proth120::proof_layout::ProofSlabSlicePr;
    use gpu_hash::keccak256::Digest;
    use std::sync::Arc;
    fn region<T>(cursor: &mut usize, count: usize) -> std::ops::Range<usize> {
        let start = cursor.next_multiple_of(32);
        *cursor = start + count * size_of::<T>();
        start..*cursor
    }
    let mut cursor = 0;
    let cap = region::<Digest>(&mut cursor, 1 << shape.cap_log);
    let leaves = region::<PR>(&mut cursor, queries << shape.log_v);
    let paths = region::<Digest>(&mut cursor, queries * shape.path_len);
    let indexes = region::<u32>(&mut cursor, queries);
    #[allow(clippy::arc_with_non_send_sync)]
    let backing = Arc::new(ctx.alloc::<PR>(cursor.div_ceil(16), BestFit).unwrap());
    super::outputs::IntermediateProofDevice {
        cap: ProofSlabSlicePr::new(Arc::clone(&backing), cap),
        leaves: ProofSlabSlicePr::new(Arc::clone(&backing), leaves),
        paths: ProofSlabSlicePr::new(Arc::clone(&backing), paths),
        tree_indexes: ProofSlabSlicePr::new(backing, indexes),
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

fn host_sibling_offset(log_leaves: u32, skip_bottom: u32, level: u32, j: u32) -> usize {
    gpu_hash::keccak256::retained_layer_offset(log_leaves, skip_bottom, level)
        + ((j >> level) ^ 1) as usize
}

#[test]
fn pr_open_intermediate_matches_cpu_small() {
    use super::openings::schedule_open_intermediate;
    let ctx = context(128);
    let stream = ctx.get_exec_stream();
    let mut twiddle_tables = ctx
        .alloc::<PR>(gpu_ntt::proth120::TABLE_LEN, AllocationPlacement::Bottom)
        .unwrap();
    let mut twiddle_factors = ctx
        .alloc::<PR>(gpu_ntt::proth120::FACTOR_LEN, AllocationPlacement::BestFit)
        .unwrap();
    let proof_twiddles = gpu_ntt::proth120::prepare_proof_twiddles(
        &mut twiddle_tables,
        &mut twiddle_factors,
        ctx.get_exec_stream(),
    )
    .unwrap();
    drop(twiddle_factors);
    let worker = worker();
    let mut rng = TestRng::new(0x7130_7eaf);
    // Diagnostic fused suffix 8_4 and n11 residue; includes all top-path levels.
    for (log_n, log_lde, tile_log, log_v) in [(15, 4, 2, 4), (11, 8, 6, 4)] {
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
        let oracle = schedule_commit_intermediate(
            &state.monomials,
            &shape,
            &mut cap,
            &mut seed,
            proof_twiddles,
            &ctx,
        )
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
                proof_twiddles,
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
    }
}

#[test]
fn pr_horner_leaves_match_cpu_small() {
    use super::openings::schedule_horner_leaves;
    let ctx = context(128);
    let stream = ctx.get_exec_stream();
    let worker = worker();
    let mut rng = TestRng::new(0x7130_80a1);
    for (log_n, log_lde, log_v) in [(11, 8, 4)] {
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
#[ignore = "production L1 WHIR query PoW and transcript draws on GPU"]
fn pr_transcript_phases_match_reference() {
    #[derive(serde::Deserialize)]
    struct Bundle {
        proof: verifier_evm::seed::Proof,
        operation_mode: prover::gkr::prover::OperationMode,
    }
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    #[derive(serde::Deserialize)]
    struct Artifact {
        l1: Bundle,
    }
    let Artifact { l1: bundle } = proof_fixtures::read_file(proof_fixtures::chain_artifact(
        "pessimistic_conjecture",
        "l1",
    ));
    let circuit: verifier_evm::seed::Circuit = serde_json::from_reader(
        std::fs::File::open(
            root.join("cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json"),
        )
        .unwrap(),
    )
    .unwrap();
    let config = ProofProfile::L1Wrap.prover_config(
        21,
        prover::definitions::SoundnessMode::PessimisticConjecture,
    );
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
    let shape = L1WhirShape::from_schedule(&config.whir_schedule);
    assert_whir_transcript_phases(whir, cpu.handoff_seed, &shape);
}

fn assert_whir_transcript_phases(
    whir: &super::L1WhirProof,
    initial: [u8; 32],
    shape: &L1WhirShape,
) {
    let ctx = context(256);
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
    let ctx = context(1024);
    let stream = ctx.get_exec_stream();
    let mut twiddle_tables = ctx
        .alloc::<PR>(gpu_ntt::proth120::TABLE_LEN, AllocationPlacement::Bottom)
        .unwrap();
    let mut twiddle_factors = ctx
        .alloc::<PR>(gpu_ntt::proth120::FACTOR_LEN, AllocationPlacement::BestFit)
        .unwrap();
    let proof_twiddles = gpu_ntt::proth120::prepare_proof_twiddles(
        &mut twiddle_tables,
        &mut twiddle_factors,
        ctx.get_exec_stream(),
    )
    .unwrap();
    drop(twiddle_factors);
    let mut rng = TestRng::new(0x7401);
    // Diagnostic: two production v4/depth5 routes reduced to n15 and n11.
    let oracle0 = small_oracle(15, 4, 16 << 17);
    let oracle1 = small_oracle(11, 8, 16 << 17);
    let monomials = rng.fields(1 << 15);
    let mut evals = monomials.clone();
    multivariate_coeffs_into_hypercube_evals(&mut evals, 15);
    let eq = rng.fields(1 << 15);
    let seed_bytes: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
    let mut model = DenseModel {
        monomials: monomials.clone(),
        evals: evals.clone(),
        eq: eq.clone(),
        query_eq: vec![PR::ZERO; 1 << 15],
        seed: Keccak256Seed(seed_bytes),
    };
    let mut state = L1WhirState::new(15, 36, &ctx).unwrap();
    memory_copy_async(&mut state.monomials, &monomials, stream).unwrap();
    memory_copy_async(&mut state.evals, &evals, stream).unwrap();
    memory_copy_async(&mut state.eq, &eq, stream).unwrap();
    let mut seed = upload(&seed_bytes, stream);
    let mut cap = upload(&[[0u32; 8]; 8], stream);
    let mut commit_seed = upload(&[0u8; 32], stream);
    let oracle_a = schedule_commit_intermediate(
        &state.monomials,
        &oracle0,
        &mut cap,
        &mut commit_seed,
        proof_twiddles,
        &ctx,
    )
    .unwrap();
    let qlog0 = 18;
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
    let oracle_b = schedule_commit_intermediate(
        &state.monomials,
        &oracle1,
        &mut cap,
        &mut commit_seed,
        proof_twiddles,
        &ctx,
    )
    .unwrap();
    let qlog1 = 15;
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
    assert_eq!(state.current_len, 128);
}

impl crate::primitive_tests::PrimitiveField for PR {
    type State = L1WhirState;
    fn sample(seed: u32) -> Self {
        TestRng::new(u64::from(seed)).field()
    }
    fn state(log_n: u32, context: &ProverContext) -> Self::State {
        L1WhirState::new(log_n, 0, context).unwrap()
    }
    fn set_forms(
        state: &mut Self::State,
        monomials: &[Self],
        evals: &[Self],
        eq: &[Self],
        context: &ProverContext,
    ) {
        let stream = context.get_exec_stream();
        memory_copy_async(&mut state.monomials, monomials, stream).unwrap();
        memory_copy_async(&mut state.evals, evals, stream).unwrap();
        memory_copy_async(&mut state.eq, eq, stream).unwrap();
        stream.synchronize().unwrap();
    }
    fn read_forms(
        state: &Self::State,
        context: &ProverContext,
    ) -> (Vec<Self>, Vec<Self>, Vec<Self>) {
        let stream = context.get_exec_stream();
        (
            download(&state.monomials, stream),
            download(&state.evals, stream),
            download(&state.eq, stream),
        )
    }
    fn build_eq(state: &mut Self::State, point: &[Self], context: &ProverContext) -> Vec<Self> {
        let stream = context.get_exec_stream();
        let point = upload(point, stream);
        schedule_eq_from_point(&point, state, context).unwrap();
        download(&state.eq, stream)
    }
    fn fold(state: &mut Self::State, challenge: Self, context: &ProverContext) {
        let old = (
            state.monomials.as_ptr(),
            state.evals.as_ptr(),
            state.eq.as_ptr(),
        );
        let next = state.current_len / 2;
        let challenge = upload(&[challenge], context.get_exec_stream());
        schedule_fold_state(state, &challenge, context).unwrap();
        assert_eq!(state.current_len, next);
        assert_eq!(state.monomials.len(), next);
        assert_eq!(state.evals.len(), next);
        assert_eq!(state.eq.len(), next);
        assert_ne!(old.0, state.monomials.as_ptr());
        assert_ne!(old.1, state.evals.as_ptr());
        assert_ne!(old.2, state.eq.as_ptr());
    }
    fn three_point(state: &mut Self::State, context: &ProverContext) -> [Self; 3] {
        schedule_three_point(state, context).unwrap();
        download(&state.reduce_out, context.get_exec_stream())
            .try_into()
            .unwrap()
    }
    fn monomial_eval(state: &mut Self::State, point: Self, context: &ProverContext) -> Self {
        let stream = context.get_exec_stream();
        let point = upload(&[point], stream);
        let mut out = upload(&[PR::ZERO], stream);
        schedule_monomial_eval(state, &point, &mut out, context).unwrap();
        download(&out, stream)[0]
    }
}
