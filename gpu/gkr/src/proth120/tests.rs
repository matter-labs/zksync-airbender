use era_cudart::memory::memory_copy_async;
use era_cudart::slice::DeviceSlice;
use fft::{bitreverse_index, Twiddles};
use field::{Field, Proth120};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::field::PR;
use gpu_prover_context::{ProverContext, ProverContextConfig};
use gpu_trace::trace::holder::{TraceHolder, TreesCacheMode};
use gpu_trace::trace::packed::{
    coset_root_offset, retained_len, PackedCommitConfig, PackedCosetRecomputeOracle,
};
use prover::gkr::prover::stages::commitment_utils::compute_column_major_lde_single_coset;
use prover::gkr::whir::coset_commit::CosetByCosetBaseCommitment;
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use prover::merkle_trees::{ColumnMajorMerkleTreeConstructor, PathQueryable};
use std::alloc::Global;
use worker::Worker;

type CpuOracle = CosetByCosetBaseCommitment<Proth120, Keccak256MerkleTreeWithCap>;

fn make_context() -> ProverContext {
    ProverContext::new(&ProverContextConfig {
        device_allocation_blocks_count: Some(256),
        host_allocator_blocks_count: 128,
        proth120_ntt_log_max_domain: Some(21),
        ..Default::default()
    })
    .unwrap()
}

fn deterministic_columns(log_rows: u32, columns: usize) -> Vec<Vec<PR>> {
    let mut state = 0x71cc_1942_519e_103du64;
    (0..columns)
        .map(|_| {
            (0..1usize << log_rows)
                .map(|_| {
                    let mut next = || {
                        state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
                        let mut z = state;
                        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                        z ^ (z >> 31)
                    };
                    let value = (next() as u128) << 64 | next() as u128;
                    PR::from_u128_with_reduction(value)
                })
                .collect()
        })
        .collect()
}

fn read_back<T: Copy>(device: &DeviceSlice<T>, initial: T, context: &ProverContext) -> Vec<T> {
    let mut host = vec![initial; device.len()];
    memory_copy_async(&mut host, device, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

fn upload_holder(
    columns: &[Vec<PR>],
    log_rows: u32,
    cfg: PackedCommitConfig,
    context: &ProverContext,
) -> TraceHolder<PR> {
    let mut raw = TraceHolder::new_without_cosets(
        log_rows,
        cfg.log_lde_factor,
        cfg.log_values_per_leaf,
        cfg.cap_log,
        columns.len(),
        TreesCacheMode::CacheNone,
        context,
    )
    .unwrap();
    let flat: Vec<PR> = columns.iter().flatten().copied().collect();
    memory_copy_async(
        raw.get_uninit_hypercube_evals_mut(),
        &flat,
        context.get_exec_stream(),
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    raw
}

fn cpu_commit(
    columns: &[Vec<PR>],
    log_rows: u32,
    pack_log2: u32,
    cfg: PackedCommitConfig,
    twiddles: &Twiddles<PR, Global>,
    worker: &Worker,
) -> CpuOracle {
    let refs: Vec<&[PR]> = columns.iter().map(Vec::as_slice).collect();
    CpuOracle::commit_packed(
        &refs,
        twiddles,
        1 << cfg.log_lde_factor,
        cfg.log_values_per_leaf as usize,
        1 << cfg.cap_log,
        log_rows as usize,
        pack_log2 as usize,
        worker,
    )
}

fn assert_raw(
    oracle: &PackedCosetRecomputeOracle<PR>,
    columns: &[Vec<PR>],
    context: &ProverContext,
) {
    let actual = read_back(oracle.raw().get_hypercube_evals(), PR::ZERO, context);
    let expected: Vec<PR> = columns.iter().flatten().copied().collect();
    assert_eq!(actual, expected, "raw columns changed");
}

#[test]
#[cfg(not(no_cuda))]
fn packed_commit_matches_cpu_small() {
    let context = make_context();
    let worker = Worker::new_with_num_threads(4);
    let mut shapes: Vec<(u32, u32, usize, u32, u32, u32)> = [1, 10, 16, 17, 20, 104]
        .into_iter()
        .map(|columns| (12, 4, columns, 2, 3, 5))
        .collect();
    shapes.extend([
        (12, 4, 20, 2, 5, 5),
        (6, 2, 10, 4, 3, 4),
        (6, 2, 1, 4, 3, 0),
    ]);
    for (log_rows, pack_log2, columns_count, log_v, cap_log, skip_bottom) in shapes {
        let cfg = PackedCommitConfig {
            log_lde_factor: 5,
            log_values_per_leaf: log_v,
            cap_log,
            skip_bottom,
        };
        let columns = deterministic_columns(log_rows, columns_count);
        let twiddles = Twiddles::<PR, Global>::new(1 << (log_rows + pack_log2), &worker);
        let cpu = cpu_commit(&columns, log_rows, pack_log2, cfg, &twiddles, &worker);
        let raw = upload_holder(&columns, log_rows, cfg, &context);
        let mut oracle =
            PackedCosetRecomputeOracle::pack_from_columns(raw, pack_log2, &context).unwrap();
        assert_eq!(oracle.log_rows(), log_rows);
        assert_eq!(oracle.pack_log2(), pack_log2);
        assert_eq!(oracle.log_packed(), log_rows + pack_log2);
        assert_eq!(oracle.columns(), columns_count);
        assert_eq!(
            oracle.packed_columns(),
            columns_count.div_ceil(1 << pack_log2)
        );
        assert_eq!(oracle.config(), None);
        assert_raw(&oracle, &columns, &context);
        let monomials = read_back(oracle.monomials(), PR::ZERO, &context);
        let expected: Vec<PR> = cpu.monomial_forms.iter().flatten().copied().collect();
        assert_eq!(
            monomials, expected,
            "packed monomials, columns={columns_count}"
        );
        oracle.commit(&cfg, &context).unwrap();
        assert_eq!(oracle.config(), Some(cfg));
        let cap = read_back(oracle.cap_digests(), [0; 8], &context);
        assert_eq!(
            cap,
            cpu.get_cap().cap,
            "cap, columns={columns_count}, cap_log={cap_log}, s={skip_bottom}"
        );
        assert_eq!(
            read_back(oracle.cap(), 0u32, &context),
            cap.iter().flatten().copied().collect::<Vec<_>>()
        );
        assert_raw(&oracle, &columns, &context);
        let retained = read_back(oracle.uninit_retained_mut(), [0; 8], &context);
        let roots = read_back(oracle.uninit_roots_mut(), [0; 8], &context);
        let h = oracle.log_packed() - log_v;
        let per_coset = retained_len(h, skip_bottom);
        for k in 0..32 {
            let evals: Vec<Box<[PR]>> = cpu
                .monomial_forms
                .iter()
                .map(|monomials| {
                    compute_column_major_lde_single_coset(monomials, &twiddles, 32, k, &worker)
                })
                .collect();
            let refs: Vec<&[PR]> = evals.iter().map(|column| &column[..]).collect();
            let cosets: &[&[&[PR]]] = &[&refs];
            let tree = <Keccak256MerkleTreeWithCap as ColumnMajorMerkleTreeConstructor<PR>>::construct_from_cosets::<PR, _>(
                cosets, 1 << log_v, 1, true, false, false, &worker);
            let expected_root = tree.get_cap().cap[0];
            assert_eq!(
                retained[k * per_coset + coset_root_offset(h, skip_bottom)],
                expected_root,
                "natural coset {k}"
            );
            let physical = bitreverse_index(k, 5);
            assert_eq!(roots[physical], expected_root, "physical coset {physical}");
            assert_eq!(cpu.top_tree.get_proof(physical).0, expected_root);
        }
        oracle.release_raw();
        oracle.release_commitment_state();
        assert_eq!(
            read_back(oracle.cap_digests(), [0; 8], &context),
            cap,
            "cap after release"
        );
    }
}

#[test]
#[cfg(not(no_cuda))]
fn packed_recompute_coset_matches_cpu_small() {
    let context = make_context();
    let worker = Worker::new_with_num_threads(4);
    let cfg = PackedCommitConfig {
        log_lde_factor: 5,
        log_values_per_leaf: 2,
        cap_log: 3,
        skip_bottom: 5,
    };
    let columns = deterministic_columns(12, 20);
    let twiddles = Twiddles::<PR, Global>::new(1 << 16, &worker);
    let raw = upload_holder(&columns, 12, cfg, &context);
    let mut oracle = PackedCosetRecomputeOracle::pack_from_columns(raw, 4, &context).unwrap();
    let mut scratch = context
        .alloc(oracle.monomials().len(), AllocationPlacement::Top)
        .unwrap();
    let before_commit = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        oracle.recompute_coset(0, &mut scratch, &context)
    }))
    .unwrap_err();
    assert!(panic_message(before_commit).contains("recompute_coset before commit"));
    oracle.commit(&cfg, &context).unwrap();
    let monomials = read_back(oracle.monomials(), PR::ZERO, &context);
    for k in [0, 1, 31] {
        oracle.recompute_coset(k, &mut scratch, &context).unwrap();
        let actual = read_back(&scratch, PR::ZERO, &context);
        let expected: Vec<PR> = monomials
            .chunks(1 << 16)
            .flat_map(|column| {
                compute_column_major_lde_single_coset(column, &twiddles, 32, k as usize, &worker)
                    .into_vec()
            })
            .collect();
        assert_eq!(actual, expected, "recomputed coset {k}");
    }
    assert_raw(&oracle, &columns, &context);
    drop(scratch);
    oracle.release_commitment_state();
    let mut scratch = context.alloc(2 << 16, AllocationPlacement::Top).unwrap();
    let after_release = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        oracle.recompute_coset(0, &mut scratch, &context)
    }))
    .unwrap_err();
    assert!(panic_message(after_release).contains("recompute_coset after release_commitment_state"));
    assert_raw(&oracle, &columns, &context);
}

fn panic_message(payload: Box<dyn std::any::Any + Send>) -> String {
    if let Some(message) = payload.downcast_ref::<String>() {
        message.clone()
    } else if let Some(message) = payload.downcast_ref::<&str>() {
        message.to_string()
    } else {
        panic!("unexpected panic payload")
    }
}
