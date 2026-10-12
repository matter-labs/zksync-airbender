use era_cudart::memory::memory_copy_async;
use era_cudart::slice::DeviceSlice;
use fft::{bitreverse_index, Twiddles};
use field::{Field, Proth120};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::PR;
use gpu_prover_context::transfer::single_shot_h2d;
use gpu_prover_context::{ProverContext, ProverContextConfig};
use gpu_trace::trace::holder::{TraceHolder, TreesCacheMode};
use gpu_trace::trace::packed::{
    coset_root_offset, opening_path_len, retained_len, PackedCommitConfig,
    PackedCosetRecomputeOracle,
};
use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;
use prover::gkr::prover::stages::commitment_utils::compute_column_major_lde_single_coset;
use prover::gkr::whir::coset_commit::CosetByCosetBaseCommitment;
use prover::merkle_trees::keccak256_for_everything_tree::{
    keccak_leaf_encoding_words, Keccak256MerkleTreeWithCap,
};
use prover::merkle_trees::{ColumnMajorMerkleTreeConstructor, PathQueryable};
use prover::transcript::{Keccak256Transcript, Transcript};
use std::alloc::Global;
use std::sync::Arc;
use worker::Worker;

use crate::setup::{L1WrapSetupHost, PackedSetupSource};

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

fn upload<T: Copy>(host: &[T], context: &ProverContext) -> DeviceAllocation<T> {
    let mut device = context
        .alloc(host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut device, host, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    device
}

fn keccak_words(words: impl IntoIterator<Item = u32>) -> [u32; 8] {
    let swapped: Vec<u32> = words.into_iter().map(u32::swap_bytes).collect();
    let digest =
        <Keccak256Transcript as Transcript<Proth120, Proth120>>::commit_initial_u32(&swapped).0;
    std::array::from_fn(|word| {
        u32::from_be_bytes(digest[4 * word..4 * word + 4].try_into().unwrap())
    })
}

fn root_matches(hashed_leaf: &[PR], path: &[[u32; 8]], index: usize, cap: &[[u32; 8]]) -> bool {
    let mut digest = keccak_words(keccak_leaf_encoding_words(hashed_leaf));
    for (level, sibling) in path.iter().enumerate() {
        digest = if (index >> level) & 1 == 0 {
            keccak_words(digest.into_iter().chain(*sibling))
        } else {
            keccak_words(sibling.iter().copied().chain(digest))
        };
    }
    digest == cap[index >> path.len()]
}

#[test]
#[cfg(not(no_cuda))]
fn packed_open_queries_match_cpu_small() {
    let context = make_context();
    let worker = Worker::new_with_num_threads(4);
    let (log_rows, pack_log2) = (12, 4);
    let cfg = PackedCommitConfig {
        log_lde_factor: 5,
        log_values_per_leaf: 2,
        cap_log: 3,
        skip_bottom: 5,
    };
    let columns = deterministic_columns(log_rows, 20);
    let twiddles = Twiddles::<PR, Global>::new(1 << (log_rows + pack_log2), &worker);
    let cpu = cpu_commit(&columns, log_rows, pack_log2, cfg, &twiddles, &worker);
    let raw = upload_holder(&columns, log_rows, cfg, &context);
    let mut oracle =
        PackedCosetRecomputeOracle::pack_from_columns(raw, pack_log2, &context).unwrap();
    let packed_columns = oracle.packed_columns();
    let h = oracle.log_packed() - cfg.log_values_per_leaf;
    let depth = opening_path_len(oracle.log_packed(), &cfg);
    assert_eq!(depth, 16);
    let leaf_len = packed_columns << cfg.log_values_per_leaf;
    let last = (1u32 << h) - 1;
    let queries: Vec<u32> = [
        (9001, 31),
        (0, 7),
        (500, 3),
        (last, 7),
        (42, 0),
        (1234, 7),
        (500, 3),
        (last, 31),
        (7777, 16),
        (0, 0),
        (42, 0),
        (3, 1),
        (12000, 30),
        (8191, 15),
        (8192, 15),
        (1, 24),
        (16000, 2),
    ]
    .into_iter()
    .map(|(leaf, coset)| (leaf << cfg.log_lde_factor) | coset)
    .collect();
    assert!(queries.iter().all(|&q| q < 1 << (h + cfg.log_lde_factor)));
    let count = queries.len();
    let d_queries = upload(&queries, &context);
    let leaf_canary = PR::from_u128_with_reduction(0x5eed);
    let path_canary = [0xdead_beef; 8];
    let index_canary = 0xaaaa_aaaa;
    let mut d_leaves = upload(&vec![leaf_canary; count * leaf_len + 2], &context);
    let mut d_paths = upload(&vec![path_canary; count * depth + 2], &context);
    let mut d_indexes = upload(&vec![index_canary; count + 2], &context);
    let before_commit = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        oracle.open_queries(
            &d_queries,
            &mut d_leaves[1..count * leaf_len + 1],
            &mut d_paths[1..count * depth + 1],
            &mut d_indexes[1..count + 1],
            &context,
        )
    }))
    .unwrap_err();
    assert!(panic_message(before_commit).contains("open_queries before commit"));
    oracle.commit(&cfg, &context).unwrap();
    oracle
        .open_queries(
            &d_queries,
            &mut d_leaves[1..count * leaf_len + 1],
            &mut d_paths[1..count * depth + 1],
            &mut d_indexes[1..count + 1],
            &context,
        )
        .unwrap();
    let leaves = read_back(&d_leaves, PR::ZERO, &context);
    let paths = read_back(&d_paths, [0; 8], &context);
    let indexes = read_back(&d_indexes, 0u32, &context);
    let cap = read_back(oracle.cap_digests(), [0; 8], &context);
    assert_eq!(cap, cpu.get_cap().cap);
    assert_eq!([leaves[0], leaves[count * leaf_len + 1]], [leaf_canary; 2]);
    assert_eq!([paths[0], paths[count * depth + 1]], [path_canary; 2]);
    assert_eq!([indexes[0], indexes[count + 1]], [index_canary; 2]);
    let expected = cpu.query_many(
        &queries.iter().map(|&q| q as usize).collect::<Vec<_>>(),
        &twiddles,
        &worker,
    );
    for (i, expected) in expected.iter().enumerate() {
        let leaf = &leaves[1 + i * leaf_len..1 + (i + 1) * leaf_len];
        let path = &paths[1 + i * depth..1 + (i + 1) * depth];
        let index = indexes[1 + i] as usize;
        assert_eq!(index, expected.index, "tree index of query {i}");
        assert_eq!(
            leaf,
            &expected.leaf_values_concatenated[..],
            "leaf of query {i}"
        );
        assert_eq!(path, &expected.path[..], "path of query {i}");
        let column_major: Vec<PR> = (0..packed_columns)
            .flat_map(|column| {
                (0..1usize << cfg.log_values_per_leaf)
                    .map(move |slot| leaf[slot * packed_columns + column])
            })
            .collect();
        assert!(
            root_matches(&column_major, path, index, &cap),
            "root of query {i}"
        );
        assert!(
            !root_matches(leaf, path, index, &cap),
            "leaf order control of query {i}"
        );
        let coset = (queries[i] & 31) as usize;
        if bitreverse_index(coset, 5) != coset {
            let natural = coset << h | (queries[i] >> cfg.log_lde_factor) as usize;
            assert!(
                !root_matches(&column_major, path, natural, &cap),
                "coset order control of query {i}"
            );
        }
    }
    let d_empty_queries = upload::<u32>(&[], &context);
    let mut d_empty_leaves = upload::<PR>(&[], &context);
    let mut d_empty_paths = upload::<[u32; 8]>(&[], &context);
    let mut d_empty_indexes = upload::<u32>(&[], &context);
    context.reset_used_mem_peak();
    let peak = context.get_used_mem_peak();
    oracle
        .open_queries(
            &d_empty_queries,
            &mut d_empty_leaves,
            &mut d_empty_paths,
            &mut d_empty_indexes,
            &context,
        )
        .unwrap();
    assert_eq!(context.get_used_mem_peak(), peak, "Q = 0 allocated scratch");
    oracle
        .open_queries(
            &d_queries,
            &mut d_leaves[1..count * leaf_len + 1],
            &mut d_paths[1..count * depth + 1],
            &mut d_indexes[1..count + 1],
            &context,
        )
        .unwrap();
    assert!(
        context.get_used_mem_peak() > peak,
        "scratch allocation not tracked"
    );
}

#[test]
#[cfg(not(no_cuda))]
fn l1_setup_host_round_trip_small() {
    let context = make_context();
    let worker = Worker::new_with_num_threads(4);
    let columns = deterministic_columns(12, 10);
    let twiddles = Twiddles::<PR, Global>::new(1 << 16, &worker);
    let setup = CpuGKRSetup {
        hypercube_evals: columns
            .iter()
            .cloned()
            .map(|column| {
                Arc::new(prover::allocation_pool::AllocationType::from(
                    column.into_boxed_slice(),
                ))
            })
            .collect(),
    };
    for cap_log in [3, 5] {
        let cfg = PackedCommitConfig {
            log_lde_factor: 5,
            log_values_per_leaf: 2,
            cap_log,
            skip_bottom: 5,
        };
        let cpu = cpu_commit(&columns, 12, 4, cfg, &twiddles, &worker);
        let host = Arc::new(L1WrapSetupHost::precompute(&setup, 4, cfg, &context).unwrap());
        assert_eq!(host.log_rows, 12);
        assert_eq!(host.columns_count, 10);
        assert_eq!(host.pack_log2, 4);
        assert_eq!(host.cfg, cfg);
        assert_eq!(host.cap(), cpu.get_cap());
        for (physical, root) in host.roots.iter().enumerate() {
            assert_eq!(
                *root,
                cpu.top_tree.get_proof(physical).0,
                "cached root {physical}"
            );
        }
        let mut source = PackedSetupSource::new(Arc::clone(&host), &context).unwrap();
        let transfer = single_shot_h2d(
            |transfer| source.schedule_transfer(transfer, &context),
            &context,
        )
        .unwrap();
        transfer.ensure_transferred(&context).unwrap();
        assert_eq!(
            read_back(source.cap(), 0u32, &context),
            host.cap().cap.iter().flatten().copied().collect::<Vec<_>>()
        );
        let raw = read_back(source.raw().get_hypercube_evals(), PR::ZERO, &context);
        assert_eq!(raw, columns.iter().flatten().copied().collect::<Vec<_>>());
        assert_eq!(
            read_back(source.oracle().monomials(), PR::ZERO, &context),
            cpu.monomial_forms
                .iter()
                .flatten()
                .copied()
                .collect::<Vec<_>>()
        );
        let queries: Vec<u32> = [
            (9001, 31),
            (0, 7),
            (500, 3),
            (16383, 7),
            (42, 0),
            (1234, 7),
            (500, 3),
            (16383, 31),
            (7777, 16),
            (0, 0),
            (42, 0),
            (3, 1),
            (12000, 30),
            (8191, 15),
            (8192, 15),
            (1, 24),
            (16000, 2),
        ]
        .into_iter()
        .map(|(leaf, coset)| (leaf << cfg.log_lde_factor) | coset)
        .collect();
        let expected = cpu.query_many(
            &queries.iter().map(|&q| q as usize).collect::<Vec<_>>(),
            &twiddles,
            &worker,
        );
        let count = queries.len();
        let depth = opening_path_len(16, &cfg);
        let d_queries = upload(&queries, &context);
        let mut d_leaves = upload(&vec![PR::ONE; count * 4], &context);
        let mut d_paths = upload(&vec![[0xdead_beef; 8]; count * depth], &context);
        let mut d_indexes = upload(&vec![0xaaaa_aaaa; count], &context);
        source
            .open_queries(
                &d_queries,
                &mut d_leaves,
                &mut d_paths,
                &mut d_indexes,
                &context,
            )
            .unwrap();
        let leaves = read_back(&d_leaves, PR::ZERO, &context);
        let paths = read_back(&d_paths, [0; 8], &context);
        let indexes = read_back(&d_indexes, 0u32, &context);
        for (i, expected) in expected.iter().enumerate() {
            let leaf = &leaves[i * 4..(i + 1) * 4];
            let path = &paths[i * depth..(i + 1) * depth];
            assert_eq!(
                leaf,
                &expected.leaf_values_concatenated[..],
                "uploaded leaf {i}"
            );
            assert_eq!(path, &expected.path[..], "uploaded path {i}");
            assert_eq!(indexes[i] as usize, expected.index, "uploaded index {i}");
            assert!(root_matches(leaf, path, expected.index, &host.cap().cap));
        }
        let mut scratch = context.alloc(1 << 16, AllocationPlacement::Top).unwrap();
        source.recompute_coset(31, &mut scratch, &context).unwrap();
        let expected = compute_column_major_lde_single_coset(
            &cpu.monomial_forms[0],
            &twiddles,
            32,
            31,
            &worker,
        );
        assert_eq!(read_back(&scratch, PR::ZERO, &context), expected.to_vec());
        drop(scratch);
        source.release_raw();
        source.release_commitment_state();
        assert_eq!(
            read_back(source.cap(), 0u32, &context),
            host.cap().cap.iter().flatten().copied().collect::<Vec<_>>()
        );
    }
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
