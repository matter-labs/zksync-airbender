use prover::merkle_trees::keccak256_for_everything_tree::keccak_leaf_encoding_words;
use prover::merkle_trees::keccak256_hash_leafs::truncate_keccak_merkle_digest;
mod backward_window;
mod claims;
mod cpu_abi;
mod forward_vm;
mod tails;
use era_cudart::memory::memory_copy_async;
use era_cudart::slice::DeviceSlice;
use fft::Twiddles;
use field::{Field, Proth120};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::PR;
use gpu_prover_context::transfer::single_shot_h2d;
use gpu_prover_context::{ProverContext, ProverContextConfig};
use gpu_trace::trace::packed::{opening_path_len, PackedCommitConfig};
use prover::common_constants::TimestampScalar;
use prover::definitions::{FinalRegisterValue, GKRExternalChallenges};
use prover::gkr::prover::setup::GKRSetup as CpuGKRSetup;
use prover::gkr::prover::OperationMode;
use prover::gkr::whir::coset_commit::CosetByCosetBaseCommitment;
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use prover::merkle_trees::PathQueryable;
use prover::transcript::{Keccak256Transcript, Transcript};
use std::alloc::Global;
use std::sync::Arc;
use worker::Worker;

use super::packed_challenges::{
    boundary_prefix_words, derive, split_challenges, transcript_prefix_words,
    PackedChallengeConfig, PACKED_CHALLENGE_DRAWS,
};
use crate::setup::{L1WrapSetupHost, PackedSetupSource};

type CpuOracle = CosetByCosetBaseCommitment<Proth120, Keccak256MerkleTreeWithCap>;

fn make_context() -> ProverContext {
    ProverContext::new(&ProverContextConfig {
        device_allocation_blocks_count: Some(256),
        host_allocator_blocks_count: 128,
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

fn upload<T: Copy>(host: &[T], context: &ProverContext) -> DeviceAllocation<T> {
    let mut device = context
        .alloc(host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut device, host, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    device
}

#[test]
#[cfg(not(no_cuda))]
fn l1_setup_host_round_trip_small() {
    let context = make_context();
    let mut twiddle_tables = context
        .alloc::<PR>(gpu_ntt::proth120::TABLE_LEN, AllocationPlacement::Bottom)
        .unwrap();
    let mut twiddle_factors = context
        .alloc::<PR>(gpu_ntt::proth120::FACTOR_LEN, AllocationPlacement::BestFit)
        .unwrap();
    let proof_twiddles = gpu_ntt::proth120::prepare_proof_twiddles(
        &mut twiddle_tables,
        &mut twiddle_factors,
        context.get_exec_stream(),
    )
    .unwrap();
    drop(twiddle_factors);
    let worker = Worker::new_with_num_threads(4);
    // Diagnostic rows, production setup width/pack/v1. Host init and proof both retain depth10.
    let log_rows = 15;
    let columns = deterministic_columns(log_rows, 10);
    let twiddles = Twiddles::<PR, Global>::new(1 << (log_rows + 3), &worker);
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
    for (cap_log, pack_log2, log_v) in [(3, 3, 1)] {
        let cfg = PackedCommitConfig {
            log_lde_factor: 4,
            log_values_per_leaf: log_v,
            cap_log,
            skip_bottom: L1WrapSetupHost::PARTIAL_TREE_REDUCTION_LAYERS,
        };
        let cpu = cpu_commit(&columns, log_rows, pack_log2, cfg, &twiddles, &worker);
        let host = Arc::new(L1WrapSetupHost::precompute(&setup, pack_log2, cfg, &context).unwrap());
        assert_eq!(host.log_rows, log_rows);
        assert_eq!(host.columns_count, 10);
        assert_eq!(host.pack_log2, pack_log2);
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
        let last = (1u32 << (log_rows + pack_log2 - log_v)) - 1;
        let queries: Vec<u32> = [
            (last, 15),
            (0, 1),
            (3, 0),
            (last, 15),
            (1, 1),
            (31, 1),
            (32, 1),
            (1023, 0),
            (1024, 0),
            (42, 15),
            (42, 15),
            (last - 1, 1),
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
        let depth = opening_path_len(log_rows + pack_log2, &cfg);
        let leaf_len = 10usize.div_ceil(1 << pack_log2) << log_v;
        let d_queries = upload(&queries, &context);
        let plan =
            gpu_trace::trace::packed::CosetQueryPlan::new(&d_queries, cfg.log_lde_factor, &context)
                .unwrap();
        let mut d_leaves = upload(&vec![PR::ONE; count * leaf_len], &context);
        let mut d_paths = upload(&vec![[0xdead_beef; 8]; count * depth], &context);
        let mut d_indexes = upload(&vec![0xaaaa_aaaa; count], &context);
        source
            .open_queries(
                &plan,
                &d_queries,
                &mut d_leaves,
                &mut d_paths,
                &mut d_indexes,
                proof_twiddles,
                &context,
            )
            .unwrap();
        let leaves = read_back(&d_leaves, PR::ZERO, &context);
        let paths = read_back(&d_paths, [0; 8], &context);
        let indexes = read_back(&d_indexes, 0u32, &context);
        for (i, expected) in expected.iter().enumerate() {
            let leaf = &leaves[i * leaf_len..(i + 1) * leaf_len];
            let path = &paths[i * depth..(i + 1) * depth];
            assert_eq!(
                leaf,
                &expected.leaf_values_concatenated[..],
                "uploaded leaf {i}"
            );
            assert_eq!(path, &expected.path[..], "uploaded path {i}");
            assert_eq!(indexes[i] as usize, expected.index, "uploaded index {i}");
            let packed_columns = cpu.monomial_forms.len();
            let column_major: Vec<PR> = (0..packed_columns)
                .flat_map(|column| {
                    (0..1usize << log_v).map(move |slot| leaf[slot * packed_columns + column])
                })
                .collect();
            assert!(root_matches(
                &column_major,
                path,
                expected.index,
                &host.cap().cap
            ));
        }
        source.release_raw();
        source.release_commitment_state();
        assert_eq!(
            read_back(source.cap(), 0u32, &context),
            host.cap().cap.iter().flatten().copied().collect::<Vec<_>>()
        );
    }
}

fn deterministic_mode(final_timestamp: TimestampScalar) -> OperationMode {
    OperationMode::SingleChunk {
        external_challenges_pow_bits: 20,
        register_final_state: std::array::from_fn(|reg| FinalRegisterValue {
            value: 0x1000_0001u32.wrapping_mul(reg as u32 + 7),
            last_access_timestamp: (0x3_9a5c_1234u64 + 0x1_0007_0011 * reg as u64)
                as TimestampScalar,
        }),
        final_pc: 0x0001_0a3c,
        final_timestamp,
    }
}

fn deterministic_words(count: usize, salt: u32) -> Vec<u32> {
    (0..count as u32)
        .map(|i| i.wrapping_mul(0x9e37_79b9) ^ salt.rotate_left(i % 32))
        .collect()
}

#[test]
#[cfg(not(no_cuda))]
fn packed_challenges_match_cpu_transcript_small() {
    let context = make_context();
    let worker = Worker::new_with_num_threads(4);
    let mode = deterministic_mode(0x2_0000_0003);
    let prefix = boundary_prefix_words(&mode);
    let top_bits = deterministic_words(2, 0x7071);
    let setup_cap = deterministic_words(64, 0x5e70);
    let merged_cap = deterministic_words(64, 0x3e6d);
    let (pow_bits, setup_present) = (20, true);
    let cfg = PackedChallengeConfig {
        pow_bits,
        cap_log: 3,
        top_bits_len: 2,
        setup_present,
    };
    let setup_words: &[u32] = if setup_present { &setup_cap } else { &[] };
    let words: Vec<u32> = [&prefix[..], &top_bits, setup_words, &merged_cap].concat();
    let seed = <Keccak256Transcript as Transcript<Proth120, Proth120>>::commit_initial_u32(&words);
    let mut expected = [Proth120::ZERO; PACKED_CHALLENGE_DRAWS];
    let (expected_seed, expected_nonce) = <Keccak256Transcript as Transcript<
            Proth120,
            Proth120,
        >>::draw_random_field_elements_with_pow(
            &seed, pow_bits, &mut expected, &worker
        );
    let d_prefix = upload(&transcript_prefix_words(&mode, &top_bits), &context);
    let d_setup_cap = upload(setup_words, &context);
    let d_merged_cap = upload(&merged_cap, &context);
    let mut d_seed = upload(&[0u8; 32], &context);
    let challenges = derive(
        &mut d_seed,
        &d_prefix,
        &d_setup_cap,
        &d_merged_cap,
        &cfg,
        &context,
    )
    .unwrap();
    let nonce = read_back(challenges.nonce(), 0u64, &context);
    let values = read_back(challenges.challenges(), PR::ZERO, &context);
    let external = read_back(challenges.external(), PR::ZERO, &context);
    let lookup = read_back(challenges.lookup(), PR::ZERO, &context);
    let final_seed = read_back(&d_seed, 0u8, &context);
    let label = format!("pow_bits={pow_bits}, setup_present={setup_present}");
    assert_eq!(nonce, [expected_nonce], "nonce, {label}");
    assert_eq!(values, expected, "challenges, {label}");
    assert_eq!(final_seed, expected_seed.0, "seed, {label}");
    let (split_external, split_lookup) = split_challenges(&expected);
    assert_eq!(
        split_external,
        GKRExternalChallenges::<Proth120, Proth120>::from_slice(&expected[..7])
    );
    assert_eq!(external, expected[..7], "external, {label}");
    assert_eq!(lookup, split_lookup, "lookup, {label}");
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

fn keccak_words(words: impl IntoIterator<Item = u32>) -> [u32; 8] {
    let swapped: Vec<u32> = words.into_iter().map(u32::swap_bytes).collect();
    let digest =
        <Keccak256Transcript as Transcript<Proth120, Proth120>>::commit_initial_u32(&swapped).0;
    let mut digest = std::array::from_fn(|word| {
        u32::from_be_bytes(digest[4 * word..4 * word + 4].try_into().unwrap())
    });
    truncate_keccak_merkle_digest(&mut digest);
    digest
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
