use super::*;
use crate::upstream::{BaseColumns, Field};
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::UnsafeMutAccessor;
use gpu_core::primitives::field::E4;
use prover::allocation_pool::GenericAllocationPool;
use prover::definitions::SecurityLevel;
use prover::gkr::prover::backend::NaiveBackend;
use prover::gkr::prover::stages::commitment_utils::commit_trace_part_with_packing;
use prover::gkr::prover_config::{
    ProverConfig, WhirBaseRoundSchedule, WhirInternalRound, WhirSchedule,
};
use prover::gkr::whir::ColumnMajorBaseOracleForLDE;
use prover::merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap;
use std::alloc::Global;
use worker::Worker;

type CpuOracle = ColumnMajorBaseOracleForLDE<BF, Blake2sU32MerkleTreeWithCap<Global>>;

fn config(message_log: usize, pack_log: usize, fold_log: usize) -> ProverConfig {
    ProverConfig::whir_only(
        message_log - pack_log,
        WhirSchedule {
            cap_size: 16,
            base_round: WhirBaseRoundSchedule {
                lde_factor_log2: 1,
                physical_packing_log2: pack_log,
                fold_log2: fold_log,
                num_queries: 1,
                ..Default::default()
            },
            internal_rounds: vec![WhirInternalRound {
                lde_factor_log2: 1,
                folding_log2: 5,
                num_queries: 1,
                queries_pow_bits: 0,
                folding_pow_bits: 0,
                num_ood_samples: 1,
                ood_pow_bits: 0,
            }],
        },
        SecurityLevel::Sec100,
    )
}

fn source(columns: usize, rows: usize) -> Vec<BF> {
    (0..columns)
        .flat_map(|column| {
            (0..rows).map(move |row| {
                let word = (row as u32
                    ^ (row as u32).rotate_left(13)
                    ^ (column as u32).wrapping_mul(0x9e3779b9))
                .wrapping_mul(0x85ebca6b);
                BF::new(word % 1_000_003)
            })
        })
        .collect()
}

fn cpu_oracle(config: &ProverConfig, raw: &[BF], worker: &Worker) -> CpuOracle {
    let rows = 1usize << config.trace_len_log2;
    let columns: Vec<_> = raw.chunks_exact(rows).collect();
    let twiddles =
        fft::Twiddles::<BF, Global>::new(1usize << config.whir_message_size_log2(), worker);
    commit_trace_part_with_packing::<BF, E4, Blake2sU32MerkleTreeWithCap<Global>, _>(
        &NaiveBackend,
        &columns,
        &twiddles,
        config.lde_factor(),
        config.base_oracles_values_per_leaf().trailing_zeros() as usize,
        config.cap_size,
        config.trace_len_log2,
        config.pack_log2(),
        &GenericAllocationPool::proxy(),
        worker,
    )
}

fn geometry(config: &ProverConfig, role: BaseOracleRole, columns: usize) -> BaseCommitmentGeometry {
    let mut counts = BaseColumns {
        memory: 0,
        witness: 0,
        setup: 0,
    };
    match role {
        BaseOracleRole::Memory => counts.memory = columns,
        BaseOracleRole::Witness => counts.witness = columns,
        BaseOracleRole::Setup => counts.setup = columns,
    }
    BaseCommitmentGeometry::from_config(config, counts)
}

fn read_device<T: Copy + Default>(data: &DeviceSlice<T>, context: &ProverContext) -> Vec<T> {
    let mut host = vec![T::default(); data.len()];
    if !data.is_empty() {
        memory_copy_async(&mut host, data, context.get_exec_stream()).unwrap();
    }
    context.get_exec_stream().synchronize().unwrap();
    host
}

fn read_openings(opened: LeafsAndMerklePaths, context: &ProverContext) -> (Vec<BF>, Vec<Digest>) {
    let leaves = opened.leafs.get_accessor();
    let paths = opened.merkle_paths.get_accessor();
    let mut output = Box::new(None);
    let dst = UnsafeMutAccessor::new(output.as_mut());
    let mut callbacks = Callbacks::new();
    callbacks
        .schedule(
            move || unsafe {
                // SAFETY: the preceding D2H copies and this callback are ordered on exec;
                // output is exclusively callback-owned until synchronization below.
                assert!(dst
                    .get_mut()
                    .replace((leaves.get().to_vec(), paths.get().to_vec()))
                    .is_none());
            },
            context.get_exec_stream(),
        )
        .unwrap();
    drop(opened);
    context.get_exec_stream().synchronize().unwrap();
    drop(callbacks);
    output.unwrap()
}

fn assert_materialized_openings(
    holder: &mut TraceHolder<BF>,
    cpu: &CpuOracle,
    context: &ProverContext,
) {
    let leaves_per_coset =
        1usize << (holder.commitment_log_domain_size() - holder.log_rows_per_leaf);
    let indices = [
        0,
        1,
        leaves_per_coset / 2 - 1,
        leaves_per_coset / 2,
        leaves_per_coset - 1,
        0,
    ];
    let mut query_indices = context
        .alloc::<u32>(indices.len(), AllocationPlacement::BestFit)
        .unwrap();
    let query_host: Vec<u32> = indices.iter().map(|index| *index as u32).collect();
    memory_copy_async(&mut query_indices, &query_host, context.get_exec_stream()).unwrap();
    for coset in 0..1usize << holder.log_lde_factor {
        let opened = holder
            .get_leafs_and_merkle_paths(coset, &query_indices, context)
            .unwrap();
        let (leaves, paths) = read_openings(opened, context);
        if holder.committed_columns_count() == 0 {
            assert!(leaves.is_empty() && paths.is_empty());
            continue;
        }
        let columns = holder.committed_columns_count();
        let slots = 1usize << holder.log_rows_per_leaf;
        let layers = holder.query_merkle_path_layout(indices.len()).0 as usize;
        for (query, &index) in indices.iter().enumerate() {
            let (_, _, expected) =
                cpu.query_for_folded_index((index << holder.log_lde_factor) | coset);
            let actual: Vec<_> = (0..slots)
                .flat_map(|slot| (0..columns).map(move |column| (column, slot)))
                .map(|(column, slot)| leaves[column * indices.len() * slots + query * slots + slot])
                .collect();
            assert_eq!(
                actual, expected.leaf_values_concatenated,
                "leaf coset {coset} query {index}"
            );
            // Existing per-coset gathers store [layer][query] digests.
            let actual_path: Vec<_> = (0..layers)
                .map(|layer| paths[layer * indices.len() + query])
                .collect();
            assert_eq!(
                actual_path, expected.path,
                "path coset {coset} query {index}"
            );
        }
    }
}

#[test]
fn in_place_restores_padded_backing() {
    let context = super::tests::make_test_context(512, 16);
    let worker = Worker::new_with_num_threads(4);
    let cfg = config(22, 2, 1);
    let shape = geometry(&cfg, BaseOracleRole::Witness, 5);
    let raw = source(5, 1 << cfg.trace_len_log2);
    let cpu = cpu_oracle(&cfg, &raw, &worker);
    let baseline = context.get_used_mem_current();
    let padded_len =
        shape.oracle(BaseOracleRole::Witness).physical_columns() << shape.message_size_log2();
    let mut dirty = context
        .alloc::<BF>(padded_len, AllocationPlacement::Bottom)
        .unwrap();
    let dirty_values = vec![BF::new(17); padded_len];
    memory_copy_async(&mut dirty, &dirty_values, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    let recycled_ptr = dirty.as_ptr();
    drop(dirty);
    let mut holder = TraceHolder::<BF>::new_base_without_cosets(
        shape,
        BaseOracleRole::Witness,
        TreesCacheMode::CachePartial,
        &context,
    )
    .unwrap();
    assert_eq!(holder.padded_hypercube_evals().as_ptr(), recycled_ptr);
    memory_copy_async(
        holder.get_uninit_hypercube_evals_mut(),
        &raw,
        context.get_exec_stream(),
    )
    .unwrap();
    holder.commit_in_place(None, &context).unwrap();
    assert_eq!(
        holder.read_full_cap_synchronously(&context).unwrap(),
        cpu.get_cap()
    );
    let restored = read_device(holder.padded_hypercube_evals(), &context);
    assert_eq!(&restored[..raw.len()], raw);
    assert!(restored[raw.len()..].iter().all(|value| *value == BF::ZERO));
    drop(holder);
    assert_eq!(context.get_used_mem_current(), baseline);
}

#[test]
fn compact_domain_full_tree_openings_match_cpu() {
    let context = super::tests::make_test_context(256, 16);
    let worker = Worker::new_with_num_threads(4);
    let cfg = config(14, 2, 0);
    let raw = source(5, 1 << cfg.trace_len_log2);
    let cpu = cpu_oracle(&cfg, &raw, &worker);
    let baseline = context.get_used_mem_current();
    let mut holder = TraceHolder::<BF>::new_base(
        geometry(&cfg, BaseOracleRole::Memory, 5),
        BaseOracleRole::Memory,
        TreesCacheMode::CacheFull,
        &context,
    )
    .unwrap();
    memory_copy_async(
        holder.get_uninit_hypercube_evals_mut(),
        &raw,
        context.get_exec_stream(),
    )
    .unwrap();
    holder.commit_all(&context).unwrap();
    assert_eq!(
        holder.read_full_cap_synchronously(&context).unwrap(),
        cpu.get_cap()
    );
    assert_materialized_openings(&mut holder, &cpu, &context);
    drop(holder);
    assert_eq!(context.get_used_mem_current(), baseline);
}
