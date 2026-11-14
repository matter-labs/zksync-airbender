//! Diagnostic packed commit/open parity through the production wrapper.

use std::alloc::Global;

use era_cudart::memory::memory_copy_async;
use fft::Twiddles;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::field::PR;
use gpu_prover_context::{ProverContext, ProverContextConfig};
use prover::gkr::whir::coset_commit::CosetByCosetBaseCommitment;
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use worker::Worker;

use super::super::holder::{TraceHolder, TreesCacheMode, PARTIAL_TREE_REDUCTION_LAYERS};
use super::super::packed::{
    opening_path_len, CosetQueryPlan, PackedCommitConfig, PackedCosetRecomputeOracle,
};

fn check_packed(raw_columns: usize, open: bool) {
    let context = ProverContext::new(&ProverContextConfig {
        device_allocation_blocks_count: Some(512),
        host_allocator_blocks_count: 256,
        ..Default::default()
    })
    .unwrap();
    let stream = context.get_exec_stream();
    let baseline = context.get_used_mem_current();
    {
        // Diagnostic: fewer rows/cosets, production pack3, base12/setup2, v1 and depth10.
        // LDE16/cap8 retains a top-tree path level as well as all within-coset levels.
        let log_rows = 15;
        let pack_log2 = 3;
        let log_packed = log_rows + pack_log2;
        let cfg = PackedCommitConfig {
            log_lde_factor: 4,
            log_values_per_leaf: 1,
            cap_log: 3,
            skip_bottom: 10,
        };
        let packed_columns = raw_columns.div_ceil(8);
        let rows = 1usize << log_rows;
        let flat = super::random_values(rows * raw_columns, raw_columns as u64);
        let columns: Vec<&[PR]> = flat.chunks_exact(rows).collect();
        let worker = Worker::new_with_num_threads(8);
        let twiddles = Twiddles::<PR, Global>::new(1 << log_packed, &worker);
        let cpu = CosetByCosetBaseCommitment::<PR, Keccak256MerkleTreeWithCap>::commit_packed(
            &columns,
            &twiddles,
            1 << cfg.log_lde_factor,
            cfg.log_values_per_leaf as usize,
            1 << cfg.cap_log,
            log_rows as usize,
            pack_log2 as usize,
            &worker,
        );
        let mut raw = TraceHolder::new_without_cosets(
            log_rows,
            cfg.log_lde_factor,
            cfg.log_values_per_leaf,
            cfg.cap_log,
            raw_columns,
            TreesCacheMode::CacheNone,
            PARTIAL_TREE_REDUCTION_LAYERS,
            &context,
        )
        .unwrap();
        memory_copy_async(raw.get_uninit_hypercube_evals_mut(), &flat, stream).unwrap();
        let mut oracle =
            PackedCosetRecomputeOracle::pack_from_columns(raw, pack_log2, &context).unwrap();
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
        oracle.commit(&cfg, proof_twiddles, &context).unwrap();
        let mut cap = vec![[0; 8]; 1 << cfg.cap_log];
        memory_copy_async(&mut cap, oracle.cap_digests(), stream).unwrap();
        let monomials = super::download(oracle.monomials(), stream);
        assert_eq!(
            monomials,
            cpu.monomial_forms
                .iter()
                .flatten()
                .copied()
                .collect::<Vec<_>>()
        );
        assert_eq!(
            super::download(oracle.raw().get_hypercube_evals(), stream),
            flat
        );
        if open {
            let h = log_packed - cfg.log_values_per_leaf;
            let last = (1u32 << h) - 1;
            let coset_mask = (1 << cfg.log_lde_factor) - 1;
            // Distinct touched order [last,1,0], duplicates, same coset, final leaf and Q12.
            let queries: Vec<u32> = [
                (last, coset_mask),
                (0, 1),
                (3, 0),
                (last, coset_mask),
                (1, 1),
                (31, 1),
                (32, 1),
                (1023, 0),
                (1024, 0),
                (42, coset_mask),
                (42, coset_mask),
                (last - 1, 1),
            ]
            .into_iter()
            .map(|(j, k)| (j << cfg.log_lde_factor) | k)
            .collect();
            let expected = cpu.query_many(
                &queries.iter().map(|&q| q as usize).collect::<Vec<_>>(),
                &twiddles,
                &worker,
            );
            let mut d_queries = context
                .alloc(queries.len(), AllocationPlacement::BestFit)
                .unwrap();
            memory_copy_async(&mut d_queries, &queries, stream).unwrap();
            let plan = CosetQueryPlan::new(&d_queries, cfg.log_lde_factor, &context).unwrap();
            let depth = opening_path_len(log_packed, &cfg);
            let leaf_len = packed_columns << cfg.log_values_per_leaf;
            let q = queries.len();
            let leaf_canary = PR::from_u128_with_reduction(0x5eed);
            let path_canary = [0xdead_beef; 8];
            let index_canary = 0xaaaa_aaaa;
            let mut leaves = vec![leaf_canary; q * leaf_len + 2];
            let mut paths = vec![path_canary; q * depth + 2];
            let mut indexes = vec![index_canary; q + 2];
            let mut d_leaves = context
                .alloc(leaves.len(), AllocationPlacement::BestFit)
                .unwrap();
            let mut d_paths = context
                .alloc(paths.len(), AllocationPlacement::BestFit)
                .unwrap();
            let mut d_indexes = context
                .alloc(indexes.len(), AllocationPlacement::BestFit)
                .unwrap();
            memory_copy_async(&mut d_leaves, &leaves, stream).unwrap();
            memory_copy_async(&mut d_paths, &paths, stream).unwrap();
            memory_copy_async(&mut d_indexes, &indexes, stream).unwrap();
            oracle
                .open_queries(
                    &plan,
                    &d_queries,
                    &mut d_leaves[1..q * leaf_len + 1],
                    &mut d_paths[1..q * depth + 1],
                    &mut d_indexes[1..q + 1],
                    proof_twiddles,
                    &context,
                )
                .unwrap();
            memory_copy_async(&mut leaves, &d_leaves, stream).unwrap();
            memory_copy_async(&mut paths, &d_paths, stream).unwrap();
            memory_copy_async(&mut indexes, &d_indexes, stream).unwrap();
            oracle.release_raw();
            oracle.release_commitment_state();
            drop(oracle);
            // Reuse freed pool storage after queued readers and D2H copies, before synchronization.
            let mut churn = context
                .alloc::<u8>(16 << 20, AllocationPlacement::BestFit)
                .unwrap();
            let churn_bytes = vec![0xa5; 16 << 20];
            memory_copy_async(&mut churn, &churn_bytes, stream).unwrap();
            stream.synchronize().unwrap();
            assert_eq!([leaves[0], leaves[q * leaf_len + 1]], [leaf_canary; 2]);
            assert_eq!([paths[0], paths[q * depth + 1]], [path_canary; 2]);
            assert_eq!([indexes[0], indexes[q + 1]], [index_canary; 2]);
            for (i, expected) in expected.iter().enumerate() {
                assert_eq!(
                    &leaves[1 + i * leaf_len..1 + (i + 1) * leaf_len],
                    &expected.leaf_values_concatenated
                );
                assert_eq!(
                    &paths[1 + i * depth..1 + (i + 1) * depth],
                    &expected.path,
                    "complete path including top tree for query {i}"
                );
                assert_eq!(indexes[1 + i] as usize, expected.index);
            }
        } else {
            oracle.release_raw();
            oracle.release_commitment_state();
            assert_eq!(
                super::download(oracle.cap_digests(), stream),
                cpu.get_cap().cap
            );
        }
        stream.synchronize().unwrap();
        assert_eq!(cap, cpu.get_cap().cap);
    }
    stream.synchronize().unwrap();
    assert_eq!(
        context.get_used_mem_current(),
        baseline,
        "packed allocations released"
    );
}

#[test]
#[cfg(not(no_cuda))]
fn sink_commit_matches_reference() {
    for columns in [96, 10] {
        check_packed(columns, false);
    }
}

#[test]
#[cfg(not(no_cuda))]
fn sink_open_queries_matches_gathers() {
    for columns in [96, 10] {
        check_packed(columns, true);
    }
}
