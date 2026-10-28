use super::*;
use crate::upstream::{BaseColumns, Field};
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::UnsafeMutAccessor;
use gpu_core::primitives::field::E4;
use prover::allocation_pool::GenericAllocationPool;
use prover::definitions::SecurityLevel;
use prover::gkr::prover::backend::NaiveBackend;
use prover::gkr::prover::stages::commitment_utils::commit_trace_part_with_packing;
use prover::gkr::prover::WhirSchedule;
use prover::gkr::prover_config::ProverConfig;
use prover::gkr::whir::hypercube_to_monomial::parallel_multivariate_hypercube_evals_into_coeffs;
use prover::gkr::whir::ColumnMajorBaseOracleForLDE;
use prover::merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap;
use std::alloc::Global;
use worker::Worker;

type CpuOracle = ColumnMajorBaseOracleForLDE<BF, Blake2sU32MerkleTreeWithCap<Global>>;

fn assert_values<T: PartialEq + std::fmt::Debug>(actual: &[T], expected: &[T], what: &str) {
    assert_eq!(actual.len(), expected.len(), "{what}: length");
    if let Some(index) = actual
        .iter()
        .zip(expected)
        .position(|(actual, expected)| actual != expected)
    {
        panic!(
            "{what}: first mismatch at {index}: {:?} != {:?}",
            actual[index], expected[index]
        );
    }
}

fn test_config(message_log: usize, k: usize) -> ProverConfig {
    test_config_with_base_fold(message_log, k, 1)
}

fn test_config_with_base_fold(message_log: usize, k: usize, fold: usize) -> ProverConfig {
    ProverConfig::whir_only(
        message_log - k,
        WhirSchedule::from_legacy_arrays(2, 16, k, &[fold, 5], &[1, 1], &[2], &[0, 0]),
        SecurityLevel::Sec100,
    )
}

#[test]
fn cpu_virtual_base_layout_accepts_zero_fold_geometry() {
    for k in [0, 2] {
        let config = test_config_with_base_fold(22, k, 0);
        let shape = geometry(&config, BaseOracleRole::Memory, 5);
        assert_eq!(shape.values_per_leaf(), 1);
        for tree in [
            TreesCacheMode::CacheNone,
            TreesCacheMode::CachePartial,
            TreesCacheMode::CacheFull,
        ] {
            TraceHolder::<BF>::validate_base_layout(&shape, tree);
        }
    }
}

fn validate_test_geometry(geometry: &BaseCommitmentGeometry, _depth: u32) {
    TraceHolder::<BF>::validate_base_layout(geometry, TreesCacheMode::CachePartial);
    validate_baby_bear_base_geometry(geometry, gpu_ntt::ntt_twiddles::OMEGA_LOG_ORDER);
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
    BaseCommitmentGeometry::from_config(config, counts).unwrap()
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

fn assert_raw_and_monomials(
    holder: &TraceHolder<BF>,
    raw: &[BF],
    worker: &Worker,
    context: &ProverContext,
) {
    assert_eq!(
        holder.get_hypercube_evals().as_ptr(),
        holder.padded_hypercube_evals().as_ptr()
    );
    assert_eq!(holder.get_hypercube_evals().len(), raw.len());
    let padded = read_device(holder.padded_hypercube_evals(), context);
    assert_values(&padded[..raw.len()], raw, "logical prefix");
    assert!(padded[raw.len()..].iter().all(|value| *value == BF::ZERO));
    let message = 1usize << holder.commitment_log_domain_size();
    assert_eq!(padded.len(), holder.committed_columns_count() * message);
    if holder.committed_columns_count() == 0 {
        return;
    }
    let mut coefficients = context
        .alloc::<BF>(message, AllocationPlacement::BestFit)
        .unwrap();
    for (column, expected_source) in padded.chunks_exact(message).enumerate() {
        let mut expected = expected_source.to_vec();
        parallel_multivariate_hypercube_evals_into_coeffs(
            &mut expected,
            holder.commitment_log_domain_size(),
            worker,
        );
        hypercube_evals_to_monomials(
            &holder.padded_hypercube_evals()[column * message..(column + 1) * message],
            &mut coefficients[..],
            holder.commitment_log_domain_size() as usize,
            false,
            context.get_exec_stream(),
            context.get_device_properties(),
        )
        .unwrap();
        assert_values(
            &read_device(&coefficients, context),
            &expected,
            &format!("packed monomials column {column}"),
        );
    }
    assert_values(
        &read_device(holder.padded_hypercube_evals(), context),
        &padded,
        "out-of-place Mobius preserves raw",
    );
}

fn assert_cosets(holder: &TraceHolder<BF>, cpu: &CpuOracle, context: &ProverContext) {
    let ColumnMajorBaseOracleForLDE::InMemory(reference) = cpu else {
        unreachable!()
    };
    let message_log = holder.commitment_log_domain_size();
    let message = 1usize << message_log;
    for (coset, expected) in reference.cosets.cosets.iter().enumerate() {
        let actual = read_device(holder.get_coset_evaluations(coset), context);
        for (column, expected) in expected.original_values_normal_order.iter().enumerate() {
            for row in 0..message {
                assert_eq!(
                    actual[column * message + row],
                    expected.get(bitreverse_index(row, message_log)),
                    "coset {coset}, physical column {column}, row {row}"
                );
            }
        }
    }
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

fn materialized_case(
    config: &ProverConfig,
    role: BaseOracleRole,
    columns: usize,
    raw: &[BF],
    cpu: &CpuOracle,
    tree: TreesCacheMode,
    deferred: bool,
    monomials: bool,
    worker: &Worker,
    context: &ProverContext,
) {
    let baseline = context.get_used_mem_current();
    let geometry = geometry(config, role, columns);
    validate_baby_bear_base_geometry(
        &geometry,
        context
            .ntt_device_context()
            .whir_leaf_transform_params()
            .omega_log_order,
    );
    let mut holder = TraceHolder::<BF>::new_base(geometry, role, tree, context).unwrap();
    assert_eq!(
        (holder.log_domain_size as usize, holder.columns_count),
        (config.trace_len_log2, columns)
    );
    assert_eq!(
        holder.allocated_columns(),
        geometry.oracle(role).padded_columns()
    );
    memory_copy_async(
        holder.get_uninit_hypercube_evals_mut(),
        raw,
        context.get_exec_stream(),
    )
    .unwrap();
    if monomials {
        assert_raw_and_monomials(&holder, raw, worker, context);
    }
    holder.commit_all(context).unwrap();
    assert_eq!(
        holder.read_full_cap_synchronously(context).unwrap(),
        cpu.get_cap()
    );
    assert_values(
        &read_device(holder.get_hypercube_evals(), context),
        raw,
        "commit preserves logical source",
    );
    if deferred {
        holder.release_cosets();
        holder.defer_materialization_until_queries(OpeningStrategy::AllCosets);
    }
    holder.finish_raw_batching(context).unwrap();
    assert!(holder.raw_hypercube_evals.is_none());
    holder.prepare_full_opening(context).unwrap();
    assert_cosets(&holder, cpu, context);
    assert_materialized_openings(&mut holder, cpu, context);
    drop(holder);
    assert_eq!(
        context.get_used_mem_current(),
        baseline,
        "packed holder reservations return to baseline"
    );
}

fn materialized_matrix(k: usize) {
    materialized_matrix_with_base_fold(k, 1)
}

fn materialized_matrix_with_base_fold(k: usize, fold: usize) {
    let context = super::tests::make_test_context(256, 16);
    let worker = Worker::new_with_num_threads(4);
    let config = test_config_with_base_fold(13, k, fold);
    let pack = 1usize << k;
    let mut cases = 0;
    for columns in [0, 1, pack - 1, pack, pack + 1, 2 * pack + 1] {
        let raw = source(columns, 1usize << config.trace_len_log2);
        let cpu = cpu_oracle(&config, &raw, &worker);
        for role in [
            BaseOracleRole::Memory,
            BaseOracleRole::Witness,
            BaseOracleRole::Setup,
        ] {
            for tree in [
                TreesCacheMode::CacheNone,
                TreesCacheMode::CachePartial,
                TreesCacheMode::CacheFull,
            ] {
                for deferred in [false, true] {
                    materialized_case(
                        &config, role, columns, &raw, &cpu, tree, deferred, !deferred, &worker,
                        &context,
                    );
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 108);
    eprintln!("packed_base_cpu_parity: k={k}, f={fold}, materialized/deferred AllCosets, 108 cases (6 widths x 3 roles x 3 tree modes x 2 lifecycles)");
}

fn assert_recomputed_openings(
    holder: &mut TraceHolder<BF>,
    cpu: &CpuOracle,
    context: &ProverContext,
) {
    let log_f = holder.log_lde_factor;
    let leaves_per_coset =
        1usize << (holder.commitment_log_domain_size() - holder.log_rows_per_leaf);
    let mut query_host: Vec<u32> = (0..1usize << log_f)
        .flat_map(|coset| {
            [
                coset as u32,
                (((leaves_per_coset - 1) << log_f) | coset) as u32,
                ((127 << log_f) | coset) as u32,
            ]
        })
        .collect();
    query_host.extend([0, 0]);
    let mut queries = context
        .alloc(query_host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut queries, &query_host, context.get_exec_stream()).unwrap();
    let columns = holder.committed_columns_count();
    let slots = 1usize << holder.log_rows_per_leaf;
    let layers = if columns == 0 {
        0
    } else {
        holder.query_merkle_path_layout(query_host.len()).0 as usize
    };
    let mut leaves = context
        .alloc::<BF>(
            query_host.len() * columns * slots,
            AllocationPlacement::BestFit,
        )
        .unwrap();
    let mut paths = context
        .alloc::<u32>(query_host.len() * layers * 8, AllocationPlacement::BestFit)
        .unwrap();
    holder.defer_materialization_until_queries(OpeningStrategy::PerCoset);
    holder.finish_raw_batching(context).unwrap();
    assert!(holder.raw_hypercube_evals.is_none());
    holder
        .gather_openings_recomputed(&queries, &mut leaves, &mut paths, context)
        .unwrap();
    let leaves = read_device(&leaves, context);
    let paths = read_device(&paths, context);
    if columns == 0 {
        assert!(leaves.is_empty() && paths.is_empty());
        return;
    }
    for (query, index) in query_host.iter().enumerate() {
        let (_, _, expected) = cpu.query_for_folded_index(*index as usize);
        assert_values(
            &leaves[query * columns * slots..(query + 1) * columns * slots],
            &expected.leaf_values_concatenated,
            &format!("recomputed leaf query {index}"),
        );
        let actual_path: Vec<Digest> = (0..layers)
            .map(|layer| {
                let offset = (query * layers + layer) * 8;
                paths[offset..offset + 8].try_into().unwrap()
            })
            .collect();
        assert_eq!(actual_path, expected.path, "recomputed path query {index}");
    }
}

fn recomputed_case(
    config: &ProverConfig,
    role: BaseOracleRole,
    columns: usize,
    raw: &[BF],
    cpu: &CpuOracle,
    tree: TreesCacheMode,
    retained: bool,
    worker: &Worker,
    context: &ProverContext,
) {
    let baseline = context.get_used_mem_current();
    let geometry = geometry(config, role, columns);
    validate_baby_bear_base_opening(
        &geometry,
        OpeningStrategy::PerCoset,
        tree,
        context
            .ntt_device_context()
            .whir_leaf_transform_params()
            .omega_log_order,
    );
    let mut holder =
        TraceHolder::<BF>::new_base_without_cosets(geometry, role, tree, context).unwrap();
    memory_copy_async(
        holder.get_uninit_hypercube_evals_mut(),
        raw,
        context.get_exec_stream(),
    )
    .unwrap();
    if retained {
        holder.commit_with_monomials(None, context).unwrap();
        holder.retain_after_commitment(WitnessPostCommitStorage::RawAndMonomials);
        if columns != 0 {
            let monomials = holder.opening_monomials.as_ref().unwrap();
            let message = 1usize << holder.commitment_log_domain_size();
            for column in 0..holder.committed_columns_count() {
                let offset = column * message;
                let copied = raw.len().saturating_sub(offset).min(message);
                let mut expected = vec![BF::ZERO; message];
                expected[..copied]
                    .copy_from_slice(&raw[offset.min(raw.len())..offset.min(raw.len()) + copied]);
                parallel_multivariate_hypercube_evals_into_coeffs(
                    &mut expected,
                    holder.commitment_log_domain_size(),
                    worker,
                );
                assert_values(
                    &read_device(&monomials[offset..offset + message], context),
                    &expected,
                    &format!("retained monomials column {column}"),
                );
            }
        }
    } else {
        holder.commit_all(context).unwrap();
        holder.release_cosets();
    }
    assert_eq!(
        holder.read_full_cap_synchronously(context).unwrap(),
        cpu.get_cap()
    );
    assert_values(
        &read_device(holder.get_hypercube_evals(), context),
        raw,
        "PerCoset commit preserves logical source",
    );
    assert_recomputed_openings(&mut holder, cpu, context);
    drop(holder);
    assert_eq!(context.get_used_mem_current(), baseline);
}

fn recomputed_matrix(k: usize, retained: bool) {
    recomputed_matrix_with_base_fold(k, retained, 1)
}

fn recomputed_matrix_with_base_fold(k: usize, retained: bool, fold: usize) {
    let context = super::tests::make_test_context(256, 16);
    let worker = Worker::new_with_num_threads(4);
    let config = test_config_with_base_fold(20, k, fold);
    let pack = 1usize << k;
    let mut cases = 0;
    for columns in [0, 1, pack - 1, pack, pack + 1, 2 * pack + 1] {
        let raw = source(columns, 1usize << config.trace_len_log2);
        let cpu = cpu_oracle(&config, &raw, &worker);
        for role in [
            BaseOracleRole::Memory,
            BaseOracleRole::Witness,
            BaseOracleRole::Setup,
        ] {
            let modes: &[TreesCacheMode] = if retained {
                &[TreesCacheMode::CachePartial]
            } else {
                &[TreesCacheMode::CacheNone, TreesCacheMode::CachePartial]
            };
            for &tree in modes {
                recomputed_case(
                    &config, role, columns, &raw, &cpu, tree, retained, &worker, &context,
                );
                cases += 1;
            }
        }
    }
    assert_eq!(cases, if retained { 18 } else { 36 });
    eprintln!(
        "packed_base_cpu_parity: k={k}, f={fold}, PerCoset retained={retained}, {cases} cases"
    );
}

macro_rules! virtual_base_tests {
    ($all:ident, $raw:ident, $retained:ident, $k:expr) => {
        #[test]
        fn $all() {
            materialized_matrix_with_base_fold($k, 0);
        }
        #[test]
        fn $raw() {
            recomputed_matrix_with_base_fold($k, false, 0);
        }
        #[test]
        fn $retained() {
            recomputed_matrix_with_base_fold($k, true, 0);
        }
    };
}
virtual_base_tests!(
    virtual_base_cpu_parity_all_cosets_k0,
    virtual_base_cpu_parity_recompute_k0,
    virtual_base_cpu_parity_retained_k0,
    0
);
virtual_base_tests!(
    virtual_base_cpu_parity_all_cosets_k2,
    virtual_base_cpu_parity_recompute_k2,
    virtual_base_cpu_parity_retained_k2,
    2
);

fn virtual_default_domain(k: usize) {
    use crate::witness::circuit_type::{CircuitType, DelegationCircuitType};
    let circuit = if k == 0 {
        CircuitType::Delegation(DelegationCircuitType::BigIntWithControl)
    } else {
        CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression)
    };
    let config = circuit.prover_config(SecurityLevel::Sec100);
    assert_eq!(
        (
            config.pack_log2(),
            config.whir_message_size_log2(),
            config.base_round().fold_log2
        ),
        (k, 22, 0)
    );
    let context = super::tests::make_test_context(4096, 128);
    let worker = Worker::new_with_num_threads(4);
    let pack = 1usize << k;
    let mut cases = 0;
    // Capability widths exercise tails and empties at the default domain.
    // Full artifact-width qualification belongs to complete proof parity.
    for columns in [0, 1, pack - 1, pack, pack + 1, 2 * pack + 1] {
        let raw = source(columns, 1usize << config.trace_len_log2);
        let cpu = cpu_oracle(&config, &raw, &worker);
        for role in [
            BaseOracleRole::Memory,
            BaseOracleRole::Witness,
            BaseOracleRole::Setup,
        ] {
            for deferred in [false, true] {
                materialized_case(
                    &config,
                    role,
                    columns,
                    &raw,
                    &cpu,
                    TreesCacheMode::CachePartial,
                    deferred,
                    !deferred,
                    &worker,
                    &context,
                );
                cases += 1;
            }
            for retained in [false, true] {
                recomputed_case(
                    &config,
                    role,
                    columns,
                    &raw,
                    &cpu,
                    TreesCacheMode::CachePartial,
                    retained,
                    &worker,
                    &context,
                );
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 72);
    eprintln!("virtual_base_cpu_parity default domain: n={}, k={k}, m=22, f=0, 72 cases (6 capability widths x 3 roles x 4 lifecycles)", config.trace_len_log2);
}

#[test]
#[ignore = "default virtual domain primitive parity with independent CPU commitment"]
fn virtual_base_cpu_parity_default_domain_k0() {
    virtual_default_domain(0);
}

#[test]
#[ignore = "default physical+virtual domain primitive parity with independent CPU commitment"]
fn virtual_base_cpu_parity_default_domain_k2() {
    virtual_default_domain(2);
}

macro_rules! recomputed_tests {
    ($($name:ident: ($k:expr, $retained:expr)),* $(,)?) => { $(#[test] fn $name() { recomputed_matrix($k, $retained); })* };
}
recomputed_tests! {
    packed_base_cpu_parity_retained_k0: (0, true), packed_base_cpu_parity_retained_k1: (1, true),
    packed_base_cpu_parity_retained_k2: (2, true), packed_base_cpu_parity_retained_k3: (3, true),
    packed_base_cpu_parity_retained_k4: (4, true),
    packed_base_cpu_parity_recompute_k0: (0, false), packed_base_cpu_parity_recompute_k1: (1, false),
    packed_base_cpu_parity_recompute_k2: (2, false), packed_base_cpu_parity_recompute_k3: (3, false),
    packed_base_cpu_parity_recompute_k4: (4, false),
}

fn production_target(trace_log: usize, k: usize, widths: [usize; 3], role: BaseOracleRole) {
    let config = prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture(trace_log, k, SecurityLevel::Sec100);
    assert_eq!(
        (
            config.whir_message_size_log2(),
            config.lde_factor(),
            config.cap_size
        ),
        (trace_log + k, 2, 16)
    );
    let columns = widths[match role {
        BaseOracleRole::Memory => 0,
        BaseOracleRole::Witness => 1,
        BaseOracleRole::Setup => 2,
    }];
    let raw = source(columns, 1usize << trace_log);
    let worker = Worker::new_with_num_threads(4);
    let cpu = cpu_oracle(&config, &raw, &worker);
    let context = super::tests::make_test_context(16 * 1024, 128);
    for deferred in [false, true] {
        materialized_case(
            &config,
            role,
            columns,
            &raw,
            &cpu,
            TreesCacheMode::CachePartial,
            deferred,
            !deferred,
            &worker,
            &context,
        );
    }
    for retained in [false, true] {
        recomputed_case(
            &config,
            role,
            columns,
            &raw,
            &cpu,
            TreesCacheMode::CachePartial,
            retained,
            &worker,
            &context,
        );
    }
    eprintln!("packed_base_cpu_parity target: N={trace_log}, k={k}, role={role:?}, logical={columns}, policies=4");
}

macro_rules! production_tests {
    ($($name:ident: ($n:expr, $k:expr, $widths:expr, $role:ident)),* $(,)?) => { $(
        #[test] #[ignore = "production-sized independent CPU/GPU oracle parity"]
        fn $name() { production_target($n, $k, $widths, BaseOracleRole::$role); }
    )* };
}
production_tests! {
    packed_base_cpu_parity_blake20_pack4_memory: (20, 4, [225, 538, 6], Memory),
    packed_base_cpu_parity_blake20_pack4_witness: (20, 4, [225, 538, 6], Witness),
    packed_base_cpu_parity_blake20_pack4_setup: (20, 4, [225, 538, 6], Setup),
    packed_base_cpu_parity_blake20_pack2_memory: (20, 2, [225, 538, 6], Memory),
    packed_base_cpu_parity_blake20_pack2_witness: (20, 2, [225, 538, 6], Witness),
    packed_base_cpu_parity_blake20_pack2_setup: (20, 2, [225, 538, 6], Setup),
    packed_base_cpu_parity_unified23_pack1_memory: (23, 1, [38, 58, 10], Memory),
    packed_base_cpu_parity_unified23_pack1_witness: (23, 1, [38, 58, 10], Witness),
    packed_base_cpu_parity_unified23_pack1_setup: (23, 1, [38, 58, 10], Setup),
}

#[test]
fn cpu_packed_base_geometry_admission_is_cuda_free() {
    for (message, k) in [(13, 0), (20, 4), (24, 1)] {
        let config = test_config(message, k);
        validate_test_geometry(
            &geometry(&config, BaseOracleRole::Memory, 1),
            PARTIAL_TREE_REDUCTION_LAYERS,
        );
    }
    let mut invalid = vec![test_config(25, 1)];
    let mut root = test_config(24, 1);
    root.whir_schedule.base_round.lde_factor_log2 = 4;
    invalid.push(root);
    let mut merged = test_config(20, 1);
    merged.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    invalid.push(merged);
    let mut cap = test_config(20, 1);
    cap.cap_size = 1;
    cap.whir_schedule.cap_size = 1;
    invalid.push(cap);
    for config in invalid {
        let geometry = geometry(&config, BaseOracleRole::Memory, 1);
        assert!(std::panic::catch_unwind(|| validate_test_geometry(
            &geometry,
            PARTIAL_TREE_REDUCTION_LAYERS
        ))
        .is_err());
    }
    assert!(!gpu_ntt::ntt::log_size_supports_retained_monomials(19));
    assert!(gpu_ntt::ntt::log_size_supports_retained_monomials(20));
    assert!(gpu_ntt::ntt::log_size_supports_retained_monomials(24));
    assert!(!gpu_ntt::ntt::log_size_supports_retained_monomials(25));
}

#[test]
fn packed_base_cpu_parity_rejects_untested_policies_before_work() {
    use std::panic::{catch_unwind, AssertUnwindSafe};
    let context = super::tests::make_test_context(256, 16);
    let config = test_config(13, 1);
    let mut holder = TraceHolder::<BF>::new_base_without_cosets(
        geometry(&config, BaseOracleRole::Memory, 1),
        BaseOracleRole::Memory,
        TreesCacheMode::CachePartial,
        &context,
    )
    .unwrap();
    let before = context.get_used_mem_current();
    assert!(catch_unwind(AssertUnwindSafe(
        || holder.defer_materialization_until_queries(OpeningStrategy::InPlace)
    ))
    .is_err());
    assert!(catch_unwind(AssertUnwindSafe(|| {
        validate_baby_bear_base_opening(
            &geometry(&config, BaseOracleRole::Memory, 1),
            OpeningStrategy::PerCoset,
            TreesCacheMode::CachePartial,
            context
                .ntt_device_context()
                .whir_leaf_transform_params()
                .omega_log_order,
        );
        holder.defer_materialization_until_queries(OpeningStrategy::PerCoset)
    }))
    .is_err());
    assert!(catch_unwind(AssertUnwindSafe(
        || holder.commit_with_monomials(None, &context)
    ))
    .is_err());
    assert!(catch_unwind(AssertUnwindSafe(|| holder.commit_in_place(None, &context))).is_err());
    assert_eq!(context.get_used_mem_current(), before);

    // A supported transform family alone does not admit untested storage
    // combinations. Reject before cap allocation or any raw-data write.
    let config = test_config(20, 1);
    let geometry = geometry(&config, BaseOracleRole::Memory, 1);
    for (all_cosets, tree) in [
        (true, TreesCacheMode::CachePartial),
        (false, TreesCacheMode::CacheNone),
        (false, TreesCacheMode::CacheFull),
    ] {
        let mut holder = if all_cosets {
            TraceHolder::<BF>::new_base(geometry, BaseOracleRole::Memory, tree, &context)
        } else {
            TraceHolder::<BF>::new_base_without_cosets(
                geometry,
                BaseOracleRole::Memory,
                tree,
                &context,
            )
        }
        .unwrap();
        let raw = vec![BF::ONE; holder.get_hypercube_evals().len()];
        memory_copy_async(
            holder.get_uninit_hypercube_evals_mut(),
            &raw,
            context.get_exec_stream(),
        )
        .unwrap();
        let before = context.get_used_mem_current();
        assert!(catch_unwind(AssertUnwindSafe(
            || holder.commit_with_monomials(None, &context)
        ))
        .is_err());
        assert_eq!(context.get_used_mem_current(), before);
        assert_values(
            &read_device(holder.get_hypercube_evals(), &context),
            &raw,
            "policy rejection preserves raw",
        );
    }
}

macro_rules! materialized_tests {
    ($($name:ident: $k:expr),* $(,)?) => { $(#[test] fn $name() { materialized_matrix($k); })* };
}
materialized_tests! {
    packed_base_cpu_parity_all_cosets_k0: 0,
    packed_base_cpu_parity_all_cosets_k1: 1,
    packed_base_cpu_parity_all_cosets_k2: 2,
    packed_base_cpu_parity_all_cosets_k3: 3,
    packed_base_cpu_parity_all_cosets_k4: 4,
}

#[test]
fn cpu_baby_bear_capability_checks_transform_domain_and_context_separately() {
    let columns = BaseColumns {
        memory: 1,
        witness: 1,
        setup: 0,
    };
    let shape = |message, lde| {
        let cfg = ProverConfig::whir_only(
            message,
            WhirSchedule::from_legacy_arrays(lde, 16, 0, &[1, 5], &[1, 1], &[2], &[0, 0]),
            SecurityLevel::Sec100,
        );
        BaseCommitmentGeometry::from_config(&cfg, columns).unwrap()
    };
    let capacity = gpu_ntt::ntt_twiddles::OMEGA_LOG_ORDER;
    validate_baby_bear_base_geometry(&shape(24, 2), capacity);
    for (shape, capacity) in [
        (shape(12, 2), capacity),
        (shape(25, 2), capacity),
        (shape(24, 16), capacity),
        (shape(24, 2), 24),
    ] {
        let scheduled = std::cell::Cell::new(false);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            validate_baby_bear_base_geometry(&shape, capacity);
            scheduled.set(true);
        }));
        assert!(result.is_err());
        assert!(!scheduled.get());
    }
}
