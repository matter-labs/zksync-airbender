//! Packed-commitment exploration test.
//!
//! Runs the plain `basic_fibonacci` program (reduced machine, no oracles, no
//! precompiles) and TRIES to prove one unified-circuit instance with the packed
//! commitment mode
//! [`OperationMode::SingleChunk`](crate::gkr::prover::OperationMode).
//!
//! Notes vs the full `unified_circuit.rs` flow:
//!   * precompiles are DISABLED at preprocessing — the supported-CSR set passed to
//!     `process_binary_into_separate_tables_ext` contains only the non-determinism
//!     CSR (no delegation CSRs), so no delegation family is produced;
//!   * external challenges are the hardcoded ones (no Fiat-Shamir memory transcript);
//!   * the twiddles handed to the proof function are of the UNIFIED CIRCUIT SIZE
//!     `<< pack_log2` (the packed commitment interpolates over the enlarged domain),
//!     while the setup commitment uses ordinary trace-sized twiddles.

#[cfg(test)]
use super::orchestration::common::run_vm_and_capture_with_rom;
use super::orchestration::common::{ProgramConfig, VmRunOutput};
use crate::cs::gkr_compiler::GKRCircuitArtifact;
#[cfg(test)]
use crate::definitions::FinalRegisterValue;
#[cfg(test)]
use crate::definitions::SecurityLevel;
#[cfg(test)]
use crate::gkr::prover::setup::GKRSetup;
#[cfg(test)]
use crate::gkr::prover::OperationMode;
use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use crate::gkr::witness_gen::family_circuits::{
    build_unified_table_driver_with_rom, evaluate_gkr_witness_for_executor_family,
    GKRFullWitnessTrace,
};
use crate::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;
#[cfg(test)]
use crate::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use crate::tests::gkr::bincode_serialize_to_file;
#[cfg(test)]
use crate::tests::gkr::orchestration::common::dummy_external_challenges;
use ::field::baby_bear::base::BabyBearField;
use common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
use cs::gkr_circuits::{
    process_binary_into_separate_tables_ext, ExecutorFamilyDecoderData, OpcodeFamilyDecoder,
    UnifiedReducedMachineDecoder,
};
use cs::tables::TableDriver;
#[cfg(test)]
use fft::Twiddles;
use field::PrimeField;
#[cfg(test)]
use field::Proth120;
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
#[cfg(test)]
use riscv_transpiler::vm::DelegationsAndUnifiedCounters;
use riscv_transpiler::vm::{Counters, ReplayBuffer};
use riscv_transpiler::witness::data_structs::UnifiedOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::UnifiedDestinationHolder;
use std::alloc::Global;
#[cfg(test)]
use transcript::Keccak256Transcript;
use worker::Worker;

/// `basic_fibonacci`: computes the 10th fibonacci number, uses no oracles and no
/// delegations (reduced-machine ASM), so nothing exercises a precompile CSR.
#[allow(dead_code)]
fn basic_fibonacci_config() -> ProgramConfig {
    ProgramConfig {
        binary_path: "../examples/basic_fibonacci/app.bin".to_string(),
        text_section_path: "../examples/basic_fibonacci/app.text".to_string(),
        // no non-determinism oracle reads
        non_determinism_reads: vec![],
        cycles_bound: 1 << 20,
        ram_bound_bytes: 1 << 30,
    }
}

/// `circuit_tester`: some hand crafted program for testing, uses no oracles and no
/// delegations (reduced-machine ASM), so nothing exercises a precompile CSR.
#[cfg(test)]
pub(super) fn circuit_tester_config() -> ProgramConfig {
    ProgramConfig {
        binary_path: "../examples/circuit_tester/app.bin".to_string(),
        text_section_path: "../examples/circuit_tester/app.text".to_string(),
        // no non-determinism oracle reads
        non_determinism_reads: vec![],
        cycles_bound: 1 << 20,
        ram_bound_bytes: 1 << 30,
    }
}

#[cfg(test)]
use crate::gkr::prover_config::example_configs::l1_wrap_2p21::{
    packed_prover_config, EXTERNAL_CHALLENGES_POW_BITS, TRACE_LEN_LOG2,
};
use common_constants::rom::L1_WRAP_ROM;

#[test]
#[ignore = "production-scale packed proof; run explicitly"]
fn gkr_unified_packed_commitment_basic_fibonacci() {
    gkr_unified_packed_commitment_basic_fibonacci_impl(8, false, false);
}

/// Copy of [`gkr_unified_packed_commitment_basic_fibonacci`] configured for large
/// external cloud machines: 64 worker threads and FULLY IN-MEMORY oracles — the
/// packed setup is committed in memory (`GKRSetup::commit_for_config`, no on-disk
/// cache) and the memory/witness base + intermediate WHIR oracles are fully
/// materialized (`WhirOracleStorage::fully_in_memory()`). The proof must be
/// byte-identical to the recompute-based run; this variant does not (re)write the
/// canonical EVM proof fixtures.
#[test]
#[ignore = "cloud-machine scale: 64 cores + enough RAM to materialize the 2^31 packed RS codewords"]
fn gkr_unified_packed_commitment_basic_fibonacci_64core_in_memory() {
    // BENCH_THREADS overrides the worker width for machines that are not
    // 64-core (e.g. the 88-core benchmark VM). SETUP_ON_DISK=1 keeps the
    // mem/witness base + intermediate oracles fully in memory while serving
    // the setup commitment from disk.
    let threads = std::env::var("BENCH_THREADS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(64);
    let setup_in_memory = std::env::var("SETUP_ON_DISK").map_or(true, |v| v != "1");
    gkr_unified_packed_commitment_basic_fibonacci_impl(threads, true, setup_in_memory);
}

/// Shared body of the packed unified fibonacci proving tests. `fully_in_memory`
/// selects the oracle storage: `false` = the historical memory-light configuration
/// (coset-recompute base/intermediate oracles + on-disk cached setup),
/// `true` = everything materialized in RAM (in-memory packed setup and oracles).
#[cfg(test)]
fn gkr_unified_packed_commitment_basic_fibonacci_impl(
    num_threads: usize,
    fully_in_memory: bool,
    setup_in_memory: bool,
) {
    let worker = Worker::new_with_num_threads(num_threads);
    let level = SecurityLevel::Sec100;
    let external_challenges_pow_bits = EXTERNAL_CHALLENGES_POW_BITS;

    // 1. Run the plain program (reduced machine, no precompiles).
    // let config = basic_fibonacci_config();
    let config = circuit_tester_config();
    let vm = run_vm_and_capture_with_rom::<
        DelegationsAndUnifiedCounters,
        ReducedMachineDecoderConfig,
        { L1_WRAP_ROM.second_word_bits() },
    >(&config, &worker);
    println!("Finished at PC = 0x{:08x}", vm.final_pc());

    // 2. Load the unified reduced-machine circuit.
    let unified_circuit: GKRCircuitArtifact<Proth120> = {
        let src = std::fs::File::open(
            "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120_2p21.json",
        )
        .expect("unified circuit layout");
        serde_json::from_reader(src).expect("deserialize unified circuit")
    };
    let num_teardown_sets = unified_circuit.memory_layout.teardown_sets.len();
    let num_calls = vm
        .counters
        .get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>();
    // The complete config owns the trace, packed message and WHIR schedules.
    let prover_config = packed_prover_config(level);
    assert_eq!(prover_config.trace_len_log2, TRACE_LEN_LOG2);
    let trace_len: usize = 1 << prover_config.trace_len_log2;
    let pack_log2 = prover_config.pack_log2;
    assert!(num_calls <= trace_len);

    // 3. Build the unified witness trace with precompiles disabled at preprocessing.
    let (full_trace, table_driver, decoder_table, top_bits) =
        build_unified_trace_without_precompiles(
            &vm,
            super::unified_reduced_machine_proth120::witness_eval_fn,
            &unified_circuit,
            num_teardown_sets,
            trace_len,
            &worker,
        );

    // ── DIAGNOSTIC: witness-level permutation self-check (family_circuits.rs style) ──
    // Extract the state (PC/ts) and shuffle-RAM permutation sets straight from the built
    // witness + the register/PC boundary, and check they reduce to identity. If they do,
    // the witness is consistent and any prover self-check divergence is in the accumulator
    // arithmetic, not the trace itself.
    {
        use crate::gkr::witness_gen::family_circuits::GKRMemoryOnlyWitnessTrace;
        use common_constants::{TimestampScalar, INITIAL_PC};
        use cs::definitions::INITIAL_TIMESTAMP;
        use std::collections::BTreeSet;

        let memory_trace = GKRMemoryOnlyWitnessTrace {
            column_major_trace: full_trace.column_major_memory_trace.clone(),
        };
        let register_final_state = vm.register_final_state();
        let final_pc = vm.final_pc();
        let final_timestamp = vm.final_timestamp();
        let flattened_inits_and_teardowns: Vec<_> = vm
            .shuffle_ram_touched_addresses
            .iter()
            .flatten()
            .cloned()
            .collect();

        let mut write_set = BTreeSet::<(u32, TimestampScalar)>::new();
        let mut read_set = BTreeSet::<(u32, TimestampScalar)>::new();
        write_set.insert((INITIAL_PC, INITIAL_TIMESTAMP));
        read_set.insert((final_pc, final_timestamp));

        let mut memory_write_set = BTreeSet::<(bool, u32, TimestampScalar, u32)>::new();
        let mut memory_read_set = BTreeSet::<(bool, u32, TimestampScalar, u32)>::new();
        let mut delegation_write_set = BTreeSet::<(bool, u32, TimestampScalar)>::new();
        for i in 0..32 {
            memory_write_set.insert((true, i as u32, 0, 0));
            memory_read_set.insert((
                true,
                i as u32,
                register_final_state[i].last_access_timestamp,
                register_final_state[i].current_value,
            ));
        }

        super::parse_state_permutation_elements_from_full_trace(
            &unified_circuit,
            &memory_trace,
            &mut write_set,
            &mut read_set,
        );
        super::parse_shuffle_ram_accesses_from_full_trace(
            &unified_circuit,
            &memory_trace,
            &mut memory_write_set,
            &mut memory_read_set,
            &mut delegation_write_set,
        );

        let state_ok = write_set == read_set;
        let init_diff: Vec<_> = memory_read_set
            .difference(&memory_write_set)
            .cloned()
            .collect();
        let teardown_diff: Vec<_> = memory_write_set
            .difference(&memory_read_set)
            .cloned()
            .collect();
        let mem_init_ok = init_diff
            .iter()
            .all(|(is_reg, _, ts, val)| !*is_reg && *ts == 0 && *val == 0);
        println!(
            "[witness-check] STATE write==read: {state_ok}   |w|={} |r|={}",
            write_set.len(),
            read_set.len()
        );
        println!(
            "[witness-check] MEMORY init_diff={} teardown_diff={} flattened_it={}  inits_all(mem,ts=0,val=0)={mem_init_ok}",
            init_diff.len(),
            teardown_diff.len(),
            flattened_inits_and_teardowns.len()
        );
        println!(
            "[witness-check] DELEGATION write_set len={}",
            delegation_write_set.len()
        );
        if !state_ok {
            let w_only: Vec<_> = write_set.difference(&read_set).take(8).cloned().collect();
            let r_only: Vec<_> = read_set.difference(&write_set).take(8).cloned().collect();
            println!("[witness-check] STATE write-only (first 8): {:?}", w_only);
            println!("[witness-check] STATE read-only  (first 8): {:?}", r_only);
        }
        if teardown_diff.len() <= 8 {
            println!("[witness-check] MEMORY teardown_diff: {:?}", teardown_diff);
        }
        assert!(state_ok, "witness state permutation is NOT identity");
        assert_eq!(
            init_diff.len(),
            teardown_diff.len(),
            "witness memory permutation unbalanced"
        );
        assert!(
            mem_init_ok,
            "witness memory inits are not (mem, ts=0, val=0)"
        );
        println!("[witness-check] witness permutation is IDENTITY — proceeding to prove");
    }

    println!("Preparing data for proving");
    // 4. The complete 2^21 wrap config supplies the packed message and WHIR schedule.

    println!("Computing setup");
    // The proof function's twiddles are of unified circuit size * (1 << pack_log2):
    // the packed commitment interpolates the merged/packed polynomials over the
    // enlarged domain.
    let packed_twiddles: Twiddles<Proth120, Global> =
        Twiddles::new(1usize << prover_config.whir_message_size_log2(), &worker);

    // 5. Construct the setup and obtain an ON-DISK commitment for it: the packed
    //    RS codewords + Merkle tree are computed once via `commit_for_config` and cached
    //    on disk; this and subsequent runs read them back lazily through
    //    `SetupCommitment::OnDisk` (so the setup never has to sit in RAM while
    //    proving). Delete the `*.rscw`/`*.tree` cache files to force a recompute.
    use crate::gkr::prover::{
        prove_configured_with_gkr_with_storage_and_backend, Proth120WorkStealingLazyBackend,
        SetupCommitment, WhirOracleStorage,
    };
    use crate::gkr::whir::coset_commit::serialize_packed_base_commitment_split_to_disk;
    use crate::gkr::whir::rs_on_disk::{coset_file_path, OnDiskRsCodewords};
    use crate::merkle_trees::on_disk::{top_tree_file_path, OnDiskTreeLayout};
    use crate::merkle_trees::{ColumnMajorMerkleTreeConstructor, RSQueryable};

    let setup = GKRSetup::construct(&table_driver, &decoder_table, trace_len, &unified_circuit);

    let lde_factor = prover_config.lde_factor;
    let values_per_leaf = prover_config.base_oracles_values_per_leaf;

    let setup_commitment = if setup_in_memory {
        // Commit the packed setup fully in memory: RS codewords + monolithic Merkle
        // tree materialized (byte-identical commitment to the on-disk/split path).
        println!("Committing setup in memory (packed)");
        setup.commit_for_config::<Keccak256MerkleTreeWithCap>(
            &packed_twiddles,
            &prover_config,
            &worker,
        )
    } else {
        // On-disk setup with the "second" (per-coset subtree) tree layout: the packed
        // setup is prepared coset-by-coset — each coset's RS codewords and its cap-size-1
        // subtree are streamed to disk, then a small top-tree over the subtree roots — so
        // the ~2^31 codeword and its tree never have to be materialized whole. This and
        // later runs read them back lazily via mmap. Delete the cache files to recompute.
        let setup_disk_prefix = format!(
            "test_proofs/unified_setup_proth120_2p21_pack{pack_log2}_lde{}_vpl{}_ondisk",
            lde_factor.trailing_zeros(),
            values_per_leaf.trailing_zeros()
        );
        let setup_disk_prefix = setup_disk_prefix.as_str();
        let setup_coset_paths: Vec<_> = (0..lde_factor)
            .map(|i| coset_file_path(setup_disk_prefix, i))
            .collect();
        let setup_on_disk_present = top_tree_file_path(setup_disk_prefix).exists()
            && setup_coset_paths.iter().all(|p| p.exists());

        if !setup_on_disk_present {
            println!(
                "On-disk setup not present; preparing coset-by-coset (split tree) and caching"
            );
            let inputs: Vec<&[Proth120]> = setup.hypercube_evals.iter().map(|el| &el[..]).collect();
            serialize_packed_base_commitment_split_to_disk::<Proth120, Keccak256MerkleTreeWithCap>(
                &inputs,
                &packed_twiddles,
                lde_factor,
                values_per_leaf.trailing_zeros() as usize,
                prover_config.cap_size,
                prover_config.trace_len_log2,
                pack_log2,
                setup_disk_prefix,
                &worker,
            )
            .expect("cache split setup to disk");
        } else {
            println!("Reusing cached on-disk setup at prefix {setup_disk_prefix}");
        }

        // Open the on-disk setup: RS codewords + the split (per-coset subtree) tree, all
        // memory-mapped and read lazily.
        let setup_rs =
            OnDiskRsCodewords::<Proth120>::open(setup_coset_paths).expect("open on-disk setup RS");
        let setup_coset_size_log2 = RSQueryable::coset_size_log2(&setup_rs);
        let setup_disk_tree = <Keccak256MerkleTreeWithCap as ColumnMajorMerkleTreeConstructor<
            Proth120,
        >>::open_disk_artifacts(
            setup_disk_prefix,
            OnDiskTreeLayout::CosetSubtrees,
            lde_factor,
        );

        SetupCommitment::OnDisk {
            rs: Box::new(setup_rs),
            tree: setup_disk_tree,
            values_per_leaf,
            coset_size_log2: setup_coset_size_log2,
        }
    };

    // 6. Prove one unified circuit instance with the packed commitment mode.
    let external_challenges = dummy_external_challenges::<Proth120, Proth120>();

    let operation_mode = OperationMode::SingleChunk {
        external_challenges_pow_bits,
        final_pc: vm.final_pc(),
        final_timestamp: vm.final_timestamp(),
        register_final_state: vm.register_final_state().map(|el| FinalRegisterValue {
            value: el.current_value,
            last_access_timestamp: el.last_access_timestamp,
        }),
    };

    let storage = if fully_in_memory {
        WhirOracleStorage::fully_in_memory()
    } else {
        WhirOracleStorage::fully_recompute()
    };

    println!("Trying to prove (unified, packed commitment, pack_log2 = {pack_log2})");
    println!(
        "  memory/witness RS codewords: {}; setup: {}",
        if fully_in_memory {
            "InMemory"
        } else {
            "Recompute"
        },
        if setup_in_memory {
            "in-memory"
        } else {
            "on-disk"
        },
    );
    let now = std::time::Instant::now();
    // This test is concretely Proth120, so it opts into the Proth120-only
    // lazy-reduction work-stealing backend (byte-identical proofs, faster LDEs).
    let _proof = prove_configured_with_gkr_with_storage_and_backend::<
        Proth120,
        Proth120,
        Keccak256MerkleTreeWithCap,
        Keccak256Transcript,
        _,
        _,
    >(
        &unified_circuit,
        &external_challenges,
        full_trace,
        &setup,
        &setup_commitment,
        &packed_twiddles,
        &prover_config,
        operation_mode,
        storage,
        top_bits,
        trace_len,
        &Proth120WorkStealingLazyBackend,
        &crate::gkr::prover::NaiveGKRBackend,
        &worker,
    );
    println!("Packed unified proving time is {:?}", now.elapsed());
}

/// Per-layer relation-type histogram for the standard (circuit) GKR layers, to scope
/// the Solidity per-gate code-generation for STEP 3.
#[test]
fn inspect_circuit_layer_relations() {
    let unified_circuit: GKRCircuitArtifact<Proth120> = serde_json::from_reader(
        std::fs::File::open(
            "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120_2p21.json",
        )
        .unwrap(),
    )
    .unwrap();
    println!(
        "[relations] {} standard layers",
        unified_circuit.layers.len()
    );
    for (li, layer) in unified_circuit.layers.iter().enumerate() {
        let gates: Vec<_> = layer
            .gates
            .iter()
            .chain(layer.gates_with_external_connections.iter())
            .collect();
        let mut hist: std::collections::BTreeMap<String, usize> = Default::default();
        for g in &gates {
            let dbg = format!("{:?}", g.enforced_relation);
            let name = dbg
                .split([' ', '{', '('])
                .next()
                .unwrap_or(&dbg)
                .to_string();
            *hist.entry(name).or_default() += 1;
        }
        println!(
            "  layer {li}: {} gates ({} plain + {} external), {} cached relations",
            gates.len(),
            layer.gates.len(),
            layer.gates_with_external_connections.len(),
            layer.cached_relations.len(),
        );
        for (name, n) in &hist {
            println!("      {n:>4}  {name}");
        }
    }
}

/// Inlined analogue of `orchestration::unified::build_unified_full_trace`, but with
/// the delegation CSRs removed from the preprocessing supported-CSR set (precompiles
/// disabled at preprocessing) and without the optional memory-consistency cross-check.
pub fn build_unified_trace_without_precompiles<C, F: PrimeField>(
    vm: &VmRunOutput<C, { L1_WRAP_ROM.second_word_bits() }>,
    witness_eval_fn_ptr: fn(&mut ColumnMajorWitnessProxy<'_, UnifiedRiscvCircuitOracle<'_>, F>),
    unified_circuit: &GKRCircuitArtifact<F>,
    num_teardown_sets: usize,
    cycles_per_chunks: usize,
    worker: &Worker,
) -> (
    GKRFullWitnessTrace<F, Global, Global>,
    TableDriver<F>,
    Vec<Option<ExecutorFamilyDecoderData>>,
    Vec<u32>,
)
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    let num_calls = vm
        .counters
        .get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>();
    println!("Replaying {} cycles for witness data", num_calls);
    // Replay the captured trace into the unified destination holder.
    let mut state = vm.snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = vm
        .snapshotter
        .reads_buffer
        .make_range(0..vm.snapshotter.reads_buffer.len());
    let mut replay_ram = ReplayerRam::<{ L1_WRAP_ROM.second_word_bits() }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![UnifiedOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = [&mut buffer[..]];
    let mut tracer = UnifiedDestinationHolder {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<C>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut replay_ram,
        &vm.tape,
        &mut (),
        vm.cycles_bound,
        &mut tracer,
    );
    assert_eq!(vm.expected_final_state(), state);

    // Preprocessing WITHOUT any delegation CSRs => no precompiles.
    println!("Creating decoder table");
    let decoders: Vec<Box<dyn OpcodeFamilyDecoder>> = vec![Box::new(UnifiedReducedMachineDecoder)];
    const SUPPORTED_CSRS: &[u16] = &[common_constants::NON_DETERMINISM_CSR as u16];
    let mut preprocessing_data = process_binary_into_separate_tables_ext::<
        BabyBearField,
        ReducedMachineDecoderConfig,
        true,
        Global,
    >(
        &vm.text_section,
        &decoders,
        L1_WRAP_ROM.word_size(),
        SUPPORTED_CSRS,
    );
    let decoder_table = preprocessing_data
        .remove(&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX)
        .expect("UnifiedReducedMachineDecoder must produce a family-128 entry");

    bincode_serialize_to_file(&buffer, "unified_proth120_witness.bin");

    let oracle = UnifiedRiscvCircuitOracle {
        inner: &buffer,
        decoder_table: &decoder_table,
    };
    let unified_table_driver =
        build_unified_table_driver_with_rom::<F, { L1_WRAP_ROM.second_word_bits() }>(&vm.binary);

    println!("Collecting inits and teardowns");

    // // Inits/teardown columns sized to the unified circuit's set count.
    // let mut inits_and_teardowns = Vec::with_capacity(num_teardown_sets);
    // for _ in 0..num_teardown_sets {
    //     let a = Vec::with_capacity(1 << TRACE_LEN_LOG2);
    //     let b = Vec::with_capacity(1 << TRACE_LEN_LOG2);
    //     let c = Vec::with_capacity(1 << TRACE_LEN_LOG2);
    //     let d = Vec::with_capacity(1 << TRACE_LEN_LOG2);
    //     inits_and_teardowns.push(([a, b], [c, d]));
    // }
    // vm.ram.collect_inits_and_teardowns_into_columns::<F, _>(
    //     worker,
    //     TRACE_LEN_LOG2,
    //     0,
    //     &mut inits_and_teardowns,
    // );

    // we should collect carefully here, as regions will not be continuous
    let max_ram_touch = vm
        .shuffle_ram_touched_addresses
        .iter()
        .map(|el| el.iter().map(|el| el.0).max().unwrap_or(0))
        .max()
        .expect("max address touched");
    assert_eq!(max_ram_touch % 4, 0);
    let mut inits_and_teardowns = vm.ram.collect_inits_and_teardowns_sets::<F, Global>(
        worker,
        cycles_per_chunks.trailing_zeros() as usize,
        num_teardown_sets,
        Some(((max_ram_touch as usize) + 4) / 4),
    );
    assert_eq!(inits_and_teardowns.len(), 1);
    let (top_bits, inits_and_teardowns_chunks) = inits_and_teardowns
        .drain(..1)
        .next()
        .expect("inits and teardowns");
    assert_eq!(top_bits.len(), num_teardown_sets);

    println!("Calculating full witness trace");

    let full_trace = evaluate_gkr_witness_for_executor_family::<F, _, _, _>(
        unified_circuit,
        witness_eval_fn_ptr,
        cycles_per_chunks,
        &oracle,
        &unified_table_driver,
        worker,
        Some(inits_and_teardowns_chunks),
        Global,
        Global,
    );

    (full_trace, unified_table_driver, decoder_table, top_bits)
}
