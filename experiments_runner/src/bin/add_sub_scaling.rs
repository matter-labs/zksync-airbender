//! Add/sub family proof THREAD-SCALING + memory-bandwidth experiment.
//!
//! Same setup as `tests/add_sub_family.rs` (keccak-f1600 program, prove ONLY
//! the add/sub family circuit at Sec100, 2^24 trace), but the proof is run
//! once per requested worker size, with the trace build and the prove call
//! timed separately (`[scaling] ...` lines); the prover's own `[timing]`
//! prints give the per-stage breakdown (setup commit, base LDE/tree, GKR
//! forward layers, sumcheck loops, WHIR rounds). Before each proof a STREAM-
//! style probe (read / copy / triad over 1 GiB u64 arrays) measures the
//! bandwidth the same worker can pull, so per-stage traffic estimates can be
//! compared against a measured ceiling.
//!
//! Usage: `add_sub_scaling --circuit <layout json> [--threads 4,8,16,32,48,64,96]
//! [--skip-bw] [--bw-only] [--outer N --inner K]` (trace length is the
//! layout's fixed 2^24)
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]

use common_constants::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;
use cs::definitions::{
    BIGINT_OPS_WITH_CONTROL_CSR_REGISTER, BLAKE2S_DELEGATION_CSR_REGISTER,
    BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER, KECCAK_SPECIAL5_CSR_REGISTER, NON_DETERMINISM_CSR,
};
use cs::gkr_circuits::opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization;
use cs::gkr_circuits::process_binary_into_separate_tables_ext;
use cs::gkr_circuits::ExecutorFamilyDecoderData;
use cs::gkr_compiler::GKRCircuitArtifact;
use cs::tables::TableDriver;
use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use prover::definitions::SecurityLevel;
use prover::gkr::prover::GKRExternalChallenges;
use prover::gkr::prover::{DefaultBabyBearGKRBackend, GKRBackend, NaiveGKRBackend};
use prover::gkr::prover_config::{example_configs, ProverConfig};
use prover::gkr::witness_gen::family_circuits::GKRFullWitnessTrace;
use prover::tests::gkr::add_sub_lui_auipc_mop;
use prover::tests::gkr::orchestration::common::{
    hardcoded_external_challenges, run_vm_and_capture, ProgramConfig,
};
use prover::tests::gkr::orchestration::delegations::{deserialize_from_file, serialize_to_file};
use prover::tests::gkr::orchestration::per_family::{
    build_nonmem_family_full_trace, prove_built_family_trace_with_prover_config_and_gkr_backend,
};
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
use riscv_transpiler::vm::{Counters, DelegationsAndFamiliesCounters};
use std::alloc::Global;
use worker::Worker;

const CIRCUIT_TYPE: u8 = ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;

/// FNV-1a 64 over a file's bytes: a stable equality digest for proof files.
fn file_digest(path: &str) -> u64 {
    let bytes = std::fs::read(path).expect("proof file");
    let mut h: u64 = 0xcbf29ce484222325;
    for b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

/// Prove the built trace on the requested GKR backend (the default = the
/// arch-specialized one when the build enables it, or the portable naive one).
#[allow(clippy::too_many_arguments)]
fn prove_with_gkr_backend(
    naive_gkr: bool,
    circuit: &GKRCircuitArtifact<BabyBearField>,
    table_driver: &TableDriver<BabyBearField>,
    decoder_table_data: &[Option<ExecutorFamilyDecoderData>],
    full_trace: GKRFullWitnessTrace<BabyBearField, Global, Global>,
    trace_len: usize,
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    prover_config: &ProverConfig,
    worker: &Worker,
) -> prover::gkr::prover::GKRProof<
    BabyBearField,
    BabyBearExt4,
    prover::merkle_trees::DefaultTreeConstructor,
> {
    if naive_gkr {
        prove_built_family_trace_with_prover_config_and_gkr_backend(
            circuit,
            table_driver,
            decoder_table_data,
            full_trace,
            trace_len,
            external_challenges,
            prover_config,
            &NaiveGKRBackend,
            worker,
        )
    } else {
        prove_built_family_trace_with_prover_config_and_gkr_backend(
            circuit,
            table_driver,
            decoder_table_data,
            full_trace,
            trace_len,
            external_challenges,
            prover_config,
            &DefaultBabyBearGKRBackend::default(),
            worker,
        )
    }
}

/// Object-safe dispatch over the two GKR backends for the outer test (the
/// prove entry is generic over the backend; each backend gets its own
/// monomorphization behind this trait).
trait GkrDispatch: Sync {
    #[allow(clippy::too_many_arguments)]
    fn prove(
        &self,
        circuit: &GKRCircuitArtifact<BabyBearField>,
        external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
        trace: GKRFullWitnessTrace<BabyBearField, Global, Global>,
        setup: &prover::gkr::prover::setup::GKRSetup<BabyBearField>,
        setup_commitment: &prover::gkr::prover::SetupCommitment<
            BabyBearField,
            prover::merkle_trees::DefaultTreeConstructor,
        >,
        twiddles: &<prover::gkr::prover::DefaultBabyBearBackend as prover::gkr::prover::Backend<
            BabyBearField,
            BabyBearExt4,
        >>::TwiddleSet,
        prover_config: &ProverConfig,
        storage: prover::gkr::prover::WhirOracleStorage,
        trace_len: usize,
        backend: &prover::gkr::prover::DefaultBabyBearBackend,
        worker: &Worker,
    ) -> prover::gkr::prover::GKRProof<
        BabyBearField,
        BabyBearExt4,
        prover::merkle_trees::DefaultTreeConstructor,
    >;
}

impl<GB: GKRBackend<BabyBearField, BabyBearExt4>> GkrDispatch for GB {
    fn prove(
        &self,
        circuit: &GKRCircuitArtifact<BabyBearField>,
        external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
        trace: GKRFullWitnessTrace<BabyBearField, Global, Global>,
        setup: &prover::gkr::prover::setup::GKRSetup<BabyBearField>,
        setup_commitment: &prover::gkr::prover::SetupCommitment<
            BabyBearField,
            prover::merkle_trees::DefaultTreeConstructor,
        >,
        twiddles: &<prover::gkr::prover::DefaultBabyBearBackend as prover::gkr::prover::Backend<
            BabyBearField,
            BabyBearExt4,
        >>::TwiddleSet,
        prover_config: &ProverConfig,
        storage: prover::gkr::prover::WhirOracleStorage,
        trace_len: usize,
        backend: &prover::gkr::prover::DefaultBabyBearBackend,
        worker: &Worker,
    ) -> prover::gkr::prover::GKRProof<
        BabyBearField,
        BabyBearExt4,
        prover::merkle_trees::DefaultTreeConstructor,
    > {
        use prover::gkr::prover::{
            prove_configured_with_gkr_with_storage_and_backend, CommitmentMode,
        };
        use prover::merkle_trees::DefaultTreeConstructor;
        use prover::transcript::Blake2sTranscript;
        prove_configured_with_gkr_with_storage_and_backend::<
            BabyBearField,
            BabyBearExt4,
            DefaultTreeConstructor,
            Blake2sTranscript,
            _,
            _,
        >(
            circuit,
            external_challenges,
            trace,
            setup,
            setup_commitment,
            twiddles,
            prover_config,
            CommitmentMode::SeparateMemoryAndWitness,
            storage,
            Vec::new(),
            trace_len,
            backend,
            self,
            worker,
        )
    }
}

/// OUTER-parallelism test: the setup (twiddles + setup construct + commit) is
/// computed ONCE and shared, then `outer` provers of the same trace run
/// concurrently, each on its own `inner`-thread worker, all with
/// `WhirOracleStorage::fully_in_memory_continuous()`. A solo `inner`-thread
/// prover runs first as the no-contention baseline.
#[allow(clippy::too_many_arguments)]
fn outer_parallel(
    outer: usize,
    inner: usize,
    naive_gkr: bool,
    pin: bool,
    circuit: &GKRCircuitArtifact<BabyBearField>,
    table_driver: &TableDriver<BabyBearField>,
    decoder_table_data: &[Option<ExecutorFamilyDecoderData>],
    trace: GKRFullWitnessTrace<BabyBearField, Global, Global>,
    trace_len: usize,
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    prover_config: &ProverConfig,
    setup_worker: &Worker,
) {
    use prover::gkr::prover::setup::GKRSetup;
    use prover::gkr::prover::{Backend, DefaultBabyBearBackend, TwiddleSetOps, WhirOracleStorage};

    let backend = DefaultBabyBearBackend::default();
    let t = std::time::Instant::now();
    let twiddles = <DefaultBabyBearBackend as Backend<BabyBearField, BabyBearExt4>>::make_twiddles(
        &backend,
        trace_len,
        setup_worker,
    );
    let setup = GKRSetup::construct(table_driver, decoder_table_data, trace_len, circuit);
    let setup_commitment = setup.commit(
        twiddles.plain(),
        prover_config.lde_factor,
        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
        prover_config.cap_size,
        trace_len.trailing_zeros() as usize,
        setup_worker,
    );
    println!(
        "[outer] shared setup (twiddles + setup construct + commit) took {:.3?}",
        t.elapsed()
    );

    let storage = WhirOracleStorage::fully_in_memory_continuous();
    let run_one = |label: String,
                   worker: &Worker,
                   trace: GKRFullWitnessTrace<BabyBearField, Global, Global>|
     -> f64 {
        let t = std::time::Instant::now();
        let go = |gb: &dyn GkrDispatch| {
            gb.prove(
                circuit,
                external_challenges,
                trace,
                &setup,
                &setup_commitment,
                &twiddles,
                prover_config,
                storage,
                trace_len,
                &backend,
                worker,
            )
        };
        let proof = if naive_gkr {
            go(&NaiveGKRBackend)
        } else {
            go(&DefaultBabyBearGKRBackend::default())
        };
        let el = t.elapsed().as_secs_f64();
        println!(
            "[outer] {label}: prove {el:.3} s (grand product {:?})",
            proof.grand_product_accumulator_computed
        );
        el
    };

    // Pool threads carry the prover's recursion-heavy serial phases now, so
    // give them a generous stack (virtual; committed lazily).
    const POOL_STACK: usize = 256 << 20;

    // No-contention baseline: ONE prover on `inner` threads, driven from
    // INSIDE its pool (the driving thread is a pool thread; every `scope`
    // body — including `smart_spawn`'s inline last chunk — runs on pool
    // threads only).
    let solo = {
        let worker = Worker::new_with_num_threads_and_stack(inner, POOL_STACK);
        let tr = trace.clone();
        worker
            .pool
            .install(|| run_one("solo baseline".to_string(), &worker, tr))
    };

    // Pinning plan: prover i owns the consecutive CPU block
    // `[i*inner, (i+1)*inner)` of the host's complexes flattened in L3-domain
    // order — whole complexes when `inner` is a multiple of the complex size.
    let cpu_blocks: Vec<Vec<usize>> = if pin {
        let complexes = Worker::cpu_complexes();
        let flat: Vec<usize> = if complexes.is_empty() {
            println!("[outer] WARNING: no L3 topology available; pinning to CPU ids in order");
            (0..std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(1))
                .collect()
        } else {
            println!(
                "[outer] host L3 complexes: {} x {} CPUs (first: {:?})",
                complexes.len(),
                complexes[0].len(),
                &complexes[0]
            );
            complexes.iter().flatten().copied().collect()
        };
        assert!(
            outer * inner <= flat.len(),
            "pinning {outer} x {inner} threads needs {} CPUs, host lists {}",
            outer * inner,
            flat.len()
        );
        (0..outer)
            .map(|i| flat[i * inner..(i + 1) * inner].to_vec())
            .collect()
    } else {
        Vec::new()
    };
    if pin {
        println!("[outer] pinned: prover 0 -> cpus {:?}", cpu_blocks[0]);
    }

    // `outer` provers at once, each on its own `inner`-thread worker.
    let traces: Vec<_> = (0..outer).map(|_| trace.clone()).collect();
    drop(trace);
    let cpu_blocks = &cpu_blocks;
    let t_all = std::time::Instant::now();
    let times: Vec<f64> = std::thread::scope(|s| {
        let handles: Vec<_> = traces
            .into_iter()
            .enumerate()
            .map(|(i, tr)| {
                let run_one = &run_one;
                std::thread::Builder::new()
                    .name(format!("prover-{i}"))
                    .stack_size(1 << 30)
                    .spawn_scoped(s, move || {
                        // create the (optionally pinned) worker first, then
                        // run the whole proof inside its pool
                        let worker = if pin {
                            Worker::new_with_num_threads_on_cpus_and_stack(
                                inner,
                                &cpu_blocks[i],
                                POOL_STACK,
                            )
                        } else {
                            Worker::new_with_num_threads_and_stack(inner, POOL_STACK)
                        };
                        worker
                            .pool
                            .install(|| run_one(format!("prover {i}"), &worker, tr))
                    })
                    .unwrap()
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let wall = t_all.elapsed().as_secs_f64();
    let min = times.iter().cloned().fold(f64::MAX, f64::min);
    let max = times.iter().cloned().fold(0.0, f64::max);
    let mean = times.iter().sum::<f64>() / times.len() as f64;
    println!(
        "[outer] SUMMARY{} (in-pool drivers): {outer} x {inner}-thread provers: wall {wall:.3} s; per-prover min {min:.3} / mean {mean:.3} / max {max:.3} s; \
         solo {inner}-thread prover {solo:.3} s; mean slowdown {:.2}x; throughput {:.3} proofs/s vs solo {:.3} proofs/s ({:.2}x)",
        if pin { " (pinned)" } else { "" },
        mean / solo,
        outer as f64 / wall,
        1.0 / solo,
        (outer as f64 / wall) * solo,
    );
}

/// STREAM-style probe on the worker's pool: best-of-3 GB/s for a pure read
/// (sum), a copy, and a triad over `len` u64 elements per array.
fn bandwidth_probe(worker: &Worker, len: usize) {
    use worker::rayon::prelude::*;

    let chunk = (len / (worker.num_cores * 8)).max(1 << 12);
    let mut a = vec![0u64; len];
    let mut b: Vec<u64> = (0..len as u64)
        .map(|i| i.wrapping_mul(0x9E37_79B9))
        .collect();
    let c: Vec<u64> = (0..len as u64).map(|i| i ^ 0x5555_5555).collect();
    // first-touch a in parallel so the timed passes see resident pages
    worker.pool.install(|| {
        a.par_chunks_mut(chunk)
            .enumerate()
            .for_each(|(i, ch)| ch.iter_mut().for_each(|x| *x = i as u64))
    });
    let bytes = (len * 8) as f64;

    let mut best_read = f64::MAX;
    let mut best_copy = f64::MAX;
    let mut best_triad = f64::MAX;
    let mut sink = 0u64;
    for _ in 0..3 {
        let t = std::time::Instant::now();
        let s: u64 = worker.pool.install(|| {
            b.par_chunks(chunk)
                .map(|ch| ch.iter().fold(0u64, |acc, &x| acc.wrapping_add(x)))
                .reduce(|| 0u64, |x, y| x.wrapping_add(y))
        });
        best_read = best_read.min(t.elapsed().as_secs_f64());
        sink = sink.wrapping_add(s);

        let t = std::time::Instant::now();
        worker.pool.install(|| {
            a.par_chunks_mut(chunk)
                .zip(b.par_chunks(chunk))
                .for_each(|(d, s)| d.copy_from_slice(s))
        });
        best_copy = best_copy.min(t.elapsed().as_secs_f64());

        let t = std::time::Instant::now();
        worker.pool.install(|| {
            a.par_chunks_mut(chunk)
                .zip(b.par_chunks(chunk))
                .zip(c.par_chunks(chunk))
                .for_each(|((d, s1), s2)| {
                    for ((x, &y), &z) in d.iter_mut().zip(s1.iter()).zip(s2.iter()) {
                        *x = y.wrapping_add(z.wrapping_mul(3));
                    }
                })
        });
        best_triad = best_triad.min(t.elapsed().as_secs_f64());
        // keep the compiler honest about `a`
        b[0] = b[0].wrapping_add(a[len - 1] & 1);
    }
    println!(
        "[bandwidth] threads={} read={:.1} GB/s copy={:.1} GB/s triad={:.1} GB/s (1 GiB arrays, best of 3; sink {sink})",
        worker.num_cores,
        bytes / best_read / 1e9,
        2.0 * bytes / best_copy / 1e9,
        3.0 * bytes / best_triad / 1e9,
    );
}

fn main() {
    let mut threads: Vec<usize> = vec![4, 8, 16, 32, 48, 64, 96];
    let mut circuit_path: Option<String> = None;
    let mut skip_bw = false;
    let mut bw_only = false;
    let mut outer = 0usize;
    let mut inner = 4usize;
    let mut naive_gkr = false;
    let mut pin = false;
    let mut proof_out: Option<String> = None;
    let trace_len_log2 = 24usize;

    let mut it = std::env::args().skip(1);
    while let Some(arg) = it.next() {
        let mut value =
            |name: &str| -> String { it.next().unwrap_or_else(|| panic!("{name} needs a value")) };
        match arg.as_str() {
            "--threads" => {
                threads = value("--threads")
                    .split(',')
                    .map(|s| s.trim().parse().expect("--threads"))
                    .collect()
            }
            "--circuit" => circuit_path = Some(value("--circuit")),
            "--skip-bw" => skip_bw = true,
            "--bw-only" => bw_only = true,
            "--outer" => outer = value("--outer").parse().expect("--outer"),
            "--gkr-backend" => {
                naive_gkr = match value("--gkr-backend").as_str() {
                    "naive" => true,
                    "default" => false,
                    other => panic!("unknown gkr backend `{other}` (naive|default)"),
                }
            }
            "--proof-out" => proof_out = Some(value("--proof-out")),
            "--pin" => pin = true,
            "--inner" => inner = value("--inner").parse().expect("--inner"),
            other => panic!("unknown argument `{other}`"),
        }
    }

    if bw_only {
        for &n in &threads {
            let worker = Worker::new_with_num_threads(n);
            bandwidth_probe(&worker, 1 << 27);
        }
        return;
    }

    let circuit_path = circuit_path.expect("--circuit <add_sub layout json> is required");
    let level = SecurityLevel::Sec100;
    let trace_len: usize = 1 << trace_len_log2;
    let num_cycles_per_chunk: usize = trace_len;
    let prover_config = example_configs::config_for_security_level_under_pessimistic_conjecture(
        trace_len_log2,
        level,
    );

    let circuit: GKRCircuitArtifact<BabyBearField> = deserialize_from_file(&circuit_path);
    assert_eq!(
        circuit.trace_len, trace_len,
        "the family layout is compiled for a fixed trace length; trace-size changes are not allowed"
    );
    let widths: Vec<String> = circuit
        .layers
        .iter()
        .map(|l| match l.intermediate_layer_width {
            Some(w) => w.to_string(),
            None => "base".to_string(),
        })
        .collect();
    println!(
        "[shape] trace_len 2^{trace_len_log2}, memory cols {}, witness cols {}, layers {} (widths: {}), \
         lde_factor {}, cap {}, base vpl {}, whir steps {:?}, queries {:?}, lde factors {:?}, pow {:?}",
        circuit.memory_layout.total_width,
        circuit.witness_layout.total_width,
        circuit.layers.len(),
        widths.join(","),
        prover_config.lde_factor,
        prover_config.cap_size,
        prover_config.base_oracles_values_per_leaf,
        prover_config.whir_schedule.whir_steps_schedule,
        prover_config.whir_schedule.whir_queries_schedule,
        prover_config.whir_schedule.whir_steps_lde_factors,
        prover_config.whir_schedule.whir_pow_schedule,
    );

    // The VM run + binary preprocessing are thread-count independent: once.
    let max_threads = *threads.iter().max().unwrap();
    let vm_worker = Worker::new_with_num_threads(max_threads);
    let config = ProgramConfig::keccak_f1600();
    let vm = run_vm_and_capture::<DelegationsAndFamiliesCounters, FullUnsignedMachineDecoderConfig>(
        &config, &vm_worker,
    );
    println!("Finished at PC = 0x{:08x}", vm.final_pc());
    let expected_final_state = vm.expected_final_state();
    let cycles_bound = vm.cycles_bound;
    let num_calls = vm.counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>();
    assert!(num_calls < num_cycles_per_chunk);
    println!("[shape] add/sub family calls: {num_calls} (of 2^{trace_len_log2} rows)");

    let preprocessing_data = process_binary_into_separate_tables_ext::<
        BabyBearField,
        FullUnsignedMachineDecoderConfig,
        true,
        Global,
    >(
        &vm.text_section,
        &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
        1 << 20,
        &[
            NON_DETERMINISM_CSR as u16,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            KECCAK_SPECIAL5_CSR_REGISTER as u16,
            BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
        ],
    );
    let decoder_table_data = &preprocessing_data[&CIRCUIT_TYPE];
    let external_challenges = hardcoded_external_challenges();

    let mut table_driver = TableDriver::<BabyBearField>::new();
    cs::gkr_circuits::add_sub_family::add_sub_lui_auipc_mop_table_driver_fn::<BabyBearField>(
        &mut table_driver,
    );

    if outer > 0 {
        let t = std::time::Instant::now();
        let built = build_nonmem_family_full_trace::<CIRCUIT_TYPE, _>(
            &vm.snapshotter,
            &vm.tape,
            &expected_final_state,
            cycles_bound,
            num_calls,
            &circuit,
            &table_driver,
            decoder_table_data,
            add_sub_lui_auipc_mop::witness_eval_fn,
            num_cycles_per_chunk,
            false,
            &vm_worker,
        );
        println!("[outer] shared trace built in {:.3?}", t.elapsed());
        outer_parallel(
            outer,
            inner,
            naive_gkr,
            pin,
            &circuit,
            &table_driver,
            decoder_table_data,
            built.full_trace,
            trace_len,
            &external_challenges,
            &prover_config,
            &vm_worker,
        );
        return;
    }

    for &n in &threads {
        let worker = Worker::new_with_num_threads(n);
        println!("================ threads = {n} ================");
        if !skip_bw {
            bandwidth_probe(&worker, 1 << 27);
        }

        let t = std::time::Instant::now();
        let built = build_nonmem_family_full_trace::<CIRCUIT_TYPE, _>(
            &vm.snapshotter,
            &vm.tape,
            &expected_final_state,
            cycles_bound,
            num_calls,
            &circuit,
            &table_driver,
            decoder_table_data,
            add_sub_lui_auipc_mop::witness_eval_fn,
            num_cycles_per_chunk,
            false,
            &worker,
        );
        let trace_build = t.elapsed().as_secs_f64();
        println!("[scaling] threads={n} stage=trace_build seconds={trace_build:.3}");

        let t = std::time::Instant::now();
        let proof = prove_with_gkr_backend(
            naive_gkr,
            &circuit,
            &table_driver,
            decoder_table_data,
            built.full_trace,
            trace_len,
            &external_challenges,
            &prover_config,
            &worker,
        );
        let prove = t.elapsed().as_secs_f64();
        println!("[scaling] threads={n} stage=prove_total seconds={prove:.3}");
        println!(
            "[scaling] threads={n} grand_product={:?}",
            proof.grand_product_accumulator_computed
        );
        if let Some(path) = &proof_out {
            serialize_to_file(&proof, path);
            println!(
                "[scaling] threads={n} gkr_backend={} proof_digest=0x{:016x}",
                if naive_gkr { "naive" } else { "default" },
                file_digest(path)
            );
        }
        drop(proof);
    }
}
