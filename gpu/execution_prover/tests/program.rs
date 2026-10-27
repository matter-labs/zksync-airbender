#![cfg_attr(feature = "verifiers", feature(allocator_api))]
//! e2e: GPU prove → `ProgramProof` assembly → ND stream → native base-layer
//! verification. Requires both a CUDA device and the `verifiers` feature
//! (heavy verifier build), so the GPU test is doubly gated.

#![allow(unused_imports)]

mod upstream {
    pub use full_statement_verifier::host_utils::cost_model::estimate_verifier_cycles;
    pub use full_statement_verifier::host_utils::{
        bridge_blake_mode, build_unified_stream, build_unrolled_stream, compute_end_params,
        final_blake_mode, load_fsv_program, unified_switch_cycles, unrolled_blake_mode,
        FsvRecursionChain,
    };
    #[cfg(feature = "verifiers")]
    pub use full_statement_verifier::host_utils::{native_verify_unified, native_verify_unrolled};
    pub use full_statement_verifier::program_proof::ProgramProof;
    pub use prover::definitions::SecurityLevel;
    pub use setups::Setups;
    pub use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};
}

use crate::upstream::build_unrolled_stream;
use gpu_execution_prover::{
    ExecutionKind, ExecutionProver, ExecutionProverConfiguration, MachineType,
};
use program_prover::assemble_program_proof;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::elf::ProgramSource;
use riscv_transpiler::vm::FlatResponsesSource;

/// Workspace root; this crate is at `gpu/execution_prover/`.
#[cfg(all(not(no_cuda), feature = "verifiers"))]
fn artifact_root() -> std::path::PathBuf {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
}

/// Idempotent `env_logger` init shared by every e2e below.
#[cfg(all(not(no_cuda), feature = "verifiers"))]
fn init_test_logger() {
    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Info)
        .try_init();
}

/// Load the `blake2_with_compression` build of an `examples/<name>` workload as
/// `(binary_image, text_section)`.
#[cfg(all(not(no_cuda), feature = "verifiers"))]
fn load_workload(name: &str) -> (Vec<u32>, Vec<u32>) {
    let artifact_root = artifact_root();
    ProgramSource::legacy_binaries(
        artifact_root.join(format!("examples/{name}/app_blake2_with_compression.bin")),
        artifact_root.join(format!("examples/{name}/app_blake2_with_compression.text")),
    )
    .load_unpadded()
}

#[cfg(all(not(no_cuda), feature = "verifiers"))]
fn read_witness(path: &std::path::Path) -> Vec<u32> {
    let raw = std::fs::read_to_string(path).expect("read witness");
    let raw = raw.trim();
    assert!(raw.len().is_multiple_of(8));
    raw.as_bytes()
        .chunks(8)
        .map(|word| {
            u32::from_str_radix(std::str::from_utf8(word).unwrap(), 16)
                .expect("invalid witness word")
        })
        .collect()
}

#[cfg(all(not(no_cuda), feature = "verifiers"))]
fn load_zksync_os_workload() -> (Vec<u32>, Vec<u32>, Vec<u32>) {
    let root = artifact_root();
    let witness = read_witness(&root.join("riscv_transpiler/examples/zksync_os/23620012_witness"));
    let (binary_image, text_section) = ProgramSource::legacy_binaries(
        root.join("riscv_transpiler/examples/zksync_os/app.bin"),
        root.join("riscv_transpiler/examples/zksync_os/app.text"),
    )
    .load_unpadded();
    (binary_image, text_section, witness)
}

#[cfg(all(not(no_cuda), feature = "verifiers", feature = "deterministic_pow"))]
fn write_compressed<T: serde::Serialize>(value: &T, path: &std::path::Path) {
    assert!(!path.exists(), "refusing to overwrite {}", path.display());
    let file_name = path.file_name().unwrap().to_string_lossy();
    let temporary = path.with_file_name(format!(".{file_name}.tmp"));
    let file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary)
        .unwrap_or_else(|err| panic!("create {}: {err}", temporary.display()));
    let file = full_statement_verifier::host_utils::fixture_codec::encode(value, file);
    file.sync_all().expect("sync calibration fixture");
    std::fs::rename(&temporary, path).unwrap_or_else(|err| {
        panic!(
            "rename {} to {}: {err}",
            temporary.display(),
            path.display()
        )
    });
}

#[cfg(all(not(no_cuda), feature = "verifiers", feature = "deterministic_pow"))]
fn write_cost_model_fixture(
    directory: &std::path::Path,
    name: &str,
    proof: &crate::upstream::ProgramProof,
    setups: &crate::upstream::Setups,
) {
    write_compressed(proof, &directory.join(format!("{name}_proof.bin")));
    write_compressed(setups, &directory.join(format!("{name}_setups.bin")));

    let riscv_counts: Vec<_> = proof
        .riscv_proofs
        .iter()
        .map(|(family, proofs)| (*family, proofs.len()))
        .collect();
    let delegation_counts: Vec<_> = proof
        .delegation_proofs
        .iter()
        .map(|(delegation, proofs)| (*delegation, proofs.len()))
        .collect();
    log::info!(
        "wrote {name}: {} cycles, RISC-V {riscv_counts:?}, delegations {delegation_counts:?}",
        proof.executed_cycles()
    );
}

/// Proofs per RISC-V family (and per Keccak-f1600 circuit) in the synthetic
/// cost-model fixtures, so each circuit's verifier cost is measured more than
/// once per fixture.
#[cfg(all(not(no_cuda), feature = "verifiers", feature = "deterministic_pow"))]
const COST_MODEL_REPEATS: usize = 4;

/// Iterations of `push_counted_loop` that fill `COST_MODEL_REPEATS` proofs of
/// every 2^24-cycle RISC-V family the loop executes, half a proof short of one
/// more.
#[cfg(all(not(no_cuda), feature = "verifiers", feature = "deterministic_pow"))]
const COST_MODEL_FILLER_ITERATIONS: u32 = ((COST_MODEL_REPEATS as u32 - 1) << 24) | (1 << 23);

/// Run `body` `iterations` times, counting down in x6; each iteration also
/// executes one `addi` and one `bne`.
#[cfg(all(not(no_cuda), feature = "verifiers", feature = "deterministic_pow"))]
fn push_counted_loop(binary: &mut Vec<u32>, iterations: u32, body: &[u32]) {
    let upper = iterations.wrapping_add(0x800) & !0xfff;
    binary.push(upper | (6 << 7) | 0x37); // lui x6, count high
    binary.push(((iterations.wrapping_sub(upper) & 0xfff) << 20) | (6 << 15) | (6 << 7) | 0x13);
    let loop_start = binary.len();
    binary.extend_from_slice(body);
    binary.push(0xfff3_0313); // addi x6, x6, -1
    let offset = (-4 * (binary.len() - loop_start) as i32) as u32;
    binary.push(
        ((offset >> 12 & 1) << 31)
            | ((offset >> 5 & 63) << 25)
            | (6 << 15)
            | (1 << 12)
            | ((offset >> 1 & 15) << 8)
            | ((offset >> 11 & 1) << 7)
            | 0x63, // bne x6, x0, loop
    );
}

/// Touch one more address window than a single i&t proof can carry.
#[cfg(all(not(no_cuda), feature = "verifiers", feature = "deterministic_pow"))]
fn push_window_touches(binary: &mut Vec<u32>) {
    let window_bits =
        setups::inits_and_teardowns::TRACE_LEN_LOG2 + setups::inits_and_teardowns::WORD_BITS;
    for window in 0..=setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS {
        let address =
            ((window << window_bits) as u32).max(common_constants::rom::ROM_BYTE_SIZE as u32);
        binary.push(address | (5 << 7) | 0x37); // lui x5, address >> 12
        binary.push(0x0052_a023); // sw x5, 0(x5)
    }
}

/// Prove `(binary_image, text_section)` with the given non-determinism reads on
/// the GPU `ExecutionProver` and assemble the `(ProgramProof, Setups)`. The
/// shared prove tail of every e2e below and of each `run_gpu_recursive_pipeline`
/// stage; callers apply their own `set_recursion_chain` / native verify (which
/// differ per stage).
#[cfg(all(not(no_cuda), feature = "verifiers"))]
fn prove_on_gpu(
    prover: &mut ExecutionProver,
    kind: ExecutionKind,
    machine: MachineType,
    binary_image: Vec<u32>,
    text_section: Vec<u32>,
    reads: Vec<u32>,
) -> (crate::upstream::ProgramProof, crate::upstream::Setups) {
    let handle = prover.add_binary(kind, machine, binary_image, text_section, None);
    prove_registered_on_gpu(prover, &handle, reads)
}

#[cfg(all(not(no_cuda), feature = "verifiers"))]
fn prove_registered_on_gpu(
    prover: &mut ExecutionProver,
    handle: &gpu_execution_prover::BinaryHandle,
    reads: Vec<u32>,
) -> (crate::upstream::ProgramProof, crate::upstream::Setups) {
    let result =
        prover.commit_memory_and_prove(0, handle, FlatResponsesSource::new_with_reads(reads));
    let artifacts = prover.program_artifacts(handle);
    assemble_program_proof(&artifacts, result)
}

/// Prove `hashed_fibonacci` (blake2_with_compression build — fires the
/// Blake2WithCompression delegation) on the GPU, assemble the
/// `ProgramProof` + setups map, build the unrolled ND stream, and run the
/// real base-layer verifier natively.
#[test]
#[cfg(all(not(no_cuda), feature = "verifiers"))]
#[ignore]
fn test_program_prover_base_layer_verify() {
    init_test_logger();
    let configuration = ExecutionProverConfiguration::default();
    let mut prover = ExecutionProver::with_configuration(configuration);
    let (binary_image, text_section) = load_workload("hashed_fibonacci");
    let (proof, setups) = prove_on_gpu(
        &mut prover,
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        binary_image,
        text_section,
        vec![100, 5],
    );
    log::info!(
        "assembled ProgramProof: {} cycles, {} riscv families, {} delegation types",
        proof.executed_cycles(),
        proof.riscv_proofs.len(),
        proof.delegation_proofs.len(),
    );

    let stream = build_unrolled_stream(&setups, &proof, verifier_common::BLAKE_MODE);
    let output = crate::upstream::native_verify_unrolled(stream, true);
    log::info!("base layer verified natively; output registers: {output:?}");
}

/// Unified counterpart of the base-layer e2e: prove the `multi_family_smoke`
/// workload (same binary + ND inputs as gpu_circuit_prover's unified GPU tests,
/// blake2_with_compression variant — the JIT lacks the g-function delegation)
/// with `ExecutionKind::Unified`, assemble the `ProgramProof` (including
/// `num_it_circuits`), build the unified ND stream, and run the real
/// base-layer unified verifier natively.
///
/// This test used to fail the global memory-permutation closure
/// (`read_set_product_accumulator == write_set_product_accumulator`, in
/// `full_statement_verifier`'s unified circuit statement). The root
/// cause was NOT the canonical inits-and-teardowns top bits (for this
/// workload the touched 2^24-word RAM chunks are exactly {0, 1}, so the
/// canonical `[0, 1]` equals the real top bits): the JIT simulator was
/// building MOP (Zimop) opcodes over M31 (the `RISCV_MOP_FIELD` default)
/// while the replay worker replays over BabyBear, so the simulation's final
/// registers / RAM state silently diverged from the traced witness —
/// per-circuit proofs stayed self-consistent and only the closure caught it.
/// Fixed by making the MOP field an explicit `JittedCode::preprocess_bytecode`
/// parameter (the simulation runner passes `MopField::BabyBear`).
#[test]
#[cfg(all(not(no_cuda), feature = "verifiers"))]
#[ignore]
fn test_program_prover_unified_base_layer_verify() {
    init_test_logger();
    let configuration = ExecutionProverConfiguration {
        // `multi_family_smoke` feeds raw non-determinism words (e.g. `0xDEAD_BEEF`) into the
        // field operations, so their inputs can not be assumed canonical
        assume_canonical_mop_inputs: false,
        ..Default::default()
    };
    let mut prover = ExecutionProver::with_configuration(configuration);
    let (binary_image, text_section) = load_workload("multi_family_smoke");
    let (proof, setups) = prove_on_gpu(
        &mut prover,
        ExecutionKind::Unified,
        MachineType::Reduced,
        binary_image,
        text_section,
        vec![50, 0xDEAD_BEEF],
    );
    log::info!(
        "assembled unified ProgramProof: {} cycles, {} unified circuits, num_it_circuits {:?}, {} delegation types",
        proof.executed_cycles(),
        proof
            .riscv_proofs
            .values()
            .map(|v| v.len())
            .sum::<usize>(),
        proof.num_it_circuits,
        proof.delegation_proofs.len(),
    );

    let stream = crate::upstream::build_unified_stream(&setups, &proof, verifier_common::BLAKE_MODE);
    let output = crate::upstream::native_verify_unified(stream, true);
    log::info!("unified base layer verified natively; output registers: {output:?}");
}

/// Unified counterpart of `test_program_prover_cpu_gpu_proof_diff`: prove
/// multi_family_smoke on the CPU reference
/// (`program_prover::unified::prove_unified_execution_with_replayer`, which
/// asserts internal closure to ONE), verify it natively, then prove on GPU and
/// diff the two `ProgramProof`s field by field.
#[test]
#[cfg(all(not(no_cuda), feature = "verifiers"))]
#[ignore]
fn test_program_prover_unified_cpu_gpu_proof_diff() {
    init_test_logger();
    let (binary_image, text_section) = load_workload("multi_family_smoke");
    let artifact_root = artifact_root();
    let (padded_binary_image, padded_text_section) = ProgramSource::legacy_binaries(
        artifact_root.join("examples/multi_family_smoke/app_blake2_with_compression.bin"),
        artifact_root.join("examples/multi_family_smoke/app_blake2_with_compression.text"),
    )
    .load();
    let worker = worker::Worker::new_with_num_threads(8);
    let configuration = ExecutionProverConfiguration {
        // `multi_family_smoke` feeds raw non-determinism words (e.g. `0xDEAD_BEEF`) into the
        // field operations, so their inputs can not be assumed canonical
        assume_canonical_mop_inputs: false,
        ..Default::default()
    };
    let security_level = configuration.security_level;

    let (cpu_proof, cpu_setups) =
        program_prover::unified::prove_unified_execution_with_replayer::<_, _>(
            1 << 31,
            &padded_binary_image,
            &padded_text_section,
            true,
            QuasiUARTSource::new_with_reads(vec![50, 0xDEAD_BEEF]),
            1 << 30,
            &worker,
            security_level,
            verifier_common::MEMORY_DELEGATION_POW_BITS as u32,
            &prover::gkr::prover::DefaultBabyBearBackend::default(),
            &prover::gkr::prover::DefaultBabyBearGKRBackend::default(),
        );
    log::info!("CPU reference proved (internal closure passed); verifying natively");
    let cpu_output = crate::upstream::native_verify_unified(
        crate::upstream::build_unified_stream(&cpu_setups, &cpu_proof),
        true,
    );
    log::info!("CPU reference verifies; output registers: {cpu_output:?}");

    // GPU flow.
    let mut prover = ExecutionProver::with_configuration(configuration);
    let (gpu_proof, gpu_setups) = prove_on_gpu(
        &mut prover,
        ExecutionKind::Unified,
        MachineType::Reduced,
        binary_image,
        text_section,
        vec![50, 0xDEAD_BEEF],
    );

    assert_eq!(
        cpu_setups.keys().collect::<Vec<_>>(),
        gpu_setups.keys().collect::<Vec<_>>(),
        "setups family keys differ"
    );
    for (family_idx, cpu_params) in cpu_setups.iter() {
        let gpu_params = &gpu_setups[family_idx];
        assert_eq!(
            cpu_params, gpu_params,
            "setup params differ for family {family_idx}"
        );
    }
    log::info!("setups match");

    serde_json::to_writer(
        std::fs::File::create("/tmp/pp_unified_cpu_proof.json").unwrap(),
        &cpu_proof,
    )
    .unwrap();
    serde_json::to_writer(
        std::fs::File::create("/tmp/pp_unified_gpu_proof.json").unwrap(),
        &gpu_proof,
    )
    .unwrap();
    log::info!("dumped /tmp/pp_unified_cpu_proof.json and /tmp/pp_unified_gpu_proof.json");

    assert_eq!(cpu_proof.final_pc, gpu_proof.final_pc, "final_pc differs");
    assert_eq!(
        cpu_proof.final_timestamp, gpu_proof.final_timestamp,
        "final_timestamp differs"
    );
    assert_eq!(
        cpu_proof.register_final_values, gpu_proof.register_final_values,
        "register_final_values differ"
    );
    assert_eq!(
        cpu_proof.num_it_circuits, gpu_proof.num_it_circuits,
        "num_it_circuits differs"
    );
    for (family_idx, cpu_family_proofs) in cpu_proof.riscv_proofs.iter() {
        let gpu_family_proofs = &gpu_proof.riscv_proofs[family_idx];
        assert_eq!(cpu_family_proofs.len(), gpu_family_proofs.len());
        for (i, (c, g)) in cpu_family_proofs.iter().zip(gpu_family_proofs).enumerate() {
            assert_eq!(
                serde_json::to_value(c).unwrap(),
                serde_json::to_value(g).unwrap(),
                "unified riscv proof differs: family {family_idx} sequence {i}"
            );
        }
    }
    for (delegation_type, cpu_delegation_proofs) in cpu_proof.delegation_proofs.iter() {
        let gpu_delegation_proofs = &gpu_proof.delegation_proofs[delegation_type];
        for (i, (c, g)) in cpu_delegation_proofs
            .iter()
            .zip(gpu_delegation_proofs)
            .enumerate()
        {
            assert_eq!(
                serde_json::to_value(c).unwrap(),
                serde_json::to_value(g).unwrap(),
                "delegation proof differs: type {delegation_type} sequence {i}"
            );
        }
    }
    log::info!("full unified CPU/GPU ProgramProof parity");
}

/// Diagnostic: prove the same binary + ND inputs on the CPU reference
/// (`program_prover::prove_unrolled_execution_with_replayer`), sanity-verify
/// the CPU proof natively, then diff the CPU-assembled `(ProgramProof, Setups)`
/// against the GPU-assembled pair field by field to localize any divergence.
#[test]
#[cfg(all(not(no_cuda), feature = "verifiers"))]
#[ignore]
fn test_program_prover_cpu_gpu_proof_diff() {
    init_test_logger();
    let (binary_image, text_section) = load_workload("hashed_fibonacci");

    // CPU reference (params mirror prover_examples::recursion's base layer,
    // including the ROM-word padding its `load_program` applies).
    let (padded_binary_image, padded_text_section) = ProgramSource::legacy_binaries(
        artifact_root().join("examples/hashed_fibonacci/app_blake2_with_compression.bin"),
        artifact_root().join("examples/hashed_fibonacci/app_blake2_with_compression.text"),
    )
    .load();
    let worker = worker::Worker::new_with_num_threads(8);
    let (cpu_proof, cpu_setups) = program_prover::unrolled::prove_unrolled_execution_with_replayer::<
        riscv_transpiler::cycle::IMStandardIsaConfigUnsignedMulDivOnly,
        std::alloc::Global,
        _,
        _,
    >(
        1 << 31,
        &padded_binary_image,
        &padded_text_section,
        true,
        QuasiUARTSource::new_with_reads(vec![100, 5]),
        1 << 30,
        &worker,
        crate::upstream::SecurityLevel::Sec100,
        verifier_common::MEMORY_DELEGATION_POW_BITS as u32,
        &prover::gkr::prover::DefaultBabyBearBackend::default(),
        &prover::gkr::prover::DefaultBabyBearGKRBackend::default(),
    );
    log::info!("CPU reference proved; verifying natively");
    let cpu_output = crate::upstream::native_verify_unrolled(
        build_unrolled_stream(&cpu_setups, &cpu_proof),
        true,
    );
    log::info!("CPU reference verifies; output registers: {cpu_output:?}");

    // GPU flow.
    let configuration = ExecutionProverConfiguration::default();
    let mut prover = ExecutionProver::with_configuration(configuration);
    let (gpu_proof, gpu_setups) = prove_on_gpu(
        &mut prover,
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        binary_image,
        text_section,
        vec![100, 5],
    );

    // Diff setups.
    assert_eq!(
        cpu_setups.keys().collect::<Vec<_>>(),
        gpu_setups.keys().collect::<Vec<_>>(),
        "setups family keys differ"
    );
    for (family_idx, cpu_params) in cpu_setups.iter() {
        let gpu_params = &gpu_setups[family_idx];
        assert_eq!(
            cpu_params, gpu_params,
            "setup params differ for family {family_idx}"
        );
    }
    log::info!("setups match");

    // Diff proof scalars + structure.
    assert_eq!(cpu_proof.final_pc, gpu_proof.final_pc, "final_pc differs");
    assert_eq!(
        cpu_proof.final_timestamp, gpu_proof.final_timestamp,
        "final_timestamp differs"
    );
    assert_eq!(
        cpu_proof.register_final_values, gpu_proof.register_final_values,
        "register_final_values differ"
    );
    // The CPU prover leaves `end_params` as a placeholder (the recursion
    // driver computes it externally); compare our assembled value against the
    // recomputation over the CPU setups instead.
    assert_eq!(
        crate::upstream::compute_end_params(&cpu_setups, cpu_proof.final_pc),
        gpu_proof.end_params,
        "end_params differ from recomputation over CPU setups"
    );
    assert_eq!(
        cpu_proof.pow_challenge, gpu_proof.pow_challenge,
        "pow_challenge differs"
    );
    // Dump both proofs for offline analysis before any assert below can fire —
    // regenerating them costs a ~17-minute CPU prove.
    serde_json::to_writer(
        std::fs::File::create("/tmp/pp_cpu_proof.json").unwrap(),
        &cpu_proof,
    )
    .unwrap();
    serde_json::to_writer(
        std::fs::File::create("/tmp/pp_gpu_proof.json").unwrap(),
        &gpu_proof,
    )
    .unwrap();
    log::info!("dumped /tmp/pp_cpu_proof.json and /tmp/pp_gpu_proof.json");

    // Per-family proof counts (missing entry == empty entry), then per-proof
    // JSON equality.
    let count_of = |m: &std::collections::BTreeMap<u32, Vec<_>>, k: u32| {
        m.get(&k).map(|v| v.len()).unwrap_or(0)
    };
    let all_families: std::collections::BTreeSet<u32> = cpu_proof
        .riscv_proofs
        .keys()
        .chain(gpu_proof.riscv_proofs.keys())
        .copied()
        .collect();
    for family_idx in all_families {
        assert_eq!(
            count_of(&cpu_proof.riscv_proofs, family_idx),
            count_of(&gpu_proof.riscv_proofs, family_idx),
            "riscv proof count differs for family {family_idx}"
        );
    }
    for (family_idx, cpu_family_proofs) in cpu_proof.riscv_proofs.iter() {
        if cpu_family_proofs.is_empty() && !gpu_proof.riscv_proofs.contains_key(family_idx) {
            continue;
        }
        let gpu_family_proofs = &gpu_proof.riscv_proofs[family_idx];
        for (i, (c, g)) in cpu_family_proofs.iter().zip(gpu_family_proofs).enumerate() {
            assert_eq!(
                serde_json::to_value(c).unwrap(),
                serde_json::to_value(g).unwrap(),
                "riscv proof differs: family {family_idx} sequence {i}"
            );
        }
    }
    log::info!("riscv proofs match");
    assert_eq!(
        cpu_proof.inits_and_teardown_proofs.len(),
        gpu_proof.inits_and_teardown_proofs.len(),
        "i&t proof counts differ"
    );
    for (i, (c, g)) in cpu_proof
        .inits_and_teardown_proofs
        .iter()
        .zip(&gpu_proof.inits_and_teardown_proofs)
        .enumerate()
    {
        assert_eq!(
            serde_json::to_value(c).unwrap(),
            serde_json::to_value(g).unwrap(),
            "i&t proof differs: sequence {i}"
        );
    }
    assert_eq!(
        cpu_proof
            .delegation_proofs
            .iter()
            .map(|(k, v)| (*k, v.len()))
            .collect::<Vec<_>>(),
        gpu_proof
            .delegation_proofs
            .iter()
            .map(|(k, v)| (*k, v.len()))
            .collect::<Vec<_>>(),
        "delegation proof counts differ"
    );
    for (delegation_type, cpu_delegation_proofs) in cpu_proof.delegation_proofs.iter() {
        let gpu_delegation_proofs = &gpu_proof.delegation_proofs[delegation_type];
        for (i, (c, g)) in cpu_delegation_proofs
            .iter()
            .zip(gpu_delegation_proofs)
            .enumerate()
        {
            assert_eq!(
                serde_json::to_value(c).unwrap(),
                serde_json::to_value(g).unwrap(),
                "delegation proof differs: type {delegation_type} sequence {i}"
            );
        }
    }
    log::info!("delegation + i&t proofs match");
    // Compiled circuits last (largest JSON).
    for (family_idx, c) in cpu_proof.compiled_riscv_circuits.iter() {
        let g = &gpu_proof.compiled_riscv_circuits[family_idx];
        assert_eq!(
            serde_json::to_value(c).unwrap(),
            serde_json::to_value(g).unwrap(),
            "compiled riscv circuit differs: family {family_idx}"
        );
    }
    log::info!("full CPU/GPU ProgramProof parity");
}

/// Recursion level 1 — the "JIT vs fsv binaries" watch item: prove the
/// `fsv_unrolled_base_layer` verifier program (blake2_with_compression
/// variant, reduced ISA) on the GPU, feeding it the base-layer
/// `ProgramProof`'s ND stream as its witness, then verify the resulting
/// recursion-layer proof natively. Exercises fsv binaries (tri-add / xor-rot
/// special opcodes) through the JIT simulator + GPU prover; a decode gap in the
/// JIT would surface here.
///
/// Mirrors one iteration of `prover_examples::recursion`'s unrolled-recursion
/// loop: chain fields come from `begin_chain(compute_end_params(base))`, and
/// the recursion-layer verify runs with `is_base = false` (reads the chain
/// preimage from the stream).
#[test]
#[cfg(all(not(no_cuda), feature = "verifiers"))]
#[ignore]
fn test_program_prover_recursion_layer_verify() {
    use crate::upstream::{compute_end_params, native_verify_unrolled, FsvRecursionChain};

    init_test_logger();
    let configuration = ExecutionProverConfiguration::default();
    let mut prover = ExecutionProver::with_configuration(configuration);

    // Stage 1: base layer (identical to test_program_prover_base_layer_verify).
    let (binary_image, text_section) = load_workload("hashed_fibonacci");
    let (base_proof, base_setups) = prove_on_gpu(
        &mut prover,
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        binary_image,
        text_section,
        vec![100, 5],
    );
    native_verify_unrolled(build_unrolled_stream(&base_setups, &base_proof), true);
    log::info!(
        "base layer proved on GPU + verified natively ({} cycles)",
        base_proof.executed_cycles()
    );

    let base_end_params = compute_end_params(&base_setups, base_proof.final_pc);
    let chain = FsvRecursionChain::begin(&base_end_params);

    // Stage 2: prove the fsv base-layer verifier over the base proof's stream.
    let (fsv_binary, fsv_text) = ProgramSource::elf(
        artifact_root()
            .join("tools/gkr_verifier/full_statement_verifiers/fsv_unrolled_base_layer_sec_100_blake2_with_compression.elf"),
    )
    .load_unpadded();
    let stream = build_unrolled_stream(&base_setups, &base_proof);
    let (mut recursion_proof, recursion_setups) = prove_on_gpu(
        &mut prover,
        ExecutionKind::Unrolled,
        MachineType::Reduced,
        fsv_binary,
        fsv_text,
        stream,
    );
    recursion_proof.set_recursion_chain(&chain);
    log::info!(
        "recursion layer proved on GPU ({} cycles)",
        recursion_proof.executed_cycles()
    );

    let output = native_verify_unrolled(
        build_unrolled_stream(&recursion_setups, &recursion_proof),
        false,
    );
    log::info!("recursion layer verified natively; output registers: {output:?}");
}

/// Full GPU recursive pipeline, mirroring `prover_examples::recursion`'s
/// `test_recursive_proving_pipeline_zksync_os` but with our test workload
/// (hashed_fibonacci) and every proof produced by the GPU `ExecutionProver`:
///
///   base (unrolled, full-unsigned ISA)
///   → unrolled recursion loop (reduced ISA, fsv verifier binaries)
///   → bridge (the unrolled verifier proved in UNIFIED mode)
///   → final (fsv_unified_recursion_layer, unified mode)
///
/// with the recursion hash chain threaded through and every layer verified
/// natively. Deviation from the CPU pipeline: the base workload is tiny
/// (~1.7k cycles), so the layer-0 verifier estimates far below the unified
/// switch threshold and the CPU flow would bridge immediately; we force one
/// unrolled layer first so the loop machinery (estimate → prove → chain) is
/// exercised, then bridge over the recursion proof. Blake modes are
/// env-selectable like the CPU pipeline (default blake2_with_compression;
/// the g-function variants need a JIT delegation that doesn't exist).
#[test]
#[cfg(all(not(no_cuda), feature = "verifiers"))]
#[ignore]
fn test_program_prover_recursive_pipeline() {
    init_test_logger();
    let (binary_image, text_section) = load_workload("hashed_fibonacci");
    run_gpu_recursive_pipeline(binary_image, text_section, vec![100, 5], true);
}

/// The real thing: the recursive pipeline over the zksync_os block workload —
/// the GPU analogue of `test_recursive_proving_pipeline_zksync_os` (heavy;
/// the base layer proves a full zksync_os block). The base estimates well
/// above the unified-switch threshold, so the unrolled recursion loop runs
/// its natural course (no forced layer). Threshold overridable via
/// `RECURSION_UNIFIED_SWITCH_CYCLES` like the CPU pipeline.
#[test]
#[cfg(all(not(no_cuda), feature = "verifiers"))]
#[ignore]
fn test_program_prover_recursive_pipeline_zksync_os() {
    init_test_logger();
    let (binary_image, text_section, witness) = load_zksync_os_workload();
    run_gpu_recursive_pipeline(binary_image, text_section, witness, false);
}

/// Generate the local, non-authoritative proof/setup inputs used to calibrate
/// the Sec100 Compression verifier cost model. This deliberately proves two
/// recursion layers instead of consulting the production scheduling threshold.
/// The synthetic workloads repeat every circuit they exercise
/// (`COST_MODEL_REPEATS`; i&t twice) so per-proof prices come from repeated
/// proofs. Output goes to the empty local `COST_MODEL_FIXTURE_DIR`.
///
/// Optionally set `COST_MODEL_INPUT_DIR` to an input-only directory containing
/// `app.bin`, `app.text`, and `inputs/<id>.hex`: concatenated eight-hex-digit
/// u32 witness words, most significant digit first (trailing whitespace allowed).
/// Inputs run in lexicographic id order, each through the base and two recursion
/// stages. The first keeps `base`/`recursion0`/`recursion1`; later inputs append
/// `_<id>`. The existing synthetic fixtures and `base_alt` run once.
/// Without this variable the committed block-23620012 guest/witness is used.
/// Never commit local inputs or generated fixtures.
#[test]
#[cfg(all(not(no_cuda), feature = "verifiers", feature = "deterministic_pow"))]
#[ignore = "manual Sec100 cost-model fixture generation (large GPU run)"]
fn test_generate_sec100_cost_model_fixtures() {
    use crate::upstream::{
        compute_end_params, load_fsv_program, native_verify_unrolled, BlakeMode, FsvProgram,
        FsvRecursionChain, SecurityLevel,
    };

    init_test_logger();

    let fixture_dir = std::env::var_os("COST_MODEL_FIXTURE_DIR")
        .map(std::path::PathBuf::from)
        .expect("set COST_MODEL_FIXTURE_DIR to an empty local output directory");
    std::fs::create_dir_all(&fixture_dir).expect("create cost-model fixture directory");
    assert!(
        std::fs::read_dir(&fixture_dir).unwrap().next().is_none(),
        "fixture output directory must be empty"
    );
    let (base_binary, base_text, inputs) =
        if let Some(directory) = std::env::var_os("COST_MODEL_INPUT_DIR") {
            let directory = std::path::PathBuf::from(directory);
            let (binary, text) = ProgramSource::legacy_binaries(
                directory.join("app.bin"),
                directory.join("app.text"),
            )
            .load_unpadded();
            let mut paths: Vec<_> = std::fs::read_dir(directory.join("inputs"))
                .unwrap()
                .map(|entry| entry.unwrap().path())
                .filter(|path| path.extension().is_some_and(|extension| extension == "hex"))
                .collect();
            paths.sort_by(|a, b| a.file_stem().cmp(&b.file_stem()));
            assert!(!paths.is_empty(), "local corpus has no inputs/*.hex");
            let inputs: Vec<_> = paths
                .iter()
                .map(|path| {
                    (
                        path.file_stem().unwrap().to_str().unwrap().to_owned(),
                        read_witness(path),
                    )
                })
                .collect();
            (binary, text, inputs)
        } else {
            let (binary, text, witness) = load_zksync_os_workload();
            (binary, text, vec![("default".to_owned(), witness)])
        };

    let configuration = ExecutionProverConfiguration {
        security_level: SecurityLevel::Sec100,
        ..Default::default()
    };
    let mut prover = ExecutionProver::with_configuration(configuration);
    // Register each common binary once: add_binary retains precomputations,
    // so registering them anew for every block would grow resident RAM.
    let guest = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        base_binary,
        base_text,
        None,
    );
    let fsv_dir = artifact_root().join("tools/gkr_verifier");
    let (binary, text) = load_fsv_program(
        &fsv_dir,
        FsvProgram::UnrolledBaseLayer,
        BlakeMode::Compression,
    );
    let base_verifier = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::Reduced,
        binary,
        text,
        None,
    );
    let (binary, text) = load_fsv_program(
        &fsv_dir,
        FsvProgram::UnrolledRecursionLayer,
        BlakeMode::Compression,
    );
    let recursion_verifier = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::Reduced,
        binary,
        text,
        None,
    );

    let mut last_chain = None;
    for (i, (id, witness)) in inputs.into_iter().enumerate() {
        let suffix = if i == 0 {
            String::new()
        } else {
            format!("_{id}")
        };
        let names = ["base", "recursion0", "recursion1"].map(|name| format!("{name}{suffix}"));
        let (base_proof, base_setups) = prove_registered_on_gpu(&mut prover, &guest, witness);
        native_verify_unrolled(build_unrolled_stream(&base_setups, &base_proof), true);
        write_cost_model_fixture(&fixture_dir, &names[0], &base_proof, &base_setups);
        let base_end_params = compute_end_params(&base_setups, base_proof.final_pc);
        let mut chain = FsvRecursionChain::begin(&base_end_params);
        let (mut recursion0_proof, recursion0_setups) = prove_registered_on_gpu(
            &mut prover,
            &base_verifier,
            build_unrolled_stream(&base_setups, &base_proof),
        );
        recursion0_proof.set_recursion_chain(&chain);
        native_verify_unrolled(
            build_unrolled_stream(&recursion0_setups, &recursion0_proof),
            false,
        );
        write_cost_model_fixture(
            &fixture_dir,
            &names[1],
            &recursion0_proof,
            &recursion0_setups,
        );
        let recursion0_end_params =
            compute_end_params(&recursion0_setups, recursion0_proof.final_pc);
        chain.extend(&recursion0_end_params);
        let (mut recursion1_proof, recursion1_setups) = prove_registered_on_gpu(
            &mut prover,
            &recursion_verifier,
            build_unrolled_stream(&recursion0_setups, &recursion0_proof),
        );
        recursion1_proof.set_recursion_chain(&chain);
        native_verify_unrolled(
            build_unrolled_stream(&recursion1_setups, &recursion1_proof),
            false,
        );
        write_cost_model_fixture(
            &fixture_dir,
            &names[2],
            &recursion1_proof,
            &recursion1_setups,
        );
        last_chain = Some(chain);
    }
    let chain = last_chain.expect("at least one calibration input");

    let (base_alt_binary, base_alt_text) = load_workload("hashed_fibonacci");
    let (base_alt_proof, base_alt_setups) = prove_on_gpu(
        &mut prover,
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        base_alt_binary,
        base_alt_text,
        vec![15, 1_200_000],
    );
    native_verify_unrolled(
        build_unrolled_stream(&base_alt_setups, &base_alt_proof),
        true,
    );
    write_cost_model_fixture(&fixture_dir, "base_alt", &base_alt_proof, &base_alt_setups);

    // 35,000 permutations exceed one 2^22-row proof for each Keccak-f1600
    // circuit, so 35,000 per repeat fill at least that many proofs.
    let permutations = 35_000 * COST_MODEL_REPEATS as u32;
    let mut keccak_binary = vec![
        common_constants::rom::ROM_BYTE_SIZE as u32 | (11 << 7) | 0x37, // lui x11, RAM
    ];
    let mut permutation = vec![0x0000_0533]; // add x10, x0, x0
    for i in 0..common_constants::delegation_types::keccak_f1600::NUM_KECCAK_F1600_CALLS {
        let csr = common_constants::delegation_types::keccak_f1600::keccak_f1600_call_csr(i);
        permutation.push((csr << 20) | 0x1073); // csrrw x0, csr, x0
    }
    push_counted_loop(&mut keccak_binary, permutations, &permutation);
    push_counted_loop(
        &mut keccak_binary,
        COST_MODEL_FILLER_ITERATIONS,
        &[0x0065_a023], // sw x6, 0(x11)
    );
    push_window_touches(&mut keccak_binary);
    keccak_binary.push(0x0000_006f); // jal x0, 0
    let (keccak_proof, keccak_setups) = prove_on_gpu(
        &mut prover,
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        keccak_binary.clone(),
        keccak_binary,
        vec![],
    );
    for csr in [
        common_constants::delegation_types::keccak_f1600::KECCAK_THETA_RHO_CSR_REGISTER,
        common_constants::delegation_types::keccak_f1600::KECCAK_COLUMN_PARITY_CSR_REGISTER,
        common_constants::delegation_types::keccak_f1600::KECCAK_CHI5_CSR_REGISTER,
    ] {
        assert!(keccak_proof.delegation_proofs[&csr].len() >= 2);
    }
    native_verify_unrolled(build_unrolled_stream(&keccak_setups, &keccak_proof), true);
    write_cost_model_fixture(&fixture_dir, "keccak_f1600", &keccak_proof, &keccak_setups);

    // One instruction of each listed family per iteration, then the i&t windows.
    let memory_program = |body: &[u32]| {
        let mut binary = vec![
            common_constants::rom::ROM_BYTE_SIZE as u32 | (9 << 7) | 0x37, // lui x9, RAM
        ];
        push_counted_loop(&mut binary, COST_MODEL_FILLER_ITERATIONS, body);
        push_window_touches(&mut binary);
        binary
    };
    let mut memory_binary = memory_program(&[
        0x0063_c3b3, // xor x7, x7, x6
        0x0263_8433, // mul x8, x7, x6
        0x0064_a023, // sw x6, 0(x9)
        0x0064_8223, // sb x6, 4(x9)
    ]);
    memory_binary.push(0x0000_006f); // jal x0, 0
    let (memory_proof, memory_setups) = prove_on_gpu(
        &mut prover,
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        memory_binary.clone(),
        memory_binary,
        vec![],
    );
    assert_eq!(memory_proof.inits_and_teardown_proofs.len(), 2);
    native_verify_unrolled(build_unrolled_stream(&memory_setups, &memory_proof), true);
    write_cost_model_fixture(
        &fixture_dir,
        "memory_windows",
        &memory_proof,
        &memory_setups,
    );

    // Price i&t and the reduced machine's families in the recursion verifier as
    // well as the base verifier. Supply a valid chain hash in x18..x25 so the
    // synthetic reduced-machine program can be checked by the recursion
    // statement verifier.
    let mut memory_binary = memory_program(&[
        0x0063_c3b3, // xor x7, x7, x6
        0x0064_a023, // sw x6, 0(x9)
    ]);
    for (i, word) in chain.hash().into_iter().enumerate() {
        let reg = (18 + i) as u32;
        let upper = word.wrapping_add(0x800) & !0xfff;
        memory_binary.push(upper | (reg << 7) | 0x37);
        memory_binary
            .push(((word.wrapping_sub(upper) & 0xfff) << 20) | (reg << 15) | (reg << 7) | 0x13);
    }
    memory_binary.push(0x0000_006f);
    let (mut memory_proof, memory_setups) = prove_on_gpu(
        &mut prover,
        ExecutionKind::Unrolled,
        MachineType::Reduced,
        memory_binary.clone(),
        memory_binary,
        vec![],
    );
    assert_eq!(memory_proof.inits_and_teardown_proofs.len(), 2);
    memory_proof.set_recursion_chain(&chain);
    native_verify_unrolled(build_unrolled_stream(&memory_setups, &memory_proof), false);
    write_cost_model_fixture(
        &fixture_dir,
        "memory_windows_recursion",
        &memory_proof,
        &memory_setups,
    );
}

#[cfg(all(not(no_cuda), feature = "verifiers"))]
fn run_gpu_recursive_pipeline(
    base_binary_image: Vec<u32>,
    base_text_section: Vec<u32>,
    base_non_determinism: Vec<u32>,
    force_first_layer: bool,
) {
    use crate::upstream::{
        bridge_blake_mode, build_unified_stream, compute_end_params, estimate_verifier_cycles,
        final_blake_mode, load_fsv_program, native_verify_unified, native_verify_unrolled,
        unified_switch_cycles, unrolled_blake_mode, FsvProgram, FsvRecursionChain,
    };

    let switch_cycles = unified_switch_cycles();

    let configuration = ExecutionProverConfiguration::default();
    let mut prover = ExecutionProver::with_configuration(configuration);

    // === Stage 1: base layer. ===
    let (base_proof, base_setups) = prove_on_gpu(
        &mut prover,
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        base_binary_image,
        base_text_section,
        base_non_determinism,
    );
    native_verify_unrolled(build_unrolled_stream(&base_setups, &base_proof), true);
    log::info!(
        "stage 1: base layer proved + verified ({} cycles)",
        base_proof.executed_cycles()
    );

    let base_end_params = compute_end_params(&base_setups, base_proof.final_pc);
    let mut chain = FsvRecursionChain::begin(&base_end_params);

    // === Stages 2-3: unrolled recursion loop. ===
    // Blake modes are env-selectable exactly like the CPU pipeline
    // (RECURSION_UNROLLED_BLAKE / RECURSION_BRIDGE_BLAKE /
    // RECURSION_FINAL_BLAKE). Defaults are blake2_with_compression; the
    // g-function variants can't run here (the JIT lacks that delegation).
    let fsv_dir = artifact_root().join("tools/gkr_verifier");
    let unrolled_blake = unrolled_blake_mode();
    let bridge_blake = bridge_blake_mode();
    let final_blake = final_blake_mode();
    log::info!(
        "blake modes: unrolled={}, bridge={}, final={}",
        unrolled_blake.tag(),
        bridge_blake.tag(),
        final_blake.tag()
    );
    let (unrolled_base_bin, unrolled_base_text) =
        load_fsv_program(&fsv_dir, FsvProgram::UnrolledBaseLayer, unrolled_blake);
    let (unrolled_rec_bin, unrolled_rec_text) =
        load_fsv_program(&fsv_dir, FsvProgram::UnrolledRecursionLayer, unrolled_blake);

    let mut proof = base_proof;
    let mut setups = base_setups;
    let mut input_is_base = true;
    let mut layer = 0u32;

    loop {
        let (program, bin, text) = if input_is_base {
            (
                FsvProgram::UnrolledBaseLayer,
                &unrolled_base_bin,
                &unrolled_base_text,
            )
        } else {
            (
                FsvProgram::UnrolledRecursionLayer,
                &unrolled_rec_bin,
                &unrolled_rec_text,
            )
        };
        let estimated = estimate_verifier_cycles(&proof, program, unrolled_blake)
            .expect("cannot estimate verifier cycles");
        log::info!("layer-{layer} verifier estimates ~{estimated} cycles");
        // Forced first layer (small workloads only): run one unrolled
        // recursion layer even when the base already estimates below the
        // threshold, so the loop machinery is exercised (see caller doc).
        if (layer > 0 || !force_first_layer) && estimated < switch_cycles {
            log::info!("... below {switch_cycles} — switching to the unified machine");
            break;
        }

        let (mut new_proof, new_setups) = prove_on_gpu(
            &mut prover,
            ExecutionKind::Unrolled,
            MachineType::Reduced,
            bin.clone(),
            text.clone(),
            build_unrolled_stream(&setups, &proof),
        );
        new_proof.set_recursion_chain(&chain);
        native_verify_unrolled(build_unrolled_stream(&new_setups, &new_proof), false);
        log::info!(
            "stage 2: unrolled recursion layer {layer} proved + verified ({} cycles)",
            new_proof.executed_cycles()
        );

        let end_params = compute_end_params(&new_setups, new_proof.final_pc);
        chain.extend(&end_params);
        proof = new_proof;
        setups = new_setups;
        input_is_base = false;
        layer += 1;
    }

    // === Stage 4: bridge — the unrolled verifier proved in unified mode
    //     (reloaded in the bridge-selected blake variant, like the CPU flow). ===
    let bridge_program = if input_is_base {
        FsvProgram::UnrolledBaseLayer
    } else {
        FsvProgram::UnrolledRecursionLayer
    };
    let (bridge_bin, bridge_text) = load_fsv_program(&fsv_dir, bridge_program, bridge_blake);
    let (bridge_bin, bridge_text) = (&bridge_bin, &bridge_text);
    let (mut bridge_proof, bridge_setups) = prove_on_gpu(
        &mut prover,
        ExecutionKind::Unified,
        MachineType::Reduced,
        bridge_bin.clone(),
        bridge_text.clone(),
        build_unrolled_stream(&setups, &proof),
    );
    bridge_proof.set_recursion_chain(&chain);
    native_verify_unified(build_unified_stream(&bridge_setups, &bridge_proof), false);
    log::info!(
        "stage 4: bridge proved in unified mode + verified ({} cycles)",
        bridge_proof.executed_cycles()
    );

    let bridge_end_params = compute_end_params(&bridge_setups, bridge_proof.final_pc);
    chain.extend(&bridge_end_params);

    // === Stage 5: final — fsv_unified_recursion_layer in unified mode. ===
    let (final_bin, final_text) =
        load_fsv_program(&fsv_dir, FsvProgram::UnifiedRecursionLayer, final_blake);
    let (mut final_proof, final_setups) = prove_on_gpu(
        &mut prover,
        ExecutionKind::Unified,
        MachineType::Reduced,
        final_bin.clone(),
        final_text.clone(),
        build_unified_stream(&bridge_setups, &bridge_proof),
    );
    final_proof.set_recursion_chain(&chain);
    let output = native_verify_unified(build_unified_stream(&final_setups, &final_proof), false);
    log::info!(
        "stage 5: final unified recursion proof verified ({} cycles); output registers: {output:?}",
        final_proof.executed_cycles()
    );

    // Convergence experiment (opt-in): keep applying the final-blake unified
    // recursion layer to its own proof and watch the cycle count settle at
    // the self-verification fixpoint. RECURSION_EXTRA_FINAL_ROUNDS=N runs N
    // more rounds; re-chaining the same program is a no-op by the chain rule.
    let extra_rounds: u32 = std::env::var("RECURSION_EXTRA_FINAL_ROUNDS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(0);
    let (mut proof, mut setups) = (final_proof, final_setups);
    for round in 0..extra_rounds {
        let end_params = compute_end_params(&setups, proof.final_pc);
        chain.extend(&end_params);
        let (mut new_proof, new_setups) = prove_on_gpu(
            &mut prover,
            ExecutionKind::Unified,
            MachineType::Reduced,
            final_bin.clone(),
            final_text.clone(),
            build_unified_stream(&setups, &proof),
        );
        new_proof.set_recursion_chain(&chain);
        native_verify_unified(build_unified_stream(&new_setups, &new_proof), false);
        log::info!(
            "extra final round {round}: verified ({} cycles)",
            new_proof.executed_cycles()
        );
        proof = new_proof;
        setups = new_setups;
    }
}

gpu_core::force_serial_libtest!();
