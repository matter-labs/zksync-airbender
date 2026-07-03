//! e2e: GPU prove → `ProgramProof` assembly → ND stream → native base-layer
//! verification. Requires both a CUDA device and the `verifiers` feature
//! (heavy verifier build), so the GPU test is doubly gated.

#![allow(unused_imports)]

use crate::upstream::build_unrolled_stream;
use crate::proof_assembly::assemble_program_proof;
use execution_prover::{ExecutionKind, ExecutionProver, ExecutionProverConfiguration, MachineType};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use serial_test::serial;
use setups::read_binary;

fn test_artifact(relative_path: &str) -> std::path::PathBuf {
    // Workspace-root-relative paths; crate is at gpu/program_prover/, so two "..".
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join(relative_path)
}

/// Prove `hashed_fibonacci` (blake2_with_compression build — fires the
/// Blake2WithCompression delegation) on the GPU, assemble the
/// `ProgramProof` + setups map, build the unrolled ND stream, and run the
/// real base-layer verifier natively. First GPU proof through the real
/// verifier.
#[test]
#[cfg(all(not(no_cuda), feature = "verifiers"))]
#[ignore]
#[serial]
fn test_program_prover_base_layer_verify() {
    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Info)
        .try_init();
    let configuration = ExecutionProverConfiguration::default();
    let security_level = configuration.security_level;
    let mut prover = ExecutionProver::with_configuration(configuration).unwrap();
    let (_, binary_image) = read_binary(&test_artifact(
        "examples/hashed_fibonacci/app_blake2_with_compression.bin",
    ));
    let (_, text_section) = read_binary(&test_artifact(
        "examples/hashed_fibonacci/app_blake2_with_compression.text",
    ));
    let handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        binary_image,
        text_section,
        None,
    );
    let non_determinism_source = QuasiUARTSource::new_with_reads(vec![100, 5]);
    let result = prover.commit_memory_and_prove(0, &handle, non_determinism_source);

    let artifacts = prover.program_artifacts(&handle);
    let worker = worker::Worker::new();
    let (proof, setups) = assemble_program_proof(&artifacts, result, security_level, &worker);
    log::info!(
        "assembled ProgramProof: {} cycles, {} riscv families, {} delegation types",
        proof.executed_cycles(),
        proof.riscv_proofs.len(),
        proof.delegation_proofs.len(),
    );

    let stream = build_unrolled_stream(&setups, &proof);
    let output = crate::upstream::native_verify_unrolled(stream, true);
    log::info!("base layer verified natively; output registers: {output:?}");
}

/// Unified counterpart of the base-layer e2e: prove the `multi_family_smoke`
/// workload (same binary + ND inputs as circuit_prover's unified GPU tests,
/// blake2_with_compression variant — the JIT lacks the g-function delegation)
/// with `ExecutionKind::Unified`, assemble the `ProgramProof` (including
/// `num_it_circuits`), build the unified ND stream, and run the real
/// base-layer unified verifier natively.
///
/// This test used to fail the global memory-permutation closure
/// (`read_set_product_accumulator == write_set_product_accumulator`,
/// full_statement_verifier/src/unified_circuit_statement.rs:255). The root
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
#[serial]
fn test_program_prover_unified_base_layer_verify() {
    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Info)
        .try_init();
    let configuration = ExecutionProverConfiguration::default();
    let security_level = configuration.security_level;
    let mut prover = ExecutionProver::with_configuration(configuration).unwrap();
    let (_, binary_image) = read_binary(&test_artifact(
        "examples/multi_family_smoke/app_blake2_with_compression.bin",
    ));
    let (_, text_section) = read_binary(&test_artifact(
        "examples/multi_family_smoke/app_blake2_with_compression.text",
    ));
    let handle = prover.add_binary(
        ExecutionKind::Unified,
        MachineType::Reduced,
        binary_image,
        text_section,
        None,
    );
    let non_determinism_source = QuasiUARTSource::new_with_reads(vec![50, 0xDEAD_BEEF]);
    let result = prover.commit_memory_and_prove(0, &handle, non_determinism_source);

    let artifacts = prover.program_artifacts(&handle);
    let worker = worker::Worker::new();
    let (proof, setups) = assemble_program_proof(&artifacts, result, security_level, &worker);
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

    let stream = crate::upstream::build_unified_stream(&setups, &proof);
    let output = crate::upstream::native_verify_unified(stream, true);
    log::info!("unified base layer verified natively; output registers: {output:?}");
}

/// Unified counterpart of `test_program_prover_cpu_gpu_proof_diff`: prove
/// multi_family_smoke on the CPU reference
/// (`prover_examples::unified::prove_unified_execution_with_replayer`, which
/// asserts internal closure to ONE), verify it natively, then prove on GPU and
/// diff the two `ProgramProof`s field by field. This is the instrument that
/// localized the JIT M31-vs-BabyBear MOP-field divergence behind the closure
/// failure `test_program_prover_unified_base_layer_verify` used to hit.
#[test]
#[cfg(all(not(no_cuda), feature = "verifiers"))]
#[ignore]
#[serial]
fn test_program_prover_unified_cpu_gpu_proof_diff() {
    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Info)
        .try_init();
    let (_, binary_image) = read_binary(&test_artifact(
        "examples/multi_family_smoke/app_blake2_with_compression.bin",
    ));
    let (_, text_section) = read_binary(&test_artifact(
        "examples/multi_family_smoke/app_blake2_with_compression.text",
    ));
    let (_, padded_binary_image) = setups::read_and_pad_binary(&test_artifact(
        "examples/multi_family_smoke/app_blake2_with_compression.bin",
    ));
    let (_, padded_text_section) = setups::read_and_pad_binary(&test_artifact(
        "examples/multi_family_smoke/app_blake2_with_compression.text",
    ));
    let worker = worker::Worker::new_with_num_threads(8);
    let configuration = ExecutionProverConfiguration::default();
    let security_level = configuration.security_level;

    let (cpu_proof, cpu_setups) =
        prover_examples::unified::prove_unified_execution_with_replayer::<std::alloc::Global>(
            1 << 31,
            &padded_binary_image,
            &padded_text_section,
            true,
            QuasiUARTSource::new_with_reads(vec![50, 0xDEAD_BEEF]),
            1 << 30,
            &worker,
            security_level,
            0,
        );
    log::info!("CPU reference proved (internal closure passed); verifying natively");
    let cpu_output = crate::upstream::native_verify_unified(
        crate::upstream::build_unified_stream(&cpu_setups, &cpu_proof),
        true,
    );
    log::info!("CPU reference verifies; output registers: {cpu_output:?}");

    // GPU flow.
    let mut prover = ExecutionProver::with_configuration(configuration).unwrap();
    let handle = prover.add_binary(
        ExecutionKind::Unified,
        MachineType::Reduced,
        binary_image,
        text_section,
        None,
    );
    let result = prover.commit_memory_and_prove(
        0,
        &handle,
        QuasiUARTSource::new_with_reads(vec![50, 0xDEAD_BEEF]),
    );
    let artifacts = prover.program_artifacts(&handle);
    let (gpu_proof, _gpu_setups) =
        assemble_program_proof(&artifacts, result, security_level, &worker);

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
/// (`prover_examples::prove_unrolled_execution_with_replayer`), sanity-verify
/// the CPU proof natively, then diff the CPU-assembled `(ProgramProof, Setups)`
/// against the GPU-assembled pair field by field to localize any divergence.
#[test]
#[cfg(all(not(no_cuda), feature = "verifiers"))]
#[ignore]
#[serial]
fn test_program_prover_cpu_gpu_proof_diff() {
    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Info)
        .try_init();
    let (_, binary_image) = read_binary(&test_artifact(
        "examples/hashed_fibonacci/app_blake2_with_compression.bin",
    ));
    let (_, text_section) = read_binary(&test_artifact(
        "examples/hashed_fibonacci/app_blake2_with_compression.text",
    ));

    // CPU reference (params mirror prover_examples::recursion's base layer,
    // including the ROM-word padding its `load_program` applies).
    let (_, padded_binary_image) = setups::read_and_pad_binary(&test_artifact(
        "examples/hashed_fibonacci/app_blake2_with_compression.bin",
    ));
    let (_, padded_text_section) = setups::read_and_pad_binary(&test_artifact(
        "examples/hashed_fibonacci/app_blake2_with_compression.text",
    ));
    let worker = worker::Worker::new_with_num_threads(8);
    let (cpu_proof, cpu_setups) = prover_examples::unrolled::prove_unrolled_execution_with_replayer::<
        riscv_transpiler::cycle::IMStandardIsaConfigUnsignedMulDivOnly,
        std::alloc::Global,
    >(
        1 << 31,
        &padded_binary_image,
        &padded_text_section,
        true,
        QuasiUARTSource::new_with_reads(vec![100, 5]),
        1 << 30,
        &worker,
        crate::upstream::SecurityLevel::Sec80,
        0,
    );
    log::info!("CPU reference proved; verifying natively");
    let cpu_output = crate::upstream::native_verify_unrolled(
        build_unrolled_stream(&cpu_setups, &cpu_proof),
        true,
    );
    log::info!("CPU reference verifies; output registers: {cpu_output:?}");

    // GPU flow.
    let configuration = ExecutionProverConfiguration::default();
    let security_level = configuration.security_level;
    let mut prover = ExecutionProver::with_configuration(configuration).unwrap();
    let handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        binary_image,
        text_section,
        None,
    );
    let result =
        prover.commit_memory_and_prove(0, &handle, QuasiUARTSource::new_with_reads(vec![100, 5]));
    let artifacts = prover.program_artifacts(&handle);
    let (gpu_proof, gpu_setups) =
        assemble_program_proof(&artifacts, result, security_level, &worker);

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
/// recursion-layer proof natively. This is the first time an fsv binary
/// (which uses pr-332's tri-add / xor-rot special opcodes) runs through the
/// JIT simulator + GPU prover — a decode gap in the JIT would surface here.
///
/// Mirrors one iteration of `prover_examples::recursion`'s unrolled-recursion
/// loop: chain fields come from `begin_chain(compute_end_params(base))`, and
/// the recursion-layer verify runs with `is_base = false` (reads the chain
/// preimage from the stream).
#[test]
#[cfg(all(not(no_cuda), feature = "verifiers"))]
#[ignore]
#[serial]
fn test_program_prover_recursion_layer_verify() {
    use crate::upstream::{compute_end_params, native_verify_unrolled, FsvRecursionChain};

    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Info)
        .try_init();
    let configuration = ExecutionProverConfiguration::default();
    let security_level = configuration.security_level;
    let mut prover = ExecutionProver::with_configuration(configuration).unwrap();
    let worker = worker::Worker::new();

    // Stage 1: base layer (identical to test_program_prover_base_layer_verify).
    let (_, binary_image) = read_binary(&test_artifact(
        "examples/hashed_fibonacci/app_blake2_with_compression.bin",
    ));
    let (_, text_section) = read_binary(&test_artifact(
        "examples/hashed_fibonacci/app_blake2_with_compression.text",
    ));
    let base_handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        binary_image,
        text_section,
        None,
    );
    let result = prover.commit_memory_and_prove(
        0,
        &base_handle,
        QuasiUARTSource::new_with_reads(vec![100, 5]),
    );
    let artifacts = prover.program_artifacts(&base_handle);
    let (base_proof, base_setups) =
        assemble_program_proof(&artifacts, result, security_level, &worker);
    native_verify_unrolled(build_unrolled_stream(&base_setups, &base_proof), true);
    log::info!(
        "base layer proved on GPU + verified natively ({} cycles)",
        base_proof.executed_cycles()
    );

    let base_end_params = compute_end_params(&base_setups, base_proof.final_pc);
    let chain = FsvRecursionChain::begin(&base_end_params);

    // Stage 2: prove the fsv base-layer verifier over the base proof's stream.
    let (_, fsv_binary) = read_binary(&test_artifact(
        "tools/gkr_verifier/fsv_unrolled_base_layer_sec_80_blake2_with_compression.bin",
    ));
    let (_, fsv_text) = read_binary(&test_artifact(
        "tools/gkr_verifier/fsv_unrolled_base_layer_sec_80_blake2_with_compression.text",
    ));
    let fsv_handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::Reduced,
        fsv_binary,
        fsv_text,
        None,
    );
    let stream = build_unrolled_stream(&base_setups, &base_proof);
    let result = prover.commit_memory_and_prove(
        0,
        &fsv_handle,
        QuasiUARTSource::new_with_reads(stream),
    );
    let artifacts = prover.program_artifacts(&fsv_handle);
    let (mut recursion_proof, recursion_setups) =
        assemble_program_proof(&artifacts, result, security_level, &worker);
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

/// Full GPU recursion ladder, mirroring `prover_examples::recursion`'s
/// `test_recursive_proving_pipeline_zksync_os` but with our test workload
/// (hashed_fibonacci) and every proof produced by the GPU `ExecutionProver`:
///
///   base (unrolled, full-unsigned ISA)
///   → unrolled recursion loop (reduced ISA, fsv verifier binaries)
///   → bridge (the unrolled verifier proved in UNIFIED mode)
///   → final (fsv_unified_recursion_layer, unified mode)
///
/// with the recursion hash chain threaded through and every rung verified
/// natively. Deviation from the CPU pipeline: the base workload is tiny
/// (~1.7k cycles), so the layer-0 verifier measures far below the unified
/// switch threshold and the CPU flow would bridge immediately; we force one
/// unrolled rung first so the loop machinery (measure → prove → chain) is
/// exercised, then bridge over the recursion proof. Blake modes are fixed to
/// blake2_with_compression (the JIT lacks the g-function delegation).
#[test]
#[cfg(all(not(no_cuda), feature = "verifiers"))]
#[ignore]
#[serial]
fn test_program_prover_recursive_pipeline() {
    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Info)
        .try_init();
    let (_, binary_image) = read_binary(&test_artifact(
        "examples/hashed_fibonacci/app_blake2_with_compression.bin",
    ));
    let (_, text_section) = read_binary(&test_artifact(
        "examples/hashed_fibonacci/app_blake2_with_compression.text",
    ));
    run_gpu_recursive_pipeline(binary_image, text_section, vec![100, 5], true);
}

/// The real thing: the recursion ladder over the zksync_os block workload —
/// the GPU analogue of `test_recursive_proving_pipeline_zksync_os` (heavy;
/// the base layer proves a full zksync_os block). The base measures well
/// above the unified-switch threshold, so the unrolled recursion loop runs
/// its natural course (no forced rung). Threshold overridable via
/// `RECURSION_UNIFIED_SWITCH_CYCLES` like the CPU pipeline.
#[test]
#[cfg(all(not(no_cuda), feature = "verifiers"))]
#[ignore]
#[serial]
fn test_program_prover_recursive_pipeline_zksync_os() {
    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Info)
        .try_init();
    // Mirrors prover_examples::recursion::read_hex_witness.
    let raw = std::fs::read_to_string(test_artifact(
        "riscv_transpiler/examples/zksync_os/23620012_witness",
    ))
    .expect("read witness file");
    let raw = raw.trim();
    assert!(raw.len() % 8 == 0);
    let witness: Vec<u32> = raw
        .as_bytes()
        .chunks(8)
        .map(|c| u32::from_str_radix(std::str::from_utf8(c).unwrap(), 16).expect("invalid hex"))
        .collect();
    let (_, binary_image) =
        read_binary(&test_artifact("riscv_transpiler/examples/zksync_os/app.bin"));
    let (_, text_section) =
        read_binary(&test_artifact("riscv_transpiler/examples/zksync_os/app.text"));
    run_gpu_recursive_pipeline(binary_image, text_section, witness, false);
}

#[cfg(all(not(no_cuda), feature = "verifiers"))]
fn run_gpu_recursive_pipeline(
    base_binary_image: Vec<u32>,
    base_text_section: Vec<u32>,
    base_non_determinism: Vec<u32>,
    force_first_rung: bool,
) {
    use crate::upstream::{
        build_unified_stream, compute_end_params, native_verify_unified, native_verify_unrolled,
        unified_switch_cycles, FsvRecursionChain,
    };
    use crate::upstream::{INITIAL_TIMESTAMP, TIMESTAMP_STEP};

    // Mirrors prover_examples::recursion's private bounds.
    const UNROLLED_RECURSION_CYCLES_BOUND: usize = 1 << 28;
    const RAM_BOUND: usize = 1 << 30;

    fn fsv(name: &str) -> (Vec<u32>, Vec<u32>) {
        let (_, bin) = read_binary(&test_artifact(&format!("tools/gkr_verifier/{name}.bin")));
        let (_, text) = read_binary(&test_artifact(&format!("tools/gkr_verifier/{name}.text")));
        (bin, text)
    }

    // Mirrors prover_examples::recursion::measure_verifier_cycles (which wraps
    // run_unrolled_machine_in_full — calling that across crates trips a rustc
    // E0391 normalization cycle on its const-generic return type, so the
    // reduced-machine VM run is inlined here).
    fn measure_verifier_cycles(bin: &[u32], text: &[u32], stream: Vec<u32>) -> u64 {
        use prover::field::baby_bear::base::BabyBearField;
        use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, Instruction};
        use riscv_transpiler::ir::ReducedMachineDecoderConfig;
        use riscv_transpiler::vm::{
            DelegationsAndUnifiedCounters, RamWithRomRegion, SimpleSnapshotter, SimpleTape,
            State, VM,
        };
        const ROM_BITS: usize = common_constants::ROM_SECOND_WORD_BITS;

        let instructions: Vec<Instruction> =
            preprocess_bytecode::<ReducedMachineDecoderConfig, true>(text);
        let tape = SimpleTape::new(&instructions);
        let mut ram = RamWithRomRegion::<ROM_BITS>::from_rom_content(bin, RAM_BOUND);
        let mut state = State::initial_with_counters(DelegationsAndUnifiedCounters::default());
        let mut snapshotter =
            SimpleSnapshotter::<DelegationsAndUnifiedCounters, ROM_BITS>::new_with_cycle_limit(
                UNROLLED_RECURSION_CYCLES_BOUND,
                state,
            );
        let mut non_determinism = QuasiUARTSource::new_with_reads(stream);
        let finished = VM::<DelegationsAndUnifiedCounters>::run_basic_unrolled::<
            _,
            _,
            _,
            BabyBearField,
        >(
            &mut state,
            &mut ram,
            &mut snapshotter,
            &tape,
            UNROLLED_RECURSION_CYCLES_BOUND,
            &mut non_determinism,
        );
        assert!(finished, "verifier program must reach its end state");
        (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP
    }

    let switch_cycles = unified_switch_cycles();

    let configuration = ExecutionProverConfiguration::default();
    let security_level = configuration.security_level;
    let mut prover = ExecutionProver::with_configuration(configuration).unwrap();
    let worker = worker::Worker::new();

    // === Stage 1: base layer. ===
    let base_handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        base_binary_image,
        base_text_section,
        None,
    );
    let result = prover.commit_memory_and_prove(
        0,
        &base_handle,
        QuasiUARTSource::new_with_reads(base_non_determinism),
    );
    let artifacts = prover.program_artifacts(&base_handle);
    let (base_proof, base_setups) =
        assemble_program_proof(&artifacts, result, security_level, &worker);
    native_verify_unrolled(build_unrolled_stream(&base_setups, &base_proof), true);
    log::info!("stage 1: base layer proved + verified ({} cycles)", base_proof.executed_cycles());

    let base_end_params = compute_end_params(&base_setups, base_proof.final_pc);
    let mut chain = FsvRecursionChain::begin(&base_end_params);

    // === Stages 2-3: unrolled recursion loop. ===
    let (unrolled_base_bin, unrolled_base_text) =
        fsv("fsv_unrolled_base_layer_sec_80_blake2_with_compression");
    let (unrolled_rec_bin, unrolled_rec_text) =
        fsv("fsv_unrolled_recursion_layer_sec_80_blake2_with_compression");

    let mut proof = base_proof;
    let mut setups = base_setups;
    let mut input_is_base = true;
    let mut layer = 0u32;

    loop {
        let (bin, text) = if input_is_base {
            (&unrolled_base_bin, &unrolled_base_text)
        } else {
            (&unrolled_rec_bin, &unrolled_rec_text)
        };
        let measured =
            measure_verifier_cycles(bin, text, build_unrolled_stream(&setups, &proof));
        log::info!("layer-{layer} verifier measures {measured} cycles");
        // Forced first rung (small workloads only): run one unrolled
        // recursion layer even when the base already measures below the
        // threshold, so the loop machinery is exercised (see caller doc).
        if (layer > 0 || !force_first_rung) && measured < switch_cycles {
            log::info!("... below {switch_cycles} — switching to the unified machine");
            break;
        }

        let fsv_handle = prover.add_binary(
            ExecutionKind::Unrolled,
            MachineType::Reduced,
            bin.clone(),
            text.clone(),
            None,
        );
        let result = prover.commit_memory_and_prove(
            0,
            &fsv_handle,
            QuasiUARTSource::new_with_reads(build_unrolled_stream(&setups, &proof)),
        );
        let artifacts = prover.program_artifacts(&fsv_handle);
        let (mut new_proof, new_setups) =
            assemble_program_proof(&artifacts, result, security_level, &worker);
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

    // === Stage 4: bridge — the unrolled verifier proved in unified mode. ===
    let (bridge_bin, bridge_text) = if input_is_base {
        (&unrolled_base_bin, &unrolled_base_text)
    } else {
        (&unrolled_rec_bin, &unrolled_rec_text)
    };
    let bridge_handle = prover.add_binary(
        ExecutionKind::Unified,
        MachineType::Reduced,
        bridge_bin.clone(),
        bridge_text.clone(),
        None,
    );
    let result = prover.commit_memory_and_prove(
        0,
        &bridge_handle,
        QuasiUARTSource::new_with_reads(build_unrolled_stream(&setups, &proof)),
    );
    let artifacts = prover.program_artifacts(&bridge_handle);
    let (mut bridge_proof, bridge_setups) =
        assemble_program_proof(&artifacts, result, security_level, &worker);
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
        fsv("fsv_unified_recursion_layer_sec_80_blake2_with_compression");
    let final_handle = prover.add_binary(
        ExecutionKind::Unified,
        MachineType::Reduced,
        final_bin,
        final_text,
        None,
    );
    let result = prover.commit_memory_and_prove(
        0,
        &final_handle,
        QuasiUARTSource::new_with_reads(build_unified_stream(&bridge_setups, &bridge_proof)),
    );
    let artifacts = prover.program_artifacts(&final_handle);
    let (mut final_proof, final_setups) =
        assemble_program_proof(&artifacts, result, security_level, &worker);
    final_proof.set_recursion_chain(&chain);
    let output = native_verify_unified(build_unified_stream(&final_setups, &final_proof), false);
    log::info!(
        "stage 5: final unified recursion proof verified ({} cycles); output registers: {output:?}",
        final_proof.executed_cycles()
    );
}
