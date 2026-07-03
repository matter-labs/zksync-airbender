//! e2e: GPU prove → `ProgramProof` assembly → ND stream → native base-layer
//! verification. Requires both a CUDA device and the `verifiers` feature
//! (heavy verifier build), so the GPU test is doubly gated.

#![allow(unused_imports)]

use crate::interim_upstream::{build_unrolled_stream, proof_cycles};
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
        proof_cycles(&proof),
        proof.riscv_proofs.len(),
        proof.delegation_proofs.len(),
    );

    let stream = build_unrolled_stream(&setups, &proof);
    let output = crate::interim_upstream::native_verify_unrolled(stream, true);
    log::info!("base layer verified natively; output registers: {output:?}");
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
    let cpu_output = crate::interim_upstream::native_verify_unrolled(
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
        crate::interim_upstream::compute_end_params(&cpu_setups, cpu_proof.final_pc),
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
