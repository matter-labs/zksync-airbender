// `Global` is unstable, and an integration test is its own crate root.
#![feature(allocator_api)]

//! Program-level GPU end-to-end tests: GPU prove -> `ProgramProof` assembly ->
//! ND stream -> native verification.
//!
//! Requires a CUDA device AND the `verifiers` feature (the verifier build is
//! heavy), so these are doubly gated.

// Most items here are used under only one of the two gates.
#![allow(unused_imports)]

mod upstream {
    //! Single-file audit point for items this suite consumes from upstream
    //! crates (`full_statement_verifier`, `prover`, `setups`,
    //! `verifier_common`), as in `gpu_execution_prover::upstream`.

    // `full_statement_verifier` — the program-level proof container.
    pub use full_statement_verifier::program_proof::ProgramProof;

    // `prover` — definitions consumed by tests only.
    pub use prover::definitions::SecurityLevel;

    // Recursion protocol helpers, from upstream library code.
    pub use full_statement_verifier::host_utils::cost_model::estimate_verifier_cycles;
    pub use full_statement_verifier::host_utils::{
        bridge_blake_mode, build_unified_stream, build_unrolled_stream, compute_end_params,
        final_blake_mode, load_fsv_program, unified_switch_cycles, unrolled_blake_mode,
        FsvRecursionChain,
    };
    #[cfg(feature = "verifiers")]
    pub use full_statement_verifier::host_utils::{native_verify_unified, native_verify_unrolled};
    pub use setups::Setups;
    pub use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};
}

use crate::upstream::build_unrolled_stream;
use gpu_execution_prover::{
    ExecutionKind, ExecutionProver, ExecutionProverConfiguration, MachineType,
};
use program_prover::assemble_program_proof;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use setups::read_binary;

/// Workspace root for test fixtures; this crate is at `gpu/execution_prover/`.
///
/// `AB_TEST_ARTIFACT_ROOT` wins when set, because `CARGO_MANIFEST_DIR` is
/// baked in at BUILD time: a test binary copied to another machine resolves
/// the builder's path, not the checkout it is running against.
#[cfg(feature = "verifiers")]
fn artifact_root() -> std::path::PathBuf {
    if let Ok(root) = std::env::var("AB_TEST_ARTIFACT_ROOT") {
        return std::path::PathBuf::from(root);
    }
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
}

/// Idempotent `env_logger` init shared by every e2e below.
#[cfg(feature = "verifiers")]
fn init_test_logger() {
    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Info)
        .try_init();
}

/// Load the `blake2_with_compression` build of an `examples/<name>` workload as
/// `(binary_image, text_section)`.
#[cfg(feature = "verifiers")]
fn load_workload(name: &str) -> (Vec<u32>, Vec<u32>) {
    let artifact_root = artifact_root();
    let (_, binary_image) = read_binary(
        &artifact_root.join(format!("examples/{name}/app_blake2_with_compression.bin")),
    );
    let (_, text_section) = read_binary(
        &artifact_root.join(format!("examples/{name}/app_blake2_with_compression.text")),
    );
    (binary_image, text_section)
}

#[cfg(feature = "verifiers")]
fn load_zksync_os_workload() -> (Vec<u32>, Vec<u32>, Vec<u32>) {
    let root = artifact_root();
    let raw =
        std::fs::read_to_string(root.join("riscv_transpiler/examples/zksync_os/23620012_witness"))
            .expect("read zkSync OS block-23620012 witness");
    let raw = raw.trim();
    assert!(raw.len().is_multiple_of(8));
    let witness = raw
        .as_bytes()
        .chunks(8)
        .map(|chunk| {
            u32::from_str_radix(std::str::from_utf8(chunk).unwrap(), 16)
                .expect("invalid zkSync OS witness word")
        })
        .collect();
    let (_, binary_image) = read_binary(&root.join("riscv_transpiler/examples/zksync_os/app.bin"));
    let (_, text_section) = read_binary(&root.join("riscv_transpiler/examples/zksync_os/app.text"));
    (binary_image, text_section, witness)
}

#[cfg(all(feature = "verifiers", feature = "deterministic_pow"))]
fn write_compressed<T: serde::Serialize>(value: &T, path: &std::path::Path) {
    assert!(!path.exists(), "refusing to overwrite {}", path.display());
    let file_name = path.file_name().unwrap().to_string_lossy();
    let temporary = path.with_file_name(format!(".{file_name}.tmp"));
    let file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary)
        .unwrap_or_else(|err| panic!("create {}: {err}", temporary.display()));
    let mut encoder = flate2::write::ZlibEncoder::new(file, flate2::Compression::default());
    bincode::serialize_into(&mut encoder, value).expect("serialize calibration fixture");
    let file = encoder.finish().expect("finish fixture compression");
    file.sync_all().expect("sync calibration fixture");
    std::fs::rename(&temporary, path).unwrap_or_else(|err| {
        panic!(
            "rename {} to {}: {err}",
            temporary.display(),
            path.display()
        )
    });
}

#[cfg(all(feature = "verifiers", feature = "deterministic_pow"))]
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

/// Prove `(binary_image, text_section)` with the given non-determinism reads
/// on the GPU `ExecutionProver` and assemble the `(ProgramProof, Setups)`.
/// Callers apply their own `set_recursion_chain` / native verify.
#[cfg(feature = "verifiers")]
fn prove_on_gpu(
    prover: &mut ExecutionProver,
    kind: ExecutionKind,
    machine: MachineType,
    binary_image: Vec<u32>,
    text_section: Vec<u32>,
    reads: Vec<u32>,
) -> (crate::upstream::ProgramProof, crate::upstream::Setups) {
    let handle = prover.add_binary(kind, machine, binary_image, text_section, None);
    let result = prover.commit_memory_and_prove(0, &handle, QuasiUARTSource::new_with_reads(reads));
    let artifacts = prover.program_artifacts(&handle);
    assemble_program_proof(&artifacts, result)
}

/// Prove `hashed_fibonacci` (blake2_with_compression build) on the GPU,
/// assemble the `ProgramProof` + setups map, build the unrolled ND stream and
/// run the real base-layer verifier natively.
#[test]
#[cfg(feature = "verifiers")]
#[ignore]
fn test_program_prover_base_layer_verify() {
    init_test_logger();
    let configuration = ExecutionProverConfiguration::default();
    let mut prover = ExecutionProver::with_configuration(configuration).unwrap();
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

    let stream = build_unrolled_stream(&setups, &proof);
    let output = crate::upstream::native_verify_unrolled(stream, true);
    log::info!("base layer verified natively; output registers: {output:?}");
}

/// Prove the `multi_family_smoke` blake2_with_compression workload with
/// `ExecutionKind::Unified` and verify the assembled proof natively.
///
/// The global memory-permutation closure this verifier checks is the only
/// thing that catches a simulation whose final registers / RAM diverge from
/// the traced witness: the per-circuit proofs stay self-consistent.
#[test]
#[cfg(feature = "verifiers")]
#[ignore]
fn test_program_prover_unified_base_layer_verify() {
    init_test_logger();
    let configuration = ExecutionProverConfiguration::default();
    let mut prover = ExecutionProver::with_configuration(configuration).unwrap();
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

    let stream = crate::upstream::build_unified_stream(&setups, &proof);
    let output = crate::upstream::native_verify_unified(stream, true);
    log::info!("unified base layer verified natively; output registers: {output:?}");
}

/// Unified counterpart of `test_program_prover_cpu_gpu_proof_diff`: prove
/// multi_family_smoke on the CPU reference
/// (`program_prover::unified::prove_unified_execution_with_replayer`, which
/// asserts internal closure to ONE), verify it natively, then prove on GPU and
/// diff the two `ProgramProof`s field by field.
#[test]
#[cfg(feature = "verifiers")]
#[ignore]
fn test_program_prover_unified_cpu_gpu_proof_diff() {
    init_test_logger();
    let (binary_image, text_section) = load_workload("multi_family_smoke");
    let artifact_root = artifact_root();
    let (_, padded_binary_image) = setups::read_and_pad_binary(
        &artifact_root.join("examples/multi_family_smoke/app_blake2_with_compression.bin"),
    );
    let (_, padded_text_section) = setups::read_and_pad_binary(
        &artifact_root.join("examples/multi_family_smoke/app_blake2_with_compression.text"),
    );
    let worker = worker::Worker::new_with_num_threads(8);
    let configuration = ExecutionProverConfiguration::default();
    let security_level = configuration.security_level;

    let (cpu_proof, cpu_setups) =
        program_prover::unified::prove_unified_execution_with_replayer::<std::alloc::Global, _, _>(
            1 << 31,
            &padded_binary_image,
            &padded_text_section,
            true,
            QuasiUARTSource::new_with_reads(vec![50, 0xDEAD_BEEF]),
            1 << 30,
            &worker,
            security_level,
            // From the constant, so it cannot drift from the shared and GPU
            // configurations; the verifier's transcript rejects any other value.
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
    let mut prover = ExecutionProver::with_configuration(configuration).unwrap();
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
/// (`program_prover::prove_unrolled_execution_with_replayer`), verify that
/// natively, then diff the two assembled `(ProgramProof, Setups)` pairs field
/// by field to localize any divergence.
#[test]
#[cfg(feature = "verifiers")]
#[ignore]
fn test_program_prover_cpu_gpu_proof_diff() {
    init_test_logger();
    let (binary_image, text_section) = load_workload("hashed_fibonacci");

    // CPU reference (params mirror prover_examples::recursion's base layer,
    // including the ROM-word padding its `load_program` applies).
    let (_, padded_binary_image) = setups::read_and_pad_binary(
        &artifact_root().join("examples/hashed_fibonacci/app_blake2_with_compression.bin"),
    );
    let (_, padded_text_section) = setups::read_and_pad_binary(
        &artifact_root().join("examples/hashed_fibonacci/app_blake2_with_compression.text"),
    );
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
    let mut prover = ExecutionProver::with_configuration(configuration).unwrap();
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
    // Dumped before any assert below can fire: regenerating the pair costs a
    // ~17-minute CPU prove.
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

    // Per-family proof counts (missing entry == empty entry).
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
/// `fsv_unrolled_base_layer` verifier program on the GPU over the base-layer
/// `ProgramProof`'s ND stream, then verify that recursion-layer proof
/// natively. A JIT decode gap in the fsv special opcodes (tri-add, xor-rot)
/// surfaces here.
///
/// Mirrors one iteration of `prover_examples::recursion`'s unrolled-recursion
/// loop: chain fields come from `begin_chain(compute_end_params(base))`, and
/// the recursion-layer verify runs with `is_base = false`.
#[test]
#[cfg(feature = "verifiers")]
#[ignore]
fn test_program_prover_recursion_layer_verify() {
    use crate::upstream::{compute_end_params, native_verify_unrolled, FsvRecursionChain};

    init_test_logger();
    let configuration = ExecutionProverConfiguration::default();
    let mut prover = ExecutionProver::with_configuration(configuration).unwrap();

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
    let (_, fsv_binary) = read_binary(
        &artifact_root()
            .join("tools/gkr_verifier/fsv_unrolled_base_layer_sec_100_blake2_with_compression.bin"),
    );
    let (_, fsv_text) =
        read_binary(&artifact_root().join(
            "tools/gkr_verifier/fsv_unrolled_base_layer_sec_100_blake2_with_compression.text",
        ));
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
/// natively. The base workload is tiny (~1.7k cycles), so the layer-0
/// verifier estimates far below the unified switch threshold; one unrolled
/// layer is forced first so the loop machinery runs at all. Blake modes are
/// env-selectable like the CPU pipeline (default blake2_with_compression;
/// the g-function variants need a JIT delegation that doesn't exist).
#[test]
#[cfg(feature = "verifiers")]
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
#[cfg(feature = "verifiers")]
#[ignore]
fn test_program_prover_recursive_pipeline_zksync_os() {
    init_test_logger();
    let (binary_image, text_section, witness) = load_zksync_os_workload();
    run_gpu_recursive_pipeline(binary_image, text_section, witness, false);
}

/// Generate the local, non-authoritative proof/setup inputs used to calibrate
/// the Sec100 Compression verifier cost model. Deliberately proves two
/// recursion layers instead of consulting the production threshold.
#[test]
#[cfg(all(feature = "verifiers", feature = "deterministic_pow"))]
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
    for name in [
        "base",
        "base_alt",
        "recursion0",
        "recursion1",
        "memory_windows",
    ] {
        for suffix in ["proof", "setups"] {
            let path = fixture_dir.join(format!("{name}_{suffix}.bin"));
            assert!(!path.exists(), "refusing to overwrite {}", path.display());
        }
    }

    let configuration = ExecutionProverConfiguration {
        security_level: SecurityLevel::Sec100,
        ..Default::default()
    };
    let mut prover = ExecutionProver::with_configuration(configuration).unwrap();

    let (base_binary, base_text, base_witness) = load_zksync_os_workload();
    let (base_proof, base_setups) = prove_on_gpu(
        &mut prover,
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        base_binary,
        base_text,
        base_witness,
    );
    native_verify_unrolled(build_unrolled_stream(&base_setups, &base_proof), true);
    write_cost_model_fixture(&fixture_dir, "base", &base_proof, &base_setups);

    let base_end_params = compute_end_params(&base_setups, base_proof.final_pc);
    let mut chain = FsvRecursionChain::begin(&base_end_params);
    let fsv_dir = artifact_root().join("tools/gkr_verifier");
    let (base_verifier_bin, base_verifier_text) = load_fsv_program(
        &fsv_dir,
        FsvProgram::UnrolledBaseLayer,
        BlakeMode::Compression,
    );
    let (mut recursion0_proof, recursion0_setups) = prove_on_gpu(
        &mut prover,
        ExecutionKind::Unrolled,
        MachineType::Reduced,
        base_verifier_bin,
        base_verifier_text,
        build_unrolled_stream(&base_setups, &base_proof),
    );
    recursion0_proof.set_recursion_chain(&chain);
    native_verify_unrolled(
        build_unrolled_stream(&recursion0_setups, &recursion0_proof),
        false,
    );
    write_cost_model_fixture(
        &fixture_dir,
        "recursion0",
        &recursion0_proof,
        &recursion0_setups,
    );

    let recursion0_end_params = compute_end_params(&recursion0_setups, recursion0_proof.final_pc);
    chain.extend(&recursion0_end_params);
    let (recursion_verifier_bin, recursion_verifier_text) = load_fsv_program(
        &fsv_dir,
        FsvProgram::UnrolledRecursionLayer,
        BlakeMode::Compression,
    );
    let (mut recursion1_proof, recursion1_setups) = prove_on_gpu(
        &mut prover,
        ExecutionKind::Unrolled,
        MachineType::Reduced,
        recursion_verifier_bin,
        recursion_verifier_text,
        build_unrolled_stream(&recursion0_setups, &recursion0_proof),
    );
    recursion1_proof.set_recursion_chain(&chain);
    native_verify_unrolled(
        build_unrolled_stream(&recursion1_setups, &recursion1_proof),
        false,
    );
    write_cost_model_fixture(
        &fixture_dir,
        "recursion1",
        &recursion1_proof,
        &recursion1_setups,
    );

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

    // Touch one more window than a single i&t proof can carry.
    let mut memory_binary = Vec::new();
    let window_bits =
        setups::inits_and_teardowns::TRACE_LEN_LOG2 + setups::inits_and_teardowns::WORD_BITS;
    for window in 0..=setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS {
        let address =
            ((window << window_bits) as u32).max(common_constants::rom::ROM_BYTE_SIZE as u32);
        memory_binary.push(address | (5 << 7) | 0x37); // lui x5, address >> 12
        memory_binary.push(0x0052_a023); // sw x5, 0(x5)
    }
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
}

#[cfg(feature = "verifiers")]
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
    let mut prover = ExecutionProver::with_configuration(configuration).unwrap();

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
    // RECURSION_UNROLLED_BLAKE / RECURSION_BRIDGE_BLAKE / RECURSION_FINAL_BLAKE
    // select the blake mode, exactly as in the CPU pipeline.
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
        // Forced first layer: run one unrolled recursion layer even when the
        // base already estimates below the threshold (see caller doc).
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

    // Convergence experiment: RECURSION_EXTRA_FINAL_ROUNDS=N keeps applying
    // the final-blake unified recursion layer to its own proof, settling at
    // the self-verification fixpoint. Re-chaining the same program is a no-op.
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
