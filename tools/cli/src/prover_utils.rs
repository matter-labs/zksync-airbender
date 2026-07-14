use clap::ValueEnum;
use execution_utils::setups::{
    binary_u8_to_u32, get_unified_circuit_artifact_for_machine_type,
    get_unrolled_circuits_artifacts_for_machine_type, pad_bytecode_bytes_for_proving,
    pad_bytecode_for_proving, read_binary,
};
use execution_utils::unified_circuit::verify_proof_in_unified_layer;
use execution_utils::unified_circuit::{
    compute_unified_setup_for_machine_configuration,
    flatten_proof_into_responses_for_unified_recursion,
    prove_unified_for_machine_configuration_into_program_proof,
};
use execution_utils::unrolled::verify_unrolled_layer_proof;
use execution_utils::unrolled::{
    compute_setup_for_machine_configuration, flatten_proof_into_responses_for_unrolled_recursion,
    prove_unrolled_for_machine_configuration_into_program_proof, UnrolledProgramProof,
    UnrolledProgramSetup,
};
#[cfg(feature = "gpu")]
use execution_utils::unrolled_gpu::{
    UnifiedRecursionProverHostState, UnrolledProver, UnrolledProverLevel,
};
use execution_utils::verifier_binaries::recursion_artifact;
use execution_utils::{RecursionArtifact, RecursionLayer};
use prover::transcript::Blake2sBufferingTranscript;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::cycle::{
    IMStandardIsaConfigWithUnsignedMulDiv, IWithoutByteAccessIsaConfigWithDelegation,
};
use serde::{Deserialize, Serialize};
use sha3::{Digest, Keccak256};
use std::path::{Path, PathBuf};
use std::time::Instant;

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, ValueEnum)]
pub enum SecurityLevel {
    #[value(name = "80")]
    Security80,
    #[value(name = "100")]
    Security100,
}

impl SecurityLevel {
    pub const fn model(self) -> verifier_common::SecurityModel {
        match self {
            Self::Security80 => verifier_common::SecurityModel::Security80,
            Self::Security100 => verifier_common::SecurityModel::Security100,
        }
    }

    pub const fn unified_recursion_target_family_proofs(self) -> usize {
        match self {
            Self::Security80 => 1,
            Self::Security100 => 2,
        }
    }

    pub const fn unified_recursion_has_converged(self, family_proof_count: usize) -> bool {
        family_proof_count == self.unified_recursion_target_family_proofs()
    }
}

impl Default for SecurityLevel {
    fn default() -> Self {
        Self::Security80
    }
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, ValueEnum)]
pub enum ProofTarget {
    Base,
    RecursionUnrolled,
    RecursionUnified,
    /// Multiple recursion-unified proofs of the same program combined into one
    /// proof. Words 0..8 of the output are the keccak rolling hash of the
    /// combined proofs' outputs; words 8..16 carry the shared recursion chain.
    RecursionCombined,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, ValueEnum)]
pub enum ProverBackend {
    Cpu,
    Gpu,
}

#[derive(Clone, Debug)]
pub struct CpuConfig {
    pub cycles_bound: usize,
    pub ram_bound: usize,
    pub worker_threads: Option<usize>,
}

impl Default for CpuConfig {
    fn default() -> Self {
        Self {
            cycles_bound: 1 << 31,
            ram_bound: 1 << 30,
            worker_threads: None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct GpuConfig {
    pub replay_worker_threads_count: usize,
}

impl Default for GpuConfig {
    fn default() -> Self {
        Self {
            replay_worker_threads_count: 8,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ProgramProverConfig {
    pub security_level: SecurityLevel,
    pub target: ProofTarget,
    pub backend: ProverBackend,
    pub cpu: CpuConfig,
    pub gpu: GpuConfig,
}

impl Default for ProgramProverConfig {
    fn default() -> Self {
        Self {
            security_level: SecurityLevel::default(),
            target: ProofTarget::RecursionUnified,
            backend: default_backend_for_build(),
            cpu: CpuConfig::default(),
            gpu: GpuConfig::default(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct ProgramSource {
    pub bin_path: String,
    pub text_path: String,
}

impl ProgramSource {
    pub fn from_paths(bin_path: String, text_path: Option<String>) -> Self {
        let text_path = text_path.unwrap_or_else(|| derive_text_path(&bin_path));
        Self {
            bin_path,
            text_path,
        }
    }

    #[cfg(feature = "gpu")]
    fn gpu_path_without_bin(&self) -> Result<String, String> {
        let bin = Path::new(&self.bin_path);
        let text = Path::new(&self.text_path);

        let Some(stripped) = strip_bin_suffix(bin) else {
            return Err(format!(
                "GPU backend expects --bin to end with .bin for automatic pairing; got {}",
                self.bin_path
            ));
        };

        let expected_text = PathBuf::from(format!("{}.text", stripped.to_string_lossy()));
        if expected_text != text {
            return Err(format!(
                "GPU backend currently requires --text to match {}. Use matching bin/text pair or CPU backend",
                expected_text.display()
            ));
        }

        Ok(stripped.to_string_lossy().to_string())
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, Default)]
pub struct ProofTimingsMs {
    pub total_ms: u64,
    pub base_ms: u64,
    pub unrolled_recursion_ms: Vec<u64>,
    pub unified_recursion_ms: Vec<u64>,
}

#[derive(Clone, Debug, Serialize, Deserialize, Default)]
pub struct ProofCounts {
    pub family_proof_count: usize,
    pub inits_and_teardowns_proof_count: usize,
    pub delegation_proof_count: usize,
    pub delegation_proof_count_by_type: Vec<(u32, usize)>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProofArtifact {
    pub schema_version: u32,
    pub security_level: SecurityLevel,
    pub target: ProofTarget,
    pub backend: ProverBackend,
    pub batch_id: u64,
    pub cycles: u64,
    pub program_bin_keccak: [u8; 32],
    pub program_text_keccak: [u8; 32],
    pub timings_ms: ProofTimingsMs,
    pub proof_counts: ProofCounts,
    pub proof: UnrolledProgramProof,
}

#[derive(Clone)]
struct LoadedProgram {
    bin_bytes: Vec<u8>,
    text_bytes: Vec<u8>,
    padded_bin_bytes: Vec<u8>,
    padded_text_bytes: Vec<u8>,
    padded_bin_u32: Vec<u32>,
    padded_text_u32: Vec<u32>,
}

#[derive(Clone)]
struct EmbeddedProgram {
    padded_bin_bytes: Vec<u8>,
    padded_text_bytes: Vec<u8>,
    padded_bin_u32: Vec<u32>,
    padded_text_u32: Vec<u32>,
}

#[derive(Clone)]
struct RecursionLevelData {
    setup: UnrolledProgramSetup,
    layouts: execution_utils::setups::CompiledCircuitsSet,
    hash_chain: [u32; 8],
    preimage: [u32; 16],
}

enum ProgramProverInner {
    Cpu,
    #[cfg(feature = "gpu")]
    Gpu(UnrolledProver),
}

pub struct ProgramProver {
    source: ProgramSource,
    config: ProgramProverConfig,
    inner: ProgramProverInner,
}

pub fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &Path) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

pub fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).expect(filename);
    serde_json::from_reader(src).unwrap()
}

pub fn u32_from_hex_string(hex_string: &str) -> Vec<u32> {
    if hex_string.len() % 8 != 0 {
        panic!("Hex string length is not a multiple of 8");
    }

    hex_string
        .as_bytes()
        .chunks(8)
        .map(|chunk| {
            let chunk_str = std::str::from_utf8(chunk).expect("Invalid UTF-8");
            u32::from_str_radix(chunk_str, 16).expect("Invalid hex number")
        })
        .collect()
}

pub fn default_backend_for_build() -> ProverBackend {
    #[cfg(feature = "gpu")]
    {
        ProverBackend::Gpu
    }
    #[cfg(not(feature = "gpu"))]
    {
        ProverBackend::Cpu
    }
}

impl ProgramProver {
    pub fn new(source: ProgramSource, config: ProgramProverConfig) -> Result<Self, String> {
        if config.target == ProofTarget::RecursionCombined {
            return Err(
                "recursion-combined proofs are produced from existing recursion-unified \
                 artifacts via `combine_artifacts` (CLI `combine` command), not by proving"
                    .to_string(),
            );
        }
        let inner = match config.backend {
            ProverBackend::Cpu => ProgramProverInner::Cpu,
            ProverBackend::Gpu => {
                #[cfg(feature = "gpu")]
                {
                    let path_without_bin = source.gpu_path_without_bin()?;
                    let mut prover_configuration =
                        gpu_prover::execution::prover::ExecutionProverConfiguration::default();
                    prover_configuration.replay_worker_threads_count =
                        config.gpu.replay_worker_threads_count;

                    let max_level = match config.target {
                        ProofTarget::Base => UnrolledProverLevel::Base,
                        ProofTarget::RecursionUnrolled => UnrolledProverLevel::RecursionUnrolled,
                        ProofTarget::RecursionUnified => UnrolledProverLevel::RecursionUnified,
                        ProofTarget::RecursionCombined => {
                            unreachable!("rejected before backend selection")
                        }
                    };

                    ProgramProverInner::Gpu(UnrolledProver::new(
                        config.security_level.model(),
                        &path_without_bin,
                        prover_configuration,
                        max_level,
                    ))
                }
                #[cfg(not(feature = "gpu"))]
                {
                    return Err(
                        "CLI was compiled without `gpu` feature, but `--backend gpu` was requested"
                            .to_string(),
                    );
                }
            }
        };

        Ok(Self {
            source,
            config,
            inner,
        })
    }

    pub fn prove_words(
        &self,
        batch_id: u64,
        input_words: Vec<u32>,
    ) -> Result<ProofArtifact, String> {
        match &self.inner {
            ProgramProverInner::Cpu => self.prove_words_cpu(batch_id, input_words),
            #[cfg(feature = "gpu")]
            ProgramProverInner::Gpu(gpu_prover) => {
                self.prove_words_gpu(gpu_prover, batch_id, input_words)
            }
        }
    }

    pub fn continue_artifact(&self, artifact: ProofArtifact) -> Result<ProofArtifact, String> {
        match &self.inner {
            ProgramProverInner::Cpu => self.continue_artifact_cpu(artifact),
            #[cfg(feature = "gpu")]
            ProgramProverInner::Gpu(_) => {
                Err("continue-proof currently supports only the CPU backend".to_string())
            }
        }
    }

    #[cfg(feature = "gpu")]
    fn prove_words_gpu(
        &self,
        prover: &UnrolledProver,
        batch_id: u64,
        input_words: Vec<u32>,
    ) -> Result<ProofArtifact, String> {
        let start = Instant::now();
        let source = QuasiUARTSource::new_with_reads(input_words);
        let (proof, cycles) = prover.prove(batch_id, source);

        let total_ms = elapsed_ms(start);
        let timings = ProofTimingsMs {
            total_ms,
            base_ms: total_ms,
            unrolled_recursion_ms: Vec::new(),
            unified_recursion_ms: Vec::new(),
        };

        let loaded = load_program(&self.source)?;
        Ok(make_artifact(
            self.config.security_level,
            self.config.target,
            self.config.backend,
            batch_id,
            cycles,
            program_keccaks(&loaded),
            timings,
            proof,
        ))
    }

    fn prove_words_cpu(
        &self,
        batch_id: u64,
        input_words: Vec<u32>,
    ) -> Result<ProofArtifact, String> {
        let security = self.config.security_level.model();
        let loaded = load_program(&self.source)?;
        let worker = make_cpu_worker(&self.config.cpu);

        let start_base = Instant::now();
        let source = QuasiUARTSource::new_with_reads(input_words);
        let mut proof = prove_unrolled_for_machine_configuration_into_program_proof::<
            IMStandardIsaConfigWithUnsignedMulDiv,
        >(
            &loaded.padded_bin_u32,
            &loaded.padded_text_u32,
            self.config.cpu.cycles_bound,
            source,
            self.config.cpu.ram_bound,
            &worker,
            security,
        );
        let base_ms = elapsed_ms(start_base);
        let cycles = (proof.final_timestamp
            - riscv_transpiler::common_constants::INITIAL_TIMESTAMP)
            / riscv_transpiler::common_constants::TIMESTAMP_STEP;

        let mut timings = ProofTimingsMs {
            total_ms: 0,
            base_ms,
            unrolled_recursion_ms: Vec::new(),
            unified_recursion_ms: Vec::new(),
        };

        if self.config.target == ProofTarget::Base {
            return Ok(finalize_artifact(
                self.config.security_level,
                self.config.target,
                self.config.backend,
                batch_id,
                cycles,
                program_keccaks(&loaded),
                timings,
                proof,
            ));
        }

        let base_level = make_base_level_data(&loaded);
        let recursion_unrolled =
            load_embedded_recursion_program(self.config.security_level, RecursionLayer::Unrolled);
        let unrolled_level = make_unrolled_recursion_level_data(&base_level, &recursion_unrolled);
        proof = continue_with_unrolled_recursion(
            proof,
            &mut timings,
            &self.config.cpu,
            &worker,
            security,
            &base_level,
            &unrolled_level,
            &recursion_unrolled,
        );

        if self.config.target == ProofTarget::RecursionUnrolled {
            return Ok(finalize_artifact(
                self.config.security_level,
                self.config.target,
                self.config.backend,
                batch_id,
                cycles,
                program_keccaks(&loaded),
                timings,
                proof,
            ));
        }

        let recursion_unified =
            load_embedded_recursion_program(self.config.security_level, RecursionLayer::Unified);
        let unified_level = make_unified_recursion_level_data(&unrolled_level, &recursion_unified);
        proof = continue_with_unified_recursion(
            proof,
            &mut timings,
            &self.config.cpu,
            &worker,
            self.config.security_level,
            security,
            &unrolled_level,
            &unified_level,
            &recursion_unified,
        );

        Ok(finalize_artifact(
            self.config.security_level,
            self.config.target,
            self.config.backend,
            batch_id,
            cycles,
            program_keccaks(&loaded),
            timings,
            proof,
        ))
    }

    fn continue_artifact_cpu(&self, artifact: ProofArtifact) -> Result<ProofArtifact, String> {
        validate_continuation_request(&artifact, self.config.target, self.config.backend)?;

        // Continuation still reuses the CPU proving pipeline. We only swap in the
        // persisted proof artifact as the previous stage instead of reproving base.
        let security = self.config.security_level.model();
        let loaded =
            load_and_validate_program(&self.source, &artifact, Some(self.config.security_level))?;
        let worker = make_cpu_worker(&self.config.cpu);

        let input_target = artifact.target;
        let batch_id = artifact.batch_id;
        let cycles = artifact.cycles;
        let mut timings = artifact.timings_ms;
        let mut proof = artifact.proof;

        let base_level = make_base_level_data(&loaded);
        let recursion_unrolled =
            load_embedded_recursion_program(self.config.security_level, RecursionLayer::Unrolled);
        let unrolled_level = make_unrolled_recursion_level_data(&base_level, &recursion_unrolled);

        if input_target == ProofTarget::Base {
            proof = continue_with_unrolled_recursion(
                proof,
                &mut timings,
                &self.config.cpu,
                &worker,
                security,
                &base_level,
                &unrolled_level,
                &recursion_unrolled,
            );
        }

        if self.config.target == ProofTarget::RecursionUnrolled {
            return Ok(finalize_artifact(
                self.config.security_level,
                self.config.target,
                self.config.backend,
                batch_id,
                cycles,
                program_keccaks(&loaded),
                timings,
                proof,
            ));
        }

        let recursion_unified =
            load_embedded_recursion_program(self.config.security_level, RecursionLayer::Unified);
        let unified_level = make_unified_recursion_level_data(&unrolled_level, &recursion_unified);
        proof = continue_with_unified_recursion(
            proof,
            &mut timings,
            &self.config.cpu,
            &worker,
            self.config.security_level,
            security,
            &unrolled_level,
            &unified_level,
            &recursion_unified,
        );

        Ok(finalize_artifact(
            self.config.security_level,
            self.config.target,
            self.config.backend,
            batch_id,
            cycles,
            program_keccaks(&loaded),
            timings,
            proof,
        ))
    }
}

pub fn verify_artifact(
    artifact: &ProofArtifact,
    source: &ProgramSource,
    expected_security_level: SecurityLevel,
    expected_target: ProofTarget,
) -> Result<[u32; 16], String> {
    validate_trusted_verification_policy(artifact, expected_security_level, expected_target)?;
    let loaded = load_and_validate_program(source, artifact, None)?;
    let security = expected_security_level.model();

    match expected_target {
        ProofTarget::Base => {
            let base_level = make_base_level_data(&loaded);
            let output = verify_unrolled_layer_proof(
                &artifact.proof,
                &base_level.setup,
                &base_level.layouts,
                true,
                security,
            )
            .map_err(|_| "base proof verification failed".to_string())?;
            ensure_recursion_chain_binds_program(&output, &base_level.hash_chain)?;
            Ok(output)
        }
        ProofTarget::RecursionUnrolled => {
            let base_level = make_base_level_data(&loaded);
            let recursion_unrolled =
                load_embedded_recursion_program(expected_security_level, RecursionLayer::Unrolled);
            let unrolled_level =
                make_unrolled_recursion_level_data(&base_level, &recursion_unrolled);

            let preimage = validate_recursion_chain(&artifact.proof)?;
            let previous_end_params: [u32; 8] =
                preimage[8..16].try_into().expect("slice with exact length");

            if previous_end_params == base_level.setup.end_params {
                let output = verify_unrolled_layer_proof(
                    &artifact.proof,
                    &base_level.setup,
                    &base_level.layouts,
                    true,
                    security,
                )
                .map_err(|_| "recursion(unrolled over base) verification failed".to_string())?;
                ensure_unrolled_target_binds_program(&output, &unrolled_level.hash_chain)?;
                Ok(output)
            } else if previous_end_params == unrolled_level.setup.end_params {
                let output = verify_unrolled_layer_proof(
                    &artifact.proof,
                    &unrolled_level.setup,
                    &unrolled_level.layouts,
                    false,
                    security,
                )
                .map_err(|_| {
                    "recursion(unrolled over recursion-unrolled) verification failed".to_string()
                })?;
                ensure_unrolled_target_binds_program(&output, &unrolled_level.hash_chain)?;
                Ok(output)
            } else {
                Err("unable to infer previous layer for recursion-unrolled proof".to_string())
            }
        }
        ProofTarget::RecursionUnified => {
            let loaded_unrolled =
                load_embedded_recursion_program(expected_security_level, RecursionLayer::Unrolled);
            let loaded_unified =
                load_embedded_recursion_program(expected_security_level, RecursionLayer::Unified);

            let base_level = make_base_level_data(&loaded);
            let unrolled_level = make_unrolled_recursion_level_data(&base_level, &loaded_unrolled);
            let unified_level = make_unified_recursion_level_data(&unrolled_level, &loaded_unified);

            validate_recursion_chain(&artifact.proof)?;

            let output = verify_proof_in_unified_layer(
                &artifact.proof,
                &unified_level.setup,
                &unified_level.layouts,
                false,
                security,
            )
            .map_err(|_| "recursion(unified) verification failed".to_string())?;
            let (family_count, _, _) = artifact.proof.get_proof_counts();
            ensure_unified_recursion_target_converged(expected_security_level, family_count)?;
            ensure_recursion_chain_binds_program(&output, &unified_level.hash_chain)?;
            Ok(output)
        }
        ProofTarget::RecursionCombined => {
            let loaded_unrolled =
                load_embedded_recursion_program(expected_security_level, RecursionLayer::Unrolled);
            let loaded_unified =
                load_embedded_recursion_program(expected_security_level, RecursionLayer::Unified);

            let base_level = make_base_level_data(&loaded);
            let unrolled_level = make_unrolled_recursion_level_data(&base_level, &loaded_unrolled);
            let unified_level = make_unified_recursion_level_data(&unrolled_level, &loaded_unified);

            validate_recursion_chain(&artifact.proof)?;

            let output = verify_proof_in_unified_layer(
                &artifact.proof,
                &unified_level.setup,
                &unified_level.layouts,
                false,
                security,
            )
            .map_err(|_| "recursion(combined) verification failed".to_string())?;
            let (family_count, _, _) = artifact.proof.get_proof_counts();
            ensure_unified_recursion_target_converged(expected_security_level, family_count)?;
            // The combined statement carries the shared recursion chain of the
            // combined proofs through unchanged, so the same chain binding as for
            // a single recursion-unified proof applies. Words 0..8 of the output
            // are the keccak rolling hash of the combined proofs' outputs and
            // must be checked by the caller against the expected batch outputs.
            ensure_recursion_chain_binds_program(&output, &unified_level.hash_chain)?;
            Ok(output)
        }
    }
}

/// Combine multiple recursion-unified proof artifacts of the same program into a
/// single proof artifact. Every input artifact is verified first; the combined
/// statement is then proved with the unified-layer recursion program and shrunk
/// via unified self-recursion until it converges. The resulting proof's output is
/// `keccak(out_1[0..8]>>32 || ... || out_n[0..8]>>32) || shared_recursion_chain`,
/// and is checked against the outputs of the input proofs before returning.
pub fn combine_artifacts(
    artifacts: &[ProofArtifact],
    source: &ProgramSource,
    security_level: SecurityLevel,
    cpu: &CpuConfig,
) -> Result<ProofArtifact, String> {
    combine_artifacts_with_program(artifacts, source, security_level, CombineBackend::Cpu(cpu))
}

/// GPU variant of [`combine_artifacts`]: input verification, witness building,
/// recursion-chain stamping and the final self-check stay on the host; only the
/// unified-layer proving passes run on the GPU.
#[cfg(feature = "gpu")]
pub fn combine_artifacts_gpu(
    artifacts: &[ProofArtifact],
    source: &ProgramSource,
    security_level: SecurityLevel,
    gpu: &GpuConfig,
) -> Result<ProofArtifact, String> {
    combine_artifacts_with_program(artifacts, source, security_level, CombineBackend::Gpu(gpu))
}

/// Variant of [`combine_artifacts`] that does not bind the inputs to a locally supplied
/// program: every input proof must instead carry — and prove — the same recursion chain,
/// which the combined proof then carries through unchanged. Use this when the combined
/// proof is handed to a downstream verifier that authenticates the chain itself (e.g. a
/// SNARK wrapper exposing it in the public input); that verifier is then responsible for
/// binding the chain to the expected program.
///
/// One-shot convenience over [`CarriedChainCombiner`]; callers combining repeatedly
/// should hold a combiner instead to reuse its cached setup state across combines.
pub fn combine_artifacts_carried_chain(
    artifacts: &[ProofArtifact],
    security_level: SecurityLevel,
    cpu: &CpuConfig,
) -> Result<ProofArtifact, String> {
    CarriedChainCombiner::new_cpu(security_level, cpu.clone()).combine(artifacts)
}

/// GPU variant of [`combine_artifacts_carried_chain`].
///
/// One-shot convenience over [`CarriedChainCombiner`]; callers combining repeatedly
/// should hold a combiner instead to reuse its cached setup state across combines.
#[cfg(feature = "gpu")]
pub fn combine_artifacts_carried_chain_gpu(
    artifacts: &[ProofArtifact],
    security_level: SecurityLevel,
    gpu: &GpuConfig,
) -> Result<ProofArtifact, String> {
    CarriedChainCombiner::new_gpu(security_level, gpu.clone()).combine(artifacts)
}

enum CombineBackend<'a> {
    Cpu(&'a CpuConfig),
    #[cfg(feature = "gpu")]
    Gpu(&'a GpuConfig),
}

/// Reusable carried-chain combiner (see [`combine_artifacts_carried_chain`]). Caches
/// everything that does not depend on the input proofs — the embedded unified-layer
/// recursion program, its setup and compiled layouts, and (with the `gpu` feature) the
/// GPU prover's host state (pinned host memory pools and circuit precomputations) — so
/// repeated combines only pay for verification and the proving passes themselves.
///
/// The caches build lazily on the first [`Self::combine`]; call [`Self::warm_up`] to
/// pay that cost up front (e.g. at service startup). GPU combines still create the
/// CUDA contexts and the device memory pool per call and release them on return, so
/// the device is free for other work (e.g. SNARK wrapping) between combines.
pub struct CarriedChainCombiner {
    security_level: SecurityLevel,
    recursion_unified: EmbeddedProgram,
    unified_setup_and_layouts: Option<(
        UnrolledProgramSetup,
        execution_utils::setups::CompiledCircuitsSet,
    )>,
    backend: CombinerBackendState,
}

enum CombinerBackendState {
    Cpu(CpuConfig),
    #[cfg(feature = "gpu")]
    Gpu {
        config: GpuConfig,
        host_state: Option<UnifiedRecursionProverHostState>,
    },
}

impl CarriedChainCombiner {
    pub fn new_cpu(security_level: SecurityLevel, cpu: CpuConfig) -> Self {
        Self::new(security_level, CombinerBackendState::Cpu(cpu))
    }

    #[cfg(feature = "gpu")]
    pub fn new_gpu(security_level: SecurityLevel, gpu: GpuConfig) -> Self {
        Self::new(
            security_level,
            CombinerBackendState::Gpu {
                config: gpu,
                host_state: None,
            },
        )
    }

    fn new(security_level: SecurityLevel, backend: CombinerBackendState) -> Self {
        let recursion_unified =
            load_embedded_recursion_program(security_level, RecursionLayer::Unified);
        Self {
            security_level,
            recursion_unified,
            unified_setup_and_layouts: None,
            backend,
        }
    }

    pub fn security_level(&self) -> SecurityLevel {
        self.security_level
    }

    /// Builds the cached state up front (the unified-level setup and layouts and, on
    /// the GPU backend, the prover's host state) so the first combine doesn't pay for
    /// it. Idempotent.
    pub fn warm_up(&mut self) {
        if self.unified_setup_and_layouts.is_none() {
            let start = Instant::now();
            let setup = compute_unified_setup_for_machine_configuration::<
                IWithoutByteAccessIsaConfigWithDelegation,
            >(
                &self.recursion_unified.padded_bin_bytes,
                &self.recursion_unified.padded_text_bytes,
            );
            let layouts = get_unified_circuit_artifact_for_machine_type::<
                IWithoutByteAccessIsaConfigWithDelegation,
            >(&self.recursion_unified.padded_bin_u32);
            log::info!(
                "COMBINER unified-level setup and layouts computed in {} ms",
                elapsed_ms(start)
            );
            self.unified_setup_and_layouts = Some((setup, layouts));
        }
        #[cfg(feature = "gpu")]
        if let CombinerBackendState::Gpu { config, host_state } = &mut self.backend {
            if host_state.is_none() {
                let start = Instant::now();
                let mut prover_configuration =
                    gpu_prover::execution::prover::ExecutionProverConfiguration::default();
                prover_configuration.replay_worker_threads_count =
                    config.replay_worker_threads_count;
                *host_state = Some(UnifiedRecursionProverHostState::new(
                    self.security_level.model(),
                    prover_configuration,
                ));
                log::info!(
                    "COMBINER GPU prover host state built in {} ms",
                    elapsed_ms(start)
                );
            }
        }
    }

    /// Combines the artifacts into one carried-chain proof; see
    /// [`combine_artifacts_carried_chain`] for the semantics.
    pub fn combine(&mut self, artifacts: &[ProofArtifact]) -> Result<ProofArtifact, String> {
        if artifacts.len() < 2 {
            return Err(format!(
                "combining requires at least two proof artifacts, got {}",
                artifacts.len()
            ));
        }

        // Chain validation is cheap and independent of the cached state, so bad inputs
        // fail before a cold combiner pays for its warm-up.
        let (hash_chain, preimage) = validate_shared_carried_chain(artifacts)?;
        let expected_keccaks = (
            artifacts[0].program_bin_keccak,
            artifacts[0].program_text_keccak,
        );

        self.warm_up();
        let (setup, layouts) = self
            .unified_setup_and_layouts
            .as_ref()
            .expect("warmed up above");
        let unified_level = RecursionLevelData {
            setup: setup.clone(),
            layouts: layouts.clone(),
            hash_chain,
            preimage,
        };

        let mut prover = match &self.backend {
            CombinerBackendState::Cpu(cpu) => {
                CombinedUnifiedProver::new_cpu(cpu, &self.recursion_unified)
            }
            #[cfg(feature = "gpu")]
            CombinerBackendState::Gpu { host_state, .. } => CombinedUnifiedProver::new_gpu(
                host_state.as_ref().expect("warmed up above"),
                artifacts[0].batch_id,
            ),
        };

        run_combine(
            artifacts,
            &unified_level,
            expected_keccaks,
            self.security_level,
            &mut prover,
        )
    }
}

/// The unified-layer prover used by the combine flow. Both backends prove the
/// same embedded unified recursion program over host-built witness words.
enum CombinedUnifiedProver<'a> {
    Cpu {
        cpu: &'a CpuConfig,
        worker: worker::Worker,
        recursion_unified: &'a EmbeddedProgram,
    },
    #[cfg(feature = "gpu")]
    Gpu {
        prover: execution_utils::unrolled_gpu::UnifiedRecursionProver,
        // Distinct per-pass ids for the GPU prover, following the
        // `UnrolledProver` convention of `batch_id * 10 + pass`.
        next_batch_id: u64,
    },
}

impl<'a> CombinedUnifiedProver<'a> {
    fn new_cpu(cpu: &'a CpuConfig, recursion_unified: &'a EmbeddedProgram) -> Self {
        Self::Cpu {
            cpu,
            worker: make_cpu_worker(cpu),
            recursion_unified,
        }
    }

    /// Derives the GPU prover from prebuilt host state: only CUDA contexts and the
    /// device memory pool are created here, and dropping the prover releases them.
    #[cfg(feature = "gpu")]
    fn new_gpu(host_state: &UnifiedRecursionProverHostState, batch_id: u64) -> Self {
        Self::Gpu {
            prover: execution_utils::unrolled_gpu::UnifiedRecursionProver::from_host_state(
                host_state,
            ),
            // Distinct per-pass ids for the GPU prover, following the
            // `UnrolledProver` convention of `batch_id * 10 + pass`.
            next_batch_id: batch_id * 10,
        }
    }

    fn kind(&self) -> ProverBackend {
        match self {
            Self::Cpu { .. } => ProverBackend::Cpu,
            #[cfg(feature = "gpu")]
            Self::Gpu { .. } => ProverBackend::Gpu,
        }
    }

    fn prove_unified_pass(
        &mut self,
        witness: Vec<u32>,
        security: verifier_common::SecurityModel,
    ) -> UnrolledProgramProof {
        match self {
            Self::Cpu {
                cpu,
                worker,
                recursion_unified,
            } => {
                let source_witness = QuasiUARTSource::new_with_reads(witness);
                prove_unified_for_machine_configuration_into_program_proof::<
                    IWithoutByteAccessIsaConfigWithDelegation,
                >(
                    &recursion_unified.padded_bin_u32,
                    &recursion_unified.padded_text_u32,
                    cpu.cycles_bound,
                    source_witness,
                    cpu.ram_bound,
                    worker,
                    security,
                )
            }
            #[cfg(feature = "gpu")]
            Self::Gpu {
                prover,
                next_batch_id,
            } => {
                let batch_id = *next_batch_id;
                *next_batch_id += 1;
                prover.prove(batch_id, witness)
            }
        }
    }
}

/// Combine bound to a locally supplied program: derives the expected recursion chain
/// from the program's own base -> unrolled -> unified chain and validates the
/// artifacts' program keccaks against its files.
fn combine_artifacts_with_program(
    artifacts: &[ProofArtifact],
    source: &ProgramSource,
    security_level: SecurityLevel,
    backend: CombineBackend,
) -> Result<ProofArtifact, String> {
    if artifacts.len() < 2 {
        return Err(format!(
            "combining requires at least two proof artifacts, got {}",
            artifacts.len()
        ));
    }

    let recursion_unified =
        load_embedded_recursion_program(security_level, RecursionLayer::Unified);

    let loaded = load_and_validate_program(source, &artifacts[0], Some(security_level))?;
    let base_level = make_base_level_data(&loaded);
    let recursion_unrolled =
        load_embedded_recursion_program(security_level, RecursionLayer::Unrolled);
    let unrolled_level = make_unrolled_recursion_level_data(&base_level, &recursion_unrolled);
    let unified_level = make_unified_recursion_level_data(&unrolled_level, &recursion_unified);
    let expected_keccaks = program_keccaks(&loaded);

    let mut prover = match backend {
        CombineBackend::Cpu(cpu) => CombinedUnifiedProver::new_cpu(cpu, &recursion_unified),
        #[cfg(feature = "gpu")]
        CombineBackend::Gpu(gpu) => {
            let mut prover_configuration =
                gpu_prover::execution::prover::ExecutionProverConfiguration::default();
            prover_configuration.replay_worker_threads_count = gpu.replay_worker_threads_count;
            let host_state =
                UnifiedRecursionProverHostState::new(security_level.model(), prover_configuration);
            CombinedUnifiedProver::new_gpu(&host_state, artifacts[0].batch_id)
        }
    };

    run_combine(
        artifacts,
        &unified_level,
        expected_keccaks,
        security_level,
        &mut prover,
    )
}

/// Core of a combine, shared by the program-bound and carried-chain flows: verify
/// every input against the unified level, prove the combined statement, shrink it to
/// convergence via unified self-recursion and self-check the result.
fn run_combine(
    artifacts: &[ProofArtifact],
    unified_level: &RecursionLevelData,
    expected_keccaks: ([u8; 32], [u8; 32]),
    security_level: SecurityLevel,
    prover: &mut CombinedUnifiedProver,
) -> Result<ProofArtifact, String> {
    let security = security_level.model();

    // Verify every input artifact (security level, target, convergence of each proof,
    // keccak consistency, and that each proof proves the expected recursion chain),
    // and collect the outputs to compute the expected combined output.
    let verify_start = Instant::now();
    let mut outputs = Vec::with_capacity(artifacts.len());
    for (idx, artifact) in artifacts.iter().enumerate() {
        let output = verify_combine_artifact_against_level(
            artifact,
            unified_level,
            expected_keccaks,
            security_level,
            ProofTarget::RecursionUnified,
        )
        .map_err(|e| format!("input proof {} failed verification: {}", idx, e))?;
        outputs.push(output);
    }
    log::info!(
        "COMBINER verified {} input proofs in {} ms",
        artifacts.len(),
        elapsed_ms(verify_start)
    );
    let expected_output =
        execution_utils::unified_circuit::compute_combined_recursion_layers_output(&outputs);

    let mut timings = ProofTimingsMs::default();

    // Prove the combined statement with the unified-layer recursion program.
    let inputs: Vec<_> = artifacts
        .iter()
        .map(
            |artifact| execution_utils::unified_circuit::CombinedRecursionInput {
                proof: &artifact.proof,
                setup: &unified_level.setup,
                compiled_layouts: &unified_level.layouts,
                input_is_unrolled: false,
            },
        )
        .collect();
    let witness =
        execution_utils::unified_circuit::flatten_proofs_into_responses_for_combined_unified_recursion(
            &inputs,
        );

    let start = Instant::now();
    let mut proof = prover.prove_unified_pass(witness, security);
    timings.unified_recursion_ms.push(elapsed_ms(start));
    log::info!(
        "COMBINER combined pass over {} proofs done in {} ms {}",
        artifacts.len(),
        elapsed_ms(start),
        proof.debug_info()
    );

    // The combined statement carries the shared (converged) recursion chain of the
    // input proofs through unchanged, so the chain witness stays the unified level's.
    proof.recursion_chain_hash = Some(unified_level.hash_chain);
    proof.recursion_chain_preimage = Some(unified_level.preimage);

    // Shrink via unified self-recursion until the proof converges.
    let mut shrink_pass = 0u64;
    loop {
        let (family_count, _, _) = proof.get_proof_counts();
        if security_level.unified_recursion_has_converged(family_count) {
            break;
        }

        let witness = flatten_proof_into_responses_for_unified_recursion(
            &proof,
            &unified_level.setup,
            &unified_level.layouts,
            false,
        );

        let start = Instant::now();
        let mut new_proof = prover.prove_unified_pass(witness, security);
        timings.unified_recursion_ms.push(elapsed_ms(start));
        log::info!(
            "COMBINER shrink pass {shrink_pass} done in {} ms {}",
            elapsed_ms(start),
            new_proof.debug_info()
        );
        shrink_pass += 1;

        new_proof.recursion_chain_hash = Some(unified_level.hash_chain);
        new_proof.recursion_chain_preimage = Some(unified_level.preimage);
        proof = new_proof;
    }

    let cycles = artifacts.iter().map(|artifact| artifact.cycles).sum();
    let artifact = finalize_artifact(
        security_level,
        ProofTarget::RecursionCombined,
        prover.kind(),
        artifacts[0].batch_id,
        cycles,
        expected_keccaks,
        timings,
        proof,
    );

    // Self-check: the combined proof must verify and produce exactly the expected
    // rolling hash of the input proofs' outputs.
    let self_check_start = Instant::now();
    let output = verify_combine_artifact_against_level(
        &artifact,
        unified_level,
        expected_keccaks,
        security_level,
        ProofTarget::RecursionCombined,
    )
    .map_err(|e| format!("combined proof failed verification: {}", e))?;
    if output != expected_output {
        return Err(format!(
            "combined proof output {:?} does not match expected combined output {:?}",
            output, expected_output
        ));
    }
    log::info!(
        "COMBINER self-checked the combined proof in {} ms",
        elapsed_ms(self_check_start)
    );

    Ok(artifact)
}

/// Checks that every artifact carries the same, internally consistent recursion chain
/// and returns it as `(hash_chain, preimage)`.
fn validate_shared_carried_chain(
    artifacts: &[ProofArtifact],
) -> Result<([u32; 8], [u32; 16]), String> {
    let preimage = validate_recursion_chain(&artifacts[0].proof)
        .map_err(|e| format!("input proof 0: {}", e))?;
    let hash_chain = artifacts[0]
        .proof
        .recursion_chain_hash
        .expect("chain validated above, so the hash is present");
    for (idx, artifact) in artifacts.iter().enumerate().skip(1) {
        if artifact.proof.recursion_chain_hash != Some(hash_chain) {
            return Err(format!(
                "input proof {} carries a different recursion chain than input proof 0",
                idx
            ));
        }
    }
    Ok((hash_chain, preimage))
}

/// Verify one proof artifact of a combine (an input, or the combined result) against
/// already-built unified-level data. Mirrors the checks [`verify_artifact`] performs for
/// the same targets, without re-deriving the level data per proof and with the program
/// keccaks checked against the combine's binding instead of files on disk.
fn verify_combine_artifact_against_level(
    artifact: &ProofArtifact,
    unified_level: &RecursionLevelData,
    expected_keccaks: ([u8; 32], [u8; 32]),
    expected_security_level: SecurityLevel,
    expected_target: ProofTarget,
) -> Result<[u32; 16], String> {
    validate_trusted_verification_policy(artifact, expected_security_level, expected_target)?;
    if (artifact.program_bin_keccak, artifact.program_text_keccak) != expected_keccaks {
        return Err(
            "proof artifact program keccaks do not match the combine's program binding".to_string(),
        );
    }
    validate_recursion_chain(&artifact.proof)?;

    let output = verify_proof_in_unified_layer(
        &artifact.proof,
        &unified_level.setup,
        &unified_level.layouts,
        false,
        expected_security_level.model(),
    )
    .map_err(|_| match expected_target {
        ProofTarget::RecursionCombined => "recursion(combined) verification failed".to_string(),
        _ => "recursion(unified) verification failed".to_string(),
    })?;
    let (family_count, _, _) = artifact.proof.get_proof_counts();
    ensure_unified_recursion_target_converged(expected_security_level, family_count)?;
    ensure_recursion_chain_binds_program(&output, &unified_level.hash_chain)?;
    Ok(output)
}

fn validate_trusted_verification_policy(
    artifact: &ProofArtifact,
    expected_security_level: SecurityLevel,
    expected_target: ProofTarget,
) -> Result<(), String> {
    if artifact.security_level != expected_security_level {
        return Err(format!(
            "proof security level ({:?}) does not match requested security level ({:?})",
            artifact.security_level, expected_security_level
        ));
    }

    if artifact.target != expected_target {
        return Err(format!(
            "proof target ({:?}) does not match requested target ({:?})",
            artifact.target, expected_target
        ));
    }

    Ok(())
}

fn validate_recursion_chain(proof: &UnrolledProgramProof) -> Result<[u32; 16], String> {
    let Some(preimage) = proof.recursion_chain_preimage else {
        return Err("proof is missing recursion_chain_preimage".to_string());
    };
    let Some(hash) = proof.recursion_chain_hash else {
        return Err("proof is missing recursion_chain_hash".to_string());
    };

    let mut hasher = Blake2sBufferingTranscript::new();
    hasher.absorb(&preimage);
    let expected_hash = hasher.finalize().0;
    if expected_hash != hash {
        return Err("recursion chain hash mismatch".to_string());
    }

    Ok(preimage)
}

/// Bind a verified proof to the program supplied by the caller.
///
/// The cryptographic verifier returns the recursion chain it actually proved in
/// `output[8..16]`. That chain authenticates the whole tower of verified programs back
/// to the base program (see `begin_recursion_chain` / `continue_recursion_chain`): it is
/// `continue_recursion_chain(this_layer_end_params, previous_chain)`, exactly how the
/// matching `*_level.hash_chain` is derived from the supplied program.
///
/// `expected_chain` is the `hash_chain` of the level whose setup was verified against,
/// derived from the supplied `--bin`/`--text`. If the proof proved a chain for a
/// different base program, the two differ and we reject.
///
/// This is the binding step: the recursion verifier's setup is the (program-independent)
/// embedded verifier program, and the `program_*_keccak` metadata is attacker-mutable, so
/// neither constrains which base program the STARK proof actually attests to — only this
/// chain comparison does.
fn ensure_recursion_chain_binds_program(
    verifier_output: &[u32; 16],
    expected_chain: &[u32; 8],
) -> Result<(), String> {
    if &verifier_output[8..16] != expected_chain {
        return Err(
            "recursion chain proven by the proof does not match the supplied program".to_string(),
        );
    }
    Ok(())
}

/// Bind a verified recursion-unrolled proof to the supplied program and target stage.
///
/// A `RecursionUnrolled` artifact must prove one unrolled-recursion wrapper around the
/// supplied program's base layer, regardless of whether the wrapped proof came directly
/// from the base layer or from a prior unrolled wrapper. In both cases, the authenticated
/// output chain must therefore match the supplied program's unrolled recursion level.
fn ensure_unrolled_target_binds_program(
    verifier_output: &[u32; 16],
    expected_unrolled_chain: &[u32; 8],
) -> Result<(), String> {
    ensure_recursion_chain_binds_program(verifier_output, expected_unrolled_chain)
}

fn ensure_unified_recursion_target_converged(
    security_level: SecurityLevel,
    family_count: usize,
) -> Result<(), String> {
    if security_level.unified_recursion_has_converged(family_count) {
        return Ok(());
    }

    Err(format!(
        "recursion(unified) proof has not converged for {:?}: got {} family proof(s), need {}",
        security_level,
        family_count,
        security_level.unified_recursion_target_family_proofs()
    ))
}

fn program_keccaks(loaded: &LoadedProgram) -> ([u8; 32], [u8; 32]) {
    (keccak256(&loaded.bin_bytes), keccak256(&loaded.text_bytes))
}

fn make_artifact(
    security_level: SecurityLevel,
    target: ProofTarget,
    backend: ProverBackend,
    batch_id: u64,
    cycles: u64,
    (program_bin_keccak, program_text_keccak): ([u8; 32], [u8; 32]),
    timings: ProofTimingsMs,
    proof: UnrolledProgramProof,
) -> ProofArtifact {
    let (family_proof_count, inits_and_teardowns_proof_count, delegation_proof_count) =
        proof.get_proof_counts();

    let proof_counts = ProofCounts {
        family_proof_count,
        inits_and_teardowns_proof_count,
        delegation_proof_count,
        delegation_proof_count_by_type: proof
            .delegation_proofs
            .iter()
            .map(|(k, v)| (*k, v.len()))
            .collect(),
    };

    ProofArtifact {
        schema_version: 1,
        security_level,
        target,
        backend,
        batch_id,
        cycles,
        program_bin_keccak,
        program_text_keccak,
        timings_ms: timings,
        proof_counts,
        proof,
    }
}

// ==============================================================================
// Staged Proving Helpers
// ==============================================================================
//
// Fresh proving and staged continuation share the same recursion transitions.
// The only difference is the starting proof artifact: freshly generated base
// proof vs. a proof loaded from disk.

fn continue_with_unrolled_recursion(
    mut proof: UnrolledProgramProof,
    timings: &mut ProofTimingsMs,
    cpu: &CpuConfig,
    worker: &worker::Worker,
    security: verifier_common::SecurityModel,
    base_level: &RecursionLevelData,
    unrolled_level: &RecursionLevelData,
    recursion_unrolled: &EmbeddedProgram,
) -> UnrolledProgramProof {
    let mut recursion_level = 0usize;
    loop {
        let previous_is_base = recursion_level == 0;
        let previous_level = if previous_is_base {
            base_level
        } else {
            unrolled_level
        };

        let witness = flatten_proof_into_responses_for_unrolled_recursion(
            &proof,
            &previous_level.setup,
            &previous_level.layouts,
            previous_is_base,
        );
        let source = QuasiUARTSource::new_with_reads(witness);

        let start = Instant::now();
        let mut new_proof = prove_unrolled_for_machine_configuration_into_program_proof::<
            IWithoutByteAccessIsaConfigWithDelegation,
        >(
            &recursion_unrolled.padded_bin_u32,
            &recursion_unrolled.padded_text_u32,
            cpu.cycles_bound,
            source,
            cpu.ram_bound,
            worker,
            security,
        );
        timings.unrolled_recursion_ms.push(elapsed_ms(start));

        new_proof.recursion_chain_hash = Some(previous_level.hash_chain);
        new_proof.recursion_chain_preimage = Some(previous_level.preimage);
        proof = new_proof;

        let (_, _, delegation_count) = proof.get_proof_counts();
        if delegation_count == 1 {
            break;
        }

        recursion_level += 1;
    }

    proof
}

fn continue_with_unified_recursion(
    mut proof: UnrolledProgramProof,
    timings: &mut ProofTimingsMs,
    cpu: &CpuConfig,
    worker: &worker::Worker,
    security_level: SecurityLevel,
    security: verifier_common::SecurityModel,
    unrolled_level: &RecursionLevelData,
    unified_level: &RecursionLevelData,
    recursion_unified: &EmbeddedProgram,
) -> UnrolledProgramProof {
    let mut unified_level_idx = 0usize;
    loop {
        let previous_is_unrolled = unified_level_idx == 0;
        let previous_level = if previous_is_unrolled {
            unrolled_level
        } else {
            unified_level
        };

        let witness = flatten_proof_into_responses_for_unified_recursion(
            &proof,
            &previous_level.setup,
            &previous_level.layouts,
            previous_is_unrolled,
        );
        let source = QuasiUARTSource::new_with_reads(witness);

        let start = Instant::now();
        let mut new_proof = prove_unified_for_machine_configuration_into_program_proof::<
            IWithoutByteAccessIsaConfigWithDelegation,
        >(
            &recursion_unified.padded_bin_u32,
            &recursion_unified.padded_text_u32,
            cpu.cycles_bound,
            source,
            cpu.ram_bound,
            worker,
            security,
        );
        timings.unified_recursion_ms.push(elapsed_ms(start));

        new_proof.recursion_chain_hash = Some(previous_level.hash_chain);
        new_proof.recursion_chain_preimage = Some(previous_level.preimage);
        proof = new_proof;

        let (family_count, _, _) = proof.get_proof_counts();
        if security_level.unified_recursion_has_converged(family_count) {
            break;
        }

        unified_level_idx += 1;
    }

    proof
}

fn finalize_artifact(
    security_level: SecurityLevel,
    target: ProofTarget,
    backend: ProverBackend,
    batch_id: u64,
    cycles: u64,
    keccaks: ([u8; 32], [u8; 32]),
    mut timings: ProofTimingsMs,
    proof: UnrolledProgramProof,
) -> ProofArtifact {
    timings.total_ms = aggregate_timing_ms(&timings);
    make_artifact(
        security_level,
        target,
        backend,
        batch_id,
        cycles,
        keccaks,
        timings,
        proof,
    )
}

fn aggregate_timing_ms(timings: &ProofTimingsMs) -> u64 {
    timings.base_ms
        + timings.unrolled_recursion_ms.iter().sum::<u64>()
        + timings.unified_recursion_ms.iter().sum::<u64>()
}

fn make_cpu_worker(cpu: &CpuConfig) -> worker::Worker {
    if let Some(threads) = cpu.worker_threads {
        worker::Worker::new_with_num_threads(threads)
    } else {
        worker::Worker::new()
    }
}

fn load_and_validate_program(
    source: &ProgramSource,
    artifact: &ProofArtifact,
    expected_security_level: Option<SecurityLevel>,
) -> Result<LoadedProgram, String> {
    let loaded = load_program(source)?;
    validate_artifact_against_program(artifact, &loaded, expected_security_level)?;
    Ok(loaded)
}

fn validate_artifact_against_program(
    artifact: &ProofArtifact,
    loaded: &LoadedProgram,
    expected_security_level: Option<SecurityLevel>,
) -> Result<(), String> {
    if let Some(expected_security_level) = expected_security_level {
        // Some callers also want this helper to enforce a trusted security-level
        // contract in addition to program-hash binding.
        if artifact.security_level != expected_security_level {
            return Err(format!(
                "proof security level ({:?}) does not match requested security level ({:?})",
                artifact.security_level, expected_security_level
            ));
        }
    }

    let actual_bin_keccak = keccak256(&loaded.bin_bytes);
    if actual_bin_keccak != artifact.program_bin_keccak {
        return Err(format!(
            "proof artifact program_bin_keccak does not match provided --bin file"
        ));
    }

    let actual_text_keccak = keccak256(&loaded.text_bytes);
    if actual_text_keccak != artifact.program_text_keccak {
        return Err(
            "proof artifact program_text_keccak does not match provided --text file".to_string(),
        );
    }

    Ok(())
}

fn validate_continuation_request(
    artifact: &ProofArtifact,
    target: ProofTarget,
    backend: ProverBackend,
) -> Result<(), String> {
    if backend != ProverBackend::Cpu {
        return Err("continue-proof currently supports only the CPU backend".to_string());
    }

    // TODO: Support continuation for GPU-produced artifacts once the GPU prover
    // exposes a way to resume from an existing proof artifact.
    if artifact.backend != ProverBackend::Cpu {
        return Err(
            "continue-proof currently supports only artifacts produced with the CPU backend"
                .to_string(),
        );
    }

    match (artifact.target, target) {
        (ProofTarget::Base, ProofTarget::RecursionUnrolled)
        | (ProofTarget::Base, ProofTarget::RecursionUnified)
        | (ProofTarget::RecursionUnrolled, ProofTarget::RecursionUnified) => {}
        (current, requested) if current == requested => {
            return Err(format!(
                "proof artifact is already at target {:?}; choose a later stage",
                current
            ));
        }
        (current, requested) => {
            return Err(format!(
                "cannot continue proof from {:?} to {:?}",
                current, requested
            ));
        }
    }

    if artifact.target == ProofTarget::RecursionUnrolled {
        validate_recursion_chain(&artifact.proof)?;
    }

    Ok(())
}

fn load_program(source: &ProgramSource) -> Result<LoadedProgram, String> {
    let bin_path = Path::new(&source.bin_path);
    let text_path = Path::new(&source.text_path);

    if !bin_path.exists() {
        return Err(format!("binary not found: {}", source.bin_path));
    }
    if !text_path.exists() {
        return Err(format!("text section not found: {}", source.text_path));
    }

    let (bin_bytes, mut bin_u32) = read_binary(bin_path);
    let (text_bytes, mut text_u32) = read_binary(text_path);

    let mut padded_bin_bytes = bin_bytes.clone();
    let mut padded_text_bytes = text_bytes.clone();
    pad_bytecode_bytes_for_proving(&mut padded_bin_bytes);
    pad_bytecode_bytes_for_proving(&mut padded_text_bytes);

    pad_bytecode_for_proving(&mut bin_u32);
    pad_bytecode_for_proving(&mut text_u32);

    Ok(LoadedProgram {
        bin_bytes,
        text_bytes,
        padded_bin_bytes,
        padded_text_bytes,
        padded_bin_u32: bin_u32,
        padded_text_u32: text_u32,
    })
}

fn load_embedded_program(binary: &[u8], text: &[u8]) -> EmbeddedProgram {
    let mut padded_bin_bytes = binary.to_vec();
    let mut padded_text_bytes = text.to_vec();
    pad_bytecode_bytes_for_proving(&mut padded_bin_bytes);
    pad_bytecode_bytes_for_proving(&mut padded_text_bytes);

    let mut padded_bin_u32 = binary_u8_to_u32(binary);
    let mut padded_text_u32 = binary_u8_to_u32(text);
    pad_bytecode_for_proving(&mut padded_bin_u32);
    pad_bytecode_for_proving(&mut padded_text_u32);

    EmbeddedProgram {
        padded_bin_bytes,
        padded_text_bytes,
        padded_bin_u32,
        padded_text_u32,
    }
}

fn load_embedded_recursion_program(
    security_level: SecurityLevel,
    recursion_layer: RecursionLayer,
) -> EmbeddedProgram {
    let security = security_level.model();
    let binary = recursion_artifact(security, recursion_layer, RecursionArtifact::Bin);
    let text = recursion_artifact(security, recursion_layer, RecursionArtifact::Txt);
    load_embedded_program(binary, text)
}

fn make_base_level_data(loaded: &LoadedProgram) -> RecursionLevelData {
    let setup = compute_setup_for_machine_configuration::<IMStandardIsaConfigWithUnsignedMulDiv>(
        &loaded.padded_bin_bytes,
        &loaded.padded_text_bytes,
    );
    let layouts = get_unrolled_circuits_artifacts_for_machine_type::<
        IMStandardIsaConfigWithUnsignedMulDiv,
    >(&loaded.padded_bin_u32);

    let (hash_chain, preimage) = UnrolledProgramSetup::begin_recursion_chain(&setup.end_params);

    RecursionLevelData {
        setup,
        layouts,
        hash_chain,
        preimage,
    }
}

fn make_unrolled_recursion_level_data(
    previous: &RecursionLevelData,
    loaded: &EmbeddedProgram,
) -> RecursionLevelData {
    let setup = compute_setup_for_machine_configuration::<IWithoutByteAccessIsaConfigWithDelegation>(
        &loaded.padded_bin_bytes,
        &loaded.padded_text_bytes,
    );
    let layouts = get_unrolled_circuits_artifacts_for_machine_type::<
        IWithoutByteAccessIsaConfigWithDelegation,
    >(&loaded.padded_bin_u32);

    let (hash_chain, preimage) = UnrolledProgramSetup::continue_recursion_chain(
        &setup.end_params,
        &previous.hash_chain,
        &previous.preimage,
    );

    RecursionLevelData {
        setup,
        layouts,
        hash_chain,
        preimage,
    }
}

fn make_unified_recursion_level_data(
    previous: &RecursionLevelData,
    loaded: &EmbeddedProgram,
) -> RecursionLevelData {
    let setup = compute_unified_setup_for_machine_configuration::<
        IWithoutByteAccessIsaConfigWithDelegation,
    >(&loaded.padded_bin_bytes, &loaded.padded_text_bytes);
    let layouts = get_unified_circuit_artifact_for_machine_type::<
        IWithoutByteAccessIsaConfigWithDelegation,
    >(&loaded.padded_bin_u32);

    let (hash_chain, preimage) = UnrolledProgramSetup::continue_recursion_chain(
        &setup.end_params,
        &previous.hash_chain,
        &previous.preimage,
    );

    RecursionLevelData {
        setup,
        layouts,
        hash_chain,
        preimage,
    }
}

fn derive_text_path(bin_path: &str) -> String {
    let bin = Path::new(bin_path);
    if let Some(stem_path) = strip_bin_suffix(bin) {
        return format!("{}.text", stem_path.to_string_lossy());
    }

    let mut text_path = bin.to_path_buf();
    text_path.set_extension("text");
    text_path.to_string_lossy().to_string()
}

fn strip_bin_suffix(path: &Path) -> Option<PathBuf> {
    let path_str = path.to_string_lossy();
    let stripped = path_str.strip_suffix(".bin")?;
    Some(PathBuf::from(stripped))
}

fn elapsed_ms(start: Instant) -> u64 {
    start.elapsed().as_millis() as u64
}

fn keccak256(data: &[u8]) -> [u8; 32] {
    let mut hasher = Keccak256::new();
    hasher.update(data);
    hasher.finalize().into()
}

#[cfg(test)]
mod recursion_binding_tests {
    use super::*;
    use execution_utils::unrolled::UnrolledProgramSetup;

    /// The recursion chain a top-layer proof carries for a base program with the given
    /// `end_params` (the value the verifier authenticates in `output[8..16]`).
    fn chain_for_program(base_end_params: [u32; 8]) -> [u32; 8] {
        let (hash_chain, _preimage) = UnrolledProgramSetup::begin_recursion_chain(&base_end_params);
        hash_chain
    }

    fn verifier_output_with_chain(chain: [u32; 8]) -> [u32; 16] {
        let mut out = [0u32; 16];
        out[8..16].copy_from_slice(&chain);
        out
    }

    #[test]
    fn accepts_when_proven_chain_matches_supplied_program() {
        let chain = chain_for_program([1, 2, 3, 4, 5, 6, 7, 8]);
        let output = verifier_output_with_chain(chain);
        assert!(ensure_recursion_chain_binds_program(&output, &chain).is_ok());
    }

    /// Regression test for proof replay across programs: a valid proof generated for
    /// program Q must not verify as a proof for a different program P, even though the
    /// program-hash metadata can be freely rewritten to P's hashes.
    #[test]
    fn rejects_proof_whose_chain_encodes_a_different_program() {
        // Two distinct base programs produce two distinct authenticated chains.
        let chain_p = chain_for_program([10, 11, 12, 13, 14, 15, 16, 17]);
        let chain_q = chain_for_program([99, 98, 97, 96, 95, 94, 93, 92]);
        assert_ne!(
            chain_p, chain_q,
            "different programs must yield different chains"
        );

        // The attacker holds a valid proof for Q; the verifier authenticates Q's chain.
        let proven_output = verifier_output_with_chain(chain_q);

        // Claiming it is a proof for P must be rejected by the binding check.
        let err = ensure_recursion_chain_binds_program(&proven_output, &chain_p)
            .expect_err("a proof whose chain encodes a different program must be rejected");
        assert!(
            err.contains("does not match the supplied program"),
            "unexpected error message: {err}"
        );

        // And it still verifies against the program it was actually generated for.
        assert!(ensure_recursion_chain_binds_program(&proven_output, &chain_q).is_ok());
    }

    #[test]
    fn rejects_base_chain_when_target_claims_recursion_unrolled() {
        let base_end_params = [1, 2, 3, 4, 5, 6, 7, 8];
        let unrolled_end_params = [11, 12, 13, 14, 15, 16, 17, 18];
        let (base_chain, base_preimage) =
            UnrolledProgramSetup::begin_recursion_chain(&base_end_params);
        let (unrolled_chain, _) = UnrolledProgramSetup::continue_recursion_chain(
            &unrolled_end_params,
            &base_chain,
            &base_preimage,
        );

        let base_output = verifier_output_with_chain(base_chain);
        let err = ensure_unrolled_target_binds_program(&base_output, &unrolled_chain)
            .expect_err("base output chain must not satisfy a recursion-unrolled target");
        assert!(
            err.contains("does not match the supplied program"),
            "unexpected error message: {err}"
        );
    }

    #[test]
    fn accepts_unrolled_chain_for_recursion_unrolled_target() {
        let base_end_params = [21, 22, 23, 24, 25, 26, 27, 28];
        let unrolled_end_params = [31, 32, 33, 34, 35, 36, 37, 38];
        let (base_chain, base_preimage) =
            UnrolledProgramSetup::begin_recursion_chain(&base_end_params);
        let (unrolled_chain, _) = UnrolledProgramSetup::continue_recursion_chain(
            &unrolled_end_params,
            &base_chain,
            &base_preimage,
        );

        let unrolled_output = verifier_output_with_chain(unrolled_chain);
        assert!(ensure_unrolled_target_binds_program(&unrolled_output, &unrolled_chain).is_ok());
    }

    fn minimal_artifact(security_level: SecurityLevel, target: ProofTarget) -> ProofArtifact {
        ProofArtifact {
            schema_version: 1,
            security_level,
            target,
            backend: ProverBackend::Cpu,
            batch_id: 0,
            cycles: 0,
            program_bin_keccak: [0u8; 32],
            program_text_keccak: [0u8; 32],
            timings_ms: ProofTimingsMs::default(),
            proof_counts: ProofCounts::default(),
            proof: UnrolledProgramProof {
                final_pc: 0,
                final_timestamp: 0,
                circuit_families_proofs: Default::default(),
                inits_and_teardowns_proofs: vec![],
                delegation_proofs: Default::default(),
                register_final_values: [trace_and_split::FinalRegisterValue {
                    value: 0,
                    last_access_timestamp: 0,
                }; 32],
                recursion_chain_preimage: None,
                recursion_chain_hash: None,
                pow_challenge: 0,
            },
        }
    }

    #[test]
    fn rejects_verification_policy_with_mismatched_security_level() {
        let artifact = minimal_artifact(SecurityLevel::Security80, ProofTarget::Base);
        let err = validate_trusted_verification_policy(
            &artifact,
            SecurityLevel::Security100,
            ProofTarget::Base,
        )
        .expect_err("verification must reject artifacts whose metadata disagrees with the trusted security level");
        assert!(
            err.contains("does not match requested security level"),
            "unexpected error message: {err}"
        );
    }

    #[test]
    fn rejects_verification_policy_with_mismatched_target() {
        let artifact = minimal_artifact(SecurityLevel::Security80, ProofTarget::Base);
        let err = validate_trusted_verification_policy(
            &artifact,
            SecurityLevel::Security80,
            ProofTarget::RecursionUnified,
        )
        .expect_err(
            "verification must reject artifacts whose metadata disagrees with the trusted target",
        );
        assert!(
            err.contains("does not match requested target"),
            "unexpected error message: {err}"
        );
    }

    #[test]
    fn rejects_unified_target_before_security100_convergence() {
        let err = ensure_unified_recursion_target_converged(SecurityLevel::Security100, 1)
            .expect_err("Security100 must require two unified family proofs");
        assert!(
            err.contains("has not converged"),
            "unexpected error message: {err}"
        );
    }

    #[test]
    fn accepts_unified_target_after_security100_convergence() {
        assert!(ensure_unified_recursion_target_converged(SecurityLevel::Security100, 2).is_ok());
    }

    #[test]
    fn rejects_combining_fewer_than_two_artifacts() {
        let artifact = minimal_artifact(SecurityLevel::Security80, ProofTarget::RecursionUnified);
        let source = ProgramSource::from_paths("app.bin".to_string(), None);
        let err = combine_artifacts(
            &[artifact],
            &source,
            SecurityLevel::Security80,
            &CpuConfig::default(),
        )
        .expect_err("combining must require at least two artifacts");
        assert!(
            err.contains("at least two proof artifacts"),
            "unexpected error message: {err}"
        );
    }

    fn stamp_recursion_chain(artifact: &mut ProofArtifact, preimage: [u32; 16]) {
        let mut hasher = Blake2sBufferingTranscript::new();
        hasher.absorb(&preimage);
        artifact.proof.recursion_chain_preimage = Some(preimage);
        artifact.proof.recursion_chain_hash = Some(hasher.finalize().0);
    }

    #[test]
    fn carried_chain_combine_rejects_inputs_without_chain() {
        let artifact_1 = minimal_artifact(SecurityLevel::Security80, ProofTarget::RecursionUnified);
        let artifact_2 = minimal_artifact(SecurityLevel::Security80, ProofTarget::RecursionUnified);
        let err = combine_artifacts_carried_chain(
            &[artifact_1, artifact_2],
            SecurityLevel::Security80,
            &CpuConfig::default(),
        )
        .expect_err("inputs without a carried recursion chain must be rejected");
        assert!(
            err.contains("recursion_chain"),
            "unexpected error message: {err}"
        );
    }

    #[test]
    fn carried_chain_combine_rejects_mismatched_chains() {
        let mut artifact_1 =
            minimal_artifact(SecurityLevel::Security80, ProofTarget::RecursionUnified);
        let mut artifact_2 =
            minimal_artifact(SecurityLevel::Security80, ProofTarget::RecursionUnified);
        stamp_recursion_chain(&mut artifact_1, [1u32; 16]);
        stamp_recursion_chain(&mut artifact_2, [2u32; 16]);
        let err = combine_artifacts_carried_chain(
            &[artifact_1, artifact_2],
            SecurityLevel::Security80,
            &CpuConfig::default(),
        )
        .expect_err("inputs carrying different recursion chains must be rejected");
        assert!(
            err.contains("different recursion chain"),
            "unexpected error message: {err}"
        );
    }

    #[test]
    fn rejects_recursion_combined_as_proving_target() {
        let source = ProgramSource::from_paths("app.bin".to_string(), None);
        let config = ProgramProverConfig {
            target: ProofTarget::RecursionCombined,
            backend: ProverBackend::Cpu,
            ..Default::default()
        };
        let err = ProgramProver::new(source, config)
            .err()
            .expect("recursion-combined must not be a direct proving target");
        assert!(err.contains("combine"), "unexpected error message: {err}");
    }

    /// End-to-end: prove a small program twice through the full CPU pipeline
    /// (base -> unrolled recursion -> unified recursion), then combine the two
    /// recursion-unified artifacts into a single proof and check that its output
    /// is the keccak rolling hash of the two proofs' outputs with the shared
    /// recursion chain carried through. `combine_artifacts` itself re-verifies
    /// the combined proof against the expected output before returning.
    #[test]
    #[ignore = "manual heavy proving test"]
    fn test_combine_recursion_unified_artifacts() {
        test_utils::skip_if_ci!();

        let source =
            ProgramSource::from_paths("../../examples/opcode_smoke/app.bin".to_string(), None);
        let input_hex = std::fs::read_to_string("../../examples/opcode_smoke/input.txt")
            .expect("opcode_smoke input");
        let input_words = u32_from_hex_string(input_hex.trim());

        let security_level = SecurityLevel::Security80;
        let cpu = CpuConfig {
            cycles_bound: 1 << 24,
            ram_bound: 1 << 30,
            worker_threads: None,
        };
        let config = ProgramProverConfig {
            security_level,
            target: ProofTarget::RecursionUnified,
            backend: ProverBackend::Cpu,
            cpu: cpu.clone(),
            gpu: GpuConfig::default(),
        };

        let prover = ProgramProver::new(source.clone(), config).expect("prover");
        let artifact_1 = prover.prove_words(0, input_words.clone()).expect("proof 1");
        let artifact_2 = prover.prove_words(1, input_words).expect("proof 2");

        let output_1 = verify_artifact(
            &artifact_1,
            &source,
            security_level,
            ProofTarget::RecursionUnified,
        )
        .expect("proof 1 verifies");
        let output_2 = verify_artifact(
            &artifact_2,
            &source,
            security_level,
            ProofTarget::RecursionUnified,
        )
        .expect("proof 2 verifies");

        let artifacts = [artifact_1, artifact_2];
        let combined_artifact = combine_artifacts(&artifacts, &source, security_level, &cpu)
            .expect("combining succeeds");

        let combined_output = verify_artifact(
            &combined_artifact,
            &source,
            security_level,
            ProofTarget::RecursionCombined,
        )
        .expect("combined proof verifies");

        let expected_output =
            execution_utils::unified_circuit::compute_combined_recursion_layers_output(&[
                output_1, output_2,
            ]);
        assert_eq!(combined_output, expected_output);

        // The carried-chain variant must combine the same inputs without access to the
        // program files and prove the same combined statement. A single combiner is
        // reused across two combines to cover the cached-state path: the second call
        // must reuse the warm unified-level setup and produce the same output.
        let mut combiner = CarriedChainCombiner::new_cpu(security_level, cpu.clone());
        for round in 0..2 {
            let combined_detached = combiner
                .combine(&artifacts)
                .unwrap_or_else(|e| panic!("carried-chain combine round {round} succeeds: {e}"));
            let detached_output = verify_artifact(
                &combined_detached,
                &source,
                security_level,
                ProofTarget::RecursionCombined,
            )
            .expect("carried-chain combined proof verifies");
            assert_eq!(detached_output, expected_output);
        }
    }
}
