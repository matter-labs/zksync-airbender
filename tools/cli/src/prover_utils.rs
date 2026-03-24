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
use execution_utils::unrolled_gpu::{UnrolledProver, UnrolledProverLevel};
use execution_utils::verifier_binaries::{
    RECURSION_UNIFIED_BIN, RECURSION_UNIFIED_TXT, RECURSION_UNROLLED_BIN, RECURSION_UNROLLED_TXT,
};
use prover::transcript::Blake2sBufferingTranscript;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::cycle::{
    IMStandardIsaConfigWithUnsignedMulDiv, IWithoutByteAccessIsaConfigWithDelegation,
};
use serde::{Deserialize, Serialize};
use sha3::{Digest, Keccak256};
use std::path::{Path, PathBuf};
use std::time::Instant;

#[cfg(all(feature = "security_80", feature = "security_100"))]
compile_error!("multiple security levels selected at the same time");
#[cfg(all(not(feature = "security_80"), not(feature = "security_100")))]
compile_error!(
    "one security level must be selected: enable either `security_80` or `security_100`"
);

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum SecurityLevel {
    Security80,
    Security100,
}

#[cfg(feature = "security_80")]
pub const COMPILED_SECURITY_LEVEL: SecurityLevel = SecurityLevel::Security80;
#[cfg(feature = "security_100")]
pub const COMPILED_SECURITY_LEVEL: SecurityLevel = SecurityLevel::Security100;

#[cfg(feature = "security_80")]
const UNIFIED_RECURSION_TARGET_FAMILY_PROOFS: usize = 1;
#[cfg(feature = "security_100")]
const UNIFIED_RECURSION_TARGET_FAMILY_PROOFS: usize = 2;

fn unified_recursion_has_converged(family_proof_count: usize) -> bool {
    // Unified recursion converges once proof shape reaches target size.
    family_proof_count == UNIFIED_RECURSION_TARGET_FAMILY_PROOFS
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, ValueEnum)]
pub enum ProofTarget {
    Base,
    RecursionUnrolled,
    RecursionUnified,
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
    pub target: ProofTarget,
    pub backend: ProverBackend,
    pub cpu: CpuConfig,
    pub gpu: GpuConfig,
}

impl Default for ProgramProverConfig {
    fn default() -> Self {
        Self {
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
                    };

                    ProgramProverInner::Gpu(UnrolledProver::new(
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
            self.config.target,
            self.config.backend,
            batch_id,
            cycles,
            &loaded,
            timings,
            proof,
        ))
    }

    fn prove_words_cpu(
        &self,
        batch_id: u64,
        input_words: Vec<u32>,
    ) -> Result<ProofArtifact, String> {
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
                self.config.target,
                self.config.backend,
                batch_id,
                cycles,
                &loaded,
                timings,
                proof,
            ));
        }

        let base_level = make_base_level_data(&loaded);
        let recursion_unrolled =
            load_embedded_program(RECURSION_UNROLLED_BIN, RECURSION_UNROLLED_TXT);
        let unrolled_level = make_unrolled_recursion_level_data(&base_level, &recursion_unrolled);
        proof = continue_with_unrolled_recursion(
            proof,
            &mut timings,
            &self.config.cpu,
            &worker,
            &base_level,
            &unrolled_level,
            &recursion_unrolled,
        );

        if self.config.target == ProofTarget::RecursionUnrolled {
            return Ok(finalize_artifact(
                self.config.target,
                self.config.backend,
                batch_id,
                cycles,
                &loaded,
                timings,
                proof,
            ));
        }

        let recursion_unified = load_embedded_program(RECURSION_UNIFIED_BIN, RECURSION_UNIFIED_TXT);
        let unified_level = make_unified_recursion_level_data(&unrolled_level, &recursion_unified);
        proof = continue_with_unified_recursion(
            proof,
            &mut timings,
            &self.config.cpu,
            &worker,
            &unrolled_level,
            &unified_level,
            &recursion_unified,
        );

        Ok(finalize_artifact(
            self.config.target,
            self.config.backend,
            batch_id,
            cycles,
            &loaded,
            timings,
            proof,
        ))
    }

    fn continue_artifact_cpu(&self, artifact: ProofArtifact) -> Result<ProofArtifact, String> {
        validate_continuation_request(&artifact, self.config.target, self.config.backend)?;

        // Continuation still reuses the CPU proving pipeline. We only swap in the
        // persisted proof artifact as the previous stage instead of reproving base.
        let loaded = load_and_validate_program(&self.source, &artifact)?;
        let worker = make_cpu_worker(&self.config.cpu);

        let input_target = artifact.target;
        let batch_id = artifact.batch_id;
        let cycles = artifact.cycles;
        let mut timings = artifact.timings_ms;
        let mut proof = artifact.proof;

        let base_level = make_base_level_data(&loaded);
        let recursion_unrolled =
            load_embedded_program(RECURSION_UNROLLED_BIN, RECURSION_UNROLLED_TXT);
        let unrolled_level = make_unrolled_recursion_level_data(&base_level, &recursion_unrolled);

        if input_target == ProofTarget::Base {
            proof = continue_with_unrolled_recursion(
                proof,
                &mut timings,
                &self.config.cpu,
                &worker,
                &base_level,
                &unrolled_level,
                &recursion_unrolled,
            );
        }

        if self.config.target == ProofTarget::RecursionUnrolled {
            return Ok(finalize_artifact(
                self.config.target,
                self.config.backend,
                batch_id,
                cycles,
                &loaded,
                timings,
                proof,
            ));
        }

        let recursion_unified = load_embedded_program(RECURSION_UNIFIED_BIN, RECURSION_UNIFIED_TXT);
        let unified_level = make_unified_recursion_level_data(&unrolled_level, &recursion_unified);
        proof = continue_with_unified_recursion(
            proof,
            &mut timings,
            &self.config.cpu,
            &worker,
            &unrolled_level,
            &unified_level,
            &recursion_unified,
        );

        Ok(finalize_artifact(
            self.config.target,
            self.config.backend,
            batch_id,
            cycles,
            &loaded,
            timings,
            proof,
        ))
    }
}

pub fn verify_artifact(
    artifact: &ProofArtifact,
    source: &ProgramSource,
) -> Result<[u32; 16], String> {
    let loaded = load_and_validate_program(source, artifact)?;

    match artifact.target {
        ProofTarget::Base => {
            let base_level = make_base_level_data(&loaded);
            verify_unrolled_layer_proof(
                &artifact.proof,
                &base_level.setup,
                &base_level.layouts,
                true,
            )
            .map_err(|_| "base proof verification failed".to_string())
        }
        ProofTarget::RecursionUnrolled => {
            let base_level = make_base_level_data(&loaded);
            let recursion_unrolled =
                load_embedded_program(RECURSION_UNROLLED_BIN, RECURSION_UNROLLED_TXT);
            let unrolled_level =
                make_unrolled_recursion_level_data(&base_level, &recursion_unrolled);

            let preimage = validate_recursion_chain(&artifact.proof)?;
            let previous_end_params: [u32; 8] =
                preimage[8..16].try_into().expect("slice with exact length");

            if previous_end_params == base_level.setup.end_params {
                verify_unrolled_layer_proof(
                    &artifact.proof,
                    &base_level.setup,
                    &base_level.layouts,
                    true,
                )
                .map_err(|_| "recursion(unrolled over base) verification failed".to_string())
            } else if previous_end_params == unrolled_level.setup.end_params {
                verify_unrolled_layer_proof(
                    &artifact.proof,
                    &unrolled_level.setup,
                    &unrolled_level.layouts,
                    false,
                )
                .map_err(|_| {
                    "recursion(unrolled over recursion-unrolled) verification failed".to_string()
                })
            } else {
                Err("unable to infer previous layer for recursion-unrolled proof".to_string())
            }
        }
        ProofTarget::RecursionUnified => {
            let loaded_unrolled =
                load_embedded_program(RECURSION_UNROLLED_BIN, RECURSION_UNROLLED_TXT);
            let loaded_unified =
                load_embedded_program(RECURSION_UNIFIED_BIN, RECURSION_UNIFIED_TXT);

            let base_level = make_base_level_data(&loaded);
            let unrolled_level = make_unrolled_recursion_level_data(&base_level, &loaded_unrolled);
            let unified_level = make_unified_recursion_level_data(&unrolled_level, &loaded_unified);

            validate_recursion_chain(&artifact.proof)?;

            verify_proof_in_unified_layer(
                &artifact.proof,
                &unified_level.setup,
                &unified_level.layouts,
                false,
            )
            .map_err(|_| "recursion(unified) verification failed".to_string())
        }
    }
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

fn make_artifact(
    target: ProofTarget,
    backend: ProverBackend,
    batch_id: u64,
    cycles: u64,
    loaded: &LoadedProgram,
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
        security_level: COMPILED_SECURITY_LEVEL,
        target,
        backend,
        batch_id,
        cycles,
        program_bin_keccak: keccak256(&loaded.bin_bytes),
        program_text_keccak: keccak256(&loaded.text_bytes),
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
        );
        timings.unified_recursion_ms.push(elapsed_ms(start));

        new_proof.recursion_chain_hash = Some(previous_level.hash_chain);
        new_proof.recursion_chain_preimage = Some(previous_level.preimage);
        proof = new_proof;

        let (family_count, _, _) = proof.get_proof_counts();
        if unified_recursion_has_converged(family_count) {
            break;
        }

        unified_level_idx += 1;
    }

    proof
}

fn finalize_artifact(
    target: ProofTarget,
    backend: ProverBackend,
    batch_id: u64,
    cycles: u64,
    loaded: &LoadedProgram,
    mut timings: ProofTimingsMs,
    proof: UnrolledProgramProof,
) -> ProofArtifact {
    timings.total_ms = aggregate_timing_ms(&timings);
    make_artifact(target, backend, batch_id, cycles, loaded, timings, proof)
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
) -> Result<LoadedProgram, String> {
    let loaded = load_program(source)?;
    validate_artifact_against_program(artifact, &loaded)?;
    Ok(loaded)
}

fn validate_artifact_against_program(
    artifact: &ProofArtifact,
    loaded: &LoadedProgram,
) -> Result<(), String> {
    if artifact.security_level != COMPILED_SECURITY_LEVEL {
        return Err(format!(
            "proof security level ({:?}) does not match binary security level ({:?})",
            artifact.security_level, COMPILED_SECURITY_LEVEL
        ));
    }

    let actual_bin_keccak = keccak256(&loaded.bin_bytes);
    if actual_bin_keccak != artifact.program_bin_keccak {
        return Err(
            "proof artifact program_bin_keccak does not match provided --bin file".to_string(),
        );
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
