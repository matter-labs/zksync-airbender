//! Backend-generic recursion-ladder driver for the CLI, built on the PR-332
//! proving stack:
//!
//! - CPU proving: `prover_examples::{unrolled,unified}::prove_*_execution_with_replayer`.
//! - GPU proving (behind the `gpu` feature): `execution_prover::ExecutionProver`
//!   + `program_prover::assemble_program_proof`.
//! - Protocol helpers (ND streams, end-params, recursion chain, fsv binaries,
//!   native verification): `full_statement_verifier::host_utils`.
//!
//! The ladder mirrors `prover_examples::recursion`'s pipeline (and its GPU
//! twin, `program_prover::tests::run_gpu_recursive_pipeline`):
//!
//!   base (unrolled, full-unsigned ISA)
//!   → unrolled recursion rungs (reduced ISA, fsv verifier binaries) while the
//!     measured verifier run stays at/above `unified_switch_cycles()`
//!   → bridge (the unrolled verifier proved in UNIFIED machine mode)
//!   → final (fsv_unified_recursion_layer, unified mode)

use clap::ValueEnum;
use full_statement_verifier::host_utils::{
    bridge_blake_mode, build_unified_stream, build_unrolled_stream, compute_end_params,
    final_blake_mode, load_fsv_program, native_verify_unified, native_verify_unrolled,
    unified_switch_cycles, unrolled_blake_mode, FsvRecursionChain,
};
use full_statement_verifier::program_proof::ProgramProof;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::cycle::{
    IMStandardIsaConfigUnsignedMulDivOnly, ReducedMachineWithDelegation,
};
use serde::{Deserialize, Serialize};
use setups::Setups;
use sha3::{Digest, Keccak256};
use std::alloc::Global;
use std::path::{Path, PathBuf};
use std::time::Instant;
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

#[cfg(all(feature = "security_80", feature = "security_100"))]
compile_error!("multiple security levels selected at the same time");
#[cfg(all(not(feature = "security_80"), not(feature = "security_100")))]
compile_error!(
    "one security level must be selected: enable either `security_80` or `security_100`"
);

/// Serde-friendly mirror of `prover::definitions::SecurityLevel` (which does
/// not derive serde) for the persisted artifact.
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum SecurityLevel {
    Sec80,
    Sec100,
}

impl SecurityLevel {
    pub fn to_prover(self) -> prover::definitions::SecurityLevel {
        match self {
            SecurityLevel::Sec80 => prover::definitions::SecurityLevel::Sec80,
            SecurityLevel::Sec100 => prover::definitions::SecurityLevel::Sec100,
        }
    }
}

#[cfg(feature = "security_80")]
pub const COMPILED_SECURITY_LEVEL: SecurityLevel = SecurityLevel::Sec80;
#[cfg(feature = "security_100")]
pub const COMPILED_SECURITY_LEVEL: SecurityLevel = SecurityLevel::Sec100;

// Per-stage cycle bounds, mirroring prover_examples::recursion.
const UNROLLED_RECURSION_CYCLES_BOUND: usize = 1 << 28;
const UNIFIED_CYCLES_BOUND: usize = 1 << 27;

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
}

#[derive(Clone, Debug, Serialize, Deserialize, Default)]
pub struct ProofTimingsMs {
    pub total_ms: u64,
    pub base_ms: u64,
    pub unrolled_recursion_ms: Vec<u64>,
    pub unified_recursion_ms: Vec<u64>,
}

/// Summary counts derivable from the stored `ProgramProof`; persisted for
/// quick inspection without loading the proof body.
#[derive(Clone, Debug, Serialize, Deserialize, Default)]
pub struct ProofCounts {
    pub riscv_proof_count: usize,
    pub riscv_proof_count_by_family: Vec<(u32, usize)>,
    pub inits_and_teardowns_proof_count: usize,
    pub delegation_proof_count: usize,
    pub delegation_proof_count_by_type: Vec<(u32, usize)>,
}

impl ProofCounts {
    fn from_proof(proof: &ProgramProof) -> Self {
        Self {
            riscv_proof_count: proof.riscv_proofs.values().map(|v| v.len()).sum(),
            riscv_proof_count_by_family: proof
                .riscv_proofs
                .iter()
                .map(|(k, v)| (*k, v.len()))
                .collect(),
            inits_and_teardowns_proof_count: proof.inits_and_teardown_proofs.len(),
            delegation_proof_count: proof.delegation_proofs.values().map(|v| v.len()).sum(),
            delegation_proof_count_by_type: proof
                .delegation_proofs
                .iter()
                .map(|(k, v)| (*k, v.len()))
                .collect(),
        }
    }
}

/// Proof artifact, schema v2 (PR-332 stack). `proof` + `setups` are enough to
/// verify natively; `chain_end_params` is the ordered list of layer
/// `end_params` from base onward, from which the recursion chain state after
/// this artifact's layer (`chain_hash` / `chain_preimage`) is reconstructed
/// for staged continuation.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProofArtifact {
    pub schema_version: u32,
    pub security_level: SecurityLevel,
    pub target: ProofTarget,
    pub backend: ProverBackend,
    pub batch_id: u64,
    /// `proof.executed_cycles()` of the artifact's (final) proof layer.
    pub cycles: u64,
    pub program_bin_keccak: [u8; 32],
    pub program_text_keccak: [u8; 32],
    pub timings_ms: ProofTimingsMs,
    pub proof_counts: ProofCounts,
    /// Layer end-params history: `[base, rung_1, .., bridge, final]`.
    pub chain_end_params: Vec<[u32; 8]>,
    /// Recursion-chain state AFTER this artifact's layer.
    pub chain_hash: [u32; 8],
    pub chain_preimage: [u32; 16],
    /// Blake-mode tags of the fsv verifier binaries the ladder used
    /// (`BlakeMode::tag()` values). Untrusted CLAIM data: at verification
    /// time they only select among the checked-in trusted fsv binaries, so a
    /// lie makes the chain-binding comparison fail.
    #[serde(default = "default_blake_tag")]
    pub blake_unrolled: String,
    #[serde(default = "default_blake_tag")]
    pub blake_bridge: String,
    #[serde(default = "default_blake_tag")]
    pub blake_final: String,
    pub proof: ProgramProof,
    pub setups: Setups,
}

pub const ARTIFACT_SCHEMA_VERSION: u32 = 2;

fn default_blake_tag() -> String {
    BlakeMode::Compression.tag().to_string()
}

// ==============================================================================
// Backend abstraction
// ==============================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LadderKind {
    Unrolled,
    Unified,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LadderMachine {
    FullUnsigned,
    Reduced,
}

/// One required op: prove `bin`/`text` (UNPADDED words; backends pad as they
/// need) in the given machine/kind with `nd_words` as the non-determinism
/// stream, returning the assembled `(ProgramProof, Setups)` pair.
pub trait ProveBackend {
    fn prove(
        &mut self,
        batch_id: u64,
        bin: &[u32],
        text: &[u32],
        kind: LadderKind,
        machine: LadderMachine,
        cycles_bound: usize,
        nd_words: Vec<u32>,
    ) -> Result<(ProgramProof, Setups), String>;
}

pub struct CpuBackend {
    cpu: CpuConfig,
    worker: worker::Worker,
}

impl CpuBackend {
    pub fn new(cpu: CpuConfig) -> Self {
        let worker = if let Some(threads) = cpu.worker_threads {
            worker::Worker::new_with_num_threads(threads)
        } else {
            worker::Worker::new()
        };
        Self { cpu, worker }
    }
}

impl ProveBackend for CpuBackend {
    fn prove(
        &mut self,
        _batch_id: u64,
        bin: &[u32],
        text: &[u32],
        kind: LadderKind,
        machine: LadderMachine,
        cycles_bound: usize,
        nd_words: Vec<u32>,
    ) -> Result<(ProgramProof, Setups), String> {
        // The CPU provers require ROM-word-padded inputs (idempotent for
        // already-padded fsv binaries).
        let mut padded_bin = bin.to_vec();
        let mut padded_text = text.to_vec();
        setups::pad_bytecode_for_proving(&mut padded_bin);
        setups::pad_bytecode_for_proving(&mut padded_text);

        let use_caches = true;
        let security_level = COMPILED_SECURITY_LEVEL.to_prover();
        let source = QuasiUARTSource::new_with_reads(nd_words);

        let result = match kind {
            LadderKind::Unrolled => match machine {
                LadderMachine::FullUnsigned => {
                    prover_examples::unrolled::prove_unrolled_execution_with_replayer::<
                        IMStandardIsaConfigUnsignedMulDivOnly,
                        Global,
                    >(
                        cycles_bound,
                        &padded_bin,
                        &padded_text,
                        use_caches,
                        source,
                        self.cpu.ram_bound,
                        &self.worker,
                        security_level,
                        0,
                    )
                }
                LadderMachine::Reduced => {
                    prover_examples::unrolled::prove_unrolled_execution_with_replayer::<
                        ReducedMachineWithDelegation,
                        Global,
                    >(
                        cycles_bound,
                        &padded_bin,
                        &padded_text,
                        use_caches,
                        source,
                        self.cpu.ram_bound,
                        &self.worker,
                        security_level,
                        0,
                    )
                }
            },
            LadderKind::Unified => {
                if machine != LadderMachine::Reduced {
                    return Err("unified proving supports only the reduced machine".to_string());
                }
                prover_examples::unified::prove_unified_execution_with_replayer::<Global>(
                    cycles_bound,
                    &padded_bin,
                    &padded_text,
                    use_caches,
                    source,
                    self.cpu.ram_bound,
                    &self.worker,
                    security_level,
                    0,
                )
            }
        };
        Ok(result)
    }
}

#[cfg(feature = "gpu")]
pub struct GpuBackend {
    prover: execution_prover::ExecutionProver,
    security_level: prover::definitions::SecurityLevel,
    worker: worker::Worker,
    // Cache handles so ladder stages / batch items reuse per-binary GPU
    // precomputations instead of re-adding the same program.
    handles: std::collections::BTreeMap<(u8, u8, [u8; 32]), execution_prover::BinaryHandle>,
}

#[cfg(feature = "gpu")]
impl GpuBackend {
    pub fn new(gpu: &GpuConfig) -> Result<Self, String> {
        let mut configuration = execution_prover::ExecutionProverConfiguration::default();
        configuration.replay_worker_threads_count = gpu.replay_worker_threads_count;
        configuration.security_level = COMPILED_SECURITY_LEVEL.to_prover();
        let security_level = configuration.security_level;
        let prover = execution_prover::ExecutionProver::with_configuration(configuration)
            .map_err(|e| format!("failed to create GPU execution prover: {e:?}"))?;
        Ok(Self {
            prover,
            security_level,
            worker: worker::Worker::new(),
            handles: std::collections::BTreeMap::new(),
        })
    }
}

#[cfg(feature = "gpu")]
impl ProveBackend for GpuBackend {
    fn prove(
        &mut self,
        batch_id: u64,
        bin: &[u32],
        text: &[u32],
        kind: LadderKind,
        machine: LadderMachine,
        _cycles_bound: usize,
        nd_words: Vec<u32>,
    ) -> Result<(ProgramProof, Setups), String> {
        use execution_prover::{ExecutionKind, MachineType};

        let execution_kind = match kind {
            LadderKind::Unrolled => ExecutionKind::Unrolled,
            LadderKind::Unified => ExecutionKind::Unified,
        };
        let machine_type = match machine {
            LadderMachine::FullUnsigned => MachineType::FullUnsigned,
            LadderMachine::Reduced => MachineType::Reduced,
        };

        let mut hasher = Keccak256::new();
        for word in bin.iter().chain(text.iter()) {
            hasher.update(word.to_le_bytes());
        }
        let key = (kind as u8, machine as u8, hasher.finalize().into());

        let handle = if let Some(handle) = self.handles.get(&key) {
            *handle
        } else {
            // `add_binary` pads internally; pass the words as loaded.
            let handle = self.prover.add_binary(
                execution_kind,
                machine_type,
                bin.to_vec(),
                text.to_vec(),
                None,
            );
            self.handles.insert(key, handle);
            handle
        };

        let result = self.prover.commit_memory_and_prove(
            batch_id,
            &handle,
            QuasiUARTSource::new_with_reads(nd_words),
        );
        let artifacts = self.prover.program_artifacts(&handle);
        Ok(program_prover::assemble_program_proof(
            &artifacts,
            result,
            self.security_level,
            &self.worker,
        ))
    }
}

// ==============================================================================
// Ladder driver
// ==============================================================================

struct LadderState {
    proof: ProgramProof,
    setups: Setups,
    chain_end_params: Vec<[u32; 8]>,
    /// Whether `proof` is a base-layer proof (drives fsv-program selection and
    /// stream/verification flavor).
    input_is_base: bool,
    timings: ProofTimingsMs,
}

fn rebuild_chain(chain_end_params: &[[u32; 8]]) -> Result<FsvRecursionChain, String> {
    let (first, rest) = chain_end_params
        .split_first()
        .ok_or_else(|| "artifact chain_end_params is empty".to_string())?;
    let mut chain = FsvRecursionChain::begin(first);
    for end_params in rest {
        chain.extend(end_params);
    }
    Ok(chain)
}

/// Directory holding the `fsv_*` verifier binaries. Overridable via `FSV_DIR`;
/// defaults to the in-repo `tools/gkr_verifier` (this is a dev tool — the
/// default assumes the binary runs near its source checkout).
fn fsv_dir() -> PathBuf {
    if let Ok(dir) = std::env::var("FSV_DIR") {
        return PathBuf::from(dir);
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../gkr_verifier")
}

/// Run (without proving) the reduced-machine verifier program over `stream`
/// and return the number of cycles it executes. Mirrors
/// `prover_examples::recursion::measure_verifier_cycles`; the reduced-machine
/// VM run is inlined (calling `run_unrolled_machine_in_full` across crates
/// trips a rustc E0391 normalization cycle on its const-generic return type).
fn measure_verifier_cycles(bin: &[u32], text: &[u32], stream: Vec<u32>, ram_bound: usize) -> u64 {
    use common_constants::{INITIAL_TIMESTAMP, TIMESTAMP_STEP};
    use prover::field::baby_bear::base::BabyBearField;
    use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, Instruction};
    use riscv_transpiler::ir::ReducedMachineDecoderConfig;
    use riscv_transpiler::vm::{
        DelegationsAndUnifiedCounters, RamWithRomRegion, SimpleSnapshotter, SimpleTape, State, VM,
    };
    const ROM_BITS: usize = common_constants::ROM_SECOND_WORD_BITS;

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<ReducedMachineDecoderConfig, true>(text);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<ROM_BITS>::from_rom_content(bin, ram_bound);
    let mut state = State::initial_with_counters(DelegationsAndUnifiedCounters::default());
    let mut snapshotter =
        SimpleSnapshotter::<DelegationsAndUnifiedCounters, ROM_BITS>::new_with_cycle_limit(
            UNROLLED_RECURSION_CYCLES_BOUND,
            state,
        );
    let mut non_determinism = QuasiUARTSource::new_with_reads(stream);
    let finished = VM::<DelegationsAndUnifiedCounters>::run_basic_unrolled::<_, _, _, BabyBearField>(
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

/// Advance a proof at some ladder position to `target`. `state.proof` must be
/// either a base proof or an unrolled recursion proof (never unified).
fn advance_to_target(
    backend: &mut dyn ProveBackend,
    mut state: LadderState,
    target: ProofTarget,
    batch_id: u64,
    ram_bound: usize,
) -> Result<LadderState, String> {
    if target == ProofTarget::Base {
        return Ok(state);
    }

    let fsv_dir = fsv_dir();
    let mut chain = rebuild_chain(&state.chain_end_params)?;
    let switch_cycles = unified_switch_cycles();

    // === Unrolled recursion rungs. ===
    let unrolled_blake = unrolled_blake_mode();
    let (unrolled_base_bin, unrolled_base_text) =
        load_fsv_program(&fsv_dir, FsvProgram::UnrolledBaseLayer, unrolled_blake);
    let (unrolled_rec_bin, unrolled_rec_text) =
        load_fsv_program(&fsv_dir, FsvProgram::UnrolledRecursionLayer, unrolled_blake);

    loop {
        let (bin, text) = if state.input_is_base {
            (&unrolled_base_bin, &unrolled_base_text)
        } else {
            (&unrolled_rec_bin, &unrolled_rec_text)
        };
        let measured = measure_verifier_cycles(
            bin,
            text,
            build_unrolled_stream(&state.setups, &state.proof),
            ram_bound,
        );
        log::info!("verifying the current proof would take {measured} cycles");
        if measured < switch_cycles {
            log::info!("... below {switch_cycles} — stopping the unrolled recursion loop");
            break;
        }

        let start = Instant::now();
        let (mut new_proof, new_setups) = backend.prove(
            batch_id,
            bin,
            text,
            LadderKind::Unrolled,
            LadderMachine::Reduced,
            UNROLLED_RECURSION_CYCLES_BOUND,
            build_unrolled_stream(&state.setups, &state.proof),
        )?;
        state.timings.unrolled_recursion_ms.push(elapsed_ms(start));
        new_proof.set_recursion_chain(&chain);

        let end_params = compute_end_params(&new_setups, new_proof.final_pc);
        chain.extend(&end_params);
        state.chain_end_params.push(end_params);
        state.proof = new_proof;
        state.setups = new_setups;
        state.input_is_base = false;
        log::info!(
            "unrolled recursion rung proved ({} cycles)",
            state.proof.executed_cycles()
        );
    }

    if target == ProofTarget::RecursionUnrolled {
        return Ok(state);
    }

    // === Bridge: the unrolled verifier proved in UNIFIED machine mode. ===
    let bridge_program = if state.input_is_base {
        FsvProgram::UnrolledBaseLayer
    } else {
        FsvProgram::UnrolledRecursionLayer
    };
    let (bridge_bin, bridge_text) = load_fsv_program(&fsv_dir, bridge_program, bridge_blake_mode());

    let start = Instant::now();
    let (mut bridge_proof, bridge_setups) = backend.prove(
        batch_id,
        &bridge_bin,
        &bridge_text,
        LadderKind::Unified,
        LadderMachine::Reduced,
        UNIFIED_CYCLES_BOUND,
        build_unrolled_stream(&state.setups, &state.proof),
    )?;
    state.timings.unified_recursion_ms.push(elapsed_ms(start));
    bridge_proof.set_recursion_chain(&chain);
    let bridge_end_params = compute_end_params(&bridge_setups, bridge_proof.final_pc);
    chain.extend(&bridge_end_params);
    state.chain_end_params.push(bridge_end_params);
    log::info!(
        "bridge proved in unified mode ({} cycles)",
        bridge_proof.executed_cycles()
    );

    // === Final: fsv_unified_recursion_layer in unified mode. ===
    let (final_bin, final_text) =
        load_fsv_program(&fsv_dir, FsvProgram::UnifiedRecursionLayer, final_blake_mode());

    let start = Instant::now();
    let (mut final_proof, final_setups) = backend.prove(
        batch_id,
        &final_bin,
        &final_text,
        LadderKind::Unified,
        LadderMachine::Reduced,
        UNIFIED_CYCLES_BOUND,
        build_unified_stream(&bridge_setups, &bridge_proof),
    )?;
    state.timings.unified_recursion_ms.push(elapsed_ms(start));
    final_proof.set_recursion_chain(&chain);
    let final_end_params = compute_end_params(&final_setups, final_proof.final_pc);
    chain.extend(&final_end_params);
    state.chain_end_params.push(final_end_params);
    log::info!(
        "final unified recursion proof done ({} cycles)",
        final_proof.executed_cycles()
    );

    state.proof = final_proof;
    state.setups = final_setups;
    state.input_is_base = false;
    Ok(state)
}

// ==============================================================================
// ProgramProver — the CLI-facing driver
// ==============================================================================

enum BackendImpl {
    Cpu(CpuBackend),
    #[cfg(feature = "gpu")]
    Gpu(GpuBackend),
}

impl BackendImpl {
    fn as_dyn(&mut self) -> &mut dyn ProveBackend {
        match self {
            BackendImpl::Cpu(b) => b,
            #[cfg(feature = "gpu")]
            BackendImpl::Gpu(b) => b,
        }
    }
}

pub struct ProgramProver {
    source: ProgramSource,
    config: ProgramProverConfig,
    backend: BackendImpl,
}

impl ProgramProver {
    pub fn new(source: ProgramSource, config: ProgramProverConfig) -> Result<Self, String> {
        let backend = match config.backend {
            ProverBackend::Cpu => BackendImpl::Cpu(CpuBackend::new(config.cpu.clone())),
            ProverBackend::Gpu => {
                #[cfg(feature = "gpu")]
                {
                    BackendImpl::Gpu(GpuBackend::new(&config.gpu)?)
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
            backend,
        })
    }

    pub fn prove_words(
        &mut self,
        batch_id: u64,
        input_words: Vec<u32>,
    ) -> Result<ProofArtifact, String> {
        let loaded = load_program(&self.source)?;

        // Base layer: the user program, unrolled, full-unsigned ISA.
        let start = Instant::now();
        let (proof, setups) = self.backend.as_dyn().prove(
            batch_id,
            &loaded.bin_u32,
            &loaded.text_u32,
            LadderKind::Unrolled,
            LadderMachine::FullUnsigned,
            self.config.cpu.cycles_bound,
            input_words,
        )?;
        let base_ms = elapsed_ms(start);
        log::info!("base layer proved ({} cycles)", proof.executed_cycles());

        let base_end_params = compute_end_params(&setups, proof.final_pc);
        let state = LadderState {
            proof,
            setups,
            chain_end_params: vec![base_end_params],
            input_is_base: true,
            timings: ProofTimingsMs {
                total_ms: 0,
                base_ms,
                unrolled_recursion_ms: Vec::new(),
                unified_recursion_ms: Vec::new(),
            },
        };

        let state = advance_to_target(
            self.backend.as_dyn(),
            state,
            self.config.target,
            batch_id,
            self.config.cpu.ram_bound,
        )?;

        Ok(finalize_artifact(
            self.config.target,
            self.config.backend,
            batch_id,
            &loaded,
            state,
        ))
    }

    pub fn continue_artifact(&mut self, artifact: ProofArtifact) -> Result<ProofArtifact, String> {
        validate_continuation_request(&artifact, self.config.target)?;
        let loaded = load_and_validate_program(&self.source, &artifact)?;

        let batch_id = artifact.batch_id;
        // A single chain entry (just the base end-params) means no recursion
        // rung ran — the stored proof is a base-layer proof even if the
        // artifact target is RecursionUnrolled.
        let input_is_base = artifact.chain_end_params.len() <= 1;
        let state = LadderState {
            proof: artifact.proof,
            setups: artifact.setups,
            chain_end_params: artifact.chain_end_params,
            input_is_base,
            timings: artifact.timings_ms,
        };

        let state = advance_to_target(
            self.backend.as_dyn(),
            state,
            self.config.target,
            batch_id,
            self.config.cpu.ram_bound,
        )?;

        Ok(finalize_artifact(
            self.config.target,
            self.config.backend,
            batch_id,
            &loaded,
            state,
        ))
    }
}

fn finalize_artifact(
    target: ProofTarget,
    backend: ProverBackend,
    batch_id: u64,
    loaded: &LoadedProgram,
    mut state: LadderState,
) -> ProofArtifact {
    state.timings.total_ms = state.timings.base_ms
        + state.timings.unrolled_recursion_ms.iter().sum::<u64>()
        + state.timings.unified_recursion_ms.iter().sum::<u64>();

    let chain = rebuild_chain(&state.chain_end_params).expect("chain history is non-empty");
    ProofArtifact {
        schema_version: ARTIFACT_SCHEMA_VERSION,
        security_level: COMPILED_SECURITY_LEVEL,
        target,
        backend,
        batch_id,
        cycles: state.proof.executed_cycles(),
        program_bin_keccak: keccak256(&loaded.bin_bytes),
        program_text_keccak: keccak256(&loaded.text_bytes),
        timings_ms: state.timings,
        proof_counts: ProofCounts::from_proof(&state.proof),
        chain_end_params: state.chain_end_params,
        chain_hash: chain.hash(),
        chain_preimage: chain.preimage(),
        // The ladder resolves the blake modes from the environment (see
        // host_utils); record the tags so verification reconstructs the same
        // ladder regardless of the verify-time environment.
        blake_unrolled: unrolled_blake_mode().tag().to_string(),
        blake_bridge: bridge_blake_mode().tag().to_string(),
        blake_final: final_blake_mode().tag().to_string(),
        proof: state.proof,
        setups: state.setups,
    }
}

// ==============================================================================
// Verification
// ==============================================================================

pub fn verify_artifact(
    artifact: &ProofArtifact,
    source: &ProgramSource,
) -> Result<[u32; 16], String> {
    let loaded = load_and_validate_program(source, artifact)?;
    validate_artifact_chain(artifact)?;

    // Trusted per-layer end-params, recomputed from the supplied program and
    // the checked-in fsv binaries (see the program-binding module comment
    // below). Cross-check the artifact's claimed history entry by entry
    // (stronger than internal consistency), then bind the verifier's
    // authenticated output chain to the trusted chain.
    let worker = worker::Worker::new();
    let expected = expected_chain_end_params(artifact, &loaded, &worker)?;
    if expected != artifact.chain_end_params {
        return Err(
            "artifact chain_end_params do not match the trusted per-layer end-params recomputed \
             from the supplied program and the checked-in fsv verifier binaries"
                .to_string(),
        );
    }
    let expected_chain = rebuild_chain(&expected)?;

    // The claim shape decides the statement flavor: a single layer is a
    // base-layer statement (no recursion chain in the stream).
    let is_base = expected.len() == 1;
    let output = match artifact.target {
        ProofTarget::Base | ProofTarget::RecursionUnrolled => native_verify_unrolled(
            build_unrolled_stream(&artifact.setups, &artifact.proof),
            is_base,
        ),
        ProofTarget::RecursionUnified => native_verify_unified(
            build_unified_stream(&artifact.setups, &artifact.proof),
            is_base,
        ),
    };
    ensure_recursion_chain_binds_program(&output, &expected_chain.hash())?;
    Ok(output)
}

// ==============================================================================
// Program binding (port of PR #321, commit a2d7ad19, from the old
// execution_utils-based cli)
// ==============================================================================
//
// The artifact JSON (program_*_keccak, chain_end_params, chain_hash, setups,
// blake tags, ...) is attacker-editable, and the recursion verifier's setup
// is the program-independent embedded verifier — so neither constrains which
// base program a recursion proof actually attests to. The authenticated value
// is the verifier's returned `output[8..16]`: the recursion chain the STARK
// proved. We therefore recompute the EXPECTED chain exclusively from trusted
// inputs — the supplied `--bin`/`--text` and the checked-in
// `tools/gkr_verifier` fsv binaries — and reject unless it matches
// `output[8..16]`. The artifact's chain_end_params / blake tags are only a
// CLAIM of the ladder shape: they select among trusted binaries and trusted
// derivations, so lying about them makes the comparison fail.

/// The reduced-machine exit sequence every provable program ends with.
/// Statically derive the program's exit PC (thin fallible wrapper over
/// `setups::program_setups::find_binary_exit_point`, which panics on a
/// malformed binary).
fn find_binary_exit_point(binary: &[u32]) -> Result<u32, String> {
    std::panic::catch_unwind(|| setups::program_setups::find_binary_exit_point(binary))
        .map_err(|_| "binary has no unique exit sequence".to_string())
}

/// Which setup family a layer's program is proven under.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum SetupMachine {
    /// Unrolled machine, full-unsigned ISA (base user programs).
    UnrolledFullUnsigned,
    /// Unrolled machine, reduced ISA (fsv unrolled verifier layers).
    UnrolledReduced,
    /// Unified reduced machine (bridge + final layers).
    Unified,
}

/// Recompute the per-program `Setups` map for `(binary, machine)` WITHOUT
/// proving, byte-identical to what the provers produce (see
/// `setups::program_setups`).
fn recompute_program_setups(
    bin: &[u32],
    text: &[u32],
    machine: SetupMachine,
    worker: &worker::Worker,
) -> Setups {
    use riscv_transpiler::cycle::IMStandardIsaConfigUnsignedMulDivOnly as FullUnsignedConfig;
    use riscv_transpiler::cycle::ReducedMachineWithDelegation as ReducedConfig;
    use setups::program_setups::{compute_unified_program_setups, compute_unrolled_program_setups};

    let mut padded_bin = bin.to_vec();
    let mut padded_text = text.to_vec();
    setups::pad_bytecode_for_proving(&mut padded_bin);
    setups::pad_bytecode_for_proving(&mut padded_text);

    let use_caches = true;
    let security_level = COMPILED_SECURITY_LEVEL.to_prover();
    match machine {
        SetupMachine::UnrolledFullUnsigned => compute_unrolled_program_setups::<
            FullUnsignedConfig,
            Global,
        >(&padded_bin, &padded_text, use_caches, security_level, worker),
        SetupMachine::UnrolledReduced => compute_unrolled_program_setups::<ReducedConfig, Global>(
            &padded_bin,
            &padded_text,
            use_caches,
            security_level,
            worker,
        ),
        SetupMachine::Unified => compute_unified_program_setups::<Global>(
            &padded_bin,
            &padded_text,
            use_caches,
            security_level,
            worker,
        ),
    }
}

/// Trusted `end_params` of `(binary, machine)`: recomputed setups (cached by
/// binary keccak in-process — the unified setup is expensive, so it is only
/// computed when the claim actually includes unified layers) hashed with the
/// binary's statically derived exit PC.
fn trusted_end_params(
    bin: &[u32],
    text: &[u32],
    machine: SetupMachine,
    worker: &worker::Worker,
) -> Result<[u32; 8], String> {
    use std::sync::{Mutex, OnceLock};
    static CACHE: OnceLock<Mutex<std::collections::HashMap<(SetupMachine, [u8; 32]), [u32; 8]>>> =
        OnceLock::new();

    let mut hasher = Keccak256::new();
    for word in bin.iter().chain(text.iter()) {
        hasher.update(word.to_le_bytes());
    }
    let key = (machine, hasher.finalize().into());

    let cache = CACHE.get_or_init(|| Mutex::new(std::collections::HashMap::new()));
    if let Some(end_params) = cache.lock().unwrap().get(&key) {
        return Ok(*end_params);
    }

    let start = Instant::now();
    let setups = recompute_program_setups(bin, text, machine, worker);
    let exit_pc = find_binary_exit_point(bin)?;
    let end_params = compute_end_params(&setups, exit_pc);
    log::info!("recomputed {machine:?} setups in {} ms", elapsed_ms(start));
    cache.lock().unwrap().insert(key, end_params);
    Ok(end_params)
}

/// Parse a blake tag claimed by the artifact and validate it against the fsv
/// program it selects.
fn parse_blake_tag(tag: &str, program: FsvProgram) -> Result<BlakeMode, String> {
    let mode = BlakeMode::parse(tag)
        .ok_or_else(|| format!("artifact claims unknown blake mode tag {tag:?}"))?;
    if !program.supports(mode) {
        return Err(format!(
            "artifact claims blake mode {tag:?} for an fsv program not built with it"
        ));
    }
    Ok(mode)
}

/// Reconstruct the ladder's per-layer `end_params`, derived ONLY from trusted
/// inputs (the supplied program + checked-in fsv binaries). The artifact
/// contributes only the CLAIM shape: target, number of chain entries, blake
/// tags.
fn expected_chain_end_params(
    artifact: &ProofArtifact,
    loaded: &LoadedProgram,
    worker: &worker::Worker,
) -> Result<Vec<[u32; 8]>, String> {
    let n = artifact.chain_end_params.len();
    let rungs = match artifact.target {
        ProofTarget::Base => {
            if n != 1 {
                return Err(format!("Base artifact must claim exactly 1 layer, got {n}"));
            }
            0
        }
        ProofTarget::RecursionUnrolled => {
            if n < 1 {
                return Err("RecursionUnrolled artifact claims no layers".to_string());
            }
            n - 1
        }
        ProofTarget::RecursionUnified => {
            if n < 3 {
                return Err(format!(
                    "RecursionUnified artifact must claim at least 3 layers \
                     (base + bridge + final), got {n}"
                ));
            }
            n - 3
        }
    };

    let mut expected = Vec::with_capacity(n);
    expected.push(trusted_end_params(
        &loaded.bin_u32,
        &loaded.text_u32,
        SetupMachine::UnrolledFullUnsigned,
        worker,
    )?);

    if artifact.target == ProofTarget::Base {
        return Ok(expected);
    }

    let fsv_dir = fsv_dir();
    let unrolled_blake = parse_blake_tag(&artifact.blake_unrolled, FsvProgram::UnrolledBaseLayer)?;

    for rung in 0..rungs {
        let program = if rung == 0 {
            FsvProgram::UnrolledBaseLayer
        } else {
            FsvProgram::UnrolledRecursionLayer
        };
        let (bin, text) = load_fsv_program(&fsv_dir, program, unrolled_blake);
        expected.push(trusted_end_params(
            &bin,
            &text,
            SetupMachine::UnrolledReduced,
            worker,
        )?);
    }

    if artifact.target == ProofTarget::RecursionUnrolled {
        return Ok(expected);
    }

    // Bridge: the unrolled verifier binary (selected by whether any rung ran)
    // proved on the UNIFIED machine — its end_params use the unified setups.
    let bridge_program = if rungs == 0 {
        FsvProgram::UnrolledBaseLayer
    } else {
        FsvProgram::UnrolledRecursionLayer
    };
    let bridge_blake = parse_blake_tag(&artifact.blake_bridge, bridge_program)?;
    let (bridge_bin, bridge_text) = load_fsv_program(&fsv_dir, bridge_program, bridge_blake);
    expected.push(trusted_end_params(
        &bridge_bin,
        &bridge_text,
        SetupMachine::Unified,
        worker,
    )?);

    // Final: fsv_unified_recursion_layer on the unified machine.
    let final_blake = parse_blake_tag(&artifact.blake_final, FsvProgram::UnifiedRecursionLayer)?;
    let (final_bin, final_text) =
        load_fsv_program(&fsv_dir, FsvProgram::UnifiedRecursionLayer, final_blake);
    expected.push(trusted_end_params(
        &final_bin,
        &final_text,
        SetupMachine::Unified,
        worker,
    )?);

    Ok(expected)
}

/// Bind a verified proof to the program supplied by the caller (PR #321).
///
/// The cryptographic verifier returns the recursion chain it actually proved
/// in `output[8..16]`: for a base-layer proof `begin(end_params)`, for a
/// recursion layer the input chain extended with the verified program's
/// `end_params` (with the same-program no-op rule — see
/// `full_statement_verifier::unrolled_proof_statement`). That chain
/// authenticates the whole tower of verified programs back to the base
/// program. `expected_chain` is derived from the supplied `--bin`/`--text`
/// and the checked-in fsv binaries only; if the proof proved a chain for a
/// different base program, the two differ and we reject.
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

fn validate_artifact_chain(artifact: &ProofArtifact) -> Result<(), String> {
    let chain = rebuild_chain(&artifact.chain_end_params)?;
    if chain.hash() != artifact.chain_hash || chain.preimage() != artifact.chain_preimage {
        return Err(
            "artifact chain_hash/chain_preimage do not match chain_end_params".to_string(),
        );
    }
    Ok(())
}

fn validate_continuation_request(
    artifact: &ProofArtifact,
    target: ProofTarget,
) -> Result<(), String> {
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
    validate_artifact_chain(artifact)
}

// ==============================================================================
// Program loading / misc helpers
// ==============================================================================

struct LoadedProgram {
    bin_bytes: Vec<u8>,
    text_bytes: Vec<u8>,
    /// Unpadded words as loaded from disk (backends pad as needed).
    bin_u32: Vec<u32>,
    text_u32: Vec<u32>,
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

    let (bin_bytes, bin_u32) = setups::read_binary(bin_path);
    let (text_bytes, text_u32) = setups::read_binary(text_path);

    Ok(LoadedProgram {
        bin_bytes,
        text_bytes,
        bin_u32,
        text_u32,
    })
}

fn load_and_validate_program(
    source: &ProgramSource,
    artifact: &ProofArtifact,
) -> Result<LoadedProgram, String> {
    if artifact.schema_version != ARTIFACT_SCHEMA_VERSION {
        return Err(format!(
            "unsupported proof artifact schema_version {} (expected {})",
            artifact.schema_version, ARTIFACT_SCHEMA_VERSION
        ));
    }
    if artifact.security_level != COMPILED_SECURITY_LEVEL {
        return Err(format!(
            "proof security level ({:?}) does not match binary security level ({:?})",
            artifact.security_level, COMPILED_SECURITY_LEVEL
        ));
    }

    let loaded = load_program(source)?;
    if keccak256(&loaded.bin_bytes) != artifact.program_bin_keccak {
        return Err(
            "proof artifact program_bin_keccak does not match provided --bin file".to_string(),
        );
    }
    if keccak256(&loaded.text_bytes) != artifact.program_text_keccak {
        return Err(
            "proof artifact program_text_keccak does not match provided --text file".to_string(),
        );
    }
    Ok(loaded)
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

/// Port of PR #321's `recursion_binding_tests`, adapted to
/// `FsvRecursionChain` (no proving required).
#[cfg(test)]
mod recursion_binding_tests {
    use super::*;

    /// The recursion chain a top-layer proof carries for a base program with
    /// the given `end_params` (the value the verifier authenticates in
    /// `output[8..16]`).
    fn chain_for_program(base_end_params: [u32; 8]) -> [u32; 8] {
        FsvRecursionChain::begin(&base_end_params).hash()
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

    /// Regression test for proof replay across programs: a valid proof
    /// generated for program Q must not verify as a proof for a different
    /// program P, even though the program-hash metadata can be freely
    /// rewritten to P's hashes.
    #[test]
    fn rejects_proof_whose_chain_encodes_a_different_program() {
        // Two distinct base programs produce two distinct authenticated chains.
        let chain_p = chain_for_program([10, 11, 12, 13, 14, 15, 16, 17]);
        let chain_q = chain_for_program([99, 98, 97, 96, 95, 94, 93, 92]);
        assert_ne!(
            chain_p, chain_q,
            "different programs must yield different chains"
        );

        // The attacker holds a valid proof for Q; the verifier authenticates
        // Q's chain.
        let proven_output = verifier_output_with_chain(chain_q);

        // Claiming it is a proof for P must be rejected by the binding check.
        let err = ensure_recursion_chain_binds_program(&proven_output, &chain_p)
            .expect_err("a proof whose chain encodes a different program must be rejected");
        assert!(
            err.contains("does not match the supplied program"),
            "unexpected error message: {err}"
        );

        // And it still verifies against the program it was actually
        // generated for.
        assert!(ensure_recursion_chain_binds_program(&proven_output, &chain_q).is_ok());
    }

    /// The multi-layer chain reconstruction matches the verifier's extension
    /// rule, including the same-program no-op.
    #[test]
    fn rebuild_chain_extends_and_deduplicates() {
        let ep0 = [1u32, 2, 3, 4, 5, 6, 7, 8];
        let ep1 = [9u32, 10, 11, 12, 13, 14, 15, 16];

        let mut reference = FsvRecursionChain::begin(&ep0);
        reference.extend(&ep1);

        let rebuilt = rebuild_chain(&[ep0, ep1]).unwrap();
        assert_eq!(rebuilt.hash(), reference.hash());
        // Repeating the same layer's end-params is a no-op, mirroring the
        // in-circuit rule.
        let rebuilt_dup = rebuild_chain(&[ep0, ep1, ep1]).unwrap();
        assert_eq!(rebuilt_dup.hash(), reference.hash());
    }

    /// The statically derived exit point matches the reference behavior on a
    /// synthetic binary and rejects binaries without a unique exit sequence.
    #[test]
    fn find_binary_exit_point_locates_the_exit_loop() {
        let mut binary = vec![0x0000_0013u32; 10]; // nops
        let exit_start = binary.len();
        binary.extend_from_slice(riscv_common::EXIT_SEQUENCE);
        binary.extend_from_slice(&[0u32; 4]);

        let exit_pc = find_binary_exit_point(&binary).unwrap();
        assert_eq!(
            exit_pc,
            ((exit_start + riscv_common::EXIT_SEQUENCE.len() - 1) * 4) as u32,
            "exit PC must be the final self-loop of the exit sequence"
        );

        assert!(find_binary_exit_point(&[0u32; 32]).is_err());
    }

    /// The exit point of a real shipped program: hashed_fibonacci's `.bin`.
    #[test]
    fn find_binary_exit_point_on_real_binary() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../examples/hashed_fibonacci/app_blake2_with_compression.bin");
        if !path.exists() {
            return; // repo layout changed; the synthetic test still covers the scan
        }
        let (_, bin) = setups::read_binary(&path);
        find_binary_exit_point(&bin).expect("shipped binary must contain one exit sequence");
    }
}
