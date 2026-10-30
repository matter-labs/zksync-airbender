#![feature(allocator_api)]

//! Backend-generic recursion-pipeline driver for the CLI, built on the
//! proving stack:
//!
//! - CPU proving: `cpu_execution_prover::CpuExecutionProver`.
//! - GPU proving (behind the `gpu` feature): `gpu_execution_prover::ExecutionProver`.
//! - Both assemble with `program_prover::assemble_program_proof`.
//! - Protocol helpers (ND streams, end-params, recursion chain, fsv binaries,
//!   native verification): `full_statement_verifier::host_utils`.
//!
//! The pipeline mirrors `prover_examples::recursion`'s (and its GPU
//! twin, `run_gpu_recursive_pipeline` in `gpu/execution_prover/tests/program.rs`):
//!
//!   base (unrolled, full-unsigned ISA)
//!   → unrolled recursion layers (reduced ISA, fsv verifier binaries) while the
//!     estimated verifier cost stays at/above `unified_switch_cycles()`
//!   → bridge (the unrolled verifier proved in UNIFIED machine mode)
//!   → final (fsv_unified_recursion_layer, unified mode), repeated until the
//!     proof converges to one unified + one delegation proof

mod artifact;
mod guests;
pub use artifact::{ProofArtifact, ARTIFACT_SCHEMA_VERSION};
use guests::{fsv_input, unrolled_verifier_cost, FsvPrograms};
pub use prover::definitions::SoundnessMode;

use clap::ValueEnum;
use execution_prover::BinaryHandle;
use full_statement_verifier::host_utils::{
    bridge_blake_mode, build_unified_stream, build_unrolled_stream, compute_end_params,
    final_blake_mode, fsv_digest, load_fsv_exact, try_native_verify_unified_in_mode,
    try_native_verify_unrolled_in_mode, unified_switch_cycles, unrolled_blake_mode,
    FsvRecursionChain,
};
use full_statement_verifier::program_proof::ProgramProof;
use riscv_transpiler::vm::FlatResponsesSource;
use serde::{Deserialize, Serialize};
use setups::Setups;
use sha3::{Digest, Keccak256};
use std::alloc::Global;
use std::path::{Path, PathBuf};
use std::time::Instant;
use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProgram};

/// Serde-friendly mirror of `prover::definitions::SecurityLevel` (which does
/// not derive serde) for the persisted artifact.
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum SecurityLevel {
    Sec100,
}

impl SecurityLevel {
    pub fn to_prover(self) -> prover::definitions::SecurityLevel {
        match self {
            SecurityLevel::Sec100 => prover::definitions::SecurityLevel::Sec100,
        }
    }
}

pub const COMPILED_SECURITY_LEVEL: SecurityLevel = SecurityLevel::Sec100;

// The existing JIT encodes the cycle limit as a 32-bit timestamp: 4 * cycles + 4.
pub const MAX_EXECUTION_CYCLES: usize = (u32::MAX as usize - 4) / 4;

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

/// Guest RAM sizes the JIT supports.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, ValueEnum)]
pub enum RamSize {
    #[value(name = "32mib")]
    Mib32,
    #[value(name = "128mib")]
    Mib128,
    #[default]
    #[value(name = "1gib")]
    Gib1,
    #[value(name = "4gib")]
    Gib4,
}

impl RamSize {
    fn jit(self) -> riscv_transpiler::jit::JitRunnerRam {
        use riscv_transpiler::jit::JitRunnerRam;
        match self {
            Self::Mib32 => JitRunnerRam::Tiny,
            Self::Mib128 => JitRunnerRam::Small,
            Self::Gib1 => JitRunnerRam::Medium,
            Self::Gib4 => JitRunnerRam::Full,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ProgramProverConfig {
    pub soundness_mode: prover::definitions::SoundnessMode,
    pub target: ProofTarget,
    pub backend: ProverBackend,
    /// Cycle limit for the proved program; `None` compiles no limit check.
    pub cycles_bound: Option<u32>,
    pub ram_size: RamSize,
    /// `None` uses every core.
    pub worker_threads: Option<usize>,
    /// `None` keeps the backend's default.
    pub replay_threads: Option<usize>,
}

impl ProgramProverConfig {
    pub fn selection(&self) -> prover::definitions::ProvingSelection {
        prover::definitions::ProvingSelection {
            security_level: COMPILED_SECURITY_LEVEL.to_prover(),
            soundness_mode: self.soundness_mode,
        }
    }
}

impl Default for ProgramProverConfig {
    fn default() -> Self {
        Self {
            soundness_mode: prover::definitions::SoundnessMode::DEFAULT,
            target: ProofTarget::RecursionUnified,
            backend: default_backend_for_build(),
            cycles_bound: None,
            ram_size: RamSize::default(),
            worker_threads: None,
            replay_threads: None,
        }
    }
}

/// Where the guest program comes from: the linked ELF, or the `objcopy` dumps of a program
/// committed as-is. The program hashes recorded in the artifact are computed over the same
/// bytes in both cases, so an artifact made from one form verifies against the other.
pub use riscv_transpiler::elf::ProgramSource;

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

// ==============================================================================
// Backend abstraction
// ==============================================================================

pub use execution_prover::{ExecutionKind, MachineType};

/// One required op: prove `bin`/`text` (UNPADDED words; backends pad as they
/// need) in the given machine/kind with `nd_words` as the non-determinism
/// stream, returning the assembled `(ProgramProof, Setups)` pair.
pub trait ProveBackend {
    /// Backend precomputations run here, before any timed prove.
    fn register(
        &mut self,
        kind: ExecutionKind,
        machine: MachineType,
        bin: &[u32],
        text: &[u32],
        cycles_bound: Option<u32>,
    );

    /// Fallible selection-aware registration. Existing implementers retain their register hook.
    fn try_register(
        &mut self,
        kind: ExecutionKind,
        machine: MachineType,
        bin: &[u32],
        text: &[u32],
        cycles_bound: Option<u32>,
    ) -> Result<(), String> {
        self.register(kind, machine, bin, text, cycles_bound);
        Ok(())
    }

    fn prove(&mut self, request: ProveRequest<'_>) -> Result<(ProgramProof, Setups), String>;

    /// `Setups` of a registered binary, from its precomputations.
    fn setups(
        &mut self,
        kind: ExecutionKind,
        machine: MachineType,
        bin: &[u32],
        text: &[u32],
    ) -> Setups;
}

/// One prove request. `bin`/`text` are UNPADDED words; backends pad as needed.
pub struct ProveRequest<'a> {
    pub batch_id: u64,
    pub bin: &'a [u32],
    pub text: &'a [u32],
    pub kind: ExecutionKind,
    pub machine: MachineType,
    pub nd_words: Vec<u32>,
}

type HandleKey = (u8, u8, [u8; 32]);

fn handle_key(kind: ExecutionKind, machine: MachineType, bin: &[u32], text: &[u32]) -> HandleKey {
    let mut hasher = Keccak256::new();
    hasher.update((bin.len() as u64).to_le_bytes());
    for word in bin.iter().chain(text.iter()) {
        hasher.update(word.to_le_bytes());
    }
    (kind as u8, machine as u8, hasher.finalize().into())
}

struct PipelineBackend<B: execution_prover::backend::ExecutionBackend> {
    prover: execution_prover::ExecutionProver<B>,
    handles: std::collections::BTreeMap<HandleKey, BinaryHandle>,
}

impl<B: execution_prover::backend::ExecutionBackend> PipelineBackend<B> {
    fn configuration(
        config: &ProgramProverConfig,
    ) -> execution_prover::ExecutionProverConfiguration<B::Configuration> {
        let defaults =
            execution_prover::ExecutionProverConfiguration::<B::Configuration>::for_selection(
                config.selection(),
            );
        execution_prover::ExecutionProverConfiguration {
            max_thread_pool_threads: config.worker_threads,
            expected_concurrent_jobs: defaults.expected_concurrent_jobs,
            replay_worker_threads_count: config
                .replay_threads
                .unwrap_or(defaults.replay_worker_threads_count),
            host_allocator_backing_allocation_size: defaults.host_allocator_backing_allocation_size,
            host_allocators_per_job_count: defaults.host_allocators_per_job_count,
            min_free_host_allocators_per_job: defaults.min_free_host_allocators_per_job,
            security_level: config.selection().security_level,
            soundness_mode: config.soundness_mode,
            ram_config: config.ram_size.jit(),
            assume_canonical_mop_inputs: defaults.assume_canonical_mop_inputs,
            backend: defaults.backend,
        }
    }

    fn new(config: &ProgramProverConfig) -> Result<Self, String> {
        let prover =
            execution_prover::ExecutionProver::try_with_configuration(Self::configuration(config))
                .map_err(|error| error.to_string())?;
        assert_eq!(prover.selection(), config.selection());
        Ok(Self {
            prover,
            handles: std::collections::BTreeMap::new(),
        })
    }
}

impl<B: execution_prover::backend::ExecutionBackend> ProveBackend for PipelineBackend<B> {
    fn register(
        &mut self,
        kind: ExecutionKind,
        machine: MachineType,
        bin: &[u32],
        text: &[u32],
        cycles_bound: Option<u32>,
    ) {
        self.try_register(kind, machine, bin, text, cycles_bound)
            .unwrap_or_else(|error| panic!("{error}"));
    }

    fn try_register(
        &mut self,
        kind: ExecutionKind,
        machine: MachineType,
        bin: &[u32],
        text: &[u32],
        cycles_bound: Option<u32>,
    ) -> Result<(), String> {
        if let std::collections::btree_map::Entry::Vacant(entry) =
            self.handles.entry(handle_key(kind, machine, bin, text))
        {
            let handle = self
                .prover
                .try_add_binary(kind, machine, bin.to_vec(), text.to_vec(), cycles_bound)
                .map_err(|error| error.to_string())?;
            entry.insert(handle);
        }
        Ok(())
    }

    fn prove(&mut self, request: ProveRequest<'_>) -> Result<(ProgramProof, Setups), String> {
        let ProveRequest {
            batch_id,
            bin,
            text,
            kind,
            machine,
            nd_words,
        } = request;
        let handle = self.handles[&handle_key(kind, machine, bin, text)];
        let result = self.prover.commit_memory_and_prove(
            batch_id,
            &handle,
            FlatResponsesSource::new_with_reads(nd_words),
        );
        let artifacts = self.prover.program_artifacts(&handle);
        Ok(program_prover::assemble_program_proof(&artifacts, result))
    }

    fn setups(
        &mut self,
        kind: ExecutionKind,
        machine: MachineType,
        bin: &[u32],
        text: &[u32],
    ) -> Setups {
        let handle = self.handles[&handle_key(kind, machine, bin, text)];
        program_prover::program_setups(&self.prover.program_artifacts(&handle))
    }
}

// ==============================================================================
// Pipeline driver
// ==============================================================================

struct RecursionState {
    proof: ProgramProof,
    setups: Setups,
    chain_end_params: Vec<[u32; 8]>,
    /// Whether `proof` is a base-layer proof (drives fsv-program selection and
    /// stream/verification flavor).
    input_is_base: bool,
    timings: ProofTimingsMs,
    program_cycles: u64,
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

/// Directory holding the `fsv_*` verifier programs. Overridable via `FSV_DIR`;
/// defaults to the in-repo `tools/gkr_verifier/full_statement_verifiers` (this
/// is a dev tool — the default assumes the binary runs near its source checkout).
fn fsv_dir() -> PathBuf {
    if let Ok(dir) = std::env::var("FSV_DIR") {
        return PathBuf::from(dir);
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../tools/gkr_verifier/full_statement_verifiers")
}

/// Advance a proof at some pipeline position to `target`. `state.proof` must be
/// either a base proof or an unrolled recursion proof (never unified).
fn advance_to_target(
    backend: &mut dyn ProveBackend,
    fsv: &FsvPrograms,
    mut state: RecursionState,
    target: ProofTarget,
    batch_id: u64,
) -> Result<RecursionState, String> {
    if target == ProofTarget::Base {
        return Ok(state);
    }

    let mut chain = rebuild_chain(&state.chain_end_params)?;
    let switch_cycles = unified_switch_cycles();

    // === Unrolled recursion layers. ===
    loop {
        let program = if state.input_is_base {
            FsvProgram::UnrolledBaseLayer
        } else {
            FsvProgram::UnrolledRecursionLayer
        };
        let guest = fsv.get(program, SetupMachine::UnrolledReduced)?;
        let label = format!("batch-{batch_id}-unrolled-{}", state.chain_end_params.len());
        let cost = unrolled_verifier_cost(guest, &state.setups, &state.proof, &label)?;
        log::debug!(
            "selected verifier cost {} cycles vs switch threshold {switch_cycles}",
            cost.cycles
        );
        if cost.cycles < switch_cycles {
            break;
        }
        let nd_words = match cost.measured_input {
            Some(words) => words,
            None => fsv_input(guest, &state.setups, &state.proof, &label)?,
        };
        let start = Instant::now();
        let (mut new_proof, new_setups) = backend.prove(ProveRequest {
            batch_id,
            bin: guest.bin(),
            text: guest.text(),
            kind: ExecutionKind::Unrolled,
            machine: MachineType::Reduced,
            nd_words,
        })?;
        state.timings.unrolled_recursion_ms.push(elapsed_ms(start));
        new_proof.set_recursion_chain(&chain);

        let end_params = compute_end_params(&new_setups, new_proof.final_pc);
        chain.extend(&end_params);
        state.chain_end_params.push(end_params);
        state.proof = new_proof;
        state.setups = new_setups;
        state.input_is_base = false;
        log::info!(
            "unrolled recursion layer proved ({} cycles)",
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
    let bridge = fsv.get(bridge_program, SetupMachine::Unified)?;
    let nd_words = fsv_input(
        bridge,
        &state.setups,
        &state.proof,
        &format!("batch-{batch_id}-bridge"),
    )?;
    let start = Instant::now();
    let (mut bridge_proof, bridge_setups) = backend.prove(ProveRequest {
        batch_id,
        bin: bridge.bin(),
        text: bridge.text(),
        kind: ExecutionKind::Unified,
        machine: MachineType::Reduced,
        nd_words,
    })?;
    state.timings.unified_recursion_ms.push(elapsed_ms(start));
    bridge_proof.set_recursion_chain(&chain);
    let bridge_end_params = compute_end_params(&bridge_setups, bridge_proof.final_pc);
    chain.extend(&bridge_end_params);
    state.chain_end_params.push(bridge_end_params);
    log::info!(
        "bridge proved in unified mode ({} cycles)",
        bridge_proof.executed_cycles()
    );

    // === Final: fsv_unified_recursion_layer in unified mode, repeated until convergence. ===
    let final_mode = fsv.final_blake;
    let final_guest = fsv.get(FsvProgram::UnifiedRecursionLayer, SetupMachine::Unified)?;

    let mut proof = bridge_proof;
    let mut setups = bridge_setups;
    let mut rounds = 0usize;
    loop {
        let nd_words = fsv_input(
            final_guest,
            &setups,
            &proof,
            &format!("batch-{batch_id}-unified-{rounds}"),
        )?;
        let start = Instant::now();
        let (mut new_proof, new_setups) = backend.prove(ProveRequest {
            batch_id,
            bin: final_guest.bin(),
            text: final_guest.text(),
            kind: ExecutionKind::Unified,
            machine: MachineType::Reduced,
            nd_words,
        })?;
        state.timings.unified_recursion_ms.push(elapsed_ms(start));
        new_proof.set_recursion_chain(&chain);
        let end_params = compute_end_params(&new_setups, new_proof.final_pc);
        chain.extend(&end_params);
        // One chain entry per distinct-program layer: verification models the
        // tail as exactly one final layer.
        if state.chain_end_params.last() != Some(&end_params) {
            state.chain_end_params.push(end_params);
        }
        rounds += 1;
        log::debug!(
            "unified recursion round {rounds} proved ({} cycles)",
            new_proof.executed_cycles()
        );
        proof = new_proof;
        setups = new_setups;
        if unified_recursion_has_converged(&proof, final_mode) {
            break;
        }
    }
    log::info!(
        "unified recursion converged after {rounds} round(s) ({} cycles)",
        proof.executed_cycles()
    );

    state.proof = proof;
    state.setups = setups;
    state.input_is_base = false;
    Ok(state)
}

/// One unified + one blake delegation proof; `BlakeSpecialOpcodes` hashes with
/// inline MOPs, so its fixed point has no delegation proof.
fn unified_recursion_has_converged(proof: &ProgramProof, final_mode: BlakeMode) -> bool {
    let riscv: usize = proof.riscv_proofs.values().map(|v| v.len()).sum();
    let delegation: usize = proof.delegation_proofs.values().map(|v| v.len()).sum();
    let expected_delegations = usize::from(final_mode != BlakeMode::BlakeSpecialOpcodes);
    riscv == 1 && delegation == expected_delegations
}

// ==============================================================================
// ProgramProver — the CLI-facing driver
// ==============================================================================

enum BackendImpl {
    Cpu(PipelineBackend<cpu_execution_prover::CpuBackend>),
    #[cfg(feature = "gpu")]
    Gpu(PipelineBackend<gpu_execution_prover::GpuBackend>),
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
    fsv: FsvPrograms,
}

impl ProgramProver {
    pub fn new(source: ProgramSource, config: ProgramProverConfig) -> Result<Self, String> {
        if config.backend == ProverBackend::Gpu
            && config.soundness_mode == prover::definitions::SoundnessMode::EthproofsSoundnessCalc
        {
            return Err("UnsupportedBackendSoundnessMode: GPU EthproofsSoundnessCalc requires internal folding-PoW and OOD-PoW".to_string());
        }
        let fsv = FsvPrograms::load(config.target, config.selection())?;
        assert_eq!(fsv.selection, config.selection());
        // Resolve source errors before creating the backend's worker pools and buffers.
        load_program(&source)?;
        let backend = match config.backend {
            ProverBackend::Cpu => BackendImpl::Cpu(PipelineBackend::new(&config)?),
            ProverBackend::Gpu => {
                #[cfg(feature = "gpu")]
                {
                    BackendImpl::Gpu(PipelineBackend::new(&config)?)
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
        let mut prover = Self {
            source,
            fsv,
            config,
            backend,
        };
        prover.register_pipeline_binaries()?;
        Ok(prover)
    }

    /// Register every binary the selected target's pipeline can touch.
    fn register_pipeline_binaries(&mut self) -> Result<(), String> {
        let start = Instant::now();
        let cycles_bound = self.config.cycles_bound;
        if let Some(cycles_bound) = cycles_bound {
            assert!(
                cycles_bound as usize <= MAX_EXECUTION_CYCLES,
                "cycle bound {cycles_bound} exceeds the execution limit {MAX_EXECUTION_CYCLES}"
            );
        }
        let loaded = load_program(&self.source)?;
        let fsv = &self.fsv;
        let target = self.config.target;
        let backend = self.backend.as_dyn();
        backend.try_register(
            ExecutionKind::Unrolled,
            MachineType::FullUnsigned,
            &loaded.bin_u32,
            &loaded.text_u32,
            cycles_bound,
        )?;
        let mut count = 1;
        if target != ProofTarget::Base {
            for program in [
                FsvProgram::UnrolledBaseLayer,
                FsvProgram::UnrolledRecursionLayer,
            ] {
                let guest = fsv.get(program, SetupMachine::UnrolledReduced)?;
                backend.try_register(
                    ExecutionKind::Unrolled,
                    MachineType::Reduced,
                    guest.bin(),
                    guest.text(),
                    None,
                )?;
                count += 1;
            }
        }
        if target == ProofTarget::RecursionUnified {
            for program in [
                FsvProgram::UnrolledBaseLayer,
                FsvProgram::UnrolledRecursionLayer,
                FsvProgram::UnifiedRecursionLayer,
            ] {
                let guest = fsv.get(program, SetupMachine::Unified)?;
                backend.try_register(
                    ExecutionKind::Unified,
                    MachineType::Reduced,
                    guest.bin(),
                    guest.text(),
                    None,
                )?;
                count += 1;
            }
        }
        log::info!(
            "prepared {count} pipeline binaries in {} ms",
            elapsed_ms(start)
        );
        Ok(())
    }

    /// Verifies a proof made by this prover. The trusted end params come from the setups
    /// this prover computed for its program and the fsv programs, so nothing is recomputed;
    /// `verify_artifact` verifies without trusting this prover.
    pub fn verify(&mut self, artifact: &ProofArtifact) -> Result<[u32; 16], String> {
        artifact.validate_expected_mode(self.config.soundness_mode)?;
        if artifact.target != self.config.target {
            return Err(format!(
                "artifact target {:?} differs from this prover's target {:?}",
                artifact.target, self.config.target
            ));
        }
        let loaded = load_and_validate_program(&self.source, artifact)?;
        validate_artifact_chain(artifact)?;
        let fsv = &self.fsv;
        let backend = self.backend.as_dyn();
        let expected = expected_chain_end_params(
            artifact.target,
            artifact.chain_end_params.len(),
            fsv.unrolled_blake.tag(),
            fsv.bridge_blake.tag(),
            fsv.final_blake.tag(),
            &mut |program| {
                let (kind, machine, (bin, text)) = match program {
                    ChainProgram::User => (
                        ExecutionKind::Unrolled,
                        MachineType::FullUnsigned,
                        (loaded.bin_u32.as_slice(), loaded.text_u32.as_slice()),
                    ),
                    ChainProgram::Fsv(program, _, setup_machine) => {
                        let guest = fsv.get(program, setup_machine)?;
                        let kind = match setup_machine {
                            SetupMachine::Unified => ExecutionKind::Unified,
                            _ => ExecutionKind::Unrolled,
                        };
                        (kind, MachineType::Reduced, (guest.bin(), guest.text()))
                    }
                };
                let setups = backend.setups(kind, machine, bin, text);
                Ok(compute_end_params(&setups, find_binary_exit_point(bin)?))
            },
        )?;
        verify_against_chain(artifact, &expected, self.config.soundness_mode)
    }

    pub fn prove_words(
        &mut self,
        batch_id: u64,
        input_words: Vec<u32>,
    ) -> Result<ProofArtifact, String> {
        let loaded = load_program(&self.source)?;

        // Base layer: the user program, unrolled, full-unsigned ISA.
        let start = Instant::now();
        let (proof, setups) = self.backend.as_dyn().prove(ProveRequest {
            batch_id,
            bin: &loaded.bin_u32,
            text: &loaded.text_u32,
            kind: ExecutionKind::Unrolled,
            machine: MachineType::FullUnsigned,
            nd_words: input_words,
        })?;
        let base_ms = elapsed_ms(start);
        log::info!("base layer proved ({} cycles)", proof.executed_cycles());

        let base_end_params = compute_end_params(&setups, proof.final_pc);
        let program_cycles = proof.executed_cycles();
        let state = RecursionState {
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
            program_cycles,
        };

        let state = advance_to_target(
            self.backend.as_dyn(),
            &self.fsv,
            state,
            self.config.target,
            batch_id,
        )?;

        Ok(finalize_artifact(
            &self.fsv,
            &self.config,
            batch_id,
            &loaded,
            state,
        ))
    }

    pub fn continue_artifact(&mut self, artifact: ProofArtifact) -> Result<ProofArtifact, String> {
        artifact.validate_expected_mode(self.config.soundness_mode)?;
        validate_continuation_request(&artifact, self.config.target)?;
        // A serialized checkpoint is untrusted even when its mode label matches.
        verify_artifact_in_mode(&artifact, &self.source, self.config.soundness_mode)?;
        let loaded = load_and_validate_program(&self.source, &artifact)?;

        let batch_id = artifact.batch_id;
        // A single chain entry (just the base end-params) means no recursion
        // layer ran — the stored proof is a base-layer proof even if the
        // artifact target is RecursionUnrolled.
        let input_is_base = artifact.chain_end_params.len() <= 1;
        let state = RecursionState {
            proof: artifact.proof,
            setups: artifact.setups,
            chain_end_params: artifact.chain_end_params,
            input_is_base,
            timings: artifact.timings_ms,
            program_cycles: artifact.program_cycles,
        };

        let state = advance_to_target(
            self.backend.as_dyn(),
            &self.fsv,
            state,
            self.config.target,
            batch_id,
        )?;

        Ok(finalize_artifact(
            &self.fsv,
            &self.config,
            batch_id,
            &loaded,
            state,
        ))
    }
}

fn finalize_artifact(
    fsv: &FsvPrograms,
    config: &ProgramProverConfig,
    batch_id: u64,
    loaded: &LoadedProgram,
    mut state: RecursionState,
) -> ProofArtifact {
    state.timings.total_ms = state.timings.base_ms
        + state.timings.unrolled_recursion_ms.iter().sum::<u64>()
        + state.timings.unified_recursion_ms.iter().sum::<u64>();
    log::info!(
        "proving stages took {} ms (base {} ms, unrolled {:?} ms, unified {:?} ms)",
        state.timings.total_ms,
        state.timings.base_ms,
        state.timings.unrolled_recursion_ms,
        state.timings.unified_recursion_ms
    );

    let chain = rebuild_chain(&state.chain_end_params).expect("chain history is non-empty");
    ProofArtifact {
        schema_version: ARTIFACT_SCHEMA_VERSION,
        security_level: COMPILED_SECURITY_LEVEL,
        soundness_mode: config.soundness_mode,
        target: config.target,
        backend: config.backend,
        batch_id,
        cycles: state.proof.executed_cycles(),
        program_cycles: state.program_cycles,
        program_bin_keccak: keccak256(&loaded.bin_bytes),
        program_text_keccak: keccak256(&loaded.text_bytes),
        timings_ms: state.timings,
        proof_counts: ProofCounts::from_proof(&state.proof),
        chain_end_params: state.chain_end_params,
        chain_hash: chain.hash(),
        chain_preimage: chain.preimage(),
        // The pipeline resolves the blake modes from the environment (see
        // host_utils); record the tags so verification reconstructs the same
        // pipeline regardless of the verify-time environment.
        blake_unrolled: fsv.unrolled_blake.tag().to_string(),
        blake_bridge: fsv.bridge_blake.tag().to_string(),
        blake_final: fsv.final_blake.tag().to_string(),
        proof: state.proof,
        setups: state.setups,
    }
}

// ==============================================================================
// Verification
// ==============================================================================

/// Trusted unified chain hashes for zero, one, or at least two unrolled recursion layers.
pub fn unified_verification_chain_hashes(source: &ProgramSource) -> Result<[[u32; 8]; 3], String> {
    unified_verification_chain_hashes_in_mode(source, SoundnessMode::PessimisticConjecture)
}

/// Trusted unified chain hashes under a caller-selected standard soundness mode.
pub fn unified_verification_chain_hashes_in_mode(
    source: &ProgramSource,
    mode: SoundnessMode,
) -> Result<[[u32; 8]; 3], String> {
    let loaded = load_program(source)?;
    let worker = worker::Worker::new();
    let unrolled_blake = unrolled_blake_mode();
    let bridge_blake = bridge_blake_mode();
    let final_blake = final_blake_mode();
    let mut hashes = [[0; 8]; 3];
    for (i, hash) in hashes.iter_mut().enumerate() {
        let expected = expected_chain_end_params(
            ProofTarget::RecursionUnified,
            i + 3,
            unrolled_blake.tag(),
            bridge_blake.tag(),
            final_blake.tag(),
            &mut recomputed_end_params(&loaded, &worker, selection_in_mode(mode)),
        )?;
        *hash = rebuild_chain(&expected)?.hash();
    }
    Ok(hashes)
}

pub fn verify_artifact(
    artifact: &ProofArtifact,
    source: &ProgramSource,
) -> Result<[u32; 16], String> {
    verify_artifact_in_mode(artifact, source, SoundnessMode::PessimisticConjecture)
}

/// Verify with a caller-supplied acceptance mode, before loading the source or setups.
pub fn verify_artifact_in_mode(
    artifact: &ProofArtifact,
    source: &ProgramSource,
    expected_mode: SoundnessMode,
) -> Result<[u32; 16], String> {
    artifact.validate_expected_mode(expected_mode)?;
    let loaded = load_and_validate_program(source, artifact)?;
    validate_artifact_chain(artifact)?;

    // Trusted per-layer end-params, recomputed from the supplied program and
    // the checked-in fsv binaries (see the program-binding module comment
    // below). Cross-check the artifact's claimed history entry by entry
    // (stronger than internal consistency), then bind the verifier's
    // authenticated output chain to the trusted chain.
    let worker = worker::Worker::new();
    let expected = expected_chain_end_params(
        artifact.target,
        artifact.chain_end_params.len(),
        &artifact.blake_unrolled,
        &artifact.blake_bridge,
        &artifact.blake_final,
        &mut recomputed_end_params(&loaded, &worker, selection_in_mode(expected_mode)),
    )?;
    verify_against_chain(artifact, &expected, expected_mode)
}

fn verify_against_chain(
    artifact: &ProofArtifact,
    expected: &[[u32; 8]],
    expected_mode: SoundnessMode,
) -> Result<[u32; 16], String> {
    if expected != artifact.chain_end_params {
        return Err(
            "artifact chain_end_params do not match the trusted per-layer end-params".to_string(),
        );
    }
    let expected_chain = rebuild_chain(expected)?;

    // The claim shape decides the statement flavor: a single layer is a
    // base-layer statement (no recursion chain in the stream).
    let is_base = expected.len() == 1;
    let output = match artifact.target {
        ProofTarget::Base | ProofTarget::RecursionUnrolled => try_native_verify_unrolled_in_mode(
            build_unrolled_stream(
                &artifact.setups,
                &artifact.proof,
                verifier_common::BLAKE_MODE,
            ),
            is_base,
            expected_mode,
        ),
        ProofTarget::RecursionUnified => try_native_verify_unified_in_mode(
            build_unified_stream(
                &artifact.setups,
                &artifact.proof,
                verifier_common::BLAKE_MODE,
            ),
            is_base,
            expected_mode,
        ),
    }
    .map_err(|error| format!("NativeVerificationFailed: {error}"))?;
    ensure_recursion_chain_binds_program(&output, &expected_chain.hash())?;
    Ok(output)
}

// ==============================================================================
// Program binding
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
// CLAIM of the pipeline shape: they select among trusted binaries and trusted
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
    selection: prover::definitions::ProvingSelection,
    worker: &worker::Worker,
) -> Result<Setups, String> {
    use riscv_transpiler::cycle::IMStandardIsaConfigUnsignedMulDivOnly as FullUnsignedConfig;
    use riscv_transpiler::cycle::ReducedMachineWithDelegation as ReducedConfig;
    use setups::program_setups::{
        compute_unified_program_setups_in_mode, compute_unrolled_program_setups_in_mode,
    };

    let mut padded_bin = bin.to_vec();
    let mut padded_text = text.to_vec();
    setups::pad_bytecode_for_proving(&mut padded_bin);
    setups::pad_bytecode_for_proving(&mut padded_text);

    let use_caches = true;
    let security_level = selection.security_level;
    match machine {
        SetupMachine::UnrolledFullUnsigned => {
            compute_unrolled_program_setups_in_mode::<FullUnsignedConfig, Global>(
                &padded_bin,
                &padded_text,
                use_caches,
                security_level,
                selection.soundness_mode,
                worker,
            )
        }
        SetupMachine::UnrolledReduced => {
            compute_unrolled_program_setups_in_mode::<ReducedConfig, Global>(
                &padded_bin,
                &padded_text,
                use_caches,
                security_level,
                selection.soundness_mode,
                worker,
            )
        }
        SetupMachine::Unified => compute_unified_program_setups_in_mode::<Global>(
            &padded_bin,
            &padded_text,
            use_caches,
            security_level,
            selection.soundness_mode,
            worker,
        ),
    }
    .map_err(|error| error.to_string())
}

/// Keep selection/profile identity even when current base caps coincide across modes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct TrustedEndParamsKey {
    machine: SetupMachine,
    selection: prover::definitions::ProvingSelection,
    profile: prover::definitions::ProverConfigProfile,
    program_hash: [u8; 32],
}

/// Trusted standard end params keyed by machine, selection, profile and exact binary/text identity.
fn trusted_end_params_cache(
) -> &'static std::sync::Mutex<std::collections::HashMap<TrustedEndParamsKey, [u32; 8]>> {
    static CACHE: std::sync::OnceLock<
        std::sync::Mutex<std::collections::HashMap<TrustedEndParamsKey, [u32; 8]>>,
    > = std::sync::OnceLock::new();
    CACHE.get_or_init(Default::default)
}

fn trusted_end_params_key(
    machine: SetupMachine,
    bin: &[u32],
    text: &[u32],
    selection: prover::definitions::ProvingSelection,
    profile: prover::definitions::ProverConfigProfile,
) -> TrustedEndParamsKey {
    TrustedEndParamsKey {
        machine,
        selection,
        profile,
        program_hash: fsv_digest(bin, text).0,
    }
}

fn selection_in_mode(soundness_mode: SoundnessMode) -> prover::definitions::ProvingSelection {
    prover::definitions::ProvingSelection {
        security_level: COMPILED_SECURITY_LEVEL.to_prover(),
        soundness_mode,
    }
}

/// Mode-explicit standard setup reconstruction. Special-profile setups need their own producer.
fn trusted_end_params_in_mode(
    bin: &[u32],
    text: &[u32],
    machine: SetupMachine,
    selection: prover::definitions::ProvingSelection,
    worker: &worker::Worker,
) -> Result<[u32; 8], String> {
    let key = trusted_end_params_key(
        machine,
        bin,
        text,
        selection,
        prover::definitions::ProverConfigProfile::Standard,
    );
    let cache = trusted_end_params_cache();
    if let Some(end_params) = cache.lock().unwrap().get(&key) {
        return Ok(*end_params);
    }

    let start = Instant::now();
    let setups = recompute_program_setups(bin, text, machine, selection, worker)?;
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

enum ChainProgram {
    User,
    Fsv(FsvProgram, BlakeMode, SetupMachine),
}

/// End params recomputed from the supplied program and the checked-in fsv binaries.
fn recomputed_end_params<'a>(
    loaded: &'a LoadedProgram,
    worker: &'a worker::Worker,
    selection: prover::definitions::ProvingSelection,
) -> impl FnMut(ChainProgram) -> Result<[u32; 8], String> + 'a {
    let fsv_dir = fsv_dir();
    move |program| match program {
        ChainProgram::User => trusted_end_params_in_mode(
            &loaded.bin_u32,
            &loaded.text_u32,
            SetupMachine::UnrolledFullUnsigned,
            selection,
            worker,
        ),
        ChainProgram::Fsv(program, blake, setup_machine) => {
            let descriptor = FsvDescriptor::new(
                selection.security_level,
                selection.soundness_mode,
                program,
                blake,
            );
            let guest = load_fsv_exact(&fsv_dir, &descriptor).map_err(|error| error.to_string())?;
            trusted_end_params_in_mode(guest.bin(), guest.text(), setup_machine, selection, worker)
        }
    }
}

/// Reconstruct the pipeline's per-layer `end_params` from trusted inputs only, which
/// `end_params` supplies per chain program. The artifact contributes only the CLAIM shape:
/// target, number of chain entries, blake tags.
fn expected_chain_end_params(
    target: ProofTarget,
    n: usize,
    blake_unrolled: &str,
    blake_bridge: &str,
    blake_final: &str,
    end_params: &mut dyn FnMut(ChainProgram) -> Result<[u32; 8], String>,
) -> Result<Vec<[u32; 8]>, String> {
    let unrolled_layers = match target {
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
    expected.push(end_params(ChainProgram::User)?);

    if target == ProofTarget::Base {
        return Ok(expected);
    }

    let unrolled_blake = parse_blake_tag(blake_unrolled, FsvProgram::UnrolledBaseLayer)?;

    for layer in 0..unrolled_layers {
        let program = if layer == 0 {
            FsvProgram::UnrolledBaseLayer
        } else {
            FsvProgram::UnrolledRecursionLayer
        };
        expected.push(end_params(ChainProgram::Fsv(
            program,
            unrolled_blake,
            SetupMachine::UnrolledReduced,
        ))?);
    }

    if target == ProofTarget::RecursionUnrolled {
        return Ok(expected);
    }

    // Bridge: the unrolled verifier binary (selected by whether any unrolled layer ran)
    // proved on the UNIFIED machine — its end_params use the unified setups.
    let bridge_program = if unrolled_layers == 0 {
        FsvProgram::UnrolledBaseLayer
    } else {
        FsvProgram::UnrolledRecursionLayer
    };
    let bridge_blake = parse_blake_tag(blake_bridge, bridge_program)?;
    expected.push(end_params(ChainProgram::Fsv(
        bridge_program,
        bridge_blake,
        SetupMachine::Unified,
    ))?);

    // Final: fsv_unified_recursion_layer on the unified machine.
    let final_blake = parse_blake_tag(blake_final, FsvProgram::UnifiedRecursionLayer)?;
    expected.push(end_params(ChainProgram::Fsv(
        FsvProgram::UnifiedRecursionLayer,
        final_blake,
        SetupMachine::Unified,
    ))?);

    Ok(expected)
}

/// Bind a verified proof to the program supplied by the caller.
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
        return Err("artifact chain_hash/chain_preimage do not match chain_end_params".to_string());
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
    let image = source
        .read()
        .map_err(|err| format!("failed to load program {source}: {err}"))?;
    // The objcopy-equivalent prefix (no ROM padding), so program hashes are the same whether the
    // program came from its ELF or from the `.bin`/`.text` dumps.
    let bin_u32 = image
        .objcopy_binary_words()
        .expect("legacy mode produces the flattened image")
        .to_vec();
    Ok(LoadedProgram {
        bin_bytes: image.objcopy_binary().unwrap(),
        text_bytes: image.text_bytes(),
        bin_u32,
        text_u32: image.text,
    })
}

/// Flat ROM image and text section words of a program, unpadded.
pub fn load_program_words(source: &ProgramSource) -> Result<(Vec<u32>, Vec<u32>), String> {
    let loaded = load_program(source)?;
    Ok((loaded.bin_u32, loaded.text_u32))
}

fn load_and_validate_program(
    source: &ProgramSource,
    artifact: &ProofArtifact,
) -> Result<LoadedProgram, String> {
    artifact.validate_schema()?;
    if artifact.security_level != COMPILED_SECURITY_LEVEL {
        return Err(format!(
            "proof security level ({:?}) does not match binary security level ({:?})",
            artifact.security_level, COMPILED_SECURITY_LEVEL
        ));
    }

    let loaded = load_program(source)?;
    if keccak256(&loaded.bin_bytes) != artifact.program_bin_keccak {
        return Err(format!(
            "proof artifact program_bin_keccak does not match the flat image of {source}"
        ));
    }
    if keccak256(&loaded.text_bytes) != artifact.program_text_keccak {
        return Err(format!(
            "proof artifact program_text_keccak does not match the text section of {source}"
        ));
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
    if !hex_string.len().is_multiple_of(8) {
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

fn elapsed_ms(start: Instant) -> u64 {
    start.elapsed().as_millis() as u64
}

fn keccak256(data: &[u8]) -> [u8; 32] {
    let mut hasher = Keccak256::new();
    hasher.update(data);
    hasher.finalize().into()
}

/// Recursion-binding tests, adapted to `FsvRecursionChain` (no proving
/// required).
#[cfg(test)]
mod recursion_binding_tests {
    use super::*;

    #[test]
    fn cpu_unified_verification_chain_binds_program() {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../examples/hashed_fibonacci");
        let [first, second] = ["app_plain.bin", "app_blake2_with_compression.bin"].map(|name| {
            unified_verification_chain_hashes(&ProgramSource::legacy_binaries_from_bin(
                dir.join(name),
            ))
            .unwrap()
        });
        for hash in first {
            assert!(
                !second.contains(&hash),
                "different guests must have different hashes"
            );
        }
    }

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
            .join("../examples/hashed_fibonacci/app_blake2_with_compression.bin");
        if !path.exists() {
            return; // repo layout changed; the synthetic test still covers the scan
        }
        let (bin, _) = ProgramSource::legacy_binaries_from_bin(&path).load_unpadded();
        find_binary_exit_point(&bin).expect("shipped binary must contain one exit sequence");
    }
}

#[cfg(test)]
mod program_source_tests {
    use super::*;

    /// Both program forms feed the same bytes to the backends and to the artifact hashes: the
    /// dumps verbatim, the ELF through its objcopy-equivalent image and text section.
    #[test]
    fn program_sources_load_consistently() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");

        let bin = root.join("examples/hashed_fibonacci/app_blake2_with_compression.bin");
        let dumps = load_program(&ProgramSource::legacy_binaries_from_bin(&bin)).unwrap();
        assert_eq!(dumps.bin_bytes, std::fs::read(&bin).unwrap());
        assert_eq!(
            dumps.text_bytes,
            std::fs::read(bin.with_extension("text")).unwrap()
        );
        assert_eq!(dumps.bin_u32.len() * 4, dumps.bin_bytes.len());
        assert_eq!(dumps.text_u32.len() * 4, dumps.text_bytes.len());

        let elf = root.join(
            "tools/gkr_verifier/circuit_verifiers/pessimistic_conjecture/add_sub_lui_auipc_mop.elf",
        );
        let loaded = load_program(&ProgramSource::elf(&elf)).unwrap();
        let (bin_u32, text_u32) = ProgramSource::elf(&elf).load_unpadded();
        assert_eq!(loaded.bin_u32, bin_u32);
        assert_eq!(loaded.text_u32, text_u32);
        assert!(!text_u32.is_empty());
        assert!(loaded.bin_u32.starts_with(&loaded.text_u32));
        assert_eq!(loaded.bin_u32.len() * 4, loaded.bin_bytes.len());
        assert_eq!(loaded.text_u32.len() * 4, loaded.text_bytes.len());
        assert_ne!(keccak256(&loaded.bin_bytes), keccak256(&loaded.text_bytes));
    }
}

#[cfg(test)]
mod soundness_selection_tests {
    use super::*;
    use prover::definitions::SoundnessMode;

    #[test]
    fn pipeline_backend_preserves_selection() {
        for &soundness_mode in SoundnessMode::ALL {
            let config = ProgramProverConfig {
                soundness_mode,
                ..ProgramProverConfig::default()
            };
            let execution =
                PipelineBackend::<cpu_execution_prover::CpuBackend>::configuration(&config);
            assert_eq!(execution.selection(), config.selection());
        }
        assert_eq!(
            ProgramProverConfig::default().soundness_mode,
            SoundnessMode::PessimisticConjecture
        );
    }

    #[test]
    fn cpu_ethproofs_source_error_precedes_backend_construction() {
        let config = ProgramProverConfig {
            target: ProofTarget::Base,
            backend: ProverBackend::Cpu,
            soundness_mode: SoundnessMode::EthproofsSoundnessCalc,
            ..ProgramProverConfig::default()
        };
        let source = ProgramSource::legacy_binaries_from_bin(std::path::Path::new(
            "/does-not-exist/task-s-program.bin",
        ));
        let error = match ProgramProver::new(source, config) {
            Err(error) => error,
            Ok(_) => panic!("CPU ethproofs pipeline unexpectedly initialized"),
        };
        assert!(error.starts_with("failed to load program"), "{error}");
    }

    #[test]
    fn gpu_ethproofs_rejection_precedes_source_loading() {
        let config = ProgramProverConfig {
            backend: ProverBackend::Gpu,
            soundness_mode: SoundnessMode::EthproofsSoundnessCalc,
            ..ProgramProverConfig::default()
        };
        let source = ProgramSource::legacy_binaries_from_bin(std::path::Path::new(
            "/does-not-exist/task-s-program.bin",
        ));
        let error = match ProgramProver::new(source, config) {
            Err(error) => error,
            Ok(_) => panic!("GPU ethproofs unexpectedly initialized"),
        };
        assert!(error.contains("UnsupportedBackendSoundnessMode"));
        assert!(error.contains("internal folding-PoW"));
        assert!(error.contains("OOD-PoW"));
    }
}

#[cfg(test)]
mod trusted_selection_tests {
    use super::*;
    use prover::definitions::{ProverConfigProfile, ProvingSelection, SoundnessMode};

    #[test]
    fn trusted_end_params_cache_isolates_mode_and_profile() {
        let mut cache = trusted_end_params_cache().lock().unwrap();
        let mut keys = Vec::new();
        for &soundness_mode in SoundnessMode::ALL {
            for profile in [
                ProverConfigProfile::Standard,
                ProverConfigProfile::L1Feeder,
                ProverConfigProfile::EvmProductionPacked,
            ] {
                let key = trusted_end_params_key(
                    SetupMachine::Unified,
                    &[0x5320_0001, 0x5320_0002],
                    &[0x5320_0003],
                    ProvingSelection {
                        soundness_mode,
                        ..ProvingSelection::default()
                    },
                    profile,
                );
                assert!(!keys.contains(&key));
                let value = [keys.len() as u32; 8];
                assert!(cache.insert(key, value).is_none());
                keys.push(key);
            }
        }
        for (i, key) in keys.iter().enumerate() {
            assert_eq!(cache.remove(key), Some([i as u32; 8]));
        }
    }

    #[test]
    fn trusted_end_params_key_preserves_binary_text_boundary() {
        let selection = ProvingSelection::default();
        let a = trusted_end_params_key(
            SetupMachine::Unified,
            &[1, 2],
            &[3],
            selection,
            ProverConfigProfile::Standard,
        );
        let b = trusted_end_params_key(
            SetupMachine::Unified,
            &[1],
            &[2, 3],
            selection,
            ProverConfigProfile::Standard,
        );
        assert_ne!(a, b);
        assert_eq!(a.selection.security_level, selection.security_level);
    }
}
