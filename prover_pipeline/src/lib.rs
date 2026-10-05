#![feature(allocator_api)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

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

use clap::ValueEnum;
use execution_prover::{BinaryHandle, ProofProfile};
use full_statement_verifier::host_utils::{
    bridge_blake_mode, build_unified_stream, build_unrolled_stream, compute_end_params,
    final_blake_mode, load_fsv_program, native_verify_unified, native_verify_unified_l1_feeder,
    native_verify_unrolled, unified_switch_cycles, unrolled_blake_mode, FsvRecursionChain,
};
use full_statement_verifier::program_proof::ProgramProof;
use riscv_transpiler::vm::FlatResponsesSource;
use serde::{Deserialize, Serialize};
use setups::Setups;
use sha3::{Digest, Keccak256};
use std::alloc::Global;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::time::Instant;
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

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

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum ProofTarget {
    Base,
    RecursionUnrolled,
    RecursionUnified,
    #[value(name = "l1-feeder")]
    L1Feeder,
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

impl Default for ProgramProverConfig {
    fn default() -> Self {
        Self {
            target: ProofTarget::RecursionUnified,
            backend: default_backend_for_build(),
            cycles_bound: None,
            ram_size: RamSize::default(),
            worker_threads: None,
            replay_threads: None,
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
    #[serde(default)]
    pub l1_feeder_ms: Vec<u64>,
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

/// Proof artifact, schema v4. `proof` + `setups` are enough to
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
    /// `executed_cycles()` of the base layer: the program's own cycle count.
    pub program_cycles: u64,
    pub program_bin_keccak: [u8; 32],
    pub program_text_keccak: [u8; 32],
    pub timings_ms: ProofTimingsMs,
    pub proof_counts: ProofCounts,
    /// Layer end-params history: `[base, unrolled_1, .., bridge, final]`.
    pub chain_end_params: Vec<[u32; 8]>,
    /// Recursion-chain state AFTER this artifact's layer.
    pub chain_hash: [u32; 8],
    pub chain_preimage: [u32; 16],
    /// Blake-mode tags of the fsv verifier binaries the pipeline used
    /// (`BlakeMode::tag()` values). Untrusted CLAIM data: at verification
    /// time they only select among the checked-in trusted fsv binaries, so a
    /// lie makes the chain-binding comparison fail.
    #[serde(default = "default_blake_tag")]
    pub blake_unrolled: String,
    #[serde(default = "default_blake_tag")]
    pub blake_bridge: String,
    #[serde(default = "default_blake_tag")]
    pub blake_final: String,
    /// Number of F2 proofs produced. Only zero versus nonzero is bound by the chain.
    #[serde(default)]
    pub l1_feeder_rounds: Option<u32>,
    /// Measured locally; consumers must remeasure before using this as a capacity bound.
    #[serde(default)]
    pub l1_feeder_verifier_cycles: Option<u64>,
    pub proof: ProgramProof,
    pub setups: Setups,
}

pub const ARTIFACT_SCHEMA_VERSION: u32 = 4;

fn default_blake_tag() -> String {
    BlakeMode::Compression.tag().to_string()
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
        profiles: &[ProofProfile],
    );

    fn prove(&mut self, request: ProveRequest<'_>) -> Result<(ProgramProof, Setups), String>;

    /// `Setups` of a binary registered for `profile`, from its precomputations; `None`
    /// when it is not registered for `profile`.
    fn setups(
        &mut self,
        kind: ExecutionKind,
        machine: MachineType,
        bin: &[u32],
        text: &[u32],
        profile: ProofProfile,
    ) -> Option<Setups>;
}

/// One prove request. `bin`/`text` are UNPADDED words; backends pad as needed.
pub struct ProveRequest<'a> {
    pub batch_id: u64,
    pub bin: &'a [u32],
    pub text: &'a [u32],
    pub kind: ExecutionKind,
    pub machine: MachineType,
    pub nd_words: Vec<u32>,
    pub profile: ProofProfile,
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

struct RegisteredBinary<H> {
    handle: H,
    profiles: BTreeSet<ProofProfile>,
}

fn register_binary<H>(
    handles: &mut BTreeMap<HandleKey, RegisteredBinary<H>>,
    key: HandleKey,
    profiles: &[ProofProfile],
    prepare: impl FnOnce() -> H,
) {
    let profiles = profiles.iter().copied().collect();
    match handles.entry(key) {
        std::collections::btree_map::Entry::Occupied(entry) => {
            assert_eq!(
                entry.get().profiles,
                profiles,
                "pipeline binary was registered for a different profile set"
            );
        }
        std::collections::btree_map::Entry::Vacant(entry) => {
            entry.insert(RegisteredBinary {
                handle: prepare(),
                profiles,
            });
        }
    }
}

struct PipelineBackend<B: execution_prover::backend::ExecutionBackend> {
    prover: execution_prover::ExecutionProver<B>,
    handles: BTreeMap<HandleKey, RegisteredBinary<BinaryHandle>>,
}

impl<B: execution_prover::backend::ExecutionBackend> PipelineBackend<B> {
    fn new(config: &ProgramProverConfig) -> Self {
        let defaults =
            execution_prover::ExecutionProverConfiguration::<B::Configuration>::default();
        let configuration = execution_prover::ExecutionProverConfiguration {
            max_thread_pool_threads: config.worker_threads,
            replay_worker_threads_count: config
                .replay_threads
                .unwrap_or(defaults.replay_worker_threads_count),
            security_level: COMPILED_SECURITY_LEVEL.to_prover(),
            ram_config: config.ram_size.jit(),
            ..defaults
        };
        Self {
            prover: execution_prover::ExecutionProver::with_configuration(configuration),
            handles: BTreeMap::new(),
        }
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
        profiles: &[ProofProfile],
    ) {
        register_binary(
            &mut self.handles,
            handle_key(kind, machine, bin, text),
            profiles,
            || {
                self.prover.add_binary(
                    kind,
                    machine,
                    bin.to_vec(),
                    text.to_vec(),
                    cycles_bound,
                    profiles,
                )
            },
        );
    }

    fn prove(&mut self, request: ProveRequest<'_>) -> Result<(ProgramProof, Setups), String> {
        let ProveRequest {
            batch_id,
            bin,
            text,
            kind,
            machine,
            nd_words,
            profile,
        } = request;
        let handle = self.handles[&handle_key(kind, machine, bin, text)].handle;
        let result = self.prover.commit_memory_and_prove(
            batch_id,
            &handle,
            FlatResponsesSource::new_with_reads(nd_words),
            match profile {
                ProofProfile::Standard => {
                    execution_prover::CommitmentMode::SeparateMemoryAndWitness
                }
                ProofProfile::L1Feeder => execution_prover::CommitmentMode::MergedMemoryAndWitness,
                ProofProfile::L1Wrap => {
                    panic!("ProofProfile::L1Wrap is proven by prove_l1_wrap, not commit_memory_and_prove")
                }
            },
            profile,
        );
        let artifacts = self.prover.program_artifacts(&handle, profile);
        Ok(program_prover::assemble_program_proof(&artifacts, result))
    }

    fn setups(
        &mut self,
        kind: ExecutionKind,
        machine: MachineType,
        bin: &[u32],
        text: &[u32],
        profile: ProofProfile,
    ) -> Option<Setups> {
        let registered = self.handles.get(&handle_key(kind, machine, bin, text))?;
        if !registered.profiles.contains(&profile) {
            return None;
        }
        Some(program_prover::program_setups(
            &self.prover.program_artifacts(&registered.handle, profile),
        ))
    }
}

// ==============================================================================
// Pipeline driver
// ==============================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PipelineBlakeModes {
    unrolled: BlakeMode,
    bridge: BlakeMode,
    final_layer: BlakeMode,
}

impl PipelineBlakeModes {
    fn from_env() -> Self {
        Self {
            unrolled: unrolled_blake_mode(),
            bridge: bridge_blake_mode(),
            final_layer: final_blake_mode(),
        }
    }

    fn continuing(
        artifact: &ProofArtifact,
        current: impl FnOnce() -> Self,
    ) -> Result<Self, String> {
        if artifact.target >= ProofTarget::RecursionUnified {
            return Ok(Self {
                unrolled: parse_blake_tag(&artifact.blake_unrolled, FsvProgram::UnrolledBaseLayer)?,
                bridge: parse_blake_tag(&artifact.blake_bridge, FsvProgram::UnrolledBaseLayer)?,
                final_layer: parse_blake_tag(
                    &artifact.blake_final,
                    FsvProgram::UnifiedRecursionLayer,
                )?,
            });
        }
        let mut current = current();
        if artifact.target >= ProofTarget::RecursionUnrolled && artifact.chain_end_params.len() > 1
        {
            current.unrolled =
                parse_blake_tag(&artifact.blake_unrolled, FsvProgram::UnrolledBaseLayer)?;
        }
        Ok(current)
    }
}

struct RecursionState {
    stage: ProofTarget,
    l1_feeder_rounds: Option<u32>,
    l1_feeder_verifier_cycles: Option<u64>,
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

/// Directory holding the `fsv_*` verifier binaries. Overridable via `FSV_DIR`;
/// defaults to the in-repo `tools/gkr_verifier` (this is a dev tool — the
/// default assumes the binary runs near its source checkout).
fn fsv_dir() -> PathBuf {
    if let Ok(dir) = std::env::var("FSV_DIR") {
        return PathBuf::from(dir);
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../tools/gkr_verifier")
}

const MAX_L1_FEEDER_ROUNDS: u32 = 4;
const L1_FEEDER_PROGRAMS: [FsvProgram; 2] = [
    FsvProgram::UnifiedRecursionLayer,
    FsvProgram::UnifiedRecursionLayerL1Feeder,
];

fn advance_stages<S>(
    mut state: S,
    current: ProofTarget,
    target: ProofTarget,
    mut run: impl FnMut(S, ProofTarget) -> Result<S, String>,
) -> Result<S, String> {
    if current < ProofTarget::RecursionUnified {
        state = run(state, target.min(ProofTarget::RecursionUnified))?;
    }
    if target == ProofTarget::L1Feeder {
        state = run(state, ProofTarget::L1Feeder)?;
    }
    Ok(state)
}

fn advance_to_target(
    backend: &mut dyn ProveBackend,
    fsv: &FsvPrograms,
    state: RecursionState,
    target: ProofTarget,
    batch_id: u64,
) -> Result<RecursionState, String> {
    let current = state.stage;
    advance_stages(state, current, target, |state, next| {
        if next == ProofTarget::L1Feeder {
            advance_feeder_stages(backend, fsv, state, batch_id)
        } else {
            advance_standard_stages(backend, fsv, state, next, batch_id)
        }
    })
}

#[derive(Debug, PartialEq, Eq)]
enum FeederStep {
    Done,
    ProveAnother,
    Err(String),
}

fn feeder_step(measured: &[u64], chunks: usize, delegations: usize) -> FeederStep {
    let Some(&cycles) = measured.last() else {
        return FeederStep::Err("feeder stopping rule requires a measurement".into());
    };
    let rounds = measured.len() - 1;
    if rounds > MAX_L1_FEEDER_ROUNDS as usize {
        return FeederStep::Err("feeder recursion exceeded the round limit".into());
    }
    if chunks == 1 && delegations == 0 && cycles <= L1_WRAP_CYCLES_BOUND as u64 {
        return FeederStep::Done;
    }
    if rounds >= 2 && cycles >= measured[measured.len() - 2] {
        return FeederStep::Err(format!(
            "feeder recursion does not contract: {} -> {cycles} verifier cycles",
            measured[measured.len() - 2]
        ));
    }
    if rounds == MAX_L1_FEEDER_ROUNDS as usize {
        return FeederStep::Err(format!(
            "feeder recursion did not fit after {rounds} F2 rounds"
        ));
    }
    FeederStep::ProveAnother
}

fn advance_feeder_stages(
    backend: &mut dyn ProveBackend,
    fsv: &FsvPrograms,
    mut state: RecursionState,
    batch_id: u64,
) -> Result<RecursionState, String> {
    let (first_bin, first_text) = &fsv.feeder_first;
    let (feeder_bin, feeder_text) = &fsv.feeder;
    let mut chain = rebuild_chain(&state.chain_end_params)?;
    let mut measured = Vec::new();
    loop {
        let (bin, text) = if measured.is_empty() {
            (first_bin, first_text)
        } else {
            (feeder_bin, feeder_text)
        };
        let start = Instant::now();
        let (mut proof, setups) = backend.prove(ProveRequest {
            batch_id,
            bin,
            text,
            kind: ExecutionKind::Unified,
            machine: MachineType::Reduced,
            nd_words: build_unified_stream(&state.setups, &state.proof),
            profile: ProofProfile::L1Feeder,
        })?;
        state.timings.l1_feeder_ms.push(elapsed_ms(start));
        proof.set_recursion_chain(&chain);
        let end_params = compute_end_params(&setups, proof.final_pc);
        chain.extend(&end_params);
        if state.chain_end_params.last() != Some(&end_params) {
            state.chain_end_params.push(end_params);
        }
        state.proof = proof;
        state.setups = setups;
        let cycles = measure_fsv_run(
            feeder_bin,
            feeder_text,
            build_unified_stream(&state.setups, &state.proof),
            1 << 27,
        )?;
        measured.push(cycles);
        let counts = ProofCounts::from_proof(&state.proof);
        log::info!(
            "feeder round {}: {} chunks, {} delegations, {cycles} verifier cycles",
            measured.len() - 1,
            counts.riscv_proof_count,
            counts.delegation_proof_count
        );
        match feeder_step(
            &measured,
            counts.riscv_proof_count,
            counts.delegation_proof_count,
        ) {
            FeederStep::Done => {
                state.stage = ProofTarget::L1Feeder;
                state.input_is_base = false;
                state.l1_feeder_rounds = Some((measured.len() - 1) as u32);
                state.l1_feeder_verifier_cycles = Some(cycles);
                return Ok(state);
            }
            FeederStep::ProveAnother => {}
            FeederStep::Err(error) => return Err(error),
        }
    }
}

struct BinaryRegistration {
    kind: ExecutionKind,
    machine: MachineType,
    bin: Vec<u32>,
    text: Vec<u32>,
    cycles_bound: Option<u32>,
    profiles: BTreeSet<ProofProfile>,
}

fn pipeline_registrations(
    loaded: &LoadedProgram,
    start: Option<ProofTarget>,
    target: ProofTarget,
    cycles_bound: Option<u32>,
    fsv: &FsvPrograms,
) -> BTreeMap<HandleKey, BinaryRegistration> {
    let mut registrations = BTreeMap::<HandleKey, BinaryRegistration>::new();
    let mut add = |kind, machine, (bin, text): &ProgramWords, cycles_bound, profile| {
        registrations
            .entry(handle_key(kind, machine, bin, text))
            .or_insert_with(|| BinaryRegistration {
                kind,
                machine,
                bin: bin.clone(),
                text: text.clone(),
                cycles_bound,
                profiles: BTreeSet::new(),
            })
            .profiles
            .insert(profile);
    };
    if start.is_none() {
        add(
            ExecutionKind::Unrolled,
            MachineType::FullUnsigned,
            &(loaded.bin_u32.clone(), loaded.text_u32.clone()),
            cycles_bound,
            ProofProfile::Standard,
        );
    }
    let start = start.unwrap_or(ProofTarget::Base);
    let mut programs = Vec::new();
    if start < ProofTarget::RecursionUnified && target > ProofTarget::Base {
        programs.extend([
            (
                &fsv.unrolled_base,
                ExecutionKind::Unrolled,
                ProofProfile::Standard,
            ),
            (
                &fsv.unrolled_recursion,
                ExecutionKind::Unrolled,
                ProofProfile::Standard,
            ),
        ]);
    }
    if start < ProofTarget::RecursionUnified && target >= ProofTarget::RecursionUnified {
        programs.extend([
            (
                &fsv.bridge_base,
                ExecutionKind::Unified,
                ProofProfile::Standard,
            ),
            (
                &fsv.bridge_recursion,
                ExecutionKind::Unified,
                ProofProfile::Standard,
            ),
            (&fsv.unified, ExecutionKind::Unified, ProofProfile::Standard),
        ]);
    }
    if start < ProofTarget::L1Feeder && target == ProofTarget::L1Feeder {
        programs.extend([
            (
                &fsv.feeder_first,
                ExecutionKind::Unified,
                ProofProfile::L1Feeder,
            ),
            (&fsv.feeder, ExecutionKind::Unified, ProofProfile::L1Feeder),
        ]);
    }
    for (program, kind, profile) in programs {
        add(kind, MachineType::Reduced, program, None, profile);
    }
    registrations
}

fn register_pipeline_plan(
    backend: &mut dyn ProveBackend,
    registrations: BTreeMap<HandleKey, BinaryRegistration>,
) {
    for (_, registration) in registrations {
        backend.register(
            registration.kind,
            registration.machine,
            &registration.bin,
            &registration.text,
            registration.cycles_bound,
            &registration.profiles.into_iter().collect::<Vec<_>>(),
        );
    }
}

fn advance_standard_stages(
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
    let unrolled_blake = fsv.unrolled_blake;

    loop {
        let (program, bin, text) = if state.input_is_base {
            (
                FsvProgram::UnrolledBaseLayer,
                &fsv.unrolled_base.0,
                &fsv.unrolled_base.1,
            )
        } else {
            (
                FsvProgram::UnrolledRecursionLayer,
                &fsv.unrolled_recursion.0,
                &fsv.unrolled_recursion.1,
            )
        };
        let estimated = full_statement_verifier::host_utils::cost_model::estimate_verifier_cycles(
            &state.proof,
            program,
            unrolled_blake,
        )
        .map_err(|e| format!("cannot estimate verifier cycles: {e}"))?;
        log::debug!(
            "estimated verifier cost {estimated} cycles vs switch threshold {switch_cycles}"
        );
        if estimated < switch_cycles {
            break;
        }

        let start = Instant::now();
        let (mut new_proof, new_setups) = backend.prove(ProveRequest {
            batch_id,
            bin,
            text,
            kind: ExecutionKind::Unrolled,
            machine: MachineType::Reduced,
            nd_words: build_unrolled_stream(&state.setups, &state.proof),
            profile: ProofProfile::Standard,
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
        state.stage = ProofTarget::RecursionUnrolled;
        return Ok(state);
    }

    // === Bridge: the unrolled verifier proved in UNIFIED machine mode. ===
    let (bridge_bin, bridge_text) = if state.input_is_base {
        &fsv.bridge_base
    } else {
        &fsv.bridge_recursion
    };

    let start = Instant::now();
    let (mut bridge_proof, bridge_setups) = backend.prove(ProveRequest {
        batch_id,
        bin: bridge_bin,
        text: bridge_text,
        kind: ExecutionKind::Unified,
        machine: MachineType::Reduced,
        nd_words: build_unrolled_stream(&state.setups, &state.proof),
        profile: ProofProfile::Standard,
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
    let (final_bin, final_text) = &fsv.unified;

    let mut proof = bridge_proof;
    let mut setups = bridge_setups;
    let mut rounds = 0usize;
    loop {
        let start = Instant::now();
        let (mut new_proof, new_setups) = backend.prove(ProveRequest {
            batch_id,
            bin: final_bin,
            text: final_text,
            kind: ExecutionKind::Unified,
            machine: MachineType::Reduced,
            nd_words: build_unified_stream(&setups, &proof),
            profile: ProofProfile::Standard,
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

    state.stage = ProofTarget::RecursionUnified;
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

type ProgramWords = (Vec<u32>, Vec<u32>);

/// The fsv verifier programs the pipeline runs and the Blake modes they were loaded for,
/// read once per prover. Programs the target never runs stay empty.
struct FsvPrograms {
    unrolled_blake: BlakeMode,
    bridge_blake: BlakeMode,
    final_blake: BlakeMode,
    unrolled_base: ProgramWords,
    unrolled_recursion: ProgramWords,
    bridge_base: ProgramWords,
    bridge_recursion: ProgramWords,
    unified: ProgramWords,
    /// F1: the special-opcodes unified verifier proved at the L1 feeder profile.
    feeder_first: ProgramWords,
    /// F2: the L1 feeder verifier.
    feeder: ProgramWords,
}

impl FsvPrograms {
    fn load(target: ProofTarget, blake: PipelineBlakeModes) -> Self {
        let dir = fsv_dir();
        let PipelineBlakeModes {
            unrolled: unrolled_blake,
            bridge: bridge_blake,
            final_layer: final_blake,
        } = blake;
        let recursion = target != ProofTarget::Base;
        let unified = target >= ProofTarget::RecursionUnified;
        let feeder = target == ProofTarget::L1Feeder;
        let load = |needed: bool, program: FsvProgram, blake: BlakeMode| {
            if needed {
                load_fsv_program(&dir, program, blake)
            } else {
                ProgramWords::default()
            }
        };
        Self {
            unrolled_base: load(recursion, FsvProgram::UnrolledBaseLayer, unrolled_blake),
            unrolled_recursion: load(
                recursion,
                FsvProgram::UnrolledRecursionLayer,
                unrolled_blake,
            ),
            bridge_base: load(unified, FsvProgram::UnrolledBaseLayer, bridge_blake),
            bridge_recursion: load(unified, FsvProgram::UnrolledRecursionLayer, bridge_blake),
            unified: load(unified, FsvProgram::UnifiedRecursionLayer, final_blake),
            feeder_first: load(
                feeder,
                L1_FEEDER_PROGRAMS[0],
                BlakeMode::BlakeSpecialOpcodes,
            ),
            feeder: load(
                feeder,
                L1_FEEDER_PROGRAMS[1],
                BlakeMode::BlakeSpecialOpcodes,
            ),
            unrolled_blake,
            bridge_blake,
            final_blake,
        }
    }

    fn modes(&self) -> PipelineBlakeModes {
        PipelineBlakeModes {
            unrolled: self.unrolled_blake,
            bridge: self.bridge_blake,
            final_layer: self.final_blake,
        }
    }

    fn get(&self, program: FsvProgram, setup_machine: SetupMachine) -> &ProgramWords {
        match (program, setup_machine) {
            (FsvProgram::UnrolledBaseLayer, SetupMachine::UnrolledReduced) => &self.unrolled_base,
            (FsvProgram::UnrolledRecursionLayer, SetupMachine::UnrolledReduced) => {
                &self.unrolled_recursion
            }
            (FsvProgram::UnrolledBaseLayer, SetupMachine::Unified) => &self.bridge_base,
            (FsvProgram::UnrolledRecursionLayer, SetupMachine::Unified) => &self.bridge_recursion,
            (FsvProgram::UnifiedRecursionLayer, SetupMachine::Unified) => &self.unified,
            (FsvProgram::UnifiedRecursionLayer, SetupMachine::UnifiedL1Feeder) => {
                &self.feeder_first
            }
            (FsvProgram::UnifiedRecursionLayerL1Feeder, SetupMachine::UnifiedL1Feeder) => {
                &self.feeder
            }
            other => unreachable!("the recursion chain never runs {other:?}"),
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
        let blake = PipelineBlakeModes::from_env();
        Self::with_registration(source, config, blake, None)
    }

    /// A prover for continuing `artifact`: it loads the blake modes the artifact was proved
    /// with and registers only the binaries of the stages after the artifact's target.
    pub fn for_continuation(
        source: ProgramSource,
        config: ProgramProverConfig,
        artifact: &ProofArtifact,
    ) -> Result<Self, String> {
        let blake = PipelineBlakeModes::continuing(artifact, PipelineBlakeModes::from_env)?;
        Self::with_registration(source, config, blake, Some(artifact.target))
    }

    fn with_registration(
        source: ProgramSource,
        config: ProgramProverConfig,
        blake: PipelineBlakeModes,
        start: Option<ProofTarget>,
    ) -> Result<Self, String> {
        let backend = match config.backend {
            ProverBackend::Cpu => BackendImpl::Cpu(PipelineBackend::new(&config)),
            ProverBackend::Gpu => {
                #[cfg(feature = "gpu")]
                {
                    BackendImpl::Gpu(PipelineBackend::new(&config))
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
            fsv: FsvPrograms::load(config.target, blake),
            config,
            backend,
        };
        prover.register_pipeline_binaries(start)?;
        Ok(prover)
    }

    /// Register every binary the stages after `start` can touch (all of them for `None`).
    fn register_pipeline_binaries(&mut self, start: Option<ProofTarget>) -> Result<(), String> {
        let started = Instant::now();
        let cycles_bound = self.config.cycles_bound;
        if let Some(cycles_bound) = cycles_bound {
            assert!(
                cycles_bound as usize <= MAX_EXECUTION_CYCLES,
                "cycle bound {cycles_bound} exceeds the execution limit {MAX_EXECUTION_CYCLES}"
            );
        }
        let loaded = load_program(&self.source)?;
        let registrations =
            pipeline_registrations(&loaded, start, self.config.target, cycles_bound, &self.fsv);
        let count = registrations.len();
        register_pipeline_plan(self.backend.as_dyn(), registrations);
        log::info!(
            "prepared {count} pipeline binaries in {} ms",
            elapsed_ms(started)
        );
        Ok(())
    }

    /// Verifies a proof made by this prover. The trusted end params come from the setups
    /// this prover computed for its program and the fsv programs, so nothing is recomputed;
    /// `verify_artifact` verifies without trusting this prover.
    pub fn verify(&mut self, artifact: &ProofArtifact) -> Result<[u32; 16], String> {
        if artifact.target != self.config.target {
            return Err(format!(
                "artifact target {:?} differs from this prover's target {:?}",
                artifact.target, self.config.target
            ));
        }
        let loaded = load_and_validate_program(&self.source, artifact)?;
        validate_artifact_chain(artifact)?;
        chain_unrolled_layers(artifact)?;
        let fsv = &self.fsv;
        let backend = self.backend.as_dyn();
        let worker = worker::Worker::new();
        let expected = expected_chain_end_params(
            artifact.target,
            artifact.chain_end_params.len(),
            fsv.unrolled_blake.tag(),
            fsv.bridge_blake.tag(),
            fsv.final_blake.tag(),
            artifact.l1_feeder_rounds,
            &mut |program| {
                let (kind, machine, profile, setup_machine, (bin, text)) = match program {
                    ChainProgram::User => (
                        ExecutionKind::Unrolled,
                        MachineType::FullUnsigned,
                        ProofProfile::Standard,
                        SetupMachine::UnrolledFullUnsigned,
                        (&loaded.bin_u32, &loaded.text_u32),
                    ),
                    ChainProgram::Fsv(program, _, setup_machine) => {
                        let (bin, text) = fsv.get(program, setup_machine);
                        let (kind, profile) = match setup_machine {
                            SetupMachine::Unified => {
                                (ExecutionKind::Unified, ProofProfile::Standard)
                            }
                            SetupMachine::UnifiedL1Feeder => {
                                (ExecutionKind::Unified, ProofProfile::L1Feeder)
                            }
                            _ => (ExecutionKind::Unrolled, ProofProfile::Standard),
                        };
                        (
                            kind,
                            MachineType::Reduced,
                            profile,
                            setup_machine,
                            (bin, text),
                        )
                    }
                };
                match backend.setups(kind, machine, bin, text, profile) {
                    Some(setups) => Ok(compute_end_params(&setups, find_binary_exit_point(bin)?)),
                    // A continuation prover registers only the stages it proves.
                    None => trusted_end_params(bin, text, setup_machine, &worker),
                }
            },
        )?;
        verify_against_chain(artifact, &expected)
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
            profile: ProofProfile::Standard,
        })?;
        let base_ms = elapsed_ms(start);
        log::info!("base layer proved ({} cycles)", proof.executed_cycles());

        let base_end_params = compute_end_params(&setups, proof.final_pc);
        let program_cycles = proof.executed_cycles();
        let state = RecursionState {
            stage: ProofTarget::Base,
            l1_feeder_rounds: None,
            l1_feeder_verifier_cycles: None,
            proof,
            setups,
            chain_end_params: vec![base_end_params],
            input_is_base: true,
            timings: ProofTimingsMs {
                total_ms: 0,
                base_ms,
                unrolled_recursion_ms: Vec::new(),
                unified_recursion_ms: Vec::new(),
                l1_feeder_ms: Vec::new(),
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
        let blake = PipelineBlakeModes::continuing(&artifact, || self.fsv.modes())?;
        if blake != self.fsv.modes() {
            self.fsv = FsvPrograms::load(self.config.target, blake);
            self.register_pipeline_binaries(Some(artifact.target))?;
        }

        let batch_id = artifact.batch_id;
        // A single chain entry (just the base end-params) means no recursion
        // layer ran — the stored proof is a base-layer proof even if the
        // artifact target is RecursionUnrolled.
        let input_is_base = artifact.chain_end_params.len() <= 1;
        let state = RecursionState {
            stage: artifact.target,
            l1_feeder_rounds: artifact.l1_feeder_rounds,
            l1_feeder_verifier_cycles: artifact.l1_feeder_verifier_cycles,
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
            self.config.target,
            self.config.backend,
            batch_id,
            &loaded,
            state,
        ))
    }
}

fn finalize_artifact(
    fsv: &FsvPrograms,
    target: ProofTarget,
    backend: ProverBackend,
    batch_id: u64,
    loaded: &LoadedProgram,
    mut state: RecursionState,
) -> ProofArtifact {
    state.timings.total_ms = state.timings.base_ms
        + state.timings.unrolled_recursion_ms.iter().sum::<u64>()
        + state.timings.unified_recursion_ms.iter().sum::<u64>()
        + state.timings.l1_feeder_ms.iter().sum::<u64>();
    log::info!(
        "proving stages took {} ms (base {} ms, unrolled {:?} ms, unified {:?} ms, feeder {:?} ms)",
        state.timings.total_ms,
        state.timings.base_ms,
        state.timings.unrolled_recursion_ms,
        state.timings.unified_recursion_ms,
        state.timings.l1_feeder_ms
    );

    let chain = rebuild_chain(&state.chain_end_params).expect("chain history is non-empty");
    ProofArtifact {
        schema_version: ARTIFACT_SCHEMA_VERSION,
        security_level: COMPILED_SECURITY_LEVEL,
        target,
        backend,
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
        l1_feeder_rounds: state.l1_feeder_rounds,
        l1_feeder_verifier_cycles: state.l1_feeder_verifier_cycles,
        proof: state.proof,
        setups: state.setups,
    }
}

// ==============================================================================
// Verification
// ==============================================================================

/// Trusted unified chain hashes for zero, one, or at least two unrolled recursion layers.
pub fn unified_verification_chain_hashes(source: &ProgramSource) -> Result<[[u32; 8]; 3], String> {
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
            None,
            &mut recomputed_end_params(&loaded, &worker),
        )?;
        *hash = rebuild_chain(&expected)?.hash();
    }
    Ok(hashes)
}

pub fn verify_artifact(
    artifact: &ProofArtifact,
    source: &ProgramSource,
) -> Result<[u32; 16], String> {
    let loaded = load_and_validate_program(source, artifact)?;
    validate_artifact_chain(artifact)?;
    chain_unrolled_layers(artifact)?;

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
        artifact.l1_feeder_rounds,
        &mut recomputed_end_params(&loaded, &worker),
    )?;
    verify_against_chain(artifact, &expected)
}

fn verify_against_chain(
    artifact: &ProofArtifact,
    expected: &[[u32; 8]],
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
        ProofTarget::Base | ProofTarget::RecursionUnrolled => native_verify_unrolled(
            build_unrolled_stream(&artifact.setups, &artifact.proof),
            is_base,
        ),
        ProofTarget::RecursionUnified => native_verify_unified(
            build_unified_stream(&artifact.setups, &artifact.proof),
            is_base,
        ),
        ProofTarget::L1Feeder => {
            let counts = ProofCounts::from_proof(&artifact.proof);
            if counts.riscv_proof_count != 1 || counts.delegation_proof_count != 0 {
                return Err(
                    "L1Feeder checkpoint must contain one RISC-V proof and no delegation proofs"
                        .into(),
                );
            }
            native_verify_unified_l1_feeder(
                build_unified_stream(&artifact.setups, &artifact.proof),
                false,
            )
        }
    };
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

pub const L1_WRAP_CYCLES_BOUND: usize = 1 << 22;
const FSV_RUN_RAM_BOUND: usize = 1 << 30;

/// Run `bin`/`text` on the reduced machine over `nd_words` and return its exact
/// cycle count, but only if it halts at the binary's success exit within
/// `cycles_bound` (an fsv program only reaches that exit if its proof verifies).
fn measure_fsv_run(
    bin: &[u32],
    text: &[u32],
    nd_words: Vec<u32>,
    cycles_bound: usize,
) -> Result<u64, String> {
    use prover::field::baby_bear::base::BabyBearField;
    use riscv_transpiler::common_constants::{
        INITIAL_TIMESTAMP, ROM_SECOND_WORD_BITS, TIMESTAMP_STEP,
    };
    use riscv_transpiler::cycle::{MachineConfig, ReducedMachineWithDelegation};
    use riscv_transpiler::ir::simple_instruction_set::preprocess_bytecode;
    use riscv_transpiler::vm::{
        DelegationsAndUnifiedCounters, RamWithRomRegion, SimpleTape, State, VM,
    };

    let success_pc = find_binary_exit_point(bin)?;
    let (finished, final_pc, final_timestamp) =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let instructions = preprocess_bytecode::<
                <ReducedMachineWithDelegation as MachineConfig>::DecodingOptions,
                true,
            >(text);
            let tape = SimpleTape::new(&instructions);
            let mut ram = RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(
                bin,
                FSV_RUN_RAM_BOUND,
            );
            let mut state = State::initial_with_counters(DelegationsAndUnifiedCounters::default());
            let mut nd =
                riscv_transpiler::abstractions::non_determinism::QuasiUARTSource::new_with_reads(
                    nd_words,
                );
            let finished = VM::<DelegationsAndUnifiedCounters>::run_basic_unrolled::<
                _,
                _,
                _,
                BabyBearField,
            >(
                &mut state, &mut ram, &mut (), &tape, cycles_bound, &mut nd
            );
            (finished, state.pc, state.timestamp)
        }))
        .map_err(|_| "fsv run aborted before reaching an exit".to_string())?;
    if !finished {
        return Err(format!("fsv run did not halt within {cycles_bound} cycles"));
    }
    if final_pc != success_pc {
        return Err(format!(
            "fsv run halted at pc 0x{final_pc:08x}, not at the success exit 0x{success_pc:08x}"
        ));
    }
    Ok((final_timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP)
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
    UnifiedL1Feeder,
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
        SetupMachine::UnrolledFullUnsigned => {
            compute_unrolled_program_setups::<FullUnsignedConfig, Global>(
                &padded_bin,
                &padded_text,
                use_caches,
                security_level,
                worker,
            )
        }
        SetupMachine::UnrolledReduced => compute_unrolled_program_setups::<ReducedConfig, Global>(
            &padded_bin,
            &padded_text,
            use_caches,
            security_level,
            worker,
        ),
        SetupMachine::UnifiedL1Feeder => {
            setups::program_setups::compute_unified_program_setups_for_profile::<Global>(
                &padded_bin,
                &padded_text,
                use_caches,
                security_level,
                ProofProfile::L1Feeder,
                worker,
            )
        }
        SetupMachine::Unified => compute_unified_program_setups::<Global>(
            &padded_bin,
            &padded_text,
            use_caches,
            security_level,
            worker,
        ),
    }
}

type TrustedEndParamsKey = (SetupMachine, [u8; 32]);

/// In-process cache of trusted `end_params`, keyed by setup machine and binary
/// keccak.
fn trusted_end_params_cache(
) -> &'static std::sync::Mutex<std::collections::HashMap<TrustedEndParamsKey, [u32; 8]>> {
    static CACHE: std::sync::OnceLock<
        std::sync::Mutex<std::collections::HashMap<TrustedEndParamsKey, [u32; 8]>>,
    > = std::sync::OnceLock::new();
    CACHE.get_or_init(Default::default)
}

fn trusted_end_params_key(machine: SetupMachine, bin: &[u32], text: &[u32]) -> TrustedEndParamsKey {
    let mut hasher = Keccak256::new();
    for word in bin.iter().chain(text.iter()) {
        hasher.update(word.to_le_bytes());
    }
    (machine, hasher.finalize().into())
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
    let key = trusted_end_params_key(machine, bin, text);
    let cache = trusted_end_params_cache();
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

fn claimed_unrolled_layers(
    target: ProofTarget,
    n: usize,
    l1_feeder_rounds: Option<u32>,
) -> Result<usize, String> {
    let tail = match target {
        ProofTarget::Base => {
            if n != 1 {
                return Err(format!("Base artifact must claim exactly 1 layer, got {n}"));
            }
            1
        }
        ProofTarget::RecursionUnrolled => 1,
        ProofTarget::RecursionUnified => 3,
        ProofTarget::L1Feeder => {
            let rounds =
                l1_feeder_rounds.ok_or("L1Feeder artifact must declare l1_feeder_rounds")?;
            // Repeated F2 programs have identical end_params; positive counts are telemetry.
            4 + usize::from(rounds > 0)
        }
    };
    n.checked_sub(tail)
        .ok_or_else(|| format!("{target:?} artifact must claim at least {tail} layers, got {n}"))
}

fn chain_unrolled_layers(artifact: &ProofArtifact) -> Result<usize, String> {
    if artifact.target == ProofTarget::L1Feeder {
        let rounds = artifact
            .l1_feeder_rounds
            .ok_or("L1Feeder artifact must declare l1_feeder_rounds")?;
        if rounds > MAX_L1_FEEDER_ROUNDS {
            return Err("L1Feeder round count exceeds the pipeline limit".into());
        }
        match artifact.l1_feeder_verifier_cycles {
            Some(cycles) if cycles > 0 && cycles <= L1_WRAP_CYCLES_BOUND as u64 => {}
            _ => return Err("L1Feeder artifact must declare verifier cycles within the wrap bound (untrusted telemetry)".into()),
        }
    } else if artifact.l1_feeder_rounds.is_some() || artifact.l1_feeder_verifier_cycles.is_some() {
        return Err("non-feeder artifact carries L1Feeder metadata".into());
    }
    claimed_unrolled_layers(
        artifact.target,
        artifact.chain_end_params.len(),
        artifact.l1_feeder_rounds,
    )
}

enum ChainProgram {
    User,
    Fsv(FsvProgram, BlakeMode, SetupMachine),
}

/// End params recomputed from the supplied program and the checked-in fsv binaries.
fn recomputed_end_params<'a>(
    loaded: &'a LoadedProgram,
    worker: &'a worker::Worker,
) -> impl FnMut(ChainProgram) -> Result<[u32; 8], String> + 'a {
    let fsv_dir = fsv_dir();
    move |program| match program {
        ChainProgram::User => trusted_end_params(
            &loaded.bin_u32,
            &loaded.text_u32,
            SetupMachine::UnrolledFullUnsigned,
            worker,
        ),
        ChainProgram::Fsv(program, blake, setup_machine) => {
            let (bin, text) = load_fsv_program(&fsv_dir, program, blake);
            trusted_end_params(&bin, &text, setup_machine, worker)
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
    l1_feeder_rounds: Option<u32>,
    end_params: &mut dyn FnMut(ChainProgram) -> Result<[u32; 8], String>,
) -> Result<Vec<[u32; 8]>, String> {
    let unrolled_layers = claimed_unrolled_layers(target, n, l1_feeder_rounds)?;

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

    if let Some(rounds) = l1_feeder_rounds {
        for program in L1_FEEDER_PROGRAMS
            .into_iter()
            .take(1 + usize::from(rounds > 0))
        {
            expected.push(end_params(ChainProgram::Fsv(
                program,
                BlakeMode::BlakeSpecialOpcodes,
                SetupMachine::UnifiedL1Feeder,
            ))?);
        }
    }

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
    validate_continuation_targets(artifact.target, target)?;
    chain_unrolled_layers(artifact)?;
    validate_artifact_chain(artifact)
}

fn validate_continuation_targets(current: ProofTarget, target: ProofTarget) -> Result<(), String> {
    if current < target && current != ProofTarget::L1Feeder {
        return Ok(());
    }
    if current == target {
        Err(format!(
            "proof artifact is already at target {current:?}; choose a later stage"
        ))
    } else {
        Err(format!(
            "cannot continue proof from {current:?} to {target:?}"
        ))
    }
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
mod l1_feeder_tests;

/// Recursion-binding tests, adapted to `FsvRecursionChain` (no proving
/// required).
#[cfg(test)]
mod recursion_binding_tests {
    use super::*;

    #[test]
    fn cpu_unified_verification_chain_binds_program() {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../examples/hashed_fibonacci");
        let [first, second] = ["app_plain.bin", "app_blake2_with_compression.bin"].map(|name| {
            unified_verification_chain_hashes(&ProgramSource::from_paths(
                dir.join(name).to_string_lossy().into_owned(),
                None,
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
        let (_, bin) = setups::read_binary(&path);
        find_binary_exit_point(&bin).expect("shipped binary must contain one exit sequence");
    }
}

#[cfg(test)]
mod fsv_run_tests {
    use super::*;

    const INPUTS: [u32; 2] = [15, 1];

    fn basic_fibonacci() -> (Vec<u32>, Vec<u32>) {
        let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../examples/basic_fibonacci");
        full_statement_verifier::host_utils::load_program(
            &dir.join("app.bin"),
            &dir.join("app.text"),
        )
    }

    #[test]
    fn measure_fsv_run_counts_exactly_the_cycles_to_the_success_exit() {
        let (bin, text) = basic_fibonacci();
        let cycles = measure_fsv_run(&bin, &text, INPUTS.to_vec(), 1 << 24).unwrap();
        assert!(cycles > 0);
        assert_eq!(
            measure_fsv_run(&bin, &text, INPUTS.to_vec(), cycles as usize),
            Ok(cycles)
        );
        assert!(measure_fsv_run(&bin, &text, INPUTS.to_vec(), cycles as usize - 1).is_err());
    }

    #[test]
    fn measure_fsv_run_rejects_a_run_that_does_not_halt() {
        let (bin, text) = basic_fibonacci();
        assert!(measure_fsv_run(&bin, &text, INPUTS.to_vec(), 16).is_err());
    }
}
