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
mod recursion_progress;
pub use artifact::{ProofArtifact, ARTIFACT_SCHEMA_VERSION};
use guests::{fsv_input, unrolled_verifier_cost, FsvPrograms, ProgramWords};
pub use prover::definitions::SoundnessMode;
use recursion_progress::{drive_final_rounds, finish_operation, FinalRoundSummary};
pub use recursion_progress::{FinalProofShape, PipelineError};

use clap::ValueEnum;
use execution_prover::{BinaryHandle, ProofProfile};
mod fsv_measure;
use fsv_measure::FsvRunReport;
mod l1_wrap;
mod unified_recursion;
use execution_prover_model::circuit_type::{CircuitType, UnrolledCircuitType};
use full_statement_verifier::host_utils::{
    bridge_blake_mode, build_unified_stream, build_unrolled_stream, compute_end_params,
    final_blake_mode, fsv_digest, load_fsv_exact, native_verify_unified,
    native_verify_unified_l1_feeder, native_verify_unified_l1_feeder_a,
    try_native_verify_unified_in_mode, try_native_verify_unrolled_in_mode, unified_switch_cycles,
    unrolled_blake_mode, FsvRecursionChain,
};
use full_statement_verifier::program_proof::ProgramProof;
use l1_wrap::{advance_l1_wrap, validate_artifact_envelope, validate_feeder_proof, L1_WRAP_KIND};
pub use l1_wrap::{L1Bundle, L1WrapVersion};
use riscv_transpiler::vm::FlatResponsesSource;
use serde::{Deserialize, Serialize};
use setups::Setups;
use sha3::{Digest, Keccak256};
use std::alloc::Global;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::time::Instant;
use unified_recursion::UnifiedProofShape;
use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProfile, FsvProgram};

#[cfg(feature = "gpu")]
pub use gpu_execution_prover::MemoryPreset;

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
    #[value(name = "l1")]
    L1,
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
    /// GPU device arena preset; Auto selects according to available device memory.
    #[cfg(feature = "gpu")]
    pub gpu_memory_preset: MemoryPreset,
}

/// The deferred L1 scope (Task S REVISION 3): the ethproofs L1 feeder, wrap and EVM profiles
/// are not implemented. Every L1 entry checks this before it loads a guest, reads an input or
/// creates a backend; there is no fallback to another mode and no mixed-mode chain.
pub fn validate_target_selection(
    target: ProofTarget,
    selection: prover::definitions::ProvingSelection,
) -> Result<(), prover::gkr::prover_config::example_configs::ConfigSelectionError> {
    use prover::definitions::ProverConfigProfile;
    if target >= ProofTarget::L1Feeder {
        ProverConfigProfile::L1Feeder.validate_selection(selection)?;
    }
    if target == ProofTarget::L1 {
        ProverConfigProfile::EvmProductionPacked.validate_selection(selection)?;
    }
    Ok(())
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
            #[cfg(feature = "gpu")]
            gpu_memory_preset: MemoryPreset::Auto,
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
    pub l1_feeder_ms: Vec<u64>,
    pub l1_wrap_ms: Option<u64>,
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

/// The feeder chain must reach one instance within this many layers.
pub const MAX_FEEDER_LAYERS: u32 = 8;
/// The cycle budget of the 2^21 L1 wrap program: the domain of the wrap
/// circuit `ProofTarget::L1` proves in.
pub const L1_WRAP_PROGRAM_CYCLE_LIMIT: usize = 1 << 21;

// ==============================================================================
// Backend abstraction
// ==============================================================================

pub use execution_prover::{ExecutionKind, L1Proof, L1WrapResult, MachineType};

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

    /// Fallible selection-aware registration. Existing implementers retain their register hook.
    fn try_register(
        &mut self,
        kind: ExecutionKind,
        machine: MachineType,
        bin: &[u32],
        text: &[u32],
        cycles_bound: Option<u32>,
        profiles: &[ProofProfile],
    ) -> Result<(), String> {
        self.register(kind, machine, bin, text, cycles_bound, profiles);
        Ok(())
    }

    fn prove(&mut self, request: ProveRequest<'_>) -> Result<(ProgramProof, Setups), String>;

    fn prove_l1_wrap(&mut self, request: L1WrapRequest<'_>) -> Result<L1WrapResult, String>;

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

pub struct L1WrapRequest<'a> {
    pub batch_id: u64,
    pub bin: &'a [u32],
    pub text: &'a [u32],
    pub nd_words: Vec<u32>,
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

#[cfg(test)]
fn register_binary<H>(
    handles: &mut BTreeMap<HandleKey, RegisteredBinary<H>>,
    key: HandleKey,
    profiles: &[ProofProfile],
    prepare: impl FnOnce() -> H,
) {
    try_register_binary(handles, key, profiles, || Ok(prepare()))
        .unwrap_or_else(|error: String| panic!("{error}"));
}

fn try_register_binary<H>(
    handles: &mut BTreeMap<HandleKey, RegisteredBinary<H>>,
    key: HandleKey,
    profiles: &[ProofProfile],
    prepare: impl FnOnce() -> Result<H, String>,
) -> Result<(), String> {
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
                handle: prepare()?,
                profiles,
            });
        }
    }
    Ok(())
}

#[cfg(test)]
thread_local! {
    /// Backends this thread started to construct: the probe that capability rejections
    /// precede backend initialization.
    static BACKEND_CONSTRUCTIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

struct PipelineBackend<B: execution_prover::backend::ExecutionBackend> {
    prover: execution_prover::ExecutionProver<B>,
    handles: BTreeMap<HandleKey, RegisteredBinary<BinaryHandle>>,
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
        Self::with_configuration(config, Self::configuration(config))
    }

    fn with_configuration(
        config: &ProgramProverConfig,
        configuration: execution_prover::ExecutionProverConfiguration<B::Configuration>,
    ) -> Result<Self, String> {
        #[cfg(test)]
        BACKEND_CONSTRUCTIONS.with(|count| count.set(count.get() + 1));
        let prover = execution_prover::ExecutionProver::try_with_configuration(configuration)
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
        profiles: &[ProofProfile],
    ) {
        self.try_register(kind, machine, bin, text, cycles_bound, profiles)
            .unwrap_or_else(|error| panic!("{error}"));
    }

    fn try_register(
        &mut self,
        kind: ExecutionKind,
        machine: MachineType,
        bin: &[u32],
        text: &[u32],
        cycles_bound: Option<u32>,
        profiles: &[ProofProfile],
    ) -> Result<(), String> {
        let prover = &mut self.prover;
        try_register_binary(
            &mut self.handles,
            handle_key(kind, machine, bin, text),
            profiles,
            || {
                prover
                    .try_add_binary(
                        kind,
                        machine,
                        bin.to_vec(),
                        text.to_vec(),
                        cycles_bound,
                        profiles,
                    )
                    .map_err(|error| error.to_string())
            },
        )
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
        assert_ne!(
            profile,
            ProofProfile::L1Wrap,
            "ProofProfile::L1Wrap is proven by prove_l1_wrap, not commit_memory_and_prove"
        );
        let handle = self.handles[&handle_key(kind, machine, bin, text)].handle;
        let result = self.prover.commit_memory_and_prove(
            batch_id,
            &handle,
            FlatResponsesSource::new_with_reads(nd_words),
            profile,
        );
        let artifacts = self.prover.program_artifacts(&handle, profile);
        let (proof, setups) = program_prover::assemble_program_proof(&artifacts, result);
        Ok((proof, setups))
    }

    fn prove_l1_wrap(&mut self, request: L1WrapRequest<'_>) -> Result<L1WrapResult, String> {
        let key = handle_key(
            L1_WRAP_KIND,
            MachineType::Reduced,
            request.bin,
            request.text,
        );
        let binary = self
            .handles
            .get(&key)
            .ok_or("L1Wrap binary was not registered")?;
        Ok(self.prover.prove_l1_wrap(
            request.batch_id,
            &binary.handle,
            FlatResponsesSource::new_with_reads(request.nd_words),
        ))
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
    l1: Option<L1Bundle>,
    proof: ProgramProof,
    setups: Setups,
    chain_end_params: Vec<[u32; 8]>,
    /// Whether `proof` is a base-layer proof (drives fsv-program selection and
    /// stream/verification flavor).
    input_is_base: bool,
    timings: ProofTimingsMs,
    program_cycles: u64,
    /// Feeder layers already proven (the last `feeder_layers` entries of
    /// `chain_end_params`); `proof` is the last of them when nonzero.
    feeder_layers: u32,
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

/// The two roles of the feeder chain: F1 verifies the final standard unified
/// proof, every later layer verifies the previous feeder proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FeederRole {
    First,
    Recurrent,
}

/// The proving profile is independent of the verifier program's input profile.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum FeederProfile {
    A,
    C,
}

impl FeederProfile {
    const ALL: [Self; 2] = [Self::A, Self::C];

    const fn circuit(self) -> UnrolledCircuitType {
        match self {
            Self::A => UnrolledCircuitType::Unified,
            Self::C => UnrolledCircuitType::Unified22,
        }
    }

    const fn kind(self) -> ExecutionKind {
        match self {
            Self::A => ExecutionKind::Unified,
            Self::C => ExecutionKind::Unified22,
        }
    }

    const fn proof_profile(self) -> ProofProfile {
        match self {
            Self::A => ProofProfile::L1FeederA,
            Self::C => ProofProfile::L1Feeder,
        }
    }

    fn config(self) -> prover::gkr::prover_config::ProverConfig {
        execution_prover::prover_config(
            execution_prover_model::circuit_type::CircuitType::Unrolled(self.circuit()),
            self.proof_profile(),
            COMPILED_SECURITY_LEVEL.to_prover(),
        )
    }

    #[cfg(test)]
    fn cap_size(self) -> usize {
        self.config().cap_size
    }

    fn native_verify(self, nd_words: Vec<u32>) -> Result<[u32; 16], String> {
        match self {
            Self::A => native_verify_unified_l1_feeder_a(nd_words),
            Self::C => native_verify_unified_l1_feeder(nd_words),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FeederStageSpec {
    program: FsvProgram,
    /// F1 runs the standard special-opcodes unified verifier, every later layer the
    /// L1 feeder A guest.
    fsv_profile: FsvProfile,
    kind: ExecutionKind,
    profile: ProofProfile,
    setup_machine: SetupMachine,
}

const fn feeder_stage(role: FeederRole, profile: FeederProfile) -> FeederStageSpec {
    FeederStageSpec {
        program: FsvProgram::UnifiedRecursionLayer,
        fsv_profile: match role {
            FeederRole::First => FsvProfile::Standard,
            FeederRole::Recurrent => FsvProfile::L1FeederA,
        },
        kind: profile.kind(),
        profile: profile.proof_profile(),
        setup_machine: SetupMachine::L1Feeder(profile),
    }
}

fn advance_stages<S, E>(
    mut state: S,
    current: ProofTarget,
    target: ProofTarget,
    mut run: impl FnMut(S, ProofTarget) -> Result<S, E>,
) -> Result<S, E> {
    if current < target && current < ProofTarget::RecursionUnified {
        state = run(state, target.min(ProofTarget::RecursionUnified))?;
    }
    if current < ProofTarget::L1Feeder && target >= ProofTarget::L1Feeder {
        state = run(state, ProofTarget::L1Feeder)?;
    }
    if current < ProofTarget::L1 && target == ProofTarget::L1 {
        state = run(state, ProofTarget::L1)?;
    }
    Ok(state)
}

fn advance_to_target(
    backend: &mut dyn ProveBackend,
    fsv: &FsvPrograms,
    state: RecursionState,
    target: ProofTarget,
    batch_id: u64,
    observer: &mut dyn FeederObserver,
    nd: &dyn Fn(&Setups, &ProgramProof) -> Vec<u32>,
    verifier: &dyn FeederVerifier,
) -> Result<RecursionState, PipelineError> {
    let current = state.stage;
    let mut prepared = None;
    advance_stages(state, current, target, |state, next| match next {
        ProofTarget::L1 => {
            let (state, prepared) = match prepared.take() {
                Some(prepared) => (state, prepared),
                None => prepare_external_feeder(fsv, state, nd, verifier)?,
            };
            Ok(advance_l1_wrap(backend, fsv, state, prepared, batch_id)?)
        }
        ProofTarget::L1Feeder => {
            let (state, fit) =
                advance_feeder_stages(backend, fsv, state, batch_id, observer, nd, verifier)?;
            prepared = Some(fit);
            Ok(state)
        }
        _ => advance_standard_stages(backend, fsv, state, next, batch_id),
    })
}

/// The feeder chain: F1 proves the special-opcodes unified verifier over the
/// final standard proof, every later layer proves the feeder verifier over
/// the previous A proof, until one terminal C instance remains; the last proof must
/// then fit the L1 wrap program.
fn advance_feeder_stages(
    backend: &mut dyn ProveBackend,
    fsv: &FsvPrograms,
    state: RecursionState,
    batch_id: u64,
    observer: &mut dyn FeederObserver,
    nd: &dyn Fn(&Setups, &ProgramProof) -> Vec<u32>,
    verifier: &dyn FeederVerifier,
) -> Result<(RecursionState, PreparedFeeder), String> {
    let (state, native_output) =
        run_feeder_layers(backend, fsv, state, batch_id, observer, nd, verifier)?;
    check_feeder_fit(fsv, state, native_output, nd, verifier)
}

/// Sees every proven feeder layer: the state after it and the verifier run
/// that predicted it.
trait FeederObserver {
    fn feeder_layer(
        &mut self,
        layer: u8,
        state: &RecursionState,
        report: &FsvRunReport,
    ) -> Result<(), String>;
}

struct NoopObserver;

impl FeederObserver for NoopObserver {
    fn feeder_layer(&mut self, _: u8, _: &RecursionState, _: &FsvRunReport) -> Result<(), String> {
        Ok(())
    }
}

/// The feeder chain's verifier runs: the native verification of the chain's
/// input, the prediction run of a feeder program over its input stream, the
/// native verification of a feeder proof, and the wrap-program run over the
/// last feeder proof.
trait FeederVerifier {
    fn native_verify_standard(&self, nd_words: Vec<u32>) -> Result<[u32; 16], String>;
    fn predict(&self, program: &ProgramWords, nd_words: Vec<u32>) -> Result<FsvRunReport, String>;
    fn native_verify(
        &self,
        profile: FeederProfile,
        nd_words: Vec<u32>,
    ) -> Result<[u32; 16], String>;
    fn wrap_run(&self, program: &ProgramWords, nd_words: Vec<u32>) -> Result<FsvRunReport, String>;
}

struct ProductionFeederVerifier;

impl FeederVerifier for ProductionFeederVerifier {
    fn native_verify_standard(&self, nd_words: Vec<u32>) -> Result<[u32; 16], String> {
        std::panic::catch_unwind(|| native_verify_unified(nd_words, false))
            .map_err(|_| "final unified proof failed native verification".to_string())
    }

    fn predict(&self, program: &ProgramWords, nd_words: Vec<u32>) -> Result<FsvRunReport, String> {
        let (bin, text) = program;
        fsv_measure::measure_fsv_run_with_counters_and_rom(
            bin,
            text,
            nd_words,
            u32::MAX as usize,
            prover::common_constants::REGULAR_ROM,
        )
    }

    fn native_verify(
        &self,
        profile: FeederProfile,
        nd_words: Vec<u32>,
    ) -> Result<[u32; 16], String> {
        profile.native_verify(nd_words)
    }

    fn wrap_run(&self, program: &ProgramWords, nd_words: Vec<u32>) -> Result<FsvRunReport, String> {
        let (bin, text) = program;
        fsv_measure::measure_fsv_run_with_counters_and_rom(
            bin,
            text,
            nd_words,
            L1_WRAP_PROGRAM_CYCLE_LIMIT,
            prover::common_constants::L1_WRAP_ROM,
        )
    }
}

/// Admission of a private feeder checkpoint before anything is proven:
/// `1..=MAX_FEEDER_LAYERS` feeder layers, setups at the feeder cap, a feeder proof of
/// any positive A instance count or one terminal C instance,
/// and a history equal to the trusted chain of the program (`end_params`
/// recomputes it). The proof's native verification and its binding to this
/// history follow in `run_feeder_layers`.
#[cfg(test)]
fn validate_feeder_checkpoint(
    state: &RecursionState,
    blake: PipelineBlakeModes,
    end_params: &mut dyn FnMut(ChainProgram) -> Result<[u32; 8], String>,
) -> Result<(), String> {
    if !(1..=MAX_FEEDER_LAYERS).contains(&state.feeder_layers) || state.input_is_base {
        return Err(format!(
            "feeder checkpoint must hold 1..={MAX_FEEDER_LAYERS} feeder layers, got {}",
            state.feeder_layers
        ));
    }
    let profile = validate_feeder_proof(&state.proof, None)?;
    setups::validate_setups_cap_size(&state.setups, profile.cap_size())?;
    let expected = expected_chain_end_params(
        ProofTarget::L1Feeder,
        state.chain_end_params.len(),
        state.feeder_layers,
        Some(profile),
        blake.unrolled.tag(),
        blake.bridge.tag(),
        blake.final_layer.tag(),
        end_params,
    )?;
    if expected != state.chain_end_params {
        return Err("feeder checkpoint history does not match the trusted chain".into());
    }
    Ok(())
}

fn delegation_calls(counters: &riscv_transpiler::vm::DelegationsAndUnifiedCounters) -> usize {
    counters.blake_calls
        + counters.bigint_calls
        + counters.keccak_calls
        + counters.keccak_f1600_calls
        + counters.blake_g_function_calls
}

/// A feeder program's prediction run must be a complete, correct
/// verification of its input: the success exit (the measurement enforces
/// it), every input word consumed, the input's native output reproduced,
/// and no delegation calls.
fn validate_prediction_report(
    report: &FsvRunReport,
    input_output: &[u32; 16],
) -> Result<(), String> {
    if report.nd_words_remaining != 0 {
        return Err(format!(
            "feeder verifier run left {} input words unread",
            report.nd_words_remaining
        ));
    }
    if report.output != *input_output {
        return Err("feeder verifier run output differs from the input's native output".into());
    }
    if delegation_calls(&report.counters) != 0 {
        return Err(format!(
            "feeder verifier run issued delegation calls ({:?})",
            report.counters
        ));
    }
    Ok(())
}

/// Choose C exactly when one 2^22 instance fits, otherwise prove at A.
fn predicted_feeder_shape(report: &FsvRunReport) -> Result<(FeederProfile, usize), String> {
    for profile in [FeederProfile::C, FeederProfile::A] {
        let circuit = profile.circuit();
        let shape = UnifiedProofShape::from_counters(circuit, &report.counters);
        if !shape.delegations.is_empty() {
            return Err(format!(
                "feeder verifier run predicts delegation proofs: {shape}"
            ));
        }
        let instances = shape
            .riscv
            .get(&(circuit.get_family_idx() as u32))
            .copied()
            .unwrap_or(0);
        if instances == 0 {
            return Err("feeder verifier run predicts no unified instance".into());
        }
        if profile == FeederProfile::A || instances == 1 {
            return Ok((profile, instances));
        }
    }
    unreachable!("A admits any positive feeder shape")
}

/// Instances of a feeder proof: the reduced family only, no delegation
/// proofs under any key, one inits-and-teardowns instance, and exactly
/// `expected` instances when given.
fn feeder_proof_instances(proof: &ProgramProof, expected: Option<usize>) -> Result<usize, String> {
    let family = UnrolledCircuitType::Unified22.get_family_idx() as u32;
    let instances = match proof.riscv_proofs.keys().collect::<Vec<_>>().as_slice() {
        [key] if **key == family => proof.riscv_proofs[&family].len(),
        keys => {
            return Err(format!(
                "feeder proof must carry the reduced-machine family {family} only, got {keys:?}"
            ))
        }
    };
    if instances == 0 {
        return Err("feeder proof carries no unified instance".into());
    }
    if let Some((kind, _)) = proof
        .delegation_proofs
        .iter()
        .find(|(_, proofs)| !proofs.is_empty())
    {
        return Err(format!(
            "feeder proof carries delegation proofs of type {kind}"
        ));
    }
    if proof.num_it_circuits != Some(1) {
        return Err(format!(
            "feeder proof must carry exactly one inits-and-teardowns instance, got {:?}",
            proof.num_it_circuits
        ));
    }
    if let Some(expected) = expected {
        if instances != expected {
            return Err(format!(
                "feeder proof carries {instances} instance(s), predicted {expected}"
            ));
        }
    }
    Ok(instances)
}

fn run_feeder_layers(
    backend: &mut dyn ProveBackend,
    fsv: &FsvPrograms,
    state: RecursionState,
    batch_id: u64,
    observer: &mut dyn FeederObserver,
    nd: &dyn Fn(&Setups, &ProgramProof) -> Vec<u32>,
    verifier: &dyn FeederVerifier,
) -> Result<(RecursionState, [u32; 16]), String> {
    assert_eq!(
        state.feeder_layers, 0,
        "production feeder entry must start at layer zero"
    );
    run_feeder_layers_inner(backend, fsv, state, batch_id, observer, nd, verifier)
}

fn run_feeder_layers_inner(
    backend: &mut dyn ProveBackend,
    fsv: &FsvPrograms,
    mut state: RecursionState,
    batch_id: u64,
    observer: &mut dyn FeederObserver,
    nd: &dyn Fn(&Setups, &ProgramProof) -> Vec<u32>,
    verifier: &dyn FeederVerifier,
) -> Result<(RecursionState, [u32; 16]), String> {
    let mut chain = rebuild_chain(&state.chain_end_params)?;
    let mut layer = state.feeder_layers;
    let (mut input_output, mut previous_instances) = if layer == 0 {
        (
            verifier.native_verify_standard(nd(&state.setups, &state.proof))?,
            None,
        )
    } else {
        let profile = validate_feeder_proof(&state.proof, None)?;
        let output = verifier.native_verify(profile, nd(&state.setups, &state.proof))?;
        ensure_recursion_chain_binds_program(&output, &chain.hash())?;
        if profile == FeederProfile::C {
            return Ok((state, output));
        }
        (output, Some(feeder_proof_instances(&state.proof, None)?))
    };
    loop {
        if layer >= MAX_FEEDER_LAYERS {
            return Err(format!(
                "L1 feeder chain did not reach one terminal C instance within {MAX_FEEDER_LAYERS} layers"
            ));
        }
        let role = if layer == 0 {
            FeederRole::First
        } else {
            FeederRole::Recurrent
        };
        let program = fsv.feeder_program(role);
        let report = verifier.predict(program, nd(&state.setups, &state.proof))?;
        validate_prediction_report(&report, &input_output)?;
        let (profile, predicted) = predicted_feeder_shape(&report)?;
        log::info!(
            "L1 feeder layer {layer}: {} verifier cycles -> {profile:?} x {predicted} instance(s)",
            report.cycles
        );
        if let Some(previous) = previous_instances {
            if profile == FeederProfile::A && predicted >= previous {
                return Err(format!(
                    "L1 feeder chain is not converging: layer {layer} would verify {previous} instance(s) into {predicted} ({} verifier cycles)",
                    report.cycles
                ));
            }
        }
        state = advance_feeder_stage(backend, program, profile, &mut chain, state, batch_id, nd)?;
        if validate_feeder_proof(&state.proof, Some(predicted))? != profile {
            return Err("feeder backend returned a proof under the wrong profile".into());
        }
        let instances = predicted;
        let output = verifier.native_verify(profile, nd(&state.setups, &state.proof))?;
        ensure_recursion_chain_binds_program(&output, &chain.hash())?;
        input_output = output;
        layer += 1;
        state.feeder_layers = layer;
        observer.feeder_layer((layer - 1) as u8, &state, &report)?;
        previous_instances = Some(instances);
        if profile == FeederProfile::C {
            return Ok((state, output));
        }
    }
}

fn advance_feeder_stage(
    backend: &mut dyn ProveBackend,
    fsv_program: &ProgramWords,
    profile: FeederProfile,
    chain: &mut FsvRecursionChain,
    mut state: RecursionState,
    batch_id: u64,
    nd: &dyn Fn(&Setups, &ProgramProof) -> Vec<u32>,
) -> Result<RecursionState, String> {
    let (bin, text) = fsv_program;
    let spec = feeder_stage(FeederRole::Recurrent, profile);
    let start = Instant::now();
    let (mut proof, setups) = backend.prove(ProveRequest {
        batch_id,
        bin,
        text,
        kind: spec.kind,
        machine: MachineType::Reduced,
        nd_words: nd(&state.setups, &state.proof),
        profile: spec.profile,
    })?;
    state.timings.l1_feeder_ms.push(elapsed_ms(start));
    proof.set_recursion_chain(chain);
    let end_params = compute_end_params(&setups, proof.final_pc);
    chain.extend(&end_params);
    state.chain_end_params.push(end_params);
    state.proof = proof;
    state.setups = setups;
    log::info!(
        "L1 feeder layer {} ({profile:?}) proved ({} cycles)",
        state.feeder_layers,
        state.proof.executed_cycles()
    );
    Ok(state)
}

/// The wrap program's run over the last feeder proof must reach its success
/// exit within [`L1_WRAP_PROGRAM_CYCLE_LIMIT`] with the native output,
/// exhausted input, no delegation calls, at most two touched 8 MiB windows
/// and the stack inside its reservation.
fn validate_wrap_report(report: &FsvRunReport, native_output: &[u32; 16]) -> Result<(), String> {
    use prover::common_constants::L1_WRAP_ROM;
    if report.cycles > L1_WRAP_PROGRAM_CYCLE_LIMIT as u64 {
        return Err(format!(
            "wrap program runs {} cycles, over the {L1_WRAP_PROGRAM_CYCLE_LIMIT} budget",
            report.cycles
        ));
    }
    if report.output != *native_output {
        return Err("wrap program output differs from the native verifier output".into());
    }
    if report.nd_words_remaining != 0 {
        return Err(format!(
            "wrap program left {} input words unread",
            report.nd_words_remaining
        ));
    }
    if delegation_calls(&report.counters) != 0 {
        return Err(format!(
            "wrap program issued delegation calls ({:?})",
            report.counters
        ));
    }
    if report.touched_windows.len() > 2 {
        return Err(format!(
            "wrap program touched {} 8 MiB windows {:?}",
            report.touched_windows.len(),
            report.touched_windows
        ));
    }
    if report.min_sp < L1_WRAP_ROM.byte_size() as u32 {
        return Err(format!(
            "wrap program stack reached 0x{:08x}, below its reservation",
            report.min_sp
        ));
    }
    Ok(())
}

struct PreparedFeeder {
    nd_words: Vec<u32>,
    native_output: [u32; 16],
    report: FsvRunReport,
}

impl PreparedFeeder {
    fn validate(&self) -> Result<(), String> {
        validate_wrap_report(&self.report, &self.native_output)
            .map_err(|e| format!("feeder proof verifier does not fit the L1 wrap: {e}"))
    }
}

fn check_feeder_fit(
    fsv: &FsvPrograms,
    mut state: RecursionState,
    native_output: [u32; 16],
    nd: &dyn Fn(&Setups, &ProgramProof) -> Vec<u32>,
    verifier: &dyn FeederVerifier,
) -> Result<(RecursionState, PreparedFeeder), String> {
    l1_wrap::validate_last_feeder_proof(&state.proof)?;
    let nd_words = nd(&state.setups, &state.proof);
    let report = verifier
        .wrap_run(&fsv.feeder_wrap, nd_words.clone())
        .map_err(|e| format!("feeder proof verifier does not fit the L1 wrap: {e}"))?;
    let prepared = PreparedFeeder {
        nd_words,
        native_output,
        report,
    };
    prepared.validate()?;
    state.stage = ProofTarget::L1Feeder;
    state.input_is_base = false;
    Ok((state, prepared))
}

/// An external C artifact has no in-process authentication or fit receipt.
fn prepare_external_feeder(
    fsv: &FsvPrograms,
    state: RecursionState,
    nd: &dyn Fn(&Setups, &ProgramProof) -> Vec<u32>,
    verifier: &dyn FeederVerifier,
) -> Result<(RecursionState, PreparedFeeder), String> {
    l1_wrap::validate_last_feeder_proof(&state.proof)?;
    let native_output =
        verifier.native_verify(FeederProfile::C, nd(&state.setups, &state.proof))?;
    ensure_recursion_chain_binds_program(
        &native_output,
        &rebuild_chain(&state.chain_end_params)?.hash(),
    )?;
    check_feeder_fit(fsv, state, native_output, nd, verifier)
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
) -> Result<BTreeMap<HandleKey, BinaryRegistration>, String> {
    let mut registrations = BTreeMap::<HandleKey, BinaryRegistration>::new();
    let mut add = |kind, machine, (bin, text): (&[u32], &[u32]), cycles_bound, profile| {
        registrations
            .entry(handle_key(kind, machine, bin, text))
            .or_insert_with(|| BinaryRegistration {
                kind,
                machine,
                bin: bin.to_vec(),
                text: text.to_vec(),
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
            (&loaded.bin_u32, &loaded.text_u32),
            cycles_bound,
            ProofProfile::Standard,
        );
    }
    let start = start.unwrap_or(ProofTarget::Base);
    let mut programs = Vec::new();
    if start < ProofTarget::RecursionUnified && target > ProofTarget::Base {
        for program in [
            FsvProgram::UnrolledBaseLayer,
            FsvProgram::UnrolledRecursionLayer,
        ] {
            programs.push((
                fsv.words(program, FsvProfile::Standard, SetupMachine::UnrolledReduced)?,
                ExecutionKind::Unrolled,
                ProofProfile::Standard,
            ));
        }
    }
    if start < ProofTarget::RecursionUnified && target >= ProofTarget::RecursionUnified {
        for program in [
            FsvProgram::UnrolledBaseLayer,
            FsvProgram::UnrolledRecursionLayer,
            FsvProgram::UnifiedRecursionLayer,
        ] {
            programs.push((
                fsv.words(program, FsvProfile::Standard, SetupMachine::Unified)?,
                ExecutionKind::Unified,
                ProofProfile::Standard,
            ));
        }
    }
    if start < ProofTarget::L1Feeder && target >= ProofTarget::L1Feeder {
        for role in [FeederRole::First, FeederRole::Recurrent] {
            for profile in FeederProfile::ALL {
                let spec = feeder_stage(role, profile);
                let (bin, text) = fsv.feeder_program(role);
                programs.push(((bin.as_slice(), text.as_slice()), spec.kind, spec.profile));
            }
        }
    }
    if start < ProofTarget::L1 && target == ProofTarget::L1 {
        let (bin, text) = &fsv.feeder_wrap;
        programs.push((
            (bin.as_slice(), text.as_slice()),
            L1_WRAP_KIND,
            ProofProfile::L1Wrap,
        ));
    }
    for (program, kind, profile) in programs {
        add(kind, MachineType::Reduced, program, None, profile);
    }
    Ok(registrations)
}

fn register_pipeline_plan(
    backend: &mut dyn ProveBackend,
    registrations: BTreeMap<HandleKey, BinaryRegistration>,
) -> Result<(), String> {
    for (_, registration) in registrations {
        backend.try_register(
            registration.kind,
            registration.machine,
            &registration.bin,
            &registration.text,
            registration.cycles_bound,
            &registration.profiles.into_iter().collect::<Vec<_>>(),
        )?;
    }
    Ok(())
}

fn advance_standard_stages(
    backend: &mut dyn ProveBackend,
    fsv: &FsvPrograms,
    mut state: RecursionState,
    target: ProofTarget,
    batch_id: u64,
) -> Result<RecursionState, PipelineError> {
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
    let final_guest = fsv.get(FsvProgram::UnifiedRecursionLayer, SetupMachine::Unified)?;

    let mut rounds = 0usize;
    let (proof, setups) = drive_final_rounds(
        (bridge_proof, bridge_setups),
        final_mode,
        |(proof, setups), round| {
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
            rounds = round + 1;
            log::debug!(
                "unified recursion round {rounds} proved ({} cycles)",
                new_proof.executed_cycles()
            );
            Ok((new_proof, new_setups))
        },
        |(proof, setups)| FinalRoundSummary {
            shape: FinalProofShape {
                unified_chunks: proof.riscv_proofs.values().map(Vec::len).sum(),
                delegation_proofs: proof.delegation_proofs.values().map(Vec::len).sum(),
            },
            converged: unified_recursion_has_converged(proof, final_mode),
            executed_cycles: proof.executed_cycles(),
            unified_chunk_capacity: setups
                .values()
                .map(|params| u64::from(params.capacity))
                .min()
                .unwrap_or(0),
        },
    )?;
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

fn unified_recursion_has_converged(proof: &ProgramProof, final_mode: BlakeMode) -> bool {
    UnifiedProofShape::from_proof(proof).has_converged(final_mode)
}

fn pipeline_backend(backend: &mut Option<BackendImpl>) -> Result<&mut dyn ProveBackend, String> {
    backend.as_mut().map(BackendImpl::as_dyn).ok_or_else(|| {
        "PipelineBackendStopped: create a new prover after a failed operation".to_owned()
    })
}

/// A proving session. Any proving or continuation error shuts down its backend;
/// create a new session to retry, including after an input-validation error.
pub struct ProgramProver {
    source: ProgramSource,
    config: ProgramProverConfig,
    backend: Option<BackendImpl>,
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
        validate_target_selection(config.target, config.selection())
            .map_err(|error| error.to_string())?;
        artifact.validate_expected_mode(config.soundness_mode)?;
        validate_continuation_request(artifact, config.target)?;
        load_and_validate_program(&source, artifact)?;
        let blake = PipelineBlakeModes::continuing(artifact, PipelineBlakeModes::from_env)?;
        Self::with_registration(source, config, blake, Some(artifact.target))
    }

    fn with_registration(
        source: ProgramSource,
        config: ProgramProverConfig,
        blake: PipelineBlakeModes,
        start: Option<ProofTarget>,
    ) -> Result<Self, String> {
        validate_target_selection(config.target, config.selection())
            .map_err(|error| error.to_string())?;
        let fsv = FsvPrograms::load(config.target, config.selection(), blake)?;
        assert_eq!(fsv.selection, config.selection());
        // Resolve source errors before creating the backend's worker pools and buffers.
        load_program(&source)?;
        let backend = match config.backend {
            ProverBackend::Cpu => BackendImpl::Cpu(PipelineBackend::new(&config)?),
            ProverBackend::Gpu => {
                #[cfg(feature = "gpu")]
                {
                    let mut configuration =
                        PipelineBackend::<gpu_execution_prover::GpuBackend>::configuration(&config);
                    configuration.backend.memory_preset = config.gpu_memory_preset;
                    BackendImpl::Gpu(PipelineBackend::with_configuration(&config, configuration)?)
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
            backend: Some(backend),
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
            pipeline_registrations(&loaded, start, self.config.target, cycles_bound, &self.fsv)?;
        let count = registrations.len();
        register_pipeline_plan(pipeline_backend(&mut self.backend)?, registrations)?;
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
        let backend = pipeline_backend(&mut self.backend)?;
        let worker = worker::Worker::new();
        let expected = expected_chain_end_params(
            artifact.target,
            artifact.chain_end_params.len(),
            artifact.feeder_layers,
            None,
            fsv.unrolled_blake.tag(),
            fsv.bridge_blake.tag(),
            fsv.final_blake.tag(),
            &mut |program| {
                let (kind, machine, profile, setup_machine, (bin, text)) = match program {
                    ChainProgram::User => (
                        ExecutionKind::Unrolled,
                        MachineType::FullUnsigned,
                        ProofProfile::Standard,
                        SetupMachine::UnrolledFullUnsigned,
                        (loaded.bin_u32.as_slice(), loaded.text_u32.as_slice()),
                    ),
                    ChainProgram::Fsv(program, fsv_profile, _, setup_machine) => {
                        let (bin, text) = fsv.words(program, fsv_profile, setup_machine)?;
                        let (kind, profile) = match setup_machine {
                            SetupMachine::Unified => {
                                (ExecutionKind::Unified, ProofProfile::Standard)
                            }
                            SetupMachine::L1Feeder(profile) => {
                                let spec = feeder_stage(FeederRole::Recurrent, profile);
                                (spec.kind, spec.profile)
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
                    None => trusted_end_params_in_mode(
                        bin,
                        text,
                        setup_machine,
                        self.config.selection(),
                        &worker,
                    ),
                }
            },
        )?;
        verify_against_chain(artifact, &expected, self.config.soundness_mode)
    }

    /// String-error compatibility entry point; failures shut down the session's backend.
    pub fn prove_words(
        &mut self,
        batch_id: u64,
        input_words: Vec<u32>,
    ) -> Result<ProofArtifact, String> {
        self.prove_words_typed(batch_id, input_words)
            .map_err(|error| error.to_string())
    }

    /// Typed proving entry point. A failed operation shuts down the backend before returning.
    pub fn prove_words_typed(
        &mut self,
        batch_id: u64,
        input_words: Vec<u32>,
    ) -> Result<ProofArtifact, PipelineError> {
        pipeline_backend(&mut self.backend)?;
        let result = self.prove_words_inner(batch_id, input_words);
        finish_operation(&mut self.backend, result)
    }

    fn prove_words_inner(
        &mut self,
        batch_id: u64,
        input_words: Vec<u32>,
    ) -> Result<ProofArtifact, PipelineError> {
        let loaded = load_program(&self.source)?;

        // Base layer: the user program, unrolled, full-unsigned ISA.
        let start = Instant::now();
        let (proof, setups) = pipeline_backend(&mut self.backend)?.prove(ProveRequest {
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
            l1: None,
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
                l1_wrap_ms: None,
            },
            program_cycles,
            feeder_layers: 0,
        };

        let state = advance_to_target(
            pipeline_backend(&mut self.backend)?,
            &self.fsv,
            state,
            self.config.target,
            batch_id,
            &mut NoopObserver,
            &|s: &Setups, p: &ProgramProof| {
                build_unified_stream(s, p, BlakeMode::BlakeSpecialOpcodes)
            },
            &ProductionFeederVerifier,
        )?;

        Ok(finalize_artifact(
            &self.fsv,
            &self.config,
            batch_id,
            &loaded,
            state,
        ))
    }

    /// String-error compatibility entry point; failures shut down the session's backend.
    pub fn continue_artifact(&mut self, artifact: ProofArtifact) -> Result<ProofArtifact, String> {
        self.continue_artifact_typed(artifact)
            .map_err(|error| error.to_string())
    }

    /// Typed continuation entry point. A failed operation shuts down the backend before returning.
    pub fn continue_artifact_typed(
        &mut self,
        artifact: ProofArtifact,
    ) -> Result<ProofArtifact, PipelineError> {
        self.continue_artifact_observed(artifact, &mut NoopObserver)
    }

    #[cfg(all(test, feature = "gpu"))]
    fn for_feeder_checkpoint(
        source: ProgramSource,
        config: ProgramProverConfig,
        blake: PipelineBlakeModes,
    ) -> Result<Self, String> {
        assert_eq!(config.target, ProofTarget::L1Feeder);
        Self::with_registration(source, config, blake, Some(ProofTarget::RecursionUnified))
    }

    #[cfg(all(test, feature = "gpu"))]
    fn resume_feeder_checkpoint(
        &mut self,
        state: RecursionState,
        batch_id: u64,
        observer: &mut dyn FeederObserver,
    ) -> Result<ProofArtifact, String> {
        let loaded = load_program(&self.source)?;
        let worker = worker::Worker::new();
        validate_feeder_checkpoint(
            &state,
            self.fsv.modes(),
            &mut recomputed_end_params(&loaded, &worker, self.config.selection()),
        )?;
        let build_feeder_stream = |s: &Setups, p: &ProgramProof| {
            build_unified_stream(s, p, BlakeMode::BlakeSpecialOpcodes)
        };
        let (state, native_output) = run_feeder_layers_inner(
            pipeline_backend(&mut self.backend)?,
            &self.fsv,
            state,
            batch_id,
            observer,
            &build_feeder_stream,
            &ProductionFeederVerifier,
        )?;
        let (mut state, _prepared) = check_feeder_fit(
            &self.fsv,
            state,
            native_output,
            &build_feeder_stream,
            &ProductionFeederVerifier,
        )?;
        state.stage = ProofTarget::L1Feeder;
        Ok(finalize_artifact(
            &self.fsv,
            &self.config,
            batch_id,
            &loaded,
            state,
        ))
    }

    fn continue_artifact_observed(
        &mut self,
        artifact: ProofArtifact,
        observer: &mut dyn FeederObserver,
    ) -> Result<ProofArtifact, PipelineError> {
        pipeline_backend(&mut self.backend)?;
        let result = self.continue_artifact_inner(artifact, observer);
        finish_operation(&mut self.backend, result)
    }

    fn continue_artifact_inner(
        &mut self,
        artifact: ProofArtifact,
        observer: &mut dyn FeederObserver,
    ) -> Result<ProofArtifact, PipelineError> {
        artifact.validate_expected_mode(self.config.soundness_mode)?;
        validate_continuation_request(&artifact, self.config.target)?;
        // A serialized checkpoint is untrusted even when its mode label matches.
        verify_artifact_in_mode(&artifact, &self.source, self.config.soundness_mode)?;
        let loaded = load_and_validate_program(&self.source, &artifact)?;
        let blake = PipelineBlakeModes::continuing(&artifact, || self.fsv.modes())?;
        if blake != self.fsv.modes() {
            self.fsv = FsvPrograms::load(self.config.target, self.config.selection(), blake)?;
            self.register_pipeline_binaries(Some(artifact.target))?;
        }

        let batch_id = artifact.batch_id;
        // A single chain entry (just the base end-params) means no recursion
        // layer ran — the stored proof is a base-layer proof even if the
        // artifact target is RecursionUnrolled.
        let input_is_base = artifact.chain_end_params.len() <= 1;
        let state = RecursionState {
            stage: artifact.target,
            l1: artifact.l1,
            proof: artifact.proof,
            setups: artifact.setups,
            chain_end_params: artifact.chain_end_params,
            input_is_base,
            timings: artifact.timings_ms,
            program_cycles: artifact.program_cycles,
            feeder_layers: artifact.feeder_layers,
        };

        let state = advance_to_target(
            pipeline_backend(&mut self.backend)?,
            &self.fsv,
            state,
            self.config.target,
            batch_id,
            observer,
            &|s: &Setups, p: &ProgramProof| {
                build_unified_stream(s, p, BlakeMode::BlakeSpecialOpcodes)
            },
            &ProductionFeederVerifier,
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
        + state.timings.unified_recursion_ms.iter().sum::<u64>()
        + state.timings.l1_feeder_ms.iter().sum::<u64>()
        + state.timings.l1_wrap_ms.unwrap_or(0);
    log::info!(
        "proving stages took {} ms (base {} ms, unrolled {:?} ms, unified {:?} ms, feeder {:?} ms, wrap {:?} ms)",
        state.timings.total_ms,
        state.timings.base_ms,
        state.timings.unrolled_recursion_ms,
        state.timings.unified_recursion_ms,
        state.timings.l1_feeder_ms,
        state.timings.l1_wrap_ms
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
        feeder_layers: state.feeder_layers,
        chain_hash: chain.hash(),
        chain_preimage: chain.preimage(),
        // The pipeline resolves the blake modes from the environment (see
        // host_utils); record the tags so verification reconstructs the same
        // pipeline regardless of the verify-time environment.
        blake_unrolled: fsv.unrolled_blake.tag().to_string(),
        blake_bridge: fsv.bridge_blake.tag().to_string(),
        blake_final: fsv.final_blake.tag().to_string(),
        l1: state.l1,
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
            0,
            None,
            unrolled_blake.tag(),
            bridge_blake.tag(),
            final_blake.tag(),
            &mut recomputed_end_params(&loaded, &worker, selection_in_mode(mode)),
        )?;
        *hash = rebuild_chain(&expected)?.hash();
    }
    Ok(hashes)
}

/// Verifies `proof` against the trusted recursion chain of `source`. For an L1 artifact this
/// covers the feeder proof and its chain; the Proth proof stays unverified.
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
        artifact.feeder_layers,
        None,
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
        ProofTarget::L1Feeder | ProofTarget::L1 => {
            let profile = validate_feeder_proof(&artifact.proof, Some(1))?;
            profile
                .native_verify(build_unified_stream(
                    &artifact.setups,
                    &artifact.proof,
                    verifier_common::BLAKE_MODE,
                ))
                .map_err(full_statement_verifier::host_utils::NativeVerificationError::InvalidProof)
        }
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
    L1Feeder(FeederProfile),
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
        SetupMachine::L1Feeder(profile) => {
            prover::definitions::ProverConfigProfile::L1Feeder
                .validate_selection(selection)
                .map_err(|error| error.to_string())?;
            Ok(
                setups::program_setups::compute_unified_program_setups_for_profile::<Global>(
                    &padded_bin,
                    &padded_text,
                    use_caches,
                    security_level,
                    profile.proof_profile(),
                    worker,
                ),
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
    let profile = match machine {
        SetupMachine::L1Feeder(_) => prover::definitions::ProverConfigProfile::L1Feeder,
        _ => prover::definitions::ProverConfigProfile::Standard,
    };
    let key = trusted_end_params_key(machine, bin, text, selection, profile);
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

/// The unrolled recursion layers an artifact's history claims: `n` minus the
/// fixed tail (base; bridge and final for unified targets) minus the claimed
/// feeder layers (`1..=MAX_FEEDER_LAYERS` for the feeder targets, 0 before).
fn claimed_unrolled_layers(
    target: ProofTarget,
    n: usize,
    feeder_layers: u32,
) -> Result<usize, String> {
    let feeder_targets = target >= ProofTarget::L1Feeder;
    if feeder_targets && !(1..=MAX_FEEDER_LAYERS).contains(&feeder_layers) {
        return Err(format!(
            "{target:?} artifact must claim between 1 and {MAX_FEEDER_LAYERS} feeder layers, got {feeder_layers}"
        ));
    }
    if !feeder_targets && feeder_layers != 0 {
        return Err(format!(
            "{target:?} artifact must claim no feeder layers, got {feeder_layers}"
        ));
    }
    let tail = match target {
        ProofTarget::Base => {
            if n != 1 {
                return Err(format!("Base artifact must claim exactly 1 layer, got {n}"));
            }
            1
        }
        ProofTarget::RecursionUnrolled => 1,
        ProofTarget::RecursionUnified => 3,
        ProofTarget::L1Feeder | ProofTarget::L1 => 3 + feeder_layers as usize,
    };
    n.checked_sub(tail)
        .ok_or_else(|| format!("{target:?} artifact must claim at least {tail} layers, got {n}"))
}

fn chain_unrolled_layers(artifact: &ProofArtifact) -> Result<usize, String> {
    claimed_unrolled_layers(
        artifact.target,
        artifact.chain_end_params.len(),
        artifact.feeder_layers,
    )
}

enum ChainProgram {
    User,
    Fsv(FsvProgram, FsvProfile, BlakeMode, SetupMachine),
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
        ChainProgram::Fsv(program, profile, blake, setup_machine) => {
            let descriptor = FsvDescriptor {
                profile,
                ..FsvDescriptor::new(
                    selection.security_level,
                    selection.soundness_mode,
                    program,
                    blake,
                )
            };
            let guest = load_fsv_exact(&fsv_dir, &descriptor).map_err(|error| error.to_string())?;
            trusted_end_params_in_mode(guest.bin(), guest.text(), setup_machine, selection, worker)
        }
    }
}

/// Reconstruct the pipeline's per-layer `end_params` from trusted inputs only, which
/// `end_params` supplies per chain program. The artifact contributes only the CLAIM shape:
/// target, number of chain entries, last feeder profile, and blake tags.
fn expected_chain_end_params(
    target: ProofTarget,
    n: usize,
    feeder_layers: u32,
    last_feeder_profile: Option<FeederProfile>,
    blake_unrolled: &str,
    blake_bridge: &str,
    blake_final: &str,
    end_params: &mut dyn FnMut(ChainProgram) -> Result<[u32; 8], String>,
) -> Result<Vec<[u32; 8]>, String> {
    let unrolled_layers = claimed_unrolled_layers(target, n, feeder_layers)?;

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
            FsvProfile::Standard,
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
        FsvProfile::Standard,
        bridge_blake,
        SetupMachine::Unified,
    ))?);

    // Final: fsv_unified_recursion_layer on the unified machine.
    let final_blake = parse_blake_tag(blake_final, FsvProgram::UnifiedRecursionLayer)?;
    expected.push(end_params(ChainProgram::Fsv(
        FsvProgram::UnifiedRecursionLayer,
        FsvProfile::Standard,
        final_blake,
        SetupMachine::Unified,
    ))?);

    if target >= ProofTarget::L1Feeder {
        // C is terminal; every earlier feeder layer uses A.
        for layer in 0..feeder_layers {
            let role = if layer == 0 {
                FeederRole::First
            } else {
                FeederRole::Recurrent
            };
            let profile = if layer + 1 == feeder_layers {
                last_feeder_profile.unwrap_or(FeederProfile::C)
            } else {
                FeederProfile::A
            };
            let spec = feeder_stage(role, profile);
            expected.push(end_params(ChainProgram::Fsv(
                spec.program,
                spec.fsv_profile,
                BlakeMode::BlakeSpecialOpcodes,
                spec.setup_machine,
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
    validate_artifact_envelope(artifact)?;
    validate_continuation_targets(artifact.target, target)?;
    chain_unrolled_layers(artifact)?;
    validate_artifact_chain(artifact)
}

fn validate_continuation_targets(current: ProofTarget, target: ProofTarget) -> Result<(), String> {
    if current < target {
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
    validate_artifact_envelope(artifact)?;
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

#[cfg(test)]
mod l1_feeder_tests;

#[cfg(test)]
mod l1_reference;

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

/// The deferred-scope boundary of the L1 targets (the pipeline counterpart of Task S's
/// standalone L1 compression checks): ethproofs is rejected with the exact capability error
/// before any guest, input or backend is touched; pessimistic L1 entries pass it unchanged.
#[cfg(test)]
mod l1_capability_tests {
    use super::*;
    use prover::definitions::{ProverConfigProfile, ProvingSelection};
    use prover::gkr::prover_config::example_configs::ConfigSelectionError;

    const L1_TARGETS: [ProofTarget; 2] = [ProofTarget::L1Feeder, ProofTarget::L1];

    fn deferred() -> String {
        ConfigSelectionError::UnsupportedSpecialConfigMode {
            profile: ProverConfigProfile::L1Feeder,
            mode: SoundnessMode::EthproofsSoundnessCalc,
        }
        .to_string()
    }

    fn missing() -> ProgramSource {
        let source = ProgramSource::elf("must-not-read-l1-capability-input.elf");
        assert!(matches!(&source, ProgramSource::Elf(path) if !path.exists()));
        source
    }

    fn backend_constructions() -> usize {
        BACKEND_CONSTRUCTIONS.with(std::cell::Cell::get)
    }

    #[test]
    fn deferred_scope_error_keeps_the_task_s_wording() {
        assert_eq!(
            deferred(),
            "UnsupportedSpecialConfigMode: ethproofs soundness mode is not implemented for the L1 feeder/wrap/EVM profile (deferred product scope); requested L1Feeder"
        );
        for target in L1_TARGETS {
            for (mode, expected) in [
                (
                    SoundnessMode::EthproofsSoundnessCalc,
                    Err(ConfigSelectionError::UnsupportedSpecialConfigMode {
                        profile: ProverConfigProfile::L1Feeder,
                        mode: SoundnessMode::EthproofsSoundnessCalc,
                    }),
                ),
                (SoundnessMode::PessimisticConjecture, Ok(())),
            ] {
                let selection = ProvingSelection {
                    soundness_mode: mode,
                    ..ProvingSelection::default()
                };
                assert_eq!(validate_target_selection(target, selection), expected);
            }
        }
        for target in [
            ProofTarget::Base,
            ProofTarget::RecursionUnrolled,
            ProofTarget::RecursionUnified,
        ] {
            for &mode in SoundnessMode::ALL {
                let selection = ProvingSelection {
                    soundness_mode: mode,
                    ..ProvingSelection::default()
                };
                validate_target_selection(target, selection).unwrap();
            }
        }
    }

    /// CPU and GPU entries: the rejection precedes guest loading, the (missing) source and
    /// backend construction, so no CUDA is reached even in a `gpu` build.
    #[test]
    fn ethproofs_l1_prover_entries_reject_before_inputs_and_backends() {
        let before = backend_constructions();
        let checkpoint = crate::l1_feeder_tests::artifact(ProofTarget::RecursionUnified, 3);
        for target in L1_TARGETS {
            for backend in [ProverBackend::Cpu, ProverBackend::Gpu] {
                let config = ProgramProverConfig {
                    target,
                    backend,
                    soundness_mode: SoundnessMode::EthproofsSoundnessCalc,
                    ..Default::default()
                };
                let error = ProgramProver::new(missing(), config.clone())
                    .err()
                    .expect("ethproofs L1 proving must be rejected");
                assert_eq!(error, deferred(), "{target:?} on {backend:?}");
                let error = ProgramProver::for_continuation(missing(), config, &checkpoint)
                    .err()
                    .expect("ethproofs L1 continuation must be rejected");
                assert_eq!(error, deferred(), "{target:?} on {backend:?}");
            }
        }
        assert_eq!(backend_constructions(), before);
    }

    /// Verify and continue take the expected mode the way `verify_artifact_in_mode` does: an L1
    /// artifact is pessimistic only, whether ethproofs is requested or claimed.
    #[test]
    fn l1_artifacts_are_pessimistic_only() {
        for target in L1_TARGETS {
            let pessimistic = crate::l1_feeder_tests::feeder_artifact(target, 6, 3);
            let mut claimed = pessimistic.clone();
            claimed.soundness_mode = SoundnessMode::EthproofsSoundnessCalc;
            for (artifact, expected) in [
                (&pessimistic, SoundnessMode::EthproofsSoundnessCalc),
                (&claimed, SoundnessMode::EthproofsSoundnessCalc),
                (&claimed, SoundnessMode::PessimisticConjecture),
            ] {
                assert_eq!(
                    artifact.validate_expected_mode(expected).unwrap_err(),
                    deferred()
                );
                assert_eq!(
                    verify_artifact_in_mode(artifact, &missing(), expected).unwrap_err(),
                    deferred()
                );
            }
            pessimistic
                .validate_expected_mode(SoundnessMode::PessimisticConjecture)
                .unwrap();
        }
    }

    /// The pessimistic L1 entries pass the check and reach the source as before.
    #[test]
    fn pessimistic_l1_entries_are_unchanged() {
        let before = backend_constructions();
        for target in L1_TARGETS {
            let config = ProgramProverConfig {
                target,
                backend: ProverBackend::Cpu,
                ..Default::default()
            };
            let error = ProgramProver::new(missing(), config)
                .err()
                .expect("a missing source must be reported");
            assert!(error.starts_with("failed to load program"), "{error}");
            // Past the mode check, verification fails later (envelope or source), never with
            // the capability error.
            let artifact = crate::l1_feeder_tests::feeder_artifact(target, 6, 3);
            let error = verify_artifact_in_mode(
                &artifact,
                &missing(),
                SoundnessMode::PessimisticConjecture,
            )
            .unwrap_err();
            assert!(!error.contains("deferred product scope"), "{error}");
        }
        assert_eq!(backend_constructions(), before);
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

    /// GPU + ethproofs is not a capability rejection: the source error comes
    /// first, as on the CPU.
    #[test]
    fn gpu_ethproofs_source_error_precedes_backend_construction() {
        let config = ProgramProverConfig {
            target: ProofTarget::Base,
            backend: ProverBackend::Gpu,
            soundness_mode: SoundnessMode::EthproofsSoundnessCalc,
            ..ProgramProverConfig::default()
        };
        let source = ProgramSource::legacy_binaries_from_bin(std::path::Path::new(
            "/does-not-exist/task-s-program.bin",
        ));
        let error = match ProgramProver::new(source, config) {
            Err(error) => error,
            Ok(_) => panic!("GPU ethproofs pipeline unexpectedly initialized"),
        };
        assert!(error.starts_with("failed to load program"), "{error}");
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
