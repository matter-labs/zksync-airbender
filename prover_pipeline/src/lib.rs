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
//! The pipeline follows these stages:
//!
//!   base (unrolled, full-unsigned ISA)
//!   → unrolled recursion layers (reduced ISA, fsv verifier binaries) while the
//!     estimated verifier cost stays at/above `unified_switch_cycles()`, or exactly
//!     `RECURSION_UNROLLED_LAYERS` additional layers per invocation when set
//!   → bridge (the unrolled verifier proved in UNIFIED machine mode)
//!   → final (fsv_unified_recursion_layer, unified mode), repeated until the
//!     proof converges to one unified + one delegation proof

mod artifact;
mod guests;
pub use artifact::{ProofArtifact, ARTIFACT_SCHEMA_VERSION};
use guests::{fsv_input, unrolled_verifier_cost, FsvPrograms};
pub use program_prover::{deserialize_from_file, serialize_to_file};
pub use prover::definitions::SoundnessMode;

use clap::ValueEnum;
use execution_prover::{BinaryHandle, ProofProfile};
mod l1_wrap;
use execution_prover_model::circuit_type::{CircuitType, UnrolledCircuitType};
use full_statement_verifier::host_utils::{
    build_unified_stream, build_unrolled_stream, compute_end_params, fsv_digest, load_fsv_exact,
    native_verify_unified_compression_in_mode, native_verify_unified_in_mode,
    native_verify_unrolled_in_mode, recursion_unrolled_layers, unified_switch_cycles,
    FsvRecursionChain,
};
use full_statement_verifier::program_proof::ProgramProof;
pub use l1_wrap::L1Bundle;
use l1_wrap::{
    advance_l1_wrap, validate_artifact_envelope, validate_compression_proof, L1_WRAP_KIND,
};
use riscv_transpiler::vm::FlatResponsesSource;
use serde::{Deserialize, Serialize};
use setups::Setups;
use sha3::{Digest, Keccak256};
use std::alloc::Global;
use std::collections::{BTreeMap, BTreeSet};
#[cfg(test)]
use std::path::Path;
use std::path::PathBuf;
use std::time::Instant;
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
    #[value(name = "compression")]
    Compression,
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

/// The deferred L1 scope: the ethproofs wrap and EVM profiles are not implemented.
/// Every L1 entry asserts this before it loads a guest, reads an input or creates a backend;
/// there is no fallback to another mode and no mixed-mode chain. The assert is the profile's
/// [`ProverConfigProfile::assert_supports`](prover::definitions::ProverConfigProfile::assert_supports).
fn assert_target_mode(target: ProofTarget, soundness_mode: prover::definitions::SoundnessMode) {
    use prover::definitions::ProverConfigProfile;
    if target >= ProofTarget::Compression {
        ProverConfigProfile::Compression.assert_supports(soundness_mode);
    }
    if target == ProofTarget::L1 {
        ProverConfigProfile::EvmProductionPacked.assert_supports(soundness_mode);
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
    pub compression_ms: Vec<u64>,
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

// ==============================================================================
// Backend abstraction
// ==============================================================================

pub use execution_prover::{ExecutionKind, L1Proof, L1WrapResult, MachineType};

/// One required op: prove `bin`/`text` (UNPADDED words; backends pad as they
/// need) in the given machine/kind with `nd_words` as the non-determinism
/// stream, returning the assembled `(ProgramProof, Setups)` pair.
pub trait ProveBackend {
    /// Backend precomputations run here, before any timed prove.
    fn register_variants(
        &mut self,
        bin: &[u32],
        text: &[u32],
        variants: &[(ExecutionKind, MachineType, &[ProofProfile], &str)],
        cycles_bound: Option<u32>,
    );

    fn finalize_setup(&mut self);

    fn prove(&mut self, request: ProveRequest<'_>) -> (ProgramProof, Setups);

    fn prove_l1_wrap(&mut self, request: L1WrapRequest<'_>) -> L1WrapResult;

    /// `Setups` of a registered binary and profile, from its precomputations.
    fn setups(
        &mut self,
        kind: ExecutionKind,
        machine: MachineType,
        bin: &[u32],
        text: &[u32],
        profile: ProofProfile,
    ) -> Setups;
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

struct RegisteredBinary {
    handle: BinaryHandle,
    role: String,
}

struct PipelineBackend<B: execution_prover::backend::ExecutionBackend> {
    prover: execution_prover::ExecutionProver<B>,
    handles: BTreeMap<HandleKey, RegisteredBinary>,
}

impl<B: execution_prover::backend::ExecutionBackend> PipelineBackend<B> {
    fn configuration(
        config: &ProgramProverConfig,
    ) -> execution_prover::ExecutionProverConfiguration<B::Configuration> {
        let defaults = execution_prover::ExecutionProverConfiguration::<B::Configuration>::for_mode(
            config.soundness_mode,
        );
        execution_prover::ExecutionProverConfiguration {
            max_thread_pool_threads: config.worker_threads,
            replay_worker_threads_count: config
                .replay_threads
                .unwrap_or(defaults.replay_worker_threads_count),
            soundness_mode: config.soundness_mode,
            ram_config: config.ram_size.jit(),
            ..defaults
        }
    }

    fn new(config: &ProgramProverConfig) -> Self {
        Self::with_configuration(Self::configuration(config))
    }

    fn with_configuration(
        configuration: execution_prover::ExecutionProverConfiguration<B::Configuration>,
    ) -> Self {
        let prover = execution_prover::ExecutionProver::with_configuration(configuration);
        Self {
            prover,
            handles: std::collections::BTreeMap::new(),
        }
    }
}

impl<B: execution_prover::backend::ExecutionBackend> ProveBackend for PipelineBackend<B> {
    fn finalize_setup(&mut self) {
        self.prover.finalize_setup();
    }

    fn register_variants(
        &mut self,
        bin: &[u32],
        text: &[u32],
        variants: &[(ExecutionKind, MachineType, &[ProofProfile], &str)],
        cycles_bound: Option<u32>,
    ) {
        for &(_, _, _, role) in variants {
            log::info!("registering {role}");
        }
        let kinds: Vec<_> = variants
            .iter()
            .map(|&(kind, machine, profiles, _)| (kind, machine, profiles))
            .collect();
        let handles =
            self.prover
                .add_binary_variants(bin.to_vec(), text.to_vec(), &kinds, cycles_bound);
        for (&(kind, machine, _, role), handle) in variants.iter().zip(handles) {
            log::info!("registered {role} with key {handle:?}");
            assert!(
                self.handles
                    .insert(
                        handle_key(kind, machine, bin, text),
                        RegisteredBinary {
                            handle,
                            role: role.to_owned(),
                        },
                    )
                    .is_none(),
                "pipeline binary was registered twice"
            );
        }
    }

    fn prove(&mut self, request: ProveRequest<'_>) -> (ProgramProof, Setups) {
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
        let registered = &self.handles[&handle_key(kind, machine, bin, text)];
        let handle = registered.handle;
        log::info!(
            "producing proof for {} with key {handle:?}",
            registered.role
        );
        let result = self.prover.commit_memory_and_prove(
            batch_id,
            &handle,
            FlatResponsesSource::new_with_reads(nd_words),
            profile,
        );
        let artifacts = self.prover.program_artifacts(&handle, profile);
        let (proof, setups) = program_prover::assemble_program_proof(&artifacts, result);
        (proof, setups)
    }

    fn prove_l1_wrap(&mut self, request: L1WrapRequest<'_>) -> L1WrapResult {
        let key = handle_key(
            L1_WRAP_KIND,
            MachineType::Reduced,
            request.bin,
            request.text,
        );
        let binary = self
            .handles
            .get(&key)
            .expect("L1Wrap binary was not registered");
        self.prover.prove_l1_wrap(
            request.batch_id,
            &binary.handle,
            FlatResponsesSource::new_with_reads(request.nd_words),
        )
    }

    fn setups(
        &mut self,
        kind: ExecutionKind,
        machine: MachineType,
        bin: &[u32],
        text: &[u32],
        profile: ProofProfile,
    ) -> Setups {
        let registered = &self.handles[&handle_key(kind, machine, bin, text)];
        program_prover::program_setups(&self.prover.program_artifacts(&registered.handle, profile))
    }
}

// ==============================================================================
// Pipeline driver
// ==============================================================================

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

/// The first compression layer verifies the final Standard unified
/// proof; later layers verify the previous Compression proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CompressionRole {
    First,
    Recurrent,
}

fn compression_schedule(
    mode: SoundnessMode,
) -> &'static [(CompressionRole, CompressionProfile, usize)] {
    match mode {
        SoundnessMode::PessimisticConjecture => &[
            (CompressionRole::First, CompressionProfile::Step, 2),
            (CompressionRole::Recurrent, CompressionProfile::Step, 1),
            (CompressionRole::Recurrent, CompressionProfile::Final, 1),
        ],
        SoundnessMode::EthproofsSoundnessCalc => &[
            (CompressionRole::First, CompressionProfile::Step, 3),
            (CompressionRole::Recurrent, CompressionProfile::Step, 2),
            (CompressionRole::Recurrent, CompressionProfile::Step, 1),
        ],
    }
}

/// The proving profile is independent of the verifier program's input profile.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
enum CompressionProfile {
    Step,
    Final,
}

impl CompressionProfile {
    #[cfg(test)]
    const ALL: [Self; 2] = [Self::Step, Self::Final];

    const fn circuit(self) -> UnrolledCircuitType {
        match self {
            Self::Step => UnrolledCircuitType::Unified,
            Self::Final => UnrolledCircuitType::Unified22,
        }
    }

    const fn kind(self) -> ExecutionKind {
        match self {
            Self::Step => ExecutionKind::Unified,
            Self::Final => ExecutionKind::Unified22,
        }
    }

    const fn proof_profile(self) -> ProofProfile {
        match self {
            Self::Step => ProofProfile::Compression,
            Self::Final => ProofProfile::CompressionFinal,
        }
    }

    fn config(self, mode: SoundnessMode) -> prover::gkr::prover_config::ProverConfig {
        self.proof_profile()
            .prover_config(self.circuit().get_domain_size_log2() as usize, mode)
    }

    #[cfg(test)]
    fn cap_size(self, mode: SoundnessMode) -> usize {
        self.config(mode).cap_size
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CompressionStageSpec {
    program: FsvProgram,
    /// The first layer runs the Standard special-opcodes unified verifier;
    /// later layers run the repeatable Compression guest.
    fsv_profile: FsvProfile,
    kind: ExecutionKind,
    profile: ProofProfile,
    setup_machine: SetupMachine,
}

const fn compression_stage(
    role: CompressionRole,
    profile: CompressionProfile,
) -> CompressionStageSpec {
    CompressionStageSpec {
        program: FsvProgram::UnifiedRecursionLayer,
        fsv_profile: match role {
            CompressionRole::First => FsvProfile::Standard,
            CompressionRole::Recurrent => FsvProfile::Compression,
        },
        kind: profile.kind(),
        profile: profile.proof_profile(),
        setup_machine: SetupMachine::Compression(profile),
    }
}

fn advance_to_target(
    backend: &mut dyn ProveBackend,
    fsv: &FsvPrograms,
    mut state: RecursionState,
    target: ProofTarget,
    mode: SoundnessMode,
    batch_id: u64,
) -> RecursionState {
    if state.stage < target && state.stage < ProofTarget::RecursionUnified {
        state = advance_standard_stages(
            backend,
            fsv,
            state,
            target.min(ProofTarget::RecursionUnified),
            batch_id,
        );
    }
    if state.stage < ProofTarget::Compression && target >= ProofTarget::Compression {
        state = advance_compression_stages(backend, fsv, state, mode, batch_id);
    }
    if state.stage < ProofTarget::L1 && target == ProofTarget::L1 {
        state = advance_l1_wrap(backend, fsv, state, batch_id);
    }
    state
}

fn advance_compression_stages(
    backend: &mut dyn ProveBackend,
    fsv: &FsvPrograms,
    mut state: RecursionState,
    mode: SoundnessMode,
    batch_id: u64,
) -> RecursionState {
    assert!(
        unified_recursion_has_converged(&state.proof),
        "compression seed must be a converged unified proof"
    );
    let mut chain = rebuild_chain(&state.chain_end_params).expect("compression seed has a chain");
    for (layer, &(role, profile, instances)) in compression_schedule(mode).iter().enumerate() {
        let (bin, text) = fsv.compression_program(role);
        let spec = compression_stage(role, profile);
        let start = Instant::now();
        let (mut proof, setups) = backend.prove(ProveRequest {
            batch_id,
            bin,
            text,
            kind: spec.kind,
            machine: MachineType::Reduced,
            nd_words: build_unified_stream(
                &state.setups,
                &state.proof,
                BlakeMode::BlakeSpecialOpcodes,
            ),
            profile: spec.profile,
        });
        validate_compression_proof(&proof, profile, instances, mode)
            .unwrap_or_else(|error| panic!("compression layer {layer}: {error}"));
        setups::validate_setups_cap_size(&setups, profile.config(mode).cap_size)
            .unwrap_or_else(|error| panic!("compression layer {layer}: {error}"));
        state.timings.compression_ms.push(elapsed_ms(start));
        proof.set_recursion_chain(&chain);
        let end_params = compute_end_params(&setups, proof.final_pc);
        chain.extend(&end_params);
        state.chain_end_params.push(end_params);
        log::info!(
            "compression layer {layer} ({profile:?}) proved ({} cycles)",
            proof.executed_cycles()
        );
        state.proof = proof;
        state.setups = setups;
    }
    state.stage = ProofTarget::Compression;
    state.input_is_base = false;
    state
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
    target: ProofTarget,
    mode: SoundnessMode,
    cycles_bound: Option<u32>,
    fsv: &FsvPrograms,
) -> BTreeMap<HandleKey, BinaryRegistration> {
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
    add(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        (&loaded.bin_u32, &loaded.text_u32),
        cycles_bound,
        ProofProfile::Standard,
    );
    let mut programs = Vec::new();
    if target > ProofTarget::Base {
        for program in [
            FsvProgram::UnrolledBaseLayer,
            FsvProgram::UnrolledRecursionLayer,
        ] {
            programs.push((
                fsv.words(program, FsvProfile::Standard, SetupMachine::UnrolledReduced),
                ExecutionKind::Unrolled,
                ProofProfile::Standard,
            ));
        }
    }
    if target >= ProofTarget::RecursionUnified {
        for program in [
            FsvProgram::UnrolledBaseLayer,
            FsvProgram::UnrolledRecursionLayer,
            FsvProgram::UnifiedRecursionLayer,
        ] {
            programs.push((
                fsv.words(program, FsvProfile::Standard, SetupMachine::Unified),
                ExecutionKind::Unified,
                ProofProfile::Standard,
            ));
        }
    }
    if target >= ProofTarget::Compression {
        for &(role, profile, _) in compression_schedule(mode) {
            let spec = compression_stage(role, profile);
            let (bin, text) = fsv.compression_program(role);
            programs.push(((bin, text), spec.kind, spec.profile));
        }
    }
    if target == ProofTarget::L1 {
        let guest = fsv
            .compression_wrap
            .as_ref()
            .expect("L1 wrap guest was not loaded");
        let (bin, text) = (guest.bin(), guest.text());
        programs.push(((bin, text), L1_WRAP_KIND, ProofProfile::L1Wrap));
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
    let mut groups: Vec<Vec<BinaryRegistration>> = Vec::new();
    for (_, registration) in registrations {
        if let Some(group) = groups.iter_mut().find(|group| {
            group[0].bin == registration.bin
                && group[0].text == registration.text
                && group[0].cycles_bound == registration.cycles_bound
        }) {
            group.push(registration);
        } else {
            groups.push(vec![registration]);
        }
    }
    for group in groups {
        let profiles: Vec<Vec<_>> = group
            .iter()
            .map(|r| r.profiles.iter().copied().collect())
            .collect();
        let variants: Vec<_> = group
            .iter()
            .zip(&profiles)
            .map(|(r, p)| {
                (
                    r.kind,
                    r.machine,
                    p.as_slice(),
                    match r.kind {
                        ExecutionKind::Unrolled => "unrolled pipeline program",
                        ExecutionKind::Unified => "unified pipeline program",
                        ExecutionKind::Unified22 => "terminal compression program",
                        ExecutionKind::L1Wrap => "L1 wrap program",
                    },
                )
            })
            .collect();
        backend.register_variants(
            &group[0].bin,
            &group[0].text,
            &variants,
            group[0].cycles_bound,
        );
    }
    backend.finalize_setup();
}

fn advance_standard_stages(
    backend: &mut dyn ProveBackend,
    fsv: &FsvPrograms,
    mut state: RecursionState,
    target: ProofTarget,
    batch_id: u64,
) -> RecursionState {
    if target == ProofTarget::Base {
        return state;
    }

    let mut chain =
        rebuild_chain(&state.chain_end_params).expect("recursion state has a base layer");
    let unrolled_layers = recursion_unrolled_layers();
    let switch_cycles = unrolled_layers.is_none().then(unified_switch_cycles);

    // === Unrolled recursion layers. ===
    let mut previous_cycles = None;
    let mut layers_proved = 0;
    loop {
        if unrolled_layers == Some(layers_proved) {
            break;
        }
        let program = if state.input_is_base {
            FsvProgram::UnrolledBaseLayer
        } else {
            FsvProgram::UnrolledRecursionLayer
        };
        let guest = fsv.get(program, SetupMachine::UnrolledReduced);
        if let Some(switch_cycles) = switch_cycles {
            let cycles = unrolled_verifier_cost(guest, &state.proof);
            log::debug!(
                "selected verifier cost {cycles} cycles vs switch threshold {switch_cycles}"
            );
            if cycles < switch_cycles {
                break;
            }
            if let Some(previous) = previous_cycles {
                assert!(
                    cycles < previous,
                    "unrolled recursion did not lower the estimated verifier cost \
                     ({previous} -> {cycles} cycles) while at or above the switch threshold \
                     {switch_cycles}"
                );
            }
            previous_cycles = Some(cycles);
        }
        let nd_words = fsv_input(guest, &state.setups, &state.proof);
        let start = Instant::now();
        let (mut new_proof, new_setups) = backend.prove(ProveRequest {
            batch_id,
            bin: guest.bin(),
            text: guest.text(),
            kind: ExecutionKind::Unrolled,
            machine: MachineType::Reduced,
            nd_words,
            profile: ProofProfile::Standard,
        });
        state.timings.unrolled_recursion_ms.push(elapsed_ms(start));
        layers_proved += 1;
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
        return state;
    }

    // === Bridge: the unrolled verifier proved in UNIFIED machine mode. ===
    let bridge_program = if state.input_is_base {
        FsvProgram::UnrolledBaseLayer
    } else {
        FsvProgram::UnrolledRecursionLayer
    };
    let bridge = fsv.get(bridge_program, SetupMachine::Unified);
    let nd_words = fsv_input(bridge, &state.setups, &state.proof);
    let start = Instant::now();
    let (mut bridge_proof, bridge_setups) = backend.prove(ProveRequest {
        batch_id,
        bin: bridge.bin(),
        text: bridge.text(),
        kind: ExecutionKind::Unified,
        machine: MachineType::Reduced,
        nd_words,
        profile: ProofProfile::Standard,
    });
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
    let final_mode = BlakeMode::Compression;
    let final_guest = fsv.get(FsvProgram::UnifiedRecursionLayer, SetupMachine::Unified);

    let mut rounds = 0usize;
    let mut previous_shape = None;
    let (mut proof, mut setups) = (bridge_proof, bridge_setups);
    loop {
        let nd_words = fsv_input(final_guest, &setups, &proof);
        let start = Instant::now();
        let (mut new_proof, new_setups) = backend.prove(ProveRequest {
            batch_id,
            bin: final_guest.bin(),
            text: final_guest.text(),
            kind: ExecutionKind::Unified,
            machine: MachineType::Reduced,
            nd_words,
            profile: ProofProfile::Standard,
        });
        state.timings.unified_recursion_ms.push(elapsed_ms(start));
        new_proof.set_recursion_chain(&chain);
        let end_params = compute_end_params(&new_setups, new_proof.final_pc);
        chain.extend(&end_params);
        // Verification models repeated rounds of the final program as one chain entry.
        if state.chain_end_params.last() != Some(&end_params) {
            state.chain_end_params.push(end_params);
        }
        rounds += 1;
        proof = new_proof;
        setups = new_setups;
        let shape = (
            proof.riscv_proofs.values().map(Vec::len).sum::<usize>(),
            proof
                .delegation_proofs
                .values()
                .map(Vec::len)
                .sum::<usize>(),
        );
        log::debug!(
            "final recursion shape {shape:?}, {} cycles",
            proof.executed_cycles()
        );
        if unified_recursion_has_converged(&proof) {
            break;
        }
        // The first bridge-to-final transition can increase either count.
        if let Some(before) = previous_shape {
            assert!(
                shape < before,
                "final Blake {} round {rounds} did not reduce \
                 (unified chunks, delegation proofs): {before:?} -> {shape:?}",
                final_mode.tag(),
            );
        }
        previous_shape = Some(shape);
    }
    log::info!(
        "unified recursion converged after {rounds} round(s) ({} cycles)",
        proof.executed_cycles()
    );

    state.stage = ProofTarget::RecursionUnified;
    state.proof = proof;
    state.setups = setups;
    state.input_is_base = false;
    state
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

/// Standard recursion converges to one unified proof and one Blake delegation proof.
fn unified_recursion_has_converged(proof: &ProgramProof) -> bool {
    let riscv: usize = proof.riscv_proofs.values().map(|v| v.len()).sum();
    let delegation: usize = proof.delegation_proofs.values().map(|v| v.len()).sum();
    riscv == 1 && delegation == 1
}

/// A proving session.
pub struct ProgramProver {
    source: ProgramSource,
    config: ProgramProverConfig,
    backend: BackendImpl,
    fsv: FsvPrograms,
}

impl ProgramProver {
    pub fn new(source: ProgramSource, config: ProgramProverConfig) -> Result<Self, String> {
        assert_target_mode(config.target, config.soundness_mode);
        let fsv = FsvPrograms::load(config.target, config.soundness_mode);
        // Resolve source errors before creating the backend's worker pools and buffers.
        let loaded = load_program(&source)?;
        let backend = match config.backend {
            ProverBackend::Cpu => BackendImpl::Cpu(PipelineBackend::new(&config)),
            ProverBackend::Gpu => {
                #[cfg(feature = "gpu")]
                {
                    let mut configuration =
                        PipelineBackend::<gpu_execution_prover::GpuBackend>::configuration(&config);
                    configuration.backend.memory_preset = config.gpu_memory_preset;
                    BackendImpl::Gpu(PipelineBackend::with_configuration(configuration))
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
        prover.register_pipeline_binaries(&loaded);
        Ok(prover)
    }

    /// Register the complete pipeline from the user program through the target.
    fn register_pipeline_binaries(&mut self, loaded: &LoadedProgram) {
        let started = Instant::now();
        let cycles_bound = self.config.cycles_bound;
        if let Some(cycles_bound) = cycles_bound {
            assert!(
                cycles_bound as usize <= MAX_EXECUTION_CYCLES,
                "cycle bound {cycles_bound} exceeds the execution limit {MAX_EXECUTION_CYCLES}"
            );
        }
        let registrations = pipeline_registrations(
            loaded,
            self.config.target,
            self.config.soundness_mode,
            cycles_bound,
            &self.fsv,
        );
        let count = registrations.len();
        register_pipeline_plan(self.backend.as_dyn(), registrations);
        log::info!(
            "prepared {count} pipeline binaries in {} ms",
            elapsed_ms(started)
        );
    }

    /// Verifies a proof made by this prover. The trusted end params come from the setups
    /// this prover computed for its program and the fsv programs, so nothing is recomputed;
    /// `verify_artifact_in_mode` verifies without trusting this prover.
    pub fn verify(&mut self, artifact: &ProofArtifact) -> Result<[u32; 16], String> {
        artifact.validate_expected_mode(self.config.soundness_mode)?;
        if artifact.target != self.config.target {
            validate_continuation_request(artifact, self.config.target)?;
        }
        validate_artifact_envelope(artifact)?;
        let loaded = load_and_validate_program(&self.source, artifact)?;
        validate_artifact_chain(artifact)?;
        let fsv = &self.fsv;
        let backend = self.backend.as_dyn();
        let mut final_setups = None;
        let expected = expected_chain_end_params(
            artifact.target,
            artifact.soundness_mode,
            artifact.chain_end_params.len(),
            BlakeMode::Compression.tag(),
            BlakeMode::Compression.tag(),
            BlakeMode::Compression.tag(),
            &mut |program| {
                let (kind, machine, profile, (bin, text)) = match program {
                    ChainProgram::User => (
                        ExecutionKind::Unrolled,
                        MachineType::FullUnsigned,
                        ProofProfile::Standard,
                        (loaded.bin_u32.as_slice(), loaded.text_u32.as_slice()),
                    ),
                    ChainProgram::Fsv(program, fsv_profile, _, setup_machine) => {
                        let (bin, text) = fsv.words(program, fsv_profile, setup_machine);
                        let (kind, profile) = match setup_machine {
                            SetupMachine::Unified => {
                                (ExecutionKind::Unified, ProofProfile::Standard)
                            }
                            SetupMachine::Compression(profile) => {
                                let spec = compression_stage(CompressionRole::Recurrent, profile);
                                (spec.kind, spec.profile)
                            }
                            _ => (ExecutionKind::Unrolled, ProofProfile::Standard),
                        };
                        (kind, MachineType::Reduced, profile, (bin, text))
                    }
                };
                let setups = backend.setups(kind, machine, bin, text, profile);
                let end_params = compute_end_params(&setups, find_binary_exit_point(bin)?);
                final_setups = Some(setups);
                Ok(end_params)
            },
        )?;
        verify_against_chain(
            artifact,
            &expected,
            self.config.soundness_mode,
            final_setups.as_ref(),
        )
    }

    /// Prove `input_words` from the base layer to the configured target.
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
        });
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
                compression_ms: Vec::new(),
                l1_wrap_ms: None,
            },
            program_cycles,
        };

        let state = advance_to_target(
            self.backend.as_dyn(),
            &self.fsv,
            state,
            self.config.target,
            self.config.soundness_mode,
            batch_id,
        );

        Ok(finalize_artifact(&self.config, batch_id, &loaded, state))
    }

    /// Verify and continue an artifact using this session's registered pipeline.
    pub fn continue_artifact(&mut self, artifact: ProofArtifact) -> Result<ProofArtifact, String> {
        validate_continuation_request(&artifact, self.config.target)?;
        self.verify(&artifact)?;
        let loaded = load_and_validate_program(&self.source, &artifact)?;

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
        };

        let state = advance_to_target(
            self.backend.as_dyn(),
            &self.fsv,
            state,
            self.config.target,
            self.config.soundness_mode,
            batch_id,
        );

        Ok(finalize_artifact(&self.config, batch_id, &loaded, state))
    }
}

fn finalize_artifact(
    config: &ProgramProverConfig,
    batch_id: u64,
    loaded: &LoadedProgram,
    mut state: RecursionState,
) -> ProofArtifact {
    state.timings.total_ms = state.timings.base_ms
        + state.timings.unrolled_recursion_ms.iter().sum::<u64>()
        + state.timings.unified_recursion_ms.iter().sum::<u64>()
        + state.timings.compression_ms.iter().sum::<u64>()
        + state.timings.l1_wrap_ms.unwrap_or(0);
    log::info!(
        "proving stages took {} ms (base {} ms, unrolled {:?} ms, unified {:?} ms, compression {:?} ms, wrap {:?} ms)",
        state.timings.total_ms,
        state.timings.base_ms,
        state.timings.unrolled_recursion_ms,
        state.timings.unified_recursion_ms,
        state.timings.compression_ms,
        state.timings.l1_wrap_ms
    );

    let chain = rebuild_chain(&state.chain_end_params).expect("chain history is non-empty");
    ProofArtifact {
        schema_version: ARTIFACT_SCHEMA_VERSION,
        security_level: COMPILED_SECURITY_LEVEL,
        soundness_mode: config.soundness_mode,
        target: config.target,
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
        // Keep the fixed stage-mode tags in the artifact schema.
        blake_unrolled: BlakeMode::Compression.tag().to_string(),
        blake_bridge: BlakeMode::Compression.tag().to_string(),
        blake_final: BlakeMode::Compression.tag().to_string(),
        l1: state.l1,
        proof: state.proof,
        setups: state.setups,
    }
}

// ==============================================================================
// Verification
// ==============================================================================

/// Trusted unified chain hashes, under a caller-selected standard soundness mode, for zero, one,
/// or at least two unrolled recursion layers.
pub fn unified_verification_chain_hashes_in_mode(
    source: &ProgramSource,
    mode: SoundnessMode,
) -> Result<[[u32; 8]; 3], String> {
    let loaded = load_program(source)?;
    let worker = worker::Worker::new();
    let unrolled_blake = BlakeMode::Compression;
    let bridge_blake = BlakeMode::Compression;
    let final_blake = BlakeMode::Compression;
    let mut hashes = [[0; 8]; 3];
    for (i, hash) in hashes.iter_mut().enumerate() {
        let expected = expected_chain_end_params(
            ProofTarget::RecursionUnified,
            mode,
            i + 3,
            unrolled_blake.tag(),
            bridge_blake.tag(),
            final_blake.tag(),
            &mut recomputed_end_params(&loaded, &worker, mode),
        )?;
        *hash = rebuild_chain(&expected)?.hash();
    }
    Ok(hashes)
}

/// Complete caller-trusted verification records for one program and mode.
/// Like the binary itself, this file is a trusted input.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TrustedParams {
    schema_version: u32,
    program_hash: [u8; 32],
    soundness_mode: SoundnessMode,
    programs: Vec<TrustedProgramParams>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct TrustedProgramParams {
    program_hash: [u8; 32],
    machine: SetupMachine,
    setups: Setups,
    exit_pc: u32,
    end_params: [u32; 8],
}

fn compute_trusted_program_params(
    bin: &[u32],
    text: &[u32],
    machine: SetupMachine,
    mode: SoundnessMode,
    worker: &worker::Worker,
    commit: &mut setups::program_setups::SetupCommitter<'_>,
) -> Result<TrustedProgramParams, String> {
    let start = Instant::now();
    let setups = recompute_program_setups_with_committer(bin, text, machine, mode, worker, commit);
    let exit_pc = find_binary_exit_point(bin)?;
    let end_params = compute_end_params(&setups, exit_pc);
    log::info!(
        "computed trusted {machine:?} params in {} ms",
        elapsed_ms(start)
    );
    Ok(TrustedProgramParams {
        program_hash: fsv_digest(bin, text).0,
        machine,
        setups,
        exit_pc,
        end_params,
    })
}

/// Compute trusted records from the user program through `target`, excluding the L1 wrap.
pub fn compute_trusted_params(
    source: &ProgramSource,
    soundness_mode: SoundnessMode,
    target: ProofTarget,
    backend: ProverBackend,
) -> Result<TrustedParams, String> {
    assert_target_mode(target, soundness_mode);
    let loaded = load_program(source)?;
    let worker = worker::Worker::new();
    let target = target.min(ProofTarget::Compression);
    let fsv = FsvPrograms::load(target, soundness_mode);
    #[cfg(feature = "gpu")]
    let mut gpu = (backend == ProverBackend::Gpu)
        .then(gpu_execution_prover::trusted_params::TrustedSetupCommitter::new);
    #[cfg(not(feature = "gpu"))]
    if backend == ProverBackend::Gpu {
        return Err("GPU trusted params require the `gpu` feature".into());
    }
    let mut programs = Vec::new();
    for (_, registration) in pipeline_registrations(&loaded, target, soundness_mode, None, &fsv) {
        for profile in registration.profiles {
            let machine = match (registration.kind, registration.machine, profile) {
                (ExecutionKind::Unrolled, MachineType::FullUnsigned, ProofProfile::Standard) => {
                    SetupMachine::UnrolledFullUnsigned
                }
                (ExecutionKind::Unrolled, MachineType::Reduced, ProofProfile::Standard) => {
                    SetupMachine::UnrolledReduced
                }
                (ExecutionKind::Unified, _, ProofProfile::Standard) => SetupMachine::Unified,
                (ExecutionKind::Unified, _, ProofProfile::Compression) => {
                    SetupMachine::Compression(CompressionProfile::Step)
                }
                (ExecutionKind::Unified22, _, ProofProfile::CompressionFinal) => {
                    SetupMachine::Compression(CompressionProfile::Final)
                }
                other => unreachable!("unsupported trusted params registration {other:?}"),
            };
            #[cfg(feature = "gpu")]
            let record = if let Some(gpu) = gpu.as_mut() {
                gpu.reset_peak();
                let record = compute_trusted_program_params(
                    &registration.bin,
                    &registration.text,
                    machine,
                    soundness_mode,
                    &worker,
                    &mut |config, setup| gpu.commit(config, setup),
                )?;
                log::info!(
                    "trusted {machine:?} record peak device allocation: {} bytes",
                    gpu.peak()
                );
                record
            } else {
                compute_trusted_program_params(
                    &registration.bin,
                    &registration.text,
                    machine,
                    soundness_mode,
                    &worker,
                    &mut setups::program_setups::cpu_setup_committer(&worker),
                )?
            };
            #[cfg(not(feature = "gpu"))]
            let record = compute_trusted_program_params(
                &registration.bin,
                &registration.text,
                machine,
                soundness_mode,
                &worker,
                &mut setups::program_setups::cpu_setup_committer(&worker),
            )?;
            programs.push(record);
        }
    }
    Ok(TrustedParams {
        schema_version: 1,
        program_hash: fsv_digest(&loaded.bin_u32, &loaded.text_u32).0,
        soundness_mode,
        programs,
    })
}

impl TrustedParams {
    fn validate(&self, loaded: &LoadedProgram, expected_mode: SoundnessMode) {
        assert_eq!(self.schema_version, 1, "unsupported trusted params schema");
        assert_eq!(
            self.program_hash,
            fsv_digest(&loaded.bin_u32, &loaded.text_u32).0,
            "trusted params program hash does not match the supplied program"
        );
        assert_eq!(
            self.soundness_mode, expected_mode,
            "trusted params soundness mode does not match the requested mode"
        );
    }

    fn resolve(&self, program: ChainProgram) -> &TrustedProgramParams {
        let (hash, machine) = match program {
            ChainProgram::User => (self.program_hash, SetupMachine::UnrolledFullUnsigned),
            ChainProgram::Fsv(program, profile, blake, machine) => {
                let guest = load_fsv_exact(
                    fsv_dir(),
                    &FsvDescriptor {
                        soundness_mode: self.soundness_mode,
                        program,
                        profile,
                        blake,
                    },
                );
                (fsv_digest(guest.bin(), guest.text()).0, machine)
            }
        };
        let mut entries = self
            .programs
            .iter()
            .filter(|record| record.machine == machine && record.program_hash == hash);
        let record = entries
            .next()
            .expect("trusted params have no record for this program hash and machine");
        assert!(entries.next().is_none(), "duplicate trusted program params");
        record
    }
}

/// Verify with a caller-supplied acceptance mode, before loading the source or setups.
pub fn verify_artifact_in_mode(
    artifact: &ProofArtifact,
    source: &ProgramSource,
    expected_mode: SoundnessMode,
) -> Result<[u32; 16], String> {
    verify_artifact_with_trusted_params_in_mode(artifact, source, expected_mode, None)
}

/// Verify using an optional caller-trusted parameter file. Without it, derive
/// the trusted parameters from the supplied binary and checked-in FSVs.
pub fn verify_artifact_with_trusted_params_in_mode(
    artifact: &ProofArtifact,
    source: &ProgramSource,
    expected_mode: SoundnessMode,
    trusted: Option<&TrustedParams>,
) -> Result<[u32; 16], String> {
    artifact.validate_expected_mode(expected_mode)?;
    validate_artifact_envelope(artifact)?;
    let loaded = load_and_validate_program(source, artifact)?;
    verify_accepted_artifact(artifact, &loaded, expected_mode, trusted)
}

/// [`verify_artifact_in_mode`] after the acceptance check, with the artifact's program already
/// loaded and checked against it.
fn verify_accepted_artifact(
    artifact: &ProofArtifact,
    loaded: &LoadedProgram,
    expected_mode: SoundnessMode,
    trusted: Option<&TrustedParams>,
) -> Result<[u32; 16], String> {
    validate_artifact_chain(artifact)?;

    // Trusted per-layer end-params, recomputed from the supplied program and
    // the checked-in fsv binaries (see the program-binding module comment
    // below). Cross-check the artifact's claimed history entry by entry
    // (stronger than internal consistency), then bind the verifier's
    // authenticated output chain to the trusted chain.
    let worker = trusted.is_none().then(worker::Worker::new);
    if let Some(trusted) = trusted {
        trusted.validate(loaded, expected_mode);
    }
    let mut recompute = worker
        .as_ref()
        .map(|worker| recomputed_end_params(loaded, worker, expected_mode));
    let mut trusted_setups = None;
    let expected = expected_chain_end_params(
        artifact.target,
        artifact.soundness_mode,
        artifact.chain_end_params.len(),
        &artifact.blake_unrolled,
        &artifact.blake_bridge,
        &artifact.blake_final,
        &mut |program| match trusted {
            Some(trusted) => {
                let record = trusted.resolve(program);
                trusted_setups = Some(&record.setups);
                Ok(record.end_params)
            }
            None => recompute.as_mut().unwrap()(program),
        },
    )?;
    verify_against_chain(artifact, &expected, expected_mode, trusted_setups)
}

fn verify_against_chain(
    artifact: &ProofArtifact,
    expected: &[[u32; 8]],
    expected_mode: SoundnessMode,
    trusted_setups: Option<&Setups>,
) -> Result<[u32; 16], String> {
    if expected != artifact.chain_end_params {
        return Err(
            "artifact chain_end_params do not match the trusted per-layer end-params".to_string(),
        );
    }
    if let Some(trusted_setups) = trusted_setups {
        assert_eq!(
            &artifact.setups, trusted_setups,
            "artifact final-layer setups do not match trusted params"
        );
    }
    let expected_chain = rebuild_chain(expected)?;

    // The claim shape decides the statement flavor: a single layer is a
    // base-layer statement (no recursion chain in the stream).
    let is_base = expected.len() == 1;
    let output = match artifact.target {
        ProofTarget::Base | ProofTarget::RecursionUnrolled => native_verify_unrolled_in_mode(
            build_unrolled_stream(
                &artifact.setups,
                &artifact.proof,
                verifier_common::BLAKE_MODE,
            ),
            is_base,
            expected_mode,
        ),
        ProofTarget::RecursionUnified => native_verify_unified_in_mode(
            build_unified_stream(
                &artifact.setups,
                &artifact.proof,
                verifier_common::BLAKE_MODE,
            ),
            is_base,
            expected_mode,
        ),
        ProofTarget::Compression | ProofTarget::L1 => native_verify_unified_compression_in_mode(
            build_unified_stream(
                &artifact.setups,
                &artifact.proof,
                verifier_common::BLAKE_MODE,
            ),
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
enum SetupMachine {
    /// Unrolled machine, full-unsigned ISA (base user programs).
    UnrolledFullUnsigned,
    /// Unrolled machine, reduced ISA (fsv unrolled verifier layers).
    UnrolledReduced,
    /// Unified reduced machine (bridge + final layers).
    Unified,
    Compression(CompressionProfile),
}

/// Recompute the per-program `Setups` map for `(binary, machine)` WITHOUT
/// proving, byte-identical to what the provers produce (see
/// `setups::program_setups`).
fn recompute_program_setups(
    bin: &[u32],
    text: &[u32],
    machine: SetupMachine,
    soundness_mode: prover::definitions::SoundnessMode,
    worker: &worker::Worker,
) -> Setups {
    recompute_program_setups_with_committer(
        bin,
        text,
        machine,
        soundness_mode,
        worker,
        &mut setups::program_setups::cpu_setup_committer(worker),
    )
}

fn recompute_program_setups_with_committer(
    bin: &[u32],
    text: &[u32],
    machine: SetupMachine,
    soundness_mode: SoundnessMode,
    worker: &worker::Worker,
    commit: &mut setups::program_setups::SetupCommitter<'_>,
) -> Setups {
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
    let security_level = COMPILED_SECURITY_LEVEL.to_prover();
    match machine {
        SetupMachine::UnrolledFullUnsigned => {
            compute_unrolled_program_setups_in_mode::<FullUnsignedConfig, Global>(
                &padded_bin,
                &padded_text,
                use_caches,
                security_level,
                soundness_mode,
                worker,
                commit,
            )
        }
        SetupMachine::UnrolledReduced => {
            compute_unrolled_program_setups_in_mode::<ReducedConfig, Global>(
                &padded_bin,
                &padded_text,
                use_caches,
                security_level,
                soundness_mode,
                worker,
                commit,
            )
        }
        SetupMachine::Compression(profile) => {
            prover::definitions::ProverConfigProfile::Compression.assert_supports(soundness_mode);
            setups::program_setups::compute_unified_program_setups_for_profile::<Global>(
                &padded_bin,
                &padded_text,
                use_caches,
                security_level,
                profile.proof_profile(),
                soundness_mode,
                worker,
                commit,
            )
        }
        SetupMachine::Unified => compute_unified_program_setups_in_mode::<Global>(
            &padded_bin,
            &padded_text,
            use_caches,
            security_level,
            soundness_mode,
            worker,
            commit,
        ),
    }
}

/// Keep mode identity even when current base caps coincide across modes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct TrustedEndParamsKey {
    machine: SetupMachine,
    soundness_mode: prover::definitions::SoundnessMode,
    program_hash: [u8; 32],
}

/// Trusted standard end params keyed by machine, soundness mode and exact binary/text identity.
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
    soundness_mode: prover::definitions::SoundnessMode,
) -> TrustedEndParamsKey {
    TrustedEndParamsKey {
        machine,
        soundness_mode,
        program_hash: fsv_digest(bin, text).0,
    }
}

/// Mode-explicit standard setup reconstruction. Special-profile setups need their own producer.
fn trusted_end_params_in_mode(
    bin: &[u32],
    text: &[u32],
    machine: SetupMachine,
    soundness_mode: prover::definitions::SoundnessMode,
    worker: &worker::Worker,
) -> Result<[u32; 8], String> {
    let key = trusted_end_params_key(machine, bin, text, soundness_mode);
    let cache = trusted_end_params_cache();
    if let Some(end_params) = cache.lock().unwrap().get(&key) {
        return Ok(*end_params);
    }

    let start = Instant::now();
    let setups = recompute_program_setups(bin, text, machine, soundness_mode, worker);
    let exit_pc = find_binary_exit_point(bin)?;
    let end_params = compute_end_params(&setups, exit_pc);
    log::info!("recomputed {machine:?} setups in {} ms", elapsed_ms(start));
    cache.lock().unwrap().insert(key, end_params);
    Ok(end_params)
}

/// Read a fixed stage-mode tag from an untrusted artifact.
fn parse_blake_tag(tag: &str) -> Result<BlakeMode, String> {
    if tag != BlakeMode::Compression.tag() {
        return Err(format!(
            "artifact Blake mode {tag:?} does not match the fixed pipeline mode"
        ));
    }
    Ok(BlakeMode::Compression)
}

/// The unrolled prefix excludes the fixed Standard and compression tails.
fn claimed_unrolled_layers(
    target: ProofTarget,
    mode: SoundnessMode,
    n: usize,
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
        ProofTarget::Compression | ProofTarget::L1 => 3 + compression_schedule(mode).len(),
    };
    n.checked_sub(tail)
        .ok_or_else(|| format!("{target:?} artifact must claim at least {tail} layers, got {n}"))
}

fn chain_unrolled_layers(artifact: &ProofArtifact) -> Result<usize, String> {
    claimed_unrolled_layers(
        artifact.target,
        artifact.soundness_mode,
        artifact.chain_end_params.len(),
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
    soundness_mode: prover::definitions::SoundnessMode,
) -> impl FnMut(ChainProgram) -> Result<[u32; 8], String> + 'a {
    let fsv_dir = fsv_dir();
    move |program| match program {
        ChainProgram::User => trusted_end_params_in_mode(
            &loaded.bin_u32,
            &loaded.text_u32,
            SetupMachine::UnrolledFullUnsigned,
            soundness_mode,
            worker,
        ),
        ChainProgram::Fsv(program, profile, blake, setup_machine) => {
            let descriptor = FsvDescriptor {
                profile,
                ..FsvDescriptor::new(soundness_mode, program, blake)
            };
            let guest = load_fsv_exact(&fsv_dir, &descriptor);
            trusted_end_params_in_mode(
                guest.bin(),
                guest.text(),
                setup_machine,
                soundness_mode,
                worker,
            )
        }
    }
}

/// Reconstruct the pipeline's per-layer `end_params` from trusted inputs only, which
/// `end_params` supplies per chain program. The artifact contributes only the CLAIM shape:
/// target, number of chain entries, and blake tags.
fn expected_chain_end_params(
    target: ProofTarget,
    mode: SoundnessMode,
    n: usize,
    blake_unrolled: &str,
    blake_bridge: &str,
    blake_final: &str,
    end_params: &mut dyn FnMut(ChainProgram) -> Result<[u32; 8], String>,
) -> Result<Vec<[u32; 8]>, String> {
    let unrolled_layers = claimed_unrolled_layers(target, mode, n)?;

    let mut expected = Vec::with_capacity(n);
    expected.push(end_params(ChainProgram::User)?);

    if target == ProofTarget::Base {
        return Ok(expected);
    }

    let unrolled_blake = parse_blake_tag(blake_unrolled)?;

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
    let bridge_blake = parse_blake_tag(blake_bridge)?;
    expected.push(end_params(ChainProgram::Fsv(
        bridge_program,
        FsvProfile::Standard,
        bridge_blake,
        SetupMachine::Unified,
    ))?);

    // Final: fsv_unified_recursion_layer on the unified machine.
    let final_blake = parse_blake_tag(blake_final)?;
    expected.push(end_params(ChainProgram::Fsv(
        FsvProgram::UnifiedRecursionLayer,
        FsvProfile::Standard,
        final_blake,
        SetupMachine::Unified,
    ))?);

    if target >= ProofTarget::Compression {
        for &(role, profile, _) in compression_schedule(mode) {
            let spec = compression_stage(role, profile);
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

/// Load `source` and check it is the artifact's program. Callers have accepted the artifact
/// ([`ProofArtifact::validate_expected_mode`]).
fn load_and_validate_program(
    source: &ProgramSource,
    artifact: &ProofArtifact,
) -> Result<LoadedProgram, String> {
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
mod compression_tests;

#[cfg(test)]
mod l1_tests;

/// Recursion-binding tests, adapted to `FsvRecursionChain` (no proving
/// required).
#[cfg(test)]
mod recursion_binding_tests {
    use super::*;

    #[test]
    fn cpu_unified_verification_chain_binds_program() {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../examples/hashed_fibonacci");
        let [first, second] = ["app_plain.bin", "app_blake2_with_compression.bin"].map(|name| {
            unified_verification_chain_hashes_in_mode(
                &ProgramSource::legacy_binaries_from_bin(dir.join(name)),
                SoundnessMode::PessimisticConjecture,
            )
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

/// The deferred-scope boundary of the wrap target: ethproofs is rejected before any guest, input
/// or backend is touched; pessimistic L1 entries pass it unchanged.
#[cfg(test)]
mod l1_capability_tests {
    use super::*;
    use prover::definitions::SoundnessMode;

    const L1_TARGETS: [ProofTarget; 1] = [ProofTarget::L1];

    fn missing() -> ProgramSource {
        let source = ProgramSource::elf("must-not-read-l1-capability-input.elf");
        assert!(matches!(&source, ProgramSource::Elf(path) if !path.exists()));
        source
    }

    /// The profile assert's message for `entry`, which must panic.
    fn refusal<T>(entry: impl FnOnce() -> T) -> String {
        let payload = std::panic::catch_unwind(std::panic::AssertUnwindSafe(entry))
            .map(|_| ())
            .expect_err("ethproofs L1 entries must be rejected");
        payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .unwrap_or_default()
            .to_owned()
    }

    /// CPU and GPU entries: the rejection precedes guest loading, the (missing) source and
    /// backend construction, so no CUDA is reached even in a `gpu` build.
    #[test]
    fn ethproofs_l1_prover_entries_reject_before_inputs_and_backends() {
        for target in L1_TARGETS {
            for backend in [ProverBackend::Cpu, ProverBackend::Gpu] {
                let config = ProgramProverConfig {
                    target,
                    backend,
                    soundness_mode: SoundnessMode::EthproofsSoundnessCalc,
                    ..Default::default()
                };
                let error = refusal(|| ProgramProver::new(missing(), config.clone()));
                assert!(
                    error.contains("supports only the pessimistic-conjecture soundness mode"),
                    "{target:?} on {backend:?}: {error}"
                );
            }
        }
    }
}
