use super::factory::{PreparedCircuit, SyntheticInputFactory};
use super::probe::{drain, input_transfers, preset_setup_reduction_layers, schedule_proof_inputs};
use crate::precomputations::l1_wrap::L1WrapPrecomputed;
use crate::upstream::{
    l1_wrap_2p21, CommitmentMode, CpuGKRSetup, L1WrapSetup, MerkleTreeCapVarLength, ProofProfile,
    ProverConfig, SecurityLevel,
};
use crate::A;
use era_cudart::result::CudaResult;
use era_cudart_sys::CudaError;
use fft::GoodAllocator;
use gpu_circuit_prover::config::prover_config;
use gpu_circuit_prover::l1_wrap::{L1Proof, L1WrapInputs, L1_WRAP_NTT_LOG_MAX_DOMAIN};
use gpu_circuit_prover::proof::memory_policy::{presets, PartialTreePolicy};
use gpu_circuit_prover::proof::merged_commitment::{
    commit_merged_from_transfers, GpuGKRMergedCommitTransfer,
};
use gpu_core::allocator::tracker::AllocationDirection;
use gpu_gkr::proth120::backward::preflight_dr_tail_resources_pr;
use gpu_gkr::setup::GpuGKRSetupTransfer;
use gpu_prover_context::{AllocationMode, ProverContext, ProverContextConfig};
use gpu_trace::witness::circuit_type::{CircuitType, UnrolledCircuitType};
use gpu_trace::witness::trace_unrolled::{InitsAndTeardownsTraceHost, UnrolledUnifiedTraceHost};
use serde::{Deserialize, Serialize};
use sha3::{Digest, Keccak256};
use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use std::sync::{Arc, OnceLock};

pub const SCHEMA_VERSION: u32 = 1;
pub const WRAP_CANDIDATES_GIB: [usize; 2] = [21, 30];
pub const WRAP_QUALIFYING_GIB: usize = 30;
pub const FEEDER_CANDIDATES_GIB: [usize; 5] = [21, 30, 40, 48, 64];
const FINAL_TRACE_SIZE_LOG_2: u32 = 4;
const WRAP_FINAL_TRACE_SIZE_LOG_2: u32 = l1_wrap_2p21::EXPLICIT_OUTPUT_LOG2 as u32;
const SECURITY_LEVEL: SecurityLevel = SecurityLevel::Sec100;
const UNIFIED22: CircuitType = CircuitType::Unrolled(UnrolledCircuitType::Unified22);
const INITS_AND_TEARDOWNS: CircuitType =
    CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Family {
    Wrap,
    Feeder,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Stage {
    Wrap,
    FeederCommit,
    FeederProof,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Follower {
    StandardIt,
    Feeder,
    Wrap,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Direction {
    Ascending,
    Descending,
}

impl Family {
    pub const ALL: [Family; 2] = [Family::Wrap, Family::Feeder];

    pub fn name(self) -> &'static str {
        match self {
            Family::Wrap => "wrap",
            Family::Feeder => "feeder",
        }
    }

    pub fn candidates_gib(self) -> &'static [usize] {
        match self {
            Family::Wrap => &WRAP_CANDIDATES_GIB,
            Family::Feeder => &FEEDER_CANDIDATES_GIB,
        }
    }

    pub fn stages(self) -> &'static [Stage] {
        match self {
            Family::Wrap => &[Stage::Wrap],
            Family::Feeder => &[Stage::FeederCommit, Stage::FeederProof],
        }
    }
}

impl Stage {
    pub fn family(self) -> Family {
        match self {
            Stage::Wrap => Family::Wrap,
            Stage::FeederCommit | Stage::FeederProof => Family::Feeder,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Stage::Wrap => "wrap",
            Stage::FeederCommit => "feeder_commit",
            Stage::FeederProof => "feeder_proof",
        }
    }
}

impl Stage {
    fn target(self) -> (CircuitType, ProofProfile, u32) {
        match self {
            Stage::Wrap => (CircuitType::L1Wrap21, ProofProfile::L1Wrap, 21),
            Stage::FeederCommit | Stage::FeederProof => (UNIFIED22, ProofProfile::L1Feeder, 22),
        }
    }

    /// The stage's (LDE factor, cap size, per-round (queries, PoW)) from its config.
    fn geometry(self) -> Option<(usize, usize, Vec<(usize, u32)>)> {
        let config = match self {
            Stage::Wrap => {
                ProofProfile::L1Wrap.prover_config(l1_wrap_2p21::TRACE_LEN_LOG2, SECURITY_LEVEL)
            }
            Stage::FeederCommit | Stage::FeederProof => feeder_config(),
        };
        let schedule = &config.whir_schedule;
        let rounds = schedule
            .whir_queries_schedule
            .iter()
            .copied()
            .zip(schedule.whir_pow_schedule.iter().copied())
            .collect();
        Some((config.lde_factor, config.cap_size, rounds))
    }

    fn policy(self, arena_bytes: usize) -> String {
        match self {
            Stage::Wrap => format!(
                "{:?}",
                presets::policy(CircuitType::L1Wrap21, ProofProfile::L1Wrap, arena_bytes)
            ),
            Stage::FeederCommit => format!(
                "{:?}",
                presets::merged_commit_strategy(UNIFIED22, ProofProfile::L1Feeder)
            ),
            Stage::FeederProof => format!(
                "{:?}",
                presets::policy(UNIFIED22, ProofProfile::L1Feeder, arena_bytes)
            ),
        }
    }
}

const FAILED_PHASES: [&str; 6] = [
    "setup_initialization",
    "prerequisite_commit",
    "target_inputs",
    "follower_inputs",
    "target_stage",
    "target_finish",
];

impl Follower {
    pub const ALL: [Follower; 3] = [Follower::StandardIt, Follower::Feeder, Follower::Wrap];

    pub fn name(self) -> &'static str {
        match self {
            Follower::StandardIt => "standard_it",
            Follower::Feeder => "feeder",
            Follower::Wrap => "wrap",
        }
    }

    fn identity(self) -> (CircuitType, ProofProfile) {
        match self {
            Follower::StandardIt => (INITS_AND_TEARDOWNS, ProofProfile::Standard),
            Follower::Feeder => (UNIFIED22, ProofProfile::L1Feeder),
            Follower::Wrap => (CircuitType::L1Wrap21, ProofProfile::L1Wrap),
        }
    }
}

impl Direction {
    pub const ALL: [Direction; 2] = [Direction::Ascending, Direction::Descending];

    pub fn name(self) -> &'static str {
        match self {
            Direction::Ascending => "ascending",
            Direction::Descending => "descending",
        }
    }

    fn allocation(self) -> AllocationDirection {
        match self {
            Direction::Ascending => AllocationDirection::Ascending,
            Direction::Descending => AllocationDirection::Descending,
        }
    }

    fn opposite(self) -> AllocationDirection {
        match self {
            Direction::Ascending => AllocationDirection::Descending,
            Direction::Descending => AllocationDirection::Ascending,
        }
    }
}

pub fn case_key(
    arena_gib: usize,
    stage: Stage,
    follower: Follower,
    direction: Direction,
) -> String {
    format!(
        "{}-{arena_gib}-{}-{}-{}",
        stage.family().name(),
        stage.name(),
        follower.name(),
        direction.name()
    )
}

pub fn candidate_case_keys(family: Family, arena_gib: usize) -> Vec<String> {
    family
        .stages()
        .iter()
        .flat_map(|&stage| {
            Follower::ALL.into_iter().flat_map(move |follower| {
                Direction::ALL
                    .into_iter()
                    .map(move |direction| case_key(arena_gib, stage, follower, direction))
            })
        })
        .collect()
}

#[derive(Clone, Debug)]
pub struct CapacityCase {
    pub stage: Stage,
    pub arena_gib: usize,
    pub follower: Follower,
    pub direction: Direction,
    pub row_path: PathBuf,
    pub partial_trees: Option<u32>,
}

fn required_env(name: &str) -> String {
    std::env::var(name).unwrap_or_else(|_| panic!("{name} is not set"))
}

impl CapacityCase {
    pub fn from_env(stage: Stage) -> Self {
        let arena = required_env("M8_CAPACITY_ARENA_GIB");
        let arena_gib: usize = arena
            .parse()
            .unwrap_or_else(|_| panic!("M8_CAPACITY_ARENA_GIB is not an integer: {arena}"));
        assert!(
            stage.family().candidates_gib().contains(&arena_gib)
                || (stage.family() == Family::Feeder && is_feeder_bracket_arena(arena_gib)),
            "M8_CAPACITY_ARENA_GIB {arena_gib} is not a {} candidate",
            stage.family().name()
        );
        let follower = required_env("M8_CAPACITY_FOLLOWER");
        let follower = Follower::ALL
            .into_iter()
            .find(|candidate| candidate.name() == follower)
            .unwrap_or_else(|| panic!("M8_CAPACITY_FOLLOWER is not a follower: {follower}"));
        let direction = required_env("M8_CAPACITY_DIRECTION");
        let direction = Direction::ALL
            .into_iter()
            .find(|candidate| candidate.name() == direction)
            .unwrap_or_else(|| panic!("M8_CAPACITY_DIRECTION is not a direction: {direction}"));
        let row_path = PathBuf::from(required_env("M8_CAPACITY_ROW"));
        assert!(
            !row_path.exists(),
            "M8_CAPACITY_ROW already exists: {}",
            row_path.display()
        );
        let partial_trees = std::env::var("M8_CAPACITY_PARTIAL_TREES")
            .ok()
            .map(|depth| {
                let depth: u32 = depth.parse().unwrap_or_else(|_| {
                    panic!("M8_CAPACITY_PARTIAL_TREES is not an integer: {depth}")
                });
                gpu_trace::trace::holder::assert_partial_tree_reduction_layers(depth);
                depth
            });
        Self {
            stage,
            arena_gib,
            follower,
            direction,
            row_path,
            partial_trees,
        }
    }

    pub fn partial_trees(&self, circuit: CircuitType, profile: ProofProfile) -> PartialTreePolicy {
        self.partial_trees
            .map(PartialTreePolicy::uniform)
            .unwrap_or_else(|| presets::partial_trees(circuit, profile))
    }

    pub fn key(&self) -> String {
        case_key(self.arena_gib, self.stage, self.follower, self.direction)
    }

    pub fn needs_wrap_source(&self) -> bool {
        self.stage == Stage::Wrap || self.follower == Follower::Wrap
    }

    pub fn arena_bytes(&self) -> usize {
        self.arena_gib << 30
    }
}

/// The active wrap, whether it is this row's target or its resident follower.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WrapIdentity {
    pub trace_len_log2: u32,
    pub lde_factor: usize,
    pub tree_cap_size: usize,
    pub queries_and_pow: Vec<(usize, u32)>,
    pub rom_bytes: usize,
    pub rom_words: usize,
    pub rom_second_word_bits: usize,
    pub layout_keccak256: String,
}

impl WrapIdentity {
    pub fn current() -> &'static Self {
        static IDENTITY: OnceLock<WrapIdentity> = OnceLock::new();
        IDENTITY.get_or_init(|| {
            let (lde_factor, tree_cap_size, queries_and_pow) = Stage::Wrap.geometry().unwrap();
            Self {
                trace_len_log2: l1_wrap_2p21::TRACE_LEN_LOG2 as u32,
                lde_factor,
                tree_cap_size,
                queries_and_pow,
                rom_bytes: l1_wrap_2p21::ROM.byte_size(),
                rom_words: l1_wrap_2p21::ROM.word_size(),
                rom_second_word_bits: l1_wrap_2p21::ROM.second_word_bits(),
                layout_keccak256: Keccak256::digest(l1_wrap_2p21::LAYOUT_JSON.as_bytes())
                    .iter()
                    .map(|byte| format!("{byte:02x}"))
                    .collect(),
            }
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapacityRow {
    pub schema_version: u32,
    pub case: String,
    pub revision: String,
    pub binary_digest: String,
    pub stage: Stage,
    pub target_circuit: String,
    pub target_profile: String,
    pub trace_len_log2: u32,
    pub policy: String,
    pub arena_bytes: usize,
    pub direction: Direction,
    pub follower: Follower,
    pub follower_circuit: String,
    pub follower_profile: String,
    pub target_input_bytes: Option<usize>,
    pub follower_input_bytes: Option<usize>,
    pub initialization_peak_bytes: Option<usize>,
    pub prerequisite_peak_bytes: Option<usize>,
    pub measured_peak_bytes: Option<usize>,
    pub output_fingerprint: Option<String>,
    #[serde(default)]
    pub partial_trees: Option<u32>,
    #[serde(default)]
    pub lde_factor: Option<usize>,
    #[serde(default)]
    pub tree_cap_size: Option<usize>,
    #[serde(default)]
    pub queries_and_pow: Option<Vec<(usize, u32)>>,
    #[serde(default)]
    pub wrap_identity: Option<WrapIdentity>,
    #[serde(default)]
    pub proof_equals_reference: Option<bool>,
    pub vmhwm_kib: Option<u64>,
    pub fits: bool,
    pub failure_kind: Option<String>,
    pub failed_phase: Option<String>,
}

#[derive(Deserialize)]
struct WrapBundle {
    wrap: String,
    proof: L1Proof,
    commitment_mode: CommitmentMode,
}

/// Fields from the manifest-validated `l1_bundle.json`, compared separately as
/// the serialized bytes of their types: the proof carries integers beyond
/// `u64`, which `serde_json::Value` cannot hold exactly.
#[derive(Debug, Deserialize)]
#[serde(from = "WrapBundle")]
pub struct WrapReference {
    pub wrap: String,
    pub proof_json: Vec<u8>,
    pub commitment_mode_json: Vec<u8>,
}

impl From<WrapBundle> for WrapReference {
    fn from(bundle: WrapBundle) -> Self {
        Self {
            wrap: bundle.wrap,
            proof_json: serde_json::to_vec(&bundle.proof).expect("L1 wrap proof serializes"),
            commitment_mode_json: serde_json::to_vec(&bundle.commitment_mode)
                .expect("L1 wrap commitment mode serializes"),
        }
    }
}

impl WrapReference {
    fn matches(&self, proof_json: &[u8], commitment_mode_json: &[u8]) -> bool {
        self.wrap == "2p21"
            && self.proof_json == proof_json
            && self.commitment_mode_json == commitment_mode_json
    }
}

pub struct WrapSource<'s, B: GoodAllocator> {
    pub setup: &'s L1WrapSetup,
    pub tracing_data: &'s UnrolledUnifiedTraceHost<B>,
    pub inits_and_teardowns: &'s InitsAndTeardownsTraceHost<B>,
    pub commitment_mode: CommitmentMode,
    pub reference: &'s WrapReference,
}

fn output_digest(bytes: Vec<u8>) -> String {
    if let Ok(path) = std::env::var("M8_CAPACITY_OUTPUT_BYTES") {
        let path = PathBuf::from(path);
        assert!(
            !path.exists(),
            "M8_CAPACITY_OUTPUT_BYTES already exists: {}",
            path.display()
        );
        std::fs::write(&path, &bytes).unwrap_or_else(|error| {
            panic!("M8_CAPACITY_OUTPUT_BYTES write {}: {error}", path.display())
        });
    }
    digest(&bytes)
}

fn revision() -> String {
    let output = std::process::Command::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("L1 capacity revision: git rev-parse");
    assert!(
        output.status.success(),
        "L1 capacity revision: git rev-parse failed"
    );
    String::from_utf8(output.stdout)
        .expect("L1 capacity revision is UTF-8")
        .trim()
        .to_string()
}

fn digest(bytes: &[u8]) -> String {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    bytes.hash(&mut hasher);
    format!("{:016x}", hasher.finish())
}

fn binary_digest() -> String {
    let path = std::env::current_exe().expect("L1 capacity binary path");
    digest(&std::fs::read(&path).expect("L1 capacity binary read"))
}

fn vmhwm_kib() -> Option<u64> {
    std::fs::read_to_string("/proc/self/status")
        .ok()?
        .lines()
        .find_map(|line| line.strip_prefix("VmHWM:"))
        .and_then(|value| value.trim().trim_end_matches("kB").trim().parse().ok())
}

fn synthetic_caps(config: &ProverConfig) -> Vec<MerkleTreeCapVarLength> {
    assert!(
        config.cap_size.is_multiple_of(config.lde_factor),
        "synthetic follower caps require cap_size divisible by lde_factor"
    );
    let cap = MerkleTreeCapVarLength {
        cap: vec![[0u32; 8]; config.cap_size / config.lde_factor],
    };
    vec![cap; config.lde_factor]
}

fn capacity_context(arena_bytes: usize) -> ProverContext {
    let defaults = ProverContextConfig::default();
    let blocks = arena_bytes >> defaults.allocator_block_log_size;
    let context = ProverContext::new(&ProverContextConfig {
        device_allocation_blocks_count: Some(blocks),
        inputs_reserve_bytes: presets::INPUTS_RESERVE_BYTES,
        proth120_ntt_log_max_domain: Some(L1_WRAP_NTT_LOG_MAX_DOMAIN),
        ..defaults
    })
    .expect("L1 capacity context");
    assert_eq!(
        context.get_mem_size(),
        arena_bytes,
        "L1 capacity arena differs from the requested candidate"
    );
    context
}

fn step<T>(
    phase: &'static str,
    context: &ProverContext,
    result: CudaResult<T>,
) -> Result<T, &'static str> {
    match result {
        Ok(value) => Ok(value),
        Err(CudaError::ErrorMemoryAllocation)
            if era_cudart::error::get_last_error() == CudaError::Success =>
        {
            drain(context).expect("L1 capacity drain after an allocation OOM");
            Err(phase)
        }
        Err(error) => panic!("L1 capacity case failed in {phase}: {error:?}"),
    }
}

fn clone_setup(setup: &L1WrapSetup) -> L1WrapSetup {
    L1WrapSetup {
        circuit: setup.circuit.clone(),
        table_driver: setup.table_driver.clone(),
        decoder_table: setup.decoder_table.clone(),
        setup: CpuGKRSetup {
            hypercube_evals: setup.setup.hypercube_evals.clone(),
        },
        trace_len: setup.trace_len,
        rom: setup.rom,
    }
}

fn feeder_config() -> ProverConfig {
    prover_config(UNIFIED22, ProofProfile::L1Feeder, SECURITY_LEVEL).unwrap()
}

type FollowerInputs<'a, B> = (
    Option<gpu_circuit_prover::proof::inputs::GpuGKRProofTransfer<'a, A>>,
    Option<L1WrapInputs<'a, B>>,
);

pub fn run_case<B: GoodAllocator>(
    case: &CapacityCase,
    wrap: Option<WrapSource<'_, B>>,
) -> CapacityRow {
    assert_eq!(
        case.needs_wrap_source(),
        wrap.is_some(),
        "L1 capacity case {} requires a wrap source exactly when the target or follower is L1Wrap",
        case.key()
    );
    if let Some(source) = &wrap {
        assert_eq!(
            source.reference.wrap, "2p21",
            "L1 capacity reference wrap identity"
        );
        assert_eq!(
            source.setup.rom,
            l1_wrap_2p21::ROM,
            "L1 capacity source ROM"
        );
        assert_eq!(
            source.setup.trace_len,
            1 << l1_wrap_2p21::TRACE_LEN_LOG2,
            "L1 capacity source trace length"
        );
        // The recorded layout hash must describe the artifact actually compiled below.
        assert!(
            serde_json::to_vec(&source.setup.circuit)
                .expect("L1 capacity source artifact serializes")
                == serde_json::to_vec(&l1_wrap_2p21::circuit_artifact())
                    .expect("L1 capacity active artifact serializes"),
            "L1 capacity source artifact differs from the active 2^21 layout"
        );
    }
    let (target_circuit, target_profile, trace_len_log2) = case.stage.target();
    let (follower_circuit, follower_profile) = case.follower.identity();
    let arena_bytes = case.arena_bytes();
    let policy = case.stage.policy(arena_bytes);
    let geometry = case.stage.geometry();
    let mut row = CapacityRow {
        schema_version: SCHEMA_VERSION,
        case: case.key(),
        revision: revision(),
        binary_digest: binary_digest(),
        stage: case.stage,
        target_circuit: format!("{target_circuit:?}"),
        target_profile: format!("{target_profile:?}"),
        trace_len_log2,
        policy,
        arena_bytes,
        direction: case.direction,
        follower: case.follower,
        follower_circuit: format!("{follower_circuit:?}"),
        follower_profile: format!("{follower_profile:?}"),
        target_input_bytes: None,
        follower_input_bytes: None,
        initialization_peak_bytes: None,
        prerequisite_peak_bytes: None,
        measured_peak_bytes: None,
        output_fingerprint: None,
        partial_trees: case.partial_trees,
        lde_factor: geometry.as_ref().map(|geometry| geometry.0),
        tree_cap_size: geometry.as_ref().map(|geometry| geometry.1),
        queries_and_pow: geometry.map(|geometry| geometry.2),
        wrap_identity: case
            .needs_wrap_source()
            .then(|| WrapIdentity::current().clone()),
        proof_equals_reference: None,
        vmhwm_kib: None,
        fits: false,
        failure_kind: None,
        failed_phase: None,
    };
    let mut context = capacity_context(arena_bytes);
    if let Err(phase) = measure(case, wrap, &mut context, &mut row) {
        row.fits = false;
        row.failure_kind = Some("allocation_oom".into());
        row.failed_phase = Some(phase.into());
    } else {
        row.fits = true;
    }
    drain(&context).expect("L1 capacity final drain");
    drop(context);
    row.vmhwm_kib = vmhwm_kib();
    std::fs::write(
        &case.row_path,
        serde_json::to_vec_pretty(&row).expect("L1 capacity row serializes"),
    )
    .unwrap_or_else(|error| panic!("L1 capacity row write {}: {error}", case.row_path.display()));
    row
}

fn measure<B: GoodAllocator>(
    case: &CapacityCase,
    wrap: Option<WrapSource<'_, B>>,
    context: &mut ProverContext,
    row: &mut CapacityRow,
) -> Result<(), &'static str> {
    let target_direction = case.direction.allocation();
    let follower_direction = case.direction.opposite();
    let needs_factory = case.stage != Stage::Wrap || case.follower != Follower::Wrap;
    let factory = needs_factory.then(|| SyntheticInputFactory::for_l1_capacity(SECURITY_LEVEL));
    context.set_allocation_mode(AllocationMode::Unbounded);
    context.reset_used_mem_peak();
    let wrap_precomputed = match &wrap {
        Some(source) => {
            let precomputed = Arc::new(step(
                "setup_initialization",
                context,
                L1WrapPrecomputed::new(
                    CircuitType::L1Wrap21,
                    clone_setup(source.setup),
                    SECURITY_LEVEL,
                ),
            )?);
            step(
                "setup_initialization",
                context,
                precomputed.initialize(SECURITY_LEVEL, context),
            )?;
            Some(precomputed)
        }
        None => None,
    };
    let feeder_needed = case.stage != Stage::Wrap || case.follower == Follower::Feeder;
    let mut feeder = if feeder_needed {
        let prepared = step(
            "setup_initialization",
            context,
            factory
                .as_ref()
                .expect("feeder inputs require the synthetic factory")
                .prepare_profile(UNIFIED22, ProofProfile::L1Feeder),
        )?;
        step(
            "setup_initialization",
            context,
            prepared
                .precomputations
                .baby_bear()
                .setup_host
                .get_or_init(context),
        )?;
        Some(prepared)
    } else {
        None
    };
    let inits_and_teardowns = match case.follower {
        Follower::StandardIt => {
            let mut prepared = step(
                "setup_initialization",
                context,
                factory
                    .as_ref()
                    .expect("I&T follower requires the synthetic factory")
                    .prepare_profile(INITS_AND_TEARDOWNS, ProofProfile::Standard),
            )?;
            step(
                "setup_initialization",
                context,
                prepared
                    .precomputations
                    .baby_bear()
                    .setup_host
                    .get_or_init(context),
            )?;
            let config =
                prover_config(INITS_AND_TEARDOWNS, ProofProfile::Standard, SECURITY_LEVEL).unwrap();
            prepared.set_memory_caps(synthetic_caps(&config));
            Some(prepared)
        }
        Follower::Feeder | Follower::Wrap => None,
    };
    step("setup_initialization", context, drain(context))?;
    row.initialization_peak_bytes = Some(context.get_used_mem_peak());

    match case.stage {
        Stage::Wrap => {
            let source = wrap.as_ref().expect("wrap target requires a wrap source");
            let precomputed = wrap_precomputed
                .as_ref()
                .expect("wrap target precomputations");
            let dr_tail_plan = preflight_dr_tail_resources_pr(
                &precomputed.programs,
                WRAP_FINAL_TRACE_SIZE_LOG_2,
                context,
            );
            context.set_allocation_mode(AllocationMode::Inputs(target_direction));
            let before = context.get_used_mem_current();
            let mut target = step(
                "target_inputs",
                context,
                L1WrapInputs::new(
                    &precomputed.geometry,
                    precomputed.decoder_host.clone(),
                    source.inits_and_teardowns.clone(),
                    source.tracing_data.clone(),
                    precomputed.host(),
                    context,
                ),
            )?;
            step("target_inputs", context, target.schedule(context))?;
            step(
                "target_inputs",
                context,
                context.get_h2d_stream().synchronize(),
            )?;
            row.target_input_bytes = Some(context.get_used_mem_current() - before);
            let follower = schedule_follower(
                case,
                context,
                follower_direction,
                &mut feeder,
                &inits_and_teardowns,
                &wrap,
                &wrap_precomputed,
                row,
            )?;
            context.set_allocation_mode(AllocationMode::Proof(target_direction));
            let job = step(
                "target_stage",
                context,
                gpu_circuit_prover::l1_wrap::prove(
                    &precomputed.programs,
                    &precomputed.circuit,
                    &precomputed.geometry,
                    &precomputed.config,
                    source.commitment_mode,
                    target,
                    &dr_tail_plan,
                    presets::policy(CircuitType::L1Wrap21, ProofProfile::L1Wrap, row.arena_bytes),
                    case.partial_trees(CircuitType::L1Wrap21, ProofProfile::L1Wrap),
                    context,
                ),
            )?;
            row.measured_peak_bytes = Some(context.get_used_mem_peak());
            let result = step("target_finish", context, job.finish())?;
            let proof_json = serde_json::to_vec(&result.proof).expect("L1 wrap proof serializes");
            row.proof_equals_reference = Some(
                source.reference.matches(
                    &proof_json,
                    &serde_json::to_vec(&result.commitment_mode)
                        .expect("L1 wrap commitment mode serializes"),
                ),
            );
            row.output_fingerprint = Some(output_digest(proof_json));
            step("target_finish", context, drain(context))?;
            drop(follower);
        }
        Stage::FeederCommit => {
            let prepared = feeder.as_ref().expect("feeder target inputs");
            let config = feeder_config();
            context.set_allocation_mode(AllocationMode::Inputs(target_direction));
            let before = context.get_used_mem_current();
            let mut target = step(
                "target_inputs",
                context,
                merged_commit_inputs(
                    prepared,
                    case.partial_trees(UNIFIED22, ProofProfile::L1Feeder).setup,
                    context,
                ),
            )?;
            step("target_inputs", context, target.schedule(context))?;
            step(
                "target_inputs",
                context,
                context.get_h2d_stream().synchronize(),
            )?;
            row.target_input_bytes = Some(context.get_used_mem_current() - before);
            let follower = schedule_follower(
                case,
                context,
                follower_direction,
                &mut feeder,
                &inits_and_teardowns,
                &wrap,
                &wrap_precomputed,
                row,
            )?;
            let prepared = feeder.as_ref().expect("feeder target inputs");
            context.set_allocation_mode(AllocationMode::Proof(target_direction));
            context.reset_used_mem_peak();
            let job = step(
                "target_stage",
                context,
                commit_merged_from_transfers::<A>(
                    &prepared.precomputations.baby_bear().gkr_programs,
                    &config,
                    target,
                    presets::merged_commit_strategy(UNIFIED22, ProofProfile::L1Feeder),
                    case.partial_trees(UNIFIED22, ProofProfile::L1Feeder),
                    false,
                    context,
                ),
            )?;
            row.measured_peak_bytes = Some(context.get_used_mem_peak());
            let (caps, _) = step("target_finish", context, job.finish())?;
            row.output_fingerprint = Some(output_digest(
                serde_json::to_vec(&caps).expect("L1 feeder caps serialize"),
            ));
            step("target_finish", context, drain(context))?;
            drop(follower);
        }
        Stage::FeederProof => {
            let config = feeder_config();
            {
                let prepared = feeder.as_ref().expect("feeder target inputs");
                context.set_allocation_mode(AllocationMode::Inputs(target_direction));
                let mut inputs = step(
                    "prerequisite_commit",
                    context,
                    merged_commit_inputs(
                        prepared,
                        case.partial_trees(UNIFIED22, ProofProfile::L1Feeder).setup,
                        context,
                    ),
                )?;
                step("prerequisite_commit", context, inputs.schedule(context))?;
                context.set_allocation_mode(AllocationMode::Proof(target_direction));
                context.reset_used_mem_peak();
                let job = step(
                    "prerequisite_commit",
                    context,
                    commit_merged_from_transfers::<A>(
                        &prepared.precomputations.baby_bear().gkr_programs,
                        &config,
                        inputs,
                        presets::merged_commit_strategy(UNIFIED22, ProofProfile::L1Feeder),
                        case.partial_trees(UNIFIED22, ProofProfile::L1Feeder),
                        false,
                        context,
                    ),
                )?;
                let (caps, _) = step("prerequisite_commit", context, job.finish())?;
                step("prerequisite_commit", context, drain(context))?;
                row.prerequisite_peak_bytes = Some(context.get_used_mem_peak());
                feeder
                    .as_mut()
                    .expect("feeder target inputs")
                    .set_memory_caps(caps);
            }
            let prepared = feeder.as_ref().expect("feeder target inputs");
            context.set_allocation_mode(AllocationMode::Inputs(target_direction));
            let before = context.get_used_mem_current();
            let (target, plan) = step(
                "target_inputs",
                context,
                schedule_proof_inputs(
                    0,
                    context,
                    prepared,
                    case.partial_trees(UNIFIED22, ProofProfile::L1Feeder).setup,
                ),
            )?;
            step(
                "target_inputs",
                context,
                context.get_h2d_stream().synchronize(),
            )?;
            row.target_input_bytes = Some(context.get_used_mem_current() - before);
            let follower = schedule_follower(
                case,
                context,
                follower_direction,
                &mut feeder,
                &inits_and_teardowns,
                &wrap,
                &wrap_precomputed,
                row,
            )?;
            let prepared = feeder.as_ref().expect("feeder target inputs");
            context.set_allocation_mode(AllocationMode::Proof(target_direction));
            let job = step(
                "target_stage",
                context,
                gpu_circuit_prover::proof::prove::<A>(
                    &prepared.precomputations.baby_bear().gkr_programs,
                    &config,
                    CommitmentMode::MergedMemoryAndWitness,
                    FINAL_TRACE_SIZE_LOG_2,
                    target,
                    &plan,
                    presets::policy(UNIFIED22, ProofProfile::L1Feeder, row.arena_bytes),
                    case.partial_trees(UNIFIED22, ProofProfile::L1Feeder),
                    context,
                ),
            )?;
            row.measured_peak_bytes = Some(context.get_used_mem_peak());
            let (proof, _) = step("target_finish", context, job.finish())?;
            row.output_fingerprint = Some(output_digest(
                serde_json::to_vec(&proof).expect("L1 feeder proof serializes"),
            ));
            step("target_finish", context, drain(context))?;
            drop(follower);
        }
    }
    Ok(())
}

fn merged_commit_inputs<'a>(
    prepared: &PreparedCircuit,
    setup_reduction_layers: u32,
    context: &ProverContext,
) -> CudaResult<GpuGKRMergedCommitTransfer<'a, A>> {
    let setup_host = prepared
        .precomputations
        .baby_bear()
        .setup_host
        .get_initialized(prepared.profile)
        .expect("merged memory+witness commitment requires the initialized setup");
    let setup = GpuGKRSetupTransfer::new(setup_host, setup_reduction_layers, context)?;
    let (decoder, inits, trace) = input_transfers(context, prepared)?;
    GpuGKRMergedCommitTransfer::new(setup, decoder, inits, trace, context)
}

#[allow(clippy::too_many_arguments)]
fn schedule_follower<'a, B: GoodAllocator + 'a>(
    case: &CapacityCase,
    context: &mut ProverContext,
    direction: AllocationDirection,
    feeder: &mut Option<PreparedCircuit>,
    inits_and_teardowns: &Option<PreparedCircuit>,
    wrap: &Option<WrapSource<'_, B>>,
    wrap_precomputed: &Option<Arc<L1WrapPrecomputed>>,
    row: &mut CapacityRow,
) -> Result<FollowerInputs<'a, B>, &'static str> {
    context.set_allocation_mode(AllocationMode::Inputs(direction));
    let before = context.get_used_mem_current();
    let follower = match case.follower {
        Follower::StandardIt => {
            let prepared = inits_and_teardowns.as_ref().expect("I&T follower inputs");
            let (inputs, _) = step(
                "follower_inputs",
                context,
                schedule_proof_inputs(
                    0,
                    context,
                    prepared,
                    preset_setup_reduction_layers(prepared),
                ),
            )?;
            (Some(inputs), None)
        }
        Follower::Feeder => {
            let prepared = feeder.as_mut().expect("feeder follower inputs");
            if prepared.memory_caps.is_none() {
                prepared.set_memory_caps(synthetic_caps(&feeder_config()));
            }
            let (inputs, _) = step(
                "follower_inputs",
                context,
                schedule_proof_inputs(
                    0,
                    context,
                    prepared,
                    preset_setup_reduction_layers(prepared),
                ),
            )?;
            (Some(inputs), None)
        }
        Follower::Wrap => {
            let source = wrap.as_ref().expect("wrap follower requires a wrap source");
            let precomputed = wrap_precomputed
                .as_ref()
                .expect("wrap follower precomputations");
            preflight_dr_tail_resources_pr(
                &precomputed.programs,
                WRAP_FINAL_TRACE_SIZE_LOG_2,
                context,
            );
            let mut inputs = step(
                "follower_inputs",
                context,
                L1WrapInputs::new(
                    &precomputed.geometry,
                    precomputed.decoder_host.clone(),
                    source.inits_and_teardowns.clone(),
                    source.tracing_data.clone(),
                    precomputed.host(),
                    context,
                ),
            )?;
            step("follower_inputs", context, inputs.schedule(context))?;
            (None, Some(inputs))
        }
    };
    row.follower_input_bytes = Some(context.get_used_mem_current() - before);
    Ok(follower)
}

pub fn validate_row(row: &CapacityRow, key: &str, revision: &str) -> Result<(), String> {
    let invalid = |reason: &str| Err(format!("L1 capacity row {key}: {reason}"));
    if row.schema_version != SCHEMA_VERSION {
        return invalid("schema version");
    }
    if row.case != key {
        return invalid("case key differs");
    }
    if row.revision != revision {
        return invalid("mixed implementation revision");
    }
    let parts: Vec<&str> = key.split('-').collect();
    let expected = (|| {
        let [_, arena, stage, follower, direction] = parts.as_slice() else {
            return None;
        };
        let arena: usize = arena.parse().ok()?;
        let stage = [Stage::Wrap, Stage::FeederCommit, Stage::FeederProof]
            .into_iter()
            .find(|candidate| candidate.name() == *stage)?;
        let follower = Follower::ALL
            .into_iter()
            .find(|candidate| candidate.name() == *follower)?;
        let direction = Direction::ALL
            .into_iter()
            .find(|candidate| candidate.name() == *direction)?;
        Some((arena, stage, follower, direction))
    })();
    let Some((arena_gib, stage, follower, direction)) = expected else {
        return invalid("malformed case key");
    };
    let (target_circuit, target_profile, trace_len_log2) = stage.target();
    let (follower_circuit, follower_profile) = follower.identity();
    if row.stage != stage
        || row.follower != follower
        || row.direction != direction
        || row.arena_bytes != arena_gib << 30
        || row.target_circuit != format!("{target_circuit:?}")
        || row.target_profile != format!("{target_profile:?}")
        || row.follower_circuit != format!("{follower_circuit:?}")
        || row.follower_profile != format!("{follower_profile:?}")
    {
        return invalid("identity differs from the case key");
    }
    let geometry = stage.geometry();
    if row.trace_len_log2 != trace_len_log2
        || row.lde_factor != geometry.as_ref().map(|geometry| geometry.0)
        || row.tree_cap_size != geometry.as_ref().map(|geometry| geometry.1)
        || row.queries_and_pow != geometry.map(|geometry| geometry.2)
    {
        return invalid("trace geometry differs from the production stage");
    }
    if row.policy != stage.policy(row.arena_bytes) {
        return invalid("policy differs from the production stage policy");
    }
    if (stage == Stage::Wrap || follower == Follower::Wrap)
        && row.wrap_identity.as_ref() != Some(WrapIdentity::current())
    {
        return invalid("wrap identity differs from the active 2^21 wrap");
    }
    if stage == Stage::Wrap
        && (row.fits || row.output_fingerprint.is_some() || row.proof_equals_reference.is_some())
        && row.proof_equals_reference != Some(true)
    {
        return invalid("completed wrap proof differs from the reference (or parity is missing)");
    }
    if row.fits {
        let complete = row.failure_kind.is_none()
            && row.failed_phase.is_none()
            && row.target_input_bytes.is_some_and(|bytes| bytes > 0)
            && row.follower_input_bytes.is_some_and(|bytes| bytes > 0)
            && row.initialization_peak_bytes.is_some()
            && row
                .measured_peak_bytes
                .is_some_and(|peak| peak <= row.arena_bytes)
            && row.output_fingerprint.is_some()
            && row.vmhwm_kib.is_some()
            && (stage != Stage::FeederProof || row.prerequisite_peak_bytes.is_some());
        if !complete {
            return invalid("a successful row lacks a metric, its output or a resident input");
        }
    } else if row.failure_kind.as_deref() != Some("allocation_oom")
        || !row
            .failed_phase
            .as_deref()
            .is_some_and(|phase| FAILED_PHASES.contains(&phase))
    {
        return invalid("a failed row is not an allocation OOM with a recorded phase");
    }
    Ok(())
}

pub fn select_capacity(
    family: Family,
    rows: &BTreeMap<String, CapacityRow>,
    revision: &str,
) -> Result<usize, String> {
    for (key, row) in rows {
        validate_row(row, key, revision)?;
        if row.stage.family() != family {
            return Err(format!("L1 capacity row {key} belongs to another family"));
        }
    }
    for &arena_gib in family.candidates_gib() {
        let keys = candidate_case_keys(family, arena_gib);
        let present: Vec<&CapacityRow> = keys.iter().filter_map(|key| rows.get(key)).collect();
        if present.len() == keys.len() && present.iter().all(|row| row.fits) {
            return Ok(arena_gib);
        }
        if !present.iter().any(|row| !row.fits) {
            return Err(format!(
                "{} candidate {arena_gib} GiB is incomplete without an allocation OOM",
                family.name()
            ));
        }
    }
    Err(format!("no sufficient {} candidate", family.name()))
}

/// Feeder arenas below the smallest candidate: floor-bracket diagnostics, never selected.
pub fn is_feeder_bracket_arena(arena_gib: usize) -> bool {
    (1..FEEDER_CANDIDATES_GIB[0]).contains(&arena_gib)
}

/// A feeder row measured with the production preset: valid and without a partial-tree override.
fn validate_feeder_row(row: &CapacityRow, key: &str, revision: &str) -> Result<(), String> {
    validate_row(row, key, revision)?;
    if let Some(depth) = row.partial_trees {
        return Err(format!(
            "L1 capacity row {key}: partial-tree override {depth} is not the production preset"
        ));
    }
    Ok(())
}

/// Every feeder case at `arena_gib` is present, valid and fits.
pub fn qualify_feeder_capacity(
    rows: &BTreeMap<String, CapacityRow>,
    revision: &str,
    arena_gib: usize,
) -> Result<(), String> {
    for key in candidate_case_keys(Family::Feeder, arena_gib) {
        let row = rows
            .get(&key)
            .ok_or_else(|| format!("L1 capacity row {key} is missing"))?;
        validate_feeder_row(row, &key, revision)?;
        if !row.fits {
            return Err(format!("L1 capacity row {key} does not fit"));
        }
    }
    Ok(())
}

/// All six qualifying cases must fit with proof parity. Return the smallest
/// tested arena with six passing cases; lower incomplete/OOM arenas are diagnostic.
/// Feeder-stage rows (including wrap followers) belong to W4 and are ignored.
pub fn qualify_wrap_capacity(
    rows: &BTreeMap<String, CapacityRow>,
    revision: &str,
    qualifying_gib: usize,
) -> Result<usize, String> {
    if !WRAP_CANDIDATES_GIB.contains(&qualifying_gib) {
        return Err(format!(
            "wrap qualifying arena {qualifying_gib} GiB is not a candidate"
        ));
    }
    for (key, row) in rows.iter().filter(|(_, row)| row.stage == Stage::Wrap) {
        if !WRAP_CANDIDATES_GIB.contains(&(row.arena_bytes >> 30)) {
            return Err(format!(
                "L1 capacity row {key}: arena is not a wrap candidate"
            ));
        }
        validate_row(row, key, revision)?;
        if let Some(depth) = row.partial_trees {
            return Err(format!(
                "L1 capacity row {key}: partial-tree override {depth} is not the production preset"
            ));
        }
    }
    for key in candidate_case_keys(Family::Wrap, qualifying_gib) {
        let row = rows
            .get(&key)
            .filter(|row| row.stage == Stage::Wrap)
            .ok_or_else(|| format!("L1 capacity row {key} is missing"))?;
        if !row.fits {
            return Err(format!("L1 capacity row {key} does not fit"));
        }
    }
    WRAP_CANDIDATES_GIB
        .into_iter()
        .find(|&arena_gib| {
            candidate_case_keys(Family::Wrap, arena_gib)
                .iter()
                .all(|key| {
                    rows.get(key).is_some_and(|row| {
                        row.stage == Stage::Wrap
                            && row.fits
                            && row.proof_equals_reference == Some(true)
                    })
                })
        })
        .ok_or_else(|| "no sufficient wrap candidate with proof parity".into())
}

/// The feeder floor bracket over complete arenas: (lowest arena where every
/// case fits, highest arena below it where a case runs out of memory).
pub fn feeder_floor_bracket(
    rows: &BTreeMap<String, CapacityRow>,
    revision: &str,
) -> Result<(usize, Option<usize>), String> {
    let mut arenas = BTreeMap::<usize, bool>::new();
    for (key, row) in rows {
        validate_feeder_row(row, key, revision)?;
        if row.stage.family() != Family::Feeder {
            return Err(format!("L1 capacity row {key} belongs to another family"));
        }
        let fits = arenas.entry(row.arena_bytes >> 30).or_insert(true);
        *fits &= row.fits;
    }
    for (&arena_gib, &fits) in &arenas {
        let complete = candidate_case_keys(Family::Feeder, arena_gib)
            .iter()
            .all(|key| rows.contains_key(key));
        if fits && !complete {
            return Err(format!(
                "feeder arena {arena_gib} GiB is incomplete without an allocation OOM"
            ));
        }
    }
    let lowest_passing = arenas
        .iter()
        .find(|(_, &fits)| fits)
        .map(|(&arena_gib, _)| arena_gib)
        .ok_or("no feeder arena fits every case")?;
    if let Some((&arena_gib, _)) = arenas.range(lowest_passing..).find(|(_, &fits)| !fits) {
        return Err(format!(
            "feeder arena {arena_gib} GiB fails above the passing {lowest_passing} GiB"
        ));
    }
    let highest_failing = arenas
        .range(..lowest_passing)
        .next_back()
        .map(|(&arena_gib, _)| arena_gib);
    Ok((lowest_passing, highest_failing))
}

pub fn read_row(path: &Path) -> CapacityRow {
    let bytes = std::fs::read(path)
        .unwrap_or_else(|error| panic!("L1 capacity row read {}: {error}", path.display()));
    serde_json::from_slice(&bytes)
        .unwrap_or_else(|error| panic!("L1 capacity row parse {}: {error}", path.display()))
}

#[cfg(test)]
mod cpu_tests {
    use super::*;

    const REVISION: &str = "0123456789abcdef0123456789abcdef01234567";

    fn passing_row(key: &str) -> CapacityRow {
        let parts: Vec<&str> = key.split('-').collect();
        let arena_gib: usize = parts[1].parse().unwrap();
        let stage = [Stage::Wrap, Stage::FeederCommit, Stage::FeederProof]
            .into_iter()
            .find(|stage| stage.name() == parts[2])
            .unwrap();
        let follower = Follower::ALL
            .into_iter()
            .find(|follower| follower.name() == parts[3])
            .unwrap();
        let direction = Direction::ALL
            .into_iter()
            .find(|direction| direction.name() == parts[4])
            .unwrap();
        let (target_circuit, target_profile, trace_len_log2) = stage.target();
        let (follower_circuit, follower_profile) = follower.identity();
        CapacityRow {
            schema_version: SCHEMA_VERSION,
            case: key.into(),
            revision: REVISION.into(),
            binary_digest: "0".into(),
            stage,
            target_circuit: format!("{target_circuit:?}"),
            target_profile: format!("{target_profile:?}"),
            trace_len_log2,
            policy: stage.policy(arena_gib << 30),
            arena_bytes: arena_gib << 30,
            direction,
            follower,
            follower_circuit: format!("{follower_circuit:?}"),
            follower_profile: format!("{follower_profile:?}"),
            target_input_bytes: Some(1),
            follower_input_bytes: Some(1),
            initialization_peak_bytes: Some(1),
            prerequisite_peak_bytes: Some(1),
            measured_peak_bytes: Some(1),
            output_fingerprint: Some("f".into()),
            partial_trees: None,
            lde_factor: stage.geometry().map(|geometry| geometry.0),
            tree_cap_size: stage.geometry().map(|geometry| geometry.1),
            queries_and_pow: stage.geometry().map(|geometry| geometry.2),
            wrap_identity: (stage == Stage::Wrap || follower == Follower::Wrap)
                .then(|| WrapIdentity::current().clone()),
            proof_equals_reference: (stage == Stage::Wrap).then_some(true),
            vmhwm_kib: Some(1),
            fits: true,
            failure_kind: None,
            failed_phase: None,
        }
    }

    fn oom(mut row: CapacityRow) -> CapacityRow {
        row.fits = false;
        row.failure_kind = Some("allocation_oom".into());
        row.failed_phase = Some("target_stage".into());
        row.measured_peak_bytes = None;
        row.output_fingerprint = None;
        row.proof_equals_reference = None;
        row
    }

    fn complete(family: Family, arena_gib: usize) -> BTreeMap<String, CapacityRow> {
        candidate_case_keys(family, arena_gib)
            .into_iter()
            .map(|key| (key.clone(), passing_row(&key)))
            .collect()
    }

    #[test]
    fn cpu_m8_capacity_matrix() {
        assert_eq!(Family::Wrap.candidates_gib(), &[21, 30]);
        assert_eq!(Family::Feeder.candidates_gib(), &[21, 30, 40, 48, 64]);
        for family in Family::ALL {
            assert!(family
                .candidates_gib()
                .windows(2)
                .all(|pair| pair[0] < pair[1]));
            for &arena_gib in family.candidates_gib() {
                let keys = candidate_case_keys(family, arena_gib);
                assert_eq!(keys.len(), family.stages().len() * 3 * 2);
                assert_eq!(
                    keys.iter().collect::<std::collections::BTreeSet<_>>().len(),
                    keys.len()
                );
            }
        }
        assert_eq!(candidate_case_keys(Family::Wrap, 21).len(), 6);
        assert_eq!(candidate_case_keys(Family::Feeder, 21).len(), 12);
        assert_eq!(
            case_key(
                64,
                Stage::FeederProof,
                Follower::StandardIt,
                Direction::Descending
            ),
            "feeder-64-feeder_proof-standard_it-descending"
        );
        assert_eq!(
            Follower::Wrap.identity(),
            (CircuitType::L1Wrap21, ProofProfile::L1Wrap)
        );
        assert_eq!(
            Follower::Feeder.identity(),
            (UNIFIED22, ProofProfile::L1Feeder)
        );
        assert_eq!(
            Follower::StandardIt.identity(),
            (INITS_AND_TEARDOWNS, ProofProfile::Standard)
        );
        for direction in Direction::ALL {
            assert_ne!(direction.allocation(), direction.opposite());
        }
        let total: usize = Family::ALL
            .into_iter()
            .map(|family| family.candidates_gib().len() * family.stages().len() * 6)
            .sum();
        assert_eq!(total, 72);
    }

    #[test]
    fn cpu_m8_capacity_selection() {
        let mut rows = complete(Family::Wrap, 30);
        let first = candidate_case_keys(Family::Wrap, 21)[0].clone();
        rows.insert(first.clone(), oom(passing_row(&first)));
        assert_eq!(select_capacity(Family::Wrap, &rows, REVISION), Ok(30));

        let rows = complete(Family::Wrap, 21);
        assert_eq!(select_capacity(Family::Wrap, &rows, REVISION), Ok(21));

        let mut incomplete = complete(Family::Wrap, 21);
        incomplete.remove(&first);
        assert!(select_capacity(Family::Wrap, &incomplete, REVISION)
            .unwrap_err()
            .contains("incomplete without an allocation OOM"));

        let extrapolated = complete(Family::Wrap, 40);
        assert!(select_capacity(Family::Wrap, &extrapolated, REVISION)
            .unwrap_err()
            .contains("21 GiB is incomplete"));

        let mut mixed = complete(Family::Wrap, 21);
        mixed.get_mut(&first).unwrap().revision = "other".into();
        assert!(select_capacity(Family::Wrap, &mixed, REVISION)
            .unwrap_err()
            .contains("mixed implementation revision"));

        let mut absent = complete(Family::Wrap, 21);
        absent.get_mut(&first).unwrap().output_fingerprint = None;
        assert!(select_capacity(Family::Wrap, &absent, REVISION)
            .unwrap_err()
            .contains("lacks a metric"));

        let mut over = complete(Family::Wrap, 21);
        over.get_mut(&first).unwrap().measured_peak_bytes = Some((21 << 30) + 1);
        assert!(select_capacity(Family::Wrap, &over, REVISION).is_err());

        let mut invalid_failure = complete(Family::Wrap, 30);
        let mut failed = oom(passing_row(&first));
        failed.failure_kind = Some("kernel_error".into());
        invalid_failure.insert(first.clone(), failed);
        assert!(select_capacity(Family::Wrap, &invalid_failure, REVISION)
            .unwrap_err()
            .contains("not an allocation OOM"));

        let mut wrong_identity = complete(Family::Wrap, 21);
        wrong_identity.get_mut(&first).unwrap().follower_profile = "L1Feeder".into();
        assert!(select_capacity(Family::Wrap, &wrong_identity, REVISION)
            .unwrap_err()
            .contains("identity differs"));

        let mut wrong_phase = complete(Family::Wrap, 30);
        let mut failed = oom(passing_row(&first));
        failed.failed_phase = Some("elsewhere".into());
        wrong_phase.insert(first.clone(), failed);
        assert!(select_capacity(Family::Wrap, &wrong_phase, REVISION)
            .unwrap_err()
            .contains("not an allocation OOM with a recorded phase"));

        for family in Family::ALL {
            let arena_gib = family.candidates_gib()[0];
            for key in candidate_case_keys(family, arena_gib) {
                let mut geometry = complete(family, arena_gib);
                let row = geometry.get_mut(&key).unwrap();
                row.trace_len_log2 = if row.trace_len_log2 == 22 { 23 } else { 22 };
                assert!(select_capacity(family, &geometry, REVISION)
                    .unwrap_err()
                    .contains("trace geometry differs"));
                let mut policy = complete(family, arena_gib);
                policy.get_mut(&key).unwrap().policy = "unsupported_policy".into();
                assert!(select_capacity(family, &policy, REVISION)
                    .unwrap_err()
                    .contains("policy differs"));
            }
        }
        let feeder_commit = candidate_case_keys(Family::Feeder, 21)[0].clone();
        let mut swapped = complete(Family::Feeder, 21);
        swapped.get_mut(&feeder_commit).unwrap().policy = Stage::FeederProof.policy(21 << 30);
        assert!(select_capacity(Family::Feeder, &swapped, REVISION)
            .unwrap_err()
            .contains("policy differs"));

        let mut feeder = complete(Family::Feeder, 30);
        let commit = candidate_case_keys(Family::Feeder, 21)[0].clone();
        feeder.insert(commit.clone(), oom(passing_row(&commit)));
        assert_eq!(select_capacity(Family::Feeder, &feeder, REVISION), Ok(30));
        let mut missing_prerequisite = complete(Family::Feeder, 21);
        let proof = candidate_case_keys(Family::Feeder, 21)
            .into_iter()
            .find(|key| key.contains("feeder_proof"))
            .unwrap();
        missing_prerequisite
            .get_mut(&proof)
            .unwrap()
            .prerequisite_peak_bytes = None;
        assert!(select_capacity(Family::Feeder, &missing_prerequisite, REVISION).is_err());

        assert!(select_capacity(Family::Wrap, &BTreeMap::new(), REVISION)
            .unwrap_err()
            .contains("incomplete"));
    }

    #[test]
    fn cpu_w5_wrap_capacity_accepts_complete_arenas() {
        let mut rows = complete(Family::Wrap, 30);
        assert_eq!(qualify_wrap_capacity(&rows, REVISION, 30), Ok(30));
        // Feeder-stage rows belong to W4, including rows with a wrap follower.
        let mut feeder = complete(Family::Feeder, 30);
        for row in feeder.values_mut() {
            row.revision = "another feeder revision".into();
        }
        rows.extend(feeder);
        assert_eq!(qualify_wrap_capacity(&rows, REVISION, 30), Ok(30));
        let first = candidate_case_keys(Family::Wrap, 21)[0].clone();
        rows.insert(first.clone(), passing_row(&first));
        assert_eq!(qualify_wrap_capacity(&rows, REVISION, 30), Ok(30));
        rows.extend(complete(Family::Wrap, 21));
        assert_eq!(qualify_wrap_capacity(&rows, REVISION, 30), Ok(21));
        rows.insert(first.clone(), oom(passing_row(&first)));
        assert_eq!(qualify_wrap_capacity(&rows, REVISION, 30), Ok(30));
    }

    #[test]
    fn cpu_w5_wrap_capacity_requires_every_qualifying_case() {
        for key in candidate_case_keys(Family::Wrap, 30) {
            let mut rows = complete(Family::Wrap, 30);
            rows.extend(complete(Family::Wrap, 21));
            rows.remove(&key);
            let error = qualify_wrap_capacity(&rows, REVISION, 30).unwrap_err();
            assert!(
                error.contains(&key) && error.contains("is missing"),
                "{error}"
            );
        }
    }

    #[test]
    fn cpu_w5_wrap_capacity_rejects_mixed_revision() {
        for arena in WRAP_CANDIDATES_GIB {
            let mut rows = complete(Family::Wrap, 21);
            rows.extend(complete(Family::Wrap, 30));
            let key = candidate_case_keys(Family::Wrap, arena)[0].clone();
            rows.get_mut(&key).unwrap().revision = "other".into();
            assert!(qualify_wrap_capacity(&rows, REVISION, 30)
                .unwrap_err()
                .contains("mixed implementation revision"));
        }
    }

    #[test]
    fn cpu_w5_wrap_capacity_rejects_wrong_proof() {
        for arena in WRAP_CANDIDATES_GIB {
            for parity in [Some(false), None] {
                let mut rows = complete(Family::Wrap, 21);
                rows.extend(complete(Family::Wrap, 30));
                let key = candidate_case_keys(Family::Wrap, arena)[0].clone();
                rows.get_mut(&key).unwrap().proof_equals_reference = parity;
                assert!(qualify_wrap_capacity(&rows, REVISION, 30)
                    .unwrap_err()
                    .contains("proof differs from the reference"));
            }
        }
        // Even a later allocation failure cannot hide an already completed wrong proof.
        let mut rows = complete(Family::Wrap, 30);
        let key = candidate_case_keys(Family::Wrap, 21)[0].clone();
        let mut failed = oom(passing_row(&key));
        failed.proof_equals_reference = Some(false);
        rows.insert(key, failed);
        assert!(qualify_wrap_capacity(&rows, REVISION, 30)
            .unwrap_err()
            .contains("proof differs from the reference"));
    }

    #[test]
    fn cpu_w5_wrap_capacity_rejects_qualifying_oom() {
        let mut rows = complete(Family::Wrap, 21);
        rows.extend(complete(Family::Wrap, 30));
        let key = candidate_case_keys(Family::Wrap, 30)[0].clone();
        rows.insert(key.clone(), oom(passing_row(&key)));
        assert!(qualify_wrap_capacity(&rows, REVISION, 30)
            .unwrap_err()
            .contains("does not fit"));
    }

    #[test]
    fn cpu_w5_wrap_capacity_rejects_stale_identity() {
        let original = complete(Family::Wrap, 30);
        let key = candidate_case_keys(Family::Wrap, 30)[0].clone();
        let mut variants = Vec::new();
        let mut row = original[&key].clone();
        row.target_circuit = "L1Wrap".into();
        row.trace_len_log2 = 22;
        variants.push(row);
        let mut row = original[&key].clone();
        row.trace_len_log2 = 22;
        variants.push(row);
        let mut row = original[&key].clone();
        row.lde_factor = Some(1);
        variants.push(row);
        let mut row = original[&key].clone();
        row.wrap_identity = None;
        variants.push(row);
        let mut row = original[&key].clone();
        row.wrap_identity.as_mut().unwrap().rom_bytes = 4 << 20;
        variants.push(row);
        let mut row = original[&key].clone();
        row.wrap_identity.as_mut().unwrap().layout_keccak256 = "stale".into();
        variants.push(row);
        let mut row = original[&key].clone();
        row.wrap_identity.as_mut().unwrap().queries_and_pow[0].0 += 1;
        variants.push(row);
        for row in variants {
            let mut rows = original.clone();
            rows.insert(key.clone(), row);
            assert!(qualify_wrap_capacity(&rows, REVISION, 30).is_err());
        }
    }

    #[test]
    fn cpu_w5_wrap_capacity_rejects_partial_tree_override() {
        let mut rows = complete(Family::Wrap, 30);
        let key = candidate_case_keys(Family::Wrap, 30)[0].clone();
        rows.get_mut(&key).unwrap().partial_trees = Some(10);
        assert!(qualify_wrap_capacity(&rows, REVISION, 30)
            .unwrap_err()
            .contains("partial-tree override"));
    }

    #[test]
    fn cpu_w5_wrap_capacity_row_defaults() {
        let row = passing_row("feeder-30-feeder_proof-wrap-descending");
        assert_eq!(row.wrap_identity.as_ref(), Some(WrapIdentity::current()));
        let mut value = serde_json::to_value(&row).unwrap();
        let fields = value.as_object_mut().unwrap();
        fields.remove("wrap_identity");
        fields.remove("proof_equals_reference");
        let legacy: CapacityRow = serde_json::from_value(value).unwrap();
        assert_eq!(legacy.wrap_identity, None);
        assert_eq!(legacy.proof_equals_reference, None);
        assert_eq!(legacy.schema_version, 1);
    }

    #[test]
    fn cpu_w5_wrap_capacity_compares_bundle_fields() {
        let mut reference = WrapReference {
            wrap: "2p21".into(),
            proof_json: b"proof".to_vec(),
            commitment_mode_json: b"mode".to_vec(),
        };
        assert!(reference.matches(b"proof", b"mode"));
        assert!(!reference.matches(b"other", b"mode"));
        assert!(!reference.matches(b"proof", b"other"));
        assert!(!reference.matches(b"proofmode", b"mode"));
        reference.wrap = "2p22".into();
        assert!(!reference.matches(b"proof", b"mode"));
    }

    #[test]
    fn cpu_w4_feeder_qualification_and_bracket() {
        let complete = |arena_gib| -> BTreeMap<String, CapacityRow> {
            candidate_case_keys(Family::Feeder, arena_gib)
                .into_iter()
                .map(|key| (key.clone(), passing_row(&key)))
                .collect()
        };
        let mut rows = complete(30);
        qualify_feeder_capacity(&rows, REVISION, 30).unwrap();
        assert!(qualify_feeder_capacity(&rows, REVISION, 21)
            .unwrap_err()
            .contains("is missing"));
        rows.extend(complete(21));
        rows.extend(complete(17));
        let failing_17 = candidate_case_keys(Family::Feeder, 17)[0].clone();
        rows.insert(failing_17.clone(), oom(passing_row(&failing_17)));
        let failing_16 = candidate_case_keys(Family::Feeder, 16)[3].clone();
        rows.insert(failing_16.clone(), oom(passing_row(&failing_16)));
        assert_eq!(feeder_floor_bracket(&rows, REVISION), Ok((21, Some(17))));

        let key_30 = candidate_case_keys(Family::Feeder, 30)[5].clone();
        let mut failing = rows.clone();
        failing.insert(key_30.clone(), oom(passing_row(&key_30)));
        assert!(qualify_feeder_capacity(&failing, REVISION, 30)
            .unwrap_err()
            .contains("does not fit"));
        assert!(feeder_floor_bracket(&failing, REVISION)
            .unwrap_err()
            .contains("fails above"));
        let mut incomplete = rows.clone();
        incomplete.remove(&candidate_case_keys(Family::Feeder, 21)[2]);
        assert!(feeder_floor_bracket(&incomplete, REVISION)
            .unwrap_err()
            .contains("incomplete"));
        let mut stale = rows.clone();
        stale.get_mut(&key_30).unwrap().lde_factor = Some(1);
        assert!(qualify_feeder_capacity(&stale, REVISION, 30)
            .unwrap_err()
            .contains("trace geometry differs"));
        let mut overridden = rows.clone();
        overridden.get_mut(&key_30).unwrap().partial_trees = Some(5);
        assert!(qualify_feeder_capacity(&overridden, REVISION, 30)
            .unwrap_err()
            .contains("partial-tree override"));
        assert!(feeder_floor_bracket(&overridden, REVISION)
            .unwrap_err()
            .contains("partial-tree override"));
        assert!(is_feeder_bracket_arena(20));
        assert!(!is_feeder_bracket_arena(0));
        assert!(!is_feeder_bracket_arena(FEEDER_CANDIDATES_GIB[0]));
    }

    /// W4's feeder-only writeback: every case at the qualifying arena fits, the
    /// candidate rows select the public floor, and bracket rows stay diagnostic.
    #[test]
    #[ignore]
    fn cpu_w4_feeder_capacity_writeback() {
        let dir = PathBuf::from(required_env("W4_CAPACITY_ROWS"));
        let revision = required_env("W4_CAPACITY_REVISION");
        let qualifying_gib: usize = required_env("W4_CAPACITY_QUALIFYING_GIB")
            .parse()
            .expect("W4_CAPACITY_QUALIFYING_GIB is an integer");
        let mut rows = BTreeMap::<String, CapacityRow>::new();
        let mut sources = BTreeMap::<String, PathBuf>::new();
        for entry in std::fs::read_dir(&dir)
            .unwrap_or_else(|error| panic!("capacity rows read {}: {error}", dir.display()))
        {
            let path = entry.expect("capacity rows entry").path();
            if path.extension().is_none_or(|extension| extension != "json") {
                continue;
            }
            let row = read_row(&path);
            if let Some(previous) = sources.insert(row.case.clone(), path.clone()) {
                panic!(
                    "capacity case {} is recorded twice: {} and {}",
                    row.case,
                    previous.display(),
                    path.display()
                );
            }
            rows.insert(row.case.clone(), row);
        }
        qualify_feeder_capacity(&rows, &revision, qualifying_gib).unwrap();
        let (bracket, candidates): (BTreeMap<_, _>, BTreeMap<_, _>) = rows
            .clone()
            .into_iter()
            .partition(|(_, row)| is_feeder_bracket_arena(row.arena_bytes >> 30));
        let selected = select_capacity(Family::Feeder, &candidates, &revision).unwrap();
        let (lowest_passing, highest_failing) = feeder_floor_bracket(&rows, &revision).unwrap();
        println!(
            "L1 feeder capacity: {qualifying_gib} GiB qualified, {selected} GiB selected, floor bracket {lowest_passing} GiB passing / {highest_failing:?} GiB failing ({} bracket rows)",
            bracket.len()
        );
        assert_eq!(presets::l1_feeder::L1_FEEDER_FLOOR_BYTES, selected << 30);
        assert_eq!(presets::l1_feeder::L1_FEEDER_FLOOR_SOURCE, "measured");
    }

    /// W5's wrap-only writeback; qualifying measurements must include proof parity.
    #[test]
    #[ignore]
    fn cpu_w5_wrap_capacity_writeback() {
        let dir = PathBuf::from(required_env("W5_CAPACITY_ROWS"));
        let revision = required_env("W5_CAPACITY_REVISION");
        let qualifying_gib: usize = required_env("W5_CAPACITY_QUALIFYING_GIB")
            .parse()
            .expect("W5_CAPACITY_QUALIFYING_GIB is an integer");
        let mut rows = BTreeMap::<String, CapacityRow>::new();
        let mut sources = BTreeMap::<String, PathBuf>::new();
        for entry in std::fs::read_dir(&dir)
            .unwrap_or_else(|error| panic!("capacity rows read {}: {error}", dir.display()))
        {
            let path = entry.expect("capacity rows entry").path();
            if path.extension().is_none_or(|extension| extension != "json") {
                continue;
            }
            let row = read_row(&path);
            if let Some(previous) = sources.insert(row.case.clone(), path.clone()) {
                panic!(
                    "capacity case {} is recorded twice: {} and {}",
                    row.case,
                    previous.display(),
                    path.display()
                );
            }
            rows.insert(row.case.clone(), row);
        }
        println!(
            "L1 wrap capacity: read {} rows ({} feeder-stage rows ignored)",
            rows.len(),
            rows.values().filter(|row| row.stage != Stage::Wrap).count()
        );
        let selected = qualify_wrap_capacity(&rows, &revision, qualifying_gib).unwrap();
        println!("L1 wrap capacity: {qualifying_gib} GiB qualified, {selected} GiB selected with proof parity");
        assert_eq!(
            presets::l1_wrap::L1_WRAP_WHOLE_PROOF_FLOOR_BYTES,
            selected << 30
        );
        assert_eq!(presets::l1_wrap::L1_WRAP_FLOOR_SOURCE, "measured");
    }
}
