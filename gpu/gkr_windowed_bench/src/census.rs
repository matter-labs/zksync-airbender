use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gpu_gkr_compiler::backward::{
    decode_continuation_program, decode_r0_program, CoeffLayer, LeanAtom, LeanProgram,
    LeanSourceBinding, LeanTerm, SOURCE_NONE,
};
use gpu_gkr_compiler::{
    compile_continuations, compile_r0, ContinuationLayerProgram, R0LayerProgram,
};
use serde::{Deserialize, Serialize};

use crate::lazy_segments::plan_lazy_segments;

pub const CENSUS_SCHEMA_VERSION: u32 = 1;

pub const CORPUS: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_g_function_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "inits_and_teardowns_layout_gkr.json",
    "jump_branch_slt_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "mem_subword_only_layout_gkr.json",
    "mem_word_only_layout_gkr.json",
    "shift_binop_layout_gkr.json",
    "unified_reduced_machine_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
];

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum BackwardRegime {
    R0,
    Ext,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoordinateId {
    pub circuit: String,
    pub layer: u32,
    pub regime: BackwardRegime,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InputHash {
    pub path: String,
    pub sha256: String,
}

pub(crate) struct CompiledCorpusLayer {
    pub circuit: String,
    pub layer: usize,
    pub trace_len: u64,
    pub canonical: gkr_eval_ir::DagLayer,
    pub r0: R0LayerProgram,
    pub ext: ContinuationLayerProgram,
}

pub(crate) struct CompiledCorpus {
    pub input_sha256: Vec<InputHash>,
    pub layers: Vec<CompiledCorpusLayer>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct HistogramBucket {
    pub key: String,
    pub count: u32,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RunHistograms {
    pub joint: Vec<HistogramBucket>,
    pub handler: Vec<HistogramBucket>,
    pub immediate: Vec<HistogramBucket>,
    pub coefficient: Vec<HistogramBucket>,
    pub source_kind: Vec<HistogramBucket>,
    pub strict_source: Vec<HistogramBucket>,
    pub singleton: Vec<HistogramBucket>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReuseCensus {
    pub source_uses: u32,
    pub unique_sources: u32,
    pub repeated_source_uses: u32,
    pub ideal_cache_loads: u32,
    pub ideal_cache_saved_loads: u32,
    pub max_source_reuse: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticRow {
    pub domain_rows: u64,
    pub passes_per_invocation: u32,
    pub terms: u32,
    pub atoms: u32,
    pub bf_atoms: u32,
    pub e4_atoms: u32,
    pub legacy_records: u32,
    pub groups: u32,
    pub singletons: u32,
    pub product_prefix_lengths: Vec<u16>,
    pub inner_segment_ends: Vec<Vec<u16>>,
    pub peeled_first_members: u32,
    pub accumulate_members: u32,
    pub canonical_runs: RunHistograms,
    pub reuse: ReuseCensus,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct HandlerCoverage {
    pub direct_records: u32,
    pub same_window_records: u32,
    pub same_window_record_ids: Vec<u16>,
    pub escape_records: u32,
    pub permutation_eligible_records: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompilerBindingRow {
    pub windows: u16,
    pub max_window_relative_column: u16,
    pub source_slots: u32,
    pub post_lazy_runs: RunHistograms,
    pub per_record_same_window_runs: RunHistograms,
    pub legal_permutation_runs: RunHistograms,
    pub handler_coverage: HandlerCoverage,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BenchmarkLimitFit {
    pub source_slots: bool,
    pub immediates: bool,
    pub coefficients: bool,
    pub records: bool,
    pub windows: bool,
    pub columns_per_window: bool,
    pub compact_words: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct InstructionTaxonomy {
    pub ldc: u64,
    pub extraction: u64,
    pub dispatch: u64,
    pub immediate: u64,
    pub reduction: u64,
    pub source_resolution: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BenchmarkEncodingRow {
    pub coefficients: u32,
    pub immediates: u32,
    pub records: u32,
    pub limit_fit: BenchmarkLimitFit,
    pub direct_words: u32,
    pub same_window_words: u32,
    pub escape_words: u32,
    pub padding_words: u32,
    pub estimated_instructions: InstructionTaxonomy,
    pub add_sub_calibration_residual: Option<i64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CensusFailure {
    pub kind: String,
    pub required: u64,
    pub maximum: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CensusCoordinate {
    pub id: CoordinateId,
    pub semantic: SemanticRow,
    pub compiler_binding: Result<CompilerBindingRow, CensusFailure>,
    pub benchmark_encoding: Result<BenchmarkEncodingRow, CensusFailure>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CorpusCensusV1 {
    pub schema_version: u32,
    pub input_sha256: Vec<InputHash>,
    pub weights: WorkloadWeightsV1,
    pub coordinates: Vec<CensusCoordinate>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BaseInvocationCounts {
    pub add_sub: u64,
    pub jump: u64,
    pub mem_word: u64,
    pub mem_subword: u64,
    pub shift: u64,
    pub mul_div: u64,
    pub initial: u64,
    pub keccak: u64,
    pub bigint: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorkloadLayer {
    pub identity: String,
    pub circuit: String,
    pub invocations: u64,
    pub domain_rows: u64,
    pub estimated_passes: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum DevelopmentRecursionProfile {
    Available {
        source: String,
        log_sha256: String,
        layers: Vec<WorkloadLayer>,
    },
    Unavailable {
        reason: String,
        log_sha256: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorkloadProfiles {
    pub current_base: BaseInvocationCounts,
    pub development_recursion_proxy: DevelopmentRecursionProfile,
    pub future_current_recursion: Option<Vec<WorkloadLayer>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorkloadWeightsV1 {
    pub schema_version: u32,
    pub profiles: WorkloadProfiles,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WorkloadWeightError {
    WrongSchemaVersion { observed: u32 },
    EmptyAvailableProfile { profile: &'static str },
}

impl core::fmt::Display for WorkloadWeightError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for WorkloadWeightError {}

impl WorkloadWeightsV1 {
    pub fn validate(&self) -> Result<(), WorkloadWeightError> {
        if self.schema_version != CENSUS_SCHEMA_VERSION {
            return Err(WorkloadWeightError::WrongSchemaVersion {
                observed: self.schema_version,
            });
        }
        if matches!(
            &self.profiles.development_recursion_proxy,
            DevelopmentRecursionProfile::Available { layers, .. } if layers.is_empty()
        ) {
            return Err(WorkloadWeightError::EmptyAvailableProfile {
                profile: "development_recursion_proxy",
            });
        }
        if matches!(&self.profiles.future_current_recursion, Some(layers) if layers.is_empty()) {
            return Err(WorkloadWeightError::EmptyAvailableProfile {
                profile: "future_current_recursion",
            });
        }
        Ok(())
    }
}

pub fn default_workload_weights() -> WorkloadWeightsV1 {
    WorkloadWeightsV1 {
        schema_version: CENSUS_SCHEMA_VERSION,
        profiles: WorkloadProfiles {
            current_base: BaseInvocationCounts {
                add_sub: 15,
                jump: 8,
                mem_word: 9,
                mem_subword: 3,
                shift: 4,
                mul_div: 1,
                initial: 1,
                keccak: 15,
                bigint: 3,
            },
            development_recursion_proxy: DevelopmentRecursionProfile::Unavailable {
                reason: "development recursion log has not been captured".to_owned(),
                log_sha256: "unavailable".to_owned(),
            },
            future_current_recursion: None,
        },
    }
}

struct ObservedLayer {
    identity: String,
    binary_key: u32,
    counts: BTreeMap<String, u64>,
}

fn observed_layers(log: &str) -> Result<Vec<ObservedLayer>, CensusError> {
    const START: &str = "PROVER producing memory commitments for binary with key ";
    const MARKER: &str = "produced memory commitment for circuit ";
    if let Some(line) = log.lines().find(|line| line.contains("proving stages took")) {
        let unrolled_start = line.find("unrolled [").map(|offset| offset + "unrolled [".len());
        if let Some(begin) = unrolled_start {
            let end = line[begin..].find(']').map(|offset| begin + offset).ok_or_else(|| {
                CensusError(format!("proving-stages line has malformed unrolled list: {line}"))
            })?;
            if !line[begin..end].trim().is_empty() {
                return Err(CensusError(format!(
                    "log reports unrolled recursion stages, which this census cannot label: {line}"
                )));
            }
        }
    }
    let mut layers: Vec<ObservedLayer> = Vec::new();
    let mut unified = 0u32;
    for line in log.lines() {
        if let Some(offset) = line.find(START) {
            let binary_key = line[offset + START.len()..]
                .split_whitespace()
                .next()
                .ok_or_else(|| CensusError(format!("layer line has no binary key: {line}")))?
                .parse::<u32>()
                .map_err(|error| CensusError(format!("invalid binary key in {line}: {error}")))?;
            let identity = if layers.is_empty() {
                "base".to_owned()
            } else {
                unified += 1;
                format!("recursion_unified_{unified}")
            };
            layers.push(ObservedLayer {
                identity,
                binary_key,
                counts: BTreeMap::new(),
            });
            continue;
        }
        if let Some(offset) = line.find(MARKER) {
            let suffix = &line[offset + MARKER.len()..];
            let index_start = suffix.rfind('[').ok_or_else(|| {
                CensusError(format!("memory-commitment line has no instance: {line}"))
            })?;
            let circuit = suffix[..index_start].to_owned();
            let layer = layers.last_mut().ok_or_else(|| {
                CensusError(format!("memory commitment precedes any layer marker: {line}"))
            })?;
            *layer.counts.entry(circuit).or_default() += 1;
        }
    }
    if layers.is_empty() || layers.iter().all(|layer| layer.counts.is_empty()) {
        return Err(CensusError(
            "workload log has no memory-commitment listings".to_owned(),
        ));
    }
    Ok(layers)
}

fn required_count(counts: &mut BTreeMap<String, u64>, circuit: &str) -> Result<u64, CensusError> {
    counts
        .remove(circuit)
        .ok_or_else(|| CensusError(format!("current-base layer is missing {circuit}")))
}

fn current_base_counts(base: &ObservedLayer) -> Result<BaseInvocationCounts, CensusError> {
    if base.identity != "base" || base.binary_key != 0 {
        return Err(CensusError(format!(
            "first observed layer is not the base layer: identity={} key={}",
            base.identity, base.binary_key
        )));
    }
    let mut counts = base.counts.clone();
    let result = BaseInvocationCounts {
        add_sub: required_count(&mut counts, "Unrolled(NonMemory(AddSubLuiAuipcMop))")?,
        jump: required_count(&mut counts, "Unrolled(NonMemory(JumpBranchSlt))")?,
        mem_word: required_count(&mut counts, "Unrolled(Memory(LoadStoreWordOnly))")?,
        mem_subword: required_count(&mut counts, "Unrolled(Memory(LoadStoreSubwordOnly))")?,
        shift: required_count(&mut counts, "Unrolled(NonMemory(ShiftBinary))")?,
        mul_div: required_count(&mut counts, "Unrolled(NonMemory(MulDivUnsigned))")?,
        initial: required_count(&mut counts, "Unrolled(InitsAndTeardowns)")?,
        keccak: required_count(&mut counts, "Delegation(KeccakSpecial5)")?,
        bigint: required_count(&mut counts, "Delegation(BigIntWithControl)")?,
    };
    if !counts.is_empty() {
        return Err(CensusError(format!(
            "current-base layer has unexpected circuit listings: {:?}",
            counts.keys().collect::<Vec<_>>()
        )));
    }
    let expected = default_workload_weights().profiles.current_base;
    if result != expected {
        return Err(CensusError(format!(
            "current-base counts drifted: observed={result:?} expected={expected:?}"
        )));
    }
    Ok(result)
}

fn workload_circuit(circuit: &str) -> Option<&'static str> {
    match circuit {
        "Unrolled(NonMemory(AddSubLuiAuipcMop))" => Some("add_sub_lui_auipc_mop"),
        "Delegation(BigIntWithControl)" => Some("bigint_with_extended_control"),
        "Delegation(Blake2WithCompression)" => Some("blake2_with_extended_control"),
        "Unrolled(InitsAndTeardowns)" => Some("inits_and_teardowns"),
        "Unrolled(NonMemory(JumpBranchSlt))" => Some("jump_branch_slt"),
        "Delegation(KeccakSpecial5)" => Some("keccak_special5"),
        "Unrolled(Memory(LoadStoreSubwordOnly))" => Some("mem_subword_only"),
        "Unrolled(Memory(LoadStoreWordOnly))" => Some("mem_word_only"),
        "Unrolled(NonMemory(ShiftBinary))" => Some("shift_binop"),
        "Unrolled(NonMemory(MulDivUnsigned))" => Some("unsigned_mul_div"),
        "Unrolled(Unified)" => Some("unified_reduced_machine"),
        _ => None,
    }
}

fn corpus_trace_lengths() -> Result<BTreeMap<String, u64>, CensusError> {
    let directory = corpus_directory();
    CORPUS
        .iter()
        .map(|layout_name| {
            let path = directory.join(layout_name);
            let bytes = std::fs::read(&path)
                .map_err(|error| CensusError(format!("read {}: {error}", path.display())))?;
            let artifact: GKRCircuitArtifact<BabyBearField> = serde_json::from_slice(&bytes)
                .map_err(|error| CensusError(format!("parse {layout_name}: {error}")))?;
            Ok((circuit_name(layout_name), artifact.trace_len as u64))
        })
        .collect()
}

pub fn workload_weights_from_log(log_path: &Path) -> Result<WorkloadWeightsV1, CensusError> {
    let text = std::fs::read_to_string(log_path)
        .map_err(|error| CensusError(format!("read {}: {error}", log_path.display())))?;
    let observed = observed_layers(&text)?;
    let current_base = current_base_counts(&observed[0])?;
    let trace_lengths = corpus_trace_lengths()?;
    let mut layers = Vec::new();
    for observed_layer in &observed {
        for (raw_circuit, invocations) in &observed_layer.counts {
            let circuit = workload_circuit(raw_circuit).ok_or_else(|| {
                CensusError(format!("workload log has unmapped circuit {raw_circuit}"))
            })?;
            let domain_rows = trace_lengths.get(circuit).copied().ok_or_else(|| {
                CensusError(format!("workload circuit {circuit} has no census layout"))
            })?;
            layers.push(WorkloadLayer {
                identity: observed_layer.identity.clone(),
                circuit: circuit.to_owned(),
                invocations: *invocations,
                domain_rows,
                estimated_passes: 1,
            });
        }
    }
    let weights = WorkloadWeightsV1 {
        schema_version: CENSUS_SCHEMA_VERSION,
        profiles: WorkloadProfiles {
            current_base,
            development_recursion_proxy: DevelopmentRecursionProfile::Unavailable {
                reason: "superseded by the single-log current recursion profile".to_owned(),
                log_sha256: "retired".to_owned(),
            },
            future_current_recursion: Some(layers),
        },
    };
    weights
        .validate()
        .map_err(|error| CensusError(error.to_string()))?;
    Ok(weights)
}

#[derive(Debug)]
pub struct CensusError(String);

impl core::fmt::Display for CensusError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for CensusError {}

#[derive(Clone)]
struct TermView {
    term: LeanTerm,
    handler: String,
    immediate: String,
    coefficient: String,
    source_kind: String,
    source_a: Option<u16>,
    source_b: Option<u16>,
    class_order: u8,
}

fn corpus_directory() -> PathBuf {
    crate::runtime_paths::compiled_circuits_directory()
}

fn circuit_name(layout: &str) -> String {
    layout
        .strip_suffix("_layout_gkr.json")
        .unwrap_or(layout)
        .to_owned()
}

fn sha256(path: &Path) -> Result<String, CensusError> {
    let output = Command::new("sha256sum")
        .arg(path)
        .output()
        .map_err(|error| CensusError(format!("run sha256sum for {}: {error}", path.display())))?;
    if !output.status.success() {
        return Err(CensusError(format!(
            "sha256sum failed for {}",
            path.display()
        )));
    }
    let text = String::from_utf8(output.stdout)
        .map_err(|error| CensusError(format!("sha256sum output is not UTF-8: {error}")))?;
    let hash = text.split_whitespace().next().unwrap_or_default();
    if hash.len() != 64 || !hash.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(CensusError(format!(
            "invalid SHA-256 for {}",
            path.display()
        )));
    }
    Ok(hash.to_owned())
}

fn sha256_bytes(bytes: &[u8], label: &str) -> Result<String, CensusError> {
    let mut child = Command::new("sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|error| CensusError(format!("run sha256sum for {label}: {error}")))?;
    child
        .stdin
        .take()
        .ok_or_else(|| CensusError(format!("open sha256sum stdin for {label}")))?
        .write_all(bytes)
        .map_err(|error| CensusError(format!("hash {label}: {error}")))?;
    let output = child
        .wait_with_output()
        .map_err(|error| CensusError(format!("wait for sha256sum for {label}: {error}")))?;
    if !output.status.success() {
        return Err(CensusError(format!("sha256sum failed for {label}")));
    }
    let text = String::from_utf8(output.stdout)
        .map_err(|error| CensusError(format!("sha256sum output is not UTF-8: {error}")))?;
    let hash = text.split_whitespace().next().unwrap_or_default();
    if hash.len() != 64 || !hash.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(CensusError(format!("invalid SHA-256 for {label}")));
    }
    Ok(hash.to_owned())
}

fn source_coordinate(binding: &LeanSourceBinding, source: u16) -> Option<u16> {
    if source == SOURCE_NONE {
        return None;
    }
    let slot = binding.source_slots.get(usize::from(source))?;
    (usize::from(slot.window) < 64 && slot.column < 128)
        .then_some((u16::from(slot.window) << 7) | slot.column)
}

fn source_kind(binding: &LeanSourceBinding, source: u16) -> &'static str {
    let Some(slot) = binding.source_slots.get(usize::from(source)) else {
        return "none";
    };
    let Some(window) = binding.windows.get(usize::from(slot.window)) else {
        return "invalid";
    };
    if window.is_procedural() {
        "procedural"
    } else if window.backing_field() == gkr_eval_ir::FieldKind::Base {
        "base"
    } else {
        "ext"
    }
}

fn view_term(term: LeanTerm, binding: &LeanSourceBinding, group_member: bool) -> TermView {
    let kind_a = source_kind(binding, term.source_a);
    let kind_b = source_kind(binding, term.source_b);
    let direct_a = source_coordinate(binding, term.source_a);
    let direct_b = source_coordinate(binding, term.source_b);
    let procedural_kind = |source: u16| {
        let slot = binding.source_slots.get(usize::from(source))?;
        binding
            .windows
            .get(usize::from(slot.window))?
            .procedural_kind()
            .map(u16::from)
    };
    let (handler, source_a, source_b, class_order) = if term.source_b == SOURCE_NONE {
        if kind_a == "procedural" {
            (
                "linear_bf_procedural",
                procedural_kind(term.source_a),
                None,
                4,
            )
        } else if kind_a == "ext" {
            ("linear_e4", direct_a, None, 1)
        } else {
            ("linear_bf", direct_a, None, 0)
        }
    } else {
        match (kind_a, kind_b) {
            ("procedural", "base") => (
                "product_bf_bf_procedural",
                direct_b,
                procedural_kind(term.source_a),
                8,
            ),
            ("base", "procedural") => (
                "product_bf_bf_procedural",
                direct_a,
                procedural_kind(term.source_b),
                8,
            ),
            ("ext", "ext") => ("product_e4_e4", direct_a, direct_b, 5),
            ("base", "base") => ("product_bf_bf", direct_a, direct_b, 2),
            ("base", "ext") => ("product_bf_e4", direct_a, direct_b, 3),
            ("ext", "base") => ("product_bf_e4", direct_b, direct_a, 3),
            _ => ("unsupported", direct_a, direct_b, u8::MAX),
        }
    };
    let immediate = match term.coeff {
        0 => "+1".to_owned(),
        1 => "-1".to_owned(),
        value if group_member => format!("immediate:{value}"),
        _ => "banked".to_owned(),
    };
    TermView {
        term,
        handler: handler.to_owned(),
        immediate,
        coefficient: if group_member {
            "group-core".to_owned()
        } else {
            format!("coefficient:{}", term.coeff)
        },
        source_kind: if term.source_b == SOURCE_NONE {
            kind_a.to_owned()
        } else {
            format!("{kind_a}+{kind_b}")
        },
        source_a,
        source_b,
        class_order,
    }
}

fn atom_views(atoms: &[LeanAtom], binding: &LeanSourceBinding) -> Vec<Vec<TermView>> {
    atoms
        .iter()
        .map(|atom| match atom {
            LeanAtom::Term(term) => vec![view_term(*term, binding, false)],
            LeanAtom::Group { members, .. } => members
                .iter()
                .map(|term| view_term(*term, binding, true))
                .collect(),
        })
        .collect()
}

fn is_bf(view: &TermView) -> bool {
    matches!(
        view.handler.as_str(),
        "linear_bf" | "product_bf_bf" | "linear_bf_procedural" | "product_bf_bf_procedural"
    )
}

fn is_compact_bf(view: &TermView) -> bool {
    matches!(view.handler.as_str(), "linear_bf" | "product_bf_bf")
}

fn post_lazy_views(mut atoms: Vec<Vec<TermView>>) -> Vec<Vec<TermView>> {
    for members in &mut atoms {
        if members.len() >= 2 && members.iter().all(is_bf) {
            members.sort_unstable_by_key(|view| {
                (
                    match view.handler.as_str() {
                        "product_bf_bf" => 0,
                        "linear_bf" => 1,
                        _ => 2,
                    },
                    match view.term.coeff {
                        0 => 0,
                        1 => 1,
                        _ => 2,
                    },
                    view.source_a,
                    view.source_b,
                    view.term.coeff,
                )
            });
        }
    }
    atoms
}

fn source_scheduled_views(atoms: &[LeanAtom], binding: &LeanSourceBinding) -> Vec<Vec<TermView>> {
    let mut scheduled = atoms
        .iter()
        .zip(atom_views(atoms, binding))
        .map(|(atom, mut members)| {
            if members.len() > 1 {
                members.sort_unstable_by_key(|view| {
                    (
                        view.source_a.unwrap_or(SOURCE_NONE),
                        view.source_b.unwrap_or(SOURCE_NONE),
                        view.class_order,
                        match view.term.coeff {
                            0 => 0,
                            1 => 1,
                            _ => 2,
                        },
                        view.term.coeff,
                    )
                });
            }
            let core = match atom {
                LeanAtom::Term(term) => term.coeff,
                LeanAtom::Group { core, .. } => *core,
            };
            (core, members)
        })
        .collect::<Vec<_>>();
    scheduled.sort_unstable_by_key(|(core, members)| {
        (
            u8::from(!members.iter().all(is_bf)),
            u8::from(members.iter().any(|view| {
                matches!(
                    view.handler.as_str(),
                    "linear_bf_procedural" | "product_bf_bf_procedural"
                )
            })),
            members
                .iter()
                .map(|view| {
                    (
                        view.source_a.unwrap_or(SOURCE_NONE),
                        view.source_b.unwrap_or(SOURCE_NONE),
                    )
                })
                .collect::<Vec<_>>(),
            u8::from(members.len() > 1),
            members
                .iter()
                .map(|view| view.class_order)
                .collect::<Vec<_>>(),
            members.len(),
            *core,
        )
    });
    scheduled.into_iter().map(|(_, members)| members).collect()
}

fn histogram(values: impl IntoIterator<Item = String>) -> Vec<HistogramBucket> {
    let mut lengths = BTreeMap::<String, u32>::new();
    let mut values = values.into_iter();
    let Some(mut previous) = values.next() else {
        return Vec::new();
    };
    let mut run = 1u32;
    for value in values {
        if value == previous {
            run += 1;
        } else {
            *lengths.entry(run.to_string()).or_default() += 1;
            previous = value;
            run = 1;
        }
    }
    let _ = previous;
    *lengths.entry(run.to_string()).or_default() += 1;
    lengths
        .into_iter()
        .map(|(key, count)| HistogramBucket { key, count })
        .collect()
}

fn run_histograms(atoms: &[Vec<TermView>]) -> RunHistograms {
    let flat = atoms.iter().flatten().collect::<Vec<_>>();
    let singleton = atoms
        .iter()
        .filter(|members| members.len() == 1)
        .map(|members| format!("{}|{}", members[0].handler, members[0].immediate));
    RunHistograms {
        joint: histogram(flat.iter().map(|view| {
            format!(
                "{}|{}|{}|{}",
                view.handler, view.immediate, view.coefficient, view.source_kind
            )
        })),
        handler: histogram(flat.iter().map(|view| view.handler.clone())),
        immediate: histogram(flat.iter().map(|view| view.immediate.clone())),
        coefficient: histogram(flat.iter().map(|view| view.coefficient.clone())),
        source_kind: histogram(flat.iter().map(|view| view.source_kind.clone())),
        strict_source: histogram(
            flat.iter()
                .map(|view| format!("{:?}:{:?}", view.source_a, view.source_b)),
        ),
        singleton: histogram(singleton),
    }
}

fn prefix_plans(atoms: &[Vec<TermView>]) -> (Vec<u16>, Vec<Vec<u16>>) {
    let mut lengths = Vec::new();
    let mut ends = Vec::new();
    for members in atoms {
        if members.len() < 2 || !members.iter().all(is_bf) {
            continue;
        }
        let count = members
            .iter()
            .take_while(|view| view.handler == "product_bf_bf")
            .count();
        if count >= 2 {
            let plan = plan_lazy_segments(count).expect("compiler group arity fits u16");
            lengths.push(plan.product_count);
            ends.push(plan.segment_ends);
        }
    }
    (lengths, ends)
}

fn reuse_census(atoms: &[Vec<TermView>]) -> ReuseCensus {
    let mut counts = BTreeMap::<u16, u32>::new();
    for view in atoms.iter().flatten() {
        for source in [view.term.source_a, view.term.source_b] {
            if source != SOURCE_NONE {
                *counts.entry(source).or_default() += 1;
            }
        }
    }
    let source_uses = counts.values().sum();
    let unique_sources = counts.len() as u32;
    ReuseCensus {
        source_uses,
        unique_sources,
        repeated_source_uses: source_uses.saturating_sub(unique_sources),
        ideal_cache_loads: unique_sources,
        ideal_cache_saved_loads: source_uses.saturating_sub(unique_sources),
        max_source_reuse: counts.values().copied().max().unwrap_or(0),
    }
}

fn same_window(view: &TermView) -> bool {
    if !is_compact_bf(view) {
        return false;
    }
    match (view.source_a, view.source_b) {
        (Some(a), Some(b)) => a >> 7 == b >> 7,
        (Some(_), None) => true,
        _ => false,
    }
}

fn handler_coverage(atoms: &[Vec<TermView>]) -> HandlerCoverage {
    let mut coverage = HandlerCoverage::default();
    let mut same_window_record_ids = BTreeSet::new();
    let mut canonical_head = 0u16;
    for members in atoms {
        let records = members.len() as u32 + u32::from(members.len() > 1);
        for view in members {
            if is_compact_bf(view) {
                coverage.direct_records += 1;
            } else {
                coverage.escape_records += 1;
            }
        }
        if members.len() > 1 && members.iter().all(is_compact_bf) {
            coverage.direct_records += 1;
            coverage.permutation_eligible_records += records;

            let product_prefix = members
                .iter()
                .take_while(|view| view.handler == "product_bf_bf")
                .count();
            let mut start = 0usize;
            while product_prefix >= 2 && start < product_prefix {
                let coefficient = members[start].term.coeff;
                let mut end = start + 1;
                while end < product_prefix && members[end].term.coeff == coefficient {
                    end += 1;
                }
                let window_pair = members[start]
                    .source_a
                    .zip(members[start].source_b)
                    .map(|(source_a, source_b)| (source_a >> 7, source_b >> 7));
                if window_pair.is_some()
                    && members[start..end].iter().all(|view| {
                        view.source_a
                            .zip(view.source_b)
                            .map(|(source_a, source_b)| (source_a >> 7, source_b >> 7))
                            == window_pair
                    })
                {
                    same_window_record_ids
                        .extend((start..end).map(|member| canonical_head + 1 + member as u16));
                }
                start = end;
            }
        } else if members.len() > 1 {
            coverage.escape_records += 1;
        }
        canonical_head += records as u16;
    }
    coverage.same_window_records = same_window_record_ids.len() as u32;
    coverage.same_window_record_ids = same_window_record_ids.into_iter().collect();
    coverage
}

fn permuted_views(mut atoms: Vec<Vec<TermView>>) -> Vec<Vec<TermView>> {
    for members in &mut atoms {
        if members.len() < 2 || !members.iter().all(is_compact_bf) {
            continue;
        }
        let products = members
            .iter()
            .take_while(|view| view.handler == "product_bf_bf")
            .count();
        if products < 2 {
            continue;
        }
        let plan = plan_lazy_segments(products).expect("compiler group arity fits u16");
        let mut start = 0usize;
        for end in plan.segment_ends {
            members[start..usize::from(end)]
                .sort_by_key(|view| (view.immediate.clone(), view.source_a, view.source_b));
            start = usize::from(end);
        }
    }
    atoms
}

fn compact_word_counts(atoms: &[Vec<TermView>]) -> (u32, u32, u32) {
    let mut direct = 0u32;
    let mut same = 0u32;
    let mut escape = 0u32;
    for members in atoms {
        if members.len() == 1 {
            direct += 2;
            same += 2;
            escape += 2;
            continue;
        }
        if !members.iter().all(is_compact_bf) {
            let words = 2 * (members.len() as u32 + 1);
            direct += words;
            same += words;
            escape += words;
            continue;
        }
        let products = members
            .iter()
            .take_while(|view| view.handler == "product_bf_bf")
            .count();
        let linear = members.len() - products;
        if products < 2 {
            let words = 2 * (members.len() as u32 + 1);
            direct += words;
            same += words;
            escape += words;
            continue;
        }
        direct += 2;
        same += 2;
        let mut start = 0usize;
        while start < products {
            let immediate = &members[start].immediate;
            let mut end = start + 1;
            while end < products && members[end].immediate == *immediate {
                end += 1;
            }
            let run = &members[start..end];
            direct += 2 + run.len() as u32;
            let first_windows = run[0]
                .source_a
                .zip(run[0].source_b)
                .map(|(a, b)| (a >> 7, b >> 7));
            let one_window_pair = first_windows.is_some()
                && run.iter().all(|view| {
                    view.source_a
                        .zip(view.source_b)
                        .map(|(a, b)| (a >> 7, b >> 7))
                        == first_windows
                });
            same += 2 + if one_window_pair {
                run.len().div_ceil(2) as u32
            } else {
                run.len() as u32
            };
            start = end;
        }
        if linear != 0 {
            let escaped_tail = 2 + 2 * linear as u32;
            direct += escaped_tail;
            same += escaped_tail;
            escape += escaped_tail;
        }
    }
    (direct, same, escape)
}

fn semantic_row(
    program: &LeanProgram,
    atoms: &[LeanAtom],
    binding: &LeanSourceBinding,
) -> SemanticRow {
    let canonical = atom_views(atoms, binding);
    let post_lazy = post_lazy_views(source_scheduled_views(atoms, binding));
    let (product_prefix_lengths, inner_segment_ends) = prefix_plans(&post_lazy);
    let groups = atoms
        .iter()
        .filter(|atom| matches!(atom, LeanAtom::Group { .. }))
        .count() as u32;
    let bf_atoms = canonical
        .iter()
        .filter(|members| members.iter().all(is_bf))
        .count() as u32;
    let group_members = canonical
        .iter()
        .filter(|members| members.len() > 1)
        .map(Vec::len)
        .sum::<usize>();
    SemanticRow {
        domain_rows: 1,
        passes_per_invocation: 1,
        terms: u32::try_from(program.term_count).unwrap(),
        atoms: u32::try_from(atoms.len()).unwrap(),
        bf_atoms,
        e4_atoms: u32::try_from(atoms.len()).unwrap() - bf_atoms,
        legacy_records: u32::try_from(program.words.len() / 4).unwrap(),
        groups,
        singletons: u32::try_from(atoms.len()).unwrap() - groups,
        product_prefix_lengths,
        inner_segment_ends,
        peeled_first_members: groups,
        accumulate_members: u32::try_from(group_members).unwrap().saturating_sub(groups),
        canonical_runs: run_histograms(&canonical),
        reuse: reuse_census(&canonical),
    }
}

fn compiler_binding_row(atoms: &[LeanAtom], binding: &LeanSourceBinding) -> CompilerBindingRow {
    let post_lazy = post_lazy_views(source_scheduled_views(atoms, binding));
    let same_window_view = post_lazy
        .iter()
        .map(|members| {
            members
                .iter()
                .cloned()
                .map(|mut view| {
                    view.handler = format!(
                        "{}:{}",
                        view.handler,
                        if same_window(&view) { "same" } else { "direct" }
                    );
                    view
                })
                .collect()
        })
        .collect::<Vec<Vec<TermView>>>();
    CompilerBindingRow {
        windows: u16::try_from(binding.windows.len()).unwrap(),
        max_window_relative_column: binding
            .source_slots
            .iter()
            .map(|slot| slot.column)
            .max()
            .unwrap_or(0),
        source_slots: u32::try_from(binding.source_slots.len()).unwrap(),
        post_lazy_runs: run_histograms(&post_lazy),
        per_record_same_window_runs: run_histograms(&same_window_view),
        legal_permutation_runs: run_histograms(&permuted_views(post_lazy.clone())),
        handler_coverage: handler_coverage(&post_lazy),
    }
}

fn benchmark_encoding_row(
    layer: &CoeffLayer,
    program: &LeanProgram,
    atoms: &[LeanAtom],
    binding: &LeanSourceBinding,
) -> Result<BenchmarkEncodingRow, CensusFailure> {
    let post_lazy = post_lazy_views(source_scheduled_views(atoms, binding));
    let (direct_words, same_window_words, escape_words) = compact_word_counts(&post_lazy);
    let coefficients = u32::try_from(layer.coefficients.len() + 2).unwrap();
    let immediates = u32::try_from(layer.immediates.len()).unwrap();
    let records = u32::try_from(program.words.len() / 4).unwrap();
    let max_column = binding
        .source_slots
        .iter()
        .map(|slot| slot.column)
        .max()
        .unwrap_or(0);
    let backing_slots = binding
        .windows
        .iter()
        .map(|window| format!("{:?}", window.family))
        .collect::<BTreeSet<_>>()
        .len();
    let fit = BenchmarkLimitFit {
        source_slots: backing_slots <= 6,
        immediates: layer.immediates.len() <= 7,
        coefficients: coefficients <= 80,
        records: records <= 175,
        windows: binding.windows.len() <= 64,
        columns_per_window: max_column < 128,
        compact_words: direct_words <= 350,
    };
    let failure = [
        (!fit.source_slots).then_some(("address_slots", backing_slots as u64, 6)),
        (!fit.immediates).then_some(("immediates", layer.immediates.len() as u64, 7)),
        (!fit.coefficients).then_some(("coefficients", u64::from(coefficients), 80)),
        (!fit.records).then_some(("records", u64::from(records), 175)),
        (!fit.windows).then_some(("windows", binding.windows.len() as u64, 64)),
        (!fit.columns_per_window).then_some(("columns_per_window", u64::from(max_column), 127)),
        (!fit.compact_words).then_some(("compact_words", u64::from(direct_words), 350)),
    ]
    .into_iter()
    .flatten()
    .next();
    if let Some((kind, required, maximum)) = failure {
        return Err(CensusFailure {
            kind: kind.to_owned(),
            required,
            maximum,
        });
    }
    Ok(BenchmarkEncodingRow {
        coefficients,
        immediates,
        records,
        limit_fit: fit,
        direct_words,
        same_window_words,
        escape_words,
        padding_words: 350 - direct_words,
        estimated_instructions: InstructionTaxonomy {
            ldc: u64::from(direct_words),
            extraction: 2 * u64::from(direct_words),
            dispatch: u64::from(records),
            immediate: u64::from(immediates),
            reduction: post_lazy
                .iter()
                .filter_map(|members| {
                    let count = members
                        .iter()
                        .take_while(|view| view.handler == "product_bf_bf")
                        .count();
                    (count >= 2)
                        .then(|| plan_lazy_segments(count).unwrap().segment_ends.len() as u64)
                })
                .sum(),
            source_resolution: post_lazy
                .iter()
                .flatten()
                .map(|view| 1 + u64::from(view.source_b.is_some()))
                .sum(),
        },
        add_sub_calibration_residual: None,
    })
}

fn coordinate(
    circuit: &str,
    layer_index: usize,
    regime: BackwardRegime,
    layer: &CoeffLayer,
    program: &LeanProgram,
    binding: &LeanSourceBinding,
    atoms: Vec<LeanAtom>,
    domain_rows: u64,
) -> CensusCoordinate {
    let mut semantic = semantic_row(program, &atoms, binding);
    semantic.domain_rows = domain_rows;
    CensusCoordinate {
        id: CoordinateId {
            circuit: circuit.to_owned(),
            layer: u32::try_from(layer_index).unwrap(),
            regime,
        },
        semantic,
        compiler_binding: Ok(compiler_binding_row(&atoms, binding)),
        benchmark_encoding: if regime == BackwardRegime::R0 {
            Err(CensusFailure {
                kind: "r0_c2_only_semantics".to_owned(),
                required: 1,
                maximum: 0,
            })
        } else {
            benchmark_encoding_row(layer, program, &atoms, binding)
        },
    }
}

pub(crate) fn compile_corpus() -> Result<CompiledCorpus, CensusError> {
    let directory = corpus_directory();
    let mut input_sha256 = Vec::with_capacity(CORPUS.len());
    let mut layers = Vec::new();

    for layout_name in CORPUS {
        let path = directory.join(layout_name);
        let bytes = std::fs::read(&path)
            .map_err(|error| CensusError(format!("read {}: {error}", path.display())))?;
        input_sha256.push(InputHash {
            path: format!("../../cs/compiled_circuits/{layout_name}"),
            sha256: sha256_bytes(&bytes, layout_name)?,
        });
        let artifact: GKRCircuitArtifact<BabyBearField> = serde_json::from_slice(&bytes)
            .map_err(|error| CensusError(format!("parse {layout_name}: {error}")))?;
        let dag = gkr_eval_ir::lower_dag(&artifact)
            .map_err(|error| CensusError(format!("lower {layout_name}: {error}")))?;
        gkr_eval_ir::validate(&dag)
            .map_err(|error| CensusError(format!("validate {layout_name}: {error}")))?;
        let r0 = compile_r0(&dag)
            .map_err(|error| CensusError(format!("compile {layout_name} R0: {error:?}")))?;
        let ext = compile_continuations(&dag)
            .map_err(|error| CensusError(format!("compile {layout_name} Ext: {error:?}")))?;
        if r0.layers.len() != dag.layers.len() || ext.layers.len() != dag.layers.len() {
            return Err(CensusError(format!(
                "regime coverage mismatch for {layout_name}"
            )));
        }
        let circuit = circuit_name(layout_name);
        let trace_len = artifact.trace_len as u64;
        for (layer, (canonical, (r0, ext))) in dag
            .layers
            .into_iter()
            .zip(r0.layers.into_iter().zip(ext.layers))
            .enumerate()
        {
            if r0.layer != layer || ext.layer != layer {
                return Err(CensusError(format!(
                    "layer index mismatch for {layout_name}: expected={layer} r0={} ext={}",
                    r0.layer, ext.layer
                )));
            }
            layers.push(CompiledCorpusLayer {
                circuit: circuit.clone(),
                layer,
                trace_len,
                canonical,
                r0,
                ext,
            });
        }
    }
    layers.sort_by(|left, right| (&left.circuit, left.layer).cmp(&(&right.circuit, right.layer)));
    if layers.len() != 57 {
        return Err(CensusError(format!(
            "unexpected compiled corpus coverage: layers={}",
            layers.len()
        )));
    }
    Ok(CompiledCorpus {
        input_sha256,
        layers,
    })
}

pub fn generate_corpus_census(weights: WorkloadWeightsV1) -> Result<CorpusCensusV1, CensusError> {
    weights
        .validate()
        .map_err(|error| CensusError(error.to_string()))?;
    let CompiledCorpus {
        input_sha256,
        layers: compiled_layers,
    } = compile_corpus()?;
    let mut coordinates = Vec::new();

    for layer in compiled_layers {
        let r0_atoms = decode_r0_program(&layer.r0.program).map_err(|error| {
            CensusError(format!(
                "decode {} R0 L{}: {error:?}",
                layer.circuit, layer.layer
            ))
        })?;
        coordinates.push(coordinate(
            &layer.circuit,
            layer.layer,
            BackwardRegime::R0,
            &layer.r0.coefficients,
            &layer.r0.program,
            &layer.r0.binding,
            r0_atoms,
            layer.trace_len,
        ));
        let ext_atoms = decode_continuation_program(&layer.ext.program).map_err(|error| {
            CensusError(format!(
                "decode {} Ext L{}: {error:?}",
                layer.circuit, layer.layer
            ))
        })?;
        coordinates.push(coordinate(
            &layer.circuit,
            layer.layer,
            BackwardRegime::Ext,
            &layer.ext.coefficients,
            &layer.ext.program,
            &layer.ext.binding,
            ext_atoms,
            layer.trace_len,
        ));
    }
    coordinates.sort_by(|left, right| {
        (&left.id.circuit, left.id.layer, left.id.regime).cmp(&(
            &right.id.circuit,
            right.id.layer,
            right.id.regime,
        ))
    });
    let layers = coordinates
        .iter()
        .map(|coordinate| (coordinate.id.circuit.clone(), coordinate.id.layer))
        .collect::<BTreeSet<_>>();
    if layers.len() != 57 || coordinates.len() != 2 * layers.len() || coordinates.len() != 114 {
        return Err(CensusError(format!(
            "unexpected corpus coverage: layers={} coordinates={}",
            layers.len(),
            coordinates.len()
        )));
    }
    Ok(CorpusCensusV1 {
        schema_version: CENSUS_SCHEMA_VERSION,
        input_sha256,
        weights,
        coordinates,
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;

    #[test]
    fn shared_compilation_preserves_checked_corpus_census_bytes() {
        let weights: WorkloadWeightsV1 = serde_json::from_slice(include_bytes!(
            "../artifacts/windowed_workload_weights_v1.json"
        ))
        .unwrap();
        let value = generate_corpus_census(weights).unwrap();
        let mut actual = serde_json::to_vec(&value).unwrap();
        actual.push(b'\n');
        assert_eq!(
            actual.as_slice(),
            include_bytes!("../artifacts/windowed_corpus_census_v1.json")
        );
    }

    #[test]
    fn shared_compilation_has_57_aligned_layer_triples() {
        let corpus = compile_corpus().unwrap();
        assert_eq!(corpus.layers.len(), 57);
        let keys = corpus
            .layers
            .iter()
            .map(|layer| (layer.circuit.as_str(), layer.layer))
            .collect::<BTreeSet<_>>();
        assert_eq!(keys.len(), 57);
        assert!(corpus
            .layers
            .iter()
            .all(|layer| { layer.r0.layer == layer.layer && layer.ext.layer == layer.layer }));
    }

    #[test]
    fn schema_is_versioned_and_has_two_regimes_per_discovered_layer() {
        let census = generate_corpus_census(default_workload_weights()).unwrap();
        assert_eq!(CENSUS_SCHEMA_VERSION, 1);
        assert_eq!(census.schema_version, CENSUS_SCHEMA_VERSION);
        assert_eq!(census.coordinates.len(), 114);

        let layers = census
            .coordinates
            .iter()
            .map(|coordinate| (coordinate.id.circuit.clone(), coordinate.id.layer))
            .collect::<BTreeSet<_>>();
        assert_eq!(layers.len(), 57);
        assert_eq!(census.coordinates.len(), 2 * layers.len());
        for key in layers {
            let regimes = census
                .coordinates
                .iter()
                .filter(|coordinate| {
                    (coordinate.id.circuit.as_str(), coordinate.id.layer) == (key.0.as_str(), key.1)
                })
                .map(|coordinate| coordinate.id.regime)
                .collect::<BTreeSet<_>>();
            assert_eq!(
                regimes,
                BTreeSet::from([BackwardRegime::R0, BackwardRegime::Ext])
            );
        }
    }

    #[test]
    fn corpus_extrema_and_three_views_are_preserved() {
        let census = generate_corpus_census(default_workload_weights()).unwrap();
        assert_eq!(
            census
                .coordinates
                .iter()
                .map(|row| row.semantic.terms)
                .max(),
            Some(1_791)
        );
        assert_eq!(
            census
                .coordinates
                .iter()
                .map(|row| row.semantic.legacy_records)
                .max(),
            Some(1_617)
        );
        assert_eq!(
            census
                .coordinates
                .iter()
                .filter_map(|row| row.compiler_binding.as_ref().ok())
                .map(|row| row.windows)
                .max(),
            Some(17)
        );
        assert!(census
            .coordinates
            .iter()
            .all(|row| row.compiler_binding.is_ok()));
        assert!(census.coordinates.iter().all(|row| row.semantic.atoms != 0));
        assert!(census.coordinates.iter().all(|row| {
            row.id.regime != BackwardRegime::R0
                || matches!(
                    &row.benchmark_encoding,
                    Err(CensusFailure { kind, .. }) if kind == "r0_c2_only_semantics"
                )
        }));

        let add_sub = census
            .coordinates
            .iter()
            .find(|row| {
                row.id.circuit == "add_sub_lui_auipc_mop"
                    && row.id.layer == 0
                    && row.id.regime == BackwardRegime::Ext
            })
            .unwrap();
        assert_eq!(
            add_sub.semantic.product_prefix_lengths,
            [6, 14, 10, 17, 4, 4, 3, 3, 7, 4]
        );
        assert_eq!(
            add_sub
                .semantic
                .inner_segment_ends
                .iter()
                .map(|ends| ends.last().copied().unwrap())
                .collect::<Vec<_>>(),
            add_sub.semantic.product_prefix_lengths
        );
        let encoding = add_sub.benchmark_encoding.as_ref().unwrap();
        assert_eq!(encoding.direct_words, 326);
        assert_eq!(encoding.padding_words, 24);
    }

    #[test]
    fn current_base_parser_requires_the_exact_nine_counts() {
        let circuits = [
            ("Unrolled(NonMemory(AddSubLuiAuipcMop))", 15),
            ("Unrolled(NonMemory(JumpBranchSlt))", 8),
            ("Unrolled(Memory(LoadStoreWordOnly))", 9),
            ("Unrolled(Memory(LoadStoreSubwordOnly))", 3),
            ("Unrolled(NonMemory(ShiftBinary))", 4),
            ("Unrolled(NonMemory(MulDivUnsigned))", 1),
            ("Unrolled(InitsAndTeardowns)", 1),
            ("Delegation(KeccakSpecial5)", 15),
            ("Delegation(BigIntWithControl)", 3),
        ];
        let mut log = String::new();
        log.push_str(
            "[INFO ] BATCH[0] PROVER producing memory commitments for binary with key 0\n",
        );
        for (circuit, count) in circuits {
            for instance in 0..count {
                log.push_str(&format!(
                    "[DEBUG] BATCH[0] GPU_WORKER[0] produced memory commitment for circuit {circuit}[{instance}] in 1 ms\n"
                ));
            }
        }
        let observed = observed_layers(&log).unwrap();
        assert_eq!(observed.len(), 1);
        assert_eq!(
            current_base_counts(&observed[0]).unwrap(),
            default_workload_weights().profiles.current_base
        );
    }

    #[test]
    fn empty_available_weight_profile_is_rejected() {
        let mut weights = default_workload_weights();
        weights.profiles.development_recursion_proxy = DevelopmentRecursionProfile::Available {
            source: "empty".to_owned(),
            log_sha256: "0".repeat(64),
            layers: Vec::new(),
        };
        assert!(matches!(
            weights.validate(),
            Err(WorkloadWeightError::EmptyAvailableProfile {
                profile: "development_recursion_proxy"
            })
        ));
    }
}
