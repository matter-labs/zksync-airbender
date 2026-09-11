// Ported from dev 67ee0944, gpu_prover/src/memory_sweep/model.rs.
use crate::memory_policy::PolicyGeometry;
use gpu_circuit_prover::proof::memory_policy::{
    FullWitnessWhirPolicy, OpeningPolicy, ProofMemoryPolicy as MemoryPolicy, WitnessMemoryPolicy,
};
use gpu_trace::witness::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{Display, Formatter};
use std::io::{Read, Write};

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
pub struct SweepRow {
    pub arena_bytes: usize,
    pub circuit: String,
    pub configuration: String,
    pub geometry: String,
    pub setup: String,
    pub witness_commitment: String,
    pub witness_opening: String,
    pub memory: String,
    pub failure_stage: Option<String>,
    pub raw_samples_ms: String,
    pub proof_fingerprint: Option<u64>,
    pub fits: bool,
    pub input_bytes: usize,
    pub peak_bytes: Option<usize>,
    pub timing_samples: usize,
    pub median_ms: Option<f32>,
    pub min_ms: Option<f32>,
    pub max_ms: Option<f32>,
    pub preferred: bool,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct TimingSummary {
    pub samples: usize,
    pub min_ms: f32,
    pub median_ms: f32,
    pub max_ms: f32,
}

impl TimingSummary {
    pub fn from_samples(samples: &[f32]) -> Option<Self> {
        if samples.is_empty()
            || samples
                .iter()
                .any(|sample| !sample.is_finite() || *sample <= 0.0)
        {
            return None;
        }
        let mut sorted = samples.to_vec();
        sorted.sort_by(f32::total_cmp);
        let middle = sorted.len() / 2;
        let median_ms = if sorted.len().is_multiple_of(2) {
            (sorted[middle - 1] + sorted[middle]) / 2.0
        } else {
            sorted[middle]
        };
        Some(Self {
            samples: sorted.len(),
            min_ms: sorted[0],
            median_ms,
            max_ms: sorted[sorted.len() - 1],
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SweepCase {
    pub circuit: CircuitType,
    pub policy: MemoryPolicy,
}

pub fn stable_cases(
    circuits: impl IntoIterator<Item = CircuitType>,
    policies: impl IntoIterator<Item = MemoryPolicy> + Clone,
) -> Vec<SweepCase> {
    circuits
        .into_iter()
        .flat_map(|circuit| {
            policies
                .clone()
                .into_iter()
                .map(move |policy| SweepCase { circuit, policy })
        })
        .collect()
}

#[derive(Debug)]
pub enum SweepModelError {
    Csv(csv::Error),
    Io(std::io::Error),
    Invalid(String),
}

impl Display for SweepModelError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Csv(error) => error.fmt(formatter),
            Self::Io(error) => error.fmt(formatter),
            Self::Invalid(message) => formatter.write_str(message),
        }
    }
}

impl std::error::Error for SweepModelError {}

impl From<csv::Error> for SweepModelError {
    fn from(error: csv::Error) -> Self {
        Self::Csv(error)
    }
}

impl From<std::io::Error> for SweepModelError {
    fn from(error: std::io::Error) -> Self {
        Self::Io(error)
    }
}

pub fn mark_preferred(rows: &mut [SweepRow]) -> Result<(), SweepModelError> {
    for row in rows.iter_mut() {
        row.preferred = false;
    }
    let mut winners = BTreeMap::<(usize, String, String), (usize, f32, String)>::new();
    for (index, row) in rows.iter().enumerate() {
        if !row.fits || row.timing_samples == 0 {
            continue;
        }
        let median = row.median_ms.ok_or_else(|| {
            SweepModelError::Invalid(format!(
                "fitting timed row {} has no median",
                row.configuration
            ))
        })?;
        if !median.is_finite() || median <= 0.0 {
            return Err(SweepModelError::Invalid(
                "proof timings must be finite and positive".into(),
            ));
        }
        let candidate = (index, median, row.configuration.clone());
        let group = (row.arena_bytes, row.circuit.clone(), row.geometry.clone());
        match winners.get(&group) {
            Some((_, best_median, best_name))
                if (candidate.1, &candidate.2) >= (*best_median, best_name) => {}
            _ => {
                winners.insert(group, candidate);
            }
        }
    }
    for (index, _, _) in winners.into_values() {
        rows[index].preferred = true;
    }
    Ok(())
}

pub fn write_csv(output: impl Write, rows: &[SweepRow]) -> Result<(), SweepModelError> {
    let mut writer = csv::Writer::from_writer(output);
    for row in rows {
        writer.serialize(row)?;
    }
    writer.flush()?;
    Ok(())
}

/// Adapted from v2's single-arena low_vram_policy generator. Each circuit
/// may now have several measured thresholds; it need not fit every arena.
pub fn generate_policy(input: impl Read, output: impl Write) -> Result<(), SweepModelError> {
    let rows = csv::Reader::from_reader(input)
        .deserialize::<SweepRow>()
        .collect::<Result<Vec<_>, _>>()?;
    let mut selected = BTreeMap::new();
    for row in rows.iter().filter(|row| row.preferred) {
        if !row.fits
            || row.timing_samples == 0
            || row.peak_bytes.is_none_or(|p| p > row.arena_bytes)
            || row.median_ms.is_none_or(|ms| !ms.is_finite() || ms <= 0.0)
        {
            return Err(SweepModelError::Invalid(
                "preferred row lacks a valid fit/timing measurement".into(),
            ));
        }
        let samples: Vec<f32> = serde_json::from_str(&row.raw_samples_ms)
            .map_err(|e| SweepModelError::Invalid(e.to_string()))?;
        let summary = TimingSummary::from_samples(&samples)
            .ok_or_else(|| SweepModelError::Invalid("invalid raw timing samples".into()))?;
        if summary.samples != row.timing_samples
            || Some(summary.median_ms) != row.median_ms
            || Some(summary.min_ms) != row.min_ms
            || Some(summary.max_ms) != row.max_ms
            || row.proof_fingerprint.is_none()
            || row.failure_stage.is_some()
        {
            return Err(SweepModelError::Invalid(
                "timing summary or proof evidence is inconsistent".into(),
            ));
        }
        let policy = MemoryPolicy::candidates()
            .find(|p| stable_name(*p) == row.configuration)
            .ok_or_else(|| SweepModelError::Invalid("unknown v3 configuration".into()))?;
        let (setup, memory, commitment, opening) = policy_fields(policy);
        if (
            &row.setup,
            &row.memory,
            &row.witness_commitment,
            &row.witness_opening,
        ) != (&setup, &memory, &commitment, &opening)
        {
            return Err(SweepModelError::Invalid(
                "configuration fields disagree".into(),
            ));
        }
        let geometry: PolicyGeometry = serde_json::from_str(&row.geometry)
            .map_err(|e| SweepModelError::Invalid(e.to_string()))?;
        let key = (
            row.circuit.clone(),
            serde_json::to_string(&geometry.allocation_key())
                .map_err(|e| SweepModelError::Invalid(e.to_string()))?,
            row.arena_bytes,
        );
        if selected.insert(key, (policy, geometry)).is_some() {
            return Err(SweepModelError::Invalid(
                "multiple preferred policies for one threshold".into(),
            ));
        }
    }
    let circuits = all_circuits();
    // A deployable budget must cover every circuit on the same allocator/leaf
    // profile. Per-circuit successes below this floor are diagnostic only.
    let mut budgets =
        BTreeMap::<(usize, u32, u32, Option<u32>, usize, bool), BTreeSet<&str>>::new();
    for ((circuit, _, arena), (_, g)) in &selected {
        budgets
            .entry((
                *arena,
                g.sweep_schema,
                g.allocator_block_log_size,
                g.small_allocator_log_chunk_size,
                g.small_allocator_pool_blocks,
                g.eval_leaves,
            ))
            .or_default()
            .insert(circuit.as_str());
    }
    if budgets.is_empty()
        || budgets.values().any(|covered| {
            covered.len() != circuits.len()
                || circuits
                    .iter()
                    .any(|c| !covered.contains(circuit_stable_name(*c)))
        })
    {
        return Err(SweepModelError::Invalid(
            "every chosen budget must have a fitting measured policy for all supported circuits"
                .into(),
        ));
    }
    let mut output = std::io::BufWriter::new(output);
    writeln!(output, "// Generated by the v3 port of dev's gpu_memory_sweep. Regenerate after memory-relevant changes.")?;
    writeln!(
        output,
        "use super::{{MemoryPolicyThreshold, PolicyGeometry}};"
    )?;
    writeln!(output, "use gpu_circuit_prover::proof::memory_policy::{{ProofMemoryPolicy, OpeningPolicy, WitnessMemoryPolicy, FullWitnessWhirPolicy}};")?;
    writeln!(output, "use gpu_trace::witness::circuit_type::{{CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType, UnrolledNonMemoryCircuitType}};")?;
    writeln!(
        output,
        "pub(super) const THRESHOLDS: &[MemoryPolicyThreshold] = &["
    )?;
    for ((name, _, arena_bytes), (policy, geometry)) in selected {
        let circuit = circuits
            .iter()
            .copied()
            .find(|c| circuit_stable_name(*c) == name)
            .unwrap();
        writeln!(output, "    MemoryPolicyThreshold {{ circuit: {}, geometry: {:?}, arena_bytes: {}, policy: {} }},",
            circuit_pattern(circuit), geometry, arena_bytes, policy_expression(policy))?;
    }
    writeln!(output, "];")?;
    output.flush()?;
    Ok(())
}

pub fn all_circuits() -> Vec<CircuitType> {
    use CircuitType::{Delegation, Unrolled};
    use UnrolledCircuitType::{InitsAndTeardowns, Memory, NonMemory, Unified};
    vec![
        Delegation(DelegationCircuitType::BigIntWithControl),
        Delegation(DelegationCircuitType::Blake2WithCompression),
        Delegation(DelegationCircuitType::Blake2GFunction),
        Delegation(DelegationCircuitType::KeccakSpecial5),
        Unrolled(InitsAndTeardowns),
        Unrolled(Memory(UnrolledMemoryCircuitType::LoadStoreSubwordOnly)),
        Unrolled(Memory(UnrolledMemoryCircuitType::LoadStoreWordOnly)),
        Unrolled(NonMemory(UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop)),
        Unrolled(NonMemory(UnrolledNonMemoryCircuitType::JumpBranchSlt)),
        Unrolled(NonMemory(UnrolledNonMemoryCircuitType::MulDivUnsigned)),
        Unrolled(NonMemory(UnrolledNonMemoryCircuitType::ShiftBinary)),
        Unrolled(Unified),
    ]
}

pub fn policy_fields(policy: MemoryPolicy) -> (String, String, String, String) {
    fn opening(p: OpeningPolicy) -> String {
        match p {
            OpeningPolicy::FullMaterialization => "full",
            OpeningPolicy::RetainMonomials => "monomials",
            OpeningPolicy::InPlace => "in_place",
        }
        .into()
    }
    let (commitment, whir) = match policy.witness {
        WitnessMemoryPolicy::FullMaterialization {
            whir: FullWitnessWhirPolicy::RetainCosets,
        } => ("full", "keep_cosets".into()),
        WitnessMemoryPolicy::FullMaterialization {
            whir: FullWitnessWhirPolicy::Recompute(p),
        } => ("full", opening(p)),
        WitnessMemoryPolicy::RetainMonomials { whir } => ("evals_monomials", opening(whir)),
        WitnessMemoryPolicy::InPlace { whir } => ("in_place", opening(whir)),
    };
    (
        opening(policy.setup),
        opening(policy.memory),
        commitment.into(),
        whir,
    )
}

pub fn stable_name(policy: MemoryPolicy) -> String {
    let (setup, memory, witness, whir) = policy_fields(policy);
    format!("setup_{setup}-memory_{memory}-witness_{witness}-opening_{whir}")
}

fn policy_expression(policy: MemoryPolicy) -> String {
    let witness = match policy.witness {
        WitnessMemoryPolicy::FullMaterialization { whir: FullWitnessWhirPolicy::RetainCosets } =>
            "WitnessMemoryPolicy::FullMaterialization { whir: FullWitnessWhirPolicy::RetainCosets }".into(),
        WitnessMemoryPolicy::FullMaterialization { whir: FullWitnessWhirPolicy::Recompute(p) } =>
            format!("WitnessMemoryPolicy::FullMaterialization {{ whir: FullWitnessWhirPolicy::Recompute(OpeningPolicy::{p:?}) }}"),
        WitnessMemoryPolicy::RetainMonomials { whir } =>
            format!("WitnessMemoryPolicy::RetainMonomials {{ whir: OpeningPolicy::{whir:?} }}"),
        WitnessMemoryPolicy::InPlace { whir } =>
            format!("WitnessMemoryPolicy::InPlace {{ whir: OpeningPolicy::{whir:?} }}"),
    };
    format!("ProofMemoryPolicy {{ setup: OpeningPolicy::{:?}, memory: OpeningPolicy::{:?}, witness: {witness} }}", policy.setup, policy.memory)
}

pub fn circuit_stable_name(circuit: CircuitType) -> &'static str {
    match circuit {
        CircuitType::Delegation(DelegationCircuitType::BigIntWithControl) => {
            "delegation_big_int_with_control"
        }
        CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression) => {
            "delegation_blake2_with_compression"
        }
        CircuitType::Delegation(DelegationCircuitType::Blake2GFunction) => {
            "delegation_blake2_g_function"
        }
        CircuitType::Delegation(DelegationCircuitType::KeccakSpecial5) => {
            "delegation_keccak_special_5"
        }
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
            "unrolled_inits_and_teardowns"
        }
        CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
        )) => "unrolled_memory_load_store_subword_only",
        CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreWordOnly,
        )) => "unrolled_memory_load_store_word_only",
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
        )) => "unrolled_non_memory_add_sub_lui_auipc_mop",
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::JumpBranchSlt,
        )) => "unrolled_non_memory_jump_branch_slt",
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::MulDivUnsigned,
        )) => "unrolled_non_memory_mul_div_unsigned",
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::ShiftBinary,
        )) => "unrolled_non_memory_shift_binary",
        CircuitType::Unrolled(UnrolledCircuitType::Unified) => "unrolled_unified",
    }
}

fn circuit_pattern(circuit: CircuitType) -> &'static str {
    match circuit {
        CircuitType::Delegation(DelegationCircuitType::BigIntWithControl) => {
            "CircuitType::Delegation(DelegationCircuitType::BigIntWithControl)"
        }
        CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression) => {
            "CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression)"
        }
        CircuitType::Delegation(DelegationCircuitType::Blake2GFunction) => {
            "CircuitType::Delegation(DelegationCircuitType::Blake2GFunction)"
        }
        CircuitType::Delegation(DelegationCircuitType::KeccakSpecial5) => {
            "CircuitType::Delegation(DelegationCircuitType::KeccakSpecial5)"
        }
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
            "CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns)"
        }
        CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
        )) => "CircuitType::Unrolled(UnrolledCircuitType::Memory(UnrolledMemoryCircuitType::LoadStoreSubwordOnly))",
        CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreWordOnly,
        )) => "CircuitType::Unrolled(UnrolledCircuitType::Memory(UnrolledMemoryCircuitType::LoadStoreWordOnly))",
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
        )) => "CircuitType::Unrolled(UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop))",
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::JumpBranchSlt,
        )) => "CircuitType::Unrolled(UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::JumpBranchSlt))",
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::MulDivUnsigned,
        )) => "CircuitType::Unrolled(UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::MulDivUnsigned))",
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::ShiftBinary,
        )) => "CircuitType::Unrolled(UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::ShiftBinary))",
        CircuitType::Unrolled(UnrolledCircuitType::Unified) => {
            "CircuitType::Unrolled(UnrolledCircuitType::Unified)"
        }
    }
}

#[cfg(test)]
mod tests;
