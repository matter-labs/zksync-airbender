use gpu_circuit_prover::proof::memory_policy::{
    GkrMemoryPolicy, OpeningStrategy, ProofMemoryPolicy as MemoryPolicy, WitnessCommitmentStrategy,
    WitnessOpeningStrategy, WitnessPostCommitStorage,
};
use gpu_trace::witness::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::error::Error;
use std::io::{Read, Write};

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
pub struct SweepRow {
    pub arena_bytes: usize,
    pub circuit: String,
    pub configuration: String,
    pub gkr: String,
    pub setup: String,
    pub witness_commitment: String,
    pub witness_post_commitment: String,
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

pub fn mark_preferred(rows: &mut [SweepRow]) -> Result<(), Box<dyn Error>> {
    for row in rows.iter_mut() {
        row.preferred = false;
    }
    let mut winners = BTreeMap::<(usize, String), (usize, f32, String)>::new();
    for (index, row) in rows.iter().enumerate() {
        if !row.fits || row.timing_samples == 0 {
            continue;
        }
        let median = row
            .median_ms
            .ok_or_else(|| format!("fitting timed row {} has no median", row.configuration))?;
        if !median.is_finite() || median <= 0.0 {
            return Err("proof timings must be finite and positive".into());
        }
        let candidate = (index, median, row.configuration.clone());
        let group = (row.arena_bytes, row.circuit.clone());
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

pub fn write_csv(output: impl Write, rows: &[SweepRow]) -> Result<(), Box<dyn Error>> {
    let mut writer = csv::Writer::from_writer(output);
    for row in rows {
        writer.serialize(row)?;
    }
    writer.flush()?;
    Ok(())
}

pub fn generate_policy(input: impl Read, output: impl Write) -> Result<(), Box<dyn Error>> {
    let rows = csv::Reader::from_reader(input)
        .deserialize::<SweepRow>()
        .collect::<Result<Vec<_>, _>>()?;
    let mut selected = BTreeMap::<usize, BTreeMap<String, MemoryPolicy>>::new();
    for row in rows.iter().filter(|row| row.preferred) {
        if !row.fits
            || row.timing_samples == 0
            || row.peak_bytes.is_none_or(|p| p > row.arena_bytes)
            || row.median_ms.is_none_or(|ms| !ms.is_finite() || ms <= 0.0)
        {
            return Err("preferred row lacks a valid fit/timing measurement".into());
        }
        let samples: Vec<f32> = serde_json::from_str(&row.raw_samples_ms)?;
        let summary = TimingSummary::from_samples(&samples).ok_or("invalid raw timing samples")?;
        if summary.samples != row.timing_samples
            || Some(summary.median_ms) != row.median_ms
            || Some(summary.min_ms) != row.min_ms
            || Some(summary.max_ms) != row.max_ms
            || row.proof_fingerprint.is_none()
            || row.failure_stage.is_some()
        {
            return Err("timing summary or proof evidence is inconsistent".into());
        }
        let policy = candidates()
            .find(|p| stable_name(*p) == row.configuration)
            .ok_or("unknown v3 configuration")?;
        if row.gkr != gkr_name(policy) {
            return Err("GKR configuration field disagrees".into());
        }
        let (setup, memory, commitment, post_commitment, opening) = policy_fields(policy);
        if (
            &row.setup,
            &row.memory,
            &row.witness_commitment,
            &row.witness_post_commitment,
            &row.witness_opening,
        ) != (&setup, &memory, &commitment, &post_commitment, &opening)
        {
            return Err("configuration fields disagree".into());
        }
        if row.arena_bytes == 0
            || !row.arena_bytes.is_multiple_of(
                1 << gpu_prover_context::ProverContextConfig::default().allocator_block_log_size,
            )
        {
            return Err("arena budget must be positive and block-aligned".into());
        }
        if selected
            .entry(row.arena_bytes)
            .or_default()
            .insert(row.circuit.clone(), policy)
            .is_some()
        {
            return Err("multiple preferred policies for one circuit at one budget".into());
        }
    }
    let circuits = all_circuits();
    if selected.is_empty()
        || rows
            .iter()
            .any(|row| !selected.contains_key(&row.arena_bytes))
        || selected.values().any(|policies| {
            policies.len() != circuits.len()
                || circuits
                    .iter()
                    .any(|c| !policies.contains_key(circuit_stable_name(*c)))
        })
    {
        return Err(
            "each chosen budget must have a fitting measured policy for every supported circuit"
                .into(),
        );
    }
    let mut output = std::io::BufWriter::new(output);
    writeln!(
        output,
        "// Generated by gpu_memory_sweep. Regenerate after memory-relevant changes."
    )?;
    writeln!(output, "use crate::proof::memory_policy::{{ProofMemoryPolicy, GkrMemoryPolicy, OpeningStrategy, WitnessMemoryPolicy, WitnessCommitmentStrategy, WitnessPostCommitStorage, WitnessOpeningStrategy}};")?;
    writeln!(output, "use gpu_trace::witness::circuit_type::{{CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType, UnrolledNonMemoryCircuitType}};")?;
    writeln!(
        output,
        "pub(crate) const PRESET_ARENA_BYTES: &[usize] = &{:?};",
        selected.keys().collect::<Vec<_>>()
    )?;
    writeln!(
        output,
        "pub(crate) const fn policy(circuit: CircuitType, arena_bytes: usize) -> ProofMemoryPolicy {{ match arena_bytes {{"
    )?;
    for (arena, policies) in selected {
        writeln!(output, "{arena} => match circuit {{")?;
        let mut groups = BTreeMap::<String, Vec<&str>>::new();
        for &circuit in &circuits {
            let policy = policies[circuit_stable_name(circuit)];
            groups
                .entry(policy_expression(policy))
                .or_default()
                .push(circuit_pattern(circuit));
        }
        for (policy, patterns) in groups {
            writeln!(output, "{} => {},", patterns.join(" | "), policy)?;
        }
        writeln!(output, "}},")?;
    }
    writeln!(output, "_ => panic!(\"unsupported memory preset arena\"),")?;
    writeln!(output, "}} }}")?;
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
        Delegation(DelegationCircuitType::KeccakColumnParity),
        Delegation(DelegationCircuitType::KeccakThetaRho),
        Delegation(DelegationCircuitType::KeccakChi5),
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

pub fn policy_fields(policy: MemoryPolicy) -> (String, String, String, String, String) {
    fn opening(strategy: OpeningStrategy) -> &'static str {
        match strategy {
            OpeningStrategy::AllCosets => "all_cosets",
            OpeningStrategy::PerCoset => "per_coset",
            OpeningStrategy::InPlace => "in_place",
        }
    }
    let commitment = match policy.witness.commitment {
        WitnessCommitmentStrategy::AllCosets => "all_cosets",
        WitnessCommitmentStrategy::PerCoset => "per_coset",
        WitnessCommitmentStrategy::InPlace => "in_place",
    };
    let post_commitment = match policy.witness.post_commitment {
        WitnessPostCommitStorage::RawEvaluations => "raw",
        WitnessPostCommitStorage::RawAndMonomials => "raw_monomials",
        WitnessPostCommitStorage::RawAndCosets => "raw_cosets",
    };
    let witness_opening = match policy.witness.opening {
        WitnessOpeningStrategy::ReuseCosets => "reuse_cosets",
        WitnessOpeningStrategy::Recompute(strategy) => opening(strategy),
    };
    (
        opening(policy.setup).into(),
        opening(policy.memory).into(),
        commitment.into(),
        post_commitment.into(),
        witness_opening.into(),
    )
}

pub fn candidates() -> impl Iterator<Item = MemoryPolicy> {
    MemoryPolicy::candidates().flat_map(|policy| {
        GkrMemoryPolicy::candidates().map(move |gkr| MemoryPolicy { gkr, ..policy })
    })
}

pub fn gkr_name(policy: MemoryPolicy) -> String {
    match policy.gkr {
        GkrMemoryPolicy::Materialize => "materialize".into(),
        GkrMemoryPolicy::Recompute {
            value_layers,
            cache_layers,
        } => format!("recompute_values_{value_layers}_caches_{cache_layers}"),
    }
}

pub fn stable_name(policy: MemoryPolicy) -> String {
    let (setup, memory, commitment, post_commitment, opening) = policy_fields(policy);
    let gkr = gkr_name(policy);
    format!("gkr_{gkr}-setup_{setup}-memory_{memory}-commitment_{commitment}-post_commitment_{post_commitment}-opening_{opening}")
}

fn policy_expression(policy: MemoryPolicy) -> String {
    let opening = match policy.witness.opening {
        WitnessOpeningStrategy::ReuseCosets => "WitnessOpeningStrategy::ReuseCosets".into(),
        WitnessOpeningStrategy::Recompute(strategy) => {
            format!("WitnessOpeningStrategy::Recompute(OpeningStrategy::{strategy:?})")
        }
    };
    format!("ProofMemoryPolicy {{ gkr: GkrMemoryPolicy::{:?}, setup: OpeningStrategy::{:?}, memory: OpeningStrategy::{:?}, witness: WitnessMemoryPolicy {{ commitment: WitnessCommitmentStrategy::{:?}, post_commitment: WitnessPostCommitStorage::{:?}, opening: {opening} }} }}", policy.gkr, policy.setup, policy.memory, policy.witness.commitment, policy.witness.post_commitment)
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
        CircuitType::Delegation(DelegationCircuitType::KeccakColumnParity) => {
            "delegation_keccak_column_parity"
        }
        CircuitType::Delegation(DelegationCircuitType::KeccakThetaRho) => {
            "delegation_keccak_theta_rho"
        }
        CircuitType::Delegation(DelegationCircuitType::KeccakChi5) => "delegation_keccak_chi5",
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
        CircuitType::Delegation(DelegationCircuitType::KeccakColumnParity) => "CircuitType::Delegation(DelegationCircuitType::KeccakColumnParity)",
        CircuitType::Delegation(DelegationCircuitType::KeccakThetaRho) => "CircuitType::Delegation(DelegationCircuitType::KeccakThetaRho)",
        CircuitType::Delegation(DelegationCircuitType::KeccakChi5) => "CircuitType::Delegation(DelegationCircuitType::KeccakChi5)",
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
