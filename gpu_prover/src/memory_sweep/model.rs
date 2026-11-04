use crate::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use crate::prover::memory_policy::MemoryPolicy;
use crate::prover::trace_holder::CosetsCacheMode;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{Display, Formatter};
use std::io::{Read, Write};

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
pub struct SweepRow {
    pub arena_bytes: usize,
    pub circuit: String,
    pub configuration: String,
    pub setup: CosetsCacheMode,
    pub witness: CosetsCacheMode,
    pub memory: CosetsCacheMode,
    pub stage_two: CosetsCacheMode,
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
        if samples.is_empty() || samples.iter().any(|sample| !sample.is_finite()) {
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

#[cfg(test)]
pub fn timed_case_order(cases: &[SweepCase], rounds: usize) -> Vec<SweepCase> {
    (0..rounds).flat_map(|_| cases.iter().copied()).collect()
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
    let mut winners = BTreeMap::<(usize, String), (usize, f32, String)>::new();
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

pub fn write_csv(output: impl Write, rows: &[SweepRow]) -> Result<(), SweepModelError> {
    let mut writer = csv::Writer::from_writer(output);
    for row in rows {
        writer.serialize(row)?;
    }
    writer.flush()?;
    Ok(())
}

pub fn generate_policy(input: impl Read, output: impl Write) -> Result<(), SweepModelError> {
    let rows = csv::Reader::from_reader(input)
        .deserialize::<SweepRow>()
        .collect::<Result<Vec<_>, _>>()?;
    let arenas = rows
        .iter()
        .map(|row| row.arena_bytes)
        .collect::<BTreeSet<_>>();
    if arenas.len() != 1 {
        return Err(SweepModelError::Invalid(
            "policy input must contain exactly one arena size".to_owned(),
        ));
    }

    let mut selected = BTreeMap::new();
    for row in rows.iter().filter(|row| row.fits && row.preferred) {
        let policy = MemoryPolicy::new(row.setup, row.witness, row.memory, row.stage_two);
        if policy.stable_name() != row.configuration {
            return Err(SweepModelError::Invalid(format!(
                "configuration fields do not match {}",
                row.configuration
            )));
        }
        if selected.insert(row.circuit.clone(), policy).is_some() {
            return Err(SweepModelError::Invalid(format!(
                "multiple preferred rows for {}",
                row.circuit
            )));
        }
    }

    let circuits = CircuitType::get_all();
    if selected.len() != circuits.len()
        || circuits
            .iter()
            .any(|circuit| !selected.contains_key(circuit_stable_name(*circuit)))
    {
        return Err(SweepModelError::Invalid(
            "policy input must select every supported circuit exactly once".to_owned(),
        ));
    }

    let mut output = std::io::BufWriter::new(output);
    writeln!(output, "use super::memory_policy::MemoryPolicy;")?;
    writeln!(output, "use super::trace_holder::CosetsCacheMode;")?;
    writeln!(
        output,
        "use crate::circuit_type::{{CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType, UnrolledNonMemoryCircuitType}};\n"
    )?;
    writeln!(
        output,
        "pub(crate) const fn low_vram_policy(circuit: CircuitType) -> MemoryPolicy {{"
    )?;
    writeln!(
        output,
        "    use CosetsCacheMode::{{CacheFull as Full, CacheSingle as Single}};\n"
    )?;
    writeln!(output, "    match circuit {{")?;
    for circuit in circuits {
        let policy = selected[circuit_stable_name(circuit)];
        writeln!(
            output,
            "        {} => MemoryPolicy::new({}, {}, {}, {}),",
            circuit_pattern(circuit),
            policy_name(policy.setup),
            policy_name(policy.witness),
            policy_name(policy.memory),
            policy_name(policy.stage_two),
        )?;
    }
    writeln!(output, "    }}")?;
    writeln!(output, "}}")?;
    output.flush()?;
    Ok(())
}

pub fn circuit_stable_name(circuit: CircuitType) -> &'static str {
    match circuit {
        CircuitType::Delegation(DelegationCircuitType::BigIntWithControl) => {
            "delegation_big_int_with_control"
        }
        CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression) => {
            "delegation_blake2_with_compression"
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
            UnrolledNonMemoryCircuitType::MulDiv,
        )) => "unrolled_non_memory_mul_div",
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::MulDivUnsigned,
        )) => "unrolled_non_memory_mul_div_unsigned",
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::ShiftBinaryCsr,
        )) => "unrolled_non_memory_shift_binary_csr",
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
            UnrolledNonMemoryCircuitType::MulDiv,
        )) => "CircuitType::Unrolled(UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::MulDiv))",
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::MulDivUnsigned,
        )) => "CircuitType::Unrolled(UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::MulDivUnsigned))",
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::ShiftBinaryCsr,
        )) => "CircuitType::Unrolled(UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::ShiftBinaryCsr))",
        CircuitType::Unrolled(UnrolledCircuitType::Unified) => {
            "CircuitType::Unrolled(UnrolledCircuitType::Unified)"
        }
    }
}

fn policy_name(policy: CosetsCacheMode) -> &'static str {
    match policy {
        CosetsCacheMode::CacheFull => "Full",
        CosetsCacheMode::CacheSingle => "Single",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn row(circuit: CircuitType, policy: MemoryPolicy, median_ms: f32) -> SweepRow {
        SweepRow {
            arena_bytes: 23_085_449_216,
            circuit: circuit_stable_name(circuit).to_owned(),
            configuration: policy.stable_name(),
            setup: policy.setup,
            witness: policy.witness,
            memory: policy.memory,
            stage_two: policy.stage_two,
            fits: true,
            input_bytes: 100,
            peak_bytes: Some(200),
            timing_samples: 5,
            median_ms: Some(median_ms),
            min_ms: Some(median_ms - 1.0),
            max_ms: Some(median_ms + 1.0),
            preferred: false,
        }
    }

    #[test]
    fn sweep_model_orders_rounds_summarizes_timings_and_selects_preferred() {
        let policies = MemoryPolicy::fixed_tree_configurations();
        assert_eq!(policies.len(), 16);
        let circuits = CircuitType::get_all();
        let cases = stable_cases([circuits[0], circuits[1]], policies.iter().copied());
        let order = timed_case_order(&cases, 3);
        assert_eq!(order.len(), cases.len() * 3);
        assert_eq!(&order[..cases.len()], cases.as_slice());
        assert_eq!(&order[cases.len()..2 * cases.len()], cases.as_slice());

        let summary = TimingSummary::from_samples(&[9.0, 1.0, 5.0, 7.0, 3.0]).unwrap();
        assert_eq!(summary.samples, 5);
        assert_eq!(summary.min_ms, 1.0);
        assert_eq!(summary.median_ms, 5.0);
        assert_eq!(summary.max_ms, 9.0);

        let mut rows = vec![
            row(circuits[0], policies[0], 10.0),
            row(circuits[0], policies[1], 5.0),
            row(circuits[1], policies[0], 7.0),
        ];
        mark_preferred(&mut rows).unwrap();
        assert_eq!(rows.iter().filter(|row| row.preferred).count(), 2);
        assert!(rows[1].preferred);
        assert!(rows[2].preferred);
    }

    #[test]
    fn policy_generation_is_deterministic_and_rejects_incomplete_or_ambiguous_input() {
        let policy = MemoryPolicy::normal();
        let mut rows = CircuitType::get_all()
            .into_iter()
            .map(|circuit| {
                let mut row = row(circuit, policy, 1.0);
                row.preferred = true;
                row
            })
            .collect::<Vec<_>>();
        let mut csv = Vec::new();
        write_csv(&mut csv, &rows).unwrap();
        let mut first = Vec::new();
        let mut second = Vec::new();
        generate_policy(csv.as_slice(), &mut first).unwrap();
        generate_policy(csv.as_slice(), &mut second).unwrap();
        assert_eq!(first, second);
        assert!(
            String::from_utf8_lossy(&first).contains("CacheFull as Full, CacheSingle as Single")
        );
        assert!(
            String::from_utf8_lossy(&first).contains("MemoryPolicy::new(Full, Full, Full, Full)")
        );
        for circuit in CircuitType::get_all() {
            assert!(String::from_utf8_lossy(&first).contains(circuit_pattern(circuit)));
        }

        rows.pop();
        let mut incomplete = Vec::new();
        write_csv(&mut incomplete, &rows).unwrap();
        assert!(generate_policy(incomplete.as_slice(), Vec::new()).is_err());

        let mut complete = CircuitType::get_all()
            .into_iter()
            .map(|circuit| {
                let mut row = row(circuit, policy, 1.0);
                row.preferred = true;
                row
            })
            .collect::<Vec<_>>();
        complete.push(complete[0].clone());
        let mut duplicate = Vec::new();
        write_csv(&mut duplicate, &complete).unwrap();
        assert!(generate_policy(duplicate.as_slice(), Vec::new()).is_err());

        complete.pop();
        complete[0].arena_bytes += 1;
        let mut two_arenas = Vec::new();
        write_csv(&mut two_arenas, &complete).unwrap();
        assert!(generate_policy(two_arenas.as_slice(), Vec::new()).is_err());
    }
}
