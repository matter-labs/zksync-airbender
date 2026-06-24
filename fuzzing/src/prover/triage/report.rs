use std::fmt;

use crate::prover::circuits::CircuitKind;
use crate::prover::crashes::BugType;
use crate::prover::crashes::CrashArtifact;
use crate::prover::crashes::CrashStep;
use crate::prover::mutations::MutationRecord;
use crate::prover::seeds::SeedCase;
use crate::prover::triage::analysis::oracle::OracleShapeSummary;

use super::AnalysisTrace;
use crate::prover::triage::analysis::CheckpointDiff;

/// High-level triage outcome for a persisted crash.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
pub enum TriageVerdict {
    FalsePositive,
    PotentiallyReal,
    Inconclusive,
}

impl fmt::Display for TriageVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FalsePositive => write!(f, "false positive"),
            Self::PotentiallyReal => write!(f, "potentially real"),
            Self::Inconclusive => write!(f, "inconclusive"),
        }
    }
}

/// Final structured triage result emitted to the terminal and optional JSON output.
#[derive(Clone, Debug, serde::Serialize)]
pub(super) struct TriageReport {
    verdict: TriageVerdict,
    seed_program: String,
    circuit: CircuitKind,
    recorded_step: CrashStep,
    recorded_bug_type: BugType,
    diff: Vec<CheckpointDiff>,
    instability: Option<CheckpointDiff>,
    mutations: Vec<String>,
    base: AnalysisTrace,
    mutated: AnalysisTrace,
}

impl TriageReport {
    pub(super) fn new(
        verdict: TriageVerdict,
        crash: &CrashArtifact,
        diff: Vec<CheckpointDiff>,
        instability: Option<CheckpointDiff>,
        base: AnalysisTrace,
        mutated: AnalysisTrace,
    ) -> Self {
        Self {
            verdict,
            seed_program: crash.seed_program.clone(),
            circuit: crash.circuit,
            recorded_step: crash.step,
            recorded_bug_type: crash.bug_type,
            diff,
            instability,
            mutations: crash
                .mutations
                .iter()
                .map(MutationRecord::summary)
                .map(ToOwned::to_owned)
                .collect(),
            base,
            mutated,
        }
    }

    /// Builds a structured report for crashes whose replay is not stable enough to trust.
    pub(super) fn inconclusive(
        base: &SeedCase,
        crash: &CrashArtifact,
        instability: CheckpointDiff,
    ) -> Self {
        // We still emit a structured report for unstable cases so batch triage can distinguish
        // "no effect" from "could not obtain a trustworthy replay".
        Self::new(
            TriageVerdict::Inconclusive,
            crash,
            vec![],
            Some(instability),
            AnalysisTrace::empty(OracleShapeSummary::from_input(&base.base_input)),
            AnalysisTrace::empty(OracleShapeSummary::from_input(&crash.mutated_input)),
        )
    }
}

impl fmt::Display for TriageReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Verdict: {}", self.verdict)?;
        writeln!(
            f,
            "Crash: seed={}, circuit={}, step={}",
            self.seed_program,
            self.circuit.slug(),
            self.recorded_step.slug()
        )?;
        writeln!(f, "Recorded bug type: {}", self.recorded_bug_type)?;
        if self.diff.is_empty() {
            writeln!(f, "Diff: none")?;
        } else {
            writeln!(f, "Diff:")?;
            for diff in &self.diff {
                writeln!(f, "  - {} ({})", diff.checkpoint(), diff.detail())?;
            }
        }

        if !self.mutations.is_empty() {
            writeln!(f, "Mutations: {}", self.mutations.join(", "))?;
        }

        Ok(())
    }
}
