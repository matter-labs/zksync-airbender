use std::fs;
use std::io;
use std::path::Path;

use crate::prover::circuits::CircuitKind;
use crate::prover::mutations::MutatedInput;
use crate::prover::mutations::MutationRecord;
use crate::prover::seeds::StoredProofInputs;

#[derive(Clone, Debug)]
pub enum ExecutionOutcome {
    DiscardedProverCrash,
    Interesting(Box<BugReport>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum BugType {
    // Completeness
    ProofGenerationBug,
    // Soundness
    ValidationBug,
}

impl BugType {
    #[inline]
    pub fn classify(r: Result<(), ()>) -> Self {
        match r {
            Ok(()) => BugType::ValidationBug,
            Err(()) => BugType::ProofGenerationBug,
        }
    }
}

impl std::fmt::Display for BugType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BugType::ProofGenerationBug => write!(f, "Completeness bug (validation failed)"),
            BugType::ValidationBug => write!(f, "Soundness bug (validation passed)"),
        }
    }
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct BugReport {
    pub seed_program: String,
    pub circuit: CircuitKind,
    pub bug_type: BugType,
    pub mutated_input: StoredProofInputs,
    pub mutations: Vec<MutationRecord>,
}

impl BugReport {
    /// Constructs a bug report from a classified mutated input.
    pub fn new(input: MutatedInput, bug_type: BugType) -> Self {
        Self {
            seed_program: input.original.seed_program,
            circuit: input.original.circuit,
            bug_type,
            mutated_input: input.mutated_input,
            mutations: input.mutations,
        }
    }
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct CrashArtifact {
    pub id: u64,
    pub seed_program: String,
    pub circuit: CircuitKind,
    pub step: CrashStep,
    pub bug_type: BugType,
    pub mutated_input: StoredProofInputs,
    pub mutations: Vec<MutationRecord>,
}

impl CrashArtifact {
    /// Constructs the persisted crash artifact for an interesting fuzzing outcome.
    pub fn new(id: u64, report: BugReport) -> Self {
        let step = match report.bug_type {
            BugType::ProofGenerationBug => CrashStep::Prover,
            BugType::ValidationBug => CrashStep::Validator,
        };

        Self {
            id,
            seed_program: report.seed_program,
            circuit: report.circuit,
            step,
            bug_type: report.bug_type,
            mutated_input: report.mutated_input,
            mutations: report.mutations,
        }
    }

    /// Returns the crash file name that should be used when persisting this artifact.
    pub fn file_name(&self) -> String {
        format!(
            "id:{:06},src:{},circ:{},step:{}.json",
            self.id,
            self.seed_program,
            self.circuit.slug(),
            self.step.slug()
        )
    }

    /// Serializes and writes this crash artifact to the given path.
    pub fn write(&self, path: &Path) -> io::Result<()> {
        let payload = serde_json::to_vec_pretty(self).map_err(|err| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "failed to serialize crash artifact `{}`: {err}",
                    path.display()
                ),
            )
        })?;
        fs::write(path, payload)
    }

    /// Reads and deserializes a persisted crash artifact.
    pub fn read(path: &Path) -> io::Result<Self> {
        let payload = fs::read(path)?;
        serde_json::from_slice(&payload).map_err(|err| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "failed to deserialize crash artifact `{}`: {err}",
                    path.display()
                ),
            )
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CrashStep {
    Prover,
    Validator,
}

impl CrashStep {
    pub fn slug(&self) -> &'static str {
        match self {
            Self::Prover => "prover",
            Self::Validator => "validator",
        }
    }
}
