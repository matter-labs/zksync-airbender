use std::alloc::Global;
use std::fmt;

use prover::merkle_trees::DefaultTreeConstructor;
use prover::merkle_trees::MerkleTreeCapVarLength;
use prover::merkle_trees::MerkleTreeConstructor as _;
use prover::prover_stages::unrolled_prover::UnrolledModeProof;
use prover::prover_stages::ProverData;
use prover::worker::Worker;
use prover::DEFAULT_TRACE_PADDING_MULTIPLE;

use crate::prover::circuits::CircuitRegistry;
use crate::prover::crashes::BugType;
use crate::prover::seeds::StoredProofInputs;
use crate::prover::triage::analysis::oracle::OracleShapeSummary;
use crate::rv32im::prover::circuits::add_sub_lui_auipc_mop::AddSubLuiAuipcMop;
use crate::rv32im::prover::circuits::jump_branch_slt::JumpBranchSltCircuit;
use crate::rv32im::prover::circuits::load_store::LoadStoreWordCircuit;
use crate::rv32im::prover::circuits::mul_div::MulDivCircuit;
use crate::rv32im::prover::circuits::subword_load_store::LoadStoreSubwordCircuit;
use crate::rv32im::prover::circuits::xor_and_or_shift_csr::XorAndOrShiftCsrCircuit;
use crate::rv32im::prover::circuits::CircuitProver;
use crate::rv32im::prover::circuits::ProofInputs;
use crate::rv32im::prover::sets::ReadSets;
use crate::rv32im::prover::sets::WriteSets;
use crate::rv32im::prover::Prover;

pub mod oracle;

/// Ordered comparison points used while replaying base and mutated inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
pub enum CheckpointKind {
    Stage1,
    Stage2,
    Stage3,
    Proof,
    Validator,
}

impl fmt::Display for CheckpointKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Stage1 => write!(f, "stage1"),
            Self::Stage2 => write!(f, "stage2"),
            Self::Stage3 => write!(f, "stage3"),
            Self::Proof => write!(f, "proof"),
            Self::Validator => write!(f, "validator"),
        }
    }
}

/// Human-readable description of the first checkpoint that diverged.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct CheckpointDiff {
    checkpoint: CheckpointKind,
    detail: String,
}

impl CheckpointDiff {
    fn new(checkpoint: CheckpointKind, detail: String) -> Self {
        Self { checkpoint, detail }
    }

    pub fn stage1(detail: String) -> Self {
        Self::new(CheckpointKind::Stage1, detail)
    }
    pub fn stage2(detail: String) -> Self {
        Self::new(CheckpointKind::Stage2, detail)
    }
    pub fn stage3(detail: String) -> Self {
        Self::new(CheckpointKind::Stage3, detail)
    }
    pub fn proof(detail: String) -> Self {
        Self::new(CheckpointKind::Proof, detail)
    }
    pub fn validator(detail: String) -> Self {
        Self::new(CheckpointKind::Validator, detail)
    }

    pub fn checkpoint(&self) -> CheckpointKind {
        self.checkpoint
    }

    pub fn detail(&self) -> &str {
        &self.detail
    }
}

#[derive(Clone, serde::Serialize)]
struct Fingerprint<T> {
    signature: String,
    payload: T,
}

impl<T: serde::Serialize> Fingerprint<T> {
    fn new(payload: T) -> Self {
        let signature = fingerprint_serializable(&payload);
        Self { signature, payload }
    }
}

impl<T: serde::Serialize> From<T> for Fingerprint<T> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<T> PartialEq for Fingerprint<T> {
    fn eq(&self, other: &Self) -> bool {
        self.signature == other.signature
    }
}

impl<T> Eq for Fingerprint<T> {}

impl<T: std::fmt::Debug> std::fmt::Debug for Fingerprint<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "fingerprint({}, {:?})", self.signature, self.payload)
        } else {
            write!(f, "{}", self.signature)
        }
    }
}

/// Reduced replay trace used for deterministic comparison during triage.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct AnalysisTrace {
    oracle_shape: OracleShapeSummary,
    stage1: Option<Fingerprint<Stage1Summary>>,
    stage2: Option<Fingerprint<Stage2Summary>>,
    stage3: Option<Fingerprint<Stage3Summary>>,
    proof: Option<Fingerprint<UnrolledModeProof>>,
    validator_outcome: Option<BugType>,
}

macro_rules! fingerprint_diff {
    ($v:expr, $lhs:expr, $rhs:expr, $name:ident) => {
        if $lhs.$name != $rhs.$name {
            $v.push(CheckpointDiff::$name(format!(
                "{} fingerprint changed from {:?} to {:?}",
                stringify!($name),
                $lhs.$name,
                $rhs.$name
            )));
        }
    };
}

impl AnalysisTrace {
    pub fn empty(oracle_shape: OracleShapeSummary) -> Self {
        Self {
            oracle_shape,
            stage1: Default::default(),
            stage2: Default::default(),
            stage3: Default::default(),
            proof: Default::default(),
            validator_outcome: Default::default(),
        }
    }

    fn new(
        oracle_shape: OracleShapeSummary,
        stage1: Option<Fingerprint<Stage1Summary>>,
        stage2: Option<Fingerprint<Stage2Summary>>,
        stage3: Option<Fingerprint<Stage3Summary>>,
        proof: Option<Fingerprint<UnrolledModeProof>>,
        validator_outcome: Option<BugType>,
    ) -> Self {
        Self {
            oracle_shape,
            stage1,
            stage2,
            stage3,
            proof,
            validator_outcome,
        }
    }

    /// Returns the earliest checkpoint where the replay traces differ.
    pub fn diff(&self, other: &AnalysisTrace) -> Vec<CheckpointDiff> {
        let mut diffs = vec![];
        // Checkpoints are ordered by prover progression so the first mismatch approximates the
        // earliest stage where the mutation had semantic effect on execution.
        fingerprint_diff!(diffs, self, other, stage1);
        fingerprint_diff!(diffs, self, other, stage2);
        fingerprint_diff!(diffs, self, other, stage3);
        fingerprint_diff!(diffs, self, other, proof);
        if self.validator_outcome != other.validator_outcome {
            diffs.push(CheckpointDiff::validator(format!(
                "validator outcome changed from {:?} to {:?}",
                self.validator_outcome, other.validator_outcome
            )));
        }

        diffs
    }
}

/// Executes a single replay and records only the compact checkpoints used for triage.
pub fn analyze_once(
    registry: &CircuitRegistry,
    input: &StoredProofInputs,
) -> anyhow::Result<AnalysisTrace> {
    // We keep the trace deliberately compact and replay-derived. Structural differences in
    // `StoredProofInputs` are guaranteed by mutation, so they are not evidence of semantic effect.
    // Instead we record fingerprints from semantic prover checkpoints plus the final verifier
    // result.
    let oracle_shape = OracleShapeSummary::from_input(input);

    let (stage1, stage2, stage3, proof, validator_outcome) = match registry.analyze(input) {
        AnalysisAttempt::Crash => (None, None, None, None, None),
        AnalysisAttempt::Success {
            semantics,
            validator_outcome,
        } => (
            Some(semantics.stage1),
            Some(semantics.stage2),
            Some(semantics.stage3),
            Some(semantics.proof),
            Some(validator_outcome),
        ),
    };

    Ok(AnalysisTrace::new(
        oracle_shape,
        stage1,
        stage2,
        stage3,
        proof,
        validator_outcome,
    ))
}

#[derive(Clone, Debug)]
enum AnalysisAttempt {
    Crash,
    Success {
        semantics: Box<ReplaySemantics>,
        validator_outcome: BugType,
    },
}

impl CircuitRegistry {
    fn analyze(&self, input: &StoredProofInputs) -> AnalysisAttempt {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| match input {
            StoredProofInputs::AddSubLuiAuipcMop(inputs) => {
                self.analyze_impl(AddSubLuiAuipcMop, inputs, AddSubLuiAuipcMop::validate_proof)
            }
            StoredProofInputs::XorAndOrShiftCsr(inputs) => self.analyze_impl(
                XorAndOrShiftCsrCircuit::new(),
                inputs,
                XorAndOrShiftCsrCircuit::validate_proof,
            ),
            StoredProofInputs::MulDiv(inputs) => {
                self.analyze_impl(MulDivCircuit, inputs, MulDivCircuit::validate_proof)
            }
            StoredProofInputs::JumpBranchSlt(inputs) => self.analyze_impl(
                JumpBranchSltCircuit,
                inputs,
                JumpBranchSltCircuit::validate_proof,
            ),
            StoredProofInputs::LoadStore(inputs, bytecode) => self.analyze_impl(
                LoadStoreWordCircuit::new(bytecode),
                inputs,
                LoadStoreWordCircuit::validate_proof,
            ),
            StoredProofInputs::SubwordLoadStore(inputs, bytecode) => self.analyze_impl(
                LoadStoreSubwordCircuit::new(bytecode),
                inputs,
                LoadStoreSubwordCircuit::validate_proof,
            ),
            StoredProofInputs::InitsAndTeardowns(_) => todo!(),
            StoredProofInputs::BlakeDelegation(_) => todo!(),
            StoredProofInputs::KeccakDelegation(_) => todo!(),
        }))
        .unwrap_or(AnalysisAttempt::Crash)
    }

    fn analyze_impl<const N: u8, C, F>(
        &self,
        cprover: C,
        inputs: &ProofInputs<C::BufferElt>,
        validate: F,
    ) -> AnalysisAttempt
    where
        C: CircuitProverAnalysis<N>,
        ProofInputs<C::BufferElt>: Clone,
        F: Fn(&ProofInputs<C::BufferElt>, &UnrolledModeProof) -> Result<(), ()>,
    {
        let prover = Prover::new();
        log::info!("Generating proof...");
        let semantics = Box::new(cprover.prove_from_inputs_with_semantics(
            inputs.clone(),
            &prover,
            prover.worker(),
        ));
        log::info!("Validating proof...");
        let validator_outcome = BugType::classify(validate(inputs, semantics.proof()));
        AnalysisAttempt::Success {
            semantics,
            validator_outcome,
        }
    }
}

trait CircuitProverAnalysis<const N: u8>: CircuitProver<N> {
    fn prove_from_inputs_with_semantics(
        &self,
        inputs: ProofInputs<Self::BufferElt>,
        prover: &Prover,
        worker: &Worker,
    ) -> ReplaySemantics {
        let oracle = self.create_oracle(&inputs.buffer, &inputs.witness_gen_data);
        let (prover_data, proof) = self.generate_proof_with_data(
            &inputs,
            prover,
            worker,
            &oracle,
            &mut ReadSets::empty(),
            &mut WriteSets::empty(),
            None,
        );
        ReplaySemantics::from_prover_data(&prover_data, proof)
    }
}

impl<const N: u8, T: CircuitProver<N>> CircuitProverAnalysis<N> for T {}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReplaySemantics {
    stage1: Fingerprint<Stage1Summary>,
    stage2: Fingerprint<Stage2Summary>,
    stage3: Fingerprint<Stage3Summary>,
    proof: Fingerprint<UnrolledModeProof>,
}

impl ReplaySemantics {
    fn proof(&self) -> &UnrolledModeProof {
        &self.proof.payload
    }

    fn from_prover_data(
        prover_data: &ProverData<DEFAULT_TRACE_PADDING_MULTIPLE, Global, DefaultTreeConstructor>,
        proof: UnrolledModeProof,
    ) -> Self {
        Self {
            stage1: Stage1Summary::from(prover_data).into(),
            stage2: Stage2Summary::from(prover_data).into(),
            stage3: Stage3Summary::from(prover_data).into(),
            proof: proof.into(),
        }
    }
}

#[derive(Clone, Debug, serde::Serialize)]
pub struct Stage1Summary {
    num_witness_columns: usize,
    witness_tree_caps: Vec<MerkleTreeCapVarLength>,
    memory_tree_caps: Vec<MerkleTreeCapVarLength>,
}

impl From<&ProverData<DEFAULT_TRACE_PADDING_MULTIPLE, Global, DefaultTreeConstructor>>
    for Stage1Summary
{
    fn from(
        prover_data: &ProverData<DEFAULT_TRACE_PADDING_MULTIPLE, Global, DefaultTreeConstructor>,
    ) -> Self {
        Self {
            num_witness_columns: prover_data.stage_1_result.num_witness_columns,
            witness_tree_caps: DefaultTreeConstructor::dump_caps(
                &prover_data.stage_1_result.witness_tree,
            ),
            memory_tree_caps: DefaultTreeConstructor::dump_caps(
                &prover_data.stage_1_result.memory_tree,
            ),
        }
    }
}

#[derive(Clone, Debug, serde::Serialize)]
pub struct Stage2Summary {
    tree_caps: Vec<MerkleTreeCapVarLength>,
    lookup_argument_linearization_challenges: Vec<prover::field::Mersenne31Quartic>,
    lookup_argument_gamma: prover::field::Mersenne31Quartic,
    decoder_table_linearization_challenges: Vec<prover::field::Mersenne31Quartic>,
    decoder_table_gamma: prover::field::Mersenne31Quartic,
    grand_product_accumulator: prover::field::Mersenne31Quartic,
    sum_over_delegation_poly: prover::field::Mersenne31Quartic,
    pow_challenge: u64,
}

impl From<&ProverData<DEFAULT_TRACE_PADDING_MULTIPLE, Global, DefaultTreeConstructor>>
    for Stage2Summary
{
    fn from(
        prover_data: &ProverData<DEFAULT_TRACE_PADDING_MULTIPLE, Global, DefaultTreeConstructor>,
    ) -> Self {
        Self {
            tree_caps: DefaultTreeConstructor::dump_caps(&prover_data.stage_2_result.trees),
            lookup_argument_linearization_challenges: prover_data
                .stage_2_result
                .lookup_argument_linearization_challenges
                .to_vec(),
            lookup_argument_gamma: prover_data.stage_2_result.lookup_argument_gamma,
            decoder_table_linearization_challenges: prover_data
                .stage_2_result
                .decoder_table_linearization_challenges
                .to_vec(),
            decoder_table_gamma: prover_data.stage_2_result.decoder_table_gamma,
            grand_product_accumulator: prover_data.stage_2_result.grand_product_accumulator,
            sum_over_delegation_poly: prover_data.stage_2_result.sum_over_delegation_poly,
            pow_challenge: prover_data.stage_2_result.pow_challenge,
        }
    }
}

#[derive(Clone, Debug, serde::Serialize)]
pub struct Stage3Summary {
    tree_caps: Vec<MerkleTreeCapVarLength>,
    quotient_alpha: prover::field::Mersenne31Quartic,
    quotient_beta: prover::field::Mersenne31Quartic,
    pow_challenge: u64,
}

impl From<&ProverData<DEFAULT_TRACE_PADDING_MULTIPLE, Global, DefaultTreeConstructor>>
    for Stage3Summary
{
    fn from(
        prover_data: &ProverData<DEFAULT_TRACE_PADDING_MULTIPLE, Global, DefaultTreeConstructor>,
    ) -> Self {
        Self {
            tree_caps: DefaultTreeConstructor::dump_caps(
                &prover_data.quotient_commitment_result.trees,
            ),
            quotient_alpha: prover_data.quotient_commitment_result.quotient_alpha,
            quotient_beta: prover_data.quotient_commitment_result.quotient_beta,
            pow_challenge: prover_data.quotient_commitment_result.pow_challenge,
        }
    }
}

fn fingerprint_serializable<T: serde::Serialize>(value: &T) -> String {
    use sha2::Digest;

    let payload = serde_json::to_vec(value).expect("checkpoint summary must serialize");
    let digest = sha2::Sha256::digest(payload);
    digest.iter().map(|byte| format!("{byte:02x}")).collect()
}
