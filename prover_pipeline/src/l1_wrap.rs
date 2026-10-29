use super::*;
use execution_prover::OperationMode;

/// The wrap identity `ProofTarget::L1` proves.
pub(super) const L1_WRAP_KIND: ExecutionKind = ExecutionKind::L1Wrap21;

/// The wrap circuit an L1 bundle was proven in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum L1WrapVersion {
    /// `ExecutionKind::L1Wrap21`: 2^21 trace, 512 KiB wrap ROM.
    #[serde(rename = "2p21")]
    Wrap2p21,
}

impl L1WrapVersion {
    pub fn kind(self) -> ExecutionKind {
        match self {
            Self::Wrap2p21 => ExecutionKind::L1Wrap21,
        }
    }

    fn of_kind(kind: ExecutionKind) -> Self {
        match kind {
            ExecutionKind::L1Wrap21 => Self::Wrap2p21,
            other => panic!("{other:?} is not an L1 wrap kind"),
        }
    }

    fn external_challenges_pow_bits(self) -> u32 {
        use prover::gkr::prover_config::example_configs::l1_wrap_2p21;
        match self {
            Self::Wrap2p21 => l1_wrap_2p21::EXTERNAL_CHALLENGES_POW_BITS,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct L1Bundle {
    pub proof: L1Proof,
    pub operation_mode: OperationMode,
    pub wrap: L1WrapVersion,
}

impl L1Bundle {
    fn from_result(result: L1WrapResult) -> Self {
        Self {
            proof: result.proof,
            operation_mode: result.operation_mode,
            wrap: L1WrapVersion::of_kind(L1_WRAP_KIND),
        }
    }

    pub(crate) fn validate(&self) -> Result<(), String> {
        let active = L1WrapVersion::of_kind(L1_WRAP_KIND);
        if self.wrap != active {
            return Err(format!(
                "L1 bundle was proven in the {:?} wrap; this build proves the {active:?} wrap",
                self.wrap
            ));
        }
        let external_challenges_pow_bits = self.wrap.external_challenges_pow_bits();
        if !matches!(
            self.operation_mode,
            OperationMode::SingleChunk {
                external_challenges_pow_bits: e,
                ..
            } if e == external_challenges_pow_bits
        ) {
            return Err(format!(
                "L1 bundle requires a production single-chunk operation for the {:?} wrap",
                self.wrap
            ));
        }
        Ok(())
    }
}

/// The setup cap every entry of an artifact's `setups` must carry: the
/// profile config's `cap_size` of the artifact's final proof layer.
pub(super) fn expected_setup_cap_size(target: ProofTarget) -> usize {
    let (profile, circuit) = if target >= ProofTarget::L1Feeder {
        (ProofProfile::L1Feeder, UnrolledCircuitType::Unified22)
    } else {
        (ProofProfile::Standard, UnrolledCircuitType::Unified)
    };
    execution_prover::prover_config(
        CircuitType::Unrolled(circuit),
        profile,
        COMPILED_SECURITY_LEVEL.to_prover(),
    )
    .cap_size
}

pub(super) fn validate_artifact_envelope(artifact: &ProofArtifact) -> Result<(), String> {
    artifact.validate_schema()?;
    match (artifact.target, &artifact.l1) {
        (ProofTarget::L1, Some(bundle)) => bundle.validate()?,
        (ProofTarget::L1, None) => return Err("L1 artifact must contain an l1 bundle".into()),
        (_, Some(_)) => return Err("non-L1 artifact must not contain an l1 bundle".into()),
        (_, None) => {}
    }
    // serde bypasses the setup-cap constructor: repeat its shape check here
    setups::validate_setups_cap_size(&artifact.setups, expected_setup_cap_size(artifact.target))?;
    if artifact.target >= ProofTarget::L1Feeder {
        validate_last_feeder_proof(&artifact.proof)?;
    }
    Ok(())
}

/// The last feeder proof an artifact may carry: one 2^22 instance of the
/// reduced family under the feeder config, no delegation proofs.
pub(super) fn validate_last_feeder_proof(proof: &ProgramProof) -> Result<(), String> {
    if validate_feeder_proof(proof, Some(1))? != FeederProfile::C {
        return Err("the last feeder proof must be one C instance".into());
    }
    Ok(())
}

/// A feeder proof with a supported trace and the matching profile schedule.
pub(super) fn validate_feeder_proof(
    proof: &ProgramProof,
    expected: Option<usize>,
) -> Result<FeederProfile, String> {
    let instances = feeder_proof_instances(proof, expected)?;
    let family = UnrolledCircuitType::Unified.get_family_idx() as u32;
    let compiled = proof
        .compiled_riscv_circuits
        .get(&family)
        .ok_or("feeder proof carries no compiled unified circuit")?;
    let profile = FeederProfile::ALL
        .into_iter()
        .find(|profile| profile.circuit().get_domain_size() == compiled.trace_len)
        .ok_or_else(|| {
            format!(
                "feeder proof circuit has unsupported trace length {}",
                compiled.trace_len
            )
        })?;
    if profile == FeederProfile::C && instances != 1 {
        return Err("C is terminal and must contain one feeder instance".into());
    }
    let expected_schedule = profile.config().whir_schedule;
    for instance in &proof.riscv_proofs[&family] {
        if instance.whir_proof.whir_schedule != expected_schedule {
            return Err(format!("feeder proof instance was not proven under the {profile:?} L1 feeder WHIR schedule"));
        }
    }
    Ok(profile)
}

pub(super) fn advance_l1_wrap(
    backend: &mut dyn ProveBackend,
    fsv: &FsvPrograms,
    mut state: RecursionState,
    prepared: PreparedFeeder,
    batch_id: u64,
) -> Result<RecursionState, String> {
    validate_last_feeder_proof(&state.proof)?;
    let start = Instant::now();
    let (bin, text) = &fsv.feeder_wrap;
    let nd_words = prepared.nd_words;
    let result = backend.prove_l1_wrap(L1WrapRequest {
        batch_id,
        bin,
        text,
        nd_words,
    })?;
    log::info!("L1 wrap proved ({} cycles)", prepared.report.cycles);
    state.l1 = Some(L1Bundle::from_result(result));
    state.timings.l1_wrap_ms = Some(elapsed_ms(start));
    state.stage = ProofTarget::L1;
    Ok(state)
}

#[cfg(test)]
mod tests;
