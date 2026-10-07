use super::*;
use execution_prover::CommitmentMode;
use prover::gkr::prover_config::example_configs::{
    EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS, EVM_PRODUCTION_PACK_LOG2,
};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct L1Bundle {
    pub proof: L1Proof,
    pub commitment_mode: CommitmentMode,
}

impl L1Bundle {
    fn from_result(result: L1WrapResult) -> Self {
        Self {
            proof: result.proof,
            commitment_mode: result.commitment_mode,
        }
    }

    fn validate(&self) -> Result<(), String> {
        if !matches!(
            self.commitment_mode,
            CommitmentMode::MergedAndPackedMemoryAndWitness {
                pack_log2: EVM_PRODUCTION_PACK_LOG2,
                external_challenges_pow_bits: EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS,
                ..
            }
        ) {
            return Err("L1 bundle requires MergedAndPackedMemoryAndWitness with production packing parameters".into());
        }
        Ok(())
    }
}

pub(super) fn validate_artifact_envelope(artifact: &ProofArtifact) -> Result<(), String> {
    if artifact.schema_version != ARTIFACT_SCHEMA_VERSION {
        return Err(format!(
            "unsupported proof artifact schema_version {} (expected {})",
            artifact.schema_version, ARTIFACT_SCHEMA_VERSION
        ));
    }
    match (artifact.target, &artifact.l1) {
        (ProofTarget::L1, Some(bundle)) => bundle.validate()?,
        (ProofTarget::L1, None) => return Err("L1 artifact must contain an l1 bundle".into()),
        (_, Some(_)) => return Err("non-L1 artifact must not contain an l1 bundle".into()),
        (_, None) => {}
    }
    if artifact.target >= ProofTarget::L1Feeder {
        validate_feeder_proof_shape(&artifact.proof)?;
    }
    Ok(())
}

pub(super) fn validate_feeder_proof_shape(proof: &ProgramProof) -> Result<(), String> {
    let counts = ProofCounts::from_proof(proof);
    if counts.riscv_proof_count != 1 || counts.delegation_proof_count != 0 {
        return Err(
            "L1Feeder sidecar must contain one RISC-V proof and no delegation proofs".into(),
        );
    }
    Ok(())
}

pub(super) fn advance_l1_wrap(
    backend: &mut dyn ProveBackend,
    fsv: &FsvPrograms,
    mut state: RecursionState,
    batch_id: u64,
) -> Result<RecursionState, String> {
    validate_feeder_proof_shape(&state.proof)?;
    let start = Instant::now();
    let (bin, text) = &fsv.feeder;
    let nd_words = build_unified_stream(&state.setups, &state.proof);
    measure_fsv_run(bin, text, nd_words.clone(), L1_WRAP_CYCLES_BOUND)
        .map_err(|e| format!("L1Wrap feeder verification failed: {e}"))?;
    let result = backend.prove_l1_wrap(L1WrapRequest {
        batch_id,
        bin,
        text,
        nd_words,
    })?;
    state.l1 = Some(L1Bundle::from_result(result));
    state.timings.l1_wrap_ms = Some(elapsed_ms(start));
    state.stage = ProofTarget::L1;
    Ok(state)
}

#[cfg(test)]
mod tests;
