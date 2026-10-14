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

/// The setup cap every entry of an artifact's `setups` must carry: the
/// profile config's `cap_size` of the artifact's final proof layer.
pub(super) fn expected_setup_cap_size(target: ProofTarget) -> usize {
    let (profile, circuit) = if target >= ProofTarget::L1Feeder {
        (ProofProfile::L1Feeder, UnrolledCircuitType::Unified22)
    } else {
        (ProofProfile::Standard, UnrolledCircuitType::Unified)
    };
    profile
        .prover_config(
            circuit.get_domain_size_log2() as usize,
            COMPILED_SECURITY_LEVEL.to_prover(),
        )
        .cap_size
}

pub(super) fn validate_artifact_envelope(artifact: &ProofArtifact) -> Result<(), String> {
    match artifact.schema_version {
        ARTIFACT_SCHEMA_VERSION => {}
        LEGACY_ARTIFACT_SCHEMA_VERSION if artifact.target < ProofTarget::L1Feeder => {}
        LEGACY_ARTIFACT_SCHEMA_VERSION => {
            return Err(format!(
                "stale {:?} proof artifact: schema_version {LEGACY_ARTIFACT_SCHEMA_VERSION} feeder artifacts predate the 2^22 feeder chain (expected {ARTIFACT_SCHEMA_VERSION})",
                artifact.target
            ))
        }
        version => {
            return Err(format!(
                "unsupported proof artifact schema_version {version} (expected {ARTIFACT_SCHEMA_VERSION})"
            ))
        }
    }
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
    feeder_proof_instances(proof, Some(1))?;
    let family = UnrolledCircuitType::Unified22.get_family_idx() as u32;
    let compiled = proof
        .compiled_riscv_circuits
        .get(&family)
        .ok_or("feeder proof carries no compiled unified circuit")?;
    if compiled.trace_len != UnrolledCircuitType::Unified22.get_domain_size() {
        return Err(format!(
            "feeder proof circuit has trace length {}, expected {}",
            compiled.trace_len,
            UnrolledCircuitType::Unified22.get_domain_size()
        ));
    }
    let expected_schedule = ProofProfile::L1Feeder
        .prover_config(
            UnrolledCircuitType::Unified22.get_domain_size_log2() as usize,
            COMPILED_SECURITY_LEVEL.to_prover(),
        )
        .whir_schedule;
    for instance in &proof.riscv_proofs[&family] {
        if instance.whir_proof.whir_schedule != expected_schedule {
            return Err(
                "feeder proof instance was not proven under the L1 feeder WHIR schedule".into(),
            );
        }
    }
    Ok(())
}

/// `ProofTarget::L1` needs the wrap circuit the wrap program is linked for:
/// the 2^21 domain of [`L1_WRAP_PROGRAM_CYCLE_LIMIT`] and the program's ROM
/// geometry. Until W3 supplies that circuit the target is rejected before
/// any registration; there is no fallback to the old wrap or the old chain.
pub(super) fn validate_l1_wrap_activation() -> Result<(), String> {
    let wrap_program = FsvProgram::UnifiedRecursionLayerL1FeederWrap;
    let circuit_domain = CircuitType::L1Wrap.get_domain_size();
    if circuit_domain != L1_WRAP_PROGRAM_CYCLE_LIMIT {
        return Err(format!(
            "ProofTarget::L1 requires the 2^{} L1 wrap circuit of the wrap program; the active CircuitType::L1Wrap proves 2^{} cycles (W3)",
            L1_WRAP_PROGRAM_CYCLE_LIMIT.trailing_zeros(),
            circuit_domain.trailing_zeros()
        ));
    }
    if unified_reduced_machine_proth120::ROM != wrap_program.rom() {
        return Err(format!(
            "ProofTarget::L1 requires an L1 wrap circuit with the {} byte ROM of the wrap program; the active circuit has a {} byte ROM (W3)",
            wrap_program.rom().byte_size(),
            unified_reduced_machine_proth120::ROM.byte_size()
        ));
    }
    Ok(())
}

pub(super) fn advance_l1_wrap(
    backend: &mut dyn ProveBackend,
    fsv: &FsvPrograms,
    mut state: RecursionState,
    batch_id: u64,
) -> Result<RecursionState, String> {
    validate_l1_wrap_activation()?;
    validate_last_feeder_proof(&state.proof)?;
    let start = Instant::now();
    let (bin, text) = &fsv.feeder_wrap;
    let nd_words = build_unified_stream(&state.setups, &state.proof);
    let native_output = native_verify_unified_l1_feeder(nd_words.clone())?;
    let report = ProductionFeederVerifier
        .wrap_run(&fsv.feeder_wrap, nd_words.clone())
        .map_err(|e| format!("L1Wrap feeder verification failed: {e}"))?;
    validate_wrap_report(&report, &native_output)
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
