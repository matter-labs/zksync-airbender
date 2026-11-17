use super::*;
use execution_prover::OperationMode;

/// The wrap identity `ProofTarget::L1` proves.
pub(super) const L1_WRAP_KIND: ExecutionKind = ExecutionKind::L1Wrap;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct L1Bundle {
    pub proof: L1Proof,
    pub operation_mode: OperationMode,
}

impl L1Bundle {
    fn from_result(result: L1WrapResult) -> Self {
        Self {
            proof: result.proof,
            operation_mode: result.operation_mode,
        }
    }

    pub(crate) fn validate(&self) -> Result<(), String> {
        let external_challenges_pow_bits =
            prover::gkr::prover_config::example_configs::l1_wrap::EXTERNAL_CHALLENGES_POW_BITS;
        if !matches!(
            self.operation_mode,
            OperationMode::SingleChunk {
                external_challenges_pow_bits: e,
                ..
            } if e == external_challenges_pow_bits
        ) {
            return Err("L1 bundle requires a production single-chunk operation".into());
        }
        Ok(())
    }
}

/// The setup cap every entry of an artifact's `setups` must carry: the
/// profile config's `cap_size` of the artifact's final proof layer.
pub(super) fn expected_setup_cap_size(target: ProofTarget) -> usize {
    if target >= ProofTarget::Compression {
        ProofProfile::CompressionFinal
            .prover_config(
                CircuitType::Unrolled(UnrolledCircuitType::Unified22).get_domain_size_log2()
                    as usize,
                SoundnessMode::PessimisticConjecture,
            )
            .cap_size
    } else {
        CircuitType::Unrolled(UnrolledCircuitType::Unified)
            .prover_config(COMPILED_SECURITY_LEVEL.to_prover())
            .cap_size
    }
}

pub(super) fn validate_artifact_envelope(artifact: &ProofArtifact) -> Result<(), String> {
    match (artifact.target, &artifact.l1) {
        (ProofTarget::L1, Some(bundle)) => bundle.validate()?,
        (ProofTarget::L1, None) => return Err("L1 artifact must contain an l1 bundle".into()),
        (_, Some(_)) => return Err("non-L1 artifact must not contain an l1 bundle".into()),
        (_, None) => {}
    }
    // serde bypasses the setup-cap constructor: repeat its shape check here
    setups::validate_setups_cap_size(&artifact.setups, expected_setup_cap_size(artifact.target))?;
    if artifact.target >= ProofTarget::Compression {
        validate_compression_proof(&artifact.proof, CompressionProfile::Final, 1)?;
    }
    Ok(())
}

/// A compression proof must have the scheduled circuit, instance count and WHIR schedule.
pub(super) fn validate_compression_proof(
    proof: &ProgramProof,
    profile: CompressionProfile,
    instances: usize,
) -> Result<(), String> {
    let family = profile.circuit().get_family_idx() as u32;
    if proof.riscv_proofs.len() != 1 || !proof.riscv_proofs.contains_key(&family) {
        return Err(format!(
            "compression proof must carry the reduced-machine family {family} only"
        ));
    }
    if proof.riscv_proofs[&family].len() != instances {
        return Err(format!(
            "compression proof carries {} instance(s), expected {instances}",
            proof.riscv_proofs[&family].len()
        ));
    }
    if !proof.delegation_proofs.is_empty() {
        return Err("compression proof must carry no delegation proofs".into());
    }
    if proof.num_it_circuits != Some(1)
        || !proof.inits_and_teardown_proofs.is_empty()
        || proof.inits_and_teardowns_circuit.is_some()
    {
        return Err(
            "compression proof must carry exactly one embedded inits-and-teardowns instance".into(),
        );
    }
    if proof.compiled_riscv_circuits.len() != 1 {
        return Err("compression proof must carry one compiled unified circuit".into());
    }
    let compiled = proof
        .compiled_riscv_circuits
        .get(&family)
        .ok_or("compression proof carries no compiled unified circuit")?;
    if compiled.trace_len != profile.circuit().get_domain_size() {
        return Err(format!(
            "compression proof circuit has trace length {}, expected {:?}",
            compiled.trace_len,
            profile.circuit()
        ));
    }
    let expected_schedule = profile.config().whir_schedule;
    for instance in &proof.riscv_proofs[&family] {
        if instance.whir_proof.whir_schedule != expected_schedule {
            return Err(format!("compression proof instance was not proven under the {profile:?} compression WHIR schedule"));
        }
    }
    Ok(())
}

pub(super) fn advance_l1_wrap(
    backend: &mut dyn ProveBackend,
    fsv: &FsvPrograms,
    mut state: RecursionState,
    batch_id: u64,
) -> RecursionState {
    let start = Instant::now();
    let guest = fsv
        .compression_wrap
        .as_ref()
        .expect("L1 wrap guest was not loaded");
    let (bin, text) = (guest.bin(), guest.text());
    let nd_words =
        build_unified_stream(&state.setups, &state.proof, BlakeMode::BlakeSpecialOpcodes);
    let result = backend.prove_l1_wrap(L1WrapRequest {
        batch_id,
        bin,
        text,
        nd_words,
    });
    log::info!("L1 wrap proved");
    state.l1 = Some(L1Bundle::from_result(result));
    state.timings.l1_wrap_ms = Some(elapsed_ms(start));
    state.stage = ProofTarget::L1;
    state
}

#[cfg(test)]
mod tests;
