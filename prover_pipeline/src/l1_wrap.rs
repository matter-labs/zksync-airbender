use super::*;
use execution_prover::CommitmentMode;
use prover::gkr::prover_config::example_configs::{
    EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS, EVM_PRODUCTION_PACK_LOG2,
};
use std::sync::OnceLock;

pub const L1_PROFILE_TAG: &str = "l1_wrap";

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct L1Bundle {
    pub proof: L1Proof,
    pub commitment_mode: CommitmentMode,
    pub profile_tag: String,
    pub layout_keccak: [u8; 32],
}

pub fn l1_layout_keccak() -> [u8; 32] {
    static HASH: OnceLock<[u8; 32]> = OnceLock::new();
    *HASH.get_or_init(|| keccak256(unified_reduced_machine_proth120::LAYOUT_JSON.as_bytes()))
}

impl L1Bundle {
    fn from_result(result: L1WrapResult) -> Result<Self, String> {
        let bundle = Self {
            proof: result.proof,
            commitment_mode: result.commitment_mode,
            profile_tag: L1_PROFILE_TAG.into(),
            layout_keccak: l1_layout_keccak(),
        };
        bundle.validate()?;
        Ok(bundle)
    }

    fn validate(&self) -> Result<(), String> {
        if self.profile_tag != L1_PROFILE_TAG {
            return Err("L1 bundle profile_tag must be l1_wrap".into());
        }
        if self.layout_keccak != l1_layout_keccak() {
            return Err("L1 bundle layout_keccak does not match the embedded Proth layout".into());
        }
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
        (ProofTarget::L1, Some(bundle)) => {
            bundle.validate()?;
            chain_unrolled_layers(artifact)?;
        }
        (ProofTarget::L1, None) => return Err("L1 artifact must contain an l1 bundle".into()),
        (_, Some(_)) => return Err("non-L1 artifact must not contain an l1 bundle".into()),
        (_, None) => {}
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
    state: RecursionState,
    batch_id: u64,
) -> Result<RecursionState, String> {
    wrap_feeder_checkpoint(state, |state| {
        let (bin, text) = &fsv.feeder;
        measure_then_wrap(
            backend,
            L1WrapRequest {
                batch_id,
                bin,
                text,
                nd_words: build_unified_stream(&state.setups, &state.proof),
            },
            measure_fsv_run,
        )
    })
}

fn wrap_feeder_checkpoint(
    mut state: RecursionState,
    wrap: impl FnOnce(&RecursionState) -> Result<(L1WrapResult, u64), String>,
) -> Result<RecursionState, String> {
    if state.stage != ProofTarget::L1Feeder {
        return Err("L1Wrap requires an L1Feeder checkpoint".into());
    }
    validate_feeder_proof_shape(&state.proof)?;
    let start = Instant::now();
    let (result, cycles) = wrap(&state)?;
    state.l1 = Some(L1Bundle::from_result(result)?);
    state.l1_feeder_verifier_cycles = Some(cycles);
    state.timings.l1_wrap_ms = Some(elapsed_ms(start));
    state.stage = ProofTarget::L1;
    Ok(state)
}

fn measure_then_wrap(
    backend: &mut dyn ProveBackend,
    request: L1WrapRequest<'_>,
    measure: impl FnOnce(&[u32], &[u32], Vec<u32>, usize) -> Result<u64, String>,
) -> Result<(L1WrapResult, u64), String> {
    let cycles = measure(
        request.bin,
        request.text,
        request.nd_words.clone(),
        L1_WRAP_CYCLES_BOUND,
    )
    .map_err(|e| format!("L1Wrap feeder verification failed: {e}"))?;
    if cycles == 0 || cycles > L1_WRAP_CYCLES_BOUND as u64 {
        return Err(format!(
            "L1Wrap feeder verifier used {cycles} cycles, outside the wrap bound"
        ));
    }
    Ok((backend.prove_l1_wrap(request)?, cycles))
}

#[cfg(test)]
mod tests;
