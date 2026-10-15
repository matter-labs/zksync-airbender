use super::*;
use execution_prover::{l1_wrap_packing, CommitmentMode};

/// The wrap identity `ProofTarget::L1` proves.
pub(super) const L1_WRAP_KIND: ExecutionKind = ExecutionKind::L1Wrap21;

/// The wrap circuit an L1 bundle was proven in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "SerializedL1WrapVersion")]
pub enum L1WrapVersion {
    /// `ExecutionKind::L1Wrap21`: 2^21 trace, 512 KiB wrap ROM.
    #[serde(rename = "2p21")]
    Wrap2p21,
}

/// Every wrap version name a bundle may carry, including the retired 2^22
/// wrap, so that an old bundle or checkpoint fails by name before any setup.
#[derive(Deserialize)]
enum SerializedL1WrapVersion {
    #[serde(rename = "2p22")]
    Retired2p22,
    #[serde(rename = "2p21")]
    Wrap2p21,
}

pub(super) const RETIRED_2P22_WRAP: &str =
    "the L1 bundle was proven in the retired 2^22 wrap (\"2p22\"); this build proves only the 2^21 wrap (\"2p21\")";

impl TryFrom<SerializedL1WrapVersion> for L1WrapVersion {
    type Error = &'static str;

    fn try_from(version: SerializedL1WrapVersion) -> Result<Self, Self::Error> {
        match version {
            SerializedL1WrapVersion::Retired2p22 => Err(RETIRED_2P22_WRAP),
            SerializedL1WrapVersion::Wrap2p21 => Ok(Self::Wrap2p21),
        }
    }
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

    fn circuit_type(self) -> CircuitType {
        self.kind().unified_circuit().unwrap()
    }

    fn circuit_artifact(
        self,
    ) -> prover::cs::gkr_compiler::GKRCircuitArtifact<prover::field::Proth120> {
        match self {
            Self::Wrap2p21 => unified_reduced_machine_proth120::l1_wrap_2p21::circuit_artifact(),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct L1Bundle {
    pub proof: L1Proof,
    pub commitment_mode: CommitmentMode,
    pub wrap: L1WrapVersion,
}

impl L1Bundle {
    fn from_result(result: L1WrapResult) -> Self {
        Self {
            proof: result.proof,
            commitment_mode: result.commitment_mode,
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
        let circuit_type = self.wrap.circuit_type();
        let (pack_log2, external_challenges_pow_bits) = l1_wrap_packing(circuit_type);
        if !matches!(
            self.commitment_mode,
            CommitmentMode::MergedAndPackedMemoryAndWitness {
                pack_log2: p,
                external_challenges_pow_bits: e,
                ..
            } if p == pack_log2 && e == external_challenges_pow_bits
        ) {
            return Err(format!(
                "L1 bundle requires MergedAndPackedMemoryAndWitness with the {:?} production packing parameters",
                self.wrap
            ));
        }
        validate_l1_proof_layout(&self.proof, self.wrap)
    }
}

/// The shape of an L1 wrap proof under its version's config: GKR layer round
/// counts and round messages; the WHIR schedule, the packed base oracles
/// (setup, merged memory and witness), the intermediate oracles, and the
/// query, leaf, path, nonce and final-polynomial counts. Run before a bundle
/// is flattened, exported or resumed.
fn validate_l1_proof_layout(proof: &L1Proof, wrap: L1WrapVersion) -> Result<(), String> {
    let circuit_type = wrap.circuit_type();
    let trace_len_log2 = circuit_type.get_domain_size_log2() as usize;
    let config =
        ProofProfile::L1Wrap.prover_config(trace_len_log2, COMPILED_SECURITY_LEVEL.to_prover());
    let (pack_log2, _) = l1_wrap_packing(circuit_type);
    let mismatch = |what: &str, got: usize, expected: usize| {
        if got == expected {
            Ok(())
        } else {
            Err(format!(
                "L1 bundle ({wrap:?}) has {got} {what}, expected {expected}"
            ))
        }
    };

    let circuit = wrap.circuit_artifact();
    let standard_layers = circuit.layers.len();
    let dimension_reducing_layers = trace_len_log2 - config.sumcheck_explicit_output_size_log_2;
    mismatch(
        "GKR layers",
        proof.sumcheck_intermediate_values.len(),
        standard_layers + dimension_reducing_layers,
    )?;
    for layer in 0..standard_layers + dimension_reducing_layers {
        let values = proof
            .sumcheck_intermediate_values
            .get(&layer)
            .ok_or_else(|| format!("L1 bundle ({wrap:?}) has no GKR layer {layer}"))?;
        let expected = if layer < standard_layers {
            trace_len_log2
        } else {
            trace_len_log2 - 1 - (layer - standard_layers)
        };
        mismatch(
            &format!("sumcheck rounds in GKR layer {layer}"),
            values.sumcheck_num_rounds,
            expected,
        )?;
        mismatch(
            &format!("round messages in GKR layer {layer}"),
            values.internal_round_coefficients.len(),
            expected,
        )?;
        if !values.internal_round_coefficients.iter().all(|round| {
            matches!(
                round,
                prover::gkr::prover::SumcheckRoundCoefficients::Multilinear(_)
            )
        }) {
            return Err(format!(
                "L1 bundle ({wrap:?}) GKR layer {layer} has a non-multilinear round message"
            ));
        }
    }

    let whir = &proof.whir_proof;
    let schedule = &config.whir_schedule;
    if whir.whir_schedule != *schedule {
        return Err(format!(
            "L1 bundle ({wrap:?}) was not proven under its WHIR schedule"
        ));
    }
    let rounds = schedule.whir_steps_schedule.len();
    let folds: usize = schedule.whir_steps_schedule.iter().sum();
    let message_log2 = trace_len_log2 + pack_log2;
    let cap_log2 = schedule.cap_size.trailing_zeros() as usize;
    mismatch("WHIR PoW nonces", whir.pow_nonces.len(), rounds)?;
    mismatch(
        "WHIR sumcheck polynomials",
        whir.sumcheck_polys.len(),
        folds,
    )?;
    mismatch(
        "WHIR final monomials",
        whir.final_monomials.len(),
        1 << (trace_len_log2 + pack_log2 - folds),
    )?;
    mismatch(
        "WHIR intermediate oracles",
        whir.intermediate_whir_oracles.len(),
        rounds - 1,
    )?;
    // packed mode: the setup and the merged memory+witness oracles, each
    // packed by 2^pack_log2 columns; the separate witness oracle is empty
    let first_fold = schedule.whir_steps_schedule[0];
    let base_path_len =
        message_log2 + schedule.base_lde_factor.trailing_zeros() as usize - first_fold - cap_log2;
    let setup_columns = circuit.generic_lookup_tables_width.div_ceil(1 << pack_log2);
    let merged_columns = (circuit.memory_layout.total_width + circuit.witness_layout.total_width)
        .div_ceil(1 << pack_log2);
    for (name, base, columns) in [
        ("setup", &whir.setup_commitment, setup_columns),
        ("merged memory", &whir.memory_commitment, merged_columns),
        ("witness", &whir.witness_commitment, 0),
    ] {
        mismatch(
            &format!("WHIR {name} oracle columns"),
            base.num_columns,
            columns,
        )?;
        mismatch(
            &format!("WHIR {name} oracle evaluations"),
            base.evals.len(),
            columns,
        )?;
        let queries = if columns == 0 {
            0
        } else {
            schedule.whir_queries_schedule[0]
        };
        mismatch(
            &format!("WHIR {name} oracle queries"),
            base.queries.len(),
            queries,
        )?;
        for query in &base.queries {
            mismatch(
                &format!("WHIR {name} oracle leaf values"),
                query.leaf_values_concatenated.len(),
                columns << first_fold,
            )?;
            mismatch(
                &format!("WHIR {name} oracle path nodes"),
                query.path.len(),
                base_path_len,
            )?;
        }
    }
    let mut poly_log2 = message_log2 - first_fold;
    for (round, oracle) in whir.intermediate_whir_oracles.iter().enumerate() {
        let fold = schedule.whir_steps_schedule[round + 1];
        let codeword_log2 =
            poly_log2 + schedule.whir_steps_lde_factors[round].trailing_zeros() as usize;
        mismatch(
            &format!("WHIR round {} queries", round + 1),
            oracle.queries.len(),
            schedule.whir_queries_schedule[round + 1],
        )?;
        for query in &oracle.queries {
            mismatch(
                &format!("WHIR round {} leaf values", round + 1),
                query.leaf_values_concatenated.len(),
                1 << fold,
            )?;
            mismatch(
                &format!("WHIR round {} path nodes", round + 1),
                query.path.len(),
                codeword_log2 - fold - cap_log2,
            )?;
        }
        poly_log2 -= fold;
    }
    Ok(())
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
    validate_feeder_proof(proof, Some(1))
}

/// A feeder proof of `expected` instances (any positive count when `None`):
/// the reduced family only under the 2^22 feeder circuit and the feeder WHIR
/// schedule, no delegation proofs.
pub(super) fn validate_feeder_proof(
    proof: &ProgramProof,
    expected: Option<usize>,
) -> Result<(), String> {
    feeder_proof_instances(proof, expected)?;
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
/// geometry; there is no fallback to the old wrap or the old chain.
pub(super) fn validate_l1_wrap_activation() -> Result<(), String> {
    let wrap_program = FsvProgram::UnifiedRecursionLayerL1FeederWrap;
    let circuit = L1_WRAP_KIND
        .unified_circuit()
        .expect("an L1 wrap kind has a circuit");
    let circuit_domain = circuit.get_domain_size();
    if circuit_domain != L1_WRAP_PROGRAM_CYCLE_LIMIT {
        return Err(format!(
            "ProofTarget::L1 requires the 2^{} L1 wrap circuit of the wrap program; {circuit:?} proves 2^{} cycles",
            L1_WRAP_PROGRAM_CYCLE_LIMIT.trailing_zeros(),
            circuit_domain.trailing_zeros()
        ));
    }
    if circuit.rom() != wrap_program.rom() {
        return Err(format!(
            "ProofTarget::L1 requires an L1 wrap circuit with the {} byte ROM of the wrap program; {circuit:?} has a {} byte ROM",
            wrap_program.rom().byte_size(),
            circuit.rom().byte_size()
        ));
    }
    Ok(())
}

/// The backends that prove [`L1_WRAP_KIND`]; checked before any setup is
/// built.
#[cfg_attr(not(feature = "gpu"), allow(dead_code))]
pub(super) fn validate_l1_wrap_backend(backend: ProverBackend) -> Result<(), String> {
    match backend {
        ProverBackend::Cpu | ProverBackend::Gpu => Ok(()),
    }
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
