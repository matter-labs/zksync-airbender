//! Verifies the ported flatten/seed modules reproduce the known-good calldata and
//! seed bytes byte-for-byte from the on-disk circuit + proof + aux data.

mod common;

fn read_fixture(version: &common::Version, name: &str) -> String {
    std::fs::read_to_string(version.data_path(name))
        .unwrap_or_else(|_| panic!("read {} fixture {name}", version.name))
        .trim()
        .to_string()
}

#[test]
fn flatten_and_seed_match_reference() {
    for version in common::VERSIONS {
        let (circuit, proof, aux) = version.load();

        let preimage = verifier_evm::commit_seed_preimage(&circuit, &proof, &aux);
        assert_eq!(
            hex::encode(&preimage),
            read_fixture(version, "gkr_step1_preimage.hex"),
            "commit_seed_preimage diverged"
        );

        // The GKR→WHIR handoff seed is an intermediate value the prover records in the proof; the
        // flatten path surfaces it verbatim. The expectation is the proof file's own recorded value
        // (source of truth) — never a hardcoded literal that goes stale when the proof is regenerated.
        let handoff = verifier_evm::gkr_whir_handoff_seed(&proof);
        assert_eq!(
            Some(handoff),
            proof.intermediate_transcript_seed,
            "gkr_whir_handoff_seed diverged from the proof's recorded intermediate_transcript_seed"
        );

        let gkr = verifier_evm::gkr_calldata(&circuit, &proof, &aux);
        assert_eq!(
            hex::encode(&gkr),
            read_fixture(version, "gkr_full_calldata.hex"),
            "gkr_calldata diverged"
        );

        let cfg = version.prover_config();
        let whir = verifier_evm::whir_calldata(
            &circuit,
            &proof,
            &aux,
            &cfg.whir_schedule.whir_steps_schedule,
            &cfg.whir_schedule.whir_queries_schedule,
        );
        assert_eq!(
            hex::encode(&whir),
            read_fixture(version, "proth120_whir_calldata_from_proof.hex"),
            "whir_calldata diverged"
        );
    }
}

#[test]
fn trace21_standard_layers_are_serialized_once() {
    // Adapt only the proof shape, not its claims: this checks serialization,
    // not cryptographic validity of a 2^21 proof.
    let (mut circuit, mut proof, aux) = common::L1_WRAP_2P22.load();
    let trace22_bytes = verifier_evm::gkr_calldata(&circuit, &proof, &aux).len();
    circuit.trace_len = 1 << 21;
    for layer in 0..circuit.layers.len() {
        let values = proof.sumcheck_intermediate_values.get_mut(&layer).unwrap();
        values.sumcheck_num_rounds = 21;
        values.internal_round_coefficients.pop().unwrap();
    }
    // The old first dimension-reducing layer had 21 rounds. With a 2^21
    // circuit that reduction is absent; shift the remaining layer indices.
    let first_dr = circuit.layers.len();
    proof
        .sumcheck_intermediate_values
        .remove(&first_dr)
        .unwrap();
    proof.sumcheck_intermediate_values = proof
        .sumcheck_intermediate_values
        .into_iter()
        .map(|(layer, values)| (layer - usize::from(layer > first_dr), values))
        .collect();

    let trace21_bytes = verifier_evm::gkr_calldata(&circuit, &proof, &aux).len();
    // Five main rounds, one 21-round DR layer, and its ten two-point claims.
    assert_eq!(
        trace22_bytes - trace21_bytes,
        5 * 4 * 16 + 21 * 4 * 16 + 10 * 2 * 16
    );
}

#[test]
#[should_panic(expected = "proof is missing a standard circuit layer")]
fn missing_standard_layer_is_rejected() {
    let (circuit, mut proof, aux) = common::L1_WRAP_2P22.load();
    proof.sumcheck_intermediate_values.remove(&0);
    verifier_evm::gkr_calldata(&circuit, &proof, &aux);
}

#[test]
#[should_panic(expected = "dimension-reducing layer must have fewer rounds than the circuit")]
fn full_trace_dimension_reducing_layer_is_rejected() {
    let (circuit, mut proof, aux) = common::L1_WRAP_2P22.load();
    proof
        .sumcheck_intermediate_values
        .get_mut(&circuit.layers.len())
        .unwrap()
        .sumcheck_num_rounds = 22;
    verifier_evm::gkr_calldata(&circuit, &proof, &aux);
}
