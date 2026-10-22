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
    for version in common::available_versions("calldata drift") {
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

        let (gkr, gkr_fields) =
            verifier_evm::flatten::gkr_calldata_with_fields(&circuit, &proof, &aux);
        let cfg = version.prover_config();
        let whir = verifier_evm::whir_stream(
            &circuit,
            &proof,
            &aux,
            &cfg.whir_schedule.whir_steps_schedule,
            &cfg.whir_schedule.whir_queries_schedule,
        );
        assert_eq!(
            hex::encode([gkr.clone(), whir].concat()),
            read_fixture(version, common::MERGED_CALLDATA),
            "merged_calldata diverged"
        );
        assert_eq!(
            hex::encode(verifier_evm::verified_mark(&proof, &aux).to_bytes()),
            read_fixture(version, common::VERIFIED_MARK),
            "verified_mark diverged"
        );
        if let Some(name) = version.mutation_fields_file {
            let stored: serde_json::Value =
                serde_json::from_str(&read_fixture(version, name)).unwrap();
            assert_eq!(
                stored,
                common::calldata_field_metadata(&gkr_fields, gkr.len()),
                "calldata field metadata diverged"
            );
        }
    }
}

#[test]
fn serialized_mutation_fields_match_the_proof_and_aux() {
    for version in common::available_versions("calldata mutation fields") {
        let (circuit, proof, aux) = version.load();
        let (gkr, fields) = verifier_evm::flatten::gkr_calldata_with_fields(&circuit, &proof, &aux);
        let prover::gkr::prover::OperationMode::SingleChunk { final_pc, .. } = aux else {
            unreachable!()
        };
        assert_eq!(fields.final_pc.value, final_pc.to_le_bytes());
        assert_eq!(
            fields.external_pow_nonce.value,
            proof.lookup_challenges_pow_nonce.to_be_bytes()
        );
        assert_eq!(
            fields.external_pow_nonce.offset,
            verifier_evm::commit_seed_preimage(&circuit, &proof, &aux).len()
        );
        // dimension-reducing layers are serialized output-first: the highest layer index
        let top = proof.sumcheck_intermediate_values.keys().max().unwrap();
        let first_round = &proof.sumcheck_intermediate_values[top].internal_round_coefficients[0];
        let expected: Vec<u8> = first_round
            .as_multilinear()
            .iter()
            .flat_map(|e| e.to_u128().to_be_bytes())
            .collect();
        assert_eq!(fields.first_dim_reduce_round.value, expected);
        for (bytes, field) in [
            (&gkr, fields.final_pc),
            (&gkr, fields.external_pow_nonce),
            (&gkr, fields.first_dim_reduce_round),
        ] {
            assert_eq!(
                &bytes[field.offset..field.offset + field.value.len()],
                field.value
            );
        }
    }
}

#[test]
fn missing_standard_layer_is_rejected() {
    for version in common::available_versions("missing_standard_layer_is_rejected") {
        common::assert_panics_with("proof is missing a standard circuit layer", || {
            let (circuit, mut proof, aux) = version.load();
            proof.sumcheck_intermediate_values.remove(&0);
            verifier_evm::gkr_calldata(&circuit, &proof, &aux);
        });
    }
}

#[test]
fn full_trace_dimension_reducing_layer_is_rejected() {
    for version in common::available_versions("full_trace_dimension_reducing_layer_is_rejected") {
        common::assert_panics_with(
            "dimension-reducing layer must have fewer rounds than the circuit",
            || {
                let (circuit, mut proof, aux) = version.load();
                proof
                    .sumcheck_intermediate_values
                    .get_mut(&circuit.layers.len())
                    .unwrap()
                    .sumcheck_num_rounds = circuit.trace_len.trailing_zeros() as usize;
                verifier_evm::gkr_calldata(&circuit, &proof, &aux);
            },
        );
    }
}

#[test]
fn missing_dimension_reducing_layer_is_rejected() {
    for version in common::available_versions("missing_dimension_reducing_layer_is_rejected") {
        common::assert_panics_with(
            "dimension-reducing layer count must match the circuit",
            || {
                let (circuit, mut proof, aux) = version.load();
                proof
                    .sumcheck_intermediate_values
                    .remove(&circuit.layers.len());
                verifier_evm::gkr_calldata(&circuit, &proof, &aux);
            },
        );
    }
}

#[test]
fn wrong_dimension_reducing_round_sequence_is_rejected() {
    for version in common::available_versions("wrong_dimension_reducing_round_sequence_is_rejected")
    {
        common::assert_panics_with(
            "dimension-reducing rounds must increase from the explicit output",
            || {
                let (circuit, mut proof, aux) = version.load();
                proof
                    .sumcheck_intermediate_values
                    .get_mut(&circuit.layers.len())
                    .unwrap()
                    .sumcheck_num_rounds -= 1;
                verifier_evm::gkr_calldata(&circuit, &proof, &aux);
            },
        );
    }
}
