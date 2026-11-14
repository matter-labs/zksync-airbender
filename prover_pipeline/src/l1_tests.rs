use super::*;
use std::fs;

fn source() -> ProgramSource {
    ProgramSource::legacy_binaries_from_bin(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../examples/basic_fibonacci/app.bin"),
    )
}

/// Setup-tree level the verifier's pinned setup frontier holds (the cap is level 3).
const SETUP_FRONTIER_LEVEL: usize = 9;

/// Recommits the L1 wrap setup (setup only, no proof), checks its cap against the committed
/// reference wrap proof, and writes the `2^SETUP_FRONTIER_LEVEL` setup-tree nodes at that
/// level, in physical order, for the verifier_evm setup frontier.
#[test]
#[ignore = "recommits the L1 wrap setup (about a minute of CPU) and writes the verifier_evm setup frontier"]
fn export_l1_wrap_setup_frontier() {
    use ::prover::field::Proth120;
    use ::prover::gkr::whir::coset_commit::CosetByCosetBaseCommitment;
    use ::prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
    use ::prover::worker::Worker;

    let artifact: ProofArtifact = proof_fixtures::read_file(proof_fixtures::chain_artifact(
        "pessimistic_conjecture",
        "l1",
    ));
    let bundle = artifact.l1.expect("L1 artifact contains the wrap bundle");
    bundle.validate().expect("committed L1 wrap bundle");
    let setup_commitment = &bundle.proof.whir_proof.setup_commitment;

    let circuit_type = CircuitType::L1Wrap;
    let (mut binary, mut text) = load_fsv_exact(
        fsv_dir(),
        &FsvDescriptor::compression(FsvProfile::CompressionFinalWrap),
    )
    .into_words();
    setups::pad_bytecode_for_proving_with_rom(&mut binary, circuit_type.rom());
    setups::pad_bytecode_for_proving_with_rom(&mut text, circuit_type.rom());
    let worker = Worker::new();
    let setup = unified_reduced_machine_proth120::l1_wrap::l1_wrap_setup(&binary, &text, &worker);
    let config = ProofProfile::L1Wrap.prover_config(
        circuit_type.get_domain_size_log2() as usize,
        SoundnessMode::PessimisticConjecture,
    );
    let pack_log2 = config.pack_log2();
    let twiddles = ::prover::fft::Twiddles::new(1 << (config.trace_len_log2 + pack_log2), &worker);
    let inputs: Vec<&[Proth120]> = setup
        .setup
        .hypercube_evals
        .iter()
        .map(|column| &column[..])
        .collect();
    let (commitment, frontier) =
        CosetByCosetBaseCommitment::<Proth120, Keccak256MerkleTreeWithCap>::commit_packed_with_level_nodes(
            &inputs,
            &twiddles,
            config.lde_factor(),
            config.base_oracles_values_per_leaf().trailing_zeros() as usize,
            config.cap_size,
            config.trace_len_log2,
            pack_log2,
            SETUP_FRONTIER_LEVEL,
            &worker,
        );
    let cap = setup_commitment.commitment.cap.cap.clone();
    assert_eq!(
        commitment.get_cap().cap,
        cap,
        "recommitted setup differs from the reference proof's setup cap"
    );
    let digests: Vec<String> = frontier
        .iter()
        .map(|d| d.iter().map(|w| format!("{w:08x}")).collect())
        .collect();
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../verifier_evm/debug_data/l1_wrap/setup_frontier.json");
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(
        &path,
        format!(
            "{}\n",
            serde_json::to_string_pretty(&serde_json::json!({
                "level": SETUP_FRONTIER_LEVEL,
                "cap_size": config.cap_size,
                "digests": digests,
            }))
            .unwrap()
        ),
    )
    .expect("writes the setup frontier");
    println!("wrote {} ({} digests)", path.display(), frontier.len());
}

#[test]
fn cpu_compression_rejects_tampered_streams() {
    let artifact: ProofArtifact = proof_fixtures::read_file(proof_fixtures::chain_artifact(
        "pessimistic_conjecture",
        "compression",
    ));
    let stream = build_unified_stream(
        &artifact.setups,
        &artifact.proof,
        BlakeMode::BlakeSpecialOpcodes,
    );
    native_verify_unified_compression_final(stream.clone()).unwrap();
    let count_end = stream.len() - 2 - 16;
    let count_start = count_end - full_statement_verifier::definitions::DELEGATION_TYPES.len();
    for offset in count_start..count_end {
        let mut bad = stream.clone();
        assert_eq!(bad[offset], 0);
        bad[offset] = 1;
        assert!(native_verify_unified_compression_final(bad)
            .unwrap_err()
            .contains("no delegation proofs"));
    }
    let mut trailing = stream.clone();
    trailing.push(7);
    assert!(native_verify_unified_compression_final(trailing)
        .unwrap_err()
        .contains("trailing"));
    let truncated = stream[..stream.len() - 1].to_vec();
    assert!(native_verify_unified_compression_final(truncated).is_err());
    let mut flipped = stream;
    flipped[(CompressionProfile::Final.cap_size() - 1) * 8] ^= 1;
    assert!(native_verify_unified_compression_final(flipped).is_err());
}

#[test]
fn supplied_standard_records_refuse_an_l1_chain_without_recomputation() {
    let artifact: ProofArtifact = proof_fixtures::read_file(proof_fixtures::chain_artifact(
        "pessimistic_conjecture",
        "compression",
    ));
    let source = source();
    let loaded = load_and_validate_program(&source, &artifact).unwrap();
    let mut trusted = TrustedParams {
        schema_version: 1,
        program_hash: fsv_digest(&loaded.bin_u32, &loaded.text_u32).0,
        soundness_mode: SoundnessMode::PessimisticConjecture,
        programs: vec![],
    };
    let mut layer = 0;
    expected_chain_end_params(
        artifact.target,
        artifact.chain_end_params.len(),
        &artifact.blake_unrolled,
        &artifact.blake_bridge,
        &artifact.blake_final,
        &mut |program| {
            let end_params = artifact.chain_end_params[layer];
            layer += 1;
            let (hash, machine, exit_pc) = match program {
                ChainProgram::User => (
                    trusted.program_hash,
                    SetupMachine::UnrolledFullUnsigned,
                    find_binary_exit_point(&loaded.bin_u32)?,
                ),
                ChainProgram::Fsv(_, _, _, SetupMachine::Compression(_)) => return Ok(end_params),
                ChainProgram::Fsv(program, profile, blake, machine) => {
                    let guest = load_fsv_exact(
                        fsv_dir(),
                        &FsvDescriptor {
                            soundness_mode: trusted.soundness_mode,
                            program,
                            profile,
                            blake,
                        },
                    );
                    (
                        fsv_digest(guest.bin(), guest.text()).0,
                        machine,
                        find_binary_exit_point(guest.bin())?,
                    )
                }
            };
            if !trusted
                .programs
                .iter()
                .any(|r| r.program_hash == hash && r.machine == machine)
            {
                trusted.programs.push(TrustedProgramParams {
                    program_hash: hash,
                    machine,
                    setups: Setups::new(),
                    exit_pc,
                    end_params,
                });
            }
            Ok(end_params)
        },
    )
    .unwrap();
    // These deliberately incomplete caller-trusted records cover the earlier
    // Standard chain; no L1 setup record may be synthesized on the caller's behalf.
    let encoded = serde_json::to_vec(&trusted).unwrap();
    let trusted: TrustedParams = serde_json::from_slice(&encoded).unwrap();
    let failure = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        verify_artifact_with_trusted_params_in_mode(
            &artifact,
            &source,
            trusted.soundness_mode,
            Some(&trusted),
        )
    }))
    .expect_err("missing L1 records must refuse");
    let message = failure
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| failure.downcast_ref::<&str>().copied())
        .unwrap_or_default();
    assert!(
        message.contains("trusted params have no record for this program hash and machine"),
        "{message}"
    );
}
