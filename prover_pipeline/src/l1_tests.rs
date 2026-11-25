use super::*;
use setups::unrolled_circuits::{
    unified_reduced_machine_proth120_2_21, unified_reduced_machine_proth120_2_22,
};
use std::fs;

fn source() -> ProgramSource {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    ProgramSource::legacy_binaries_from_bin(root.join("examples/basic_fibonacci/app.bin"))
}

#[test]
fn ethproofs_l1_wrap_gkr_security_margins() {
    use ::prover::cs::{definitions::NUM_REGISTERS, gkr_compiler::GKRCircuitArtifact};
    use ::prover::field::Proth120;
    use ::prover::gkr::prover_config::{example_configs::l1_wrap, pow_bits};

    let circuit: GKRCircuitArtifact<Proth120> = serde_json::from_str(include_str!(
        "../../circuit_defs/unrolled_circuits/unified_reduced_machine_proth120_2_22/generated/layout.json"
    ))
    .expect("embedded 2^22 Proth120 unified layout");
    let config = l1_wrap::ethproofs_packed_prover_config();
    assert_eq!(circuit.trace_len, 1 << config.trace_len_log2);
    let m = 3.0;
    let loss = ((m + 0.5) * 2.0_f64.powf(config.base_round().lde_factor_log2 as f64 / 2.0)).log2();
    let challenge_bits = 128.0 - 37.0_f64.log2();
    let external_pow_bits = f64::from(l1_wrap::EXTERNAL_CHALLENGES_POW_BITS);

    let lookup_degree = pow_bits::lookup_identity_degree(&circuit);
    let lookup_bits = challenge_bits + external_pow_bits - (lookup_degree as f64).log2() - loss;
    assert!(lookup_bits >= 100.0, "lookup: {lookup_bits:.9} bits");

    let keys_per_row =
        circuit.memory_layout.ram_access_sets.len() + 1 + circuit.memory_layout.teardown_sets.len();
    let memory_degree = circuit.trace_len * keys_per_row + NUM_REGISTERS + 1;
    let memory_bits =
        challenge_bits + external_pow_bits - (memory_degree as f64).log2() - 2.0 - loss;
    assert!(
        memory_bits >= 100.0,
        "single-instance memory: {memory_bits:.9} bits"
    );
}

/// Setup-tree level pinned by the wrap verifier.
const SETUP_FRONTIER_LEVEL: usize = 10;

/// Recommits the L1 wrap setup (setup only, no proof), checks its cap against the committed
/// reference wrap proof, and writes the `2^SETUP_FRONTIER_LEVEL` setup-tree nodes at that
/// level, in physical order, for the verifier_evm setup frontier.
#[test]
#[ignore = "recommits both L1 wrap setups and writes their EVM setup frontiers"]
fn export_l1_wrap_setup_frontier() {
    for &mode in SoundnessMode::ALL {
        export_setup_frontier(mode);
    }
}

fn export_setup_frontier(mode: SoundnessMode) {
    use ::prover::field::Proth120;
    use ::prover::gkr::whir::coset_commit::CosetByCosetBaseCommitment;
    use ::prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
    use ::prover::worker::Worker;

    let artifact: ProofArtifact =
        proof_fixtures::read_file(proof_fixtures::chain_artifact(mode.file_suffix(), "l1"));
    let bundle = artifact.l1.expect("L1 artifact contains the wrap bundle");
    bundle.validate().expect("committed L1 wrap bundle");
    let setup_commitment = &bundle.proof.whir_proof.setup_commitment;

    let rom = ::prover::common_constants::rom::L1_WRAP_ROM;
    let (mut binary, mut text) = load_fsv_exact(
        fsv_dir(),
        &FsvDescriptor::compression(mode, FsvProfile::L1Wrap),
    )
    .into_words();
    setups::pad_bytecode_for_proving_with_rom(&mut binary, rom);
    setups::pad_bytecode_for_proving_with_rom(&mut text, rom);
    let worker = Worker::new();
    let setup = match mode {
        SoundnessMode::PessimisticConjecture => {
            unified_reduced_machine_proth120_2_21::l1_wrap::l1_wrap_setup(&binary, &text, &worker)
        }
        SoundnessMode::EthproofsSoundnessCalc => {
            unified_reduced_machine_proth120_2_22::l1_wrap::l1_wrap_setup(&binary, &text, &worker)
        }
    };
    let config =
        ::prover::gkr::prover_config::example_configs::l1_wrap::packed_prover_config_in_mode(mode);
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
        .join("../verifier_evm/debug_data")
        .join(mode.file_suffix())
        .join("setup_frontier.json");
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
    let verify = |stream| {
        native_verify_unified_compression_in_mode(stream, SoundnessMode::PessimisticConjecture)
    };
    verify(stream.clone()).unwrap();
    let count_end = stream.len() - 2 - 16;
    let count_start = count_end - full_statement_verifier::definitions::DELEGATION_TYPES.len();
    for offset in count_start..count_end {
        let mut bad = stream.clone();
        assert_eq!(bad[offset], 0);
        bad[offset] = 1;
        assert!(verify(bad).unwrap_err().contains("no delegation proofs"));
    }
    let mut trailing = stream.clone();
    trailing.push(7);
    assert!(verify(trailing).unwrap_err().contains("trailing"));
    let truncated = stream[..stream.len() - 1].to_vec();
    assert!(verify(truncated).is_err());
    let mut flipped = stream;
    flipped[(CompressionProfile::Final.cap_size(SoundnessMode::PessimisticConjecture) - 1) * 8] ^=
        1;
    assert!(verify(flipped).is_err());
}

#[test]
#[should_panic(expected = "Ethproofs Compression instance count must be in 1..=3")]
fn ethproofs_compression_rejects_four_instances() {
    use full_statement_verifier::unified_circuit_statement::verify_unified_circuit_recursion_layer_sec_100_compression_ethproofs_soundcalc;
    use prover::field::{
        baby_bear::base::BabyBearField, baby_bear::ext4::BabyBearExt4, FieldExtension,
    };

    let artifact: ProofArtifact = proof_fixtures::read_file(proof_fixtures::chain_artifact(
        "ethproofs_soundcalc",
        "compression",
    ));
    let setup_words: usize = artifact
        .setups
        .values()
        .map(|params| params.flattened_setup_caps().len())
        .sum();
    let challenge_words = <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE
        * prover::definitions::GKRExternalChallenges::<BabyBearField, BabyBearExt4>::TOTAL_CHALLENGES;
    let count_offset =
        setup_words + 3 * artifact.proof.register_final_values.len() + 3 + challenge_words;
    let mut stream = build_unified_stream(
        &artifact.setups,
        &artifact.proof,
        BlakeMode::BlakeSpecialOpcodes,
    );
    assert_eq!(stream[count_offset], 1);
    stream[count_offset] = 4;
    stream.truncate(count_offset + 1);
    let _ = verify_unified_circuit_recursion_layer_sec_100_compression_ethproofs_soundcalc::<
        _,
        verifier_common::errors::DebugErrorCreator,
        { verifier_common::USE_REDUCED_BLAKE2_ROUNDS },
    >(&mut stream.into_iter());
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
        artifact.soundness_mode,
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
