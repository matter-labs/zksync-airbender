#![cfg(all(feature = "verifiers", feature = "host_utils"))]

use common_constants::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
use full_statement_verifier::host_utils::fixture_artifact::ChainArtifact;
use full_statement_verifier::host_utils::{build_unified_stream, native_verify_unified_in_mode};
use prover::definitions::SoundnessMode;
use verifier_common::BlakeMode;

fn with_fixtures(mut check: impl FnMut(SoundnessMode, ChainArtifact)) {
    for &mode in SoundnessMode::ALL {
        for chain in ["unified", "unrolled_unified"] {
            check(mode, ChainArtifact::load(mode, chain));
        }
    }
}

fn build_stream(artifact: &ChainArtifact, blake: BlakeMode) -> Vec<u32> {
    build_unified_stream(&artifact.setups, &artifact.proof, blake)
}

fn prefix_len(artifact: &ChainArtifact) -> usize {
    artifact
        .setups
        .values()
        .map(|params| params.setup_caps.cap.as_flattened().len())
        .sum()
}

#[test]
fn unified_recursion_layer_accepts_valid_proof() {
    with_fixtures(|mode, artifact| {
        let output = native_verify_unified_in_mode(
            build_stream(&artifact, verifier_common::BLAKE_MODE),
            false,
            mode,
        )
        .unwrap();
        assert_eq!(output[8..16], artifact.chain_hash);
    });
}

#[test]
fn unified_recursion_layer_rejects_corrupted_stream() {
    with_fixtures(|mode, artifact| {
        let mut stream = build_stream(&artifact, verifier_common::BLAKE_MODE);
        let prefix_len = prefix_len(&artifact);
        assert!(stream.len() > prefix_len);
        let index = prefix_len + (stream.len() - prefix_len) / 2;
        stream[index] ^= 0x5555_5555;
        assert!(native_verify_unified_in_mode(stream, false, mode).is_err());
    });
}

#[test]
fn rejects_corrupted_setup_cap() {
    with_fixtures(|mode, artifact| {
        let mut stream = build_stream(&artifact, verifier_common::BLAKE_MODE);
        let prefix_len = prefix_len(&artifact);
        assert!(prefix_len > 0);
        stream[prefix_len / 2] ^= 0x5555_5555;
        assert!(native_verify_unified_in_mode(stream, false, mode).is_err());
    });
}

#[test]
fn rejects_tampered_final_register_state() {
    with_fixtures(|mode, artifact| {
        let mut stream = build_stream(&artifact, verifier_common::BLAKE_MODE);
        stream[prefix_len(&artifact) + 3] ^= 0x5555_5555;
        assert!(native_verify_unified_in_mode(stream, false, mode).is_err());
    });
}

#[test]
fn rejects_num_it_circuits_zero() {
    with_fixtures(|mode, mut artifact| {
        artifact.proof.num_it_circuits = Some(0);
        assert!(native_verify_unified_in_mode(
            build_stream(&artifact, verifier_common::BLAKE_MODE),
            false,
            mode
        )
        .is_err());
    });
}

#[test]
fn rejects_num_it_circuits_exceeds_num_circuits() {
    with_fixtures(|mode, mut artifact| {
        artifact.proof.num_it_circuits = Some(2);
        assert!(native_verify_unified_in_mode(
            build_stream(&artifact, verifier_common::BLAKE_MODE),
            false,
            mode
        )
        .is_err());
    });
}

#[test]
fn rejects_duplicated_multi_instance() {
    with_fixtures(|mode, mut artifact| {
        let proofs = artifact
            .proof
            .riscv_proofs
            .get_mut(&(REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32))
            .unwrap();
        assert_eq!(proofs.len(), 1);
        proofs.push(proofs[0].clone());
        artifact.proof.num_it_circuits = Some(2);
        assert!(native_verify_unified_in_mode(
            build_stream(&artifact, verifier_common::BLAKE_MODE),
            false,
            mode
        )
        .is_err());
    });
}

#[allow(dead_code)]
fn load_binary_section(path: &str) -> Vec<u32> {
    let bytes = std::fs::read(path).unwrap_or_else(|_| {
        panic!("Missing {path} — run `cd tools/gkr_verifier && ./dump_bin.sh` (or gkr_test.sh `binaries`)")
    });
    assert!(
        bytes.len().is_multiple_of(4),
        "binary section not word-aligned"
    );
    bytes
        .as_chunks::<4>()
        .0
        .iter()
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect()
}

#[test]
#[ignore = "CPU RISC-V execution of the registered FSV guests"]
fn unified_recursion_layer_transpiler_accepts_valid_proof() {
    use common_constants::rom::ROM_SECOND_WORD_BITS;
    use full_statement_verifier::host_utils::load_fsv_exact;
    use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
    use riscv_transpiler::ir::simple_instruction_set::*;
    use riscv_transpiler::ir::ReducedMachineDecoderConfig;
    use riscv_transpiler::vm::*;
    use verifier_common::field::baby_bear::base::BabyBearField;
    use verifier_common::fsv_binaries::{FsvDescriptor, FsvProgram};

    for &mode in SoundnessMode::ALL {
        let guest = load_fsv_exact(
            proof_fixtures::root().join("tools/gkr_verifier/full_statement_verifiers"),
            &FsvDescriptor::new(
                mode,
                FsvProgram::UnifiedRecursionLayer,
                BlakeMode::Compression,
            ),
        );
        for chain in ["unified", "unrolled_unified"] {
            let artifact = ChainArtifact::load(mode, chain);
            let oracle_responses = build_stream(&artifact, BlakeMode::Compression);
            let expected_output = native_verify_unified_in_mode(
                build_stream(&artifact, verifier_common::BLAKE_MODE),
                false,
                mode,
            )
            .unwrap();
            assert_eq!(expected_output[8..16], artifact.chain_hash);
            let instructions: Vec<Instruction> =
                preprocess_bytecode::<ReducedMachineDecoderConfig, true>(guest.text());
            let tape = SimpleTape::new(&instructions);
            let mut ram = RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(
                guest.bin(),
                1 << 30,
            );
            let cycles_bound = 1 << 24;
            let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
            let mut snapshotter = SimpleSnapshotter::<
                DelegationsAndFamiliesCounters,
                { ROM_SECOND_WORD_BITS },
            >::new_with_cycle_limit(cycles_bound, state);
            let mut non_determinism = QuasiUARTSource::new_with_reads(oracle_responses);
            let finished =
                VM::<DelegationsAndFamiliesCounters>::run_basic_unrolled::<_, _, _, BabyBearField>(
                    &mut state,
                    &mut ram,
                    &mut snapshotter,
                    &tape,
                    cycles_bound,
                    &mut non_determinism,
                );
            assert!(finished);
            let actual_output: [u32; 16] = std::array::from_fn(|i| state.registers[10 + i].value);
            assert_eq!(actual_output, expected_output);
            let cycles = (state.timestamp - common_constants::INITIAL_TIMESTAMP)
                / common_constants::TIMESTAMP_STEP;
            println!("FSV unified recursion {mode:?} {chain}: {cycles} cycles");
        }
    }
}
