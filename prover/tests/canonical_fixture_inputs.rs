#![cfg(feature = "test")]

use common_constants::ROM_SECOND_WORD_BITS;
use prover::definitions::{SecurityLevel, SoundnessMode};
use prover::tests::gkr::orchestration::canonical_fixtures::{
    canonical_circuits, capture_canonical_inputs, CanonicalCircuit, CanonicalInputs,
    CanonicalTrace, CANONICAL_CIRCUITS,
};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use worker::Worker;

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_owned()
}

fn fingerprint(inputs: CanonicalInputs) -> u64 {
    let mut hash = DefaultHasher::new();
    inputs.circuit.hash(&mut hash);
    inputs.binary.hash(&mut hash);
    inputs.text_section.hash(&mut hash);
    inputs.decoder_table.hash(&mut hash);
    inputs.trace.hash(&mut hash);
    inputs.inits_and_teardowns.hash(&mut hash);
    inputs.boundary.hash(&mut hash);
    // Hash the ordered table rows in place. Subword ROM tables have millions
    // of rows: retaining two drivers and two padded dumps makes the comparison
    // much larger than either canonical input capture.
    for (index, table) in inputs.table_driver.tables.iter().enumerate() {
        index.hash(&mut hash);
        if let cs::tables::LookupWrapper::Initialized(table) = table {
            table.id.hash(&mut hash);
            table.num_key_columns.hash(&mut hash);
            table.num_value_columns.hash(&mut hash);
            table.data.hash(&mut hash);
        }
    }
    hash.finish()
}

/// Execute every real workload and replay it twice with different RAM-worker
/// partitions. Each circuit is a separate test process for a useful RSS bound.
fn assert_replay_is_deterministic(circuit: CanonicalCircuit) {
    let root = root();
    let parallel = Worker::new_with_num_threads(8);
    let serial = Worker::new_with_num_threads(1);
    assert!(CANONICAL_CIRCUITS.contains(&circuit));
    eprintln!("capturing {}", circuit.stem());
    let first = capture_canonical_inputs(&root, circuit, &parallel);
    for mode in SoundnessMode::ALL {
        let config = circuit.prover_config(&root, *mode);
        assert_eq!(config.security_level, SecurityLevel::Sec100);
        assert_eq!(1 << config.trace_len_log2, first.compiled_circuit.trace_len);
        assert!(circuit.proof_path(&root, *mode).exists());
    }
    match &first.trace {
        CanonicalTrace::NonMemory(rows) => {
            // The CPU oracle needs genuine optional PC entries. Every real
            // row must point to an instruction assigned to its family.
            assert!(first.decoder_table.iter().any(Option::is_none));
            assert!(!rows.is_empty());
            for row in rows {
                assert!(first.decoder_table[(row.opcode_data.initial_pc >> 2) as usize].is_some());
            }
        }
        CanonicalTrace::KeccakColumnParity(rows) => assert_eq!(rows.len(), 363),
        CanonicalTrace::KeccakThetaRho(rows) => assert_eq!(rows.len(), 360),
        CanonicalTrace::KeccakChi5(rows) => assert_eq!(rows.len(), 360),
        CanonicalTrace::Unified(_) => {
            let ram = first.inits_and_teardowns.as_ref().unwrap();
            assert!(ram.top_bits.windows(2).any(|pair| pair[1] > pair[0] + 1));
            assert_eq!(
                first.boundary,
                capture_canonical_inputs(
                    &root,
                    CanonicalCircuit::Blake2WithExtendedControl,
                    &parallel,
                )
                .boundary
            );
        }
        CanonicalTrace::InitsAndTeardowns => {
            let ram = first.inits_and_teardowns.as_ref().unwrap();
            assert_eq!(ram.top_bits, (0..8).collect::<Vec<_>>());
            assert!(ram.touched.iter().all(|&(address, (_, value))| {
                address as usize >= 1 << (16 + ROM_SECOND_WORD_BITS) || value == 0
            }));
        }
        _ => {}
    }
    let expected = fingerprint(first);
    let repeated = capture_canonical_inputs(&root, circuit, &serial);
    assert_eq!(expected, fingerprint(repeated));
}

macro_rules! replay_test {
    ($name:ident, $circuit:ident) => {
        #[test]
        fn $name() {
            assert_replay_is_deterministic(CanonicalCircuit::$circuit);
        }
    };
}

replay_test!(
    canonical_fixture_inputs_add_sub_lui_auipc_mop,
    AddSubLuiAuipcMop
);
replay_test!(canonical_fixture_inputs_jump_branch_slt, JumpBranchSlt);
replay_test!(canonical_fixture_inputs_shift_binop, ShiftBinop);
replay_test!(canonical_fixture_inputs_unsigned_mul_div, UnsignedMulDiv);
replay_test!(canonical_fixture_inputs_mem_word_only, MemWordOnly);
replay_test!(canonical_fixture_inputs_mem_subword_only, MemSubwordOnly);
replay_test!(
    canonical_fixture_inputs_inits_and_teardowns,
    InitsAndTeardowns
);
replay_test!(
    canonical_fixture_inputs_unified_reduced_machine,
    UnifiedReducedMachine
);
replay_test!(
    canonical_fixture_inputs_bigint_with_extended_control,
    BigintWithExtendedControl
);
replay_test!(
    canonical_fixture_inputs_blake2_with_extended_control,
    Blake2WithExtendedControl
);
replay_test!(canonical_fixture_inputs_keccak_special5, KeccakSpecial5);
replay_test!(
    canonical_fixture_inputs_keccak_column_parity,
    KeccakColumnParity
);
replay_test!(canonical_fixture_inputs_keccak_theta_rho, KeccakThetaRho);
replay_test!(canonical_fixture_inputs_keccak_chi5, KeccakChi5);

#[test]
fn canonical_fixture_registry_matches_inventory() {
    use std::collections::BTreeSet;
    for &mode in SoundnessMode::ALL {
        let actual: BTreeSet<_> = canonical_circuits(mode)
            .map(|circuit| circuit.stem())
            .collect();
        let expected: BTreeSet<_> = proof_fixtures::circuits(mode.file_suffix()).collect();
        assert_eq!(actual, expected, "{mode:?}");
    }
}

#[test]
fn canonical_fixture_encoding() {
    type Proof = prover::gkr::prover::GKRProof<
        field::baby_bear::base::BabyBearField,
        field::baby_bear::ext4::BabyBearExt4,
        prover::merkle_trees::DefaultTreeConstructor,
    >;
    let root = root();
    for &mode in SoundnessMode::ALL {
        for circuit in canonical_circuits(mode) {
            let path = circuit.proof_path(&root, mode);
            let proof: Proof = proof_fixtures::read_file(&path);
            assert_eq!(
                proof.whir_proof.whir_schedule,
                circuit.prover_config(&root, mode).whir_schedule
            );
            assert_eq!(
                proof_fixtures::encode(&proof, Vec::new()),
                std::fs::read(path).unwrap()
            );
        }
    }
}
