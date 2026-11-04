//! The serialized prover configs of every production circuit
//! (`<circuit crate>/generated/prover_config_<level>_<mode>.json`, plus the
//! `.md` notes of the modes that have them): the geometry each circuit
//! definition declares ([`circuit_common::CircuitGeometry`]) applied to its
//! compiled circuit artifact (the source of the committed column widths),
//! rendered per [`circuit_common::SoundnessMode`]. `geometry_of` maps a
//! fixture circuit name (`verifier_common::test_circuits::CIRCUITS`) to its
//! definition's geometry; the tests below keep the files current.

use circuit_common::{CircuitGeometry, DelegationCircuit, RiscVCycleCircuit};
use prover::field::baby_bear::base::BabyBearField;
use verifier_common::test_circuits::CircuitData;

use crate::*;

/// The geometry of the circuit definition behind the fixture circuit `name`.
pub fn geometry_of(name: &str) -> CircuitGeometry {
    type F = BabyBearField;
    match name {
        "add_sub_lui_auipc_mop" => {
            <AddSubLuiAuipcMopCircuit as RiscVCycleCircuit<F, false>>::geometry()
        }
        "bigint_with_extended_control" => {
            <BigIntDelegationCircuit as DelegationCircuit<F>>::geometry()
        }
        "blake2_g_function" => {
            <Blake2sGFunctionDelegationCircuit as DelegationCircuit<F>>::geometry()
        }
        "blake2_with_extended_control" => {
            <Blake2sWithCompressionDelegationCircuit as DelegationCircuit<F>>::geometry()
        }
        "inits_and_teardowns" => inits_and_teardowns::geometry(),
        "jump_branch_slt" => <JumpBranchSltCircuit as RiscVCycleCircuit<F, false>>::geometry(),
        "keccak_chi5" => <KeccakChi5DelegationCircuit as DelegationCircuit<F>>::geometry(),
        "keccak_column_parity" => {
            <KeccakColumnParityDelegationCircuit as DelegationCircuit<F>>::geometry()
        }
        "keccak_special5" => <KeccakSpecial5DelegationCircuit as DelegationCircuit<F>>::geometry(),
        "keccak_theta_rho" => <KeccakThetaRhoDelegationCircuit as DelegationCircuit<F>>::geometry(),
        "mem_subword_only" => {
            <LoadStoreSubwordOnlyCircuit as RiscVCycleCircuit<F, true>>::geometry()
        }
        "mem_word_only" => <LoadStoreWordOnlyCircuit as RiscVCycleCircuit<F, true>>::geometry(),
        "shift_binop" => <ShiftBinaryCircuit as RiscVCycleCircuit<F, false>>::geometry(),
        "unified_reduced_machine" => {
            <UnifiedReducedMachineCircuit as RiscVCycleCircuit<F, true>>::geometry()
        }
        "unsigned_mul_div" => <UnsignedMulDivCircuit as RiscVCycleCircuit<F, false>>::geometry(),
        other => panic!("no circuit definition is registered for the fixture circuit {other}"),
    }
}

/// The circuit crate root of a fixture circuit (its `production_path` is
/// relative to the repository root's children).
pub fn circuit_crate_root(circuit: &CircuitData) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(circuit.production_path.trim_start_matches("../"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use circuit_common::{
        prover_config_file_name, prover_config_notes_file_name, SecurityLevel, SoundnessMode,
    };
    use prover::gkr::prover_config::ProverConfig;
    use verifier_common::test_circuits::CIRCUITS;

    /// Every serialized config equals the one its circuit's geometry derives
    /// from the compiled circuit (and the notes match); otherwise run
    /// `cargo test -p setups --release -- --ignored regenerate_prover_config_fixtures`.
    /// The default-mode config from the geometry alone (what the provers use
    /// by circuit type) must be the same config.
    #[test]
    fn prover_config_fixtures_are_current() {
        for circuit in CIRCUITS.iter() {
            let geometry = geometry_of(circuit.name);
            let compiled = circuit.compiled_circuit();
            let root = circuit_crate_root(circuit);
            for &level in SecurityLevel::ALL {
                assert_eq!(
                    geometry.default_mode_prover_config(level),
                    geometry.prover_config(&compiled, level, SoundnessMode::DEFAULT),
                    "{}: the default-mode config must not depend on the column count",
                    circuit.name
                );
                for &mode in SoundnessMode::ALL {
                    let path = root.join(prover_config_file_name(level, mode));
                    let on_disk: ProverConfig = serde_json::from_reader(
                        std::fs::File::open(&path)
                            .unwrap_or_else(|e| panic!("{}: {e}", path.display())),
                    )
                    .unwrap();
                    assert_eq!(
                        on_disk,
                        geometry.prover_config(&compiled, level, mode),
                        "{} is stale: regenerate the prover config fixtures",
                        path.display()
                    );
                    let notes_path = root.join(prover_config_notes_file_name(level, mode));
                    match geometry.prover_config_notes(&compiled, level, mode) {
                        Some(notes) => assert_eq!(
                            std::fs::read_to_string(&notes_path)
                                .unwrap_or_else(|e| panic!("{}: {e}", notes_path.display())),
                            notes,
                            "{} is stale",
                            notes_path.display()
                        ),
                        None => assert!(
                            !notes_path.exists(),
                            "{} has no notes in this mode",
                            notes_path.display()
                        ),
                    }
                }
            }
        }
    }

    /// A geometry whose declared trace length differs from the compiled circuit's is
    /// refused before any schedule is resolved.
    #[test]
    #[should_panic(
        expected = "TraceLengthMismatch: declared trace length 8388608 differs from compiled trace length 16777216"
    )]
    fn mismatched_trace_length_is_refused() {
        let circuit = CIRCUITS
            .iter()
            .find(|circuit| circuit.name == "add_sub_lui_auipc_mop")
            .expect("fixture circuit");
        let geometry = geometry_of(circuit.name);
        assert_eq!(geometry.trace_len_log2, 24);
        let mismatched = CircuitGeometry {
            trace_len_log2: 23,
            ..geometry
        };
        mismatched.prover_config(
            &circuit.compiled_circuit(),
            SecurityLevel::Sec100,
            SoundnessMode::PessimisticConjecture,
        );
    }

    /// Rewrite every circuit's config (and notes) files from its geometry.
    #[test]
    #[ignore]
    fn regenerate_prover_config_fixtures() {
        for circuit in CIRCUITS.iter() {
            let compiled = circuit.compiled_circuit();
            circuit_common::save_prover_configs_in(
                &circuit_crate_root(circuit),
                &compiled,
                &geometry_of(circuit.name),
            );
        }
    }
}
