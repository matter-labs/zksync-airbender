use crate::gkr_compiler::compile_inits_and_teardowns_circuit;
use common_constants::circuit_families::INITS_AND_TEARDOWNS_FORMAL_CIRCUIT_FAMILY_IDX;
use prover::cs::gkr_compiler::GKRCircuitArtifact;
use prover::cs::*;
use prover::field::baby_bear::base::BabyBearField;
use prover::field::PrimeField;
use prover::gkr::prover_config::ProverConfig;
use prover::*;

pub const FAMILY_IDX: u8 = INITS_AND_TEARDOWNS_FORMAL_CIRCUIT_FAMILY_IDX;
/// log2 of the LOGICAL trace length for the purposes of GKR (the rows of the
/// circuit trace; the base commitment of this circuit is unpacked, so it is
/// also the committed polynomial size).
pub const TRACE_LEN_LOG2: u32 = 24;
pub const NUM_INIT_AND_TEARDOWN_SETS: usize = 8;
pub const WORD_BITS: u32 = 2;

fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

pub fn get_inits_and_teardowns_circuit<F: PrimeField>(use_caches: bool) -> GKRCircuitArtifact<F> {
    compile_inits_and_teardowns_circuit::<F, WORD_BITS>(
        NUM_INIT_AND_TEARDOWN_SETS,
        TRACE_LEN_LOG2 as usize,
        use_caches,
    )
}

pub fn get_table_driver<F: PrimeField>() -> prover::cs::tables::TableDriver<F> {
    prover::cs::tables::TableDriver::new()
}

/// The proving geometry of this trait-less circuit — the counterpart of
/// `DelegationCircuit::geometry`: a 2^24 trace, unpacked.
pub fn geometry() -> circuit_common::CircuitGeometry {
    circuit_common::CircuitGeometry {
        trace_len_log2: TRACE_LEN_LOG2,
        base_packing: circuit_common::BasePacking::NONE,
    }
}

/// The prover config this circuit is proved with (and its verifier generated
/// for) at `level` under `mode`, from the compiled circuit; serialized by
/// [`generate_artifacts`] next to the layout.
pub fn prover_config_in_mode(
    compiled_circuit: &GKRCircuitArtifact<BabyBearField>,
    level: prover::definitions::SecurityLevel,
    mode: circuit_common::SoundnessMode,
) -> ProverConfig {
    geometry().prover_config(compiled_circuit, level, mode)
}

/// The config in the default soundness mode, from the geometry alone.
pub fn prover_config(level: prover::definitions::SecurityLevel) -> ProverConfig {
    geometry().default_mode_prover_config(level)
}

/// This function will generate layout and quotient files for verifier, plus
/// the per-level, per-mode prover configs
/// (`generated/prover_config_<level>_<mode>.json`).
pub fn generate_artifacts() {
    let compiled_machine = get_inits_and_teardowns_circuit::<BabyBearField>(true);
    serialize_to_file(&compiled_machine, "generated/layout.json");
    circuit_common::save_prover_configs(&compiled_machine, &geometry());
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;

    #[cfg(test)]
    #[test]
    fn generate() {
        skip_if_ci!();
        generate_artifacts();
    }
}
