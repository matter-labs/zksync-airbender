use crate::gkr_compiler::compile_inits_and_teardowns_circuit;
use common_constants::circuit_families::INITS_AND_TEARDOWNS_FORMAL_CIRCUIT_FAMILY_IDX;
use prover::cs::gkr_compiler::GKRCircuitArtifact;
use prover::cs::*;
use prover::field::baby_bear::base::BabyBearField;
use prover::field::PrimeField;
use prover::gkr::prover_config::ProverConfig;
use prover::*;

pub const FAMILY_IDX: u8 = INITS_AND_TEARDOWNS_FORMAL_CIRCUIT_FAMILY_IDX;
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

/// The prover config this circuit is proved with (and its verifier generated
/// for) at `level` — the counterpart of `DelegationCircuit::prover_config` for
/// this trait-less circuit; serialized by [`generate_artifacts`] next to the
/// layout.
pub fn prover_config(level: prover::definitions::SecurityLevel) -> ProverConfig {
    prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(
        TRACE_LEN_LOG2 as usize,
        level,
    )
}

/// This function will generate layout and quotient files for verifier, plus
/// the per-level prover configs (`generated/prover_config_<level>.json`).
pub fn generate_artifacts() {
    let compiled_machine = get_inits_and_teardowns_circuit::<BabyBearField>(true);
    serialize_to_file(&compiled_machine, "generated/layout.json");
    for &level in prover::definitions::SecurityLevel::ALL {
        let config = prover_config(level);
        assert_eq!(1usize << config.trace_len_log2, compiled_machine.trace_len);
        config.validate_for_whir_message_size(config.whir_message_size_log2());
        serialize_to_file(
            &config,
            &format!("generated/prover_config_{}.json", level.dir_suffix()),
        );
    }
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
