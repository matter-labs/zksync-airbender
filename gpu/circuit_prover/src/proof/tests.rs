use super::*;
use crate::upstream::SecurityLevel;
use gpu_gkr::proof_layout::build_proof_layout_inputs_for_geometry;
use gpu_trace::witness::circuit_type::{CircuitType, DelegationCircuitType};

fn check_layout(mutate: impl FnOnce(&mut crate::upstream::WhirSchedule)) {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../cs/compiled_circuits/blake2_with_extended_control_layout_gkr.json");
    let circuit = Arc::new(serde_json::from_reader(std::fs::File::open(path).unwrap()).unwrap());
    let programs = GkrPrograms::compile(
        CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression),
        circuit,
    )
    .unwrap();
    let config = programs.circuit_type().prover_config(SecurityLevel::Sec100);
    let geometry =
        BaseCommitmentGeometry::from_config(&config, BaseColumns::of(programs.compiled_circuit()));
    let mut schedule = config.whir_schedule.clone();
    mutate(&mut schedule);
    build_proof_layout_inputs_for_geometry(
        &programs,
        &schedule,
        config.sumcheck_explicit_output_size_log_2 as u32,
        geometry,
    );
}

#[test]
#[should_panic(expected = "base-round folding PoW is not implemented")]
fn cpu_base_folding_pow_is_refused() {
    check_layout(|schedule| schedule.base_round.folding_pow_bits = 1);
}

#[test]
#[should_panic(expected = "exactly one OOD sample per oracle")]
fn cpu_multiple_ood_samples_are_refused() {
    check_layout(|schedule| schedule.internal_rounds[0].num_ood_samples = 2);
}

#[test]
#[should_panic(expected = "symbolic term outside current oracle domain")]
fn cpu_missing_query_subgroup_is_refused() {
    check_layout(|schedule| schedule.internal_rounds[0].lde_factor_log2 = 0);
}

#[test]
#[should_panic(expected = "query domain must be strictly below field two-adicity")]
fn cpu_base_query_domain_is_refused() {
    check_layout(|schedule| schedule.base_round.lde_factor_log2 = 5);
}

#[test]
#[should_panic(expected = "recomputation must omit a nonempty prefix")]
fn cpu_gkr_recompute_requires_nonempty_prefix() {
    memory_policy::GkrMemoryPolicy::Recompute {
        value_layers: 0,
        cache_layers: 0,
    }
    .validate_for_main_layers(3);
}

#[test]
#[should_panic(expected = "value omission must retain the final MAIN value layer")]
fn cpu_gkr_recompute_retains_final_value_layer() {
    memory_policy::GkrMemoryPolicy::Recompute {
        value_layers: 3,
        cache_layers: 0,
    }
    .validate_for_main_layers(3);
}

#[test]
#[should_panic(expected = "cache omission exceeds the MAIN layer count")]
fn cpu_gkr_recompute_bounds_cache_omission() {
    memory_policy::GkrMemoryPolicy::Recompute {
        value_layers: 0,
        cache_layers: 4,
    }
    .validate_for_main_layers(3);
}
