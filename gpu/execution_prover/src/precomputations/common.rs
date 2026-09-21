use super::CircuitPrecomputations;
use gpu_trace::witness::circuit_type::CircuitType;

use crate::upstream::{build_common_setups, SecurityLevel};
use std::collections::BTreeMap;
use worker::Worker;

/// Build the binary-independent precomputations — every delegation circuit and
/// inits-and-teardowns — from the shared canonical setups.
pub(crate) fn get_common_precomputations_for_all(
    worker: &Worker,
    security_level: SecurityLevel,
) -> BTreeMap<CircuitType, CircuitPrecomputations> {
    build_common_setups(worker)
        .into_iter()
        .map(|(circuit_type, setup)| {
            let (log_lde_factor, log_rows_per_leaf, log_tree_cap_size) =
                config_logs_for_circuit(circuit_type, security_level);
            let precomputations = CircuitPrecomputations::from_canonical(
                circuit_type,
                setup,
                log_lde_factor,
                log_rows_per_leaf,
                log_tree_cap_size,
            )
            .unwrap();
            (circuit_type, precomputations)
        })
        .collect()
}

/// The WHIR geometry the GPU worker will use at `prove()` time, which differs
/// per circuit.
pub(crate) fn config_logs_for_circuit(
    circuit_type: CircuitType,
    security_level: SecurityLevel,
) -> (u32, u32, u32) {
    let prover_config = gpu_circuit_prover::config::prover_config(circuit_type, security_level)
        .expect("ExecutionProverConfiguration validated GPU security level before precomputation");
    (
        prover_config.lde_factor.trailing_zeros(),
        prover_config.base_oracles_values_per_leaf.trailing_zeros(),
        prover_config.cap_size.trailing_zeros(),
    )
}

#[cfg(test)]
mod tests {
    use gpu_trace::witness::circuit_type::{
        CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
        UnrolledNonMemoryCircuitType,
    };

    fn every_circuit_type() -> Vec<CircuitType> {
        use gpu_core::primitives::machine_type::MachineType;
        let mut out = vec![
            CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
            CircuitType::Unrolled(UnrolledCircuitType::Unified),
        ];
        out.extend(
            DelegationCircuitType::get_all_delegation_types()
                .iter()
                .map(|d| CircuitType::Delegation(*d)),
        );
        for machine in [
            MachineType::Full,
            MachineType::FullUnsigned,
            MachineType::Reduced,
        ] {
            out.extend(
                UnrolledMemoryCircuitType::get_circuit_types_for_machine_type(machine)
                    .iter()
                    .map(|c| CircuitType::Unrolled(UnrolledCircuitType::Memory(*c))),
            );
            out.extend(
                UnrolledNonMemoryCircuitType::get_circuit_types_for_machine_type(machine)
                    .iter()
                    .map(|c| CircuitType::Unrolled(UnrolledCircuitType::NonMemory(*c))),
            );
        }
        out.sort();
        out.dedup();
        out
    }

    /// Both backends must commit and prove under the same geometry, and each
    /// reads it from its own entry point so a CPU backend need not depend on
    /// the GPU one. This pins the two to the same values.
    #[test]
    fn cpu_shared_and_gpu_prover_configs_agree_for_every_circuit() {
        let security_level = crate::upstream::SecurityLevel::Sec100;
        let circuits = every_circuit_type();
        assert!(!circuits.is_empty());

        for circuit_type in circuits {
            let shared = execution_prover::config::prover_config(circuit_type, security_level);
            let gpu = gpu_circuit_prover::config::prover_config(circuit_type, security_level)
                .expect("Sec100 is a supported GPU security level");

            assert_eq!(
                shared.lde_factor, gpu.lde_factor,
                "{circuit_type:?} LDE factor differs"
            );
            assert_eq!(
                shared.cap_size, gpu.cap_size,
                "{circuit_type:?} cap size differs"
            );
            assert_eq!(
                shared.base_oracles_values_per_leaf, gpu.base_oracles_values_per_leaf,
                "{circuit_type:?} base oracle leaf width differs"
            );
            assert_eq!(
                shared.whir_schedule.whir_steps_schedule, gpu.whir_schedule.whir_steps_schedule,
                "{circuit_type:?} WHIR step schedule differs"
            );
            assert_eq!(
                shared.whir_schedule.base_lde_factor, gpu.whir_schedule.base_lde_factor,
                "{circuit_type:?} WHIR base LDE factor differs"
            );
            assert_eq!(
                shared.security_level.security_bits(),
                gpu.security_level.security_bits(),
                "{circuit_type:?} security bits differ"
            );
        }
    }
}
