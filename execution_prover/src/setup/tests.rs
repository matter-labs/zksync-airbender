use super::*;
use execution_prover_model::circuit_type::{
    UnrolledCircuitType, UnrolledMemoryCircuitType, UnrolledNonMemoryCircuitType,
};
use execution_prover_model::MachineType;
use worker::Worker;

#[test]
fn cpu_every_unrolled_family_of_every_machine_type_builds() {
    let worker = Worker::new();
    let words = (1usize << (16 + common_constants::ROM_SECOND_WORD_BITS)) / 4;
    let binary = vec![0u32; words];
    for machine in [MachineType::FullUnsigned, MachineType::Reduced] {
        for circuit in UnrolledMemoryCircuitType::get_circuit_types_for_machine_type(machine) {
            let circuit_type = UnrolledCircuitType::Memory(*circuit);
            let canonical = build_unrolled_setup(machine, circuit_type, &binary, &binary, &worker);
            let CanonicalCircuitSetup::Riscv(setup) = canonical else {
                unreachable!()
            };
            assert_eq!(setup.trace_len, circuit_type.get_domain_size());
        }
        for circuit in UnrolledNonMemoryCircuitType::get_circuit_types_for_machine_type(machine) {
            let circuit_type = UnrolledCircuitType::NonMemory(*circuit);
            let canonical = build_unrolled_setup(machine, circuit_type, &binary, &binary, &worker);
            let CanonicalCircuitSetup::Riscv(setup) = canonical else {
                unreachable!()
            };
            assert_eq!(setup.trace_len, circuit_type.get_domain_size());
        }
    }
}
