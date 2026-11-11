use super::*;
use crate::ExecutionKind;
use execution_prover_model::MachineType;
use worker::Worker;

#[test]
fn cpu_every_unrolled_family_of_every_machine_type_builds() {
    let worker = Worker::new_with_num_threads(8);
    let words = (1usize << (16 + common_constants::ROM_SECOND_WORD_BITS)) / 4;
    let mut binary = vec![0u32; words];
    // A jump loop makes the signed division unreachable. It must still retain
    // the original FullUnsigned setup decoding when the execution ISA is Full.
    binary[0] = 0x0000_006f;
    binary[1] = 0x0220_c033; // div x0, x1, x2
    let full = preprocess_binary(MachineType::Full, &[ExecutionKind::Unrolled], &binary);
    let execution = riscv_transpiler::ir::simple_instruction_set::preprocess_bytecode::<
        riscv_transpiler::ir::FullMachineDecoderConfig,
        true,
    >(&binary);
    assert!(
        full.execution_instructions == execution,
        "Full execution tape changed"
    );
    for machine in [MachineType::FullUnsigned, MachineType::Reduced] {
        for circuit_type in circuit_types_for_variant(ExecutionKind::Unrolled, machine) {
            let CanonicalCircuitSetup::Riscv(setup) =
                build_unrolled_setup(machine, circuit_type, &binary, &binary, &worker)
            else {
                unreachable!()
            };
            assert_eq!(setup.trace_len, circuit_type.get_domain_size());
            if machine == MachineType::FullUnsigned {
                let CanonicalCircuitSetup::Riscv(candidate) =
                    build_unrolled_setup_with_preprocessing(circuit_type, &binary, &full, &worker)
                else {
                    unreachable!()
                };
                assert_eq!(
                    setup.setup.hypercube_evals.len(),
                    candidate.setup.hypercube_evals.len()
                );
                for (column, (expected, actual)) in setup
                    .setup
                    .hypercube_evals
                    .iter()
                    .zip(&candidate.setup.hypercube_evals)
                    .enumerate()
                {
                    assert_eq!(expected.len(), actual.len());
                    let differing_row = expected
                        .iter()
                        .zip(actual.iter())
                        .position(|(expected, actual)| expected != actual);
                    assert_eq!(differing_row, None, "Full setup differs from original FullUnsigned setup for {circuit_type:?}, column {column}");
                }
            }
        }
    }
}
