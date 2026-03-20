use super::{execute_case, run_test_vector_opcode, ExpectedOutcome};
use crate::ir::FullUnsignedMachineDecoderConfig;

#[test]
fn test_vector_csrrw() {
    const CSRRW_NONDETERMINISM_OPCODE: u32 = 0x7c0110f3;
    const CSRRW_BLAKE2ROUNDEXTENDED_OPCODE: u32 = 0x7c7110f3;
    const CSRRW_U256BIGINTOPS_OPCODE: u32 = 0x7ca110f3;

    run_test_vector_opcode(
        "csrrw x1, 1984, x2",
        Some(CSRRW_NONDETERMINISM_OPCODE),
        [0; 32],
        None,
    );
    run_test_vector_opcode(
        "csrrw x1, 1991, x2",
        Some(CSRRW_BLAKE2ROUNDEXTENDED_OPCODE),
        [0; 32],
        None,
    );
    run_test_vector_opcode(
        "csrrw x1, 1994, x2",
        Some(CSRRW_U256BIGINTOPS_OPCODE),
        [0; 32],
        None,
    );
}

#[test]
#[should_panic(
    expected = "detected transpiler marker CSR during replay; programs containing development cycle markers must not be proved"
)]
fn test_vector_marker_csr_is_rejected_by_replayer() {
    const CSRRW_MARKER_OPCODE: u32 = 0x7ff01073; // csrrw x0, 2047, x0

    execute_case::<FullUnsignedMachineDecoderConfig>(
        &[CSRRW_MARKER_OPCODE],
        [0; 32],
        &ExpectedOutcome {
            final_pc: 4,
            register_checks: vec![],
            memory_checks: vec![],
        },
    );
}
