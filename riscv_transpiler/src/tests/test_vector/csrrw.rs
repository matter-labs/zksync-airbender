use super::run_test_vector_opcode;

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
