use super::*;

pub(crate) fn create_blake_with_compression_delegation_layout() -> (
    CompiledCircuitArtifact<Mersenne31Field>,
    Vec<Vec<RawExpression<Mersenne31Field>>>,
) {
    (
        setups::blake2_with_compression::get_delegation_circuit().compiled_circuit,
        setups::blake2_with_compression::get_ssa_form(),
    )
}

// pub(crate) fn create_blake_delegation_layout() -> CompiledCircuitArtifact<Mersenne31Field> {
//     setups::blake2_single_round::get_delegation_circuit().compiled_circuit
// }

pub(crate) fn create_bigint_with_control_delegation_layout() -> (
    CompiledCircuitArtifact<Mersenne31Field>,
    Vec<Vec<RawExpression<Mersenne31Field>>>,
) {
    (
        setups::bigint_with_control::get_delegation_circuit().compiled_circuit,
        setups::bigint_with_control::get_ssa_form(),
    )
}

pub(crate) fn create_keccak_special5_delegation_layout() -> (
    CompiledCircuitArtifact<Mersenne31Field>,
    Vec<Vec<RawExpression<Mersenne31Field>>>,
) {
    (
        setups::keccak_special5::get_delegation_circuit().compiled_circuit,
        setups::keccak_special5::get_ssa_form(),
    )
}
