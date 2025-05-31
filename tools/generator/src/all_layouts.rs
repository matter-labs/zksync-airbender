use prover::cs::machine::machine_configurations::dump_ssa_witness_eval_form;

use super::*;

pub(crate) fn create_main_machine_layout_with_delegation() -> (
    CompiledCircuitArtifact<Mersenne31Field>,
    Vec<Vec<RawExpression<Mersenne31Field>>>,
) {
    let dummy_bytecode = vec![0u32; setups::risc_v_cycles::MAX_ROM_SIZE / 4];

    let compiled_machine = setups::risc_v_cycles::get_machine(
        &dummy_bytecode,
        setups::risc_v_cycles::ALLOWED_DELEGATION_CSRS,
    );

    let machine = setups::risc_v_cycles::formal_machine_for_compilation();
    let ssa = dump_ssa_witness_eval_form::<
        _,
        _,
        { setups::risc_v_cycles::ROM_ADDRESS_SPACE_SECOND_WORD_BITS },
    >(machine);

    (compiled_machine, ssa)
}

pub(crate) fn create_machine_without_signed_mul_div_layout_with_delegation() -> (
    CompiledCircuitArtifact<Mersenne31Field>,
    Vec<Vec<RawExpression<Mersenne31Field>>>,
) {
    let dummy_bytecode = vec![0u32; setups::machine_without_signed_mul_div::MAX_ROM_SIZE / 4];

    let compiled_machine = setups::machine_without_signed_mul_div::get_machine(
        &dummy_bytecode,
        setups::machine_without_signed_mul_div::ALLOWED_DELEGATION_CSRS,
    );

    let machine = setups::machine_without_signed_mul_div::formal_machine_for_compilation();
    let ssa = dump_ssa_witness_eval_form::<
        _,
        _,
        { setups::machine_without_signed_mul_div::ROM_ADDRESS_SPACE_SECOND_WORD_BITS },
    >(machine);

    (compiled_machine, ssa)
}

pub(crate) fn create_reduced_machine_layout_with_delegation() -> (
    CompiledCircuitArtifact<Mersenne31Field>,
    Vec<Vec<RawExpression<Mersenne31Field>>>,
) {
    let dummy_bytecode = vec![0u32; setups::reduced_risc_v_machine::MAX_ROM_SIZE / 4];

    let compiled_machine = setups::reduced_risc_v_machine::get_machine(
        &dummy_bytecode,
        setups::reduced_risc_v_machine::ALLOWED_DELEGATION_CSRS,
    );

    let machine = setups::reduced_risc_v_machine::formal_machine_for_compilation();
    let ssa = dump_ssa_witness_eval_form::<
        _,
        _,
        { setups::reduced_risc_v_machine::ROM_ADDRESS_SPACE_SECOND_WORD_BITS },
    >(machine);

    (compiled_machine, ssa)
}

pub(crate) fn create_final_reduced_machine_layout_with_delegation() -> (
    CompiledCircuitArtifact<Mersenne31Field>,
    Vec<Vec<RawExpression<Mersenne31Field>>>,
) {
    let dummy_bytecode = vec![0u32; setups::final_reduced_risc_v_machine::MAX_ROM_SIZE / 4];

    let compiled_machine = setups::final_reduced_risc_v_machine::get_machine(
        &dummy_bytecode,
        setups::final_reduced_risc_v_machine::ALLOWED_DELEGATION_CSRS,
    );

    let machine = setups::final_reduced_risc_v_machine::formal_machine_for_compilation();
    let ssa = dump_ssa_witness_eval_form::<
        _,
        _,
        { setups::final_reduced_risc_v_machine::ROM_ADDRESS_SPACE_SECOND_WORD_BITS },
    >(machine);

    (compiled_machine, ssa)
}

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

// pub(crate) fn create_poseidon2_delegation_layout() -> CompiledCircuitArtifact<Mersenne31Field> {
//     setups::poseidon2_compression_with_witness::get_delegation_circuit().compiled_circuit
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
