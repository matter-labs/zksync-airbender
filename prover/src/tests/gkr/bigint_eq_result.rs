use super::bigint_with_extended_control::witness_eval_fn;
use super::constraint_check::{failing, lowered_constraints, tampered_failures, F};
use super::{deserialize_from_file, find_base_layer_address};
use crate::gkr::witness_gen::delegation_circuits::evaluate_gkr_witness_for_delegation_circuit;
use crate::tracers::oracles::transpiler_oracles::delegation::BigintDelegationOracle;
use common_constants::{
    bigint_with_control::EQ_OP_BIT_IDX, rom::ROM_BYTE_SIZE, DELEGATION_INVOCATION_OFFSET,
};
use cs::gkr_circuits::delegation::bigint_with_control::bigint_with_extended_control_delegation_circuit_table_driver_fn;
use cs::gkr_compiler::GKRCircuitArtifact;
use cs::tables::TableDriver;
use field::Field;
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use std::alloc::Global;
use worker::Worker;

#[test]
fn bigint_eq_result_is_bound_to_the_equality_flag() {
    let circuit: GKRCircuitArtifact<F> = deserialize_from_file(
        "../cs/compiled_circuits/bigint_with_extended_control_layout_gkr.json",
    );
    let mut row = BigintDelegationWitness::empty();
    row.write_timestamp = (1 << 24) + DELEGATION_INVOCATION_OFFSET;
    let ptr = ROM_BYTE_SIZE as u32;
    for (access, value) in row
        .reg_accesses
        .iter_mut()
        .zip([ptr, ptr + 64, 1 << EQ_OP_BIT_IDX])
    {
        access.read_value = value;
        access.write_value = value;
    }
    row.reg_accesses[2].write_value = 1;
    let oracle = BigintDelegationOracle {
        cycle_data: &[row],
        marker: core::marker::PhantomData,
    };
    let mut table_driver = TableDriver::<F>::new();
    bigint_with_extended_control_delegation_circuit_table_driver_fn(&mut table_driver);
    let mut trace = evaluate_gkr_witness_for_delegation_circuit(
        &circuit,
        witness_eval_fn,
        circuit.trace_len,
        &oracle,
        &table_driver,
        &Worker::new(),
        Global,
        Global,
    );
    let x12_low = find_base_layer_address(&circuit, "control read/write from x12 write[0]");
    let constraints: Vec<_> = lowered_constraints(&circuit)
        .into_iter()
        .filter(|relation| {
            relation
                .linear_terms
                .iter()
                .any(|(_, address)| *address == x12_low)
        })
        .collect();
    assert!(failing(&constraints, &trace, 0).is_empty());
    assert!(!tampered_failures(&constraints, &mut trace, 0, &[(x12_low, F::ZERO)]).is_empty());
}
