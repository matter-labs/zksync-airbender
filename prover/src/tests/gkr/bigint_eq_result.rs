use super::bigint_with_extended_control::witness_eval_fn;
use super::relative_timestamps::{failing, lowered_constraints, tampered_failures};
use super::{deserialize_from_file, find_base_layer_address, read_cell};
use crate::gkr::witness_gen::delegation_circuits::evaluate_gkr_witness_for_delegation_circuit;
use crate::tracers::oracles::transpiler_oracles::delegation::BigintDelegationOracle;
use ::cs::definitions::gkr::{RamAddress, RamQuery, RamWordRepresentation};
use ::cs::definitions::GKRAddress;
use ::cs::gkr_circuits::delegation::bigint_with_control::bigint_with_extended_control_delegation_circuit_table_driver_fn;
use ::cs::gkr_compiler::GKRCircuitArtifact;
use ::cs::tables::TableDriver;
use ::field::baby_bear::base::BabyBearField;
use ::field::{Field, PrimeField};
use common_constants::bigint_with_control::EQ_OP_BIT_IDX;
use common_constants::rom::ROM_BYTE_SIZE;
use common_constants::{TimestampData, TimestampScalar, DELEGATION_INVOCATION_OFFSET};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::{RegisterOrIndirectReadData, RegisterOrIndirectReadWriteData};
use std::alloc::Global;
use worker::Worker;

type F = BabyBearField;

#[test]
fn bigint_eq_result_is_bound_to_the_equality_flag() {
    let circuit: GKRCircuitArtifact<F> = deserialize_from_file(
        "../cs/compiled_circuits/bigint_with_extended_control_layout_gkr.json",
    );
    let rows: Vec<_> = [
        ([u32::MAX; 8], [u32::MAX; 8], 1),
        ([5, 0, 0, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 0], 0),
    ]
    .into_iter()
    .enumerate()
    .map(|(index, (a, b, x12_out))| {
        let write_timestamp =
            (1 << 24) + 16 * index as TimestampScalar + DELEGATION_INVOCATION_OFFSET;
        let timestamp = TimestampData::from_scalar(write_timestamp - 5);
        let a_ptr = ROM_BYTE_SIZE as u32 + 128 * index as u32;
        let register = |read_value, write_value| RegisterOrIndirectReadWriteData {
            read_value,
            write_value,
            timestamp,
        };
        let mut row = BigintDelegationWitness::empty();
        row.write_timestamp = write_timestamp;
        row.reg_accesses = [
            register(a_ptr, a_ptr),
            register(a_ptr + 64, a_ptr + 64),
            register(1 << EQ_OP_BIT_IDX, x12_out),
        ];
        row.indirect_reads = b.map(|read_value| RegisterOrIndirectReadData {
            read_value,
            timestamp,
        });
        row.indirect_writes = a.map(|value| register(value, value));
        row
    })
    .collect();
    let oracle = BigintDelegationOracle {
        cycle_data: &rows,
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
    let x12_low = circuit
        .memory_layout
        .ram_access_sets
        .iter()
        .find_map(|query| match query {
            RamQuery::Write(write) if write.address == RamAddress::ConstantRegister(12) => {
                match write.write_value {
                    RamWordRepresentation::U16Limbs([low, _]) => {
                        Some(GKRAddress::BaseLayerMemory(low))
                    }
                    _ => None,
                }
            }
            _ => None,
        })
        .unwrap();
    let flag = find_base_layer_address(&circuit, "values are equal for perform eq");
    let constraints: Vec<_> = lowered_constraints(&circuit)
        .into_iter()
        .filter(|relation| {
            relation
                .linear_terms
                .iter()
                .any(|(_, address)| *address == x12_low || *address == flag)
        })
        .collect();
    assert_eq!(constraints.len(), 2);

    for (row, expected) in [1, 0, 0].into_iter().enumerate() {
        assert_eq!(read_cell(&trace, x12_low, row).as_u32_reduced(), expected);
        assert!(failing(&constraints, &trace, row).is_empty());
    }
    assert_eq!(read_cell(&trace, flag, 2), F::ONE);

    for (row, expected) in [1, 0].into_iter().enumerate() {
        let wrong = F::from_u32_unchecked(1 - expected);
        assert!(!tampered_failures(&constraints, &mut trace, row, &[(x12_low, wrong)]).is_empty());
        let failures = tampered_failures(
            &constraints,
            &mut trace,
            row,
            &[(x12_low, wrong), (flag, wrong)],
        );
        assert!(!failures.is_empty());
        assert!(failures.iter().all(|inputs| !inputs.contains(&x12_low)));
    }
}
