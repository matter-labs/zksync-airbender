use crate::gkr::witness_gen::oracles::*;
use common_constants::*;
use cs::cs::circuit_impl::BasicAssembly;
use cs::cs::circuit_trait::Circuit;
use cs::gkr_circuits::process_binary_into_separate_tables_ext;
use cs::gkr_circuits::OpcodeFamilyDecoder;
use cs::witness_placer::cs_debug_evaluator::CSDebugWitnessEvaluator;
use field::PrimeField;
use riscv_transpiler::ir::DecodingOptions;
use riscv_transpiler::witness::*;
use std::alloc::Global;

mod mul_div_circuit;
mod unified_circuit_tests;

pub(crate) fn test_single_non_mem_cycle<F: PrimeField, OPT: DecodingOptions>(
    opcode: u32,
    circuit_family: u8,
    decoder: impl OpcodeFamilyDecoder,
    opcode_data: NonMemoryOpcodeTracingData,
    circuit_table_addition_fn: impl FnOnce(&mut BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>),
    circuit_fn: impl FnOnce(&mut BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>),
) {
    let mut t = process_binary_into_separate_tables_ext::<F, OPT, false, Global>(
        &vec![opcode],
        &[Box::new(decoder)],
        1 << 20,
        &[
            NON_DETERMINISM_CSR as u16,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            KECCAK_SPECIAL5_CSR_REGISTER as u16,
            BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
        ],
    );
    let decoder_data = t.remove(&circuit_family).expect("decoder data");
    assert_eq!(opcode_data.initial_pc, 0);

    {
        let oracle_input = NonMemoryOpcodeTracingDataWithTimestamp {
            opcode_data,
            rs1_read_timestamp: TimestampData::from_scalar(0),
            rs2_read_timestamp: TimestampData::from_scalar(0),
            rd_read_timestamp: TimestampData::from_scalar(0),
            cycle_timestamp: TimestampData::from_scalar(4),
        };

        let decoder_data = decoder_data[0].expect("is some");

        let oracle = NonMemoryCircuitOracle {
            inner: &[oracle_input],
            decoder_table: &[Some(decoder_data)],
            default_pc_value_in_padding: 4,
        };

        let oracle: NonMemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
        let mut cs = BasicAssembly::<F, CSDebugWitnessEvaluator<F>, false>::new_with_oracle_and_preprocessed_decoder(
            oracle,
            vec![decoder_data],
        );

        (circuit_table_addition_fn)(&mut cs);
        (circuit_fn)(&mut cs);

        assert!(cs.is_satisfied());
    }
}

pub(crate) fn test_single_mem_cycle<F: PrimeField, OPT: DecodingOptions>(
    opcode: u32,
    circuit_family: u8,
    decoder: impl OpcodeFamilyDecoder,
    opcode_data: NonMemoryOpcodeTracingData,
    binary: &[u32],
    circuit_table_addition_fn: impl FnOnce(&mut BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>),
    circuit_fn: impl FnOnce(&mut BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>),
) {
    let mut t = process_binary_into_separate_tables_ext::<F, OPT, false, Global>(
        &vec![opcode],
        &[Box::new(decoder)],
        1 << 20,
        &[
            NON_DETERMINISM_CSR as u16,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            KECCAK_SPECIAL5_CSR_REGISTER as u16,
            BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
        ],
    );
    let decoder_data = t.remove(&circuit_family).expect("decoder data");
    assert_eq!(opcode_data.initial_pc, 0);

    {
        let oracle_input = NonMemoryOpcodeTracingDataWithTimestamp {
            opcode_data,
            rs1_read_timestamp: TimestampData::from_scalar(0),
            rs2_read_timestamp: TimestampData::from_scalar(0),
            rd_read_timestamp: TimestampData::from_scalar(0),
            cycle_timestamp: TimestampData::from_scalar(4),
        };

        let decoder_data = decoder_data[0].expect("is some");

        let oracle = NonMemoryCircuitOracle {
            inner: &[oracle_input],
            decoder_table: &[Some(decoder_data)],
            default_pc_value_in_padding: 4,
        };

        let oracle: NonMemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
        let mut cs = BasicAssembly::<F, CSDebugWitnessEvaluator<F>, false>::new_with_oracle_and_preprocessed_decoder(
            oracle,
            vec![decoder_data],
        );

        (circuit_table_addition_fn)(&mut cs);
        (circuit_fn)(&mut cs);

        assert!(cs.is_satisfied());
    }
}

pub(crate) fn test_single_unified_cycle<F: PrimeField, OPT: DecodingOptions>(
    decoder: impl OpcodeFamilyDecoder,
    opcode_data: UnifiedOpcodeTracingDataWithTimestamp,
    binary: &[u32],
    circuit_table_addition_fn: impl FnOnce(&mut BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>),
    circuit_fn: impl FnOnce(&mut BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>),
) {
    test_single_unified_cycle_with_oracle::<F, OPT, _>(
        decoder,
        opcode_data,
        binary,
        circuit_table_addition_fn,
        circuit_fn,
        |oracle| oracle,
    )
}

/// Like [`test_single_unified_cycle`], but lets the caller wrap the trace
/// oracle (e.g. to poison output placeholders and pin the self-generating
/// witness contract of the `ASSUME_MEMORY_VALUES_ASSIGNED == false` regime).
pub(crate) fn test_single_unified_cycle_with_oracle<
    F: PrimeField,
    OPT: DecodingOptions,
    O: ::cs::oracle::Oracle<F> + 'static,
>(
    decoder: impl OpcodeFamilyDecoder,
    opcode_data: UnifiedOpcodeTracingDataWithTimestamp,
    binary: &[u32],
    circuit_table_addition_fn: impl FnOnce(&mut BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>),
    circuit_fn: impl FnOnce(&mut BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>),
    wrap_oracle: impl FnOnce(UnifiedRiscvCircuitOracle<'static>) -> O,
) {
    let mut t = process_binary_into_separate_tables_ext::<F, OPT, false, Global>(
        binary,
        &[Box::new(decoder)],
        1 << 20,
        &[
            NON_DETERMINISM_CSR as u16,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
        ],
    );
    let decoder_data = t
        .remove(&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX)
        .expect("decoder data");

    {
        let oracle = UnifiedRiscvCircuitOracle {
            inner: &[opcode_data],
            decoder_table: &decoder_data,
        };

        let oracle: UnifiedRiscvCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
        let oracle = (wrap_oracle)(oracle);
        let mut cs = BasicAssembly::<F, CSDebugWitnessEvaluator<F>, false>::new_with_oracle_and_preprocessed_decoder(
            oracle,
            decoder_data.iter().map(|el| el.unwrap_or_default()).collect::<Vec<_>>(),
        );

        (circuit_table_addition_fn)(&mut cs);
        (circuit_fn)(&mut cs);

        assert!(cs.is_satisfied());
    }
}
