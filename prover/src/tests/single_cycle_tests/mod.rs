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
