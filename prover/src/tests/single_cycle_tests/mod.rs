use crate::gkr::witness_gen::oracles::*;
use ::cs::oracle::Placeholder;
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
mod unified_extended_circuit_tests;

pub(crate) fn test_single_non_mem_cycle<F: PrimeField, OPT: DecodingOptions>(
    opcode: u32,
    circuit_family: u8,
    decoder: impl OpcodeFamilyDecoder,
    opcode_data: NonMemoryOpcodeTracingData,
    circuit_table_addition_fn: impl FnOnce(&mut BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>),
    circuit_fn: impl FnOnce(&mut BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>),
) {
    let mut t = process_binary_into_separate_tables_ext::<F, OPT, false, Global>(
        &[opcode],
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

#[allow(dead_code)]
pub(crate) fn test_single_mem_cycle<F: PrimeField, OPT: DecodingOptions>(
    opcode: u32,
    circuit_family: u8,
    decoder: impl OpcodeFamilyDecoder,
    opcode_data: NonMemoryOpcodeTracingData,
    _binary: &[u32],
    circuit_table_addition_fn: impl FnOnce(&mut BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>),
    circuit_fn: impl FnOnce(&mut BasicAssembly<F, CSDebugWitnessEvaluator<F>, false>),
) {
    let mut t = process_binary_into_separate_tables_ext::<F, OPT, false, Global>(
        &[opcode],
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
    let circuit_family = decoder.instruction_family_index();
    // Unsupported words (e.g. `unimp` trap padding) only matter if executed: a replayed cycle
    // at such a PC fails the decoder lookup.
    let mut t = process_binary_into_separate_tables_ext::<F, OPT, true, Global>(
        binary,
        &[Box::new(decoder)],
        1 << 20,
        &[
            NON_DETERMINISM_CSR as u16,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            KECCAK_SPECIAL5_CSR_REGISTER as u16,
            KECCAK_THETA_RHO_CSR_REGISTER as u16,
            KECCAK_COLUMN_PARITY_CSR_REGISTER as u16,
            KECCAK_CHI5_CSR_REGISTER as u16,
        ],
    );
    let decoder_data = t.remove(&circuit_family).expect("decoder data");

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

/// Oracle wrapper that poisons every `ShuffleRamWriteValue` query.
///
/// The `ASSUME_MEMORY_VALUES_ASSIGNED == false` regime has a
/// self-generating witness contract: the oracle is only trusted for
/// INPUTS (instruction, register/memory READ values, timestamps); every
/// family must DERIVE its outputs (the shared rd/mem write-value columns)
/// in-circuit, gated on its own activity mask. If any family silently
/// falls back to the oracle for its write value, this wrapper feeds it
/// garbage and the per-family rd-write constraints reject the row.
pub(crate) struct PoisonedWriteValueOracle<O>(pub(crate) O);

impl<F: PrimeField, O: ::cs::oracle::Oracle<F>> ::cs::oracle::Oracle<F>
    for PoisonedWriteValueOracle<O>
{
    fn get_witness_from_placeholder(
        &self,
        placeholder: Placeholder,
        subindex: usize,
        trace_row: usize,
    ) -> F {
        if matches!(placeholder, Placeholder::ShuffleRamWriteValue(_)) {
            return F::from_u32_with_reduction(0xBEEF);
        }
        self.0
            .get_witness_from_placeholder(placeholder, subindex, trace_row)
    }

    fn get_u32_witness_from_placeholder(&self, placeholder: Placeholder, trace_row: usize) -> u32 {
        if matches!(placeholder, Placeholder::ShuffleRamWriteValue(_)) {
            return 0xDEAD_BEEF;
        }
        self.0
            .get_u32_witness_from_placeholder(placeholder, trace_row)
    }

    fn get_u16_witness_from_placeholder(&self, placeholder: Placeholder, trace_row: usize) -> u16 {
        if matches!(placeholder, Placeholder::ShuffleRamWriteValue(_)) {
            return 0xBEEF;
        }
        self.0
            .get_u16_witness_from_placeholder(placeholder, trace_row)
    }

    fn get_u8_witness_from_placeholder(&self, placeholder: Placeholder, trace_row: usize) -> u8 {
        // no write-value placeholder is queried as u8; delegate (must NOT
        // fall through to the trait default, which routes via the field
        // query the inner oracle doesn't support for every placeholder)
        self.0
            .get_u8_witness_from_placeholder(placeholder, trace_row)
    }

    fn get_boolean_witness_from_placeholder(
        &self,
        placeholder: Placeholder,
        trace_row: usize,
    ) -> bool {
        self.0
            .get_boolean_witness_from_placeholder(placeholder, trace_row)
    }

    fn get_timestamp_witness_from_placeholder(
        &self,
        placeholder: Placeholder,
        trace_row: usize,
    ) -> cs::definitions::TimestampScalar {
        self.0
            .get_timestamp_witness_from_placeholder(placeholder, trace_row)
    }

    fn get_executor_family_data(
        &self,
        trace_row: usize,
    ) -> cs::gkr_circuits::ExecutorFamilyDecoderData {
        self.0.get_executor_family_data(trace_row)
    }
}
