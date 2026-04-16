use super::*;

#[cfg(test)]
mod test {
    use super::*;
    use cs::gkr_circuits::DivMulDecoder;
    use cs::gkr_circuits::{
        mul_div_circuit_with_preprocessed_bytecode_for_gkr, mul_div_table_addition_fn,
    };
    use field::baby_bear::base::BabyBearField;
    use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;

    type F = BabyBearField;

    fn test_mul_div_circuit(opcode: u32, opcode_data: NonMemoryOpcodeTracingData) {
        test_single_non_mem_cycle::<F, FullUnsignedMachineDecoderConfig>(
            opcode,
            MUL_DIV_CIRCUIT_FAMILY_IDX,
            DivMulDecoder::<false>,
            opcode_data,
            |cs| {
                mul_div_table_addition_fn::<F, _, false>(cs);
            },
            |cs| {
                mul_div_circuit_with_preprocessed_bytecode_for_gkr::<F, _, false>(cs);
            },
        )
    }

    #[test]
    fn test_div_non_zero_by_zero() {
        let divu_opcode_data = NonMemoryOpcodeTracingData {
            initial_pc: 0,
            rs1_value: 42,
            rs2_value: 0,
            rd_old_value: 0,
            rd_value: u32::MAX,
            new_pc: 4,
            delegation_type: 0,
        };
        let divu_opcode = 0x0220d1b3;
        test_mul_div_circuit(divu_opcode, divu_opcode_data);

        let remu_opcode_data = NonMemoryOpcodeTracingData {
            initial_pc: 0,
            rs1_value: 42,
            rs2_value: 0,
            rd_old_value: 0,
            rd_value: 42,
            new_pc: 4,
            delegation_type: 0,
        };
        let remu_opcode = 0x0220f1b3;
        test_mul_div_circuit(remu_opcode, remu_opcode_data);
    }

    #[test]
    fn test_div_zero_by_zero() {
        let divu_opcode_data = NonMemoryOpcodeTracingData {
            initial_pc: 0,
            rs1_value: 0,
            rs2_value: 0,
            rd_old_value: 0,
            rd_value: u32::MAX,
            new_pc: 4,
            delegation_type: 0,
        };
        let divu_opcode = 0x0220d1b3;
        test_mul_div_circuit(divu_opcode, divu_opcode_data);

        let remu_opcode_data = NonMemoryOpcodeTracingData {
            initial_pc: 0,
            rs1_value: 0,
            rs2_value: 0,
            rd_old_value: 0,
            rd_value: 0,
            new_pc: 4,
            delegation_type: 0,
        };
        let remu_opcode = 0x0220f1b3;
        test_mul_div_circuit(remu_opcode, remu_opcode_data);
    }
}
