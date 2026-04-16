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
    fn test_div_non_zero_by_one() {
        let divu_opcode_data = NonMemoryOpcodeTracingData {
            initial_pc: 0,
            rs1_value: 42,
            rs2_value: 1,
            rd_old_value: 0,
            rd_value: 42,
            new_pc: 4,
            delegation_type: 0,
        };
        let divu_opcode = 0x0220d1b3;
        test_mul_div_circuit(divu_opcode, divu_opcode_data);

        let remu_opcode_data = NonMemoryOpcodeTracingData {
            initial_pc: 0,
            rs1_value: 42,
            rs2_value: 1,
            rd_old_value: 0,
            rd_value: 0,
            new_pc: 4,
            delegation_type: 0,
        };
        let remu_opcode = 0x0220f1b3;
        test_mul_div_circuit(remu_opcode, remu_opcode_data);
    }

    #[test]
    fn test_div_non_zero_by_non_zero() {
        let divu_opcode_data = NonMemoryOpcodeTracingData {
            initial_pc: 0,
            rs1_value: 42,
            rs2_value: 10,
            rd_old_value: 0,
            rd_value: 4,
            new_pc: 4,
            delegation_type: 0,
        };
        let divu_opcode = 0x0220d1b3;
        test_mul_div_circuit(divu_opcode, divu_opcode_data);

        let remu_opcode_data = NonMemoryOpcodeTracingData {
            initial_pc: 0,
            rs1_value: 42,
            rs2_value: 10,
            rd_old_value: 0,
            rd_value: 2,
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

    #[test]
    fn test_mul_max() {
        let mul_pcode_data = NonMemoryOpcodeTracingData {
            initial_pc: 0,
            rs1_value: u32::MAX,
            rs2_value: u32::MAX,
            rd_old_value: 0,
            rd_value: u32::MAX,
            new_pc: 4,
            delegation_type: 0,
        };
        let mul_opcode = 0x022081b3;
        test_mul_div_circuit(mul_opcode, mul_pcode_data);

        let mulhu_opcode_data = NonMemoryOpcodeTracingData {
            initial_pc: 0,
            rs1_value: u32::MAX,
            rs2_value: u32::MAX,
            rd_old_value: 0,
            rd_value: (((u32::MAX as u64) * (u32::MAX as u64)) >> 32) as u32,
            new_pc: 4,
            delegation_type: 0,
        };
        let mulhu_opcode = 0x0220b1b3;
        test_mul_div_circuit(mulhu_opcode, mulhu_opcode_data);
    }
}
