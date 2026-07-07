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

    #[test]
    fn test_mulhu() {
        let opcode_data = NonMemoryOpcodeTracingData {
            initial_pc: 0,
            rs1_value: 0,
            rs2_value: 281475,
            rd_old_value: 0,
            rd_value: 0,
            new_pc: 4,
            delegation_type: 0,
        };
        let opcode = 0x0220b1b3;
        test_mul_div_circuit(opcode, opcode_data);
    }

    #[test]
    fn test_on_external_witness() {
        use std::path::Path;

        fn bincode_deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
            let src = std::fs::File::open(filename).unwrap();
            bincode::deserialize_from(src).unwrap()
        }

        fn read_binary(path: &Path) -> (Vec<u8>, Vec<u32>) {
            use std::io::Read;
            let mut file = std::fs::File::open(path).expect("must open provided file");
            let mut buffer = vec![];
            file.read_to_end(&mut buffer).expect("must read the file");
            assert_eq!(buffer.len() % core::mem::size_of::<u32>(), 0);
            let mut binary = Vec::with_capacity(buffer.len() / core::mem::size_of::<u32>());
            for el in buffer.as_chunks::<4>().0 {
                binary.push(u32::from_le_bytes(*el));
            }

            (buffer, binary)
        }

        let witness: Vec<NonMemoryOpcodeTracingDataWithTimestamp> = bincode_deserialize_from_file(
            "../circuit_defs/prover_examples/family_4_circuit_0_oracle_witness.bin",
        );
        println!("{} inputs in total", witness.len());
        let (_, binary) = read_binary(&Path::new(
            "../riscv_transpiler/examples/zksync_os/app.text",
        ));
        for (i, wit) in witness.into_iter().enumerate() {
            if i % 100 == 0 {
                println!("{}", i);
            }
            let pc = wit.opcode_data.initial_pc;
            let opcode = binary[(pc / 4) as usize];
            // remap witness
            let mut opcode_data = wit.opcode_data;
            opcode_data.initial_pc = 0;
            opcode_data.new_pc = 4;
            test_mul_div_circuit(opcode, opcode_data);
        }
    }
}
