use super::*;

#[cfg(test)]
mod test {
    use super::*;
    use cs::gkr_circuits::unified_reduced_machine::UnifiedReducedMachineDecoder;
    use cs::gkr_circuits::unified_reduced_machine::*;
    use field::baby_bear::base::BabyBearField;
    use field::Proth120;
    use riscv_transpiler::ir::ReducedMachineDecoderConfig;

    type F = BabyBearField;

    fn test_unified_circuit_circuit<F: PrimeField>(
        opcode_data: UnifiedOpcodeTracingDataWithTimestamp,
        binary: &[u32],
    ) {
        test_single_unified_cycle::<F, ReducedMachineDecoderConfig>(
            UnifiedReducedMachineDecoder,
            opcode_data,
            binary,
            |cs| {
                unified_reduced_machine_table_addition_fn::<F, _>(cs);
                for (table_type, table) in
                    cs::gkr_circuits::mem_word_only::create_mem_word_only_special_tables::<
                        F,
                        { common_constants::ROM_SECOND_WORD_BITS },
                    >(binary)
                {
                    cs.add_table_with_content(table_type, table);
                }
            },
            |cs| {
                unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr::<F, _>(cs);
            },
        )
    }

    #[test]
    fn test_unified_proth120_on_external_witness() {
        use crate::tests::gkr::bincode_deserialize_from_file;
        use std::path::Path;

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

        let witness: Vec<UnifiedOpcodeTracingDataWithTimestamp> =
            bincode_deserialize_from_file("unified_proth120_witness.bin");
        println!("{} inputs in total", witness.len());
        let (_, binary) = read_binary(&Path::new("../examples/basic_fibonacci/app.bin"));

        for (i, wit) in witness.into_iter().enumerate().skip(10) {
            let pc = wit.initial_pc();
            println!("Opcode = 0x{:08x}", binary[(pc as usize) / 4]);
            println!("{}", i);
            if let UnifiedOpcodeTracingDataWithTimestamp::Mem(wit) = wit {
                if wit.discr == MEM_LOAD_TRACE_DATA_MARKER {
                    dbg!(wit.as_load_data());
                } else {
                    dbg!(wit.as_store_data());
                }
            }
            dbg!(&wit);
            test_unified_circuit_circuit::<BabyBearField>(wit, &binary);
        }
    }
}
