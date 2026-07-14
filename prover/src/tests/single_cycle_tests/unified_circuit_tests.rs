use super::*;

#[cfg(test)]
mod test {
    use super::*;
    use ::cs::oracle::Placeholder;
    use cs::gkr_circuits::unified_reduced_machine::UnifiedReducedMachineDecoder;
    use cs::gkr_circuits::unified_reduced_machine::*;
    use field::baby_bear::base::BabyBearField;
    use field::Proth120;
    use riscv_transpiler::ir::ReducedMachineDecoderConfig;

    type F = BabyBearField;

    fn read_binary(path: &std::path::Path) -> (Vec<u8>, Vec<u32>) {
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

    /// Oracle wrapper that poisons every `ShuffleRamWriteValue` query.
    ///
    /// The `ASSUME_MEMORY_VALUES_ASSIGNED == false` regime has a
    /// self-generating witness contract: the oracle is only trusted for
    /// INPUTS (instruction, register/memory READ values, timestamps); every
    /// family must DERIVE its outputs (the shared rd/mem write-value columns)
    /// in-circuit, gated on its own activity mask. If any family silently
    /// falls back to the oracle for its write value, this wrapper feeds it
    /// garbage and the per-family rd-write constraints reject the row.
    struct PoisonedWriteValueOracle<O>(O);

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

        fn get_u32_witness_from_placeholder(
            &self,
            placeholder: Placeholder,
            trace_row: usize,
        ) -> u32 {
            if matches!(placeholder, Placeholder::ShuffleRamWriteValue(_)) {
                return 0xDEAD_BEEF;
            }
            self.0
                .get_u32_witness_from_placeholder(placeholder, trace_row)
        }

        fn get_u16_witness_from_placeholder(
            &self,
            placeholder: Placeholder,
            trace_row: usize,
        ) -> u16 {
            if matches!(placeholder, Placeholder::ShuffleRamWriteValue(_)) {
                return 0xBEEF;
            }
            self.0
                .get_u16_witness_from_placeholder(placeholder, trace_row)
        }

        fn get_u8_witness_from_placeholder(
            &self,
            placeholder: Placeholder,
            trace_row: usize,
        ) -> u8 {
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

    #[test]
    fn test_unified_witness_self_generates_write_values() {
        use crate::tests::gkr::bincode_deserialize_from_file;
        use std::path::Path;

        let witness: Vec<UnifiedOpcodeTracingDataWithTimestamp> =
            bincode_deserialize_from_file("unified_proth120_witness.bin");
        let (_, binary) = read_binary(Path::new("../examples/basic_fibonacci/app.bin"));

        for (i, wit) in witness.into_iter().enumerate().skip(10) {
            println!("cycle {}", i);
            test_single_unified_cycle_with_oracle::<BabyBearField, ReducedMachineDecoderConfig, _>(
                UnifiedReducedMachineDecoder,
                wit,
                &binary,
                |cs| {
                    unified_reduced_machine_table_addition_fn::<BabyBearField, _>(cs);
                    for (table_type, table) in
                        cs::gkr_circuits::mem_word_only::create_mem_word_only_special_tables::<
                            BabyBearField,
                            { common_constants::ROM_SECOND_WORD_BITS },
                        >(&binary)
                    {
                        cs.add_table_with_content(table_type, table);
                    }
                },
                |cs| {
                    unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr::<
                        BabyBearField,
                        _,
                    >(cs);
                },
                PoisonedWriteValueOracle,
            );
        }
    }

    #[test]
    fn test_unified_proth120_on_external_witness() {
        use crate::tests::gkr::bincode_deserialize_from_file;
        use std::path::Path;

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
