use common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
use common_constants::NON_DETERMINISM_CSR;
use cs::definitions::TimestampScalar;
use cs::gkr_circuits::unified_reduced_machine::UnifiedReducedMachineDecoder;
use cs::gkr_circuits::{
    process_binary_into_separate_tables_ext, ExecutorFamilyDecoderData, OpcodeFamilyDecoder,
};
use cs::oracle::*;
use field::PrimeField;
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
use riscv_transpiler::witness::data_structs::{
    UnifiedOpcodeTracingDataWithTimestamp, MEM_LOAD_TRACE_DATA_MARKER,
};
use std::alloc::Global;

pub struct UnifiedRiscvCircuitOracle<'a> {
    pub(crate) inner: &'a [UnifiedOpcodeTracingDataWithTimestamp],
    decoder_table_with_options: Vec<Option<ExecutorFamilyDecoderData>>,
    decoder_table: Vec<ExecutorFamilyDecoderData>,
}

impl<'a> UnifiedRiscvCircuitOracle<'a> {
    pub fn new<F: PrimeField>(
        inner: &'a [UnifiedOpcodeTracingDataWithTimestamp],
        text_section: &[u32],
        bytecode_size_words: usize,
    ) -> Self {
        let decoders: Vec<Box<dyn OpcodeFamilyDecoder>> =
            vec![Box::new(UnifiedReducedMachineDecoder)];
        let mut preprocessing_data = process_binary_into_separate_tables_ext::<
            F,
            FullUnsignedMachineDecoderConfig,
            true,
            Global,
        >(text_section, &decoders, bytecode_size_words, &[]);
        let decoder_table_with_options = preprocessing_data
            .remove(&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX)
            .expect("UnifiedReducedMachineDecoder must produce a family-128 entry");
        let decoder_table = decoder_table_with_options
            .iter()
            .map(|el| el.unwrap_or_default())
            .collect();
        Self {
            inner,
            decoder_table_with_options,
            decoder_table,
        }
    }

    pub fn decoder_table_with_options(&self) -> &[Option<ExecutorFamilyDecoderData>] {
        &self.decoder_table_with_options
    }
}

impl<'a, F: PrimeField> Oracle<F> for UnifiedRiscvCircuitOracle<'a> {
    #[track_caller]
    fn get_witness_from_placeholder(
        &self,
        placeholder: Placeholder,
        _subindex: usize,
        _trace_step: usize,
    ) -> F {
        panic!(
            "placeholder {:?} is not supported as field query",
            placeholder
        );
    }

    fn get_u32_witness_from_placeholder(&self, placeholder: Placeholder, trace_step: usize) -> u32 {
        let Some(cycle_data) = self.inner.get(trace_step) else {
            return match placeholder {
                Placeholder::PcInit
                | Placeholder::PcFin
                | Placeholder::ShuffleRamAddress(_)
                | Placeholder::ShuffleRamReadValue(_)
                | Placeholder::ShuffleRamWriteValue(_)
                | Placeholder::ExternalOracle => 0,
                a => panic!(
                    "padding-row u32 query: placeholder {:?} has no defined default \
                     (trace_step={trace_step} >= inner.len()={})",
                    a,
                    self.inner.len()
                ),
            };
        };

        let decoded = <Self as cs::oracle::Oracle<F>>::get_executor_family_data(self, trace_step);

        match placeholder {
            Placeholder::PcInit => cycle_data.initial_pc(),
            Placeholder::PcFin => cycle_data.final_pc(),

            Placeholder::ShuffleRamAddress(access_idx) => match access_idx {
                1 => match cycle_data {
                    UnifiedOpcodeTracingDataWithTimestamp::NonMem(..) => decoded.rs2_index as u32,
                    UnifiedOpcodeTracingDataWithTimestamp::Mem(inner) => {
                        if inner.discr == MEM_LOAD_TRACE_DATA_MARKER {
                            inner.as_load_data().aligned_ram_address
                        } else {
                            decoded.rs2_index as u32
                        }
                    }
                },
                2 => match cycle_data {
                    UnifiedOpcodeTracingDataWithTimestamp::NonMem(..) => decoded.rd_index as u32,
                    UnifiedOpcodeTracingDataWithTimestamp::Mem(inner) => {
                        if inner.discr == MEM_LOAD_TRACE_DATA_MARKER {
                            decoded.rd_index as u32
                        } else {
                            inner.as_store_data().aligned_ram_address
                        }
                    }
                },
                _ => {
                    unreachable!()
                }
            },

            Placeholder::ShuffleRamReadValue(access_idx) => match access_idx {
                0 => cycle_data.rs1_read_value(),
                1 => cycle_data.rs2_or_mem_load_read_value(),
                2 => cycle_data.rd_or_mem_store_read_value(),
                _ => {
                    unreachable!()
                }
            },
            Placeholder::ShuffleRamWriteValue(access_idx) => match access_idx {
                2 => cycle_data.rd_or_mem_store_write_value(),
                _ => {
                    unreachable!()
                }
            },
            Placeholder::ExternalOracle => {
                if cycle_data.delegation_type() == (NON_DETERMINISM_CSR as u16) {
                    cycle_data.rd_or_mem_store_write_value()
                } else {
                    0
                }
            }
            a @ _ => {
                panic!("placeholder {:?} is not supported as u32 query", a);
            }
        }
    }

    fn get_u16_witness_from_placeholder(&self, placeholder: Placeholder, trace_step: usize) -> u16 {
        let Some(cycle_data) = self.inner.get(trace_step) else {
            return 0;
        };

        let decoded = <Self as cs::oracle::Oracle<F>>::get_executor_family_data(self, trace_step);

        match placeholder {
            // rs1/rs2/rd register-index queries. For Mem-LOAD access 1 (RAM address)
            // and Mem-STORE access 2 (RAM address) the witness eval queries u32 instead.
            Placeholder::ShuffleRamAddress(access_idx) => match access_idx {
                0 => decoded.rs1_index as u16,
                1 => match cycle_data {
                    UnifiedOpcodeTracingDataWithTimestamp::NonMem(..) => decoded.rs2_index,
                    UnifiedOpcodeTracingDataWithTimestamp::Mem(inner) => {
                        if inner.discr == MEM_LOAD_TRACE_DATA_MARKER {
                            unreachable!("load: access 1 is a RAM address, must be queried as u32")
                        } else {
                            decoded.rs2_index
                        }
                    }
                },
                2 => match cycle_data {
                    UnifiedOpcodeTracingDataWithTimestamp::NonMem(..) => decoded.rd_index as u16,
                    UnifiedOpcodeTracingDataWithTimestamp::Mem(inner) => {
                        if inner.discr == MEM_LOAD_TRACE_DATA_MARKER {
                            decoded.rd_index as u16
                        } else {
                            unreachable!("store: access 2 is a RAM address, must be queried as u32")
                        }
                    }
                },
                _ => unreachable!(),
            },
            Placeholder::DelegationType => {
                match cycle_data {
                    UnifiedOpcodeTracingDataWithTimestamp::Mem(..) => 0,
                    UnifiedOpcodeTracingDataWithTimestamp::NonMem(inner) => {
                        if inner.opcode_data.delegation_type != 0
                            && inner.opcode_data.delegation_type != (NON_DETERMINISM_CSR as u16)
                        {
                            inner.opcode_data.delegation_type
                        } else {
                            // It's just a convention - if we do not use delegation, then we put 0 into corresponding column
                            0
                        }
                    }
                }
            }
            Placeholder::DelegationABIOffset => 0, // we do not use it anymore

            a @ _ => {
                panic!("placeholder {:?} is not supported as u16 query", a);
            }
        }
    }

    fn get_u8_witness_from_placeholder(&self, placeholder: Placeholder, trace_step: usize) -> u8 {
        let Some(_cycle_data) = self.inner.get(trace_step) else {
            return 0;
        };

        let decoded = <Self as cs::oracle::Oracle<F>>::get_executor_family_data(self, trace_step);

        match placeholder {
            Placeholder::ShuffleRamAddress(access_idx) => match access_idx {
                0 => decoded.rs1_index,
                _ => {
                    unreachable!()
                }
            },
            a @ _ => {
                panic!("placeholder {:?} is not supported as u8 query", a);
            }
        }
    }

    fn get_boolean_witness_from_placeholder(
        &self,
        placeholder: Placeholder,
        trace_step: usize,
    ) -> bool {
        let Some(cycle_data) = self.inner.get(trace_step) else {
            return match placeholder {
                Placeholder::ShuffleRamIsRegisterAccess(access_idx) => match access_idx {
                    0 => true,
                    1 => true,
                    2 => true,
                    _ => {
                        unreachable!()
                    }
                },
                _ => false,
            };
        };

        match placeholder {
            Placeholder::ShuffleRamIsRegisterAccess(access_idx) => match access_idx {
                0 => true,
                1 => cycle_data.rs2_is_reg(),
                2 => cycle_data.rd_is_reg(),
                _ => {
                    unreachable!()
                }
            },

            Placeholder::ExecuteDelegation => {
                // NOTE: we use single field here to indicate both non-determinism
                // CSR and delegation csrs, so we compare vs 0 and non-determinism CSR index
                let delegation_type = cycle_data.delegation_type();
                delegation_type != 0 && delegation_type != (NON_DETERMINISM_CSR as u16)
            }
            Placeholder::ExecuteOpcodeFamilyCycle => true,

            a @ _ => {
                panic!("placeholder {:?} is not supported as boolean query", a);
            }
        }
    }

    fn get_timestamp_witness_from_placeholder(
        &self,
        placeholder: Placeholder,
        trace_step: usize,
    ) -> TimestampScalar {
        let Some(cycle_data) = self.inner.get(trace_step) else {
            if placeholder == Placeholder::OpcodeFamilyCycleInitialTimestamp {
                use cs::definitions::MAX_INITIAL_TIMESTAMP;
                return MAX_INITIAL_TIMESTAMP;
            } else {
                return 0;
            };
        };

        match placeholder {
            Placeholder::ShuffleRamReadTimestamp(access_idx) => match access_idx {
                0 => cycle_data.rs1_read_timestamp(),
                1 => cycle_data.rs2_or_mem_load_read_timestamp(),
                2 => cycle_data.rd_or_mem_store_read_timestamp(),
                _ => {
                    unreachable!()
                }
            },
            Placeholder::OpcodeFamilyCycleInitialTimestamp => cycle_data.cycle_timestamp(),
            a @ _ => {
                panic!("placeholder {:?} is not supported as timestamp scalar", a);
            }
        }
    }

    fn get_executor_family_data(&self, trace_step: usize) -> ExecutorFamilyDecoderData {
        let Some(cycle_data) = self.inner.get(trace_step) else {
            return Default::default();
        };
        let pc = cycle_data.initial_pc();
        let idx = (pc as usize) / 4;
        assert!(
            idx < self.decoder_table.len(),
            "PC 0x{:08x} out of decoder table bounds (len={})",
            pc,
            self.decoder_table.len()
        );
        self.decoder_table[idx]
    }
}
