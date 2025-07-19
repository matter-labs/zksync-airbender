use cs::cs::oracle::ExecutorFamilyDecoderData;
use cs::cs::oracle::Oracle;
use cs::cs::placeholder::Placeholder;
use cs::definitions::TimestampScalar;
use field::PrimeField;
use risc_v_simulator::machine_mode_only_unrolled::{
    MemoryOpcodeTracingDataWithTimestamp, MEM_LOAD_TRACE_DATA_MARKER, MEM_STORE_TRACE_DATA_MARKER,
};

pub struct MemoryCircuitOracle<'a> {
    pub inner: &'a [MemoryOpcodeTracingDataWithTimestamp],
    pub decoder_table: &'a [ExecutorFamilyDecoderData],
}

impl<'a, F: PrimeField> Oracle<F> for MemoryCircuitOracle<'a> {
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
            // there are few cases of conventional values
            return match placeholder {
                Placeholder::PcInit => 0,
                Placeholder::PcFin => 4,
                _ => 0,
            };
        };
        let decoded =
            <Self as cs::cs::oracle::Oracle<F>>::get_executor_family_data(self, trace_step);

        match placeholder {
            Placeholder::PcInit => cycle_data.initial_pc(),
            Placeholder::PcFin => cycle_data.initial_pc() + 4,

            Placeholder::ShuffleRamReadValue(access_idx) => match access_idx {
                0 => cycle_data.opcode_data.rs1_value,
                1 => cycle_data.rs2_or_ram_read_value(),
                2 => cycle_data.rd_or_ram_read_value(),
                _ => {
                    unreachable!()
                }
            },
            Placeholder::ShuffleRamWriteValue(access_idx) => match access_idx {
                2 => cycle_data.opcode_data.rd_value,
                _ => {
                    unreachable!()
                }
            },
            Placeholder::ShuffleRamAddress(access_idx) => match access_idx {
                1 => {
                    if cycle_data.discr == MEM_LOAD_TRACE_DATA_MARKER {
                        cycle_data.ram_address()
                    } else if cycle_data.discr == MEM_STORE_TRACE_DATA_MARKER {
                        decoded.rs2_index as u32
                    } else {
                        unreachable!()
                    }
                }
                2 => {
                    if cycle_data.discr == MEM_LOAD_TRACE_DATA_MARKER {
                        decoded.rd_index as u32
                    } else if cycle_data.discr == MEM_STORE_TRACE_DATA_MARKER {
                        cycle_data.ram_address()
                    } else {
                        unreachable!()
                    }
                }
                _ => {
                    unreachable!()
                }
            },
            a @ _ => {
                panic!("placeholder {:?} is not supported as u32 query", a);
            }
        }
    }

    fn get_u16_witness_from_placeholder(&self, placeholder: Placeholder, trace_step: usize) -> u16 {
        let Some(_cycle_data) = self.inner.get(trace_step) else {
            return 0;
        };

        match placeholder {
            a @ _ => {
                panic!("placeholder {:?} is not supported as u16 query", a);
            }
        }
    }

    fn get_u8_witness_from_placeholder(&self, placeholder: Placeholder, trace_step: usize) -> u8 {
        let Some(_cycle_data) = self.inner.get(trace_step) else {
            return 0;
        };

        let decoded =
            <Self as cs::cs::oracle::Oracle<F>>::get_executor_family_data(self, trace_step);

        match placeholder {
            Placeholder::ShuffleRamAddress(0) => decoded.rs1_index,
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
                Placeholder::ShuffleRamIsRegisterAccess(1) => false, // padding is LOAD
                Placeholder::ShuffleRamIsRegisterAccess(2) => true,  // padding is LOAD
                _ => false,
            };
        };

        match placeholder {
            Placeholder::ShuffleRamIsRegisterAccess(access_idx) => match access_idx {
                0 => true,
                1 => {
                    if cycle_data.discr == MEM_LOAD_TRACE_DATA_MARKER {
                        false
                    } else if cycle_data.discr == MEM_STORE_TRACE_DATA_MARKER {
                        true
                    } else {
                        unreachable!()
                    }
                }
                2 => {
                    if cycle_data.discr == MEM_LOAD_TRACE_DATA_MARKER {
                        true
                    } else if cycle_data.discr == MEM_STORE_TRACE_DATA_MARKER {
                        false
                    } else {
                        unreachable!()
                    }
                }
                _ => {
                    unreachable!()
                }
            },
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
                0 => cycle_data.rs1_read_timestamp.as_scalar(),
                1 => cycle_data.rs2_or_ram_read_timestamp.as_scalar(),
                2 => cycle_data.rd_or_ram_read_timestamp.as_scalar(),
                _ => {
                    unreachable!()
                }
            },
            Placeholder::OpcodeFamilyCycleInitialTimestamp => {
                cycle_data.cycle_timestamp.as_scalar()
            }
            a @ _ => {
                panic!("placeholder {:?} is not supported as timestamp scalar", a);
            }
        }
    }

    fn get_executor_family_data(&self, trace_step: usize) -> ExecutorFamilyDecoderData {
        let Some(cycle_data) = self.inner.get(trace_step) else {
            return Default::default();
        };
        let pc = cycle_data.opcode_data.initial_pc;
        self.decoder_table[(pc as usize) / 4]
    }
}
