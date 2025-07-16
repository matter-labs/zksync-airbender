use cs::cs::oracle::ExecutorFamilyDecoderData;
use cs::cs::placeholder::Placeholder;
use cs::definitions::TimestampScalar;
use cs::{cs::oracle::Oracle, machine::NON_DETERMINISM_CSR};
use field::PrimeField;
use risc_v_simulator::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;

pub struct NonMemoryCircuitOracle<'a> {
    pub inner: &'a [NonMemoryOpcodeTracingDataWithTimestamp],
    pub decoder_table: &'a [ExecutorFamilyDecoderData],
    pub default_pc_value_in_padding: u32,
}

impl<'a, F: PrimeField> Oracle<F> for NonMemoryCircuitOracle<'a> {
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
                Placeholder::PcFin => self.default_pc_value_in_padding,
                _ => 0,
            };
        };

        match placeholder {
            Placeholder::PcInit => cycle_data.opcode_data.initial_pc,
            Placeholder::PcFin => cycle_data.opcode_data.new_pc,

            Placeholder::ShuffleRamReadValue(access_idx) => match access_idx {
                0 => cycle_data.opcode_data.rs1_value,
                1 => cycle_data.opcode_data.rs2_value,
                2 => cycle_data.opcode_data.rd_old_value,
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
            Placeholder::ExternalOracle => {
                if cycle_data.opcode_data.delegation_type == NON_DETERMINISM_CSR {
                    cycle_data.opcode_data.rd_value
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

        match placeholder {
            Placeholder::DelegationType => cycle_data.opcode_data.delegation_type,
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

        let decoded =
            <Self as cs::cs::oracle::Oracle<F>>::get_executor_family_data(self, trace_step);

        match placeholder {
            Placeholder::ShuffleRamAddress(access_idx) => match access_idx {
                0 => decoded.rs1_index,
                1 => decoded.rs2_index,
                2 => decoded.rd_index,
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
            return false;
        };

        match placeholder {
            Placeholder::ShuffleRamIsRegisterAccess(access_idx) => match access_idx {
                0 => true,
                1 => true,
                2 => true,
                _ => {
                    unreachable!()
                }
            },

            Placeholder::ExecuteDelegation => {
                // NOTE: we use single field here to indicate both non-determinism
                // CSR and delegation csrs, so we compare vs 0 and non-determinism CSR index
                let delegation_type = cycle_data.opcode_data.delegation_type;
                delegation_type != 0 && delegation_type != NON_DETERMINISM_CSR
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
                0 => cycle_data.rs1_read_timestamp.as_scalar(),
                1 => cycle_data.rs2_read_timestamp.as_scalar(),
                2 => cycle_data.rd_read_timestamp.as_scalar(),
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
