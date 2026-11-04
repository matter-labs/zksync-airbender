use crate::tracers::delegation::DelegationWitness;
use cs::cs::oracle::Oracle;
use cs::cs::placeholder::Placeholder;
use cs::definitions::TimestampScalar;
use fft::GoodAllocator;
use field::PrimeField;
use std::alloc::Global;

#[derive(Clone, Copy, Debug)]
pub struct DelegationCircuitOracle<'a, A: GoodAllocator = Global> {
    pub cycle_data: &'a DelegationWitness<A>,
}

impl<'a, A: GoodAllocator, F: PrimeField> Oracle<F> for DelegationCircuitOracle<'a, A> {
    #[track_caller]
    fn get_witness_from_placeholder(
        &self,
        placeholder: Placeholder,
        _subindex: usize,
        trace_step: usize,
    ) -> F {
        if trace_step >= self.cycle_data.write_timestamp.len() {
            return F::ZERO;
        }

        match placeholder {
            Placeholder::DelegationNondeterminismAccess(_access_idx) => {
                unimplemented!("not used by any circuit yet");
            }
            Placeholder::DelegationNondeterminismAccessNoSplits(_access_idx) => {
                unimplemented!("not used by any circuit yet");
            }
            a @ _ => {
                panic!("Placeholder query {:?} is not supported as field", a);
            }
        }
    }

    fn get_u32_witness_from_placeholder(&self, placeholder: Placeholder, trace_row: usize) -> u32 {
        if trace_row >= self.cycle_data.write_timestamp.len() {
            return 0;
        }

        let base_register_index = self.cycle_data.base_register_index as usize;

        match placeholder {
            Placeholder::DelegationRegisterReadValue(register_index) => {
                debug_assert!(register_index >= base_register_index);
                let reg_offset = register_index - base_register_index;
                let offset =
                    trace_row * self.cycle_data.num_register_accesses_per_delegation + reg_offset;

                self.cycle_data.register_accesses[offset].read_value
            }
            Placeholder::DelegationRegisterWriteValue(register_index) => {
                debug_assert!(register_index >= base_register_index);
                let reg_offset = register_index - base_register_index;
                let offset =
                    trace_row * self.cycle_data.num_register_accesses_per_delegation + reg_offset;

                self.cycle_data.register_accesses[offset].write_value
            }
            Placeholder::DelegationIndirectReadValue {
                register_index,
                word_index,
            } => {
                debug_assert!(register_index >= base_register_index);
                let reg_offset = register_index - base_register_index;
                let access = self.cycle_data.indirect_accesses_properties[reg_offset][word_index];

                let t = if access.use_writes {
                    self.cycle_data.num_indirect_writes_per_delegation
                } else {
                    self.cycle_data.num_indirect_reads_per_delegation
                };
                let offset = trace_row * t + access.index;

                if access.use_writes {
                    self.cycle_data.indirect_writes[offset].read_value
                } else {
                    self.cycle_data.indirect_reads[offset].read_value
                }
            }
            Placeholder::DelegationIndirectWriteValue {
                register_index,
                word_index,
            } => {
                debug_assert!(register_index >= base_register_index);
                let reg_offset = register_index - base_register_index;
                let access = self.cycle_data.indirect_accesses_properties[reg_offset][word_index];

                assert!(access.use_writes, "indirect is readonly");

                let offset =
                    trace_row * self.cycle_data.num_indirect_writes_per_delegation + access.index;

                self.cycle_data.indirect_writes[offset].write_value
            }
            a @ _ => {
                panic!("Placeholder query {:?} is not supported as u32", a);
            }
        }
    }

    fn get_u16_witness_from_placeholder(&self, placeholder: Placeholder, trace_row: usize) -> u16 {
        if trace_row >= self.cycle_data.write_timestamp.len() {
            return 0;
        }
        match placeholder {
            Placeholder::DelegationABIOffset => 0,
            Placeholder::DelegationType => self.cycle_data.delegation_type,
            Placeholder::DelegationIndirectAccessVariableOffset { variable_index } => {
                self.cycle_data.indirect_offset_variables[trace_row
                    * self
                        .cycle_data
                        .num_indirect_access_variable_offsets_per_delegation
                    + variable_index]
                    .variable_offset_value
            }
            a @ _ => {
                panic!("Placeholder query {:?} is not supported as u16", a);
            }
        }
    }

    fn get_u8_witness_from_placeholder(&self, _placeholder: Placeholder, _trace_row: usize) -> u8 {
        unimplemented!("not yet used by any circuit");
    }

    fn get_boolean_witness_from_placeholder(
        &self,
        placeholder: Placeholder,
        trace_row: usize,
    ) -> bool {
        if trace_row >= self.cycle_data.write_timestamp.len() {
            return false;
        }
        match placeholder {
            Placeholder::ExecuteDelegation => true,
            a @ _ => {
                panic!("Placeholder query {:?} is not supported as boolean", a);
            }
        }
    }

    fn get_timestamp_witness_from_placeholder(
        &self,
        placeholder: Placeholder,
        trace_row: usize,
    ) -> TimestampScalar {
        if trace_row >= self.cycle_data.write_timestamp.len() {
            return 0;
        }

        let base_register_index = self.cycle_data.base_register_index as usize;

        match placeholder {
            Placeholder::DelegationWriteTimestamp => {
                let timestamp = self.cycle_data.write_timestamp[trace_row].as_scalar();
                debug_assert_eq!(timestamp % 4, 3);

                timestamp
            }
            Placeholder::DelegationRegisterReadTimestamp(register_index) => {
                debug_assert!(register_index >= base_register_index);
                let reg_offset = register_index - base_register_index;
                let offset =
                    trace_row * self.cycle_data.num_register_accesses_per_delegation + reg_offset;

                self.cycle_data.register_accesses[offset]
                    .timestamp
                    .as_scalar()
            }
            Placeholder::DelegationIndirectReadTimestamp {
                register_index,
                word_index,
            } => {
                debug_assert!(register_index >= base_register_index);
                let reg_offset = register_index - base_register_index;
                let access = self.cycle_data.indirect_accesses_properties[reg_offset][word_index];

                let t = if access.use_writes {
                    self.cycle_data.num_indirect_writes_per_delegation
                } else {
                    self.cycle_data.num_indirect_reads_per_delegation
                };
                let offset = trace_row * t + access.index;

                if access.use_writes {
                    self.cycle_data.indirect_writes[offset]
                        .timestamp
                        .as_scalar()
                } else {
                    self.cycle_data.indirect_reads[offset].timestamp.as_scalar()
                }
            }
            a @ _ => {
                panic!(
                    "Placeholder query {:?} is not supported as timestamp scalar",
                    a
                );
            }
        }
    }
}
