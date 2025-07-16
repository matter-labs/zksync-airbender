use crate::tracers::main_cycle_optimized::CycleData;
use cs::cs::oracle::Oracle;
use cs::cs::placeholder::Placeholder;
use cs::definitions::TimestampScalar;
use fft::GoodAllocator;
use field::PrimeField;
use risc_v_simulator::cycle::MachineConfig;
use std::alloc::Global;

#[derive(Clone, Copy, Debug)]
pub struct MainRiscVOracle<'a, C: MachineConfig, A: GoodAllocator = Global> {
    pub cycle_data: &'a CycleData<C, A>,
}

impl<'a, C: MachineConfig, A: GoodAllocator, F: PrimeField> Oracle<F>
    for MainRiscVOracle<'a, C, A>
{
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
        let cycle_data = &self.cycle_data.per_cycle_data[trace_step];

        match placeholder {
            Placeholder::PcInit => cycle_data.pc,
            Placeholder::FirstRegMem => cycle_data.rs1_read_value,
            Placeholder::SecondRegMem => cycle_data.rs2_or_mem_word_read_value,
            Placeholder::WriteRdReadSetWitness => cycle_data.rd_or_mem_word_read_value,

            Placeholder::MemSlot => {
                // decide whether we did store or load
                let rs2_or_mem_address = cycle_data.rs2_or_mem_word_address;
                let rd_or_mem_address = cycle_data.rd_or_mem_word_address;
                if rs2_or_mem_address.is_register() == false && rd_or_mem_address.is_register() {
                    // it is LOAD
                    // In this case we return from rs2 or mem
                    cycle_data.rs2_or_mem_word_read_value
                } else if rs2_or_mem_address.is_register()
                    && rd_or_mem_address.is_register() == false
                {
                    // it is STORE
                    // In this case we return from rd or mem
                    cycle_data.rd_or_mem_word_read_value
                } else {
                    0
                }
            }

            Placeholder::ShuffleRamAddress(access_idx) => match access_idx {
                1 => cycle_data.rs2_or_mem_word_address.as_u32_formal_address(),
                2 => cycle_data.rd_or_mem_word_address.as_u32_formal_address(),
                _ => {
                    unreachable!()
                }
            },
            // Placeholder::ShuffleRamReadTimestamp(access_idx) => match access_idx {
            //     0 => self.cycle_data.rs1_read_timestamp[trace_step].as_scalar(),
            //     1 => self.cycle_data.rs2_or_mem_read_timestamp[trace_step].as_scalar(),
            //     2 => self.cycle_data.rd_or_mem_read_timestamp[trace_step].as_scalar(),
            //     _ => {
            //         unreachable!()
            //     }
            // },
            Placeholder::ShuffleRamReadValue(access_idx) => match access_idx {
                0 => cycle_data.rs1_read_value,
                1 => cycle_data.rs2_or_mem_word_read_value,
                2 => cycle_data.rd_or_mem_word_read_value,
                _ => {
                    unreachable!()
                }
            },

            Placeholder::ShuffleRamWriteValue(access_idx) => match access_idx {
                0 => cycle_data.rs1_read_value,
                1 => cycle_data.rs2_or_mem_word_read_value,
                2 => cycle_data.rd_or_mem_word_write_value,
                _ => {
                    unreachable!()
                }
            },
            Placeholder::ExternalOracle => cycle_data.non_determinism_read,
            a @ _ => {
                panic!("placeholder {:?} is not supported as u32 query", a);
            }
        }
    }

    fn get_u16_witness_from_placeholder(&self, placeholder: Placeholder, trace_step: usize) -> u16 {
        let cycle_data = &self.cycle_data.per_cycle_data[trace_step];

        match placeholder {
            Placeholder::DelegationABIOffset => 0,
            Placeholder::DelegationType => cycle_data.delegation_request,

            Placeholder::ShuffleRamAddress(access_idx) => match access_idx {
                0 => cycle_data.rs1_reg_idx as u16,
                1 => cycle_data.rs2_or_mem_word_address.as_u32_formal_address() as u16,
                2 => cycle_data.rd_or_mem_word_address.as_u32_formal_address() as u16,
                _ => {
                    unreachable!()
                }
            },
            Placeholder::ExecuteDelegation => (cycle_data.delegation_request != 0) as u16,
            a @ _ => {
                panic!("placeholder {:?} is not supported as u16 query", a);
            }
        }
    }

    fn get_u8_witness_from_placeholder(&self, placeholder: Placeholder, _trace_row: usize) -> u8 {
        panic!("placeholder {:?} is not supported as u8 query", placeholder);
    }

    fn get_boolean_witness_from_placeholder(
        &self,
        placeholder: Placeholder,
        trace_step: usize,
    ) -> bool {
        let cycle_data = &self.cycle_data.per_cycle_data[trace_step];

        match placeholder {
            Placeholder::ShuffleRamIsRegisterAccess(access_idx) => match access_idx {
                0 => true,
                1 => cycle_data.rs2_or_mem_word_address.is_register(),
                2 => cycle_data.rd_or_mem_word_address.is_register(),
                _ => {
                    unreachable!()
                }
            },

            Placeholder::ExecuteDelegation => cycle_data.delegation_request != 0,

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
        let cycle_data = &self.cycle_data.per_cycle_data[trace_step];

        match placeholder {
            Placeholder::ShuffleRamReadTimestamp(access_idx) => match access_idx {
                0 => cycle_data.rs1_read_timestamp.as_scalar(),
                1 => cycle_data.rs2_or_mem_read_timestamp.as_scalar(),
                2 => cycle_data.rd_or_mem_read_timestamp.as_scalar(),
                _ => {
                    unreachable!()
                }
            },
            a @ _ => {
                panic!("placeholder {:?} is not supported as timestamp scalar", a);
            }
        }
    }
}
