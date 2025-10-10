use cs::cs::oracle::Oracle;
use cs::cs::placeholder::Placeholder;
use cs::definitions::TimestampScalar;
use field::PrimeField;
use riscv_transpiler::witness::delegation::bigint::BigintAbiDescription;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionAbiDescription;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5AbiDescription;
use riscv_transpiler::witness::*;
use common_constants::KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS;

#[derive(Clone, Copy, Debug)]
pub struct DelegationOracle<
    'a,
    D: DelegationAbiDescription,
    const REG_ACCESSES: usize,
    const INDIRECT_READS: usize,
    const INDIRECT_WRITES: usize,
    const VARIABLE_OFFSETS: usize,
> {
    pub cycle_data:
        &'a [DelegationWitness<REG_ACCESSES, INDIRECT_READS, INDIRECT_WRITES, VARIABLE_OFFSETS>],
    pub marker: core::marker::PhantomData<D>,
}

pub type BigintDelegationOracle<'a> = DelegationOracle<'a, BigintAbiDescription, 3, 8, 8, 0>;
pub type Blake2sDelegationOracle<'a> =
    DelegationOracle<'a, Blake2sRoundFunctionAbiDescription, 4, 16, 24, 0>;
pub type KeccakDelegationOracle<'a> = DelegationOracle<'a, KeccakSpecial5AbiDescription, 2, 0, {KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS*2}, KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS>;


impl<
        'a,
        D: DelegationAbiDescription,
        const REG_ACCESSES: usize,
        const INDIRECT_READS: usize,
        const INDIRECT_WRITES: usize,
        const VARIABLE_OFFSETS: usize,
        F: PrimeField,
    > Oracle<F>
    for DelegationOracle<'a, D, REG_ACCESSES, INDIRECT_READS, INDIRECT_WRITES, VARIABLE_OFFSETS>
{
    #[track_caller]
    fn get_witness_from_placeholder(
        &self,
        placeholder: Placeholder,
        _subindex: usize,
        trace_row: usize,
    ) -> F {
        if trace_row >= self.cycle_data.len() {
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
        if trace_row >= self.cycle_data.len() {
            return 0;
        }

        let cycle_data = self.cycle_data[trace_row];
        let base_register_index = D::BASE_REGISTER;

        match placeholder {
            Placeholder::DelegationRegisterReadValue(register_index) => {
                debug_assert!(register_index >= base_register_index);
                let reg_offset = register_index - base_register_index;
                cycle_data.reg_accesses[reg_offset].read_value
            }
            Placeholder::DelegationRegisterWriteValue(register_index) => {
                debug_assert!(register_index >= base_register_index);
                let reg_offset = register_index - base_register_index;
                cycle_data.reg_accesses[reg_offset].write_value
            }
            Placeholder::DelegationIndirectReadValue {
                register_index,
                word_index,
            } => {
                debug_assert!(register_index >= base_register_index);
                if D::use_read_indirects(register_index) {
                    let range = D::INDIRECT_READS_DESCRIPTION[register_index].clone();
                    let pos = range.start + word_index;
                    debug_assert!(pos < range.end);

                    cycle_data.indirect_reads[pos].read_value
                } else {
                    let range = D::INDIRECT_WRITES_DESCRIPTION[register_index].clone();
                    let pos = range.start + word_index;
                    debug_assert!(pos < range.end);

                    cycle_data.indirect_writes[pos].read_value
                }
            }
            Placeholder::DelegationIndirectWriteValue {
                register_index,
                word_index,
            } => {
                debug_assert!(register_index >= base_register_index);
                if D::use_read_indirects(register_index) {
                    panic!("indirect is readonly");
                } else {
                    let range = D::INDIRECT_WRITES_DESCRIPTION[register_index].clone();
                    let pos = range.start + word_index;
                    debug_assert!(pos < range.end);

                    cycle_data.indirect_writes[pos].write_value
                }
            }
            a @ _ => {
                panic!("Placeholder query {:?} is not supported as u32", a);
            }
        }
    }

    fn get_u16_witness_from_placeholder(&self, placeholder: Placeholder, trace_row: usize) -> u16 {
        if trace_row >= self.cycle_data.len() {
            return 0;
        }

        match placeholder {
            Placeholder::DelegationABIOffset => 0,
            Placeholder::DelegationType => D::DELEGATION_TYPE,
            Placeholder::DelegationIndirectAccessVariableOffset { variable_index } => {
                D::VARIABLE_OFFSETS_DESCRIPTION[variable_index]
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
        if trace_row >= self.cycle_data.len() {
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
        if trace_row >= self.cycle_data.len() {
            return 0;
        }

        let cycle_data = self.cycle_data[trace_row];
        let base_register_index = D::BASE_REGISTER;

        match placeholder {
            Placeholder::DelegationWriteTimestamp => {
                let timestamp = cycle_data.write_timestamp;
                debug_assert_eq!(timestamp % 4, 3);

                timestamp
            }
            Placeholder::DelegationRegisterReadTimestamp(register_index) => {
                debug_assert!(register_index >= base_register_index);
                let reg_offset = register_index - base_register_index;
                cycle_data.reg_accesses[reg_offset].timestamp.as_scalar()
            }
            Placeholder::DelegationIndirectReadTimestamp {
                register_index,
                word_index,
            } => {
                debug_assert!(register_index >= base_register_index);
                if D::use_read_indirects(register_index) {
                    let range = D::INDIRECT_READS_DESCRIPTION[register_index].clone();
                    let pos = range.start + word_index;
                    debug_assert!(pos < range.end);

                    cycle_data.indirect_reads[pos].timestamp.as_scalar()
                } else {
                    let range = D::INDIRECT_WRITES_DESCRIPTION[register_index].clone();
                    let pos = range.start + word_index;
                    debug_assert!(pos < range.end);

                    cycle_data.indirect_writes[pos].timestamp.as_scalar()
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
