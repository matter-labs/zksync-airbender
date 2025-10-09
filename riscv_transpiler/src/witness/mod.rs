pub mod delegation;

pub use self::delegation::{DelegationAbiDescription, DelegationWitness};
use risc_v_simulator::machine_mode_only_unrolled::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
};

pub trait WitnessTracer {
    fn write_non_memory_family_data<const FAMILY: u8>(
        &mut self,
        data: NonMemoryOpcodeTracingDataWithTimestamp,
    );
    fn write_memory_family_data<const FAMILY: u8>(
        &mut self,
        data: MemoryOpcodeTracingDataWithTimestamp,
    );
    fn write_delegation<
        const DELEGATION_TYPE: u16,
        const REG_ACCESSES: usize,
        const INDIRECT_READS: usize,
        const INDIRECT_WRITES: usize,
        const VARIABLE_OFFSETS: usize,
    >(
        &mut self,
        data: DelegationWitness<REG_ACCESSES, INDIRECT_READS, INDIRECT_WRITES, VARIABLE_OFFSETS>,
    );
}

// this is largely an example, but is fine for all CPU purposes

// Holder for destination buffer for one particular delegation type. It may represent only part
// of the destination circuit's capacity
pub struct DelegationDestinationHolder<
    'a,
    const DELEGATION_TYPE: u16,
    const REG_ACCESSES: usize,
    const INDIRECT_READS: usize,
    const INDIRECT_WRITES: usize,
    const VARIABLE_OFFSETS: usize,
> {
    pub buffers: &'a mut [&'a mut [DelegationWitness<
        REG_ACCESSES,
        INDIRECT_READS,
        INDIRECT_WRITES,
        VARIABLE_OFFSETS,
    >]],
}

impl<
        'a,
        const DELEGATION_TYPE: u16,
        const REG_ACCESSES: usize,
        const INDIRECT_READS: usize,
        const INDIRECT_WRITES: usize,
        const VARIABLE_OFFSETS: usize,
    > WitnessTracer
    for DelegationDestinationHolder<
        'a,
        DELEGATION_TYPE,
        REG_ACCESSES,
        INDIRECT_READS,
        INDIRECT_WRITES,
        VARIABLE_OFFSETS,
    >
{
    fn write_non_memory_family_data<const FAMILY: u8>(
        &mut self,
        _data: NonMemoryOpcodeTracingDataWithTimestamp,
    ) {
    }
    fn write_memory_family_data<const FAMILY: u8>(
        &mut self,
        _data: MemoryOpcodeTracingDataWithTimestamp,
    ) {
    }

    #[inline(always)]
    fn write_delegation<
        const DELEGATION_TYPE_T: u16,
        const REG_ACCESSES_T: usize,
        const INDIRECT_READS_T: usize,
        const INDIRECT_WRITES_T: usize,
        const VARIABLE_OFFSETS_T: usize,
    >(
        &mut self,
        data: DelegationWitness<
            REG_ACCESSES_T,
            INDIRECT_READS_T,
            INDIRECT_WRITES_T,
            VARIABLE_OFFSETS_T,
        >,
    ) {
        debug_assert_eq!(REG_ACCESSES, REG_ACCESSES_T);
        debug_assert_eq!(INDIRECT_READS, INDIRECT_READS_T);
        debug_assert_eq!(INDIRECT_WRITES, INDIRECT_WRITES);
        debug_assert_eq!(VARIABLE_OFFSETS, VARIABLE_OFFSETS_T);
        if DELEGATION_TYPE == DELEGATION_TYPE_T {
            unsafe {
                if self.buffers.len() > 0 {
                    let first = self.buffers.get_unchecked_mut(0);
                    first
                        .as_mut_ptr()
                        .cast::<DelegationWitness<
                            REG_ACCESSES_T,
                            INDIRECT_READS_T,
                            INDIRECT_WRITES_T,
                            VARIABLE_OFFSETS_T,
                        >>()
                        .write(data);
                    // For some reason truncating the buffer doesn't work - livetime analysis complains
                    *first = core::mem::transmute(first.get_unchecked_mut(1..));
                    if first.is_empty() {
                        self.buffers = core::mem::transmute(self.buffers.get_unchecked_mut(1..));
                    }
                } else {
                    // nothing
                }
            }
        } else {
        }
    }
}

pub type BigintDelegationDestinationHolder<'a> = DelegationDestinationHolder<
    'a,
    { common_constants::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16 },
    3,
    8,
    8,
    0,
>;
pub type BlakeDelegationDestinationHolder<'a> = DelegationDestinationHolder<
    'a,
    { common_constants::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER as u16 },
    4,
    16,
    24,
    0,
>;

// Holder for destination buffer for one particular delegation type. It may represent only part
// of the destination circuit's capacity
pub struct NonMemDestinationHolder<'a, const FAMILY: u8> {
    pub buffers: &'a mut [&'a mut [NonMemoryOpcodeTracingDataWithTimestamp]],
}

impl<'a, const FAMILY: u8> WitnessTracer for NonMemDestinationHolder<'a, FAMILY> {
    #[inline(always)]
    fn write_non_memory_family_data<const FAMILY_T: u8>(
        &mut self,
        data: NonMemoryOpcodeTracingDataWithTimestamp,
    ) {
        if FAMILY == FAMILY_T {
            unsafe {
                if self.buffers.len() > 0 {
                    let first = self.buffers.get_unchecked_mut(0);
                    first.as_mut_ptr().write(data);
                    // For some reason truncating the buffer doesn't work - livetime analysis complains
                    *first = core::mem::transmute(first.get_unchecked_mut(1..));
                    if first.is_empty() {
                        self.buffers = core::mem::transmute(self.buffers.get_unchecked_mut(1..));
                    }
                } else {
                    // nothing
                }
            }
        } else {
        }
    }
    fn write_memory_family_data<const FAMILY_T: u8>(
        &mut self,
        _data: MemoryOpcodeTracingDataWithTimestamp,
    ) {
    }

    fn write_delegation<
        const DELEGATION_TYPE: u16,
        const REG_ACCESSES_T: usize,
        const INDIRECT_READS_T: usize,
        const INDIRECT_WRITES_T: usize,
        const VARIABLE_OFFSETS_T: usize,
    >(
        &mut self,
        _data: DelegationWitness<
            REG_ACCESSES_T,
            INDIRECT_READS_T,
            INDIRECT_WRITES_T,
            VARIABLE_OFFSETS_T,
        >,
    ) {
    }
}

// Holder for destination buffer for one particular delegation type. It may represent only part
// of the destination circuit's capacity
pub struct MemDestinationHolder<'a, const FAMILY: u8> {
    pub buffers: &'a mut [&'a mut [MemoryOpcodeTracingDataWithTimestamp]],
}

impl<'a, const FAMILY: u8> WitnessTracer for MemDestinationHolder<'a, FAMILY> {
    fn write_non_memory_family_data<const FAMILY_T: u8>(
        &mut self,
        _data: NonMemoryOpcodeTracingDataWithTimestamp,
    ) {
    }

    #[inline(always)]
    fn write_memory_family_data<const FAMILY_T: u8>(
        &mut self,
        data: MemoryOpcodeTracingDataWithTimestamp,
    ) {
        if FAMILY == FAMILY_T {
            unsafe {
                if self.buffers.len() > 0 {
                    let first = self.buffers.get_unchecked_mut(0);
                    first.as_mut_ptr().write(data);
                    // For some reason truncating the buffer doesn't work - livetime analysis complains
                    *first = core::mem::transmute(first.get_unchecked_mut(1..));
                    if first.is_empty() {
                        self.buffers = core::mem::transmute(self.buffers.get_unchecked_mut(1..));
                    }
                } else {
                    // nothing
                }
            }
        } else {
        }
    }

    fn write_delegation<
        const DELEGATION_TYPE: u16,
        const REG_ACCESSES_T: usize,
        const INDIRECT_READS_T: usize,
        const INDIRECT_WRITES_T: usize,
        const VARIABLE_OFFSETS_T: usize,
    >(
        &mut self,
        _data: DelegationWitness<
            REG_ACCESSES_T,
            INDIRECT_READS_T,
            INDIRECT_WRITES_T,
            VARIABLE_OFFSETS_T,
        >,
    ) {
    }
}
