pub mod delegation;

use std::mem::MaybeUninit;

pub use self::delegation::{DelegationAbiDescription, DelegationWitness};
use risc_v_simulator::machine_mode_only_unrolled::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
    UnifiedOpcodeTracingDataWithTimestamp,
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
pub type KeccakDelegationDestinationHolder<'a> = DelegationDestinationHolder<
    'a,
    { common_constants::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER as u16 },
    2,
    0,
    { common_constants::keccak_special5::KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS * 2 },
    { common_constants::keccak_special5::KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS },
>;

pub struct UninitDelegationDestinationHolder<
    'a,
    const DELEGATION_TYPE: u16,
    const REG_ACCESSES: usize,
    const INDIRECT_READS: usize,
    const INDIRECT_WRITES: usize,
    const VARIABLE_OFFSETS: usize,
> {
    pub buffers: &'a mut [&'a mut [MaybeUninit<
        DelegationWitness<REG_ACCESSES, INDIRECT_READS, INDIRECT_WRITES, VARIABLE_OFFSETS>,
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
    for UninitDelegationDestinationHolder<
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
                        .cast::<MaybeUninit<
                            DelegationWitness<
                                REG_ACCESSES_T,
                                INDIRECT_READS_T,
                                INDIRECT_WRITES_T,
                                VARIABLE_OFFSETS_T,
                            >,
                        >>()
                        .as_mut_unchecked()
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

pub type UninitBigintDelegationDestinationHolder<'a> = UninitDelegationDestinationHolder<
    'a,
    { common_constants::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16 },
    3,
    8,
    8,
    0,
>;
pub type UninitBlakeDelegationDestinationHolder<'a> = UninitDelegationDestinationHolder<
    'a,
    { common_constants::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER as u16 },
    4,
    16,
    24,
    0,
>;
pub type UninitKeccakDelegationDestinationHolder<'a> = UninitDelegationDestinationHolder<
    'a,
    { common_constants::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER as u16 },
    2,
    0,
    { common_constants::keccak_special5::KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS * 2 },
    { common_constants::keccak_special5::KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS },
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
pub struct UninitNonMemDestinationHolder<'a, const FAMILY: u8> {
    pub buffers: &'a mut [&'a mut [MaybeUninit<NonMemoryOpcodeTracingDataWithTimestamp>]],
}

impl<'a, const FAMILY: u8> WitnessTracer for UninitNonMemDestinationHolder<'a, FAMILY> {
    #[inline(always)]
    fn write_non_memory_family_data<const FAMILY_T: u8>(
        &mut self,
        data: NonMemoryOpcodeTracingDataWithTimestamp,
    ) {
        if FAMILY == FAMILY_T {
            unsafe {
                if self.buffers.len() > 0 {
                    let first = self.buffers.get_unchecked_mut(0);
                    first.as_mut_ptr().as_mut_unchecked().write(data);
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

pub struct UninitMemDestinationHolder<'a, const FAMILY: u8> {
    pub buffers: &'a mut [&'a mut [MaybeUninit<MemoryOpcodeTracingDataWithTimestamp>]],
}

impl<'a, const FAMILY: u8> WitnessTracer for UninitMemDestinationHolder<'a, FAMILY> {
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
                    first.as_mut_ptr().as_mut_unchecked().write(data);
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

pub struct UnifiedDestinationHolder<'a> {
    pub buffers: &'a mut [&'a mut [UnifiedOpcodeTracingDataWithTimestamp]],
}

impl<'a> WitnessTracer for UnifiedDestinationHolder<'a> {
    fn write_non_memory_family_data<const FAMILY_T: u8>(
        &mut self,
        data: NonMemoryOpcodeTracingDataWithTimestamp,
    ) {
        unsafe {
            if self.buffers.len() > 0 {
                let first = self.buffers.get_unchecked_mut(0);
                first
                    .as_mut_ptr()
                    .write(UnifiedOpcodeTracingDataWithTimestamp::NonMem(data));
                // For some reason truncating the buffer doesn't work - livetime analysis complains
                *first = core::mem::transmute(first.get_unchecked_mut(1..));
                if first.is_empty() {
                    self.buffers = core::mem::transmute(self.buffers.get_unchecked_mut(1..));
                }
            } else {
                // nothing
            }
        }
    }

    #[inline(always)]
    fn write_memory_family_data<const FAMILY_T: u8>(
        &mut self,
        data: MemoryOpcodeTracingDataWithTimestamp,
    ) {
        unsafe {
            if self.buffers.len() > 0 {
                let first = self.buffers.get_unchecked_mut(0);
                first
                    .as_mut_ptr()
                    .write(UnifiedOpcodeTracingDataWithTimestamp::Mem(data));
                // For some reason truncating the buffer doesn't work - livetime analysis complains
                *first = core::mem::transmute(first.get_unchecked_mut(1..));
                if first.is_empty() {
                    self.buffers = core::mem::transmute(self.buffers.get_unchecked_mut(1..));
                }
            } else {
                // nothing
            }
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

pub trait DestinationHolderConstructor: 'static + Send + Sync + Clone + Copy {
    type Tracer<'a>: WitnessTracer;
    type UninitTracer<'a>: WitnessTracer;
    type Element: 'static + Send + Sync + Clone;

    fn make_tracer<'a>(buffers: &'a mut [&'a mut [Self::Element]]) -> Self::Tracer<'a>;
    fn make_uninit_tracer<'a>(
        buffers: &'a mut [&'a mut [MaybeUninit<Self::Element>]],
    ) -> Self::UninitTracer<'a>;
}

#[derive(Clone, Copy, Debug)]
pub struct MemDestinationHolderConstructor<const FAMILY_IDX: u8>;

impl<const FAMILY_IDX: u8> DestinationHolderConstructor
    for MemDestinationHolderConstructor<FAMILY_IDX>
{
    type Element = MemoryOpcodeTracingDataWithTimestamp;
    type Tracer<'a> = MemDestinationHolder<'a, FAMILY_IDX>;
    type UninitTracer<'a> = UninitMemDestinationHolder<'a, FAMILY_IDX>;

    fn make_tracer<'a>(buffers: &'a mut [&'a mut [Self::Element]]) -> Self::Tracer<'a> {
        MemDestinationHolder { buffers }
    }

    fn make_uninit_tracer<'a>(
        buffers: &'a mut [&'a mut [MaybeUninit<Self::Element>]],
    ) -> Self::UninitTracer<'a> {
        UninitMemDestinationHolder { buffers }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct NonMemDestinationHolderConstructor<const FAMILY_IDX: u8>;

impl<const FAMILY_IDX: u8> DestinationHolderConstructor
    for NonMemDestinationHolderConstructor<FAMILY_IDX>
{
    type Element = NonMemoryOpcodeTracingDataWithTimestamp;
    type Tracer<'a> = NonMemDestinationHolder<'a, FAMILY_IDX>;
    type UninitTracer<'a> = UninitNonMemDestinationHolder<'a, FAMILY_IDX>;

    fn make_tracer<'a>(buffers: &'a mut [&'a mut [Self::Element]]) -> Self::Tracer<'a> {
        NonMemDestinationHolder { buffers }
    }

    fn make_uninit_tracer<'a>(
        buffers: &'a mut [&'a mut [MaybeUninit<Self::Element>]],
    ) -> Self::UninitTracer<'a> {
        UninitNonMemDestinationHolder { buffers }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct DelegationDestinationHolderConstructor<
    const DELEGATION_TYPE: u16,
    const REG_ACCESSES: usize,
    const INDIRECT_READS: usize,
    const INDIRECT_WRITES: usize,
    const VARIABLE_OFFSETS: usize,
>;

impl<
        const DELEGATION_TYPE: u16,
        const REG_ACCESSES: usize,
        const INDIRECT_READS: usize,
        const INDIRECT_WRITES: usize,
        const VARIABLE_OFFSETS: usize,
    > DestinationHolderConstructor
    for DelegationDestinationHolderConstructor<
        DELEGATION_TYPE,
        REG_ACCESSES,
        INDIRECT_READS,
        INDIRECT_WRITES,
        VARIABLE_OFFSETS,
    >
{
    type Element =
        DelegationWitness<REG_ACCESSES, INDIRECT_READS, INDIRECT_WRITES, VARIABLE_OFFSETS>;
    type Tracer<'a> = DelegationDestinationHolder<
        'a,
        DELEGATION_TYPE,
        REG_ACCESSES,
        INDIRECT_READS,
        INDIRECT_WRITES,
        VARIABLE_OFFSETS,
    >;
    type UninitTracer<'a> = UninitDelegationDestinationHolder<
        'a,
        DELEGATION_TYPE,
        REG_ACCESSES,
        INDIRECT_READS,
        INDIRECT_WRITES,
        VARIABLE_OFFSETS,
    >;

    fn make_tracer<'a>(buffers: &'a mut [&'a mut [Self::Element]]) -> Self::Tracer<'a> {
        DelegationDestinationHolder { buffers }
    }

    fn make_uninit_tracer<'a>(
        buffers: &'a mut [&'a mut [MaybeUninit<Self::Element>]],
    ) -> Self::UninitTracer<'a> {
        UninitDelegationDestinationHolder { buffers }
    }
}

pub type BigintDelegationDestinationHolderConstructor = DelegationDestinationHolderConstructor<
    { common_constants::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16 },
    3,
    8,
    8,
    0,
>;
pub type BlakeDelegationDestinationHolderConstructor = DelegationDestinationHolderConstructor<
    { common_constants::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER as u16 },
    4,
    16,
    24,
    0,
>;
pub type KeccakDelegationDestinationHolderConstructor<'a> = DelegationDestinationHolderConstructor<
    { common_constants::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER as u16 },
    2,
    0,
    { common_constants::keccak_special5::KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS * 2 },
    { common_constants::keccak_special5::KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS },
>;
