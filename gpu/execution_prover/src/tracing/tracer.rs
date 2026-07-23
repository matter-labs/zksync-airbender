use super::{DataTraceRanges, PtrRange, SplitDataTraceRanges, UnifiedDataTraceRanges};
use gpu_trace::witness::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use riscv_transpiler::witness::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
    UnifiedOpcodeTracingDataWithTimestamp, WitnessTracer,
};
use std::any;
use std::collections::VecDeque;

const ADD_SUB_FAMILY_IDX: u8 = CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
    UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
))
.get_family_idx();
const JUMP_BRANCH_FAMILY_IDX: u8 = CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
    UnrolledNonMemoryCircuitType::JumpBranchSlt,
))
.get_family_idx();
const SHIFT_BINARY_FAMILY_IDX: u8 = CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
    UnrolledNonMemoryCircuitType::ShiftBinary,
))
.get_family_idx();
const MUL_DIV_FAMILY_IDX: u8 = CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
    UnrolledNonMemoryCircuitType::MulDivUnsigned,
))
.get_family_idx();
const LOAD_STORE_SUBWORD_FAMILY_IDX: u8 = CircuitType::Unrolled(UnrolledCircuitType::Memory(
    UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
))
.get_family_idx();
const LOAD_STORE_WORD_FAMILY_IDX: u8 = CircuitType::Unrolled(UnrolledCircuitType::Memory(
    UnrolledMemoryCircuitType::LoadStoreWordOnly,
))
.get_family_idx();
const BLAKE_DELEGATION_TYPE_ID: u16 =
    DelegationCircuitType::Blake2WithCompression.get_delegation_type_id();
const BIGINT_DELEGATION_TYPE_ID: u16 =
    DelegationCircuitType::BigIntWithControl.get_delegation_type_id();
const KECCAK_DELEGATION_TYPE_ID: u16 =
    DelegationCircuitType::KeccakSpecial5.get_delegation_type_id();
const BLAKE_G_FUNCTION_DELEGATION_TYPE_ID: u16 =
    DelegationCircuitType::Blake2GFunction.get_delegation_type_id();

struct TracerRanges<T: Copy + 'static> {
    queue: VecDeque<PtrRange<T>>,
    current: PtrRange<T>,
    count: usize,
}

impl<T: Copy + 'static> TracerRanges<T> {
    fn new(queue: VecDeque<PtrRange<T>>) -> Self {
        Self {
            queue,
            current: PtrRange::default(),
            count: 0,
        }
    }

    /// # Safety
    ///
    /// Caller must ensure the producer reserved enough capacity in `queue`
    /// for every `write` made during a snapshot (see `process_snapshot`).
    #[inline(always)]
    unsafe fn write(&mut self, value: T) {
        self.write_type_unchecked(value);
    }

    /// # Safety
    ///
    /// Same capacity contract as [`Self::write`], plus `U` must equal `T`
    /// (debug-asserted below). Used to forward dispatch-erased values from
    /// callers that have a const-generic guarantee of type equality.
    #[inline(always)]
    unsafe fn write_type_unchecked<U: Copy + 'static>(&mut self, value: U) {
        debug_assert_eq!(any::TypeId::of::<T>(), any::TypeId::of::<U>());
        if core::hint::unlikely(self.current.start == self.current.end) {
            // SAFETY: capacity precondition: producer pre-queued enough
            // `PtrRange`s for this snapshot's writes.
            self.current = self.queue.pop_front().unwrap_unchecked();
        }
        // SAFETY: `self.current.start` points into a live `PtrRange` reserved
        // for this tracer; `T == U` debug-checked above.
        *(self.current.start as *mut U) = value;
        self.current.start = self.current.start.add(1);
        self.count += 1;
    }
}

pub(crate) trait Tracer: WitnessTracer {
    type Ranges: DataTraceRanges + Send;

    fn new(trace_ranges: Self::Ranges) -> Self;
}

pub(crate) struct SplitTracer {
    blake_calls: TracerRanges<Blake2sRoundFunctionDelegationWitness>,
    bigint_calls: TracerRanges<BigintDelegationWitness>,
    keccak_calls: TracerRanges<KeccakSpecial5DelegationWitness>,
    blake_g_function_calls: TracerRanges<Blake2sGFunctionDelegationWitness>,
    add_sub_family: TracerRanges<NonMemoryOpcodeTracingDataWithTimestamp>,
    binary_shift_csr_family: TracerRanges<NonMemoryOpcodeTracingDataWithTimestamp>,
    slt_branch_family: TracerRanges<NonMemoryOpcodeTracingDataWithTimestamp>,
    mul_div_family: TracerRanges<NonMemoryOpcodeTracingDataWithTimestamp>,
    word_size_mem_family: TracerRanges<MemoryOpcodeTracingDataWithTimestamp>,
    subword_size_mem_family: TracerRanges<MemoryOpcodeTracingDataWithTimestamp>,
}

impl Tracer for SplitTracer {
    type Ranges = SplitDataTraceRanges;

    fn new(trace_ranges: Self::Ranges) -> Self {
        Self {
            blake_calls: TracerRanges::new(trace_ranges.blake_calls),
            bigint_calls: TracerRanges::new(trace_ranges.bigint_calls),
            keccak_calls: TracerRanges::new(trace_ranges.keccak_calls),
            blake_g_function_calls: TracerRanges::new(trace_ranges.blake_g_function_calls),
            add_sub_family: TracerRanges::new(trace_ranges.add_sub_family),
            binary_shift_csr_family: TracerRanges::new(trace_ranges.binary_shift_csr_family),
            slt_branch_family: TracerRanges::new(trace_ranges.slt_branch_family),
            mul_div_family: TracerRanges::new(trace_ranges.mul_div_family),
            word_size_mem_family: TracerRanges::new(trace_ranges.word_size_mem_family),
            subword_size_mem_family: TracerRanges::new(trace_ranges.subword_size_mem_family),
        }
    }
}

// `SplitTracer` and `UnifiedTracer` both name their four delegation
// `TracerRanges` fields identically (`blake_calls` / `bigint_calls` /
// `keccak_calls` / `blake_g_function_calls`), so `WitnessTracer::write_delegation`
// dispatches identically for both — this macro is the shared method body,
// invoked once per `impl WitnessTracer for { Split, Unified }Tracer` block.
macro_rules! impl_write_delegation {
    () => {
        #[inline(always)]
        fn write_delegation<
            const DELEGATION_TYPE: u16,
            const REG_ACCESSES: usize,
            const INDIRECT_READS: usize,
            const INDIRECT_WRITES: usize,
            const VARIABLE_OFFSETS: usize,
        >(
            &mut self,
            data: riscv_transpiler::witness::DelegationWitness<
                REG_ACCESSES,
                INDIRECT_READS,
                INDIRECT_WRITES,
                VARIABLE_OFFSETS,
            >,
        ) {
            // SAFETY: `unreachable_unchecked` covers the upstream
            // `WitnessTracer::write_delegation` contract (DELEGATION_TYPE outside
            // the enumerated set). `write_type_unchecked` is sound because each
            // arm pairs a const DELEGATION_TYPE with the matching witness type T
            // by construction.
            unsafe {
                if const { DELEGATION_TYPE == BLAKE_DELEGATION_TYPE_ID } {
                    self.blake_calls.write_type_unchecked(data)
                } else if const { DELEGATION_TYPE == BIGINT_DELEGATION_TYPE_ID } {
                    self.bigint_calls.write_type_unchecked(data)
                } else if const { DELEGATION_TYPE == KECCAK_DELEGATION_TYPE_ID } {
                    self.keccak_calls.write_type_unchecked(data)
                } else if const { DELEGATION_TYPE == BLAKE_G_FUNCTION_DELEGATION_TYPE_ID } {
                    self.blake_g_function_calls.write_type_unchecked(data)
                } else {
                    core::hint::unreachable_unchecked()
                };
            }
        }
    };
}

impl WitnessTracer for SplitTracer {
    #[inline(always)]
    fn needs_tracing_data_for_circuit_family<const FAMILY: u8>(&self) -> bool {
        true
    }

    #[inline(always)]
    fn needs_tracing_data_for_delegation_type<const DELEGATION_TYPE: u16>(&self) -> bool {
        true
    }

    #[inline(always)]
    fn write_non_memory_family_data<const FAMILY: u8>(
        &mut self,
        data: NonMemoryOpcodeTracingDataWithTimestamp,
    ) {
        // SAFETY: `unreachable_unchecked` is reached only if the upstream
        // `WitnessTracer` contract is violated (FAMILY outside the enumerated
        // set). The `.write()` calls rely on capacity pre-queued by the
        // matching family `Producer` for this snapshot.
        unsafe {
            if const { FAMILY == ADD_SUB_FAMILY_IDX } {
                self.add_sub_family.write(data)
            } else if const { FAMILY == JUMP_BRANCH_FAMILY_IDX } {
                self.slt_branch_family.write(data)
            } else if const { FAMILY == SHIFT_BINARY_FAMILY_IDX } {
                self.binary_shift_csr_family.write(data)
            } else if const { FAMILY == MUL_DIV_FAMILY_IDX } {
                self.mul_div_family.write(data)
            } else {
                core::hint::unreachable_unchecked()
            };
        }
    }

    #[inline(always)]
    fn write_memory_family_data<const FAMILY: u8>(
        &mut self,
        data: MemoryOpcodeTracingDataWithTimestamp,
    ) {
        // SAFETY: as in `write_non_memory_family_data` — `unreachable_unchecked`
        // covers the upstream FAMILY contract; `.write()` relies on pre-queued
        // capacity owned by the matching family `Producer`.
        unsafe {
            if const { FAMILY == LOAD_STORE_SUBWORD_FAMILY_IDX } {
                self.subword_size_mem_family.write(data)
            } else if const { FAMILY == LOAD_STORE_WORD_FAMILY_IDX } {
                self.word_size_mem_family.write(data)
            } else {
                core::hint::unreachable_unchecked()
            };
        }
    }

    impl_write_delegation!();
}

pub(crate) struct UnifiedTracer {
    blake_calls: TracerRanges<Blake2sRoundFunctionDelegationWitness>,
    bigint_calls: TracerRanges<BigintDelegationWitness>,
    keccak_calls: TracerRanges<KeccakSpecial5DelegationWitness>,
    blake_g_function_calls: TracerRanges<Blake2sGFunctionDelegationWitness>,
    cycles: TracerRanges<UnifiedOpcodeTracingDataWithTimestamp>,
}

impl Tracer for UnifiedTracer {
    type Ranges = UnifiedDataTraceRanges;

    fn new(trace_ranges: Self::Ranges) -> Self {
        Self {
            blake_calls: TracerRanges::new(trace_ranges.blake_calls),
            bigint_calls: TracerRanges::new(trace_ranges.bigint_calls),
            keccak_calls: TracerRanges::new(trace_ranges.keccak_calls),
            blake_g_function_calls: TracerRanges::new(trace_ranges.blake_g_function_calls),
            cycles: TracerRanges::new(trace_ranges.cycles),
        }
    }
}

impl WitnessTracer for UnifiedTracer {
    #[inline(always)]
    fn needs_tracing_data_for_circuit_family<const FAMILY: u8>(&self) -> bool {
        true
    }

    #[inline(always)]
    fn needs_tracing_data_for_delegation_type<const DELEGATION_TYPE: u16>(&self) -> bool {
        true
    }

    #[inline(always)]
    fn write_non_memory_family_data<const FAMILY: u8>(
        &mut self,
        data: NonMemoryOpcodeTracingDataWithTimestamp,
    ) {
        // SAFETY: capacity pre-queued by the unified `Producer` for the
        // `cycles` stream during `process_snapshot`.
        unsafe {
            self.cycles
                .write(UnifiedOpcodeTracingDataWithTimestamp::NonMem(data))
        }
    }

    #[inline(always)]
    fn write_memory_family_data<const FAMILY: u8>(
        &mut self,
        data: MemoryOpcodeTracingDataWithTimestamp,
    ) {
        // SAFETY: as above — capacity pre-queued by the unified `Producer`.
        unsafe {
            self.cycles
                .write(UnifiedOpcodeTracingDataWithTimestamp::Mem(data))
        }
    }

    impl_write_delegation!();
}
