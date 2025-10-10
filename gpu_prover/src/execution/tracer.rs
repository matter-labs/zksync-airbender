use crate::execution::snapshotter::{DelegationsAndFamiliesDataTraceRanges, PtrRange};
use cs::definitions::{
    ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX, BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
    BLAKE2S_DELEGATION_CSR_REGISTER, JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX,
    KECCAK_SPECIAL5_CSR_REGISTER, LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX,
    LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX, MUL_DIV_CIRCUIT_FAMILY_IDX,
    SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX,
};
use prover::risc_v_simulator::machine_mode_only_unrolled::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use riscv_transpiler::witness::WitnessTracer;
use std::any;
use std::collections::VecDeque;

struct TracerRanges<T: Copy + 'static> {
    queue: VecDeque<PtrRange<T>>,
    current: PtrRange<T>,
}

impl<T: Copy + 'static> TracerRanges<T> {
    fn new(queue: VecDeque<PtrRange<T>>) -> Self {
        Self {
            queue,
            current: PtrRange::default(),
        }
    }

    #[inline(always)]
    unsafe fn write(&mut self, value: T) {
        self.write_type_unchecked(value);
    }

    #[inline(always)]
    unsafe fn write_type_unchecked<U: Copy + 'static>(&mut self, value: U) {
        debug_assert_eq!(any::TypeId::of::<T>(), any::TypeId::of::<U>());
        if core::hint::unlikely(self.current.start == self.current.end) {
            self.current = self.queue.pop_front().unwrap_unchecked();
        }
        *(self.current.start as *mut U) = value;
        self.current.start = self.current.start.add(1);
    }
}

pub(crate) struct SplitTracer {
    blake_calls: TracerRanges<Blake2sRoundFunctionDelegationWitness>,
    bigint_calls: TracerRanges<BigintDelegationWitness>,
    keccak_calls: TracerRanges<KeccakSpecial5DelegationWitness>,
    add_sub_family: TracerRanges<NonMemoryOpcodeTracingDataWithTimestamp>,
    binary_shift_csr_family: TracerRanges<NonMemoryOpcodeTracingDataWithTimestamp>,
    slt_branch_family: TracerRanges<NonMemoryOpcodeTracingDataWithTimestamp>,
    mul_div_family: TracerRanges<NonMemoryOpcodeTracingDataWithTimestamp>,
    word_size_mem_family: TracerRanges<MemoryOpcodeTracingDataWithTimestamp>,
    subword_size_mem_family: TracerRanges<MemoryOpcodeTracingDataWithTimestamp>,
}

impl SplitTracer {
    pub fn new(trace_ranges: DelegationsAndFamiliesDataTraceRanges) -> Self {
        Self {
            blake_calls: TracerRanges::new(trace_ranges.blake_calls),
            bigint_calls: TracerRanges::new(trace_ranges.bigint_calls),
            keccak_calls: TracerRanges::new(trace_ranges.keccak_calls),
            add_sub_family: TracerRanges::new(trace_ranges.add_sub_family),
            binary_shift_csr_family: TracerRanges::new(trace_ranges.binary_shift_csr_family),
            slt_branch_family: TracerRanges::new(trace_ranges.slt_branch_family),
            mul_div_family: TracerRanges::new(trace_ranges.mul_div_family),
            word_size_mem_family: TracerRanges::new(trace_ranges.word_size_mem_family),
            subword_size_mem_family: TracerRanges::new(trace_ranges.subword_size_mem_family),
        }
    }
}

impl WitnessTracer for SplitTracer {
    #[inline(always)]
    fn write_non_memory_family_data<const FAMILY: u8>(
        &mut self,
        data: NonMemoryOpcodeTracingDataWithTimestamp,
    ) {
        unsafe {
            if const { FAMILY == ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX } {
                self.add_sub_family.write(data)
            } else if const { FAMILY == JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX } {
                self.slt_branch_family.write(data)
            } else if const { FAMILY == SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX } {
                self.binary_shift_csr_family.write(data)
            } else if const { FAMILY == MUL_DIV_CIRCUIT_FAMILY_IDX } {
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
        unsafe {
            if const { FAMILY == LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX } {
                self.subword_size_mem_family.write(data)
            } else if const { FAMILY == LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX } {
                self.word_size_mem_family.write(data)
            } else {
                core::hint::unreachable_unchecked()
            };
        }
    }

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
        unsafe {
            if const { DELEGATION_TYPE == BLAKE2S_DELEGATION_CSR_REGISTER as u16 } {
                self.blake_calls.write_type_unchecked(data)
            } else if const { DELEGATION_TYPE == BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16 } {
                self.bigint_calls.write_type_unchecked(data)
            } else if const { DELEGATION_TYPE == KECCAK_SPECIAL5_CSR_REGISTER as u16 } {
                self.keccak_calls.write_type_unchecked(data)
            } else {
                core::hint::unreachable_unchecked()
            };
        }
    }
}
