use crate::allocator::host::ConcurrentStaticHostAllocator;
use cs::definitions::TimestampScalar;
use fft::GoodAllocator;
use prover::risc_v_simulator::machine_mode_only_unrolled::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
};
use riscv_transpiler::vm::{Counters, DelegationsAndFamiliesCounters, State};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use std::collections::VecDeque;
use std::sync::Arc;

pub(crate) struct OnceSnapshotter {
    pub period: usize,
    pub non_determinism_reads: Vec<u32>,
    pub memory_reads: Vec<(u32, (u32, u32))>,
}

impl OnceSnapshotter {
    pub fn new_for_period(period: usize) -> Self {
        Self {
            period,
            non_determinism_reads: Vec::with_capacity(period),
            memory_reads: Vec::with_capacity(period << 1),
        }
    }
}

impl<C: Counters> riscv_transpiler::vm::Snapshotter<C> for OnceSnapshotter {
    #[inline(always)]
    fn take_snapshot(&mut self, _state: &State<C>) {
        assert!(self.non_determinism_reads.len() <= self.period);
        assert!(self.memory_reads.len() <= self.period << 1);
    }

    #[inline(always)]
    fn append_non_determinism_read(&mut self, value: u32) {
        unsafe { self.non_determinism_reads.extend_one_unchecked(value) }
    }

    #[inline(always)]
    fn append_memory_read(
        &mut self,
        _address: u32,
        read_value: u32,
        read_timestamp: TimestampScalar,
        _write_timestamp: TimestampScalar,
    ) {
        let read_timestamp = (read_timestamp as u32, (read_timestamp >> 32) as u32);
        let value = (read_value, read_timestamp);
        unsafe { self.memory_reads.extend_one_unchecked(value) }
    }
}

type A = ConcurrentStaticHostAllocator;

pub(crate) struct PtrRange<T> {
    pub start: *mut T,
    pub end: *mut T,
    pub chunk: Option<Arc<Vec<T, A>>>,
}

impl<T> Default for PtrRange<T> {
    fn default() -> Self {
        Self {
            start: std::ptr::null_mut(),
            end: std::ptr::null_mut(),
            chunk: None,
        }
    }
}

unsafe impl<T> Send for PtrRange<T> {}

#[derive(Default)]
pub(crate) struct DelegationsAndFamiliesDataTraceRanges {
    pub blake_calls: VecDeque<PtrRange<Blake2sRoundFunctionDelegationWitness>>,
    pub bigint_calls: VecDeque<PtrRange<BigintDelegationWitness>>,
    pub keccak_calls: VecDeque<PtrRange<KeccakSpecial5DelegationWitness>>,
    pub add_sub_family: VecDeque<PtrRange<NonMemoryOpcodeTracingDataWithTimestamp>>,
    pub binary_shift_csr_family: VecDeque<PtrRange<NonMemoryOpcodeTracingDataWithTimestamp>>,
    pub slt_branch_family: VecDeque<PtrRange<NonMemoryOpcodeTracingDataWithTimestamp>>,
    pub mul_div_family: VecDeque<PtrRange<NonMemoryOpcodeTracingDataWithTimestamp>>,
    pub word_size_mem_family: VecDeque<PtrRange<MemoryOpcodeTracingDataWithTimestamp>>,
    pub subword_size_mem_family: VecDeque<PtrRange<MemoryOpcodeTracingDataWithTimestamp>>,
}

pub(crate) struct SplitSnapshot {
    pub index: usize,
    pub cycles_count: usize,
    pub initial_state: State<DelegationsAndFamiliesCounters>,
    pub non_determinism_reads: Vec<u32>,
    pub memory_reads: Vec<(u32, (u32, u32))>,
    pub trace_ranges: DelegationsAndFamiliesDataTraceRanges,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::execution::ram::RamWithRomRegion;
    use crate::tests::read_binary;
    use itertools::Itertools;
    use prover::common_constants::{INITIAL_TIMESTAMP, TIMESTAMP_STEP};
    use prover::risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
    use riscv_transpiler::ir::{decode, FullMachineDecoderConfig};
    use riscv_transpiler::vm::{DelegationsAndFamiliesCounters, SimpleTape, VM};
    use std::path::Path;

    #[test]
    fn test_snapshotter() {
        let binary_image = read_binary(&Path::new("../examples/hashed_fibonacci/app.bin"));
        let text_section = read_binary(&Path::new("../examples/hashed_fibonacci/app.text"));
        // let mut non_determinism_source = QuasiUARTSource::new_with_reads(vec![1 << 24, 0]);
        let mut non_determinism_source = QuasiUARTSource::new_with_reads(vec![0, 1 << 18]);
        let mut ram = RamWithRomRegion::<30, 22, true>::new(&binary_image);
        let preprocessed_bytecode = text_section
            .iter()
            .copied()
            .map(decode::<FullMachineDecoderConfig>)
            .collect_vec();
        let tape = SimpleTape::new(&preprocessed_bytecode);
        type CountersT = DelegationsAndFamiliesCounters;
        let mut state = State::initial_with_counters(CountersT::default());
        let mut snapshotters = vec![];
        let now = std::time::Instant::now();
        loop {
            const PERIOD: usize = 1 << 20;
            let mut snapshotter = OnceSnapshotter::new_for_period(PERIOD);
            let is_program_finished = VM::run_basic_unrolled(
                &mut state,
                1,
                &mut ram,
                &mut snapshotter,
                &tape,
                PERIOD,
                &mut non_determinism_source,
            );
            snapshotters.push(snapshotter);
            if is_program_finished {
                break;
            }
        }
        let elapsed = now.elapsed();
        let cycles = (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;
        let mhz = cycles as f64 / elapsed.as_micros() as f64;
        println!(
            "Execution of {cycles} cycles finished in {:?} @ {} MHz",
            elapsed, mhz
        );
        println!(
            "Total memory reads: {}",
            snapshotters
                .iter()
                .map(|s| s.memory_reads.len())
                .sum::<usize>()
        );
        println!(
            "Total non-determinism reads: {}",
            snapshotters
                .iter()
                .map(|s| s.non_determinism_reads.len())
                .sum::<usize>()
        );
        let now = std::time::Instant::now();
        let count = ram.get_touched_words_count();
        println!(
            "Touched memory words: {} Counted in {:?}",
            count,
            now.elapsed()
        );
    }
}
