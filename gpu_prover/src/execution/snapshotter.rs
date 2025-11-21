use super::A;
use prover::risc_v_simulator::machine_mode_only_unrolled::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
    UnifiedOpcodeTracingDataWithTimestamp,
};
use riscv_transpiler::jit::{MachineState, TraceChunk};
use riscv_transpiler::vm::{Counters, Snapshotter};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use std::collections::VecDeque;
use std::sync::Arc;
// pub(crate) struct OnceSnapshotter {
//     pub period: usize,
//     pub initial_timestamp: TimestampScalar,
//     pub reads: Vec<(u32, (u32, u32))>,
// }
//
// const MAX_MEMORY_READS_PER_CYCLE: usize = 8;
//
// impl OnceSnapshotter {
//     pub fn new_for_period(period: usize, state: &State<impl Counters>) -> Self {
//         Self {
//             period,
//             initial_timestamp: state.timestamp,
//             reads: Vec::with_capacity(Self::get_max_reads_len(period)),
//         }
//     }
//
//     pub fn assert_no_overflow(&self) {
//         let reads_len = self.reads.len();
//         let max_reads_len = Self::get_max_reads_len(self.period);
//         assert!(
//             reads_len <= max_reads_len,
//             "reads_len: {reads_len}, max_reads_len: {max_reads_len}"
//         );
//     }
//
//     fn get_max_reads_len(period: usize) -> usize {
//         period + period * MAX_MEMORY_READS_PER_CYCLE
//     }
//
//     #[inline(always)]
//     fn append_read(&mut self, value: (u32, (u32, u32))) {
//         debug_assert!(self.reads.len() < Self::get_max_reads_len(self.period));
//         unsafe { self.reads.extend_one_unchecked(value) }
//     }
// }
//
// impl<C: Counters> riscv_transpiler::vm::Snapshotter<C> for OnceSnapshotter {
//     #[inline(always)]
//     fn take_snapshot_if_needed(&mut self, state: &State<C>) -> bool {
//         let cycles_executed =
//             ((state.timestamp - self.initial_timestamp) / TIMESTAMP_STEP) as usize;
//         self.period <= cycles_executed
//     }
//
//     #[inline(always)]
//     fn take_final_snapshot(&mut self, _state: &State<C>) {}
//
//     #[inline(always)]
//     fn append_arbitrary_value(&mut self, value: u32) {
//         self.append_read((value, (0, 0)));
//     }
//
//     #[inline(always)]
//     fn append_memory_read(
//         &mut self,
//         _address: u32,
//         read_value: u32,
//         read_timestamp: TimestampScalar,
//         _write_timestamp: TimestampScalar,
//     ) {
//         let read_timestamp = (read_timestamp as u32, (read_timestamp >> 32) as u32);
//         let value = (read_value, read_timestamp);
//         self.append_read(value);
//     }
// }

pub(crate) trait DataTraceRanges {}

pub(crate) struct Snapshot<R: DataTraceRanges> {
    pub index: usize,
    pub cycles_count: usize,
    pub initial_state: MachineState,
    pub trace: Box<TraceChunk>,
    pub trace_ranges: R,
}

unsafe impl<R: DataTraceRanges> Send for Snapshot<R> {}

pub(crate) struct PtrRange<T> {
    pub start: *mut T,
    pub end: *mut T,
    pub _chunk: Option<Arc<Vec<T, A>>>,
}

impl<T> Default for PtrRange<T> {
    fn default() -> Self {
        Self {
            start: std::ptr::null_mut(),
            end: std::ptr::null_mut(),
            _chunk: None,
        }
    }
}

unsafe impl<T> Send for PtrRange<T> {}

#[derive(Default)]
pub(crate) struct SplitDataTraceRanges {
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

impl DataTraceRanges for SplitDataTraceRanges {}

#[derive(Default)]
pub(crate) struct UnifiedDataTraceRanges {
    pub blake_calls: VecDeque<PtrRange<Blake2sRoundFunctionDelegationWitness>>,
    pub bigint_calls: VecDeque<PtrRange<BigintDelegationWitness>>,
    pub keccak_calls: VecDeque<PtrRange<KeccakSpecial5DelegationWitness>>,
    pub cycles: VecDeque<PtrRange<UnifiedOpcodeTracingDataWithTimestamp>>,
}

impl DataTraceRanges for UnifiedDataTraceRanges {}

#[cfg(test)]
mod tests {

    // #[test]
    // fn test_snapshotter() {
    //     let binary_image = read_binary(&Path::new("../examples/hashed_fibonacci/app.bin"));
    //     let text_section = read_binary(&Path::new("../examples/hashed_fibonacci/app.text"));
    //     // let mut non_determinism_source = QuasiUARTSource::new_with_reads(vec![1 << 24, 0]);
    //     let mut non_determinism_source = QuasiUARTSource::new_with_reads(vec![0, 1 << 18]);
    //     let mut ram = RamWithRomRegion::<30>::new(&binary_image);
    //     let preprocessed_bytecode = preprocess_bytecode::<FullMachineDecoderConfig>(&text_section);
    //     let tape = SimpleTape::new(&preprocessed_bytecode);
    //     type CountersT = DelegationsAndFamiliesCounters;
    //     let mut state = State::initial_with_counters(CountersT::default());
    //     let mut snapshotters = vec![];
    //     let now = std::time::Instant::now();
    //     loop {
    //         const PERIOD: usize = 1 << 20;
    //         let mut snapshotter = OnceSnapshotter::new_for_period(PERIOD, &state);
    //         let is_program_finished = VM::run_basic_unrolled(
    //             &mut state,
    //             &mut ram,
    //             &mut snapshotter,
    //             &tape,
    //             PERIOD,
    //             &mut non_determinism_source,
    //         );
    //         snapshotters.push(snapshotter);
    //         if is_program_finished {
    //             break;
    //         }
    //     }
    //     let elapsed = now.elapsed();
    //     let cycles = (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;
    //     let mhz = cycles as f64 / elapsed.as_micros() as f64;
    //     println!(
    //         "Execution of {cycles} cycles finished in {:?} @ {} MHz",
    //         elapsed, mhz
    //     );
    //     println!(
    //         "Total reads count: {}",
    //         snapshotters.iter().map(|s| s.reads.len()).sum::<usize>()
    //     );
    //     let now = std::time::Instant::now();
    //     let count = ram.get_touched_words_count();
    //     println!(
    //         "Touched memory words: {} Counted in {:?}",
    //         count,
    //         now.elapsed()
    //     );
    // }
}
