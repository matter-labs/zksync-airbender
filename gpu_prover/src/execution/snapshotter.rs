use super::A;
use crate::execution::simulation_runner::LockedBoxedTraceChunk;
use prover::risc_v_simulator::machine_mode_only_unrolled::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
    UnifiedOpcodeTracingDataWithTimestamp,
};
use riscv_transpiler::jit::MachineState;
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use std::collections::VecDeque;
use std::sync::Arc;

pub(crate) trait DataTraceRanges {}

pub(crate) struct Snapshot<R: DataTraceRanges> {
    pub index: usize,
    pub cycles_count: usize,
    pub initial_state: MachineState,
    pub trace: LockedBoxedTraceChunk,
    pub final_state: MachineState,
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
