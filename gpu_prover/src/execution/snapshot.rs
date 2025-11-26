use crate::execution::simulation_runner::LockedBoxedTraceChunk;
use crate::execution::tracing::DataTraceRanges;
use riscv_transpiler::jit::MachineState;

pub(crate) struct Snapshot<R: DataTraceRanges> {
    pub index: usize,
    pub cycles_count: usize,
    pub initial_state: MachineState,
    pub trace: LockedBoxedTraceChunk,
    pub final_state: MachineState,
    pub trace_ranges: R,
}

unsafe impl<R: DataTraceRanges> Send for Snapshot<R> {}

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
