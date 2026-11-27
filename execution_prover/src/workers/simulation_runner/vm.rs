use super::*;
use crate::upstream::BF;
use common_constants::rom::{L1_WRAP_ROM, REGULAR_ROM};
use common_constants::TimestampScalar;
use riscv_transpiler::ir::simple_instruction_set::InstructionName;
use riscv_transpiler::jit::{MachineCounters, TRACE_CHUNK_LEN};
use riscv_transpiler::vm::{InstructionTape, RamPeek, SimpleTape, Snapshotter, State, RAM, VM};
use std::cell::RefCell;

impl<
        ND: NonDeterminismCSRSource + Send + 'static,
        T: TracingType<A> + 'static,
        A: HostTraceAllocator + 'static,
        S: DerefMut<Target = TraceChunk> + Send + 'static,
    > SimulationRunner<ND, T, A, S>
{
    pub(in crate::workers) fn run_vm(
        &mut self,
        binary_image: &[u32],
        instruction_tape: &SimpleTape,
        cycles_bound: Option<u32>,
        memory_holder: &mut MemoryHolder,
    ) {
        let binary_image_len = binary_image.len();
        assert!(
            binary_image_len <= self.rom.word_size(),
            "the binary image ({binary_image_len} words) exceeds the circuit's {:?}",
            self.rom
        );
        let (memory, timestamps) = memory_holder.memory_and_timestamps_mut();
        memory[..binary_image_len].copy_from_slice(binary_image);
        memory[binary_image_len..ROM_WORD_SIZE].fill(0);
        let mut trace = self
            .free_trace_chunks_receiver
            .recv()
            .expect("must receive a trace chunk for simulation");
        trace.len = 0;
        self.trace = Some(trace);
        self.instant = Some(Instant::now());

        let timestamp_bound =
            cycles_bound.map(|cycles| INITIAL_TIMESTAMP + u64::from(cycles) * TIMESTAMP_STEP);
        let widths = instruction_tape.word_group_widths(self.ram_config);
        let rom = self.rom;
        let runner = RefCell::new(&mut *self);
        let mut sink = TraceSink(&runner);
        let mut nd = RunNonDeterminism {
            runner: &runner,
            index: 0,
        };
        if rom == L1_WRAP_ROM {
            run(
                &mut VmRam::<{ L1_WRAP_ROM.byte_size() }> { memory, timestamps },
                &mut sink,
                instruction_tape,
                &widths,
                timestamp_bound,
                &mut nd,
            );
        } else {
            run(
                &mut VmRam::<{ REGULAR_ROM.byte_size() }> { memory, timestamps },
                &mut sink,
                instruction_tape,
                &widths,
                timestamp_bound,
                &mut nd,
            );
        }
        if let Some(trace) = self.trace.take() {
            self.free_trace_chunks_sender
                .send(trace)
                .expect("simulation runner trace-return channel closed during teardown");
        }
        if !self.is_aborted {
            let batch_id = self.batch_id;
            let cycles_count = (self.state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;
            let elapsed_ms = self.total_elapsed.as_secs_f64() * 1000.0;
            let mhz = (cycles_count as f64) / (elapsed_ms * 1000.0);
            debug!("BATCH[{batch_id}] SIMULATOR finished execution with {cycles_count} cycles in {elapsed_ms:.3} ms @ {mhz:.3} MHz");
        }
    }
}

fn run<R: RAM, S: Snapshotter<MachineCounters>, ND: NonDeterminismCSRSource>(
    ram: &mut R,
    sink: &mut S,
    tape: &SimpleTape,
    widths: &[u8],
    timestamp_bound: Option<TimestampScalar>,
    nd: &mut ND,
) {
    let mut state = State::initial_with_counters(MachineCounters::default());
    while timestamp_bound.is_none_or(|bound| state.timestamp < bound) {
        let pc = state.pc;
        let width = *widths.get((pc / 4) as usize).unwrap_or_else(|| {
            panic!(
                "VM PC {pc:#010x} is outside the instruction tape (length {})",
                widths.len()
            )
        });
        for _ in 0..width {
            VM::<MachineCounters>::run_step::<_, _, _, BF>(&mut state, ram, sink, tape, nd);
            state.timestamp += TIMESTAMP_STEP;
        }
        if state.pc == pc && tape.read_instruction(pc).name == InstructionName::Jal {
            sink.take_final_snapshot(&state);
            return;
        }
        if sink.take_snapshot_if_needed(&state) {
            return;
        }
    }
    sink.take_final_snapshot(&state);
}

struct VmRam<'a, const ROM: usize> {
    memory: &'a mut [u32],
    timestamps: &'a mut [TimestampScalar],
}

impl<const ROM: usize> VmRam<'_, ROM> {
    fn word_index(&self, address: u32) -> usize {
        assert_eq!(address % 4, 0, "VM RAM unaligned address {address:#010x}");
        let index = (address / 4) as usize;
        assert!(
            index < self.memory.len(),
            "VM RAM address out of bounds: {address:#010x} (RAM size {:#x} bytes)",
            std::mem::size_of_val(self.memory)
        );
        index
    }
}

impl<const ROM: usize> RamPeek for VmRam<'_, ROM> {
    fn peek_word(&self, address: u32) -> u32 {
        self.memory[self.word_index(address)]
    }
}

impl<const ROM: usize> RAM for VmRam<'_, ROM> {
    const ROM_BYTE_SIZE: usize = ROM;

    fn read_word(&mut self, address: u32, timestamp: TimestampScalar) -> (TimestampScalar, u32) {
        let index = self.word_index(address);
        let value = self.memory[index];
        let previous = replace(&mut self.timestamps[index], timestamp | 1);
        (previous, value)
    }

    fn write_word(
        &mut self,
        address: u32,
        word: u32,
        timestamp: TimestampScalar,
    ) -> (TimestampScalar, u32) {
        let index = self.word_index(address);
        assert!(
            address as usize >= ROM,
            "VM RAM write to ROM at {address:#010x}"
        );
        let previous = replace(&mut self.timestamps[index], timestamp | 2);
        let value = replace(&mut self.memory[index], word);
        (previous, value)
    }

    fn mask_read_for_witness(&self, _address: &mut u32, _value: &mut u32) {}

    fn skip_if_replaying(&mut self, _num_snapshots: usize) {
        unreachable!("VM RAM is for simulation")
    }
}

struct TraceSink<'a, 'runner, C>(&'a RefCell<&'runner mut C>);

impl<
        ND: NonDeterminismCSRSource + Send + 'static,
        T: TracingType<A> + 'static,
        A: HostTraceAllocator + 'static,
        S: DerefMut<Target = TraceChunk> + Send + 'static,
    > Snapshotter<MachineCounters> for TraceSink<'_, '_, SimulationRunner<ND, T, A, S>>
{
    fn take_snapshot_if_needed(&mut self, state: &State<MachineCounters>) -> bool {
        let mut runner = self.0.borrow_mut();
        let trace = runner.trace.as_deref_mut().unwrap();
        if trace.len as usize >= TRACE_CHUNK_LEN {
            let ptr = NonNull::from(trace);
            runner.receive_trace(ptr, &MachineState::from(state));
        }
        runner.is_aborted
    }

    fn take_final_snapshot(&mut self, state: &State<MachineCounters>) {
        let mut runner = self.0.borrow_mut();
        let ptr = NonNull::from(runner.trace.as_deref_mut().unwrap());
        runner.receive_final_trace_piece(ptr, &MachineState::from(state));
    }

    fn append_arbitrary_value(&mut self, value: u32) {
        self.0
            .borrow_mut()
            .trace
            .as_deref_mut()
            .unwrap()
            .append_arbitrary_value(value);
    }

    fn append_memory_read(
        &mut self,
        _address: u32,
        read_value: u32,
        read_timestamp: TimestampScalar,
        _write_timestamp: TimestampScalar,
    ) {
        self.0
            .borrow_mut()
            .trace
            .as_deref_mut()
            .unwrap()
            .add_element(read_value, read_timestamp);
    }
}

struct RunNonDeterminism<'a, 'runner, C> {
    runner: &'a RefCell<&'runner mut C>,
    index: usize,
}

impl<
        ND: NonDeterminismCSRSource + Send + 'static,
        T: TracingType<A> + 'static,
        A: HostTraceAllocator + 'static,
        S: DerefMut<Target = TraceChunk> + Send + 'static,
    > NonDeterminismCSRSource for RunNonDeterminism<'_, '_, SimulationRunner<ND, T, A, S>>
{
    fn read(&mut self) -> u32 {
        if ND::PROVIDES_FLATTENED_NON_DETERMINISM {
            let word = self
                .runner
                .borrow()
                .non_determinism_source
                .read_flattened_word(self.index);
            self.index += 1;
            word
        } else {
            self.runner.borrow_mut().non_determinism_source.read()
        }
    }

    fn write_with_memory_access<R: RamPeek + ?Sized>(&mut self, ram: &R, value: u32) {
        if !ND::PROVIDES_FLATTENED_NON_DETERMINISM {
            self.runner
                .borrow_mut()
                .non_determinism_source
                .write_with_memory_access(ram, value);
        }
    }

    fn write_with_memory_access_raw(&mut self, _ram: &[u32], _value: u32) {
        unreachable!("VM nondeterminism uses RamPeek")
    }

    fn write_with_memory_access_dyn(&mut self, _ram: &dyn RamPeek, _value: u32) {
        unreachable!("VM nondeterminism uses RamPeek")
    }
}
