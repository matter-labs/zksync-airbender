use super::*;
use crate::tracing::{SplitTracingType, UnifiedTracingType};
use crate::workers::simulation::run_replayer;
use common_constants::TimestampScalar;
use crossbeam_channel::unbounded;
use execution_prover_model::allocator::CpuTraceAllocator;
use execution_prover_model::circuit_type::UnrolledCircuitType;
use execution_prover_model::trace::{TracingDataHost, UnrolledTracingDataHost};
use riscv_transpiler::ir::simple_instruction_set::preprocess_bytecode;
use riscv_transpiler::ir::{
    FullMachineDecoderConfig, FullUnsignedMachineDecoderConfig, ReducedMachineDecoderConfig,
};
use riscv_transpiler::jit::{CounterType, MachineCounters};
use riscv_transpiler::vm::{FlatResponsesSource, RamPeek, SimpleTape, State};
use riscv_transpiler::witness::UnifiedOpcodeTracingDataWithTimestamp;
use std::alloc::Global;
use std::sync::atomic::Ordering;

pub(crate) const HALT: u32 = 0x0000_006f;
pub(crate) const RAM_BASE: u32 = common_constants::ROM_BYTE_SIZE as u32;
const UNIFIED: CircuitType = CircuitType::Unrolled(UnrolledCircuitType::Unified);
type Allocator = CpuTraceAllocator;
type VmState = State<MachineCounters>;

pub(crate) fn lui(rd: u32, value: u32) -> u32 {
    assert_eq!(value & 0xfff, 0);
    value | (rd << 7) | 0x37
}

pub(crate) fn addi(rd: u32, rs1: u32, imm: u32) -> u32 {
    (imm << 20) | (rs1 << 15) | (rd << 7) | 0x13
}

fn lw(rd: u32, rs1: u32, offset: u32) -> u32 {
    (offset << 20) | (rs1 << 15) | (2 << 12) | (rd << 7) | 0x03
}

pub(crate) fn sw(rs2: u32, rs1: u32, offset: u32) -> u32 {
    assert!(offset < 32);
    (rs2 << 20) | (rs1 << 15) | (2 << 12) | (offset << 7) | 0x23
}

pub(crate) fn nd_read(rd: u32) -> u32 {
    (common_constants::NON_DETERMINISM_CSR << 20) | (1 << 12) | (rd << 7) | 0x73
}

pub(crate) fn nd_write(rs1: u32) -> u32 {
    (common_constants::NON_DETERMINISM_CSR << 20) | (rs1 << 15) | (1 << 12) | 0x73
}

#[derive(Debug, PartialEq, Eq)]
struct Piece {
    initial: VmState,
    final_state: VmState,
    cycles: usize,
    reads: usize,
}

#[derive(Debug, PartialEq, Eq)]
struct Observed {
    pieces: Vec<Piece>,
    reads: Vec<(u32, TimestampScalar)>,
    rows: Vec<UnifiedOpcodeTracingDataWithTimestamp>,
}

pub(crate) struct Simulator {
    tape: Arc<SimpleTape>,
    text: Arc<Box<[u32]>>,
    image: Option<Arc<Box<[u32]>>>,
    machine_type: MachineType,
    #[cfg(target_arch = "x86_64")]
    assume_canonical_mop_inputs: bool,
    circuit: CircuitType,
    ram_config: JitRunnerRam,
    pub(crate) memory: Box<MemoryHolder>,
}

impl Simulator {
    pub(crate) fn new(text: &[u32]) -> Self {
        Self::with_config(text, UNIFIED, JitRunnerRam::Tiny)
    }

    fn with_config(text: &[u32], circuit: CircuitType, ram_config: JitRunnerRam) -> Self {
        Self::with_machine(text, circuit, ram_config, MachineType::Reduced)
    }

    fn with_machine(
        text: &[u32],
        circuit: CircuitType,
        ram_config: JitRunnerRam,
        machine_type: MachineType,
    ) -> Self {
        let instructions = match machine_type {
            MachineType::Full => preprocess_bytecode::<FullMachineDecoderConfig, true>(text),
            MachineType::FullUnsigned => {
                preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(text)
            }
            MachineType::Reduced => preprocess_bytecode::<ReducedMachineDecoderConfig, true>(text),
        };
        Self {
            tape: Arc::new(SimpleTape::new(&instructions)),
            text: Arc::new(text.into()),
            image: None,
            machine_type,
            #[cfg(target_arch = "x86_64")]
            assume_canonical_mop_inputs: false,
            circuit,
            ram_config,
            memory: MemoryHolder::allocate_zeroed(ram_config, Global),
        }
    }

    fn produce<ND: NonDeterminismCSRSource + Send + 'static>(
        &mut self,
        source: ND,
        cap: Option<u32>,
        jit: bool,
        abort: bool,
        allocator_bytes: usize,
    ) -> Produced<ND, UnifiedTracingType> {
        self.produce_for(
            source,
            cap,
            jit,
            Arc::new(AtomicBool::new(abort)),
            allocator_bytes,
        )
    }

    fn produce_for<ND, T>(
        &mut self,
        source: ND,
        cap: Option<u32>,
        jit: bool,
        abort: Arc<AtomicBool>,
        allocator_bytes: usize,
    ) -> Produced<ND, T>
    where
        ND: NonDeterminismCSRSource + Send + 'static,
        T: TracingType<Allocator> + 'static,
    {
        let (free_tx, free_rx) = unbounded();
        for _ in 0..2 {
            free_tx
                .send(unsafe { Box::<TraceChunk>::new_zeroed().assume_init() })
                .unwrap();
        }
        let (snapshot_tx, snapshots) = unbounded();
        let (results_tx, results) = unbounded();
        let (allocators_tx, allocators) = unbounded();
        for _ in 0..4 {
            allocators_tx.send(Allocator::new(allocator_bytes)).unwrap();
        }
        let runner = SimulationRunner::<_, T, _, _>::new(
            0,
            self.machine_type,
            self.circuit,
            source,
            free_tx.clone(),
            free_rx.clone(),
            snapshot_tx,
            results_tx.clone(),
            allocators,
            abort.clone(),
            None,
            self.ram_config,
            #[cfg(target_arch = "x86_64")]
            self.assume_canonical_mop_inputs,
        );
        let image = self.image.as_ref().unwrap_or(&self.text);

        #[cfg(target_arch = "x86_64")]
        let runner = if jit {
            runner.run(
                image.clone(),
                self.text.clone(),
                cap,
                Arc::new(Mutex::new(TypeMap::new())),
                &mut self.memory,
            )
        } else {
            let mut runner = runner;
            runner.run_vm(image, &self.tape, cap, &mut self.memory);
            runner
        };
        #[cfg(not(target_arch = "x86_64"))]
        let mut runner = runner;
        #[cfg(not(target_arch = "x86_64"))]
        {
            assert!(!jit);
            runner.run_vm(image, &self.tape, cap, &mut self.memory);
        }

        Produced {
            snapshots,
            free_tx,
            free_rx,
            results_tx,
            results,
            abort,
            is_aborted: runner.is_aborted,
            source: runner.non_determinism_source,
        }
    }

    pub(crate) fn run_vm<ND: NonDeterminismCSRSource + Send + 'static>(
        &mut self,
        source: ND,
    ) -> (ND, VmState, Vec<(u32, TimestampScalar)>) {
        let (source, observed) = self.observe(source, None, false);
        (
            source,
            observed.pieces.last().unwrap().final_state,
            observed.reads,
        )
    }

    fn observe<ND: NonDeterminismCSRSource + Send + 'static>(
        &mut self,
        source: ND,
        cap: Option<u32>,
        jit: bool,
    ) -> (ND, Observed) {
        self.produce(source, cap, jit, false, 4096)
            .replay(self.circuit.rom(), self.tape.clone())
    }
}

struct Produced<ND, T: TracingType<Allocator>> {
    snapshots: Receiver<Snapshot<T::Ranges, Box<TraceChunk>>>,
    free_tx: Sender<Box<TraceChunk>>,
    free_rx: Receiver<Box<TraceChunk>>,
    results_tx: Sender<WorkerResult<Allocator>>,
    results: Receiver<WorkerResult<Allocator>>,
    abort: Arc<AtomicBool>,
    is_aborted: bool,
    source: ND,
}

impl<ND, T: TracingType<Allocator>> Produced<ND, T> {
    fn replay(self, rom: RomGeometry, tape: Arc<SimpleTape>) -> (ND, Observed) {
        assert!(!self.is_aborted);
        let mut reads = Vec::new();
        let mut pieces = Vec::new();
        let (snapshot_tx, snapshots) = unbounded();
        for snapshot in self.snapshots {
            let (values, timestamps) = snapshot.trace.data();
            reads.extend(values.iter().copied().zip(timestamps.iter().copied()));
            pieces.push(Piece {
                initial: snapshot.initial_state.into(),
                final_state: snapshot.final_state.into(),
                cycles: snapshot.cycles_count,
                reads: values.len(),
            });
            snapshot_tx.send(snapshot).unwrap();
        }
        drop(snapshot_tx);
        assert!(!pieces.is_empty());
        run_replayer::<T, Allocator, _>(
            0,
            0,
            rom,
            tape,
            snapshots,
            self.free_tx,
            self.results_tx,
            self.abort,
        );
        assert_eq!(self.free_rx.len(), 2);
        let mut rows = Vec::new();
        let mut produced = 0;
        let mut replayed = Vec::new();
        for result in self.results {
            match result {
                WorkerResult::SnapshotProduced => produced += 1,
                WorkerResult::SnapshotReplayed(index) => replayed.push(index),
                WorkerResult::TracingData(data) => {
                    use UnifiedOpcodeTracingDataWithTimestamp::{Mem, NonMem};
                    match data.tracing_data {
                        TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(trace)) => {
                            rows.extend(
                                trace.chunks.iter().flat_map(|chunk| chunk.iter().copied()),
                            );
                        }
                        TracingDataHost::Unrolled(UnrolledTracingDataHost::Memory(trace)) => {
                            rows.extend(
                                trace
                                    .chunks
                                    .iter()
                                    .flat_map(|chunk| chunk.iter().copied().map(Mem)),
                            );
                        }
                        TracingDataHost::Unrolled(UnrolledTracingDataHost::NonMemory(trace)) => {
                            rows.extend(
                                trace
                                    .chunks
                                    .iter()
                                    .flat_map(|chunk| chunk.iter().copied().map(NonMem)),
                            );
                        }
                        TracingDataHost::Delegation(_) => {}
                    }
                }
                _ => {}
            }
        }
        assert_eq!(produced, pieces.len());
        assert_eq!(replayed, (0..produced).collect::<Vec<_>>());
        assert_eq!(
            rows.len(),
            pieces.iter().map(|piece| piece.cycles).sum::<usize>()
        );
        (
            self.source,
            Observed {
                pieces,
                reads,
                rows,
            },
        )
    }
}

fn memory_program() -> [u32; 12] {
    [
        lui(1, RAM_BASE),
        addi(2, 0, 19),
        sw(2, 1, 0),
        addi(2, 0, 31),
        sw(2, 1, 4),
        lw(3, 1, 0),
        lw(4, 1, 4),
        lw(5, 1, 8),
        lw(6, 1, 12),
        nd_read(7),
        nd_read(8),
        HALT,
    ]
}

fn responses() -> FlatResponsesSource {
    FlatResponsesSource::new_with_reads(vec![41, 53])
}

#[test]
fn simulator_snapshot() {
    let mut simulator = Simulator::new(&memory_program());
    let (_, trace) = simulator.observe(responses(), None, false);
    assert_eq!(trace.pieces.len(), 1);
    let piece = &trace.pieces[0];
    assert_eq!(piece.initial, MachineState::initial().into());
    assert_eq!(piece.cycles, 12);
    assert_eq!(piece.final_state.pc, 44);
    assert_eq!(piece.final_state.timestamp, 52);
    assert_eq!(
        trace.reads,
        [
            (0, 0),
            (0, 0),
            (19, 14),
            (31, 22),
            (0, 0),
            (0, 0),
            (41, 0),
            (53, 0)
        ]
    );
    let state = piece.final_state;
    assert_eq!(state.registers[3].value, 19);
    assert_eq!(state.registers[4].value, 31);
    assert_eq!(state.registers[7].value, 41);
    assert_eq!(state.registers[8].value, 53);
    assert_eq!(state.counters.values[..6], [5, 1, 0, 0, 6, 0]);
    assert!(state.counters.values[6..].iter().all(|&count| count == 0));
    assert_eq!(
        trace
            .rows
            .iter()
            .map(|row| row.initial_pc())
            .collect::<Vec<_>>(),
        (0..48).step_by(4).collect::<Vec<_>>(),
    );
    let index = RAM_BASE as usize / 4;
    let (memory, timestamps) = simulator.memory.memory_and_timestamps_mut();
    assert_eq!(&memory[index..index + 4], &[19, 31, 0, 0]);
    assert_eq!(&timestamps[index..index + 4], &[25, 29, 33, 37]);
}

#[cfg(target_arch = "x86_64")]
#[test]
fn simulator_snapshot_matches_jit() {
    for cap in [Some(5), Some(6), Some(9), None] {
        assert_snapshot_matches_jit(JitRunnerRam::Tiny, cap);
    }
}

#[cfg(target_arch = "x86_64")]
#[test]
#[ignore = "allocates two Medium RAM holders"]
fn simulator_medium_ram_snapshot_matches_jit() {
    assert_snapshot_matches_jit(JitRunnerRam::Medium, Some(6));
}

#[cfg(target_arch = "x86_64")]
fn assert_snapshot_matches_jit(ram: JitRunnerRam, cap: Option<u32>) {
    let program = memory_program();
    let mut vm = Simulator::with_config(&program, UNIFIED, ram);
    let mut jit = Simulator::with_config(&program, UNIFIED, ram);
    let (_, vm_trace) = vm.observe(responses(), cap, false);
    let (_, jit_trace) = jit.observe(responses(), cap, true);
    assert_eq!(vm_trace, jit_trace, "{ram:?} at cap {cap:?}");
    let vm_memory = vm.memory.memory_and_timestamps_mut();
    let jit_memory = jit.memory.memory_and_timestamps_mut();
    assert!(vm_memory == jit_memory, "{ram:?} at cap {cap:?}");
    if cap == Some(6) {
        let piece = &vm_trace.pieces[0];
        assert_eq!(piece.cycles, 9);
        assert_eq!(piece.final_state.pc, 36);
        assert_eq!(piece.final_state.timestamp, 40);
        assert_eq!(
            piece.final_state.counters.values[CounterType::MemWord as usize],
            6
        );
        assert_eq!(
            vm_trace.reads,
            [(0, 0), (0, 0), (19, 14), (31, 22), (0, 0), (0, 0)]
        );
    }
}

#[test]
fn simulator_cap_and_abort() {
    const BEQ_X0_SELF: u32 = 0x0000_0063;
    let mut simulator = Simulator::new(&[BEQ_X0_SELF]);
    let finished = simulator.produce((), Some(5), false, false, 4096);
    let snapshot = finished.snapshots.try_recv().unwrap();
    let state: VmState = snapshot.final_state.into();
    assert_eq!(snapshot.cycles_count, 5);
    assert_eq!(state.pc, 0);
    assert_eq!(state.timestamp, 24);
    assert_eq!(state.counters.values[CounterType::BranchSlt as usize], 5);
    assert!(snapshot.trace.data().0.is_empty());
    assert!(finished.snapshots.try_recv().is_err());

    let mut simulator = Simulator::new(&[HALT]);
    let (_, stopped) = simulator.observe((), Some(0), false);
    assert_eq!(stopped.pieces.len(), 1);
    assert_eq!(
        stopped.pieces[0].final_state,
        MachineState::initial().into()
    );
    assert!(stopped.reads.is_empty());

    let aborted = simulator.produce((), None, false, true, 4096);
    assert!(aborted.is_aborted);
    assert_eq!(aborted.free_rx.len(), 2);
    assert!(aborted.snapshots.try_recv().is_err());
    assert!(aborted.results.try_recv().is_err());
}

#[test]
fn simulator_aborts_at_full_trace_piece() {
    use riscv_transpiler::jit::TRACE_CHUNK_LEN;

    struct AbortOnRead {
        flag: Arc<AtomicBool>,
        reads: usize,
    }

    impl NonDeterminismCSRSource for AbortOnRead {
        fn read(&mut self) -> u32 {
            self.reads += 1;
            self.flag.store(true, Ordering::Relaxed);
            19
        }

        fn write_with_memory_access<R: RamPeek + ?Sized>(&mut self, _: &R, _: u32) {
            unreachable!()
        }

        fn write_with_memory_access_raw(&mut self, _: &[u32], _: u32) {
            unreachable!()
        }

        fn write_with_memory_access_dyn(&mut self, _: &dyn RamPeek, _: u32) {
            unreachable!()
        }
    }

    const JAL_BACK_EIGHT: u32 = 0xff9f_f06f;
    let mut simulator =
        Simulator::new(&[lui(1, RAM_BASE), nd_read(2), sw(2, 1, 0), JAL_BACK_EIGHT]);
    let abort = Arc::new(AtomicBool::new(false));
    let source = AbortOnRead {
        flag: abort.clone(),
        reads: 0,
    };
    let iterations = TRACE_CHUNK_LEN / 2;
    let cap = Some((1 + 3 * (iterations + 1)) as u32);
    let aborted = simulator.produce_for::<_, UnifiedTracingType>(source, cap, false, abort, 4096);
    assert!(aborted.is_aborted);
    assert_eq!(aborted.source.reads, iterations);
    assert_eq!(simulator.memory.memory()[RAM_BASE as usize / 4], 19);
    assert_eq!(aborted.free_rx.len(), 2);
    assert!(aborted.snapshots.try_recv().is_err());
    assert!(aborted.results.try_recv().is_err());
}

#[test]
fn simulator_blake_rounds() {
    use common_constants::delegation_types::blake2s_with_control::{
        BLAKE2S_DELEGATION_CSR_REGISTER, BLAKE2S_NUM_CONTROL_BITS,
    };

    let delegation = BLAKE2S_DELEGATION_CSR_REGISTER << 20 | 0x1073;
    for rounds in [7, 10] {
        let control = u32::from(rounds == 7);
        let x12 = ((1 << BLAKE2S_NUM_CONTROL_BITS) | control) << 16;
        let mut program = vec![lui(10, RAM_BASE), addi(11, 10, 128), lui(12, x12)];
        program.extend(std::iter::repeat_n(delegation, rounds));
        program.push(HALT);
        let cap = Some(4);
        let mut vm = Simulator::new(&program);
        let (_, trace) = vm.observe((), cap, false);
        let state = trace.pieces[0].final_state;
        assert_eq!(trace.pieces[0].cycles, 3 + rounds);
        assert_eq!(state.pc, 4 * (3 + rounds) as u32);
        assert_eq!(
            state.timestamp,
            INITIAL_TIMESTAMP + (3 + rounds) as u64 * TIMESTAMP_STEP
        );
        assert_eq!(
            state.counters.values[CounterType::BlakeDelegation as usize],
            rounds as u64
        );
        assert_eq!(trace.reads.len(), 40);
        assert_eq!(state.registers[12].timestamp, state.timestamp - 1);
        #[cfg(target_arch = "x86_64")]
        {
            let mut jit = Simulator::new(&program);
            let (_, reference) = jit.observe((), cap, true);
            assert_eq!(trace, reference);
            assert!(
                vm.memory.memory_and_timestamps_mut() == jit.memory.memory_and_timestamps_mut()
            );
        }
    }
}

#[test]
fn simulator_rollover() {
    use riscv_transpiler::jit::TRACE_CHUNK_LEN;
    use std::mem::size_of;

    for exact in [true, false] {
        let base = RAM_BASE;
        let mut program = vec![lui(1, base), addi(2, 0, 19), sw(2, 1, 0)];
        if exact {
            program.extend([lw(7, 1, 0), lw(8, 1, 4), lw(9, 1, 8)]);
        }
        let head = program.len() as u32 * 4;
        program.extend([
            lw(3, 1, 0),
            lw(4, 1, 4),
            lw(5, 1, 8),
            lw(6, 1, 12),
            0xff1f_f06f,
        ]);
        let groups = TRACE_CHUNK_LEN / 4 - usize::from(exact);
        let first_cycles = head as usize / 4 + groups * 5 - 1;
        let cycles = first_cycles + if exact { 0 } else { 5 };
        let cap = Some(cycles as u32);
        let allocator_bytes = cycles * size_of::<UnifiedOpcodeTracingDataWithTimestamp>();
        let mut vm = Simulator::new(&program);
        let (_, trace) = vm
            .produce((), cap, false, false, allocator_bytes)
            .replay(vm.circuit.rom(), vm.tape.clone());
        assert_eq!(trace.pieces.len(), 2);
        let [first, final_piece] = trace.pieces.as_slice() else {
            unreachable!()
        };
        assert_eq!(first.reads, TRACE_CHUNK_LEN + usize::from(!exact));
        assert_eq!(first.cycles, first_cycles);
        assert_eq!(first.final_state.pc, head + 16);
        assert_eq!(first.final_state, final_piece.initial);
        if exact {
            assert_eq!((final_piece.cycles, final_piece.reads), (0, 0));
            assert_eq!(final_piece.initial, final_piece.final_state);
        } else {
            assert_eq!((final_piece.cycles, final_piece.reads), (5, 4));
            assert_eq!(final_piece.final_state.pc, head + 16);
            assert_eq!(
                final_piece.final_state.timestamp,
                first.final_state.timestamp + 5 * TIMESTAMP_STEP
            );
            assert_eq!(
                trace.rows[first_cycles..]
                    .iter()
                    .map(|row| row.initial_pc())
                    .collect::<Vec<_>>(),
                [head + 16, head, head + 4, head + 8, head + 12]
            );
        }
        assert_eq!(trace.reads.len(), first.reads + final_piece.reads);
        assert_eq!(trace.reads[0], (0, 0));
        let (group_reads, remainder) = trace.reads[if exact { 4 } else { 1 }..].as_chunks::<4>();
        assert!(remainder.is_empty());
        for (i, reads) in group_reads.iter().enumerate() {
            let ts = INITIAL_TIMESTAMP + (head as u64 / 4 + i as u64 * 5) * TIMESTAMP_STEP;
            let value_timestamp = if i == 0 {
                if exact {
                    17
                } else {
                    14
                }
            } else {
                ts - 5 * TIMESTAMP_STEP + 1
            };
            assert_eq!(reads[0], (19, value_timestamp));
            for (slot, read) in reads.iter().enumerate().skip(1) {
                let previous = if i == 0 {
                    if exact && slot <= 2 {
                        17 + slot as u64 * 4
                    } else {
                        0
                    }
                } else {
                    ts - 5 * TIMESTAMP_STEP + slot as u64 * TIMESTAMP_STEP + 1
                };
                assert_eq!(*read, (0, previous));
            }
        }
        #[cfg(target_arch = "x86_64")]
        {
            let mut jit = Simulator::new(&program);
            let (_, reference) = jit
                .produce((), cap, true, false, allocator_bytes)
                .replay(jit.circuit.rom(), jit.tape.clone());
            assert_eq!(trace.pieces, reference.pieces);
            assert!(trace.reads == reference.reads);
            assert!(trace.rows == reference.rows);
        }
    }
}

#[test]
fn simulator_split_mop_and_rev8() {
    use field::PrimeField;

    const MOP_ADD_X3_X1_X2: u32 =
        (0b1000001 << 25) | (2 << 20) | (1 << 15) | (4 << 12) | (3 << 7) | 0x73;
    const REV8_X4_X3: u32 = (0x698 << 20) | (3 << 15) | (5 << 12) | (4 << 7) | 0x13;
    for machine_type in [MachineType::Full, MachineType::FullUnsigned] {
        for (a, b) in [(0x0345_6000, 0x0567_8000), (0xdead_b000, 0x1234_5000)] {
            let program = [lui(1, a), lui(2, b), MOP_ADD_X3_X1_X2, REV8_X4_X3, HALT];
            let mut vm =
                Simulator::with_machine(&program, UNIFIED, JitRunnerRam::Tiny, machine_type);
            let (_, trace) = vm
                .produce_for::<_, SplitTracingType>((), None, false, Arc::default(), 4096)
                .replay(vm.circuit.rom(), vm.tape.clone());
            let state = trace.pieces[0].final_state;
            let sum = ((u64::from(a) + u64::from(b))
                % u64::from(crate::upstream::BF::CHARACTERISTICS_U32)) as u32;
            assert_eq!(state.registers[3].value, sum);
            assert_eq!(state.registers[4].value, sum.swap_bytes());
            assert_eq!(state.counters.values[..6], [3, 1, 1, 0, 0, 0]);
            #[cfg(target_arch = "x86_64")]
            {
                let mut jit =
                    Simulator::with_machine(&program, UNIFIED, JitRunnerRam::Tiny, machine_type);
                jit.assume_canonical_mop_inputs =
                    u64::from(a) < u64::from(crate::upstream::BF::CHARACTERISTICS_U32);
                let (_, reference) = jit
                    .produce_for::<_, SplitTracingType>((), None, true, Arc::default(), 4096)
                    .replay(jit.circuit.rom(), jit.tape.clone());
                assert_eq!(trace, reference);
            }
        }
    }
}

#[test]
fn simulator_wrap_rom_and_image_reuse() {
    use common_constants::rom::L1_WRAP_ROM;

    let wrap_boundary = L1_WRAP_ROM.byte_size() as u32;
    let long_image_word = L1_WRAP_ROM.word_size() + 1;
    let program = [
        lui(1, wrap_boundary),
        addi(2, 0, 19),
        sw(2, 1, 0),
        lw(3, 1, 0),
        HALT,
    ];

    let mut simulator = Simulator::new(&[lw(5, 0, 0), lw(6, 0, 0), HALT]);
    let mut image = vec![0; long_image_word + 1];
    image[0] = 0x1234;
    image[long_image_word] = 0xdead_beef;
    simulator.image = Some(Arc::new(image.into_boxed_slice()));
    let (_, regular) = simulator.observe((), None, false);
    assert_eq!(regular.reads, [(0x1234, 0), (0x1234, 5)]);
    for row in &regular.rows[..2] {
        assert_eq!(row.rs2_or_mem_load_read_value(), 0);
    }
    assert_eq!(regular.pieces[0].final_state.registers[6].value, 0x1234);
    assert_eq!(simulator.memory.memory()[long_image_word], 0xdead_beef);

    simulator.circuit = CircuitType::L1Wrap21;
    simulator.image = None;
    simulator.text = Arc::new(Box::new(program));
    simulator.tape = Arc::new(SimpleTape::new(&preprocess_bytecode::<
        ReducedMachineDecoderConfig,
        true,
    >(&program)));
    let (_, final_state, reads) = simulator.run_vm(());
    assert_eq!(reads, [(0, 0), (19, 14)]);
    assert_eq!(final_state.registers[3].value, 19);
    assert_eq!(simulator.memory.memory()[long_image_word], 0);
    assert_eq!(simulator.memory.memory()[L1_WRAP_ROM.word_size()], 19);
}

#[test]
#[should_panic(expected = "VM PC 0x00000004 is outside the instruction tape (length 1)")]
fn simulator_rejects_pc_outside_tape() {
    const JAL_FORWARD_FOUR: u32 = 0x0040_006f;
    Simulator::new(&[JAL_FORWARD_FOUR]).run_vm(());
}

#[test]
#[should_panic(expected = "VM RAM write to ROM at 0x0007fffc")]
fn simulator_rejects_wrap_rom_write() {
    let program = [lui(1, 0x8_0000), addi(1, 1, 0xffc), sw(0, 1, 0), HALT];
    Simulator::with_config(&program, CircuitType::L1Wrap21, JitRunnerRam::Tiny).run_vm(());
}

#[test]
#[should_panic(expected = "VM RAM address out of bounds: 0x02000000 (RAM size 0x2000000 bytes)")]
fn simulator_rejects_out_of_ram_load() {
    let program = [
        lui(1, JitRunnerRam::Tiny.ram_size() as u32),
        lw(2, 1, 0),
        HALT,
    ];
    Simulator::new(&program).run_vm(());
}

#[test]
fn simulator_keccak() {
    use common_constants::delegation_types::keccak_f1600::{
        keccak_f1600_call_csr, KECCAK_F1600_ACCESSED_SLOTS, KECCAK_F1600_FINAL_CONTROL_VALUE,
        KECCAK_F1600_INITIAL_CONTROL_VALUE, NUM_KECCAK_F1600_CALLS,
    };

    let mut program = vec![
        addi(10, 0, KECCAK_F1600_INITIAL_CONTROL_VALUE),
        lui(11, RAM_BASE),
    ];
    program
        .extend((0..NUM_KECCAK_F1600_CALLS).map(|idx| keccak_f1600_call_csr(idx) << 20 | 0x1073));
    program.push(HALT);
    let cap = Some(3);
    let mut vm = Simulator::new(&program);
    let (_, trace) = vm
        .produce((), cap, false, false, 64 << 10)
        .replay(vm.circuit.rom(), vm.tape.clone());
    let state = trace.pieces[0].final_state;
    assert_eq!(trace.pieces[0].cycles, 2 + NUM_KECCAK_F1600_CALLS);
    assert_eq!(state.registers[10].value, KECCAK_F1600_FINAL_CONTROL_VALUE);
    assert_eq!(
        state.counters.values[CounterType::KeccakF1600Delegation as usize],
        NUM_KECCAK_F1600_CALLS as u64,
    );
    assert_eq!(trace.reads, vec![(0, 0); KECCAK_F1600_ACCESSED_SLOTS * 2]);
    #[cfg(target_arch = "x86_64")]
    {
        let mut jit = Simulator::new(&program);
        let (_, reference) = jit
            .produce((), cap, true, false, 64 << 10)
            .replay(jit.circuit.rom(), jit.tape.clone());
        assert_eq!(trace, reference);
        assert!(vm.memory.memory_and_timestamps_mut() == jit.memory.memory_and_timestamps_mut());
    }
}
