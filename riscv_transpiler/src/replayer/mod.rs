use crate::ir::DelegationType;
use crate::ir::Instruction;
use crate::ir::InstructionName;
use crate::vm::Counters;
use crate::vm::InstructionTape;
use crate::vm::NonDeterminismCSRSource;
use crate::vm::State;
use crate::vm::RAM;
use crate::witness::WitnessTracer;
use common_constants::circuit_families::*;
use common_constants::TimestampScalar;
use common_constants::TIMESTAMP_STEP;
use risc_v_simulator::machine_mode_only_unrolled::TimestampData;

mod delegations;
mod instructions;

#[derive(Clone, Copy, Debug)]
pub struct ReplayerRam<'a, const ROM_BOUND_SECOND_WORD_BITS: usize> {
    pub ram_log: &'a [(u32, (u32, u32))],
}

#[derive(Clone, Copy, Debug)]
pub struct ReplayerNonDeterminism<'a> {
    pub non_determinism_reads_log: &'a [u32],
}

impl<'a, const ROM_BOUND_SECOND_WORD_BITS: usize> RAM
    for ReplayerRam<'a, ROM_BOUND_SECOND_WORD_BITS>
{
    fn peek_word(&self, address: u32) -> u32 {
        debug_assert_eq!(address % 4, 0);
        debug_assert!(self.ram_log.len() > 0);
        unsafe {
            let (value, _) = *self.ram_log.get_unchecked(0);

            value
        }
    }

    #[track_caller]
    #[inline(always)]
    fn read_word(&mut self, address: u32, timestamp: TimestampScalar) -> (TimestampScalar, u32) {
        debug_assert_eq!(address % 4, 0);
        debug_assert!(self.ram_log.len() > 0);
        unsafe {
            let (value, (low, high)) = *self.ram_log.get_unchecked(0);
            self.ram_log = core::mem::transmute(self.ram_log.get_unchecked(1..));
            let read_timestamp = (low as TimestampScalar) | ((high as TimestampScalar) << 32);
            debug_assert!(read_timestamp < timestamp, "trying to read replay log at address 0x{:08x} with timestamp {}, but read timestamp is {}", address, timestamp, read_timestamp);

            // println!("Read at address 0x{:08x} at timestamp {} into value {} and read timestamp {}", address, timestamp, value, read_timestamp);
            (read_timestamp, value)
        }
    }

    #[inline(always)]
    fn mask_read_for_witness(&self, address: &mut u32, value: &mut u32) {
        // we do not do anything here
        debug_assert_eq!(*address % 4, 0);
        if *address < 1 << (16 + ROM_BOUND_SECOND_WORD_BITS) {
            *address = 0u32;
            *value = 0u32;
        }
    }

    #[inline(always)]
    fn write_word(
        &mut self,
        address: u32,
        _word: u32,
        timestamp: TimestampScalar,
    ) -> (TimestampScalar, u32) {
        debug_assert_eq!(address % 4, 0);
        debug_assert!(self.ram_log.len() > 0);
        unsafe {
            let (old_value, (low, high)) = *self.ram_log.get_unchecked(0);
            self.ram_log = core::mem::transmute(self.ram_log.get_unchecked(1..));
            let read_timestamp = (low as TimestampScalar) | ((high as TimestampScalar) << 32);
            debug_assert!(read_timestamp < timestamp, "trying to write replay log at address 0x{:08x} with timestamp {}, but read timestamp is {}", address, timestamp, read_timestamp);

            // println!("Write at address 0x{:08x} at timestamp {} of value {} into value {} and read timestamp {}", address, timestamp, _word, old_value, read_timestamp);
            (read_timestamp, old_value)
        }
    }
}

impl<'a, R: RAM> NonDeterminismCSRSource<R> for ReplayerNonDeterminism<'a> {
    fn read(&mut self) -> u32 {
        debug_assert!(self.non_determinism_reads_log.len() > 0);
        unsafe {
            let value = *self.non_determinism_reads_log.get_unchecked(0);
            self.non_determinism_reads_log =
                core::mem::transmute(self.non_determinism_reads_log.get_unchecked(1..));

            value
        }
    }
    #[inline(always)]
    fn write_with_memory_access(&mut self, _ram: &R, _value: u32) {}
}

pub struct ReplayerVM<C: Counters> {
    pub state: State<C>,
}

impl<C: Counters> ReplayerVM<C> {
    pub fn replay_basic_unrolled<R: RAM, ND: NonDeterminismCSRSource<R>>(
        state: &mut State<C>,
        num_snapshots: usize,
        ram: &mut R,
        instruction_tape: &impl InstructionTape,
        snapshot_period: usize,
        nd: &mut ND,
        tracer: &mut impl WitnessTracer,
    ) {
        use crate::replayer::instructions::*;

        for _ in 0..num_snapshots {
            for _ in 0..snapshot_period {
                unsafe {
                    let pc = state.pc;
                    let instr = instruction_tape.read_instruction(pc);
                    match instr.name {
                        InstructionName::Illegal => illegal::<C, R>(state, ram, instr, tracer),
                        InstructionName::Lui => lui_auipc::lui::<C, R>(state, ram, instr, tracer),
                        InstructionName::Auipc => {
                            lui_auipc::auipc::<C, R>(state, ram, instr, tracer)
                        }

                        InstructionName::Jal => jal_jalr::jal::<C, R>(state, ram, instr, tracer),
                        InstructionName::Jalr => jal_jalr::jalr::<C, R>(state, ram, instr, tracer),

                        InstructionName::Slt => slt::slt::<C, R, false>(state, ram, instr, tracer),
                        InstructionName::Slti => slt::slt::<C, R, true>(state, ram, instr, tracer),

                        InstructionName::Sltu => {
                            slt::sltu::<C, R, false>(state, ram, instr, tracer)
                        }
                        InstructionName::Sltiu => {
                            slt::sltu::<C, R, true>(state, ram, instr, tracer)
                        }

                        InstructionName::Branch => {
                            branch::branch::<C, R>(state, ram, instr, tracer)
                        }

                        InstructionName::Sw => memory::sw::<C, R>(state, ram, instr, tracer),
                        InstructionName::Lw => memory::lw::<C, R>(state, ram, instr, tracer),

                        InstructionName::Sh => memory::sh::<C, R>(state, ram, instr, tracer),
                        InstructionName::Lhu => {
                            memory::lh::<C, R, false>(state, ram, instr, tracer)
                        }
                        InstructionName::Lh => memory::lh::<C, R, true>(state, ram, instr, tracer),

                        InstructionName::Sb => memory::sb::<C, R>(state, ram, instr, tracer),
                        InstructionName::Lbu => {
                            memory::lb::<C, R, false>(state, ram, instr, tracer)
                        }
                        InstructionName::Lb => memory::lb::<C, R, true>(state, ram, instr, tracer),

                        InstructionName::Add => {
                            add_sub::add_op::<C, R, false>(state, ram, instr, tracer)
                        }
                        InstructionName::Addi => {
                            add_sub::add_op::<C, R, true>(state, ram, instr, tracer)
                        }
                        InstructionName::Sub => add_sub::sub_op::<C, R>(state, ram, instr, tracer),
                        InstructionName::Xor => {
                            binary::xor::<C, R, false>(state, ram, instr, tracer)
                        }
                        InstructionName::Xori => {
                            binary::xor::<C, R, true>(state, ram, instr, tracer)
                        }
                        InstructionName::And => {
                            binary::and::<C, R, false>(state, ram, instr, tracer)
                        }
                        InstructionName::Andi => {
                            binary::and::<C, R, true>(state, ram, instr, tracer)
                        }
                        InstructionName::Or => {
                            binary::and::<C, R, false>(state, ram, instr, tracer)
                        }
                        InstructionName::Ori => {
                            binary::and::<C, R, true>(state, ram, instr, tracer)
                        }
                        InstructionName::Sll => {
                            shifts::sll::<C, R, false>(state, ram, instr, tracer)
                        }
                        InstructionName::Slli => {
                            shifts::sll::<C, R, true>(state, ram, instr, tracer)
                        }
                        InstructionName::Srl => {
                            shifts::srl::<C, R, false>(state, ram, instr, tracer)
                        }
                        InstructionName::Srli => {
                            shifts::srl::<C, R, true>(state, ram, instr, tracer)
                        }
                        InstructionName::Sra => {
                            shifts::sra::<C, R, false>(state, ram, instr, tracer)
                        }
                        InstructionName::Srai => {
                            shifts::sra::<C, R, true>(state, ram, instr, tracer)
                        }
                        InstructionName::Mul => mul_div::mul::<C, R>(state, ram, instr, tracer),
                        InstructionName::Mulhu => mul_div::mulhu::<C, R>(state, ram, instr, tracer),
                        InstructionName::Divu => mul_div::divu::<C, R>(state, ram, instr, tracer),
                        InstructionName::Remu => mul_div::remu::<C, R>(state, ram, instr, tracer),
                        InstructionName::ZicsrNonDeterminismRead => {
                            zicsr::nd_read::<C, R, ND>(state, ram, instr, tracer, nd)
                        }
                        InstructionName::ZicsrNonDeterminismWrite => {
                            zicsr::nd_write::<C, R>(state, ram, instr, tracer)
                        }
                        InstructionName::ZicsrDelegation => {
                            zicsr::call_delegation::<C, R>(state, ram, instr, tracer)
                        }
                        _ => core::hint::unreachable_unchecked(),
                    }
                    if state.pc == pc {
                        return;
                    }
                    state.timestamp += TIMESTAMP_STEP;
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use common_constants::INITIAL_TIMESTAMP;
    use risc_v_simulator::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;

    use crate::ir::decode;
    use crate::ir::FullUnsignedMachineDecoderConfig;
    use crate::vm::test::read_binary;
    use crate::vm::Counters;
    use crate::vm::*;
    use crate::witness::NonMemDestinationHolder;

    use super::*;
    use std::path::Path;

    // type CountersT = DelegationsCounters;
    type CountersT = DelegationsAndFamiliesCounters;

    #[test]
    fn test_replay_simple_fibonacci() {
        let (_, binary) = read_binary(&Path::new("examples/fibonacci/app.bin"));
        let (_, text) = read_binary(&Path::new("examples/fibonacci/app.text"));
        let instructions: Vec<Instruction> = text
            .into_iter()
            .map(|el| decode::<FullUnsignedMachineDecoderConfig>(el))
            .collect();
        let tape = SimpleTape::new(&instructions);
        let mut ram = RamWithRomRegion::<5>::from_rom_content(&binary, 1 << 30);
        let period = 1 << 20;
        let num_snapshots = 1000;
        let cycles_bound = period * num_snapshots;

        let mut state = State::initial_with_counters(CountersT::default());

        let mut snapshotter = SimpleSnapshotter::new_with_cycle_limit(cycles_bound, period, state);

        let now = std::time::Instant::now();
        VM::<CountersT>::run_basic_unrolled::<
            SimpleSnapshotter<CountersT, 5>,
            RamWithRomRegion<5>,
            _,
        >(
            &mut state,
            num_snapshots,
            &mut ram,
            &mut snapshotter,
            &tape,
            period,
            &mut (),
        );
        let elapsed = now.elapsed();

        let total_snapshots = snapshotter.snapshots.len();
        let cycles_upper_bound = total_snapshots * period;

        println!(
            "Performance is {} MHz ({} total snapshots with period of {} cycles)",
            (cycles_upper_bound as f64) / (elapsed.as_micros() as f64),
            total_snapshots,
            period
        );

        let exact_cycles_passed = (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;

        println!("Passed exactly {} cycles", exact_cycles_passed);

        let counters = state.counters;

        // now replay - first from the start
        let mut state = State::initial_with_counters(CountersT::default());

        let mut ram = ReplayerRam::<5> {
            ram_log: &snapshotter.reads_buffer,
        };

        let mut nd = ReplayerNonDeterminism {
            non_determinism_reads_log: &snapshotter.non_determinism_reads_buffer,
        };

        let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); (1 << 22) - 1];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = NonMemDestinationHolder::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX> {
            buffers: &mut buffers[..],
        };
        let now = std::time::Instant::now();
        ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
            &mut state,
            num_snapshots,
            &mut ram,
            &tape,
            period,
            &mut nd,
            &mut tracer,
        );
        let elapsed = now.elapsed();

        println!(
            "Replay performance is {} MHz ({} total snapshots with period of {} cycles)",
            (cycles_upper_bound as f64) / (elapsed.as_micros() as f64),
            total_snapshots,
            period
        );

        // now let's give an example of parallel processing

        let total_num_add_sub =
            counters.get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>();

        println!("In total {} of ADD/SUB family opcodes", total_num_add_sub);

        let circuit_capacity = (1 << 24) - 1;

        let num_circuits = total_num_add_sub.div_ceil(circuit_capacity);

        println!("In total {} of ADD/SUB circuits", num_circuits);

        // allocate ALL of them
        let mut total_witness =
            vec![
                vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); circuit_capacity];
                num_circuits
            ];

        // now there is no concrete solution what is the most optimal strategy here, but let's assume that frequency of particular opcodes
        // is well spread over the cycles

        let worker = worker::Worker::new_with_num_threads(2);
        let chunk_size = total_num_add_sub.div_ceil(worker.num_cores);

        let mut witness_buffers: Vec<_> = total_witness.iter_mut().map(|el| &mut el[..]).collect();

        let now = std::time::Instant::now();
        worker.scope(total_snapshots, |scope, geometry| {
            let tape_ref = &tape;
            let mut starting_snapshot = snapshotter.initial_snapshot;
            let mut current_snapshot = starting_snapshot;
            let mut snapshots_iter = snapshotter.snapshots.iter();
            for _i in 0..geometry.len() {
                let mut num_snapshots = 0;
                'inner: while current_snapshot
                    .state
                    .counters
                    .get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(
                ) - starting_snapshot
                    .state
                    .counters
                    .get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(
                ) < chunk_size
                {
                    if let Some(next_snapshot) = snapshots_iter.next() {
                        num_snapshots += 1;
                        current_snapshot = *next_snapshot;
                    } else {
                        break 'inner;
                    }
                }

                let start_chunk_idx = starting_snapshot
                    .state
                    .counters
                    .get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(
                ) / circuit_capacity;
                let start_chunk_offset = starting_snapshot
                    .state
                    .counters
                    .get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(
                ) % circuit_capacity;

                let end_chunk_idx = current_snapshot
                    .state
                    .counters
                    .get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(
                ) / circuit_capacity;
                let end_chunk_offset = current_snapshot
                    .state
                    .counters
                    .get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(
                ) % circuit_capacity;

                let mut chunks = vec![];
                let mut offset = start_chunk_offset;
                unsafe {
                    // Lazy to go via splits
                    for src_chunk in start_chunk_idx..=end_chunk_idx {
                        if src_chunk == end_chunk_idx {
                            if end_chunk_offset > 0 {
                                let range = 0..end_chunk_offset;
                                let chunk = (&mut witness_buffers[src_chunk][range]
                                    as *mut [NonMemoryOpcodeTracingDataWithTimestamp])
                                    .as_mut_unchecked();
                                chunks.push(chunk);
                            }
                        } else {
                            let range = offset..;
                            offset = 0;
                            let chunk = (&mut witness_buffers[src_chunk][range]
                                as *mut [NonMemoryOpcodeTracingDataWithTimestamp])
                                .as_mut_unchecked();
                            chunks.push(chunk);
                        }
                    }
                }

                let ram_range =
                    starting_snapshot.memory_reads_start..current_snapshot.memory_reads_end;
                let nd_range = starting_snapshot.non_determinism_reads_start
                    ..current_snapshot.non_determinism_reads_end;

                let mut ram = ReplayerRam::<5> {
                    ram_log: &snapshotter.reads_buffer[ram_range],
                };
                let mut nd = ReplayerNonDeterminism {
                    non_determinism_reads_log: &snapshotter.non_determinism_reads_buffer[nd_range],
                };

                // println!("Thread {}", _i);
                // for el in chunks.iter() {
                //     println!("Chunk of size {}", el.len());
                // }

                // spawn replayer
                scope.spawn(move |_| {
                    let mut chunks = chunks;
                    let mut tracer =
                        NonMemDestinationHolder::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX> {
                            buffers: &mut chunks,
                        };
                    let mut state = starting_snapshot.state;
                    ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
                        &mut state,
                        num_snapshots,
                        &mut ram,
                        tape_ref,
                        period,
                        &mut nd,
                        &mut tracer,
                    );
                });

                starting_snapshot = current_snapshot;
            }
        });
        let elapsed = now.elapsed();

        println!(
            "Parallel replay performance is {} MHz ({} total snapshots with period of {} cycles) at {} cores",
            (cycles_upper_bound as f64) / (elapsed.as_micros() as f64),
            total_snapshots,
            period,
            worker.get_num_cores(),
        );

        let mut ts = 0;
        for (i, el) in total_witness.iter().flatten().enumerate() {
            if i < total_num_add_sub {
                let cycle_ts = el.cycle_timestamp.as_scalar();
                assert_ne!(cycle_ts, 0, "timestamp is 0 at position {}", i);
                assert!(cycle_ts > ts, "timestamp is not ordered at position {}", i);
                ts = cycle_ts;
            }
        }
    }
}
