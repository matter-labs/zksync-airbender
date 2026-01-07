use crate::ir::DelegationType;
use crate::ir::Instruction;
use crate::ir::InstructionName;
use crate::vm::Counters;
use crate::vm::InstructionTape;
use crate::vm::NonDeterminismCSRSource;
use crate::vm::State;
use crate::vm::{RamPeek, RAM};
use crate::witness::WitnessTracer;
use common_constants::circuit_families::*;
use common_constants::TimestampScalar;
use common_constants::TIMESTAMP_STEP;
use risc_v_simulator::machine_mode_only_unrolled::TimestampData;

mod delegations;
mod instructions;

#[derive(Debug)]
pub struct ReplayerRam<'a, const ROM_BOUND_SECOND_WORD_BITS: usize> {
    pub ram_log: &'a mut [&'a [(u32, (u32, u32))]],
}

impl<'a, const ROM_BOUND_SECOND_WORD_BITS: usize> RamPeek
    for ReplayerRam<'a, ROM_BOUND_SECOND_WORD_BITS>
{
    #[inline(always)]
    fn peek_word(&self, address: u32) -> u32 {
        debug_assert_eq!(address % 4, 0);
        debug_assert!(self.ram_log.len() > 0);
        unsafe {
            let (value, _) = *self.ram_log.get_unchecked(0).get_unchecked(0);

            value
        }
    }
}

impl<'a, const ROM_BOUND_SECOND_WORD_BITS: usize> RAM
    for ReplayerRam<'a, ROM_BOUND_SECOND_WORD_BITS>
{
    const REPLAY_NON_DETERMINISM_VIA_RAM_STUB: bool = true;

    #[track_caller]
    #[inline(always)]
    fn read_word(&mut self, address: u32, timestamp: TimestampScalar) -> (TimestampScalar, u32) {
        debug_assert_eq!(address % 4, 0);
        debug_assert!(self.ram_log.len() > 0);
        unsafe {
            let src = self.ram_log.get_unchecked_mut(0);
            let (value, (low, high)) = *src.get_unchecked(0);
            let next = src.get_unchecked(1..);
            if next.len() > 0 {
                *src = next;
            } else {
                self.ram_log = core::mem::transmute(self.ram_log.get_unchecked_mut(1..));
            }

            let read_timestamp = (low as TimestampScalar) | ((high as TimestampScalar) << 32);
            debug_assert!(read_timestamp < timestamp, "trying to read replay log at address 0x{:08x} with timestamp {}, but read timestamp is {}", address, timestamp, read_timestamp);

            // println!("Read at address 0x{:08x} at timestamp {} into value {} and read timestamp {}", address, timestamp, value, read_timestamp);
            (read_timestamp, value)
        }
    }

    #[inline(always)]
    fn mask_read_for_witness(&self, address: &mut u32, value: &mut u32) {
        debug_assert_eq!(*address % 4, 0);
        if *address < 1 << (16 + ROM_BOUND_SECOND_WORD_BITS) {
            // NOTE: we no longer mask an address, just a value as it's only initialized to
            // 0 via inits, and can not be writen over by circuits
            // *address = 0u32;
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
            let src = self.ram_log.get_unchecked_mut(0);
            let (value, (low, high)) = *src.get_unchecked(0);
            let next = src.get_unchecked(1..);
            if next.len() > 0 {
                *src = next;
            } else {
                self.ram_log = core::mem::transmute(self.ram_log.get_unchecked_mut(1..));
            }

            let read_timestamp = (low as TimestampScalar) | ((high as TimestampScalar) << 32);
            debug_assert!(read_timestamp < timestamp, "trying to read replay log at address 0x{:08x} with timestamp {}, but read timestamp is {}", address, timestamp, read_timestamp);

            // println!("Read at address 0x{:08x} at timestamp {} into value {} and read timestamp {}", address, timestamp, value, read_timestamp);
            (read_timestamp, value)
        }
    }

    #[inline(always)]
    fn skip_if_replaying(&mut self, num_snapshots: usize) {
        unsafe {
            let src = self.ram_log.get_unchecked_mut(0);
            debug_assert!(src.len() >= num_snapshots);
            let next = src.get_unchecked(num_snapshots..);
            if next.len() > 0 {
                *src = next;
            } else {
                self.ram_log = core::mem::transmute(self.ram_log.get_unchecked_mut(1..));
            }
        }
    }
}

pub struct ReplayerVM<C: Counters> {
    pub state: State<C>,
}

impl<C: Counters> ReplayerVM<C> {
    pub fn replay_basic_unrolled<R: RAM, ND: NonDeterminismCSRSource>(
        state: &mut State<C>,
        ram: &mut R,
        instruction_tape: &impl InstructionTape,
        nd: &mut ND,
        cycle_bound: usize,
        tracer: &mut impl WitnessTracer,
    ) {
        let final_ts = state.timestamp + (TIMESTAMP_STEP * (cycle_bound as u64));
        Self::replay_by_timestamp_bound(state, ram, instruction_tape, nd, final_ts, tracer);
    }

    pub fn replay_by_timestamp_bound<R: RAM, ND: NonDeterminismCSRSource>(
        state: &mut State<C>,
        ram: &mut R,
        instruction_tape: &impl InstructionTape,
        nd: &mut ND,
        timestamp_bound: TimestampScalar,
        tracer: &mut impl WitnessTracer,
    ) {
        while state.timestamp < timestamp_bound {
            unsafe {
                let pc = state.pc;
                use crate::replayer::instructions::*;
                let instr = instruction_tape.read_instruction(pc);
                match instr.name {
                    InstructionName::Illegal => illegal::<C, R>(state, ram, instr, tracer),
                    InstructionName::Lui => lui_auipc::lui::<C, R>(state, ram, instr, tracer),
                    InstructionName::Auipc => lui_auipc::auipc::<C, R>(state, ram, instr, tracer),

                    InstructionName::Jal => jal_jalr::jal::<C, R>(state, ram, instr, tracer),
                    InstructionName::Jalr => jal_jalr::jalr::<C, R>(state, ram, instr, tracer),

                    InstructionName::Slt => slt::slt::<C, R, false>(state, ram, instr, tracer),
                    InstructionName::Slti => slt::slt::<C, R, true>(state, ram, instr, tracer),

                    InstructionName::Sltu => slt::sltu::<C, R, false>(state, ram, instr, tracer),
                    InstructionName::Sltiu => slt::sltu::<C, R, true>(state, ram, instr, tracer),

                    InstructionName::Branch => branch::branch::<C, R>(state, ram, instr, tracer),

                    InstructionName::Sw => memory::sw::<C, R>(state, ram, instr, tracer),
                    InstructionName::Lw => memory::lw::<C, R>(state, ram, instr, tracer),

                    InstructionName::Sh => memory::sh::<C, R>(state, ram, instr, tracer),
                    InstructionName::Lhu => memory::lh::<C, R, false>(state, ram, instr, tracer),
                    InstructionName::Lh => memory::lh::<C, R, true>(state, ram, instr, tracer),

                    InstructionName::Sb => memory::sb::<C, R>(state, ram, instr, tracer),
                    InstructionName::Lbu => memory::lb::<C, R, false>(state, ram, instr, tracer),
                    InstructionName::Lb => memory::lb::<C, R, true>(state, ram, instr, tracer),

                    InstructionName::Add => {
                        add_sub::add_op::<C, R, false>(state, ram, instr, tracer)
                    }
                    InstructionName::Addi => {
                        add_sub::add_op::<C, R, true>(state, ram, instr, tracer)
                    }
                    InstructionName::Sub => add_sub::sub_op::<C, R>(state, ram, instr, tracer),
                    InstructionName::Xor => binary::xor::<C, R, false>(state, ram, instr, tracer),
                    InstructionName::Xori => binary::xor::<C, R, true>(state, ram, instr, tracer),
                    InstructionName::And => binary::and::<C, R, false>(state, ram, instr, tracer),
                    InstructionName::Andi => binary::and::<C, R, true>(state, ram, instr, tracer),
                    InstructionName::Or => binary::or::<C, R, false>(state, ram, instr, tracer),
                    InstructionName::Ori => binary::or::<C, R, true>(state, ram, instr, tracer),
                    InstructionName::Sll => shifts::sll::<C, R, false>(state, ram, instr, tracer),
                    InstructionName::Slli => shifts::sll::<C, R, true>(state, ram, instr, tracer),
                    InstructionName::Srl => shifts::srl::<C, R, false>(state, ram, instr, tracer),
                    InstructionName::Srli => shifts::srl::<C, R, true>(state, ram, instr, tracer),
                    InstructionName::Sra => shifts::sra::<C, R, false>(state, ram, instr, tracer),
                    InstructionName::Srai => shifts::sra::<C, R, true>(state, ram, instr, tracer),
                    InstructionName::Mul => mul_div::mul::<C, R>(state, ram, instr, tracer),
                    InstructionName::Mulhu => mul_div::mulhu::<C, R>(state, ram, instr, tracer),
                    InstructionName::Divu => mul_div::divu::<C, R>(state, ram, instr, tracer),
                    InstructionName::Remu => mul_div::remu::<C, R>(state, ram, instr, tracer),

                    InstructionName::ZimopAdd => mop::mop_addmod::<C, R>(state, ram, instr, tracer),
                    InstructionName::ZimopSub => mop::mop_submod::<C, R>(state, ram, instr, tracer),
                    InstructionName::ZimopMul => mop::mop_mulmod::<C, R>(state, ram, instr, tracer),

                    InstructionName::ZicsrNonDeterminismRead => {
                        zicsr::nd_read::<C, R, ND>(state, ram, instr, tracer, nd)
                    }
                    InstructionName::ZicsrNonDeterminismWrite => {
                        zicsr::nd_write::<C, R>(state, ram, instr, tracer)
                    }
                    InstructionName::ZicsrDelegation => {
                        zicsr::call_delegation::<C, R>(state, ram, instr, tracer)
                    }
                    a @ _ => {
                        panic!("Unknown instruction {:?}", a);
                    }
                    _ => core::hint::unreachable_unchecked(),
                }
                state.timestamp += TIMESTAMP_STEP;
                if state.pc == pc {
                    return;
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use common_constants::INITIAL_TIMESTAMP;
    use risc_v_simulator::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;

    use crate::ir::preprocess_bytecode;
    use crate::ir::FullUnsignedMachineDecoderConfig;
    use crate::vm::test::read_binary;
    use crate::vm::Counters;
    use crate::vm::*;
    use crate::witness::NonMemDestinationHolder;

    use super::*;
    use std::path::Path;

    // type CountersT = DelegationsCounters;
    type CountersT = DelegationsAndFamiliesCounters;

    // #[test]
    // fn test_replay_simple_fibonacci() {
    //     let (_, binary) = read_binary(&Path::new("examples/fibonacci/app.bin"));
    //     let (_, text) = read_binary(&Path::new("examples/fibonacci/app.text"));
    //     let instructions: Vec<Instruction> = text
    //         .into_iter()
    //         .map(|el| decode::<FullUnsignedMachineDecoderConfig>(el))
    //         .collect();
    //     let tape = SimpleTape::new(&instructions);
    //     let mut ram = RamWithRomRegion::<5>::from_rom_content(&binary, 1 << 30);
    //     let period = 1 << 20;
    //     let num_snapshots = 1000;
    //     let cycles_bound = period * num_snapshots;

    //     let mut state = State::initial_with_counters(CountersT::default());

    //     let mut snapshotter = SimpleSnapshotter::new_with_cycle_limit(cycles_bound, period, state);

    //     let now = std::time::Instant::now();
    //     VM::<CountersT>::run_basic_unrolled::<
    //         SimpleSnapshotter<CountersT, 5>,
    //         RamWithRomRegion<5>,
    //         _,
    //     >(
    //         &mut state,
    //         num_snapshots,
    //         &mut ram,
    //         &mut snapshotter,
    //         &tape,
    //         period,
    //         &mut (),
    //     );
    //     let elapsed = now.elapsed();

    //     let total_snapshots = snapshotter.snapshots.len();
    //     let cycles_upper_bound = total_snapshots * period;

    //     println!(
    //         "Performance is {} MHz ({} total snapshots with period of {} cycles)",
    //         (cycles_upper_bound as f64) / (elapsed.as_micros() as f64),
    //         total_snapshots,
    //         period
    //     );

    //     let exact_cycles_passed = (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;

    //     println!("Passed exactly {} cycles", exact_cycles_passed);

    //     let counters = state.counters;

    //     // now replay - first from the start
    //     let mut state = State::initial_with_counters(CountersT::default());

    //     let mut ram_log_buffers = snapshotter
    //         .reads_buffer
    //         .make_range(0..snapshotter.reads_buffer.len());
    //     let mut ram = ReplayerRam::<5> {
    //         ram_log: &mut ram_log_buffers,
    //     };

    //     let mut nd_log_buffers = snapshotter
    //         .non_determinism_reads_buffer
    //         .make_range(0..snapshotter.non_determinism_reads_buffer.len());
    //     let mut nd = ReplayerNonDeterminism {
    //         non_determinism_reads_log: &mut nd_log_buffers,
    //     };

    //     let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); (1 << 22) - 1];
    //     let mut buffers = vec![&mut buffer[..]];
    //     let mut tracer = NonMemDestinationHolder::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX> {
    //         buffers: &mut buffers[..],
    //     };
    //     let now = std::time::Instant::now();
    //     ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
    //         &mut state,
    //         num_snapshots,
    //         &mut ram,
    //         &tape,
    //         period,
    //         &mut nd,
    //         &mut tracer,
    //     );
    //     let elapsed = now.elapsed();

    //     println!(
    //         "Replay performance is {} MHz ({} total snapshots with period of {} cycles)",
    //         (cycles_upper_bound as f64) / (elapsed.as_micros() as f64),
    //         total_snapshots,
    //         period
    //     );

    //     // now let's give an example of parallel processing

    //     let total_num_add_sub =
    //         counters.get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>();

    //     println!("In total {} of ADD/SUB family opcodes", total_num_add_sub);

    //     let circuit_capacity = (1 << 24) - 1;

    //     let num_circuits = total_num_add_sub.div_ceil(circuit_capacity);

    //     println!("In total {} of ADD/SUB circuits", num_circuits);

    //     // allocate ALL of them
    //     let mut total_witness =
    //         vec![
    //             vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); circuit_capacity];
    //             num_circuits
    //         ];

    //     // now there is no concrete solution what is the most optimal strategy here, but let's assume that frequency of particular opcodes
    //     // is well spread over the cycles

    //     let worker = worker::Worker::new_with_num_threads(2);
    //     let chunk_size = total_num_add_sub.div_ceil(worker.num_cores);

    //     let mut witness_buffers: Vec<_> = total_witness.iter_mut().map(|el| &mut el[..]).collect();

    //     let now = std::time::Instant::now();
    //     worker.scope(total_snapshots, |scope, geometry| {
    //         let tape_ref = &tape;
    //         let mut starting_snapshot = snapshotter.initial_snapshot;
    //         let mut current_snapshot = starting_snapshot;
    //         let mut snapshots_iter = snapshotter.snapshots.iter();
    //         for _i in 0..geometry.len() {
    //             let mut num_snapshots = 0;
    //             'inner: while current_snapshot
    //                 .state
    //                 .counters
    //                 .get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(
    //             ) - starting_snapshot
    //                 .state
    //                 .counters
    //                 .get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(
    //             ) < chunk_size
    //             {
    //                 if let Some(next_snapshot) = snapshots_iter.next() {
    //                     num_snapshots += 1;
    //                     current_snapshot = *next_snapshot;
    //                 } else {
    //                     break 'inner;
    //                 }
    //             }

    //             let start_chunk_idx = starting_snapshot
    //                 .state
    //                 .counters
    //                 .get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(
    //             ) / circuit_capacity;
    //             let start_chunk_offset = starting_snapshot
    //                 .state
    //                 .counters
    //                 .get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(
    //             ) % circuit_capacity;

    //             let end_chunk_idx = current_snapshot
    //                 .state
    //                 .counters
    //                 .get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(
    //             ) / circuit_capacity;
    //             let end_chunk_offset = current_snapshot
    //                 .state
    //                 .counters
    //                 .get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>(
    //             ) % circuit_capacity;

    //             let mut chunks = vec![];
    //             let mut offset = start_chunk_offset;
    //             unsafe {
    //                 // Lazy to go via splits
    //                 for src_chunk in start_chunk_idx..=end_chunk_idx {
    //                     if src_chunk == end_chunk_idx {
    //                         if end_chunk_offset > 0 {
    //                             let range = 0..end_chunk_offset;
    //                             let chunk = (&mut witness_buffers[src_chunk][range]
    //                                 as *mut [NonMemoryOpcodeTracingDataWithTimestamp])
    //                                 .as_mut_unchecked();
    //                             chunks.push(chunk);
    //                         }
    //                     } else {
    //                         let range = offset..;
    //                         offset = 0;
    //                         let chunk = (&mut witness_buffers[src_chunk][range]
    //                             as *mut [NonMemoryOpcodeTracingDataWithTimestamp])
    //                             .as_mut_unchecked();
    //                         chunks.push(chunk);
    //                     }
    //                 }
    //             }

    //             let ram_range =
    //                 starting_snapshot.memory_reads_start..current_snapshot.memory_reads_end;
    //             let nd_range = starting_snapshot.non_determinism_reads_start
    //                 ..current_snapshot.non_determinism_reads_end;

    //             let snapshotter_ref = &snapshotter;

    //             // println!("Thread {}", _i);
    //             // for el in chunks.iter() {
    //             //     println!("Chunk of size {}", el.len());
    //             // }

    //             // spawn replayer
    //             scope.spawn(move |_| {
    //                 let mut ram_log_buffers = snapshotter_ref.reads_buffer.make_range(ram_range);
    //                 let mut nd_log_buffers = snapshotter_ref
    //                     .non_determinism_reads_buffer
    //                     .make_range(nd_range);

    //                 let mut ram = ReplayerRam::<5> {
    //                     ram_log: &mut ram_log_buffers,
    //                 };

    //                 let mut nd = ReplayerNonDeterminism {
    //                     non_determinism_reads_log: &mut nd_log_buffers,
    //                 };
    //                 let mut chunks = chunks;
    //                 let mut tracer =
    //                     NonMemDestinationHolder::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX> {
    //                         buffers: &mut chunks,
    //                     };
    //                 let mut state = starting_snapshot.state;
    //                 ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
    //                     &mut state,
    //                     num_snapshots,
    //                     &mut ram,
    //                     tape_ref,
    //                     period,
    //                     &mut nd,
    //                     &mut tracer,
    //                 );
    //             });

    //             starting_snapshot = current_snapshot;
    //         }
    //     });
    //     let elapsed = now.elapsed();

    //     println!(
    //         "Parallel replay performance is {} MHz ({} total snapshots with period of {} cycles) at {} cores",
    //         (cycles_upper_bound as f64) / (elapsed.as_micros() as f64),
    //         total_snapshots,
    //         period,
    //         worker.get_num_cores(),
    //     );

    //     let mut ts = 0;
    //     for (i, el) in total_witness.iter().flatten().enumerate() {
    //         if i < total_num_add_sub {
    //             let cycle_ts = el.cycle_timestamp.as_scalar();
    //             assert_ne!(cycle_ts, 0, "timestamp is 0 at position {}", i);
    //             assert!(cycle_ts > ts, "timestamp is not ordered at position {}", i);
    //             ts = cycle_ts;
    //         }
    //     }
    // }

    #[test]
    fn test_replay_keccak_f1600() {
        let (_, binary) = read_binary(&Path::new("examples/keccak_f1600/app.bin"));
        let (_, text) = read_binary(&Path::new("examples/keccak_f1600/app.text"));
        let instructions: Vec<Instruction> =
            preprocess_bytecode::<FullUnsignedMachineDecoderConfig>(&text);
        let tape = SimpleTape::new(&instructions);
        let mut ram = RamWithRomRegion::<5>::from_rom_content(&binary, 1 << 30);
        let cycles_bound = 1 << 30;

        let mut state = State::initial_with_counters(CountersT::default());

        let mut snapshotter: SimpleSnapshotter<
            CountersT,
            { common_constants::rom::ROM_SECOND_WORD_BITS },
        > = SimpleSnapshotter::new_with_cycle_limit(cycles_bound, state);

        let now = std::time::Instant::now();
        VM::<CountersT>::run_basic_unrolled::<_, _, _>(
            &mut state,
            &mut ram,
            &mut snapshotter,
            &tape,
            cycles_bound,
            &mut (),
        );
        let elapsed = now.elapsed();

        let cycles_elapsed = (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;

        // now replay - first from the start
        let mut state = State::initial_with_counters(CountersT::default());

        let mut ram_log_buffers = snapshotter
            .reads_buffer
            .make_range(0..snapshotter.reads_buffer.len());
        let mut ram = ReplayerRam::<{ common_constants::rom::ROM_SECOND_WORD_BITS }> {
            ram_log: &mut ram_log_buffers,
        };

        let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); (1 << 22) - 1];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = NonMemDestinationHolder::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX> {
            buffers: &mut buffers[..],
        };
        let now = std::time::Instant::now();
        ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
            &mut state,
            &mut ram,
            &tape,
            &mut (),
            cycles_elapsed as usize,
            &mut tracer,
        );
        let elapsed = now.elapsed();

        println!(
            "Replay performance is {} MHz ({} cycles)",
            (cycles_elapsed as f64) / (elapsed.as_micros() as f64),
            cycles_elapsed,
        );

        dbg!(state.pc);
        dbg!(state.timestamp);

        dbg!(&state.registers[10..18]);

        dbg!(state.registers[0]);
    }
}
