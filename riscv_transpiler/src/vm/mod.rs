use crate::ir::DelegationType;
use crate::ir::Instruction;
use crate::ir::InstructionName;
use crate::jit::{MachineState, MAX_NUM_COUNTERS};
use common_constants::circuit_families::*;
use common_constants::{TimestampScalar, INITIAL_TIMESTAMP, TIMESTAMP_STEP};
use std::fmt::Debug;

mod instructions;
mod ram_with_rom_region;
mod replay_snapshotter;
mod simple_tape;

pub(crate) mod delegations;

pub use self::ram_with_rom_region::RamWithRomRegion;
pub use self::replay_snapshotter::*;
pub use self::simple_tape::SimpleTape;

pub trait Counters: 'static + Clone + Copy + Debug + PartialEq + Eq + Send + Sync {
    fn bump_bigint(&mut self, by: usize);
    fn bump_blake2_round_function(&mut self, by: usize);
    fn bump_keccak_special5(&mut self, by: usize);
    #[inline(always)]
    fn log_circuit_family<const FAMILY: u8>(&mut self) {
        self.log_multiple_circuit_family_calls::<FAMILY>(1)
    }
    fn log_multiple_circuit_family_calls<const FAMILY: u8>(&mut self, num_calls: usize);
    fn get_calls_to_circuit_family<const FAMILY: u8>(&self) -> usize;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
#[repr(C, align(16))]
pub struct Register {
    pub timestamp: TimestampScalar,
    pub value: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct State<C: Counters> {
    pub registers: [Register; 32],
    pub timestamp: TimestampScalar,
    pub pc: u32,
    pub counters: C,
}

impl<C: Counters> State<C> {
    pub fn initial_with_counters(counters: C) -> Self {
        Self {
            registers: [Register {
                value: 0,
                timestamp: 0,
            }; 32],
            counters,
            timestamp: INITIAL_TIMESTAMP,
            pc: 0,
        }
    }
}

impl<C: Counters + From<[u32; MAX_NUM_COUNTERS]>> From<MachineState> for State<C> {
    fn from(state: MachineState) -> Self {
        Self {
            registers: std::array::from_fn(|i| Register {
                timestamp: state.register_timestamps[i],
                value: state.registers[i],
            }),
            timestamp: state.timestamp,
            pc: state.pc,
            counters: state.counters.into(),
        }
    }
}

pub trait Snapshotter<C: Counters> {
    fn take_snapshot_if_needed(&mut self, state: &State<C>) -> bool;
    fn take_final_snapshot(&mut self, state: &State<C>);
    fn append_arbitrary_value(&mut self, value: u32);
    fn append_memory_read(
        &mut self,
        address: u32,
        read_value: u32,
        read_timestamp: TimestampScalar,
        write_timestamp: TimestampScalar,
    );
}

impl<C: Counters> Snapshotter<C> for () {
    #[inline(always)]
    fn take_snapshot_if_needed(&mut self, _state: &State<C>) -> bool {
        false
    }
    #[inline(always)]
    fn take_final_snapshot(&mut self, state: &State<C>) {}
    #[inline(always)]
    fn append_arbitrary_value(&mut self, _value: u32) {}
    #[inline(always)]
    fn append_memory_read(
        &mut self,
        _address: u32,
        _read_value: u32,
        _read_timestamp: TimestampScalar,
        _write_timestamp: TimestampScalar,
    ) {
    }
}

pub trait RamPeek {
    fn peek_word(&self, address: u32) -> u32;
}

impl<const N: usize> RamPeek for [u32; N] {
    #[inline(always)]
    fn peek_word(&self, address: u32) -> u32 {
        debug_assert_eq!(address % 4, 0);
        let word_idx = (address / 4) as usize;
        debug_assert!(word_idx < N);
        unsafe { *self.get_unchecked(word_idx) }
    }
}

impl RamPeek for [u32] {
    #[inline(always)]
    fn peek_word(&self, address: u32) -> u32 {
        debug_assert_eq!(address % 4, 0);
        let word_idx = (address / 4) as usize;
        debug_assert!(word_idx < self.len());
        unsafe { *self.get_unchecked(word_idx) }
    }
}

pub trait RAM: RamPeek {
    const REPLAY_NON_DETERMINISM_VIA_RAM_STUB: bool = false;

    fn read_word(&mut self, address: u32, timestamp: TimestampScalar) -> (TimestampScalar, u32);
    fn mask_read_for_witness(&self, address: &mut u32, value: &mut u32);
    fn write_word(
        &mut self,
        address: u32,
        word: u32,
        timestamp: TimestampScalar,
    ) -> (TimestampScalar, u32);
    fn skip_if_replaying(&mut self, num_snapshots: usize);
}

// TODO: make separate replayer RAM as NOT peekable, and that can only read and
pub trait ReplayableRam {
    fn mask_read_for_witness(&self, address: &mut u32, value: &mut u32);
    fn read_arbitrary_value(&self) -> u32;
    fn skip(&mut self, num_snapshots: usize);
    fn next(&mut self) -> (TimestampScalar, u32);
    fn next_extended(&mut self, address: u32, write_ts: TimestampScalar) -> (TimestampScalar, u32);
}

pub trait InstructionTape: Send + Sync {
    fn read_instruction(&self, pc: u32) -> Instruction;
}

// there is no interpretation of methods here, it's just read/write and that's all
pub trait NonDeterminismCSRSource {
    fn read(&mut self) -> u32;

    // we in general can allow CSR source to peek into memory (readonly)
    // to perform adhoc computations to prepare result. This will allow to save on
    // passing large structures
    fn write_with_memory_access<R: RamPeek>(&mut self, ram: &R, value: u32)
    where
        Self: Sized;

    // we in general can allow CSR source to peek into memory (readonly)
    // to perform adhoc computations to prepare result. This will allow to save on
    // passing large structures
    fn write_with_memory_access_dyn(&mut self, ram: &dyn RamPeek, value: u32);
}

impl NonDeterminismCSRSource for () {
    fn read(&mut self) -> u32 {
        0u32
    }
    fn write_with_memory_access<R: RamPeek>(&mut self, _ram: &R, _value: u32) {}
    fn write_with_memory_access_dyn(&mut self, ram: &dyn RamPeek, value: u32) {}
}

impl NonDeterminismCSRSource for risc_v_simulator::abstractions::non_determinism::QuasiUARTSource {
    fn read(&mut self) -> u32 {
        // self.oracle.pop_front().unwrap_or_default()
        self.oracle.pop_front().expect("must have an answer")
    }

    fn write_with_memory_access<R: RamPeek>(&mut self, _ram: &R, value: u32) {
        self.write_state.process_write(value);
    }
    fn write_with_memory_access_dyn(&mut self, _ram: &dyn RamPeek, value: u32) {
        self.write_state.process_write(value);
    }
}

pub struct VM<C: Counters> {
    pub state: State<C>,
}

impl<C: Counters> VM<C> {
    pub fn run_basic_unrolled<S: Snapshotter<C>, R: RAM, ND: NonDeterminismCSRSource>(
        state: &mut State<C>,
        ram: &mut R,
        snapshotter: &mut S,
        instruction_tape: &impl InstructionTape,
        cycle_bound: usize,
        nd: &mut ND,
    ) -> bool {
        for _cycle in 0..cycle_bound {
            let pc = state.pc;

            Self::run_step(state, ram, snapshotter, instruction_tape, nd);

            state.timestamp += TIMESTAMP_STEP;
            if state.pc == pc {
                snapshotter.take_final_snapshot(&*state);
                return true;
            }

            if snapshotter.take_snapshot_if_needed(&*state) {
                return false;
            }
        }

        false
    }
    pub fn run_by_timestamp_bound<S: Snapshotter<C>, R: RAM, ND: NonDeterminismCSRSource>(
        state: &mut State<C>,
        ram: &mut R,
        snapshotter: &mut S,
        instruction_tape: &impl InstructionTape,
        timestamp_bound: TimestampScalar,
        nd: &mut ND,
    ) -> bool {
        while state.timestamp < timestamp_bound {
            let pc = state.pc;

            Self::run_step(state, ram, snapshotter, instruction_tape, nd);

            state.timestamp += TIMESTAMP_STEP;
            if state.pc == pc {
                snapshotter.take_final_snapshot(&*state);
                return true;
            }

            if snapshotter.take_snapshot_if_needed(&*state) {
                return false;
            }
        }

        false
    }

    #[inline(always)]
    pub fn run_step<S: Snapshotter<C>, R: RAM, ND: NonDeterminismCSRSource>(
        state: &mut State<C>,
        ram: &mut R,
        snapshotter: &mut S,
        instruction_tape: &impl InstructionTape,
        nd: &mut ND,
    ) {
        use crate::vm::instructions::*;
        unsafe {
            let pc = state.pc;
            let instr = instruction_tape.read_instruction(pc);
            debug_assert_eq!(state.timestamp % TIMESTAMP_STEP, 0);
            match instr.name {
                InstructionName::Illegal => illegal(state, ram, snapshotter, instr),
                InstructionName::Lui => lui_auipc::lui::<C, S, R>(state, ram, snapshotter, instr),
                InstructionName::Auipc => {
                    lui_auipc::auipc::<C, S, R>(state, ram, snapshotter, instr)
                }

                InstructionName::Jal => jal_jalr::jal::<C, S, R>(state, ram, snapshotter, instr),
                InstructionName::Jalr => jal_jalr::jalr::<C, S, R>(state, ram, snapshotter, instr),

                InstructionName::Slt => slt::slt::<C, S, R, false>(state, ram, snapshotter, instr),
                InstructionName::Slti => slt::slt::<C, S, R, true>(state, ram, snapshotter, instr),

                InstructionName::Sltu => {
                    slt::sltu::<C, S, R, false>(state, ram, snapshotter, instr)
                }
                InstructionName::Sltiu => {
                    slt::sltu::<C, S, R, true>(state, ram, snapshotter, instr)
                }

                InstructionName::Branch => {
                    branch::branch::<C, S, R>(state, ram, snapshotter, instr)
                }

                InstructionName::Sw => memory::sw::<C, S, R>(state, ram, snapshotter, instr),
                InstructionName::Lw => memory::lw::<C, S, R>(state, ram, snapshotter, instr),

                InstructionName::Sh => memory::sh::<C, S, R>(state, ram, snapshotter, instr),
                InstructionName::Lhu => {
                    memory::lh::<C, S, R, false>(state, ram, snapshotter, instr)
                }
                InstructionName::Lh => memory::lh::<C, S, R, true>(state, ram, snapshotter, instr),

                InstructionName::Sb => memory::sb::<C, S, R>(state, ram, snapshotter, instr),
                InstructionName::Lbu => {
                    memory::lb::<C, S, R, false>(state, ram, snapshotter, instr)
                }
                InstructionName::Lb => memory::lb::<C, S, R, true>(state, ram, snapshotter, instr),

                InstructionName::Add => {
                    add_sub::add_op::<C, S, R, false>(state, ram, snapshotter, instr)
                }
                InstructionName::Addi => {
                    add_sub::add_op::<C, S, R, true>(state, ram, snapshotter, instr)
                }
                InstructionName::Sub => add_sub::sub_op::<C, S, R>(state, ram, snapshotter, instr),
                InstructionName::Xor => {
                    binary::xor::<C, S, R, false>(state, ram, snapshotter, instr)
                }
                InstructionName::Xori => {
                    binary::xor::<C, S, R, true>(state, ram, snapshotter, instr)
                }
                InstructionName::And => {
                    binary::and::<C, S, R, false>(state, ram, snapshotter, instr)
                }
                InstructionName::Andi => {
                    binary::and::<C, S, R, true>(state, ram, snapshotter, instr)
                }
                InstructionName::Or => binary::or::<C, S, R, false>(state, ram, snapshotter, instr),
                InstructionName::Ori => binary::or::<C, S, R, true>(state, ram, snapshotter, instr),
                InstructionName::Sll => {
                    shifts::sll::<C, S, R, false>(state, ram, snapshotter, instr)
                }
                InstructionName::Slli => {
                    shifts::sll::<C, S, R, true>(state, ram, snapshotter, instr)
                }
                InstructionName::Srl => {
                    shifts::srl::<C, S, R, false>(state, ram, snapshotter, instr)
                }
                InstructionName::Srli => {
                    shifts::srl::<C, S, R, true>(state, ram, snapshotter, instr)
                }
                InstructionName::Sra => {
                    shifts::sra::<C, S, R, false>(state, ram, snapshotter, instr)
                }
                InstructionName::Srai => {
                    shifts::sra::<C, S, R, true>(state, ram, snapshotter, instr)
                }
                InstructionName::Mul => mul_div::mul::<C, S, R>(state, ram, snapshotter, instr),
                InstructionName::Mulhu => mul_div::mulhu::<C, S, R>(state, ram, snapshotter, instr),
                InstructionName::Divu => mul_div::divu::<C, S, R>(state, ram, snapshotter, instr),
                InstructionName::Remu => mul_div::remu::<C, S, R>(state, ram, snapshotter, instr),

                InstructionName::ZimopAdd => {
                    mop::mop_addmod::<C, S, R>(state, ram, snapshotter, instr)
                }
                InstructionName::ZimopSub => {
                    mop::mop_submod::<C, S, R>(state, ram, snapshotter, instr)
                }
                InstructionName::ZimopMul => {
                    mop::mop_mulmod::<C, S, R>(state, ram, snapshotter, instr)
                }

                InstructionName::ZicsrNonDeterminismRead => {
                    zicsr::nd_read::<C, S, R, ND>(state, ram, snapshotter, instr, nd)
                }
                InstructionName::ZicsrNonDeterminismWrite => {
                    zicsr::nd_write::<C, S, R, ND>(state, ram, snapshotter, instr, nd)
                }
                InstructionName::ZicsrDelegation => {
                    zicsr::call_delegation::<C, S, R>(state, ram, snapshotter, instr)
                }
                a @ _ => {
                    panic!("Unknown instruction {:?}", a);
                }
                _ => core::hint::unreachable_unchecked(),
            }
        }
    }
}

// pub fn run_default(
//     num_snapshots: usize,
//     ram: &mut RamWithRomRegion<5>,
//     snapshotter: &mut SimpleSnapshotter<DelegationsCounters, 5>,
//     instruction_tape: &mut SimpleTape,
//     snapshot_period: usize,
// ) -> bool {
//     let mut state = State::initial_with_counters(DelegationsCounters::default());
//     VM::<DelegationsCounters>::run_basic_unrolled::<
//         SimpleSnapshotter<DelegationsCounters, 5>,
//         RamWithRomRegion<5>,
//         _,
//     >(
//         &mut state,
//         num_snapshots,
//         ram,
//         snapshotter,
//         instruction_tape,
//         snapshot_period,
//         &mut (),
//     )
// }

#[cfg(test)]
pub(crate) mod test {
    use crate::ir::{preprocess_bytecode, FullUnsignedMachineDecoderConfig};

    use super::*;
    use std::path::Path;

    pub(crate) fn read_binary(path: &Path) -> (Vec<u8>, Vec<u32>) {
        use std::io::Read;
        let mut file = std::fs::File::open(path).expect("must open provided file");
        let mut buffer = vec![];
        file.read_to_end(&mut buffer).expect("must read the file");
        assert_eq!(buffer.len() % core::mem::size_of::<u32>(), 0);
        let mut binary = Vec::with_capacity(buffer.len() / core::mem::size_of::<u32>());
        for el in buffer.as_chunks::<4>().0 {
            binary.push(u32::from_le_bytes(*el));
        }

        (buffer, binary)
    }

    #[test]
    fn test_simple_fibonacci() {
        let (_, binary) = read_binary(&Path::new("examples/fibonacci/app.bin"));
        let (_, text) = read_binary(&Path::new("examples/fibonacci/app.text"));
        let instructions: Vec<Instruction> =
            preprocess_bytecode::<FullUnsignedMachineDecoderConfig>(&text);
        let tape = SimpleTape::new(&instructions);
        let mut ram = RamWithRomRegion::<5>::from_rom_content(&binary, 1 << 30);

        let cycles_bound = 1 << 30;

        let mut state = State::initial_with_counters(DelegationsCounters::default());

        let mut snapshotter = SimpleSnapshotter::<
            _,
            { common_constants::rom::ROM_SECOND_WORD_BITS },
            Vec<(u32, (u32, u32))>,
        >::new_with_cycle_limit(cycles_bound, state);

        let now = std::time::Instant::now();
        VM::<DelegationsCounters>::run_basic_unrolled::<_, _, _>(
            &mut state,
            &mut ram,
            &mut snapshotter,
            &tape,
            cycles_bound,
            &mut (),
        );
        let elapsed = now.elapsed();

        let cycles_elapsed = (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;

        println!(
            "Performance is {} MHz ({} cycles)",
            (cycles_elapsed as f64) / (elapsed.as_micros() as f64),
            cycles_elapsed,
        );

        println!(
            "Captured {} snapshots, in total of {} memory reads",
            snapshotter.snapshots.len(),
            snapshotter.reads_buffer.len()
        );

        dbg!(&state.registers[10..18]);
    }

    #[test]
    fn test_keccak_f1600() {
        let (_, binary) = read_binary(&Path::new("examples/keccak_f1600/app.bin"));
        let (_, text) = read_binary(&Path::new("examples/keccak_f1600/app.text"));
        let instructions: Vec<Instruction> =
            preprocess_bytecode::<FullUnsignedMachineDecoderConfig>(&text);
        let tape = SimpleTape::new(&instructions);
        let mut ram = RamWithRomRegion::<5>::from_rom_content(&binary, 1 << 30);

        let cycles_bound = 1 << 30;

        let mut state = State::initial_with_counters(DelegationsCounters::default());

        let mut snapshotter = SimpleSnapshotter::<
            _,
            { common_constants::rom::ROM_SECOND_WORD_BITS },
            Vec<(u32, (u32, u32))>,
        >::new_with_cycle_limit(cycles_bound, state);

        let now = std::time::Instant::now();
        VM::<DelegationsCounters>::run_basic_unrolled::<_, _, _>(
            &mut state,
            &mut ram,
            &mut snapshotter,
            &tape,
            cycles_bound,
            &mut (),
        );
        let elapsed = now.elapsed();

        let cycles_elapsed = (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;

        println!(
            "Performance is {} MHz ({} cycles)",
            (cycles_elapsed as f64) / (elapsed.as_micros() as f64),
            cycles_elapsed,
        );

        println!(
            "Captured {} snapshots, in total of {} memory reads",
            snapshotter.snapshots.len(),
            snapshotter.reads_buffer.len()
        );

        assert_eq!(
            state.counters.keccak_calls % common_constants::NUM_DELEGATION_CALLS_FOR_KECCAK_F1600,
            0
        );

        dbg!(state.pc);
        dbg!(state.timestamp);

        dbg!(&state.registers[10..18]);

        dbg!(state.registers[0]);
    }

    #[test]
    fn test_reference_block_exec() {
        use crate::ir::*;
        use risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;

        let (_, binary) = read_binary(&Path::new("examples/zksync_os/app.bin"));
        let (_, text) = read_binary(&Path::new("examples/zksync_os/app.text"));

        let (witness, _) = read_binary(&Path::new("examples/zksync_os/23620012_witness"));
        let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
        let witness: Vec<_> = witness
            .as_chunks::<4>()
            .0
            .iter()
            .map(|el| u32::from_be_bytes(*el))
            .collect();
        let mut source = QuasiUARTSource::new_with_reads(witness);

        let instructions: Vec<Instruction> =
            preprocess_bytecode::<FullUnsignedMachineDecoderConfig>(&text);
        let tape = SimpleTape::new(&instructions);
        let mut ram =
            RamWithRomRegion::<{ common_constants::rom::ROM_SECOND_WORD_BITS }>::from_rom_content(
                &binary,
                1 << 30,
            );

        let cycles_bound = 1 << 30;

        let mut state = State::initial_with_counters(DelegationsCounters::default());
        let mut snapshotter = SimpleSnapshotter::new_with_cycle_limit(cycles_bound, state);

        let now = std::time::Instant::now();
        VM::<DelegationsCounters>::run_basic_unrolled::<
            SimpleSnapshotter<DelegationsCounters, { common_constants::rom::ROM_SECOND_WORD_BITS }>,
            _,
            _,
        >(
            &mut state,
            &mut ram,
            &mut snapshotter,
            &tape,
            cycles_bound,
            &mut source,
        );
        let elapsed = now.elapsed();

        let final_timestamp = state.timestamp;
        assert_eq!(final_timestamp % TIMESTAMP_STEP, 0);
        let num_instructions = (final_timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;
        println!(
            "Frequency is {} MHz over {} instructions",
            (num_instructions as f64) * 1000f64 / (elapsed.as_nanos() as f64),
            num_instructions,
        );

        println!("PC = 0x{:08x}", state.pc);
        dbg!(state.registers.map(|el| el.value));
    }
}
