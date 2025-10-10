use crate::ir::DelegationType;
use crate::ir::Instruction;
use crate::ir::InstructionName;
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

pub trait Counters: 'static + Clone + Copy + Debug {
    fn bump_bigint(&mut self);
    fn bump_blake2_round_function(&mut self);
    fn bump_keccak_special5(&mut self);
    fn bump_non_determinism(&mut self);
    fn log_circuit_family<const FAMILY: u8>(&mut self);
    fn get_calls_to_circuit_family<const FAMILY: u8>(&self) -> usize;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

pub trait Snapshotter<C: Counters>: 'static {
    fn take_snapshot(&mut self, state: &State<C>);
    fn append_non_determinism_read(&mut self, value: u32);
    fn append_memory_read(
        &mut self,
        address: u32,
        read_value: u32,
        read_timestamp: TimestampScalar,
        write_timestamp: TimestampScalar,
    );
}

pub trait RAM {
    fn peek_word(&self, address: u32) -> u32;
    fn read_word(&mut self, address: u32, timestamp: TimestampScalar) -> (TimestampScalar, u32);
    fn mask_read_for_witness(&self, address: &mut u32, value: &mut u32);
    fn write_word(
        &mut self,
        address: u32,
        word: u32,
        timestamp: TimestampScalar,
    ) -> (TimestampScalar, u32);
}

pub trait InstructionTape {
    fn read_instruction(&self, pc: u32) -> Instruction;
}

// there is no interpretation of methods here, it's just read/write and that's all
pub trait NonDeterminismCSRSource<R: RAM + ?Sized> {
    fn read(&mut self) -> u32;

    // we in general can allow CSR source to peek into memory (readonly)
    // to perform adhoc computations to prepare result. This will allow to save on
    // passing large structures
    fn write_with_memory_access(&mut self, ram: &R, value: u32);
}

impl<R: RAM> NonDeterminismCSRSource<R> for () {
    fn read(&mut self) -> u32 {
        0u32
    }
    fn write_with_memory_access(&mut self, _ram: &R, _value: u32) {}
}

impl<R: RAM> NonDeterminismCSRSource<R>
    for risc_v_simulator::abstractions::non_determinism::QuasiUARTSource
{
    fn read(&mut self) -> u32 {
        self.oracle.pop_front().unwrap_or_default()
    }

    fn write_with_memory_access(&mut self, _ram: &R, value: u32) {
        self.write_state.process_write(value);
    }
}

pub struct VM<C: Counters> {
    pub state: State<C>,
}

impl<C: Counters> VM<C> {
    pub fn run_basic_unrolled<S: Snapshotter<C>, R: RAM, ND: NonDeterminismCSRSource<R>>(
        state: &mut State<C>,
        num_snapshots: usize,
        ram: &mut R,
        snapshotter: &mut S,
        instruction_tape: &impl InstructionTape,
        snapshot_period: usize,
        nd: &mut ND,
    ) -> bool {
        use crate::vm::instructions::*;

        for _ in 0..num_snapshots {
            for _ in 0..snapshot_period {
                unsafe {
                    let pc = state.pc;
                    let instr = instruction_tape.read_instruction(pc);
                    match instr.name {
                        InstructionName::Illegal => illegal(state, ram, snapshotter, instr),
                        InstructionName::Lui => {
                            lui_auipc::lui::<C, S, R>(state, ram, snapshotter, instr)
                        }
                        InstructionName::Auipc => {
                            lui_auipc::auipc::<C, S, R>(state, ram, snapshotter, instr)
                        }

                        InstructionName::Jal => {
                            jal_jalr::jal::<C, S, R>(state, ram, snapshotter, instr)
                        }
                        InstructionName::Jalr => {
                            jal_jalr::jalr::<C, S, R>(state, ram, snapshotter, instr)
                        }

                        InstructionName::Slt => {
                            slt::slt::<C, S, R, false>(state, ram, snapshotter, instr)
                        }
                        InstructionName::Slti => {
                            slt::slt::<C, S, R, true>(state, ram, snapshotter, instr)
                        }

                        InstructionName::Sltu => {
                            slt::sltu::<C, S, R, false>(state, ram, snapshotter, instr)
                        }
                        InstructionName::Sltiu => {
                            slt::sltu::<C, S, R, true>(state, ram, snapshotter, instr)
                        }

                        InstructionName::Branch => {
                            branch::branch::<C, S, R>(state, ram, snapshotter, instr)
                        }

                        InstructionName::Sw => {
                            memory::sw::<C, S, R>(state, ram, snapshotter, instr)
                        }
                        InstructionName::Lw => {
                            memory::lw::<C, S, R>(state, ram, snapshotter, instr)
                        }

                        InstructionName::Sh => {
                            memory::sh::<C, S, R>(state, ram, snapshotter, instr)
                        }
                        InstructionName::Lhu => {
                            memory::lh::<C, S, R, false>(state, ram, snapshotter, instr)
                        }
                        InstructionName::Lh => {
                            memory::lh::<C, S, R, true>(state, ram, snapshotter, instr)
                        }

                        InstructionName::Sb => {
                            memory::sb::<C, S, R>(state, ram, snapshotter, instr)
                        }
                        InstructionName::Lbu => {
                            memory::lb::<C, S, R, false>(state, ram, snapshotter, instr)
                        }
                        InstructionName::Lb => {
                            memory::lb::<C, S, R, true>(state, ram, snapshotter, instr)
                        }

                        InstructionName::Add => {
                            add_sub::add_op::<C, S, R, false>(state, ram, snapshotter, instr)
                        }
                        InstructionName::Addi => {
                            add_sub::add_op::<C, S, R, true>(state, ram, snapshotter, instr)
                        }
                        InstructionName::Sub => {
                            add_sub::sub_op::<C, S, R>(state, ram, snapshotter, instr)
                        }
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
                        InstructionName::Or => {
                            binary::and::<C, S, R, false>(state, ram, snapshotter, instr)
                        }
                        InstructionName::Ori => {
                            binary::and::<C, S, R, true>(state, ram, snapshotter, instr)
                        }
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
                        InstructionName::Mul => {
                            mul_div::mul::<C, S, R>(state, ram, snapshotter, instr)
                        }
                        InstructionName::Mulhu => {
                            mul_div::mulhu::<C, S, R>(state, ram, snapshotter, instr)
                        }
                        InstructionName::Divu => {
                            mul_div::divu::<C, S, R>(state, ram, snapshotter, instr)
                        }
                        InstructionName::Remu => {
                            mul_div::remu::<C, S, R>(state, ram, snapshotter, instr)
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
                        _ => core::hint::unreachable_unchecked(),
                    }
                    state.timestamp += TIMESTAMP_STEP;
                    if state.pc == pc {
                        snapshotter.take_snapshot(&*state);
                        return true;
                    }
                }
            }

            snapshotter.take_snapshot(&*state);
        }

        false
    }
}

pub fn run_default(
    num_snapshots: usize,
    ram: &mut RamWithRomRegion<5>,
    snapshotter: &mut SimpleSnapshotter<DelegationsCounters, 5>,
    instruction_tape: &mut SimpleTape,
    snapshot_period: usize,
) -> bool {
    let mut state = State::initial_with_counters(DelegationsCounters::default());
    VM::<DelegationsCounters>::run_basic_unrolled::<
        SimpleSnapshotter<DelegationsCounters, 5>,
        RamWithRomRegion<5>,
        _,
    >(
        &mut state,
        num_snapshots,
        ram,
        snapshotter,
        instruction_tape,
        snapshot_period,
        &mut (),
    )
}

#[cfg(test)]
pub(crate) mod test {
    use crate::ir::decode;
    use crate::ir::FullUnsignedMachineDecoderConfig;

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
        let instructions: Vec<Instruction> = text
            .into_iter()
            .map(|el| decode::<FullUnsignedMachineDecoderConfig>(el))
            .collect();
        let tape = SimpleTape::new(&instructions);
        let mut ram = RamWithRomRegion::<5>::from_rom_content(&binary, 1 << 30);
        let period = 1 << 20;
        let num_snapshots = 1000;
        let cycles_bound = period * num_snapshots;

        let mut state = State::initial_with_counters(DelegationsCounters::default());

        let mut snapshotter = SimpleSnapshotter::new_with_cycle_limit(cycles_bound, period, state);

        let now = std::time::Instant::now();
        VM::<DelegationsCounters>::run_basic_unrolled::<
            SimpleSnapshotter<DelegationsCounters, 5>,
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

        dbg!(&state.registers[10..18]);
    }

    #[test]
    fn test_keccak_f1600() {
        let (_, binary) = read_binary(&Path::new("examples/keccak_f1600/app.bin"));
        let (_, text) = read_binary(&Path::new("examples/keccak_f1600/app.text"));
        let instructions: Vec<Instruction> = text
            .into_iter()
            .map(|el| decode::<FullUnsignedMachineDecoderConfig>(el))
            .collect();
        let tape = SimpleTape::new(&instructions);
        let mut ram = RamWithRomRegion::<5>::from_rom_content(&binary, 1 << 30);
        let period = 1 << 20;
        let num_snapshots = 1000;
        let cycles_bound = period * num_snapshots;

        let mut state = State::initial_with_counters(DelegationsCounters::default());

        let mut snapshotter = SimpleSnapshotter::new_with_cycle_limit(cycles_bound, period, state);

        let now = std::time::Instant::now();
        VM::<DelegationsCounters>::run_basic_unrolled::<
            SimpleSnapshotter<DelegationsCounters, 5>,
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

        dbg!(&state.registers[10..18]);
    }
}
