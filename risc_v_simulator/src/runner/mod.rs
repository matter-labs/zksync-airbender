use std::path::Path;

use crate::abstractions::non_determinism::NonDeterminismCSRSource;
use crate::abstractions::non_determinism::QuasiUARTSource;
use crate::cycle::state::StateTracer;
use crate::cycle::IMStandardIsaConfig;
use crate::cycle::MachineConfig;
use crate::mmu::NoMMU;
use crate::sim::Simulator;
use crate::sim::SimulatorConfig;
use crate::{abstractions::memory::VectorMemoryImpl, cycle::state::RiscV32State};

pub const DEFAULT_ENTRY_POINT: u32 = 0x01000000;
pub const CUSTOM_ENTRY_POINT: u32 = 0;

pub fn run_simple_simulator(config: SimulatorConfig) -> [u32; 8] {
    run_simple_with_entry_point(config)
}

pub fn run_simple_with_entry_point(config: SimulatorConfig) -> [u32; 8] {
    let (_, state) =
        run_simple_with_entry_point_and_non_determimism_source(config, QuasiUARTSource::default());
    let registers = state.registers;
    [
        registers[10],
        registers[11],
        registers[12],
        registers[13],
        registers[14],
        registers[15],
        registers[16],
        registers[17],
    ]
}

pub fn run_simple_with_entry_point_and_non_determimism_source<
    S: NonDeterminismCSRSource<VectorMemoryImpl>,
>(
    config: SimulatorConfig,
    non_determinism_source: S,
) -> (S, RiscV32State<IMStandardIsaConfig>) {
    run_simple_with_entry_point_and_non_determimism_source_for_config::<S, IMStandardIsaConfig>(
        config,
        non_determinism_source,
    )
}

pub fn run_simple_with_entry_point_and_non_determimism_source_for_config<
    S: NonDeterminismCSRSource<VectorMemoryImpl>,
    C: MachineConfig,
>(
    config: SimulatorConfig,
    non_determinism_source: S,
) -> (S, RiscV32State<C>) {
    let state = RiscV32State::<C>::initial(config.entry_point);
    let memory_tracer = ();
    let mmu = NoMMU { sapt: 0 };

    let mut memory = VectorMemoryImpl::new_for_byte_size(1 << 30); // use 1 GB RAM
    memory.load_image(config.entry_point, read_bin(&config.bin_path).into_iter());

    let mut sim = Simulator::new(
        config,
        state,
        memory,
        memory_tracer,
        mmu,
        non_determinism_source,
    );

    sim.run(|_, _| {}, |_, _| {});

    (sim.non_determinism_source, sim.state)
}

pub fn run_simple_for_num_cycles<S: NonDeterminismCSRSource<VectorMemoryImpl>, C: MachineConfig>(
    binary: &[u8],
    entry_point: u32,
    cycles: usize,
    mut non_determinism_source: S,
) -> RiscV32State<C> {
    let mut state = RiscV32State::<C>::initial(entry_point);
    let mut memory_tracer = ();
    let mut mmu = NoMMU { sapt: 0 };

    let mut memory = VectorMemoryImpl::new_for_byte_size(1 << 30); // use 1 GB RAM
    memory.load_image(entry_point, binary.iter().copied());

    let mut previous_pc = entry_point;
    let mut cycle_counter = 0u64;

    for _cycle in 0..cycles as usize {
        cycle_counter += 1;
        RiscV32State::<C>::cycle(
            &mut state,
            &mut memory,
            &mut memory_tracer,
            &mut mmu,
            &mut non_determinism_source,
        );

        if state.pc == previous_pc {
            println!("Took {} cycles to finish", cycle_counter);
            break;
        }
        previous_pc = state.pc;
    }

    state
}

// pub fn run_simple_with_entry_point_with_delegation_and_non_determimism_source<
//     S: NonDeterminismCSRSource<VectorMemoryImpl>,
// >(
//     config: SimulatorConfig,
//     non_determinism_source: S,
// ) -> S {
//     let state = RiscV32State::initial(config.entry_point);
//     let memory_tracer = ();
//     let mmu = NoMMU { sapt: 0 };

//     let mut memory = VectorMemoryImpl::new_for_byte_size(1 << 30); // use 1 GB RAM
//     memory.load_image(config.entry_point, read_bin(&config.bin_path).into_iter());

//     let mut sim = Simulator::new(
//         config,
//         state,
//         memory,
//         memory_tracer,
//         mmu,
//         non_determinism_source,
//     );

//     sim.run(|_, _| {}, |_, _| {});

//     sim.non_determinism_source
// }

pub fn run_simulator_with_traces(config: SimulatorConfig) -> (StateTracer, ()) {
    run_simulator_with_traces_for_config(config)
}

pub fn run_simulator_with_traces_for_config<C: MachineConfig>(
    config: SimulatorConfig,
) -> (StateTracer<C>, ()) {
    let state = RiscV32State::<C>::initial(CUSTOM_ENTRY_POINT);
    let memory_tracer = ();
    let mmu = NoMMU { sapt: state.sapt };
    let non_determinism_source = QuasiUARTSource::default();

    let mut memory = VectorMemoryImpl::new_for_byte_size(1 << 30); // use 1 GB RAM
    memory.load_image(config.entry_point, read_bin(&config.bin_path).into_iter());

    let cycles = config.cycles;
    println!("Will run for up to {} cycles", cycles);

    let mut sim = Simulator::new(
        config,
        state,
        memory,
        memory_tracer,
        mmu,
        non_determinism_source,
    );

    let mut state_tracer = StateTracer::new_for_num_cycles(cycles + 1);
    state_tracer.insert(0, sim.state);

    sim.run(
        |_, _| {},
        |sim, cycle| {
            println!("mtvec: {:?}", sim.state.machine_mode_trap_data.setup.tvec);
            state_tracer.insert(cycle + 1, sim.state);
        },
    );

    (state_tracer, sim.memory_tracer)
}

fn read_bin<P: AsRef<Path>>(path: P) -> Vec<u8> {
    dbg!(path.as_ref());
    let mut file = std::fs::File::open(path).expect("must open provided file");
    let mut buffer = vec![];
    std::io::Read::read_to_end(&mut file, &mut buffer).expect("must read the file");

    assert_eq!(buffer.len() % 4, 0);
    dbg!(buffer.len() / 4);

    buffer
}
