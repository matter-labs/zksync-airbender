use std::path::Path;

use crate::abstractions::memory::MemorySource;
use crate::abstractions::memory::VectorMemoryImpl;
use crate::abstractions::non_determinism::NonDeterminismCSRSource;
use crate::abstractions::non_determinism::QuasiUARTSource;
use crate::cycle::state::RiscV32MachineV1;
use crate::cycle::state::StateTracer;
use crate::cycle::IMStandardIsaConfig;
use crate::cycle::MachineConfig;
use crate::mmu::NoMMU;
use crate::setup::BaselineWithND;
use crate::setup::DefaultSetup;
use crate::sim::BinarySource;
use crate::sim::ProfilerConfig;
use crate::sim::RiscV32Machine;
use crate::sim::RiscV32MachineSetup;
use crate::sim::RunResult;
use crate::sim::RunResultMeasurements;
use crate::sim::Simulator;
use crate::sim::SimulatorConfig;

pub const DEFAULT_ENTRY_POINT: u32 = 0x01000000;
pub const CUSTOM_ENTRY_POINT: u32 = 0;

pub fn run_simple_simulator(config: SimulatorConfig) -> [u32; 8] {
    run_simple_with_entry_point(config)
}

pub fn run_simple_with_entry_point(config: SimulatorConfig) -> [u32; 8] {
    let result =
        run_simple_with_entry_point_and_non_determimism_source(config, QuasiUARTSource::default());
    let registers = result.state.registers;
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
) -> RunResult<BaselineWithND<S, IMStandardIsaConfig>> {
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
) -> RunResult<BaselineWithND<S, C>> {
    let setup = BaselineWithND::<_, C>::new(non_determinism_source);

    let mut sim = Simulator::<_, C>::new(config, setup);

    sim.run(|_, _| {}, |_, _| {})
}

pub fn run_simple_for_num_cycles<S: NonDeterminismCSRSource<VectorMemoryImpl>, C: MachineConfig>(
    binary: &[u8],
    entry_point: u32,
    cycles: usize,
    mut non_determinism_source: S,
) -> RunResult<BaselineWithND<S, C>> {
    let setup = BaselineWithND::<_, C>::new(non_determinism_source);

    let mut sim = Simulator::<_, C>::new(
        SimulatorConfig::new(BinarySource::Slice(binary), entry_point, cycles, None),
        setup,
    );

    let exec = sim.run(|_, _| {}, |_, _| {});

    exec
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

// pub fn run_simulator_with_traces(config: SimulatorConfig) -> (StateTracer, ()) {
//     run_simulator_with_traces_for_config(config)
// }

pub fn run_simulator_with_traces_for_config<C: MachineConfig>(
    config: SimulatorConfig,
) -> RunResult<DefaultSetup> {
    let setup = DefaultSetup::default();

    let mut state_tracer = StateTracer::new_for_num_cycles(config.cycles);

    let mut sim = Simulator::<DefaultSetup, C>::new(config, setup);

    state_tracer.insert(0, sim.machine.state().clone());

    let exec = sim.run(
        |_, _| {},
        |sim, cycle| {
            println!(
                "mtvec: {:?}",
                sim.machine.state.machine_mode_trap_data.setup.tvec
            );
            state_tracer.insert(cycle + 1, sim.machine.state().clone());
        },
    );

    exec
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
