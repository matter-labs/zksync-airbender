use std::marker::PhantomData;
use std::path::{Path, PathBuf};

use diag::ProfilerStats;

use crate::abstractions::csr_processor::CustomCSRProcessor;
use crate::cycle::state::{RiscV32ObservableState, NUM_REGISTERS};
use crate::cycle::IMStandardIsaConfig;
use crate::cycle::MachineConfig;
use crate::mmu::NoMMU;
use crate::qol::PipeOp;
use crate::{
    abstractions::{
        memory::MemorySource,
        non_determinism::NonDeterminismCSRSource,
        tracer::Tracer,
    },
    cycle::state::RiscV32State as RiscV32StateNaive,
    mmu::MMUImplementation,
    runner::DEFAULT_ENTRY_POINT,
};

use self::diag::Profiler;

pub(crate) mod diag;

pub(crate) struct Simulator<S, C> 
where 
    S: RiscV32MachineSetup,
    C: MachineConfig
{
    pub(crate) machine: S::M,
    // pub(crate) memory_source: MS,
    // pub(crate) memory_tracer: TR,
    // pub(crate) mmu: MMU,
    // pub(crate) non_determinism_source: ND,
    //
    // pub(crate) state: RS,
    cycles: usize,
    executed: bool,

    profiler: Option<Profiler>,
    phantom: PhantomData<C>,
}

impl<S, C> Simulator<S, C>
where 
    S: RiscV32MachineSetup, 
    C: MachineConfig 
{
    pub(crate) fn new(
        config: SimulatorConfig,
        setup: S,
    ) -> Self {
        Self {
            machine: setup.instantiate(&config),
            cycles: config.cycles,
            executed: false,
            profiler: Profiler::new(config),
            phantom: PhantomData,
        }
    }

    pub(crate) fn run<FnPre, FnPost>(
        mut self,
        mut fn_pre: FnPre,
        mut fn_post: FnPost,
    ) -> RunResult<S>
    where
        FnPre: FnMut(&mut Self, usize),
        FnPost: FnMut(&mut Self, usize),
    {
        // TODO: consume self on run
        if self.executed { panic!("Can run only once.") }
        self.executed = true;

        let now = std::time::Instant::now();
        let mut previous_pc = self.machine.state().pc;
        let mut end_of_execution_reached = false;
        let mut cycles = 0;

        for cycle in 0..self.cycles as usize {
            if let Some(profiler) = self.profiler.as_mut() {
                profiler.pre_cycle::<S, C>(
                    &mut self.machine,
                    // &mut self.state,
                    // &mut self.memory_source,
                    // &mut self.memory_tracer,
                    // &mut self.mmu,
                    cycle,
                );
            }

            fn_pre(&mut self, cycle);

            self.machine.cycle();

            // RiscV32Machine::<C>::cycle(
            //     &mut self.state,
            //     &mut self.memory_source,
            //     &mut self.memory_tracer,
            //     &mut self.mmu,
            //     &mut self.non_determinism_source,
            // );

            fn_post(&mut self, cycle);

            if self.machine.state().pc == previous_pc {
                end_of_execution_reached = true;
                cycles = cycle;
                println!("Took {} cycles to finish", cycle);
                break;
            }
            previous_pc = self.machine.state().pc;
        }

        assert!(
            end_of_execution_reached,
            "program failed to each the end of execution over {} cycles",
            self.cycles
        );

        let exec_time = now.elapsed();

        if let Some(profiler) = self.profiler.as_mut() {
            println!("Profiler begins execution");
            profiler.print_stats();
            profiler.write_stacktrace();
        }

        let (state, memory_source, non_determinism_source, memory_tracer) = self.machine.deconstruct();

        RunResult {
            state,
            memory_source,
            memory_tracer,
            non_determinism_source,
            measurements: RunResultMeasurements {
                time: RunResultTimes { 
                    exec_time,
                    exec_cycles: cycles,
                },
                profiler: self.profiler.as_ref().map(|x| x.stats.clone()),

            },
            phantom: PhantomData,
        }
    }
}


pub(crate) trait RiscV32MachineSetup
where 
    Self: Sized
{
    type ND: NonDeterminismCSRSource<Self::MS>;
    type MS: MemorySource;
    type TR: Tracer<Self::C>;
    type MMU: MMUImplementation<Self::MS, Self::TR, Self::C>;
    type C: MachineConfig;

    type M: RiscV32Machine<Self::ND, Self::MS, Self::TR, Self::MMU, Self::C>;

    fn instantiate(self, config: &SimulatorConfig) -> Self::M {
        let mut machine = self.instantiate(config);

        machine.populate_memory(config.entry_point, config.bin.to_iter());

        machine
    }
}

pub(crate) trait RiscV32Machine<ND, MS, TR, MMU, C> 
    where 
    ND: NonDeterminismCSRSource<MS>,
    MS: MemorySource,
    TR: Tracer<C>,
    MMU: MMUImplementation<MS, TR, C>,
    C: MachineConfig,
{
    // fn initial(entry_addr: u32) -> Self;
    fn cycle(&mut self);

    fn state(&self) -> &RiscV32ObservableState;
    fn non_determinism_source(&self) -> &ND;

    fn deconstruct(self) -> (RiscV32ObservableState, MS, ND, TR);

    fn collect_stacktrace(
        &mut self,
        symbol_info: &diag::SymbolInfo,
        dwarf_cache: &mut diag::DwarfCache,
        cycle: usize
    ) -> diag::StacktraceCollectionResult;

    fn populate_memory<B>(&mut self, at: u32, bytes: B) 
        where B: IntoIterator<Item = u8>;

    // fn pc(&self) -> u32;
    // fn sapt(&self) -> u32;
    // fn registers(&self) -> &[u32; NUM_REGISTERS];
}

pub enum BinarySource<'a> {
    Path(PathBuf),
    Slice(&'a [u8])
}

impl<'a> BinarySource<'a> {
    pub fn to_iter(&self) -> Box<dyn Iterator<Item = u8> + 'a> {

        fn read_bin<P: AsRef<Path>>(path: P) -> Vec<u8> { dbg!(path.as_ref());
            let mut file = std::fs::File::open(path).expect("must open provided file");
            let mut buffer = vec![];
            std::io::Read::read_to_end(&mut file, &mut buffer).expect("must read the file");

            assert_eq!(buffer.len() % 4, 0);
            dbg!(buffer.len() / 4);

            buffer
        }

        match self {
            BinarySource::Slice(items) => Box::new(items.iter().copied()),
            BinarySource::Path(path_buf) => Box::new(read_bin(path_buf).into_iter()),
        }
    }
}

pub enum Machine {
    V1,
    ProofUnrolled,
}

pub struct SimulatorConfig<'a> {
    pub bin: BinarySource<'a>,
    pub entry_point: u32,
    pub cycles: usize,
    pub diagnostics: Option<DiagnosticsConfig>,
}

impl<'a> SimulatorConfig<'a> {
    pub fn simple<P: AsRef<Path>>(bin_path: P) -> Self {
        Self::new(
            bin_path.as_ref().to_owned().to(BinarySource::Path),
            DEFAULT_ENTRY_POINT,
            1 << 22,
            None,
        )
    }

    pub fn new(
        bin_path: BinarySource<'a>,
        entry_point: u32,
        cycles: usize,
        diagnostics: Option<DiagnosticsConfig>,
    ) -> Self {
        Self {
            bin: bin_path,
            entry_point,
            cycles,
            diagnostics,
        }
    }
}

#[derive(Clone)]
pub struct DiagnosticsConfig {
    symbols_path: PathBuf,
    pub profiler_config: Option<ProfilerConfig>,
}

impl DiagnosticsConfig {
    pub fn new(symbols_path: PathBuf) -> Self {
        Self {
            symbols_path,
            profiler_config: None,
        }
    }
}

#[derive(Clone)]
pub struct ProfilerConfig {
    output_path: PathBuf,
    pub reverse_graph: bool,
    pub frequency_recip: usize,
}

impl ProfilerConfig {
    pub fn new(output_path: PathBuf) -> Self {
        Self {
            output_path,
            reverse_graph: false,
            frequency_recip: 100,
        }
    }
}

pub struct RunResult<S: RiscV32MachineSetup> {
    pub non_determinism_source: S::ND,
    pub memory_tracer: S::TR,
    pub memory_source: S::MS,
    pub state: RiscV32ObservableState,
    pub measurements: RunResultMeasurements,
    phantom: PhantomData<S::C>,
}

pub struct RunResultMeasurements {
    time: RunResultTimes,
    profiler: Option<ProfilerStats>
}

pub struct RunResultTimes {
    exec_time: std::time::Duration,
    exec_cycles: usize,
}

impl RunResultTimes {
    pub fn freq(&self) -> usize {
        self.exec_cycles * 1000 / self.exec_time.as_millis() as usize
    }
}

