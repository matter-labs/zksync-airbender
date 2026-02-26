use prover::common_constants;
use prover::risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::vm;
use riscv_transpiler::vm::RamWithRomRegion;
use riscv_transpiler::vm::SimpleTape;
use riscv_transpiler::vm::State;

use super::types::CountersT;
use crate::rv32im::binary::Binary;
use crate::rv32im::common::constants::TOTAL_MEM_SIZE;
use crate::rv32im::types::Snapshotter;
use crate::rv32im::GuestResult;
use crate::rv32im::DEFAULT_CYCLES;

type Ram = RamWithRomRegion<{ common_constants::ROM_SECOND_WORD_BITS }>;

#[derive(Copy, Clone)]
pub struct VMSnapshot<'vm> {
    ram: &'vm Ram,
    state: State<CountersT>,
    snapshotter: &'vm Snapshotter,
    tape: &'vm SimpleTape,

    #[cfg(feature = "prover")]
    binary: &'vm [u32],
    #[cfg(feature = "prover")]
    text: Option<&'vm [u32]>,
}

impl<'vm> VMSnapshot<'vm> {
    pub fn snapshotter(&self) -> &'vm Snapshotter {
        self.snapshotter
    }

    pub fn state(&self) -> State<vm::DelegationsAndFamiliesCounters> {
        self.state
    }

    pub fn ram(&self) -> &'vm Ram {
        self.ram
    }

    pub fn tape(&self) -> &'vm SimpleTape {
        self.tape
    }

    pub fn cycles_bound(&self) -> usize {
        VM::cycle_count()
    }

    #[cfg(feature = "prover")]
    pub fn binary(&self) -> &'vm [u32] {
        self.binary
    }

    #[cfg(feature = "prover")]
    pub fn text(&self) -> &'vm [u32] {
        self.text.unwrap_or(self.binary)
    }
}

pub struct VM {
    finished: bool,
    tape: SimpleTape,
    ram: Ram,
    state: State<CountersT>,
    snapshotter: Snapshotter,
    non_determinism: QuasiUARTSource,

    #[cfg(feature = "prover")]
    binary: Vec<u32>,
    #[cfg(feature = "prover")]
    text: Option<Vec<u32>>,
}

impl VM {
    fn cycle_count() -> usize {
        DEFAULT_CYCLES
    }

    pub fn new(binary: &Binary) -> Self {
        let instructions = binary.instructions();
        let state = State::initial_with_counters(CountersT::default());
        Self {
            finished: false,
            tape: SimpleTape::new(&instructions),
            ram: Ram::from_rom_content(&binary.data_chunks(), TOTAL_MEM_SIZE),
            state,
            snapshotter: Snapshotter::new_with_cycle_limit(Self::cycle_count(), state),
            non_determinism: QuasiUARTSource::default(),
            #[cfg(feature = "prover")]
            binary: binary.data_chunks(),
            #[cfg(feature = "prover")]
            text: binary.text_chunks(),
        }
    }

    pub fn run(&mut self) {
        log::debug!("Starting target VM...");
        let is_program_finished = vm::VM::<CountersT>::run_basic_unrolled(
            &mut self.state,
            &mut self.ram,
            &mut self.snapshotter,
            &self.tape,
            Self::cycle_count(),
            &mut self.non_determinism,
        );
        log::debug!("VM stopped. Program finished? {is_program_finished}");
        self.finished = is_program_finished;
    }

    pub fn output_registers(&self) -> Option<GuestResult> {
        self.finished.then(|| {
            std::array::from_fn(|idx| {
                // We want registers A0-7, which are aliases to registers X10-17
                let reg_idx = idx + 10;
                self.state.registers[reg_idx].value
            })
        })
    }

    pub fn final_state(&self) -> &State<CountersT> {
        &self.state
    }

    pub fn snapshot(&self) -> VMSnapshot<'_> {
        VMSnapshot {
            ram: &self.ram,
            state: self.state,
            snapshotter: &self.snapshotter,
            #[cfg(feature = "prover")]
            binary: &self.binary,
            #[cfg(feature = "prover")]
            text: self.text.as_deref(),
            tape: &self.tape,
        }
    }

    #[cfg(feature = "prover")]
    fn prove(&mut self) {
        crate::rv32im::prover::prove_vm_result(self.snapshot());
    }
}

macro_rules! panic_or_abort {
    ($abort:expr, $($arg:tt)*) => {
        if $abort {
                        log::error!($( $arg )*);
                        std::process::abort();
                    } else {
                        panic!($( $arg )*);
                    }
    };
}

/// Either returns `None` if the string matches the one emitted by the panic raised if the
/// simulator encounters an exception or aborts the whole process.
fn check_panic_string<const ABORT: bool>(s: impl AsRef<str>) -> Option<GuestResult> {
    let s = s.as_ref();
    log::debug!("Panic string: {s:?}");
    if s.starts_with("Illegal instruction encounteted at PC =")
        || s.starts_with("Unaligned memory access at PC =")
    {
        return None;
    }

    panic_or_abort!(ABORT, "Target raised unhandled error: {s}")
    // if ABORT {
    //    log::error!("Target raised unhandled error: {s}");
    //    std::process::abort()
    //} else {
    //    panic!("Target raised unhandled error: {s}")
    //}
}

pub fn run_vm<const ABORT: bool>(data: &[u8], text: Option<&[u8]>) -> Option<GuestResult> {
    match std::panic::catch_unwind(|| {
        let binary = Binary::new(data, text);
        let mut vm = VM::new(&binary);
        vm.run();
        let registers = vm.output_registers();
        #[cfg(feature = "prover")]
        vm.prove();
        registers
    }) {
        Ok(tr) => tr,
        Err(err) => match err.downcast::<String>() {
            Ok(s) => check_panic_string::<ABORT>(*s),
            Err(err) => match err.downcast::<&'static str>() {
                Ok(s) => check_panic_string::<ABORT>(*s),
                Err(_) => {
                    panic_or_abort!(ABORT, "Unknown error type");
                    // if ABORT {
                    //    log::error!("Unknown error type");
                    //    std::process::abort();
                    //} else {
                    //    panic!("Unknown error type");
                    //}
                }
            },
        },
    }
}
