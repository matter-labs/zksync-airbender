//! Checked interpreter execution for feeder prediction and wrap-program gates.

use prover::common_constants::{RomGeometry, TimestampScalar, L1_WRAP_ROM, REGULAR_ROM};
use prover::field::baby_bear::base::BabyBearField;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::cycle::{MachineConfig, ReducedMachineWithDelegation};
use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, Instruction};
use riscv_transpiler::vm::{
    DelegationsAndUnifiedCounters, InstructionTape, RamPeek, RamWithRomRegion, SimpleTape,
    Snapshotter, State, RAM, VM,
};
use serde::{Deserialize, Serialize};
use std::cell::Cell;

const REGULAR_RAM_BOUND: usize = 1 << 30;
const WRAP_RAM_BOUND: usize = 1 << 24;
const WINDOW_BITS: u32 = 23;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct FsvRunReport {
    pub cycles: u64,
    pub output: [u32; 16],
    pub nd_words_remaining: usize,
    #[serde(with = "SerializableCounters")]
    pub counters: DelegationsAndUnifiedCounters,
    /// All 8 MiB windows accessed through RAM, including peek/delegation reads.
    pub touched_windows: Vec<u32>,
    /// Highest byte of any accessed word, including ROM reads.
    pub max_touched_address: u32,
    /// Minimum SP after its first nonzero initialization, or zero if never initialized.
    pub min_sp: u32,
    pub success_pc: u32,
    pub final_pc: u32,
}

#[derive(Serialize, Deserialize)]
#[serde(remote = "DelegationsAndUnifiedCounters")]
struct SerializableCounters {
    non_determinism_reads: usize,
    blake_calls: usize,
    bigint_calls: usize,
    keccak_calls: usize,
    keccak_f1600_calls: usize,
    blake_g_function_calls: usize,
    cycles: usize,
}

pub(crate) fn measure_fsv_run_with_counters_and_rom(
    bin: &[u32],
    text: &[u32],
    nd_words: Vec<u32>,
    cycles_bound: usize,
    rom: RomGeometry,
) -> Result<FsvRunReport, String> {
    if bin.len() > rom.word_size() || text.len() > rom.word_size() {
        return Err("fsv image or text exceeds selected ROM".into());
    }
    let success_pc = super::find_binary_exit_point(bin)?;
    let run = || {
        if rom == L1_WRAP_ROM {
            measure_inner::<3>(
                bin,
                text,
                nd_words,
                cycles_bound,
                success_pc,
                WRAP_RAM_BOUND,
            )
        } else {
            assert_eq!(rom, REGULAR_ROM);
            measure_inner::<6>(
                bin,
                text,
                nd_words,
                cycles_bound,
                success_pc,
                REGULAR_RAM_BOUND,
            )
        }
    };
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(run)).map_err(|payload| {
        let reason = payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .unwrap_or("unknown interpreter panic");
        format!("fsv run aborted before reaching its success exit: {reason}")
    })?
}

fn measure_inner<const ROM_BITS: usize>(
    bin: &[u32],
    text: &[u32],
    nd_words: Vec<u32>,
    cycles_bound: usize,
    success_pc: u32,
    ram_bound: usize,
) -> Result<FsvRunReport, String> {
    use prover::common_constants::{INITIAL_TIMESTAMP, TIMESTAMP_STEP};

    let instructions = preprocess_bytecode::<
        <ReducedMachineWithDelegation as MachineConfig>::DecodingOptions,
        true,
    >(text);
    let tape = CheckedTape {
        inner: SimpleTape::new(&instructions),
        words: instructions.len(),
    };
    let mut ram = CheckedRam::<ROM_BITS>::new(bin, ram_bound);
    let mut observer = StackObserver::default();
    let mut state = State::initial_with_counters(DelegationsAndUnifiedCounters::default());
    let mut nd = QuasiUARTSource::new_with_reads(nd_words);
    let finished = VM::<DelegationsAndUnifiedCounters>::run_basic_unrolled::<_, _, _, BabyBearField>(
        &mut state,
        &mut ram,
        &mut observer,
        &tape,
        cycles_bound,
        &mut nd,
    );
    if !finished {
        return Err(format!("fsv run did not halt within {cycles_bound} cycles"));
    }
    if state.pc != success_pc {
        return Err(format!(
            "fsv run halted at pc 0x{:08x}, not at the success exit 0x{success_pc:08x}",
            state.pc,
        ));
    }
    Ok(FsvRunReport {
        cycles: (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP,
        output: std::array::from_fn(|i| state.registers[10 + i].value),
        nd_words_remaining: nd.oracle.len(),
        counters: state.counters,
        touched_windows: (0..128)
            .filter(|i| ram.windows.get() & (1u128 << i) != 0)
            .collect(),
        max_touched_address: ram.max_address.get(),
        min_sp: observer.min_sp.unwrap_or(0),
        success_pc,
        final_pc: state.pc,
    })
}

struct CheckedTape {
    inner: SimpleTape,
    words: usize,
}

impl InstructionTape for CheckedTape {
    #[inline(always)]
    fn read_instruction(&self, pc: u32) -> Instruction {
        assert!(
            pc.is_multiple_of(4),
            "unaligned fsv instruction fetch at 0x{pc:08x}"
        );
        assert!(
            (pc as usize / 4) < self.words,
            "fsv instruction fetch outside text at 0x{pc:08x}"
        );
        self.inner.read_instruction(pc)
    }
}

/// Every access is checked before delegating to RamWithRomRegion's unchecked
/// implementation. Cells also capture read-only peeks used by delegation/ND adapters.
struct CheckedRam<const ROM_BITS: usize> {
    inner: RamWithRomRegion<ROM_BITS>,
    byte_bound: usize,
    windows: Cell<u128>,
    max_address: Cell<u32>,
}

impl<const ROM_BITS: usize> CheckedRam<ROM_BITS> {
    fn new(bin: &[u32], byte_bound: usize) -> Self {
        assert!(byte_bound <= REGULAR_RAM_BOUND);
        Self {
            inner: RamWithRomRegion::from_rom_content(bin, byte_bound),
            byte_bound,
            windows: Cell::new(0),
            max_address: Cell::new(0),
        }
    }

    #[inline(always)]
    fn check_and_observe(&self, address: u32) {
        assert!(
            address.is_multiple_of(4),
            "unaligned fsv memory access at 0x{address:08x}"
        );
        assert!(
            (address as usize) < self.byte_bound,
            "fsv memory access outside RAM at 0x{address:08x} (bound 0x{:08x})",
            self.byte_bound
        );
        self.windows
            .set(self.windows.get() | (1u128 << (address >> WINDOW_BITS)));
        self.max_address
            .set(self.max_address.get().max(address + 3));
    }
}

impl<const ROM_BITS: usize> RamPeek for CheckedRam<ROM_BITS> {
    #[inline(always)]
    fn peek_word(&self, address: u32) -> u32 {
        self.check_and_observe(address);
        self.inner.peek_word(address)
    }
}

impl<const ROM_BITS: usize> RAM for CheckedRam<ROM_BITS> {
    const ROM_BYTE_SIZE: usize = 1 << (16 + ROM_BITS);

    #[inline(always)]
    fn read_word(&mut self, address: u32, timestamp: TimestampScalar) -> (TimestampScalar, u32) {
        self.check_and_observe(address);
        self.inner.read_word(address, timestamp)
    }

    #[inline(always)]
    fn write_word(
        &mut self,
        address: u32,
        word: u32,
        timestamp: TimestampScalar,
    ) -> (TimestampScalar, u32) {
        self.check_and_observe(address);
        self.inner.write_word(address, word, timestamp)
    }

    fn mask_read_for_witness(&self, address: &mut u32, value: &mut u32) {
        self.inner.mask_read_for_witness(address, value);
    }

    fn skip_if_replaying(&mut self, num_snapshots: usize) {
        self.inner.skip_if_replaying(num_snapshots);
    }
}

#[derive(Default)]
struct StackObserver {
    min_sp: Option<u32>,
}

impl StackObserver {
    fn observe(&mut self, state: &State<DelegationsAndUnifiedCounters>) {
        let sp = state.registers[2].value;
        // Startup initializes SP from zero. After that, a zero SP is an
        // actual observation and must fail a downstream stack-reservation gate.
        if sp != 0 || self.min_sp.is_some() {
            self.min_sp = Some(self.min_sp.map_or(sp, |old| old.min(sp)));
        }
    }
}

impl Snapshotter<DelegationsAndUnifiedCounters> for StackObserver {
    fn take_snapshot_if_needed(&mut self, state: &State<DelegationsAndUnifiedCounters>) -> bool {
        self.observe(state);
        false
    }

    fn take_final_snapshot(&mut self, state: &State<DelegationsAndUnifiedCounters>) {
        self.observe(state);
    }

    fn append_arbitrary_value(&mut self, _value: u32) {}

    fn append_memory_read(
        &mut self,
        _address: u32,
        _read_value: u32,
        _read_timestamp: TimestampScalar,
        _write_timestamp: TimestampScalar,
    ) {
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn program(prefix: &[u32]) -> (Vec<u32>, Vec<u32>) {
        let data_offset = (1 + prefix.len() + riscv_common::EXIT_SEQUENCE.len()) * 4;
        // addi s10, zero, data_offset: the exit sequence loads the output from ROM.
        let mut text = vec![((data_offset as u32) << 20) | (26 << 7) | 0x13];
        text.extend_from_slice(prefix);
        text.extend_from_slice(riscv_common::EXIT_SEQUENCE);
        let mut bin = text.clone();
        bin.extend(100..116);
        (bin, text)
    }

    fn run(prefix: &[u32], nd: Vec<u32>) -> Result<FsvRunReport, String> {
        let (bin, text) = program(prefix);
        measure_fsv_run_with_counters_and_rom(&bin, &text, nd, 100, L1_WRAP_ROM)
    }

    #[test]
    fn report_observes_stack_peak_windows_outputs_and_trailing_input() {
        let report = run(
            &[
                0x0088_0137, // lui sp, 0x880 (stack top 0x880000)
                0xfc01_0113, // addi sp, sp, -64
                0x0401_0113, // addi sp, sp, 64
                0x0090_02b7, // lui t0, 0x900
                0x0002_a023, // sw zero, 0(t0)
            ],
            vec![7],
        )
        .unwrap();
        assert_eq!(report.min_sp, 0x87ffc0);
        assert_eq!(report.touched_windows, vec![0, 1]);
        assert_eq!(report.max_touched_address, 0x900003);
        assert_eq!(report.output, std::array::from_fn(|i| 100 + i as u32));
        assert_eq!(report.nd_words_remaining, 1);
        assert_eq!(report.cycles, 23);
        assert_eq!(report.final_pc, report.success_pc);
        let encoded = serde_json::to_string(&report).unwrap();
        assert_eq!(
            serde_json::from_str::<FsvRunReport>(&encoded).unwrap(),
            report
        );
    }

    #[test]
    fn exact_cycle_bound_and_success_exit_are_required() {
        let (bin, text) = program(&[]);
        assert_eq!(
            measure_fsv_run_with_counters_and_rom(&bin, &text, vec![], 18, L1_WRAP_ROM)
                .unwrap()
                .cycles,
            18
        );
        assert!(
            measure_fsv_run_with_counters_and_rom(&bin, &text, vec![], 17, L1_WRAP_ROM)
                .unwrap_err()
                .contains("did not halt")
        );
        assert!(run(&[0x0000_006f], vec![])
            .unwrap_err()
            .contains("not at the success exit"));
    }

    #[test]
    fn nd_exhaustion_is_observed_and_truncation_rejected() {
        // csrrw t0, 0x7c0, zero
        assert_eq!(run(&[0x7c00_12f3], vec![9]).unwrap().nd_words_remaining, 0);
        assert!(run(&[0x7c00_12f3], vec![])
            .unwrap_err()
            .contains("must have an answer"));
    }

    #[test]
    fn release_bounds_reject_load_store_and_pc_before_unchecked_access() {
        for access in [0x0002_a303, 0x0002_a023] {
            // lw t1,0(t0); sw zero,0(t0)
            assert!(run(&[0x0100_02b7, access], vec![])
                .unwrap_err()
                .contains("memory access outside RAM"));
        }
        assert!(run(&[0x0100_02b7, 0x0002_8067], vec![])
            .unwrap_err()
            .contains("instruction fetch outside text"));
        let ram = CheckedRam::<3>::new(&[], WRAP_RAM_BOUND);
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(
            || ram.peek_word(WRAP_RAM_BOUND as u32)
        ))
        .is_err());
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| ram.peek_word(1))).is_err()
        );
    }

    #[test]
    fn selected_geometry_changes_rom_write_boundary() {
        // Address 1 MiB is writable under the wrap layout, and ROM under regular.
        let (bin, text) = program(&[0x0010_02b7, 0x0002_a023]);
        assert!(
            measure_fsv_run_with_counters_and_rom(&bin, &text, vec![], 100, L1_WRAP_ROM).is_ok()
        );
        assert!(
            measure_fsv_run_with_counters_and_rom(&bin, &text, vec![], 100, REGULAR_ROM)
                .unwrap_err()
                .contains("write into ROM")
        );
        let oversized = vec![0; REGULAR_ROM.word_size()];
        assert!(
            measure_fsv_run_with_counters_and_rom(&oversized, &text, vec![], 100, L1_WRAP_ROM)
                .unwrap_err()
                .contains("exceeds selected ROM")
        );
    }

    #[test]
    fn regular_unpadded_and_padded_images_execute_identically() {
        let (mut bin, mut text) = program(&[]);
        let expected =
            measure_fsv_run_with_counters_and_rom(&bin, &text, vec![], 100, REGULAR_ROM).unwrap();
        setups::pad_bytecode_for_proving(&mut bin);
        setups::pad_bytecode_for_proving(&mut text);
        assert_eq!(
            measure_fsv_run_with_counters_and_rom(&bin, &text, vec![], 100, REGULAR_ROM).unwrap(),
            expected
        );
    }

    #[test]
    fn ram_trait_default_keeps_regular_rom() {
        struct LegacyRam;
        impl RamPeek for LegacyRam {
            fn peek_word(&self, _: u32) -> u32 {
                unreachable!()
            }
        }
        impl RAM for LegacyRam {
            fn read_word(&mut self, _: u32, _: TimestampScalar) -> (TimestampScalar, u32) {
                unreachable!()
            }
            fn write_word(&mut self, _: u32, _: u32, _: TimestampScalar) -> (TimestampScalar, u32) {
                unreachable!()
            }
            fn mask_read_for_witness(&self, _: &mut u32, _: &mut u32) {
                unreachable!()
            }
            fn skip_if_replaying(&mut self, _: usize) {
                unreachable!()
            }
        }
        assert_eq!(
            LegacyRam::ROM_BYTE_SIZE,
            prover::common_constants::ROM_BYTE_SIZE
        );
        assert_eq!(
            RamWithRomRegion::<6>::ROM_BYTE_SIZE,
            LegacyRam::ROM_BYTE_SIZE
        );
        assert_eq!(
            RamWithRomRegion::<3>::ROM_BYTE_SIZE,
            L1_WRAP_ROM.byte_size()
        );
    }
}
