use crate::cs::definitions::TimestampScalar;
use crate::gkr::prover::GKRExternalChallenges;
use crate::gkr::witness_gen::trace_structs::RamShuffleMemStateRecord;
use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use cs::definitions::{INITIAL_TIMESTAMP, NUM_PERMUTATION_ARGUMENT_KEY_PARTS};
use fft::materialize_powers_serial_starting_with_elem;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, Instruction};
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
use riscv_transpiler::vm::{Counters, RamWithRomRegion, SimpleSnapshotter, SimpleTape, State, VM};
use std::alloc::Global;
use worker::Worker;

/// log2 of the trace length used by every executor-family circuit (per-family,
/// unified, i/t). Must match the cs-side compile constant.
pub const TRACE_LEN_LOG2: usize = 24;
pub const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;
pub const WORD_BITS: u32 = core::mem::size_of::<u32>().trailing_zeros();

/// Per-family path: how many init+teardown sets the standalone
/// `inits_and_teardowns` circuit emits per invocation. Hardcoded to match the
/// cs-side compile setting; the orchestration asserts this matches the
/// program-run RAM bound.
pub const NUM_INIT_AND_TEARDOWN_SETS_PER_FAMILY_MODE: usize = 16;
pub const RAM_BOUND_BYTES: usize = 1 << 30;
const _: () =
    assert!((NUM_INIT_AND_TEARDOWN_SETS_PER_FAMILY_MODE << TRACE_LEN_LOG2) << 2 == RAM_BOUND_BYTES);

/// Per-delegation-circuit chunk sizes (mirrors `family_circuits.rs` consts).
pub const BLAKE_NUM_DELEGATION_CYCLES: usize = 1 << 20;
pub const BIGINT_NUM_DELEGATION_CYCLES: usize = 1 << 22;
pub const KECCAK_NUM_DELEGATION_CYCLES: usize = 1 << 22;
pub const BLAKE_G_FUNCTION_NUM_DELEGATION_CYCLES: usize = 1 << 22;

/// Inputs that fully specify a program prove run.
pub struct ProgramConfig {
    pub binary_path: String,
    pub text_section_path: String,
    pub non_determinism_reads: Vec<u32>,
    pub cycles_bound: usize,
    pub ram_bound_bytes: usize,
}

impl ProgramConfig {
    /// `multi_family_smoke` with the Blake2s G-function delegation feature.
    /// Exercises F1+F2+F3+F4 (no MUL/DIV, no sub-word memory) plus a single
    /// Blake2s G-function CSR invocation, which produces non-empty witness
    /// for the `blake_g_function` delegation in the unified prove pipeline.
    pub fn multi_family_smoke_blake_g_function() -> Self {
        Self {
            binary_path: "../examples/multi_family_smoke/app_blake2_g_function.bin".to_string(),
            text_section_path: "../examples/multi_family_smoke/app_blake2_g_function.text"
                .to_string(),
            // First word = inner-loop count `n` (~50 RISC-V cycles per iteration).
            // n=50 → ~2.5K total cycles, in the same ballpark as keccak_f1600
            // (2774 cycles). Exercises F1+F2+F3+F4 over enough rows that the
            // padding-vs-execution ratio is sensible for negative tests.
            non_determinism_reads: vec![50, 0xDEAD_BEEF],
            cycles_bound: 1 << 20,
            ram_bound_bytes: RAM_BOUND_BYTES,
        }
    }

    /// `multi_family_smoke` with the Blake2s-with-compression delegation
    /// feature. Same F1+F2+F3+F4 program shape as the G-function variant;
    /// produces non-empty witness for the `blake` (compression) delegation.
    pub fn multi_family_smoke_blake_compression() -> Self {
        Self {
            binary_path: "../examples/multi_family_smoke/app_blake2_with_compression.bin"
                .to_string(),
            text_section_path: "../examples/multi_family_smoke/app_blake2_with_compression.text"
                .to_string(),
            non_determinism_reads: vec![50, 0xDEAD_BEEF],
            cycles_bound: 1 << 20,
            ram_bound_bytes: RAM_BOUND_BYTES,
        }
    }

    /// `hashed_fibonacci` with the Blake2s G-function delegation feature.
    /// Per-family use only — this program contains M-extension opcodes
    /// (`mulhu`/`mul` from the magic-number-divide lowering of
    /// `% 1_000_000_000`), so it requires the full machine (F1+F2+F3+F4+F5+F6).
    /// The unified reduced machine rejects these instructions.
    pub fn hashed_fibonacci_blake_g_function() -> Self {
        Self {
            binary_path: "../examples/hashed_fibonacci/app_blake2_g_function.bin".to_string(),
            text_section_path: "../examples/hashed_fibonacci/app_blake2_g_function.text"
                .to_string(),
            non_determinism_reads: vec![15, 1],
            cycles_bound: 1 << 20,
            ram_bound_bytes: RAM_BOUND_BYTES,
        }
    }

    /// `hashed_fibonacci` with the Blake2s-with-compression delegation feature.
    /// Per-family use only (same M-extension caveat as the G-function variant).
    pub fn hashed_fibonacci_blake_compression() -> Self {
        Self {
            binary_path: "../examples/hashed_fibonacci/app_blake2_with_compression.bin".to_string(),
            text_section_path: "../examples/hashed_fibonacci/app_blake2_with_compression.text"
                .to_string(),
            non_determinism_reads: vec![15, 1],
            cycles_bound: 1 << 20,
            ram_bound_bytes: RAM_BOUND_BYTES,
        }
    }

    /// `keccak_f1600` — the canonical per-family test program. Exercises
    /// the keccak delegation CSR + sub-word memory accesses (F5). Per-family
    /// use only; the unified reduced machine has no F5 sub-word family so
    /// loads/stores of LB/LH/SB/SH would trip the unsupported-PC assert.
    /// Default for per-family tests.
    pub fn keccak_f1600() -> Self {
        Self {
            binary_path: "../riscv_transpiler/examples/keccak_f1600/app.bin".to_string(),
            text_section_path: "../riscv_transpiler/examples/keccak_f1600/app.text".to_string(),
            non_determinism_reads: vec![15, 1],
            cycles_bound: 1 << 20,
            ram_bound_bytes: RAM_BOUND_BYTES,
        }
    }

    /// `mop_smoke` — a program built to exercise all four `mop.*` opcodes
    /// (the modular-arithmetic extension handled by the `add_sub_lui_auipc_mop`
    /// family). Per-family use; drives `add_sub_mop_real_program_check_satisfied`.
    pub fn mop_smoke() -> Self {
        Self {
            binary_path: "../examples/mop_smoke/app.bin".to_string(),
            text_section_path: "../examples/mop_smoke/app.text".to_string(),
            non_determinism_reads: vec![15, 1],
            cycles_bound: 1 << 20,
            ram_bound_bytes: RAM_BOUND_BYTES,
        }
    }
}

/// Output of [`run_vm_and_capture`]: the binary buffers, the snapshotter the
/// downstream proves replay against, and end-of-execution state.
pub struct VmRunOutput<C: Counters + Copy + Default> {
    pub binary: Vec<u32>,
    pub text_section: Vec<u32>,
    pub instructions: Vec<Instruction>,
    pub tape: SimpleTape,
    pub ram: RamWithRomRegion<{ common_constants::ROM_SECOND_WORD_BITS }>,
    pub snapshotter: SimpleSnapshotter<C, { common_constants::ROM_SECOND_WORD_BITS }>,
    pub final_state: State<C>,
    pub expected_final_state: State<C>,
    pub counters: C,
    pub final_pc: u32,
    pub final_timestamp: TimestampScalar,
    pub register_final_state: [RamShuffleMemStateRecord; 32],
    pub shuffle_ram_touched_addresses: Vec<Vec<(u32, (TimestampScalar, u32)), Global>, Global>,
    pub total_unique_teardowns: usize,
    pub cycles_bound: usize,
    /// Echo of `ProgramConfig::ram_bound_bytes` so downstream consumers
    /// (i/t coverage checks, etc.) don't need to keep the config around.
    pub ram_bound_bytes: usize,
}

/// Run the program in `config` once, capturing the snapshotter (so individual
/// prove steps can replay it with their own destination tracers) plus the
/// touched-address set used for i/t consistency checks.
pub fn run_vm_and_capture<C>(config: &ProgramConfig, worker: &Worker) -> VmRunOutput<C>
where
    C: Counters + Copy + Default + std::fmt::Debug,
{
    println!("Using {} binary", config.binary_path);

    let binary_bytes = std::fs::read(&config.binary_path).expect("program binary");
    let text_bytes = std::fs::read(&config.text_section_path).expect("program text section");
    assert!(binary_bytes.len() % 4 == 0);
    assert!(text_bytes.len() % 4 == 0);
    let binary: Vec<u32> = binary_bytes
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();
    let text_section: Vec<u32> = text_bytes
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text_section);
    let tape = SimpleTape::new(&instructions);

    let mut ram = RamWithRomRegion::<{ common_constants::ROM_SECOND_WORD_BITS }>::from_rom_content(
        &binary,
        config.ram_bound_bytes,
    );

    let mut state = State::initial_with_counters(C::default());
    let mut snapshotter =
        SimpleSnapshotter::<C, { common_constants::ROM_SECOND_WORD_BITS }>::new_with_cycle_limit(
            config.cycles_bound,
            state,
        );
    let mut non_determinism = QuasiUARTSource::new_with_reads(config.non_determinism_reads.clone());

    let is_program_finished = VM::<C>::run_basic_unrolled::<_, _, _, BabyBearField>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        config.cycles_bound,
        &mut non_determinism,
    );
    assert!(is_program_finished, "program did not reach looping state");

    let exact_cycles_passed =
        (state.timestamp - INITIAL_TIMESTAMP) / common_constants::TIMESTAMP_STEP;
    println!("Passed exactly {} cycles", exact_cycles_passed);

    let counters = snapshotter
        .snapshots
        .last()
        .expect("snapshotter captured at least one snapshot")
        .state
        .counters;

    let shuffle_ram_touched_addresses = ram.collect_inits_and_teardowns(worker, Global);
    let total_unique_teardowns: usize = shuffle_ram_touched_addresses
        .iter()
        .map(|el| el.len())
        .sum();
    println!("Touched {} unique addresses", total_unique_teardowns);

    let final_pc = state.pc;
    let final_timestamp = state.timestamp;

    let register_final_state = state.registers.map(|el| RamShuffleMemStateRecord {
        last_access_timestamp: el.timestamp,
        current_value: el.value,
    });

    let mut expected_final_state = state;
    expected_final_state.counters = Default::default();

    VmRunOutput {
        binary,
        text_section,
        instructions,
        tape,
        ram,
        snapshotter,
        final_state: state,
        expected_final_state,
        counters,
        final_pc,
        final_timestamp,
        register_final_state,
        shuffle_ram_touched_addresses,
        total_unique_teardowns,
        cycles_bound: config.cycles_bound,
        ram_bound_bytes: config.ram_bound_bytes,
    }
}

/// Asserts the memory-only witness trace matches the memory section of a
/// full witness trace. Sanity check that catches witness-gen bugs early.
/// Moved here from `prover/src/tests/gkr/mod.rs` because the orchestration
/// (compiled in lib builds) can't see the test module (gated by
/// `#[cfg(any(test, feature = "test"))]`).
pub fn ensure_memory_trace_consistency<F: field::PrimeField>(
    memory_trace: &crate::gkr::witness_gen::family_circuits::GKRMemoryOnlyWitnessTrace<
        F,
        impl std::alloc::Allocator + Clone,
        impl std::alloc::Allocator + Clone,
    >,
    witness_trace: &crate::gkr::witness_gen::family_circuits::GKRFullWitnessTrace<
        F,
        impl std::alloc::Allocator + Clone,
        impl std::alloc::Allocator + Clone,
    >,
) {
    assert_eq!(
        memory_trace.column_major_trace.len(),
        witness_trace.column_major_memory_trace.len()
    );
    for column in 0..memory_trace.column_major_trace.len() {
        let from_mem = &memory_trace.column_major_trace[column];
        let from_wit = &witness_trace.column_major_memory_trace[column];
        assert_eq!(from_mem.len(), from_wit.len());
        assert!(from_mem.len().is_power_of_two());
        for row in 0..from_mem.len() {
            assert_eq!(
                from_mem[row], from_wit[row],
                "diverged for column {}, row {}",
                column, row
            );
        }
    }
}

pub fn hardcoded_external_challenges() -> GKRExternalChallenges<BabyBearField, BabyBearExt4> {
    let memory_argument_alpha = BabyBearExt4::from_array_of_base([
        BabyBearField::new(2),
        BabyBearField::new(5),
        BabyBearField::new(42),
        BabyBearField::new(123),
    ]);
    let permutation_argument_additive_part = BabyBearExt4::from_array_of_base([
        BabyBearField::new(7),
        BabyBearField::new(11),
        BabyBearField::new(1024),
        BabyBearField::new(8000),
    ]);
    let permutation_argument_linearization_challenges: [BabyBearExt4;
        NUM_PERMUTATION_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            memory_argument_alpha,
            NUM_PERMUTATION_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();
    GKRExternalChallenges::<BabyBearField, BabyBearExt4> {
        permutation_argument_linearization_challenges,
        permutation_argument_additive_part,
        _marker: core::marker::PhantomData,
    }
}

/// Parse the `GKR_CIRCUITS` env-var filter into a set of base circuit names.
/// `None` (unset or empty) means no filter — prove every circuit applicable
/// to the active mode. Orchestration prove fns use this to gate individual
/// sub-circuit proves.
pub fn parse_circuits_filter() -> Option<std::collections::HashSet<String>> {
    let raw = std::env::var("GKR_CIRCUITS").ok()?;
    if raw.trim().is_empty() {
        return None;
    }
    Some(raw.split(',').map(|s| s.trim().to_string()).collect())
}

/// `GKR_PROVE_EMPTY=1` → prove every circuit applicable to the mode, even if
/// the program made zero calls.
pub fn parse_prove_empty() -> bool {
    matches!(
        std::env::var("GKR_PROVE_EMPTY").as_deref(),
        Ok("1") | Ok("true") | Ok("TRUE")
    )
}

/// Returns `true` when this circuit name should be proved. Either: the
/// filter is empty (= all applicable) OR the filter contains this name.
pub fn circuit_in_filter(filter: &Option<std::collections::HashSet<String>>, name: &str) -> bool {
    filter.as_ref().map(|s| s.contains(name)).unwrap_or(true)
}
