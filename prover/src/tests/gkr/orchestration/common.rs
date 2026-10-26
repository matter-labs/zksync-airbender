use crate::cs::definitions::TimestampScalar;
use crate::gkr::prover::GKRExternalChallenges;
use crate::gkr::witness_gen::trace_structs::RamShuffleMemStateRecord;
use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use cs::definitions::{INITIAL_TIMESTAMP, NUM_PERMUTATION_ARGUMENT_KEY_PARTS};
use fft::materialize_powers_serial_starting_with_elem;
use field::{Field, FieldExtension, PrimeField};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, Instruction};
use riscv_transpiler::vm::{Counters, RamWithRomRegion, SimpleSnapshotter, SimpleTape, State, VM};
use std::alloc::Global;
use worker::Worker;

/// Default log2 trace length for executor circuits and standalone i/t.
/// Must match the corresponding CS compile settings.
pub const TRACE_LEN_LOG2: usize = 24;
pub const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;
pub const WORD_BITS: u32 = core::mem::size_of::<u32>().trailing_zeros();

pub const RAM_BOUND_BYTES: usize = 1 << 30;

/// Per-delegation-circuit chunk sizes (mirrors `family_circuits.rs` consts).
pub const BLAKE_NUM_DELEGATION_CYCLES: usize = 1 << 20;
pub const BIGINT_NUM_DELEGATION_CYCLES: usize = 1 << 22;
pub const KECCAK_NUM_DELEGATION_CYCLES: usize = 1 << 22;
pub const BLAKE_G_FUNCTION_NUM_DELEGATION_CYCLES: usize = 1 << 22;

/// Inputs that fully specify a program prove run.
pub struct ProgramConfig {
    pub program: riscv_transpiler::elf::ProgramSource,
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
            program: riscv_transpiler::elf::ProgramSource::legacy_binaries(
                "../examples/multi_family_smoke/app_blake2_g_function.bin",
                "../examples/multi_family_smoke/app_blake2_g_function.text",
            ),
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
            program: riscv_transpiler::elf::ProgramSource::legacy_binaries(
                "../examples/multi_family_smoke/app_blake2_with_compression.bin",
                "../examples/multi_family_smoke/app_blake2_with_compression.text",
            ),
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
            program: riscv_transpiler::elf::ProgramSource::legacy_binaries(
                "../examples/hashed_fibonacci/app_blake2_g_function.bin",
                "../examples/hashed_fibonacci/app_blake2_g_function.text",
            ),
            non_determinism_reads: vec![15, 1],
            cycles_bound: 1 << 20,
            ram_bound_bytes: RAM_BOUND_BYTES,
        }
    }

    /// `hashed_fibonacci` with the Blake2s-with-compression delegation feature.
    /// Per-family use only (same M-extension caveat as the G-function variant).
    pub fn hashed_fibonacci_blake_compression() -> Self {
        Self {
            program: riscv_transpiler::elf::ProgramSource::legacy_binaries(
                "../examples/hashed_fibonacci/app_blake2_with_compression.bin",
                "../examples/hashed_fibonacci/app_blake2_with_compression.text",
            ),
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
            program: riscv_transpiler::elf::ProgramSource::legacy_binaries(
                "../riscv_transpiler/examples/keccak_f1600/app.bin",
                "../riscv_transpiler/examples/keccak_f1600/app.text",
            ),
            non_determinism_reads: vec![15, 1],
            cycles_bound: 1 << 20,
            ram_bound_bytes: RAM_BOUND_BYTES,
        }
    }

    /// `keccak` — Keccak-f1600 permutations through the column parity, theta/rho and chi5
    /// delegations.
    pub fn keccak() -> Self {
        Self {
            program: riscv_transpiler::elf::ProgramSource::legacy_binaries(
                "../examples/keccak/app.bin",
                "../examples/keccak/app.text",
            ),
            non_determinism_reads: vec![],
            cycles_bound: 1 << 20,
            ram_bound_bytes: RAM_BOUND_BYTES,
        }
    }

    /// `mop_smoke` — a program built to exercise all four `mop.*` opcodes
    /// (the modular-arithmetic extension handled by the `add_sub_lui_auipc_mop`
    /// family). Per-family use; drives `add_sub_mop_real_program_check_satisfied`.
    pub fn mop_smoke() -> Self {
        Self {
            program: riscv_transpiler::elf::ProgramSource::legacy_binaries(
                "../examples/mop_smoke/app.bin",
                "../examples/mop_smoke/app.text",
            ),
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
    pub counters: C,
    pub shuffle_ram_touched_addresses: Vec<Vec<(u32, (TimestampScalar, u32)), Global>, Global>,
    pub total_unique_teardowns: usize,
    pub cycles_bound: usize,
    /// Echo of `ProgramConfig::ram_bound_bytes` so downstream consumers
    /// (i/t coverage checks, etc.) don't need to keep the config around.
    pub ram_bound_bytes: usize,
}

impl<C: Counters + Copy + Default> VmRunOutput<C> {
    /// Final program counter, derived from `final_state` (previously a denormalized field).
    pub fn final_pc(&self) -> u32 {
        self.final_state.pc
    }

    /// Final timestamp, derived from `final_state`.
    pub fn final_timestamp(&self) -> TimestampScalar {
        self.final_state.timestamp
    }

    /// Per-register final (value, timestamp) records, derived from `final_state`.
    pub fn register_final_state(&self) -> [RamShuffleMemStateRecord; 32] {
        self.final_state
            .registers
            .map(|el| RamShuffleMemStateRecord {
                last_access_timestamp: el.timestamp,
                current_value: el.value,
            })
    }

    /// `final_state` with counters zeroed — the boundary state the replayer must reproduce.
    pub fn expected_final_state(&self) -> State<C> {
        let mut s = self.final_state;
        s.counters = Default::default();
        s
    }
}

/// Run the program in `config` once, capturing the snapshotter (so individual
/// prove steps can replay it with their own destination tracers) plus the
/// touched-address set used for i/t consistency checks.
pub fn run_vm_and_capture<C, D>(config: &ProgramConfig, worker: &Worker) -> VmRunOutput<C>
where
    C: Counters + Copy + Default + std::fmt::Debug,
    D: riscv_transpiler::ir::DecodingOptions,
{
    println!("Using {} program", config.program);

    let (binary, text_section) = config.program.load_unpadded();

    let instructions: Vec<Instruction> = preprocess_bytecode::<D, true>(&text_section);
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

    VmRunOutput {
        binary,
        text_section,
        instructions,
        tape,
        ram,
        snapshotter,
        final_state: state,
        counters,
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

pub fn dummy_external_challenges<F: PrimeField, E: FieldExtension<F> + Field>(
) -> GKRExternalChallenges<F, E> {
    GKRExternalChallenges::<F, E> {
        permutation_argument_linearization_challenges: [E::ZERO;
            NUM_PERMUTATION_ARGUMENT_KEY_PARTS - 1],
        permutation_argument_additive_part: E::ZERO,
        _marker: core::marker::PhantomData,
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
/// The soundness mode the family / delegation proofs are produced in:
/// `GKR_SOUNDNESS_MODE=pessimistic_conjecture` (default) or
/// `ethproofs_soundcalc`. Every circuit is proved with the config its circuit
/// definition serialized for that mode ([`fixture_prover_config`]), so the
/// proofs match the verifiers generated from the same files.
pub fn soundness_mode() -> crate::definitions::SoundnessMode {
    use crate::definitions::SoundnessMode;
    match std::env::var("GKR_SOUNDNESS_MODE").ok().as_deref() {
        None | Some("") => SoundnessMode::DEFAULT,
        Some(raw) => SoundnessMode::ALL
            .iter()
            .copied()
            .find(|m| m.file_suffix() == raw.trim())
            .unwrap_or_else(|| panic!("unknown GKR_SOUNDNESS_MODE `{raw}`")),
    }
}

/// The proof-file suffix of `level` in the current [`soundness_mode`]:
/// `sec_100` for the default mode (the production fixtures keep their names),
/// `sec_100_<mode>` otherwise (`verifier_common::test_circuits::fixture_suffix`).
pub fn proof_suffix(level: crate::definitions::SecurityLevel) -> String {
    // one-off experiments name their proofs explicitly so the fixtures stay intact
    if let Ok(suffix) = std::env::var("GKR_PROOF_SUFFIX") {
        if !suffix.trim().is_empty() {
            return suffix.trim().to_string();
        }
    }
    let mode = soundness_mode();
    if mode == crate::definitions::SoundnessMode::DEFAULT {
        level.dir_suffix().to_string()
    } else {
        format!("{}_{}", level.dir_suffix(), mode.file_suffix())
    }
}

/// `GKR_BASE_PACKING_OVERRIDE=none|virtual|pack<k>|pack<k>_virtual`: a ONE-OFF
/// experiment proving every circuit of the run with that base packing (and the
/// current [`soundness_mode`]) instead of its definition's; the config is
/// computed on the fly from the circuit's layout and written next to the proof
/// (`test_proofs/<stem>_<suffix>_prover_config.json`) so the verifier generator
/// can pick it up. Pair it with `GKR_PROOF_SUFFIX` so the fixtures stay intact.
pub fn base_packing_override() -> Option<crate::gkr::prover_config::BasePacking> {
    use crate::gkr::prover_config::BasePacking;
    let raw = std::env::var("GKR_BASE_PACKING_OVERRIDE").ok()?;
    let raw = raw.trim();
    if raw.is_empty() {
        return None;
    }
    let (physical, virtual_) = match raw {
        "none" => (0, false),
        "virtual" => (0, true),
        other => {
            let (pack, virtual_) = match other.strip_suffix("_virtual") {
                Some(pack) => (pack, true),
                None => (other, false),
            };
            let k = pack
                .strip_prefix("pack")
                .and_then(|k| k.parse::<usize>().ok())
                .unwrap_or_else(|| panic!("unknown GKR_BASE_PACKING_OVERRIDE `{raw}`"));
            (k, virtual_)
        }
    };
    Some(BasePacking {
        physical_packing_log2: physical,
        virtual_packing: virtual_,
    })
}

fn one_off_prover_config(
    stem: &str,
    level: crate::definitions::SecurityLevel,
    packing: crate::gkr::prover_config::BasePacking,
) -> crate::gkr::prover_config::ProverConfig {
    use crate::gkr::prover_config::{example_configs, BaseColumns};
    let layout_path = format!("{}/generated/layout.json", circuit_definition_dir(stem));
    let file = std::fs::File::open(&layout_path).unwrap_or_else(|e| panic!("{layout_path}: {e}"));
    let compiled: cs::gkr_compiler::GKRCircuitArtifact<BabyBearField> =
        serde_json::from_reader(std::io::BufReader::new(file))
            .unwrap_or_else(|e| panic!("{layout_path}: {e}"));
    let mut config = example_configs::prover_config(
        soundness_mode(),
        level,
        compiled.trace_len.trailing_zeros() as usize,
        packing,
        Some(&BaseColumns::of(&compiled)),
    );
    // `GKR_MERKLE_MULTIPROOF=1`: flatten and verify the query openings of the
    // rounds that qualify (`WhirSchedule::merkle_multiproof_for_round`) as
    // pruned multiproofs (the proof itself is unchanged).
    if std::env::var("GKR_MERKLE_MULTIPROOF").map_or(false, |v| v.trim() == "1") {
        config.whir_schedule.merkle_multiproofs = true;
    }
    let out = format!("test_proofs/{stem}_{}_prover_config.json", proof_suffix(level));
    let mut dst = std::fs::File::create(&out).unwrap_or_else(|e| panic!("{out}: {e}"));
    serde_json::to_writer_pretty(&mut dst, &config).unwrap();
    println!(
        "one-off prover config for {stem}: {:?} in {:?}, written to {out}",
        packing,
        soundness_mode()
    );
    config
}

/// The circuit-definition crate of a proof stem (relative to `prover/`).
fn circuit_definition_dir(stem: &str) -> &'static str {
    match stem {
        "add_sub_lui_auipc_mop" => "../circuit_defs/unrolled_circuits/add_sub_lui_auipc_mop",
        "bigint_with_extended_control" => "../circuit_defs/bigint_with_control",
        "blake2_g_function" => "../circuit_defs/blake2_g_function",
        "blake2_with_extended_control" => "../circuit_defs/blake2_with_compression",
        "inits_and_teardowns" => "../circuit_defs/unrolled_circuits/inits_and_teardowns",
        "jump_branch_slt" => "../circuit_defs/unrolled_circuits/jump_branch_slt",
        "keccak_chi5" => "../circuit_defs/keccak_chi5",
        "keccak_column_parity" => "../circuit_defs/keccak_column_parity",
        "keccak_special5" => "../circuit_defs/keccak_special5",
        "keccak_theta_rho" => "../circuit_defs/keccak_theta_rho",
        "mem_subword_only" => "../circuit_defs/unrolled_circuits/load_store_subword_only",
        "mem_word_only" => "../circuit_defs/unrolled_circuits/load_store_word_only",
        "shift_binop" => "../circuit_defs/unrolled_circuits/shift_binary",
        "unified_reduced_machine" => "../circuit_defs/unrolled_circuits/unified_reduced_machine",
        "unsigned_mul_div" => "../circuit_defs/unrolled_circuits/mul_div_unsigned",
        other => panic!("no circuit definition is registered for the proof stem {other}"),
    }
}

/// The prover config the circuit definition of `stem` serialized for `level`
/// in the current [`soundness_mode`]
/// (`<crate>/generated/prover_config_<level>_<mode>.json`, written by the
/// crate's artifact generator from its geometry and compiled circuit): the
/// single source of a fixture proof's geometry, and the config the circuit's
/// verifier of that mode is generated from.
pub fn fixture_prover_config(
    stem: &str,
    level: crate::definitions::SecurityLevel,
) -> crate::gkr::prover_config::ProverConfig {
    // the override only applies to the circuits selected for proving: the others
    // never prove, and their shape may have no certified schedule
    if let Some(packing) = base_packing_override() {
        let selected = parse_circuits_filter()
            .is_none_or(|filter| filter.contains(stem));
        if selected {
            return one_off_prover_config(stem, level, packing);
        }
    }
    let path = format!(
        "{}/generated/prover_config_{}_{}.json",
        circuit_definition_dir(stem),
        level.dir_suffix(),
        soundness_mode().file_suffix()
    );
    let file = std::fs::File::open(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let config: crate::gkr::prover_config::ProverConfig =
        serde_json::from_reader(std::io::BufReader::new(file))
            .unwrap_or_else(|e| panic!("{path}: {e}"));
    config
}

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

pub fn log_prove_decision(name: &str, should_prove: bool, compute_only: bool) {
    if should_prove {
        println!("Proving {name}");
    } else if compute_only {
        println!("Skipping {name} prove (compute-only pass; witness still replayed)");
    } else {
        println!(
            "Skipping {name} prove (filtered out by GKR_CIRCUITS, or 0 calls without \
             GKR_PROVE_EMPTY); witness still replayed"
        );
    }
}
