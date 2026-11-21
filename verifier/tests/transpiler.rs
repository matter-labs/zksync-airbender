mod common;

use common::{SecurityLevel, SoundnessMode};
use field::baby_bear::base::BabyBearField;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::simple_instruction_set::*;
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use riscv_transpiler::vm::*;
use verifier_common::BlakeMode;

/// The circuit's proof fixture of `mode` on its RISC-V verifier program of
/// `mode` (`tools/gkr_verifier/circuit_verifiers/<mode>/<circuit>.elf`); the
/// flamegraph is `gkr_flamegraph_<circuit>_<mode>.svg`.
fn run_transpiler(name: &str, level: SecurityLevel, mode: SoundnessMode) {
    // the tracked per-circuit ELFs are the `blake2_with_compression` builds
    let (nds, external_challenges) =
        common::load_nds_in_mode(name, level, mode, BlakeMode::Compression);
    let elf_path = common::elf_path_in_mode(name, level, mode);
    run_transpiler_on(
        &format!("{}_{}", name, mode.file_suffix()),
        nds,
        external_challenges,
        elf_path,
    );
}

/// [`run_transpiler_on_with_output`] writing `gkr_flamegraph_<name>.svg` into
/// the current directory (the tracked per-circuit flamegraphs).
fn run_transpiler_on(
    name: &str,
    nds: Vec<u32>,
    external_challenges: prover::definitions::GKRExternalChallenges<
        BabyBearField,
        field::baby_bear::ext4::BabyBearExt4,
    >,
    elf_path: String,
) -> u64 {
    let output_path = std::env::current_dir()
        .unwrap()
        .join(format!("gkr_flamegraph_{}.svg", name));
    run_transpiler_on_with_output(name, nds, external_challenges, elf_path, output_path)
}

/// Run the RISC-V verifier program `elf_path` (its ROM image and symbols) on
/// the flattened proof `nds`, asserting success and printing the exact cycle
/// count + writing a flamegraph to `output_path`. Returns the cycle count.
fn run_transpiler_on_with_output(
    name: &str,
    nds: Vec<u32>,
    external_challenges: prover::definitions::GKRExternalChallenges<
        BabyBearField,
        field::baby_bear::ext4::BabyBearExt4,
    >,
    elf_path: String,
    output_path: std::path::PathBuf,
) -> u64 {
    println!("{}: oracle data length: {} u32 words", name, nds.len());

    let (binary, text_section) =
        riscv_transpiler::elf::load_legacy_program(std::path::Path::new(&elf_path));

    let mut oracle_responses = vec![];
    external_challenges.flatten_into_buffer(&mut oracle_responses);
    oracle_responses.extend(nds);

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<ReducedMachineDecoderConfig, true>(&text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram =
        RamWithRomRegion::<{ common_constants::rom::ROM_SECOND_WORD_BITS }>::from_rom_content(
            &binary,
            1 << 30,
        );

    let cycles_bound = 1 << 24;
    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
    let mut snapshotter = SimpleSnapshotter::<
        DelegationsAndFamiliesCounters,
        { common_constants::rom::ROM_SECOND_WORD_BITS },
    >::new_with_cycle_limit(cycles_bound, state);
    let mut non_determinism = QuasiUARTSource::new_with_reads(oracle_responses);

    let symbols_path = std::path::PathBuf::from(&elf_path);
    if let Some(dir) = output_path.parent() {
        std::fs::create_dir_all(dir).unwrap();
    }
    let mut fg_config =
        riscv_transpiler::vm::FlamegraphConfig::new(symbols_path, output_path.clone());
    fg_config.frequency_recip = 1;
    let mut profiler = riscv_transpiler::vm::VmFlamegraphProfiler::new(fg_config).unwrap();

    let is_program_finished =
        VM::<DelegationsAndFamiliesCounters>::run_basic_unrolled_with_flamegraph::<
            _,
            _,
            _,
            BabyBearField,
        >(
            &mut state,
            &mut ram,
            &mut snapshotter,
            &tape,
            cycles_bound,
            &mut non_determinism,
            &mut profiler,
        )
        .expect("flamegraph profiler IO error");

    assert!(
        is_program_finished,
        "{}: verifier did not finish (PC stuck or cycle bound reached)",
        name,
    );

    let exact_cycles =
        (state.timestamp - common_constants::INITIAL_TIMESTAMP) / common_constants::TIMESTAMP_STEP;
    println!("{}: finished in {} cycles", name, exact_cycles);

    let c = &state.counters;
    println!("{}: circuit call counters:", name);
    println!("  add_sub_lui_auipc_mop: {}", c.add_sub_family);
    println!("  jump_branch_slt:       {}", c.slt_branch_family);
    println!("  shift_binop_csr:       {}", c.binary_shift_family);
    println!("  mul_div:               {}", c.mul_div_family);
    println!("  mem_word:              {}", c.word_size_mem_family);
    println!("  mem_subword:           {}", c.subword_size_mem_family);
    println!("  blake2:                {}", c.blake_calls);
    println!("  bigint:                {}", c.bigint_calls);
    println!("  keccak:                {}", c.keccak_calls);

    for (i, reg) in state.registers[10..18].iter().enumerate() {
        println!("  a{} = 0x{:08x} ({})", i, reg.value, reg.value);
    }

    let a0 = state.registers[10].value;
    if a0 == 0xDEAD {
        let error_code = state.registers[11].value;
        let layer = state.registers[12].value;
        let round = state.registers[13].value;
        match error_code {
            1 => panic!(
                "{}: GKR SumcheckRoundFailed layer={} round={}",
                name, layer, round
            ),
            2 => panic!("{}: GKR FinalStepCheckFailed layer={}", name, layer),
            3 => panic!("{}: WHIR verification failed", name),
            4 => panic!("{}: GKR CacheRelationFailed layer={}", name, layer),
            _ => panic!("{}: unknown error code={}", name, error_code),
        }
    }
    assert_eq!(a0, 1, "{}: a0 = {} (expected 1 for success)", name, a0);

    println!("{}: completed successfully in transpiler", name);
    println!("Flamegraph written to {}", output_path.display());
    exact_cycles
}

macro_rules! generate_transpiler_tests {
    ($($name:ident; $prod_path:expr),* $(,)?) => {
        paste::paste! {
            $(
                #[test]
                #[ignore = "requires RISC-V binaries from tools/gkr_verifier"]
                fn [<$name _pessimistic_conjecture>]() {
                    run_transpiler(stringify!($name), SecurityLevel::Sec100, SoundnessMode::PessimisticConjecture);
                }
                #[test]
                #[ignore = "requires RISC-V binaries from tools/gkr_verifier and the ethproofs_soundcalc proof fixture"]
                fn [<$name _ethproofs_soundcalc>]() {
                    run_transpiler(stringify!($name), SecurityLevel::Sec100, SoundnessMode::EthproofsSoundnessCalc);
                }
            )*
        }
    };
}
verifier_common::gkr_fixture_circuits!(generate_transpiler_tests);

/// The add/sub verifier guest built with the zero-knowledge masking exit
/// (`riscv_common::finish_execution_recursion_extended`), on the same proof as the plain test.
/// The oracle is a `GuestSource`: the proof as its input words, and a `QueryDispatcher` with the
/// masking responder, which has to answer the masking query of the exit sequence.
#[test]
#[ignore = "requires `./dump_bin.sh --blake special_opcodes_extension --zk-exit add_sub_lui_auipc_mop_ethproofs_soundcalc` in tools/gkr_verifier"]
fn add_sub_lui_auipc_mop_ethproofs_soundcalc_zk_masking_exit() {
    use riscv_transpiler::oracle::zk_masking::parameters::{
        ADDRESS_CHUNKS, ITERATIONS, LOOP_INSTRUCTIONS_BELOW_BOUNDARY, MAX_MASKING_CYCLES,
        MIN_FRESH_STORES_PER_ADDRESS_CHUNK, MIN_MASKING_CYCLES, PC_LOW_LIMB_SPAN_BYTES,
    };
    use riscv_transpiler::oracle::zk_masking::{
        MaskingMemoryLayout, MaskingResponder, RECURSION_EXIT_TAIL_SEQUENCE,
    };
    use riscv_transpiler::oracle::{GuestSource, QueryDispatcher, RunMode};

    let name = "add_sub_lui_auipc_mop";
    let (level, mode) = (SecurityLevel::Sec100, SoundnessMode::EthproofsSoundnessCalc);
    let (nds, external_challenges) =
        common::load_nds_in_mode(name, level, mode, BlakeMode::BlakeSpecialOpcodes);
    let plain_elf_path = common::elf_path_in_mode(name, level, mode);
    let elf_path = plain_elf_path.replace(
        &format!("{}.elf", name),
        &format!("zk_masking_exit/{}.elf", name),
    );
    let (binary, text_section) =
        riscv_transpiler::elf::load_legacy_program(std::path::Path::new(&elf_path));

    let mut oracle_responses = vec![];
    external_challenges.flatten_into_buffer(&mut oracle_responses);
    oracle_responses.extend(nds);

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<ReducedMachineDecoderConfig, true>(&text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram =
        RamWithRomRegion::<{ common_constants::rom::ROM_SECOND_WORD_BITS }>::from_rom_content(
            &binary,
            1 << 30,
        );
    let cycles_bound = 1 << 24;
    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
    let mut snapshotter = SimpleSnapshotter::<
        DelegationsAndFamiliesCounters,
        { common_constants::rom::ROM_SECOND_WORD_BITS },
    >::new_with_cycle_limit(cycles_bound, state);

    // a 2^23 trace: inits and teardowns cover 64 Mb, of which the guest itself uses the low 32
    let layout = MaskingMemoryLayout::for_trace_len_log2(23);
    let mut oracle = QueryDispatcher::new(RunMode::RiscVRun);
    oracle.add_external_processor(MaskingResponder::from_os_entropy(layout));
    let mut non_determinism = GuestSource::new(oracle_responses, oracle);

    let is_program_finished =
        VM::<DelegationsAndFamiliesCounters>::run_basic_unrolled::<_, _, _, BabyBearField>(
            &mut state,
            &mut ram,
            &mut snapshotter,
            &tape,
            cycles_bound,
            &mut non_determinism,
        );
    assert!(is_program_finished);
    let exact_cycles =
        (state.timestamp - common_constants::INITIAL_TIMESTAMP) / common_constants::TIMESTAMP_STEP;
    println!(
        "finished in {} cycles, {} to {} of them masking",
        exact_cycles, MIN_MASKING_CYCLES, MAX_MASKING_CYCLES
    );

    // the dispatch: the proof is read in full by the guest, the response to the masking query
    // to its last word, and the guest is still connected (the masking query is not a disconnect)
    assert!(non_determinism.inputs.is_empty());
    assert!(!non_determinism.oracle.has_pending_response());
    assert!(non_determinism.oracle.is_connected());

    // registers: the verifier's success in x10, zeroes up to x25, the counters in x26-x28, and
    // nothing of the masking randomness anywhere else
    let registers: Vec<u32> = state.registers.iter().map(|r| r.value).collect();
    assert_eq!(registers[10], 1);
    assert!(registers[11..26].iter().all(|value| *value == 0));
    assert_eq!(registers[26..29], [0x11, 0x22, 0x33]);
    assert!(registers[..10].iter().all(|value| *value == 0));
    assert!(registers[29..].iter().all(|value| *value == 0));

    // the execution ends on the explicit loop of the new exit tail
    let tail = RECURSION_EXIT_TAIL_SEQUENCE;
    let tail_starts: Vec<usize> = binary
        .windows(tail.len())
        .enumerate()
        .filter_map(|(offset, window)| (window == tail).then_some(offset))
        .collect();
    assert_eq!(tail_starts.len(), 1);
    assert_eq!(state.pc as usize, (tail_starts[0] + tail.len() - 1) * 4);

    // the loop is across a 64 KiB boundary: the branch that skips an instruction is the second
    // to last instruction below it, and the loop starts 13 instructions below it. The loop is
    // found by its head, the only place of the binary with two oracle reads into t0 and t1
    // followed by `add t2, t0, t1`.
    let loop_head = [0x7c0012f3u32, 0x7c001373, 0x006283b3];
    let loop_starts: Vec<usize> = binary
        .windows(loop_head.len())
        .enumerate()
        .filter_map(|(offset, window)| (window == loop_head).then_some(offset))
        .collect();
    assert_eq!(loop_starts.len(), 1);
    let boundary = (loop_starts[0] as u32 + LOOP_INSTRUCTIONS_BELOW_BOUNDARY) * 4;
    assert_eq!(boundary % PC_LOW_LIMB_SPAN_BYTES, 0);
    // blt t0, t1, +8
    assert_eq!(binary[boundary as usize / 4 - 2], 0x0062c463);

    // the stores: the guest never touches memory above 32 Mb, so every non-zero word there is a
    // masking store. About half of the stores go to new addresses, a half of those to the second
    // inits/teardowns set, evenly over its 2 Mb chunks; the stores to used addresses add a few
    let chunk_bytes = layout.total_init_memory_bytes / ADDRESS_CHUNKS;
    let mut stores_in_second_set = 0;
    for chunk in ADDRESS_CHUNKS / 2..ADDRESS_CHUNKS {
        let stores = (chunk * chunk_bytes..(chunk + 1) * chunk_bytes)
            .step_by(4)
            .filter(|address| ram.peek_word(*address) != 0)
            .count() as u32;
        assert!(
            stores >= MIN_FRESH_STORES_PER_ADDRESS_CHUNK,
            "chunk {}: {} stores",
            chunk,
            stores
        );
        stores_in_second_set += stores;
    }
    println!(
        "{} words above 32 Mb hold a masking store, of {} stores",
        stores_in_second_set, ITERATIONS
    );
}
