mod common;

use field::baby_bear::base::BabyBearField;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::simple_instruction_set::*;
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use riscv_transpiler::vm::*;

fn run_transpiler(name: &str) {
    #[cfg(feature = "verifier_stats")]
    verifier_common::stats::reset();

    let (nds, external_challenges) = common::load_nds(name);
    println!("{}: oracle data length: {} u32 words", name, nds.len());

    let (bin_path, text_path, elf_path) = common::binary_paths(name);

    let binary = common::load_binary_section(&bin_path);
    let text_section = common::load_binary_section(&text_path);

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
    let output_path = std::env::current_dir()
        .unwrap()
        .join(format!("gkr_flamegraph_{}.svg", name));
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

    #[cfg(feature = "verifier_stats")]
    {
        common::extract_riscv_stats_log(&ram, &elf_path);
        common::print_stats_log(name);
    }

    println!("{}: completed successfully in transpiler", name);
    println!("Flamegraph written to {}", output_path.display());
}

macro_rules! generate_transpiler_tests {
    ($($name:ident: $schedule:ident: $layout_suffix:expr),* $(,)?) => {
        $(
            #[test]
            #[ignore = "requires RISC-V binaries from tools/gkr_verifier"]
            // Stats counters / STATS_LOG are global; serialize stats-enabled
            // runs so parallel tests don't clobber each other's measurements.
            #[cfg_attr(feature = "verifier_stats", serial_test::serial)]
            fn $name() {
                run_transpiler(stringify!($name));
            }
        )*
    };
}
verifier_common::gkr_circuits!(generate_transpiler_tests);
