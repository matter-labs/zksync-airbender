mod common;

use common::{SecurityLevel, SoundnessMode};
use field::baby_bear::base::BabyBearField;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::simple_instruction_set::*;
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use riscv_transpiler::vm::*;

/// The circuit's proof fixture of `mode` on its RISC-V verifier program of
/// `mode` (`tools/gkr_verifier/circuit_verifiers/<mode>/<circuit>.elf`); the
/// flamegraph is `gkr_flamegraph_<circuit>_<mode>.svg`.
fn run_transpiler(name: &str, level: SecurityLevel, mode: SoundnessMode) {
    let (nds, external_challenges) = common::load_nds_in_mode(name, level, mode);
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
verifier_common::gkr_circuits!(generate_transpiler_tests);

/// The PACKED-base-commitment fixture (`blake2_with_extended_control` proved
/// with `pack_log2 = 4`, see `verifier_common::test_circuits::packed_fixture`)
/// on its own RISC-V verifier binary
/// `tools/gkr_verifier/circuit_verifiers/pessimistic_conjecture/blake2_with_extended_control_pack4.elf`
/// (build it with `dump_bin.sh blake2_with_extended_control_pack4_pessimistic_conjecture`).
/// Compare its cycle count with `blake2_with_extended_control_pessimistic_conjecture`.
#[test]
#[ignore = "requires RISC-V binaries from tools/gkr_verifier"]
fn blake2_with_extended_control_sec_100_pack4() {
    use verifier_common::test_circuits::packed_fixture;
    let (nds, external_challenges) = packed_fixture::load_nds();
    let packed = packed_fixture::elf_path();
    run_transpiler_on(
        &format!(
            "{}_{}",
            packed_fixture::CIRCUIT_NAME,
            packed_fixture::DIR_SUFFIX
        ),
        nds,
        external_challenges,
        packed,
    );
}

/// The blake base-round comparison sweep: every
/// `verifier_common::test_circuits::blake_variants::BlakeVariant` (physical
/// packing 2^0..=2^4, two or one value(s) per column per base leaf) on its own
/// RISC-V verifier program `tools/gkr_verifier/blake2_with_extended_control_sec_100{infix}.elf`
/// (build them with `dump_bin.sh blake2_with_extended_control_<variant>_pessimistic_conjecture`).
/// Every verifier must accept its fixture; the cycle counts land in
/// `flamegraphs/blake_variants/cycles.txt` next to one flamegraph per variant.
/// `GKR_BLAKE_VARIANTS=_pack2,_pack3_virtual` (comma-separated infixes,
/// `default` for the plain config) restricts the sweep.
#[test]
#[ignore = "requires RISC-V binaries from tools/gkr_verifier"]
fn blake2_with_extended_control_sec_100_variants() {
    use verifier_common::test_circuits::blake_variants::BlakeVariant;
    let selected: Option<std::collections::HashSet<String>> = std::env::var("GKR_BLAKE_VARIANTS")
        .ok()
        .map(|raw| raw.split(',').map(|s| s.trim().to_string()).collect());
    let out_dir = std::env::current_dir()
        .unwrap()
        .join("flamegraphs")
        .join("blake_variants");
    std::fs::create_dir_all(&out_dir).unwrap();
    let mut summary = String::from(
        "# variant  physical_packing_log2  values_per_column_per_leaf  cycles\n",
    );
    for variant in BlakeVariant::all() {
        let infix = variant.infix();
        let selected_here = selected
            .as_ref()
            .is_none_or(|set| set.contains(&infix) || (infix.is_empty() && set.contains("default")));
        if !selected_here {
            continue;
        }
        let name = variant.name();
        let (nds, external_challenges) = variant.load_nds();
        let elf_path = variant.elf_path();
        let cycles = run_transpiler_on_with_output(
            &name,
            nds,
            external_challenges,
            elf_path,
            out_dir.join(format!("gkr_flamegraph_{}.svg", name)),
        );
        summary.push_str(&format!(
            "{}  {}  {}  {}\n",
            name,
            variant.pack_log2,
            1usize << variant.fold_log2,
            cycles
        ));
        println!("[blake-variants] {name}: {cycles} cycles");
    }
    let summary_path = out_dir.join("cycles.txt");
    std::fs::write(&summary_path, &summary).unwrap();
    println!("[blake-variants] summary written to {}", summary_path.display());
    print!("{summary}");
}
