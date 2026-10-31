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

/// ONE-OFF: run the proof `prover/test_proofs/<ONE_OFF_CIRCUIT>_<ONE_OFF_PROOF_SUFFIX>_gkr_proof.json`
/// on the verifier program `ONE_OFF_ELF`; the flamegraph is
/// `gkr_flamegraph_<circuit>_<suffix>.svg`.
#[test]
#[ignore = "one-off experiments; driven by ONE_OFF_CIRCUIT / ONE_OFF_PROOF_SUFFIX / ONE_OFF_ELF"]
fn one_off_from_env() {
    let name = std::env::var("ONE_OFF_CIRCUIT").expect("ONE_OFF_CIRCUIT");
    let suffix = std::env::var("ONE_OFF_PROOF_SUFFIX").expect("ONE_OFF_PROOF_SUFFIX");
    let elf_path = std::env::var("ONE_OFF_ELF").expect("ONE_OFF_ELF");
    // `ONE_OFF_BLAKE`: the ELF's blake build (`dump_bin.sh --blake`), default
    // `blake2_with_compression`
    let blake = std::env::var("ONE_OFF_BLAKE")
        .ok()
        .map(|v| BlakeMode::parse(&v).unwrap_or_else(|| panic!("unknown ONE_OFF_BLAKE `{v}`")))
        .unwrap_or(BlakeMode::Compression);
    let circuit = common::circuit_by_name(&name);
    let proof_path = format!(
        "{}/../prover/test_proofs/{}_{}_gkr_proof.json",
        env!("CARGO_MANIFEST_DIR"),
        name,
        suffix
    );
    let proof: prover::gkr::prover::GKRProof<
        BabyBearField,
        field::baby_bear::ext4::BabyBearExt4,
        prover::merkle_trees::DefaultTreeConstructor,
    > = serde_json::from_reader(std::io::BufReader::new(
        std::fs::File::open(&proof_path).unwrap_or_else(|e| panic!("{proof_path}: {e}")),
    ))
    .unwrap();
    let compiled = circuit.compiled_circuit();
    let nds = verifier_common::gkr::flatten::flatten_gkr_proof_for_nds::<
        BabyBearField,
        field::baby_bear::ext4::BabyBearExt4,
        prover::merkle_trees::DefaultTreeConstructor,
    >(&proof, &compiled, blake);
    run_transpiler_on(
        &format!("{}_{}", name, suffix),
        nds,
        proof.external_challenges,
        elf_path,
    );
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
