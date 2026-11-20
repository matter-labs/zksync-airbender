mod common;

use field::Proth120;
use prover::definitions::SoundnessMode;
use prover::fft::Twiddles;
use prover::gkr::prover::OperationMode;
use prover::gkr::prover_config::{ProofProfile, WhirInternalRound};
use prover::gkr::whir::coset_commit::CosetByCosetBaseCommitment;
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use riscv_transpiler::elf::{read_elf_from_path_with_rom, ElfReadMode};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use unified_reduced_machine_proth120::l1_wrap::l1_wrap_setup;
use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProfile, FsvProgram};
use verifier_evm::encoding::{encode_single_tx, FormatParams};
use worker::Worker;

const REGISTRY: [u8; 20] = [
    0x78, 0xd5, 0x49, 0xf2, 0xa1, 0x40, 0x92, 0x3c, 0x51, 0x7c, 0x23, 0xb0, 0x08, 0xdf, 0xfe, 0x97,
    0x9b, 0x3c, 0x4e, 0x91,
];

#[derive(Clone, Copy)]
enum WrapCase {
    P32_2500,
    P32_469,
}

fn alternate_case(case: WrapCase) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let (
        mode,
        trace_log,
        fixture_dir,
        folds,
        rates,
        queries,
        query_pow,
        fold_pow,
        ood_pow,
        batching,
    ) = match case {
        // P32-2500, including an intermediate codeword at log domain 32.
        WrapCase::P32_2500 => (
            SoundnessMode::PessimisticConjecture,
            21,
            "pessimistic_conjecture",
            vec![1, 4, 4, 4, 5],
            vec![7, 9, 12, 15, 18],
            vec![12, 10, 7, 6, 5],
            vec![30, 25, 30, 25, 25],
            vec![9, 10, 9, 8, 7],
            vec![18, 20, 22, 24],
            13,
        ),
        // P32-469, a base fold of three and oracle domain logs 26, 26, 23, 21.
        WrapCase::P32_469 => (
            SoundnessMode::PessimisticConjecture,
            21,
            "pessimistic_conjecture",
            vec![3, 5, 4, 4],
            vec![2, 5, 7, 9],
            vec![47, 19, 14, 11],
            vec![22, 21, 19, 18],
            vec![4, 4, 1, 0],
            vec![8, 7, 7],
            8,
        ),
    };
    let mut config = ProofProfile::L1Wrap.prover_config(trace_log, mode);
    let schedule = &mut config.whir_schedule;
    schedule.base_round.lde_factor_log2 = rates[0];
    schedule.base_round.fold_log2 = folds[0];
    schedule.base_round.batching_pow_bits = Some(batching);
    schedule.base_round.folding_pow_bits = fold_pow[0];
    schedule.base_round.num_queries = queries[0];
    schedule.base_round.queries_pow_bits = query_pow[0];
    schedule.internal_rounds = (1..folds.len())
        .map(|i| WhirInternalRound {
            lde_factor_log2: rates[i],
            folding_log2: folds[i],
            num_queries: queries[i],
            queries_pow_bits: query_pow[i],
            folding_pow_bits: fold_pow[i],
            num_ood_samples: 1,
            ood_pow_bits: ood_pow[i - 1],
        })
        .collect();
    let run = root.join("target").join(format!(
        "l1-gpu-verify-{fixture_dir}-{}",
        std::process::id()
    ));
    let data = run.join("data");
    let project = run.join("merged");
    fs::create_dir_all(&data).unwrap();
    fs::create_dir_all(project.join("src")).unwrap();
    fs::create_dir_all(project.join("test")).unwrap();
    let schedule_path = data.join("schedule.json");
    fs::write(
        &schedule_path,
        serde_json::to_vec(&config.whir_schedule).unwrap(),
    )
    .unwrap();

    let gpu_cli =
        PathBuf::from(std::env::var_os("AB_L1_GPU_CLI").expect("release CLI with the gpu feature"));
    let lock =
        PathBuf::from(std::env::var_os("AB_GPU_LOCK_WRAPPER").expect("shared GPU lock wrapper"));
    let census = data.join("device-census.txt");
    let compression = root
        .join("fixtures/chains")
        .join(fixture_dir)
        .join("compression.json.zlib");
    let status = Command::new("bash")
        .current_dir(root)
        .arg(lock)
        .arg("bash")
        .arg("-c")
        .arg("nvidia-smi > \"$1\"; shift; exec \"$@\"")
        .arg("bash")
        .arg(census)
        .arg(gpu_cli)
        .args(["continue-proof", "--target", "l1", "--backend", "gpu"])
        .arg("--bin")
        .arg(root.join("examples/basic_fibonacci/app.bin"))
        .arg("--proof")
        .arg(compression)
        .args(["--soundness-mode", mode.cli_name()])
        .args(["--gpu-memory-preset", "21gib"])
        .arg("--l1-whir-schedule")
        .arg(schedule_path)
        .arg("--output-dir")
        .arg(&data)
        .args(["--output-file", "proof.json.zlib"])
        .status()
        .expect("locked GPU wrap");
    assert!(
        status.success(),
        "GPU wrap failed, artifacts in {}",
        run.display()
    );

    let bundle = common::load_bundle(data.join("proof.json.zlib"));
    assert_eq!(bundle.proof.whir_proof.whir_schedule, config.whir_schedule);
    let guest = FsvDescriptor {
        soundness_mode: mode,
        profile: FsvProfile::CompressionFinalWrap,
        program: FsvProgram::UnifiedRecursionLayer,
        blake: BlakeMode::BlakeSpecialOpcodes,
    };
    let image = read_elf_from_path_with_rom(
        &root
            .join("tools/gkr_verifier/full_statement_verifiers")
            .join(guest.relative_path()),
        ElfReadMode::Legacy,
        guest.profile.rom(),
    )
    .unwrap();
    let binary = image.flattened_binary.as_ref().unwrap();
    let final_pc = trace_and_split::setups::program_setups::find_binary_exit_point(binary);
    let OperationMode::SingleChunk {
        final_pc: proof_pc, ..
    } = bundle.operation_mode
    else {
        panic!("expected single-chunk wrap");
    };
    assert_eq!(proof_pc, final_pc);
    let worker = Worker::new();
    let setup = l1_wrap_setup(binary, &image.padded_text_words(), &worker);
    let twiddles = Twiddles::new(1 << config.whir_message_size_log2(), &worker);
    let rows: Vec<_> = setup
        .setup
        .hypercube_evals
        .iter()
        .map(|col| &col[..])
        .collect();
    let params = FormatParams {
        setup_frontier_level: 10,
    };
    let (setup_oracle, frontier) =
        CosetByCosetBaseCommitment::<Proth120, Keccak256MerkleTreeWithCap>::commit_packed_with_level_nodes(
            &rows, &twiddles, config.lde_factor(), config.base_round().fold_log2, config.cap_size,
            trace_log, config.pack_log2(), params.setup_frontier_level, &worker,
        );
    let cap = setup_oracle.get_cap().cap;
    assert_eq!(
        cap,
        bundle.proof.whir_proof.setup_commitment.commitment.cap.cap
    );
    let contracts = verifier_evm::generate_wrap_verifier(
        &setup.circuit,
        &config,
        &params,
        final_pc,
        &bundle.proof.inits_and_teardowns_top_bits,
        &cap,
        &frontier,
        REGISTRY,
    );
    let calldata = encode_single_tx(
        &setup.circuit,
        &bundle.proof,
        &bundle.operation_mode,
        &config,
        &params,
    );
    fs::write(data.join("proof.bin"), &calldata.bytes).unwrap();
    fs::write(
        data.join(common::VERIFIED_MARK),
        hex::encode(verifier_evm::verified_mark(&bundle.operation_mode).to_bytes()),
    )
    .unwrap();
    fs::write(
        data.join(common::CALLDATA_FIELDS),
        common::calldata_field_metadata(&calldata, &params).to_string(),
    )
    .unwrap();
    fs::write(
        project.join("src/GkrWhirVerifier.sol"),
        contracts.verifier_sol,
    )
    .unwrap();
    fs::write(
        project.join("src/TestRegistry.sol"),
        include_str!(concat!(
            "../generated_contracts/l1_wrap/merged/",
            "src/TestRegistry.sol"
        )),
    )
    .unwrap();
    let base = include_str!(concat!("../generated_contracts/l1_wrap/merged/", "test/MergedBase.sol"))
        .replace("../../../debug_data/l1_wrap", "../data")
        .replace("interface Vm {", "interface Vm {\n    function readFileBinary(string calldata path) external view returns (bytes memory);");
    fs::write(project.join("test/MergedBase.sol"), base).unwrap();
    fs::write(
        project.join("test/GpuL1WrapControls.t.sol"),
        include_str!("gpu_l1_wrap_controls.sol"),
    )
    .unwrap();
    let settings = include_str!(concat!(
        "../generated_contracts/l1_wrap/merged/",
        "foundry.toml"
    ))
    .replace("../../../debug_data/l1_wrap", "../data");
    fs::write(
        project.join("foundry.toml"),
        settings + "\ngas_limit = 240000000\nblock_gas_limit = 240000000\n",
    )
    .unwrap();

    let output = Command::new("forge")
        .current_dir(&project)
        .args(["test", "--match-contract", "GpuL1WrapControls", "-vv"])
        .output()
        .expect("CPU-executed EVM verifier");
    let log = String::from_utf8(output.stdout).unwrap();
    fs::write(run.join("forge.log"), &log).unwrap();
    assert!(
        output.status.success() && log.contains("5 passed; 0 failed"),
        "verifier or mutation test failed: {log}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[ignore = "full GPU wrap and CPU verifier; cargo test -p verifier_evm --release --test gpu_l1_wrap gpu_l1_wrap_p32_2500 -- --exact --ignored"]
fn gpu_l1_wrap_p32_2500() {
    alternate_case(WrapCase::P32_2500);
}

#[test]
#[ignore = "full GPU wrap and CPU verifier; cargo test -p verifier_evm --release --test gpu_l1_wrap gpu_l1_wrap_p32_469_fold3 -- --exact --ignored"]
fn gpu_l1_wrap_p32_469_fold3() {
    alternate_case(WrapCase::P32_469);
}
