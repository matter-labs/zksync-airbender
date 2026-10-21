//! AIH-334: test the generated validation without rewriting committed contracts.

mod common;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;
use prover::gkr::prover_config::{example_configs::EVM_PRODUCTION_TRACE_LEN_LOG2, pow_bits};
use std::path::PathBuf;

fn fixture_final_pc() -> u32 {
    let encoded = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("debug_data/gkr_step1_preimage.hex"),
    )
    .unwrap();
    let preimage = hex::decode(encoded.trim()).unwrap();
    u32::from_le_bytes(preimage[384..388].try_into().unwrap())
}

fn generated_verifier() -> String {
    let json = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json"),
    )
    .unwrap();
    let circuit: GKRCircuitArtifact<Proth120> = serde_json::from_str(&json).unwrap();
    let config = common::production_prover_config();
    let batch_pow_bits = pow_bits::batched_proximity_check_pow_bits::<Proth120, Proth120>(
        config.security_level.security_bits(),
        EVM_PRODUCTION_TRACE_LEN_LOG2 + common::PACK_LOG2,
        config.whir_schedule.base_lde_factor.trailing_zeros() as usize,
        pow_bits::total_base_oracle_columns(&circuit),
    );
    verifier_evm::generate_verifier(
        &circuit,
        &config,
        common::PACK_LOG2,
        20,
        batch_pow_bits,
        fixture_final_pc(),
        &[0, 1],
    )
}

fn yul_function(source: &str, name: &str) -> String {
    let marker = format!("function {name}(");
    assert_eq!(source.matches(&marker).count(), 1, "ambiguous {name}");
    let start = source.find(&marker).unwrap();
    let open = start + source[start..].find('{').unwrap();
    let mut depth = 0;
    for (offset, byte) in source[open..].bytes().enumerate() {
        match byte {
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    return source[start..=open + offset].to_owned();
                }
            }
            _ => {}
        }
    }
    panic!("unterminated {name}");
}

#[test]
fn generated_verifier_checks_windows_before_transcript_processing() {
    let source = generated_verifier();
    let init = yul_function(&source, "transcript_init");
    let check = init
        .find("gkr_validate_inits_teardowns_windows(ptr)")
        .unwrap();
    assert!(check < init.find("calldatacopy(").unwrap());
    assert!(source.contains("ptr := transcript_init(0)"));
    let validation = yul_function(&source, "gkr_validate_inits_teardowns_windows");
    assert!(validation.contains("lt(index, 256)"));
    assert!(validation.contains("lt(i, 2)"));
    assert!(validation.contains("add(preimage_ptr, 404)"));
    // Both committed entrypoints must carry the same checks as regeneration.
    let normalize = |text: &str| text.split_whitespace().collect::<String>();
    for name in [
        "src/GkrWhirVerifier.sol",
        "test/fixtures/GkrWhirVerifierFixture.sol",
    ] {
        let committed = std::fs::read_to_string(
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("generated_contracts/merged")
                .join(name),
        )
        .unwrap();
        assert_eq!(
            normalize(&yul_function(
                &committed,
                "gkr_validate_inits_teardowns_windows"
            )),
            normalize(&validation),
            "{name} window validation drifted",
        );
        assert_eq!(
            normalize(&yul_function(&committed, "transcript_init")),
            normalize(&init)
        );
        assert_eq!(
            normalize(&yul_function(&committed, "gkr_inits_teardowns_topbits")),
            normalize(&yul_function(&source, "gkr_inits_teardowns_topbits")),
        );
    }
}

/// Run explicitly with `cargo test -p verifier_evm --test initialization_windows
/// -- --ignored`. `SOLC_PATH` can select a local Solidity 0.8.36 binary.
#[test]
#[ignore = "requires Foundry and Solidity 0.8.36"]
fn generated_window_validation_executes_in_evm() {
    let source = generated_verifier();
    let functions = [
        yul_function(&source, "gkr_inits_teardowns_topbits"),
        yul_function(&source, "gkr_validate_inits_teardowns_windows"),
    ]
    .join("\n");
    let harness = format!(
        "// SPDX-License-Identifier: UNLICENSED\npragma solidity =0.8.36;\n\
         contract InitializationWindows {{ fallback() external {{ assembly {{\n\
         {functions}\n gkr_validate_inits_teardowns_windows(0)\n\
         mstore(0, 1) return(0, 32)\n }} }} }}\n"
    );
    let directory = std::env::temp_dir().join(format!(
        "airbender-initialization-windows-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir_all(directory.join("src")).unwrap();
    std::fs::create_dir_all(directory.join("test")).unwrap();
    std::fs::create_dir_all(directory.join("fixtures")).unwrap();
    let fixture = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("debug_data/merged_calldata.hex"),
    )
    .unwrap();
    std::fs::write(
        directory.join("fixtures/gkr-calldata.bin"),
        hex::decode(fixture.trim()).unwrap(),
    )
    .unwrap();
    std::fs::write(directory.join("src/GkrVerifier.sol"), source).unwrap();
    std::fs::copy(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("generated_contracts/merged/test/fixtures/GkrWhirVerifierFixture.sol"),
        directory.join("src/GkrWhirVerifierFixture.sol"),
    )
    .unwrap();
    std::fs::write(directory.join("src/InitializationWindows.sol"), harness).unwrap();
    std::fs::write(
        directory.join("test/InitializationWindows.t.sol"),
        include_str!("contracts/InitializationWindows.t.sol"),
    )
    .unwrap();
    std::fs::write(
        directory.join("foundry.toml"),
        "[profile.default]\nvia_ir = true\noptimizer = true\noptimizer_runs = 1\n\
         fs_permissions = [{ access = 'read', path = './fixtures' }]\n\
         [profile.default.fuzz]\nruns = 256\n",
    )
    .unwrap();
    let solc = std::env::var("SOLC_PATH").unwrap_or_else(|_| "0.8.36".to_owned());
    let output = std::process::Command::new("forge")
        .args(["test", "--root"])
        .arg(&directory)
        .args(["--use", &solc, "--offline", "-vv"])
        .output()
        .expect("run Foundry (install forge to execute this explicit EVM test)");
    assert!(
        output.status.success(),
        "EVM tests failed; retained project at {}\n{}\n{}",
        directory.display(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    print!("{}", String::from_utf8_lossy(&output.stdout));
    std::fs::remove_dir_all(directory).unwrap();
}
