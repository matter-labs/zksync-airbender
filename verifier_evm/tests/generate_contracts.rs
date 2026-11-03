//! Regenerates the on-chain verifier Solidity into `generated_contracts/merged/src/` from the
//! circuit artifact. The Foundry project scaffolding (foundry.toml + the single-transaction
//! test) is committed static. The production verifier binds the checked-in feeder binary; a
//! separate test-only verifier binds the saved proof's program, which may be an older feeder.
//!
//! NOTE: on macOS/aarch64 nightly, rustc may SIGBUS in debuginfo emission while compiling the
//! `keccak_special5` circuit crate this test transitively depends on; run with
//! `RUSTFLAGS="-C debuginfo=0"` (see generated_contracts/run_merged.sh).

mod common;

use common::production_prover_config;
use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;

use std::path::Path;
use trace_and_split::setups::program_setups::find_binary_exit_point;

// Deployment parameters for the program being verified. These are properties of the *program +
// circuit*, NOT of any particular proof — verifier synthesis must never depend on proof/aux data.
// The verifier binds the statement to the terminal PC of the checked-in L1 feeder verifier binary
// (`feeder_exit_pc`); the external-challenges PoW difficulty is a verifier soundness knob.
const EXTERNAL_POW_BITS: u32 = 20;
// The inits/teardowns RAM-set base chunk indices the program is proven with (one per teardown
// set of the circuit, each pinned in the verifier as a uint8 constant): the unified circuit's
// sets are enumerated 0, 1.
const INITS_TEARDOWNS_TOP_BITS: &[u32] = &[0, 1];
// `fsv_unified_recursion_layer_sec_100_l1_feeder` (special-opcodes blake variant) — the merged-mode
// L1-feeder full-statement verifier whose execution the L1 proof attests (it verifies the final
// BabyBear recursion artifact).
const FEEDER_BINARY: &str =
    "../tools/gkr_verifier/fsv_unified_recursion_layer_sec_100_l1_feeder_special_opcodes_extension.bin";

fn feeder_exit_pc() -> u32 {
    let bytes = std::fs::read(FEEDER_BINARY).unwrap_or_else(|_| {
        panic!("Missing {FEEDER_BINARY} — run reproducible build script first");
    });
    assert!(
        bytes.len().is_multiple_of(4),
        "binary section not word-aligned"
    );
    let binary: Vec<u32> = bytes
        .as_chunks::<4>()
        .0
        .iter()
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect();
    find_binary_exit_point(&binary)
}

fn generate_contract(final_pc: u32, inits_teardowns_top_bits: &[u32]) -> String {
    let json = std::fs::read_to_string(
        "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
    )
    .unwrap();
    let circuit: GKRCircuitArtifact<Proth120> = serde_json::from_str(&json).unwrap();

    let prover_config = production_prover_config();
    // the packing factor and the WHIR batching PoW come from the prover config
    verifier_evm::generate_verifier(
        &circuit,
        &prover_config,
        EXTERNAL_POW_BITS,
        final_pc,
        inits_teardowns_top_bits,
    )
}

#[test]
fn generate_contract_into_dir() {
    let src = generate_contract(feeder_exit_pc(), INITS_TEARDOWNS_TOP_BITS);

    let p = Path::new("generated_contracts/merged/src/GkrWhirVerifier.sol");
    std::fs::create_dir_all(p.parent().unwrap()).unwrap();
    std::fs::write(p, &src).unwrap();
    eprintln!("wrote {} ({} bytes)", p.display(), src.len());
}

#[test]
fn generate_fixture_contract_into_dir() {
    // This preimage is checked against the saved proof by flatten_roundtrip. Its final PC
    // and teardown top bits are properties of that proof's program, not deployment
    // parameters for the production verifier above. The preimage begins with 32 registers
    // of three LE u32 words each, then final PC/timestamp (12 bytes), then the top bits.
    let preimage = hex::decode(
        std::fs::read_to_string("debug_data/gkr_step1_preimage.hex")
            .unwrap()
            .trim(),
    )
    .unwrap();
    let final_pc = u32::from_le_bytes(preimage[32 * 12..32 * 12 + 4].try_into().unwrap());
    let top_bits_offset = 32 * 12 + 12;
    let top_bits: Vec<_> = (0..INITS_TEARDOWNS_TOP_BITS.len())
        .map(|i| {
            let offset = top_bits_offset + i * 4;
            u32::from_le_bytes(preimage[offset..offset + 4].try_into().unwrap())
        })
        .collect();
    let src = generate_contract(final_pc, &top_bits);
    let declaration = "contract GkrWhirVerifier {";
    assert_eq!(src.matches(declaration).count(), 1);
    let src = src.replacen(declaration, "contract GkrWhirVerifierFixture {", 1);
    let p = Path::new("generated_contracts/merged/test/fixtures/GkrWhirVerifierFixture.sol");
    std::fs::create_dir_all(p.parent().unwrap()).unwrap();
    std::fs::write(p, &src).unwrap();
    eprintln!("wrote {} ({} bytes)", p.display(), src.len());
}
