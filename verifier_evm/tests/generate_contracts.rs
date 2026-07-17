//! Regenerates the on-chain verifier Solidity into `generated_contracts/` from the circuit
//! artifact. The Foundry project scaffolding (foundry.toml + the two-tx test) is committed
//! static; only the three verifier sources are (re)generated here.

use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;
use std::path::Path;

// Deployment parameters for the current program/proof (Sec100). See gkr.sol constants.
const EXTERNAL_POW_BITS: u32 = 20;
const WHIR_BATCH_POW_BITS: u32 = 11;
const FINAL_PC: u32 = 384;

#[test]
fn generate_contracts_into_dir() {
    let json = std::fs::read_to_string(
        "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
    )
    .unwrap();
    let circuit: GKRCircuitArtifact<Proth120> = serde_json::from_str(&json).unwrap();

    let out = verifier_evm::generate_verifiers(
        &circuit,
        EXTERNAL_POW_BITS,
        WHIR_BATCH_POW_BITS,
        FINAL_PC,
    );

    let root = Path::new("generated_contracts");
    let write = |rel: &str, content: &str| {
        let p = root.join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(&p, content).unwrap();
        eprintln!("wrote {} ({} bytes)", p.display(), content.len());
    };

    write("gkr/src/GkrVerifier.sol", &out.gkr_sol);
    write("whir/src/WhirVerifier.sol", &out.whir_sol);
    write("two_tx/src/GkrWhirRegistry.sol", &out.registry_sol);
}
