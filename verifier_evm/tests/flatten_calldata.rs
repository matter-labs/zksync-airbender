//! Regenerates the verifier calldata + intermediate commit seed into `debug_data/` using the
//! production flatten/seed functions (from a serialized proof + aux + circuit). This is what a
//! deployment tool would call to prepare the two on-chain transactions' calldata. The two-tx
//! Foundry test reads these `debug_data/*.hex` files. Nothing here is read by `src/`.

mod common;

#[test]
fn write_calldata_into_debug_data() {
    for version in common::selected_versions() {
        let (circuit, proof, aux) = version.load();
        std::fs::create_dir_all(version.data_root).unwrap();
        let put = |name: &str, bytes: &[u8]| {
            let path = version.data_path(name);
            std::fs::write(&path, hex::encode(bytes)).unwrap();
            eprintln!("wrote {} ({} bytes)", path.display(), bytes.len());
        };

        let cfg = version.prover_config();
        let (folds, queries) = (
            &cfg.whir_schedule.whir_steps_schedule,
            &cfg.whir_schedule.whir_queries_schedule,
        );
        put(
            "gkr_full_calldata.hex",
            &verifier_evm::gkr_calldata(&circuit, &proof, &aux),
        );
        put(
            "proth120_whir_calldata_from_proof.hex",
            &verifier_evm::whir_calldata(&circuit, &proof, &aux, folds, queries),
        );
        put(
            "gkr_step1_preimage.hex",
            &verifier_evm::commit_seed_preimage(&circuit, &proof, &aux),
        );
        put(
            "gkr_whir_handoff_seed.hex",
            &verifier_evm::gkr_whir_handoff_seed(&proof),
        );
    }
}
