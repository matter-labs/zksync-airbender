//! Regenerates the verifier calldata, the registry mark and the intermediate commit seed into
//! `debug_data/` using the production flatten/seed/encoding functions (from a serialized proof +
//! aux + circuit). This is what a deployment tool would call to prepare the single transaction's
//! calldata (v0 `merged_calldata.hex`, F1 `single_tx_f1.hex`); the merged Foundry tests read these
//! files. Nothing here is read by `src/`.

mod common;

#[test]
#[ignore = "writes versioned debug_data; run explicitly before read-only drift tests"]
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
        let (gkr, gkr_fields) =
            verifier_evm::flatten::gkr_calldata_with_fields(&circuit, &proof, &aux);
        let merged = verifier_evm::merged_calldata(&circuit, &proof, &aux, folds, queries);
        assert_eq!(&merged[..gkr.len()], &gkr[..]);
        put(common::MERGED_CALLDATA, &merged);
        put(
            common::VERIFIED_MARK,
            &verifier_evm::verified_mark(&proof, &aux).to_bytes(),
        );
        if let Some(name) = version.mutation_fields_file {
            let metadata = common::calldata_field_metadata(&gkr_fields, gkr.len());
            let path = version.data_path(name);
            std::fs::write(
                &path,
                format!("{}\n", serde_json::to_string_pretty(&metadata).unwrap()),
            )
            .unwrap();
            eprintln!("wrote {}", path.display());
        }
        put(
            "gkr_step1_preimage.hex",
            &verifier_evm::commit_seed_preimage(&circuit, &proof, &aux),
        );
        put(
            "gkr_whir_handoff_seed.hex",
            &verifier_evm::gkr_whir_handoff_seed(&proof),
        );
        let f1 =
            verifier_evm::encoding::encode_single_tx(&circuit, &proof, &aux, &version.f1_params());
        put(common::F1_CALLDATA, &f1.bytes);
        let path = version.data_path(common::F1_FIELDS);
        std::fs::write(
            &path,
            format!(
                "{}\n",
                serde_json::to_string_pretty(&common::f1_field_metadata(&f1, &version.f1_params()))
                    .unwrap()
            ),
        )
        .unwrap();
        eprintln!("wrote {}", path.display());
    }
}
