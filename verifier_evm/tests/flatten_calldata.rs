//! Regenerate F1 calldata and its statement from the canonical L1 bundle.
mod common;

#[test]
#[ignore = "writes committed calldata; run before the Foundry verifier"]
fn write_calldata_into_debug_data() {
    let (circuit, proof, mode) = common::load();
    let params = common::f1_params();
    let f1 = verifier_evm::encoding::encode_single_tx(
        &circuit,
        &proof,
        &mode,
        &common::prover_config(),
        &params,
    );
    let put = |name: &str, value: &[u8]| {
        std::fs::write(common::data_path(name), hex::encode(value)).unwrap();
    };
    put(common::F1_CALLDATA, &f1.bytes);
    put(
        common::VERIFIED_MARK,
        &verifier_evm::verified_mark(&proof, &mode).to_bytes(),
    );
    std::fs::write(
        common::data_path(common::F1_FIELDS),
        format!(
            "{}\n",
            serde_json::to_string_pretty(&common::f1_field_metadata(&f1, &params)).unwrap()
        ),
    )
    .unwrap();
}
