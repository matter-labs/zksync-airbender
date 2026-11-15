//! Regenerate the compressed calldata and its statement from the canonical L1 bundle.
mod common;

#[test]
#[ignore = "writes committed calldata; run before the Foundry verifier"]
fn write_calldata_into_debug_data() {
    let (circuit, proof, mode) = common::load();
    let params = common::format_params();
    let calldata = verifier_evm::encoding::encode_single_tx(
        &circuit,
        &proof,
        &mode,
        &common::prover_config(),
        &params,
    );
    let put = |name: &str, value: &[u8]| {
        std::fs::write(common::data_path(name), hex::encode(value)).unwrap();
    };
    put(common::CALLDATA, &calldata.bytes);
    put(
        common::VERIFIED_MARK,
        &verifier_evm::verified_mark(&proof, &mode).to_bytes(),
    );
    std::fs::write(
        common::data_path(common::CALLDATA_FIELDS),
        format!(
            "{}\n",
            serde_json::to_string_pretty(&common::calldata_field_metadata(&calldata, &params))
                .unwrap()
        ),
    )
    .unwrap();
}
