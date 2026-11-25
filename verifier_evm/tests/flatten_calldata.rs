//! Regenerate the compressed calldata and its statement from the canonical L1 bundle.
mod common;
use prover::definitions::SoundnessMode;

#[test]
#[ignore = "writes committed calldata; run before the Foundry verifier"]
fn write_calldata_into_debug_data() {
    for &mode in SoundnessMode::ALL {
        write_calldata(mode);
    }
}

fn write_calldata(mode: SoundnessMode) {
    let (circuit, proof, operation_mode) = common::load(mode);
    let params = common::format_params(mode);
    let calldata = verifier_evm::encoding::encode_single_tx(
        &circuit,
        &proof,
        &operation_mode,
        &common::prover_config(mode),
        &params,
    );
    let put = |name: &str, value: &[u8]| {
        std::fs::write(common::data_path(mode, name), hex::encode(value)).unwrap();
    };
    put(common::CALLDATA, &calldata.bytes);
    put(
        common::VERIFIED_MARK,
        &verifier_evm::verified_mark(&operation_mode).to_bytes(),
    );
    std::fs::write(
        common::data_path(mode, common::CALLDATA_FIELDS),
        format!(
            "{}\n",
            serde_json::to_string_pretty(&common::calldata_field_metadata(&calldata, &params))
                .unwrap()
        ),
    )
    .unwrap();
}
