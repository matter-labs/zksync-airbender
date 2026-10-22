mod common;

const MISSING: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/__missing_version_selection_proof__.json"
);

#[test]
fn registered_bundles_are_present() {
    assert_eq!(
        common::registered_versions()
            .iter()
            .map(|version| version.name)
            .collect::<Vec<_>>(),
        ["2p21"]
    );
}

#[test]
fn missing_proof_is_an_error() {
    assert!(!std::path::Path::new(MISSING).exists());
    let version = common::Version {
        proof: MISSING,
        ..common::L1_WRAP_2P21
    };
    assert!(std::panic::catch_unwind(|| version.require_bundle()).is_err());
}

#[test]
fn present_proof_with_missing_aux_is_an_error() {
    let version = common::Version {
        proof: "Cargo.toml", // Check file presence, not proof deserialization.
        aux: MISSING,
        ..common::L1_WRAP_2P21
    };
    assert!(std::panic::catch_unwind(|| version.require_bundle()).is_err());
}
