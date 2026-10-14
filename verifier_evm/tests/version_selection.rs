mod common;

const MISSING: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/__missing_version_selection_proof__.json"
);

#[test]
fn pending_bundle_skips_reads_but_rejects_writes() {
    assert!(!std::path::Path::new(MISSING).exists());
    let version = common::Version {
        proof: MISSING,
        ..common::L1_WRAP_2P21
    };
    assert!(!version.available_for_read("missing-proof regression"));
    assert!(std::panic::catch_unwind(|| version.require_bundle()).is_err());
    let required = common::Version {
        allow_missing_proof: false,
        ..version
    };
    assert!(
        std::panic::catch_unwind(|| required.available_for_read("required-proof regression"))
            .is_err()
    );
}

#[test]
fn present_proof_with_missing_aux_is_an_error() {
    let version = common::Version {
        aux: MISSING,
        allow_missing_proof: true,
        ..common::L1_WRAP_2P22
    };
    assert!(
        std::panic::catch_unwind(|| version.available_for_read("partial-bundle regression"))
            .is_err()
    );
}
