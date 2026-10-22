mod common;

const MISSING: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/__missing_version_selection_proof__.json"
);

#[test]
fn pending_bundle_skips_reads_but_rejects_writes() {
    assert!(!std::path::Path::new(MISSING).exists());
    assert_eq!(
        common::VERSIONS.iter().map(|v| v.name).collect::<Vec<_>>(),
        ["2p21"]
    );
    let version = common::Version {
        proof: MISSING,
        contracts_root: MISSING,
        data_root: MISSING,
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
fn generated_outputs_forbid_missing_proof_skip() {
    for (contracts_root, data_root, wrong_final_pc_contract) in [
        (".", MISSING, Some("src/templates/gkr.sol")),
        (MISSING, "src", None),
    ] {
        // Immutable source files exercise the output-presence checks without a proof bundle.
        let version = common::Version {
            proof: MISSING,
            contracts_root,
            data_root,
            wrong_final_pc_contract,
            ..common::L1_WRAP_2P21
        };
        assert!(
            std::panic::catch_unwind(|| version.available_for_read("lost-proof regression"))
                .is_err(),
            "a missing proof with generated outputs must fail"
        );
    }
}

#[test]
fn present_proof_with_missing_aux_is_an_error() {
    let version = common::Version {
        proof: "Cargo.toml", // This test checks file presence, not proof deserialization.
        aux: MISSING,
        allow_missing_proof: true,
        ..common::L1_WRAP_2P21
    };
    assert!(
        std::panic::catch_unwind(|| version.available_for_read("partial-bundle regression"))
            .is_err()
    );
}
