use prover::definitions::DEFAULT_CAP_SIZE;
use prover::merkle_trees::MerkleTreeCapVarLength;
use setups::{validate_setups_cap_size, Setups, UnrolledCircuitSetupParams};

/// A cap other than the default, exercising the variable-length setup cap.
const NON_DEFAULT_CAP_SIZE: usize = 32;

fn cap(num_leafs: usize) -> MerkleTreeCapVarLength {
    MerkleTreeCapVarLength {
        cap: (0..num_leafs)
            .map(|leaf| core::array::from_fn(|word| (leaf * 8 + word) as u32))
            .collect(),
    }
}

#[test]
fn standard_and_feeder_caps_roundtrip_through_json() {
    for cap_size in [DEFAULT_CAP_SIZE, NON_DEFAULT_CAP_SIZE] {
        let params =
            UnrolledCircuitSetupParams::from_setup_tree_cap(128, 1 << 22, cap(cap_size), cap_size);
        assert_eq!(params.setup_caps.cap.len(), cap_size);
        assert_eq!(params.flattened_setup_caps().len(), cap_size * 8);
        assert_eq!(
            params.flattened_setup_caps(),
            (0..cap_size * 8).map(|w| w as u32).collect::<Vec<_>>()
        );
        let json = serde_json::to_string(&params).unwrap();
        let decoded: UnrolledCircuitSetupParams = serde_json::from_str(&json).unwrap();
        assert_eq!(decoded, params);
        decoded.validate_cap_size(cap_size).unwrap();
        let value: serde_json::Value = serde_json::from_str(&json).unwrap();
        let leaves = value["setup_caps"]["cap"].as_array().unwrap();
        assert_eq!(leaves.len(), cap_size);
        assert!(leaves
            .iter()
            .all(|leaf| leaf.as_array().unwrap().len() == 8));
    }
}

#[test]
fn wrong_cap_lengths_are_rejected() {
    for (num_leafs, expected) in [
        (0, DEFAULT_CAP_SIZE),
        (15, DEFAULT_CAP_SIZE),
        (17, DEFAULT_CAP_SIZE),
        (31, NON_DEFAULT_CAP_SIZE),
        (33, NON_DEFAULT_CAP_SIZE),
        (DEFAULT_CAP_SIZE, NON_DEFAULT_CAP_SIZE),
        (NON_DEFAULT_CAP_SIZE, DEFAULT_CAP_SIZE),
    ] {
        let result = std::panic::catch_unwind(|| {
            UnrolledCircuitSetupParams::from_setup_tree_cap(128, 1 << 22, cap(num_leafs), expected)
        });
        let message = result.unwrap_err();
        let message = message
            .downcast_ref::<String>()
            .cloned()
            .unwrap_or_else(|| message.downcast_ref::<&str>().unwrap().to_string());
        assert_eq!(
            message,
            format!("setup tree cap of family 128 has {num_leafs} leafs, expected {expected}")
        );
        let params = UnrolledCircuitSetupParams {
            family_idx: 128,
            capacity: 1 << 22,
            setup_caps: cap(num_leafs),
        };
        assert!(params.validate_cap_size(expected).is_err());
    }
}

#[test]
fn mixed_cap_setups_are_rejected() {
    let mut setups = Setups::new();
    setups.insert(
        1,
        UnrolledCircuitSetupParams::from_setup_tree_cap(
            1,
            1 << 22,
            cap(DEFAULT_CAP_SIZE),
            DEFAULT_CAP_SIZE,
        ),
    );
    validate_setups_cap_size(&setups, DEFAULT_CAP_SIZE).unwrap();
    assert!(validate_setups_cap_size(&setups, NON_DEFAULT_CAP_SIZE).is_err());
    setups.insert(
        2,
        UnrolledCircuitSetupParams::from_setup_tree_cap(
            2,
            1 << 22,
            cap(NON_DEFAULT_CAP_SIZE),
            NON_DEFAULT_CAP_SIZE,
        ),
    );
    assert!(validate_setups_cap_size(&setups, DEFAULT_CAP_SIZE).is_err());
    assert!(validate_setups_cap_size(&setups, NON_DEFAULT_CAP_SIZE).is_err());
}
