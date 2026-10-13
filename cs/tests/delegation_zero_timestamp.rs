use cs::definitions::GKRAddress;
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use field::{Field, PrimeField};

#[test]
fn active_delegations_cannot_use_timestamp_zero() {
    let names = [
        "bigint_with_extended_control",
        "blake2_with_extended_control",
        "blake2_g_function",
        "keccak_special5",
        "keccak_chi5",
        "keccak_column_parity",
        "keccak_theta_rho",
    ];
    for (name, variant) in names
        .into_iter()
        .flat_map(|name| ["gkr", "no_caches_gkr"].map(|variant| (name, variant)))
    {
        let path = format!(
            "{}/compiled_circuits/{name}_layout_{variant}.json",
            env!("CARGO_MANIFEST_DIR")
        );
        let layout: GKRCircuitArtifact<BabyBearField> =
            serde_json::from_reader(std::fs::File::open(path).unwrap()).unwrap();
        let state = layout.memory_layout.delegation_state.as_ref().unwrap();
        let ts_high = GKRAddress::BaseLayerMemory(state.invocation_timestamp[1]);
        // Timestamp comparisons still use the high limb; only its standalone
        // range check is redundant with the main machine's range check.
        assert!(
            layout
                .timestamp_range_check_lookup_expressions
                .iter()
                .all(|lookup| {
                    !(lookup.input.constant.is_zero()
                        && lookup.input.linear_terms.as_ref() == [(BabyBearField::ONE, ts_high)])
                }),
            "{name} {variant}: redundant invocation high-limb range check"
        );
        let input = &layout.timestamp_range_check_lookup_expressions[0].input;
        assert_eq!(input.linear_terms.len(), 2, "{name}");
        let [(ts_coefficient, ts_address), (execute_coefficient, execute_address)] =
            input.linear_terms.as_ref()
        else {
            unreachable!()
        };
        assert!(
            matches!(ts_address, GKRAddress::BaseLayerMemory(_)),
            "{name}"
        );
        assert!(
            matches!(execute_address, GKRAddress::BaseLayerMemory(_)),
            "{name}"
        );
        assert_ne!(ts_address, execute_address, "{name}");

        let lookup_value = |ts_low: u32, execute: u32| {
            let mut result = input.constant;
            for (coefficient, value) in [(*ts_coefficient, ts_low), (*execute_coefficient, execute)]
            {
                let mut term = coefficient;
                term.mul_assign(&BabyBearField::from_u32_unchecked(value));
                result.add_assign(&term);
            }
            result.as_u32_reduced()
        };
        assert_eq!(lookup_value(0, 0), 0, "{name}: padding");
        assert_eq!(lookup_value(1, 1), 0, "{name}: first valid slot");
        assert_eq!(lookup_value(5, 1), 1, "{name}: next valid slot");
        assert_eq!(
            lookup_value((1 << 19) - 3, 1),
            (1 << 17) - 1,
            "{name}: last valid slot before the low limb wraps"
        );
        assert!(
            lookup_value(2, 1) >= 1 << 19,
            "{name}: an active timestamp outside cycle_start + 1 must fail"
        );
        assert!(
            lookup_value(0, 1) >= 1 << 19,
            "{name}: a phantom row must fail the timestamp range lookup"
        );
    }
}
