mod coverage;
mod fixture;

use field::Proth120;

#[test]
fn cpu_fixture_contract() {
    let reference = fixture::manifest_and_identities();
    let circuit = unified_reduced_machine_proth120::circuit_artifact();
    coverage::validate_metadata(&reference, &circuit);
    let (bin, text, nd_words) = fixture::wrap_inputs(&reference);
    assert!(
        !bin.is_empty() && !text.is_empty() && !nd_words.is_empty(),
        "Proth120 witness fixture wrap inputs"
    );
    let value = Proth120::new(1);
    assert!(
        value.raw_u128_value() > u64::MAX as u128,
        "Proth120 fixture typed u128 exercise"
    );
    let json = serde_json::to_string(&value).expect("Proth120 fixture typed u128 encoding");
    let decoded: Proth120 =
        serde_json::from_str(&json).expect("Proth120 fixture typed u128 decoding");
    assert_eq!(
        value.raw_u128_value(),
        decoded.raw_u128_value(),
        "Proth120 fixture typed u128 bytes"
    );

    let actual = [Proth120::new(0), Proth120::new(1), Proth120::new(2)];
    let mut copied_cpu_column = actual.to_vec();
    copied_cpu_column[1] = Proth120::new(0);
    let mismatch = copied_cpu_column
        .iter()
        .copied()
        .zip(actual)
        .enumerate()
        .find_map(|(row, (expected, actual))| {
            fixture::field_cell("memory", 7, row, expected, actual.raw_u128_value()).err()
        })
        .expect("Proth120 witness comparator detects flipped CPU cell");
    assert_eq!(
        (mismatch.set.as_str(), mismatch.column, mismatch.row),
        ("memory", 7, 1),
        "Proth120 witness comparator negative-control location"
    );
    assert_eq!(
        mismatch.expected,
        format!("raw 0x{:032x}", copied_cpu_column[1].raw_u128_value())
    );
    assert_eq!(
        mismatch.actual,
        format!("raw 0x{:032x}", actual[1].raw_u128_value())
    );
}
