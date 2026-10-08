use crate::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use field::proth120::Proth120;
use field::PrimeField;
use std::collections::BTreeSet;

fn round_trip<F: PrimeField + serde::Serialize + serde::de::DeserializeOwned>(
    text: &str,
) -> GKRCircuitArtifact<F> {
    let artifact: GKRCircuitArtifact<F> = serde_json::from_str(text).unwrap();
    assert_eq!(serde_json::to_string_pretty(&artifact).unwrap(), text);
    artifact
}

fn check_comparisons<F: PrimeField>(name: &str, artifact: &GKRCircuitArtifact<F>) {
    let accesses = &artifact.memory_layout.ram_access_sets;
    let comparisons = &artifact
        .aux_layout_data
        .shuffle_ram_timestamp_comparison_aux_vars;
    let groups = &artifact.aux_layout_data.relative_timestamp_groups;
    if groups.is_empty() {
        assert!(comparisons.iter().all(Option::is_some), "{name}");
        return;
    }
    assert_eq!(comparisons.len(), accesses.len(), "{name}");
    let mut grouped = BTreeSet::new();
    let mut group_columns = BTreeSet::new();
    for group in groups {
        assert!(!group.members.is_empty(), "{name}");
        assert!(group_columns.insert(group.read_timestamp), "{name}");
        for &member in group.members.iter() {
            assert!(grouped.insert(member), "{name} access {member}");
            assert_eq!(
                accesses[member].get_read_timestamp_columns(),
                group.read_timestamp,
                "{name} access {member}"
            );
        }
    }
    for (access_idx, (access, comparison)) in accesses.iter().zip(comparisons).enumerate() {
        assert_eq!(
            comparison.is_none(),
            grouped.contains(&access_idx),
            "{name} access {access_idx}"
        );
        if comparison.is_some() {
            assert!(
                !group_columns.contains(&access.get_read_timestamp_columns()),
                "{name} access {access_idx}"
            );
        }
    }
}

#[test]
fn committed_layouts_round_trip_and_compare_every_ungrouped_access() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/compiled_circuits");
    let mut checked = 0;
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        let name = path.file_name().unwrap().to_str().unwrap().to_owned();
        if !name.contains("_layout_") || !name.ends_with(".json") {
            continue;
        }
        let text = std::fs::read_to_string(&path).unwrap();
        if name.contains("proth120") {
            check_comparisons(&name, &round_trip::<Proth120>(&text));
        } else {
            check_comparisons(&name, &round_trip::<BabyBearField>(&text));
        }
        checked += 1;
    }
    assert!(checked >= 31, "{checked}");
}
