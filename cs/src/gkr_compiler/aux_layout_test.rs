use crate::definitions::GKRAddress;
use crate::gkr_compiler::{
    CompiledMaxQuadraticGKRRelation, GKRCacheRelation, GKRCircuitArtifact, GKRRelation,
};
use common_constants::TIMESTAMP_COLUMNS_NUM_BITS;
use field::baby_bear::base::BabyBearField;
use field::proth120::Proth120;
use field::{Field, PrimeField};
use std::collections::{BTreeMap, BTreeSet};

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
    let width = artifact.memory_layout.total_width;
    assert!(
        accesses
            .iter()
            .flat_map(|access| access.get_read_timestamp_columns())
            .chain(groups.iter().flat_map(|group| group.read_timestamp))
            .all(|column| column < width),
        "{name}"
    );
    assert!(
        artifact
            .layers
            .iter()
            .flat_map(|layer| layer.cached_relations.values())
            .filter(|relation| matches!(relation, GKRCacheRelation::MemoryTuple(..)))
            .flat_map(|relation| relation.dependencies())
            .all(
                |address| matches!(address, GKRAddress::BaseLayerMemory(column) if column < width)
            ),
        "{name}"
    );
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

type Relation = CompiledMaxQuadraticGKRRelation<BabyBearField>;

fn constraints(artifact: &GKRCircuitArtifact<BabyBearField>) -> Vec<&Relation> {
    artifact
        .layers
        .iter()
        .flat_map(|layer| {
            layer
                .gates_with_external_connections
                .iter()
                .chain(layer.gates.iter())
        })
        .filter_map(|gate| match &gate.enforced_relation {
            GKRRelation::EnforceSingleMaxQuadraticConstraint { input, .. } => Some(input),
            _ => None,
        })
        .collect()
}

fn inputs(relation: &Relation) -> BTreeSet<GKRAddress> {
    relation
        .quadratic_terms
        .iter()
        .flat_map(|(a, terms)| std::iter::once(*a).chain(terms.iter().map(|(_, b)| *b)))
        .chain(relation.linear_terms.iter().map(|(_, a)| *a))
        .collect()
}

fn evaluate(relation: &Relation, values: &BTreeMap<GKRAddress, BabyBearField>) -> BabyBearField {
    let mut result = relation.constant;
    for (a, terms) in relation.quadratic_terms.iter() {
        let mut inner = BabyBearField::ZERO;
        for (coefficient, b) in terms.iter() {
            let mut term = *coefficient;
            term.mul_assign(&values[b]);
            inner.add_assign(&term);
        }
        inner.mul_assign(&values[a]);
        result.add_assign(&inner);
    }
    for (coefficient, a) in relation.linear_terms.iter() {
        let mut term = *coefficient;
        term.mul_assign(&values[a]);
        result.add_assign(&term);
    }
    result
}

#[test]
fn relative_timestamp_group_borrows_are_derived_from_committed_limbs() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/compiled_circuits");
    let limb = BabyBearField::from_u32_unchecked(1 << TIMESTAMP_COLUMNS_NUM_BITS);
    let mut minus_limb = limb;
    minus_limb.negate();
    for (stem, memory_width, witness_width, num_groups, num_generic_lookups) in [
        ("keccak_chi5", 66, 123, 6, 17),
        ("keccak_theta_rho", 72, 127, 4, 50),
    ] {
        for variant in ["layout_gkr", "layout_no_caches_gkr"] {
            let name = format!("{stem}_{variant}");
            let text = std::fs::read_to_string(format!("{dir}/{name}.json")).unwrap();
            let artifact: GKRCircuitArtifact<BabyBearField> = serde_json::from_str(&text).unwrap();
            assert_eq!(artifact.memory_layout.total_width, memory_width, "{name}");
            assert_eq!(artifact.witness_layout.total_width, witness_width, "{name}");
            let witness = &artifact.witness_layout;
            assert!(
                witness.multiplicities_columns_for_range_check_16.is_empty(),
                "{name}"
            );
            assert_eq!(
                witness.multiplicities_columns_for_timestamp_range_check,
                witness_width - 2..witness_width - 1,
                "{name}"
            );
            assert_eq!(
                witness.multiplicities_columns_for_generic_lookup,
                witness_width - 1..witness_width,
                "{name}"
            );
            assert_eq!(
                artifact.generic_lookups.len(),
                num_generic_lookups,
                "{name}"
            );
            assert!(
                artifact.range_check_16_lookup_expressions.is_empty(),
                "{name}"
            );
            assert_eq!(
                artifact.timestamp_range_check_lookup_expressions.len(),
                2,
                "{name}"
            );
            let groups = &artifact.aux_layout_data.relative_timestamp_groups;
            assert_eq!(groups.len(), num_groups, "{name}");
            let state = artifact.memory_layout.delegation_state.as_ref().unwrap();
            let invocation_high = GKRAddress::BaseLayerMemory(state.invocation_timestamp[1]);
            let constraints = constraints(&artifact);
            for group in groups {
                let [low, high] = group.read_timestamp.map(GKRAddress::BaseLayerMemory);
                let readers: Vec<&Relation> = constraints
                    .iter()
                    .copied()
                    .filter(|relation| inputs(relation).contains(&high))
                    .collect();
                let [linear, quadratic] = readers[..] else {
                    panic!(
                        "{name} group {:?}: {} readers",
                        group.members,
                        readers.len()
                    );
                };
                let (linear, quadratic) = if linear.quadratic_terms.is_empty() {
                    (linear, quadratic)
                } else {
                    (quadratic, linear)
                };
                assert!(linear.quadratic_terms.is_empty(), "{name}");
                let coefficient = |address: GKRAddress| {
                    linear
                        .linear_terms
                        .iter()
                        .find(|(_, a)| *a == address)
                        .map(|(c, _)| *c)
                };
                assert_eq!(coefficient(low), Some(BabyBearField::ONE), "{name}");
                assert_eq!(coefficient(high), Some(limb), "{name}");
                assert_eq!(coefficient(invocation_high), Some(minus_limb), "{name}");
                assert_eq!(
                    inputs(quadratic),
                    BTreeSet::from([invocation_high, high]),
                    "{name}"
                );
                for i in 0..3u32 {
                    for h in 0..3u32 {
                        let values = BTreeMap::from([
                            (invocation_high, BabyBearField::from_u32_unchecked(i)),
                            (high, BabyBearField::from_u32_unchecked(h)),
                        ]);
                        let mut borrow = BabyBearField::from_u32_unchecked(i);
                        borrow.sub_assign(&BabyBearField::from_u32_unchecked(h));
                        let mut expected = borrow;
                        expected.sub_assign(&BabyBearField::ONE);
                        expected.mul_assign(&borrow);
                        assert_eq!(evaluate(quadratic, &values), expected, "{name} {i} {h}");
                    }
                }
            }
        }
    }
}
