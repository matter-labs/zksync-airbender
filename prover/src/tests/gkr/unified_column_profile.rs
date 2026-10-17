//! Compare the baseline circuit with the globally selected column cuts.
use cs::gkr_circuits::unified_reduced_machine::{
    build_unified_artifact, build_unified_artifact_core, UnifiedCircuitProfile,
    REGULAR_UNIFIED_PROFILE,
};
use field::baby_bear::base::BabyBearField;
use field::{PrimeField, Proth120};

fn check<F: PrimeField>(label: &str, trace_log2: usize) {
    let baseline = build_unified_artifact_core::<F, BabyBearField>(
        true,
        trace_log2,
        1,
        UnifiedCircuitProfile::Baseline,
    );
    let cuts = build_unified_artifact::<F>(true, trace_log2, 1);
    assert_eq!(baseline.memory_layout.total_width, 38, "{label}");
    assert_eq!(cuts.memory_layout.total_width, 38, "{label}");
    assert_eq!(baseline.witness_layout.total_width, 66, "{label}");
    assert_eq!(cuts.witness_layout.total_width, 58, "{label}");
    assert_eq!(baseline.generic_lookup_tables_width, 10, "{label}");
    assert_eq!(cuts.generic_lookup_tables_width, 10, "{label}");
    assert_eq!(
        baseline.num_generic_lookups, cuts.num_generic_lookups,
        "{label}"
    );
    assert_eq!(
        baseline.range_check_16_lookup_expressions.len(),
        cuts.range_check_16_lookup_expressions.len(),
        "{label}"
    );
    assert_eq!(
        baseline.timestamp_range_check_lookup_expressions.len(),
        cuts.timestamp_range_check_lookup_expressions.len(),
        "{label}"
    );
    for (profile, artifact) in [("baseline", &baseline), ("cuts", &cuts)] {
        let layers: Vec<_> = artifact
            .layers
            .iter()
            .map(|layer| {
                (
                    layer.gates.len(),
                    layer.gates_with_external_connections.len(),
                    layer.cached_relations.len(),
                    layer.intermediate_layer_width,
                    layer.inputs().len(),
                )
            })
            .collect();
        println!(
            "{label} {profile}: memory={} witness={} setup={} scratch={} layers={layers:?}",
            artifact.memory_layout.total_width,
            artifact.witness_layout.total_width,
            artifact.generic_lookup_tables_width,
            artifact.scratch_space_size
        );
    }
}

#[test]
#[ignore = "compiles four unified artifacts"]
fn unified_profile_width_vectors() {
    assert_eq!(REGULAR_UNIFIED_PROFILE, UnifiedCircuitProfile::ColumnCuts);
    check::<BabyBearField>("regular 2^23", 23);
    check::<Proth120>("proth120 2^22", 22);
}
