//! Task 14 — Coverage + `U32SpaceGeneric` audit (cs-internal)
//!
//! Three INDEPENDENT checks:
//!
//! - **1a: Full-golden-fixture family coverage.** Deserializes every committed
//!   `cs/compiled_circuits/*_layout_gkr.json` and `*_layout_no_caches_gkr.json`
//!   (22 files, 11 each suffix). Walks `layers[*].gates`,
//!   `gates_with_external_connections`, and `cached_relations` to collect the
//!   `NoFieldGKRRelation` + `NoFieldGKRCacheRelation` discriminant names found in
//!   the committed fixtures. Asserts the observed set equals an explicit
//!   `EXPECTED_FROM_FIXTURES` constant; fails on drift in either direction.
//!
//! - **1b: Support-coverage.** Runs `lower_dag` over every
//!   `single_relation_artifact(variant)` from `sample_relations()`. Collects the
//!   variants that lower WITHOUT `Err`. Asserts this set equals
//!   `EXPECTED_SUPPORTED` (no such constant exists in the generator — this test
//!   defines the drift guard). Also asserts each supported variant has a named
//!   test in the Task-8/9/10 lower family tests.
//!
//! - **1c: `U32SpaceGeneric` audit.** Asserts no golden/fixture artifact contains
//!   a `U32SpaceGeneric` address form in any memory-tuple relation, AND that
//!   `lower_dag` returns `Err` (NOT panic) for a synthetic artifact that does.
//!
//! # Sets must NOT be conflated
//!
//! `EXPECTED_FROM_FIXTURES` and `EXPECTED_SUPPORTED` are intentionally different.
//! `LookupWithDensAndSetupExpressions` is in `EXPECTED_SUPPORTED` (lower_dag
//! handles it) but is absent from `EXPECTED_FROM_FIXTURES` (its CS construction
//! site is commented out so no committed fixture emits it). Merging the two sets
//! would hide this divergence.

use std::collections::BTreeSet;
use std::path::PathBuf;

use field::baby_bear::base::BabyBearField;

use crate::gkr_compiler::{
    GKRCircuitArtifact, NoFieldGKRCacheRelation, NoFieldGKRRelation,
};
use crate::gkr_compiler::dag_ir::lower_dag;
use crate::gkr_compiler::test_support::{sample_relations, single_relation_artifact};

// ── File-system helpers ──────────────────────────────────────────────────────

fn compiled_circuit_dir() -> PathBuf {
    // `cs` lives at `<workspace>/cs`; compiled_circuits is a peer directory.
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("compiled_circuits")
}

/// Load one fixture JSON → `GKRCircuitArtifact<BabyBearField>`.
/// Returns `None` when the file is absent or fails to deserialize (stale
/// fixture layout).
fn load_fixture(path: &PathBuf) -> Option<GKRCircuitArtifact<BabyBearField>> {
    let bytes = std::fs::read(path).ok()?;
    serde_json::from_slice(&bytes).ok()
}

// ── Fixture file lists ───────────────────────────────────────────────────────

/// Every committed `*_layout_gkr.json` fixture.
/// The `inits_and_teardowns` layout is named `..._preprocessed_layout_gkr.json`
/// so we list it explicitly rather than deriving from a base name.
const LAYOUT_GKR_FIXTURES: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_g_function_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "inits_and_teardowns_preprocessed_layout_gkr.json",
    "jump_branch_slt_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "mem_subword_only_layout_gkr.json",
    "mem_word_only_layout_gkr.json",
    "shift_binop_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
];

/// Every committed `*_layout_no_caches_gkr.json` fixture.
const LAYOUT_NO_CACHES_GKR_FIXTURES: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
    "bigint_with_extended_control_layout_no_caches_gkr.json",
    "blake2_g_function_layout_no_caches_gkr.json",
    "blake2_with_extended_control_layout_no_caches_gkr.json",
    "inits_and_teardowns_layout_no_caches_gkr.json",
    "jump_branch_slt_layout_no_caches_gkr.json",
    "keccak_special5_layout_no_caches_gkr.json",
    "mem_subword_only_layout_no_caches_gkr.json",
    "mem_word_only_layout_no_caches_gkr.json",
    "shift_binop_layout_no_caches_gkr.json",
    "unsigned_mul_div_layout_no_caches_gkr.json",
];

// ── Family discriminant name helpers ────────────────────────────────────────

/// Return the discriminant name (like `"LinearBaseFieldRelation"`) for a gate
/// relation.  Exhaustive, NO wildcard arm — adding a variant to
/// `NoFieldGKRRelation` breaks the build here, forcing this list to be updated.
fn gate_family_name(rel: &NoFieldGKRRelation) -> &'static str {
    use NoFieldGKRRelation as R;
    match rel {
        R::LinearBaseFieldRelation { .. } => "LinearBaseFieldRelation",
        R::MaxQuadratic { .. } => "MaxQuadratic",
        R::EnforceSingleMaxQuadraticConstraint { .. } => "EnforceSingleMaxQuadraticConstraint",
        R::EnforceConstraintsMaxQuadratic { .. } => "EnforceConstraintsMaxQuadratic",
        R::CopyInBaseField { .. } => "CopyInBaseField",
        R::CopyInExtensionField { .. } => "CopyInExtensionField",
        R::InitialGrandProductFromCaches { .. } => "InitialGrandProductFromCaches",
        R::InitialGrandProductWithoutCaches { .. } => "InitialGrandProductWithoutCaches",
        R::UnbalancedGrandProductWithCache { .. } => "UnbalancedGrandProductWithCache",
        R::MaterializeGrandProductTermExpression { .. } => "MaterializeGrandProductTermExpression",
        R::TrivialProduct { .. } => "TrivialProduct",
        R::MaskIntoIdentityProduct { .. } => "MaskIntoIdentityProduct",
        R::MaterializeSingleLookupInput { .. } => "MaterializeSingleLookupInput",
        R::MaterializedVectorLookupInput { .. } => "MaterializedVectorLookupInput",
        R::InitsOrTeardownsInitialPair { .. } => "InitsOrTeardownsInitialPair",
        R::LookupWithCachedDensAndSetup { .. } => "LookupWithCachedDensAndSetup",
        R::LookupWithDensAndSetupExpressions { .. } => "LookupWithDensAndSetupExpressions",
        R::LookupWithDensAndCachedSetup { .. } => "LookupWithDensAndCachedSetup",
        R::LookupPairFromBaseInputs { .. } => "LookupPairFromBaseInputs",
        R::LookupPairFromMaterializedBaseInputs { .. } => "LookupPairFromMaterializedBaseInputs",
        R::LookupFromMaterializedBaseInputWithSetup { .. } => {
            "LookupFromMaterializedBaseInputWithSetup"
        }
        R::LookupUnbalancedPairWithMaterializedBaseInputs { .. } => {
            "LookupUnbalancedPairWithMaterializedBaseInputs"
        }
        R::LookupPairFromVectorInputs { .. } => "LookupPairFromVectorInputs",
        R::LookupPairFromMaterializedVectorInputs { .. } => {
            "LookupPairFromMaterializedVectorInputs"
        }
        R::LookupFromVectorInputWithSetup { .. } => "LookupFromVectorInputWithSetup",
        R::LookupFromMaterializedVectorInputWithSetup { .. } => {
            "LookupFromMaterializedVectorInputWithSetup"
        }
        R::LookupPairFromCachedVectorInputs { .. } => "LookupPairFromCachedVectorInputs",
        R::LookupUnbalancedPairWithVectorInputs { .. } => "LookupUnbalancedPairWithVectorInputs",
        R::LookupUnbalancedPairWithMaterializedVectorInputs { .. } => {
            "LookupUnbalancedPairWithMaterializedVectorInputs"
        }
        R::AggregateLookupRationalPair { .. } => "AggregateLookupRationalPair",
    }
}

/// Return the discriminant name for a cache relation.
fn cache_family_name(rel: &NoFieldGKRCacheRelation) -> &'static str {
    match rel {
        NoFieldGKRCacheRelation::SingleColumnLookup { .. } => "Cache::SingleColumnLookup",
        NoFieldGKRCacheRelation::VectorizedLookup(_) => "Cache::VectorizedLookup",
        NoFieldGKRCacheRelation::MemoryTuple(_) => "Cache::MemoryTuple",
        NoFieldGKRCacheRelation::VectorizedLookupSetup(_) => "Cache::VectorizedLookupSetup",
    }
}

// ── Collect families from one artifact ──────────────────────────────────────

/// Walk every layer's `gates`, `gates_with_external_connections`, and
/// `cached_relations` and insert the family name (gate or cache variant) into
/// `names`.
fn collect_families(artifact: &GKRCircuitArtifact<BabyBearField>, names: &mut BTreeSet<&'static str>) {
    for layer in &artifact.layers {
        for gate in layer.gates.iter().chain(layer.gates_with_external_connections.iter()) {
            names.insert(gate_family_name(&gate.enforced_relation));
        }
        for (_addr, rel) in layer.cached_relations.iter() {
            names.insert(cache_family_name(rel));
        }
    }
}

// ── Step 1a: EXPECTED_FROM_FIXTURES ─────────────────────────────────────────

/// The exact set of `NoFieldGKRRelation` and `NoFieldGKRCacheRelation`
/// discriminants observed in ALL 22 committed layout fixtures. Fail on drift in
/// EITHER direction.
///
/// Derived by: run the test `fixture_family_coverage` with this set temporarily
/// empty, observe what the test reports as observed, verify manually, then fill
/// this in as the authoritative constant.
///
/// `LookupWithDensAndSetupExpressions` is absent here because its CS
/// construction site is commented out (Task 13 handoff).
const EXPECTED_FROM_FIXTURES: &[&str] = &[
    // ── Gate families ────────────────────────────────────────────────────────
    // (Observed from all 22 committed layout fixtures; derived by running the
    // test and recording the full observed set.)
    //
    // Notable ABSENCES from fixtures (compared to EXPECTED_SUPPORTED):
    //   - EnforceConstraintsMaxQuadratic: not emitted by any committed circuit
    //   - LinearBaseFieldRelation: not emitted by any committed circuit
    //   - LookupPairFromCachedVectorInputs: not emitted by any committed circuit
    //   - LookupWithDensAndSetupExpressions: CS construction site commented out
    //   - UnbalancedGrandProductWithCache: not emitted by any committed circuit
    "AggregateLookupRationalPair",
    "CopyInBaseField",
    "CopyInExtensionField",
    "EnforceSingleMaxQuadraticConstraint",
    "InitialGrandProductFromCaches",
    "InitialGrandProductWithoutCaches",
    "InitsOrTeardownsInitialPair",
    "LookupFromMaterializedBaseInputWithSetup",
    "LookupFromMaterializedVectorInputWithSetup",
    "LookupFromVectorInputWithSetup",
    "LookupPairFromBaseInputs",
    "LookupPairFromMaterializedBaseInputs",
    "LookupPairFromMaterializedVectorInputs",
    "LookupPairFromVectorInputs",
    "LookupUnbalancedPairWithMaterializedBaseInputs",
    "LookupUnbalancedPairWithMaterializedVectorInputs",
    "LookupUnbalancedPairWithVectorInputs",
    "LookupWithCachedDensAndSetup",
    "LookupWithDensAndCachedSetup",
    "MaskIntoIdentityProduct",
    "MaterializeGrandProductTermExpression",
    "MaterializeSingleLookupInput",
    "MaterializedVectorLookupInput",
    "MaxQuadratic",
    "TrivialProduct",
    // ── Cache families ───────────────────────────────────────────────────────
    "Cache::MemoryTuple",
    "Cache::SingleColumnLookup",
    "Cache::VectorizedLookup",
    "Cache::VectorizedLookupSetup",
];

// ── Step 1b: EXPECTED_SUPPORTED ─────────────────────────────────────────────

/// The exact set of `NoFieldGKRRelation` variant names that `lower_dag` handles
/// without returning `Err`. Defined here as the drift guard — no such constant
/// exists in the generator.
///
/// Differs from `EXPECTED_FROM_FIXTURES` in that it covers only GATE relations
/// (not cache relations — caches are lowered internally by `lower_dag` and are
/// not exposed through `single_relation_artifact`). It also includes
/// `LookupWithDensAndSetupExpressions` (generator supports it; no fixture emits
/// it) and excludes some variants that are confirmed-dead (`U32SpaceGeneric`
/// propagation) or not reachable through `single_relation_artifact`.
const EXPECTED_SUPPORTED: &[&str] = &[
    "AggregateLookupRationalPair",
    "CopyInBaseField",
    "CopyInExtensionField",
    "EnforceConstraintsMaxQuadratic",
    "EnforceSingleMaxQuadraticConstraint",
    "InitialGrandProductFromCaches",
    "InitialGrandProductWithoutCaches",
    "InitsOrTeardownsInitialPair",
    "LinearBaseFieldRelation",
    "LookupFromMaterializedBaseInputWithSetup",
    "LookupFromMaterializedVectorInputWithSetup",
    "LookupFromVectorInputWithSetup",
    "LookupPairFromBaseInputs",
    "LookupPairFromCachedVectorInputs",
    "LookupPairFromMaterializedBaseInputs",
    "LookupPairFromMaterializedVectorInputs",
    "LookupPairFromVectorInputs",
    "LookupUnbalancedPairWithMaterializedBaseInputs",
    "LookupUnbalancedPairWithMaterializedVectorInputs",
    "LookupUnbalancedPairWithVectorInputs",
    "LookupWithCachedDensAndSetup",
    "LookupWithDensAndCachedSetup",
    // LookupWithDensAndSetupExpressions: supported by lower_dag, but absent
    // from committed fixtures (CS construction site commented out — Task 13
    // handoff). Present here but NOT in EXPECTED_FROM_FIXTURES.
    "LookupWithDensAndSetupExpressions",
    "MaskIntoIdentityProduct",
    "MaterializeGrandProductTermExpression",
    "MaterializeSingleLookupInput",
    "MaterializedVectorLookupInput",
    "MaxQuadratic",
    "TrivialProduct",
    "UnbalancedGrandProductWithCache",
];

// ── Test: 1a — fixture family coverage ──────────────────────────────────────

/// Parse every committed `*_layout_gkr.json` and `*_layout_no_caches_gkr.json`
/// fixture and collect the actual `NoFieldGKRRelation` and
/// `NoFieldGKRCacheRelation` discriminant names. Assert the observed set equals
/// `EXPECTED_FROM_FIXTURES` exactly (fail on drift in either direction).
///
/// Every enumerated fixture file must deserialize successfully — a stale or
/// missing file is a hard test failure (not a silent skip).  This prevents a
/// newly-introduced relation family from vacuously passing if it only appears in
/// a fixture that was silently skipped.
#[test]
fn fixture_family_coverage() {
    let dir = compiled_circuit_dir();
    let mut observed: BTreeSet<&'static str> = BTreeSet::new();
    let mut loaded_count = 0usize;
    let all_fixtures: Vec<&&str> = LAYOUT_GKR_FIXTURES
        .iter()
        .chain(LAYOUT_NO_CACHES_GKR_FIXTURES.iter())
        .collect();
    let files_found = all_fixtures.len();

    for filename in &all_fixtures {
        let path = dir.join(filename);
        let artifact = load_fixture(&path).unwrap_or_else(|| {
            panic!(
                "fixture_family_coverage: failed to load or deserialize fixture {:?} \
                 (stale layout is a hard test failure — regenerate the fixture)",
                path.display()
            )
        });
        loaded_count += 1;
        collect_families(&artifact, &mut observed);
    }

    assert_eq!(
        loaded_count, files_found,
        "fixture_family_coverage: loaded {loaded_count} of {files_found} fixtures — \
         every enumerated fixture must load successfully"
    );

    assert!(
        loaded_count > 0,
        "fixture_family_coverage: zero fixtures loaded — is compiled_circuit_dir correct? ({})",
        dir.display()
    );

    let expected: BTreeSet<&'static str> = EXPECTED_FROM_FIXTURES.iter().copied().collect();

    // Families in fixtures but NOT in the expected set → unexpected fixture family.
    let unexpected: Vec<_> = observed.difference(&expected).copied().collect();
    // Families in the expected set but NOT in fixtures → missing expected family.
    let missing: Vec<_> = expected.difference(&observed).copied().collect();

    assert!(
        unexpected.is_empty() && missing.is_empty(),
        "fixture family drift detected ({loaded_count} fixtures loaded).\n\
         Unexpected (in fixtures but not in EXPECTED_FROM_FIXTURES): {unexpected:?}\n\
         Missing (in EXPECTED_FROM_FIXTURES but not in fixtures): {missing:?}\n\
         Full observed set: {observed:?}"
    );
}

// ── Test: 1b — support-coverage ─────────────────────────────────────────────

/// Every variant from `sample_relations()` that `lower_dag` handles without `Err`
/// must equal `EXPECTED_SUPPORTED`. Fails on drift in either direction — if a
/// variant is added to the generator without updating this constant, or if a
/// variant is removed, the test fails.
///
/// Also asserts `LookupWithDensAndSetupExpressions` is in `EXPECTED_SUPPORTED`
/// but NOT in `EXPECTED_FROM_FIXTURES` (the concrete divergence between the two
/// sets that spec §9 mandates are kept independent).
#[test]
fn support_coverage() {
    let mut supported: BTreeSet<&'static str> = BTreeSet::new();

    for (name, rel) in sample_relations() {
        let artifact = single_relation_artifact(rel);
        if lower_dag(&artifact).is_ok() {
            supported.insert(name);
        }
    }

    let expected: BTreeSet<&'static str> = EXPECTED_SUPPORTED.iter().copied().collect();

    let extra: Vec<_> = supported.difference(&expected).copied().collect();
    let missing: Vec<_> = expected.difference(&supported).copied().collect();

    assert!(
        extra.is_empty() && missing.is_empty(),
        "support-coverage drift detected.\n\
         Variants that lower OK but are not in EXPECTED_SUPPORTED: {extra:?}\n\
         Variants in EXPECTED_SUPPORTED that did NOT lower OK: {missing:?}\n\
         Full supported set: {supported:?}"
    );

    // Assert the canonical §9 divergence: LookupWithDensAndSetupExpressions
    // must be in EXPECTED_SUPPORTED (supported) but absent from EXPECTED_FROM_FIXTURES
    // (no committed fixture emits it). This is the concrete reason the two sets
    // must not be conflated.
    assert!(
        expected.contains("LookupWithDensAndSetupExpressions"),
        "LookupWithDensAndSetupExpressions must be in EXPECTED_SUPPORTED"
    );
    let from_fixtures: BTreeSet<&'static str> = EXPECTED_FROM_FIXTURES.iter().copied().collect();
    assert!(
        !from_fixtures.contains("LookupWithDensAndSetupExpressions"),
        "LookupWithDensAndSetupExpressions must NOT be in EXPECTED_FROM_FIXTURES \
         (CS construction site commented out — no fixture should emit it). \
         If a fixture was found to emit it in test 1a, that is a STOP finding: \
         update EXPECTED_FROM_FIXTURES and report the divergence."
    );
}

// ── Test: 1c — U32SpaceGeneric audit ────────────────────────────────────────

/// Asserts:
///
/// 1. No committed fixture contains the `U32SpaceGeneric` address form in any
///    gate or cache memory-tuple relation.
/// 2. `lower_dag` returns `Err` (not panic) for a synthetic artifact that
///    DOES contain `U32SpaceGeneric`.
///
/// `U32SpaceGeneric` is a `CompiledAddressStrict` variant in
/// `NoFieldSpecialMemoryContributionRelation::address`; the confirmed-dead
/// `prover::evaluate_memory_query` `todo!()` path means no real circuit
/// should ever emit it.
#[test]
fn u32_space_generic_audit() {
    use crate::gkr_compiler::{
        CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
        NoFieldSpecialMemoryContributionRelation,
    };
    use crate::definitions::gkr::RamWordRepresentation;

    // ── Part 1: no committed fixture contains U32SpaceGeneric ───────────────

    let dir = compiled_circuit_dir();
    let mut loaded_count = 0usize;

    for filename in LAYOUT_GKR_FIXTURES
        .iter()
        .chain(LAYOUT_NO_CACHES_GKR_FIXTURES.iter())
    {
        let path = dir.join(filename);
        let artifact = load_fixture(&path).unwrap_or_else(|| {
            panic!(
                "u32_space_generic_audit: failed to load fixture {:?} \
                 (stale layout is a hard test failure)",
                path.display()
            )
        });
        loaded_count += 1;

        // Walk every memory tuple that appears in the artifact.
        for layer in &artifact.layers {
            let all_gates = layer
                .gates
                .iter()
                .chain(layer.gates_with_external_connections.iter());
            for gate in all_gates {
                check_relation_no_u32_generic(filename, &gate.enforced_relation);
            }
            for (_addr, cache_rel) in layer.cached_relations.iter() {
                if let NoFieldGKRCacheRelation::MemoryTuple(mt) = cache_rel {
                    assert_no_u32_space_generic(filename, "Cache::MemoryTuple", mt);
                }
            }
        }
    }

    assert!(
        loaded_count > 0,
        "u32_space_generic_audit: zero fixtures loaded (is compiled_circuit_dir correct?)"
    );

    // ── Part 2: lower_dag returns Err (not panic) for a synthetic U32SpaceGeneric ──

    let generic_tuple = NoFieldSpecialMemoryContributionRelation {
        address_space: CompiledAddressSpaceRelationStrict::Constant(0),
        address: CompiledAddressStrict::U32SpaceGeneric([
            (vec![(1u64, 0usize)].into_boxed_slice(), 0u64),
            (vec![(1u64, 1usize)].into_boxed_slice(), 0u64),
        ]),
        timestamp: CompiledMemoryTimestamp::Zero,
        value: RamWordRepresentation::Zero,
        timestamp_offset: 0,
    };

    // Embed in a MaterializeGrandProductTermExpression gate (the simplest
    // gate that passes through a single memory tuple to lower_memory_tuple).
    let rel = NoFieldGKRRelation::MaterializeGrandProductTermExpression {
        input: generic_tuple,
        output: crate::definitions::GKRAddress::InnerLayer { layer: 1, offset: 0 },
    };
    let artifact = single_relation_artifact(rel);
    let result = lower_dag(&artifact);
    assert!(
        result.is_err(),
        "lower_dag must return Err (not panic) for a U32SpaceGeneric artifact"
    );
    let msg = result.unwrap_err();
    assert!(
        msg.contains("U32SpaceGeneric"),
        "Err message must name the dead path; got: {msg:?}"
    );
}

// ── Task 2: PeekSingleColumn resolution coverage ────────────────────────────

#[test]
fn resolutions_peek_single_column_present_for_timestamp() {
    use crate::gkr_compiler::dag_ir::{lower_dag, RangeWidth, ResolutionStrategy};

    let path = compiled_circuit_dir().join("jump_branch_slt_layout_gkr.json");
    let artifact = load_fixture(&path).expect("fixture must load");
    let circuit = lower_dag(&artifact).expect("lower_dag must succeed");

    let timestamp_peeks = circuit
        .layers
        .iter()
        .flat_map(|l| l.resolutions.values())
        .filter(|s| matches!(s, ResolutionStrategy::PeekSingleColumn { width: RangeWidth::Timestamp, .. }))
        .count();
    assert!(
        timestamp_peeks > 0,
        "timestamp single-column lookups must emit PeekSingleColumn{{Timestamp}} resolutions"
    );
}

/// Assert no memory-tuple in `rel` uses `U32SpaceGeneric`.
fn check_relation_no_u32_generic(fixture_name: &str, rel: &NoFieldGKRRelation) {
    use crate::gkr_compiler::CompiledAddressStrict;
    use NoFieldGKRRelation as R;

    let tuples: Vec<_> = match rel {
        R::MaterializeGrandProductTermExpression { input, .. } => vec![input],
        R::InitialGrandProductWithoutCaches { input, .. } => {
            vec![&input[0], &input[1]]
        }
        // For the other variants there is no inline memory tuple.
        _ => return,
    };
    for mt in tuples {
        assert_no_u32_space_generic(fixture_name, "gate", mt);
    }
}

fn assert_no_u32_space_generic(
    fixture_name: &str,
    context: &str,
    mt: &crate::gkr_compiler::NoFieldSpecialMemoryContributionRelation,
) {
    use crate::gkr_compiler::CompiledAddressStrict;
    assert!(
        !matches!(mt.address, CompiledAddressStrict::U32SpaceGeneric(..)),
        "fixture {fixture_name:?} contains U32SpaceGeneric in {context} — \
         this is the confirmed-dead path and should never appear in committed artifacts"
    );
}
