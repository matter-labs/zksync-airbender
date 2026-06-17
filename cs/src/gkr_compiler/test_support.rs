//! Shared GKR test-support fixtures.
//!
//! These builders are `pub` and gated behind `#[cfg(any(test, feature =
//! "test-support"))]` so they can be reused by tests in BOTH the `cs` crate and
//! downstream crates (e.g. `prover`). `cs`'s `#[cfg(test)]` items are not
//! compiled when `cs` is a dependency, and `pub(crate)` items are invisible
//! cross-crate, so the only way to share these artifact/relation builders is a
//! `pub` module behind a Cargo feature.

use std::collections::BTreeMap;

use super::codegen_ir::{Domain, RelationMeta};
use super::{GKRCircuitArtifact, GKRLayerDescription, GateArtifacts, NoFieldGKRRelation};
use crate::definitions::gkr::{GKRMemoryLayout, GKRWitnessLayout};
use crate::definitions::GKRAddress;
use crate::gkr_compiler::layout::GKRAuxLayoutData;

/// Concrete field used by all GKR test fixtures.
pub type ConcreteField = ::field::baby_bear::base::BabyBearField;

/// `GKRAddress::BaseLayerWitness(i)` helper.
fn blw(i: usize) -> GKRAddress {
    GKRAddress::BaseLayerWitness(i)
}

/// `GKRAddress::InnerLayer { layer, offset }` helper.
fn inner(layer: usize, offset: usize) -> GKRAddress {
    GKRAddress::InnerLayer { layer, offset }
}

// ---------------------------------------------------------------------------
// add_sub golden artifact builders (relocated from codegen_ir's private test
// module so they can be reused cross-crate).
// ---------------------------------------------------------------------------

/// Compile the smallest family circuit (add_sub_lui_auipc_mop) into a real,
/// multi-layer GKR artifact WITH intermediate denominator caches.
pub fn build_add_sub_artifact() -> GKRCircuitArtifact<ConcreteField> {
    use crate::gkr_circuits::add_sub_family::{
        add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr,
        add_sub_lui_auipc_mop_table_addition_fn,
    };
    use crate::gkr_compiler::compile_unrolled_circuit_state_transition_into_gkr;
    use common_constants::ROM_WORD_SIZE;

    compile_unrolled_circuit_state_transition_into_gkr::<ConcreteField>(
        &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
        &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr(cs),
        ROM_WORD_SIZE,
        24,
    )
}

/// Same circuit as [`build_add_sub_artifact`] but WITHOUT intermediate caches.
pub fn build_add_sub_artifact_no_caches() -> GKRCircuitArtifact<ConcreteField> {
    use crate::gkr_circuits::add_sub_family::{
        add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr,
        add_sub_lui_auipc_mop_table_addition_fn,
    };
    use crate::gkr_compiler::compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches;
    use common_constants::ROM_WORD_SIZE;

    compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches::<ConcreteField>(
        &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
        &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr(cs),
        ROM_WORD_SIZE,
        24,
    )
}

// ---------------------------------------------------------------------------
// Per-variant sample relations + metadata (relocated from codegen_ir's private
// `mod tests`). One representative relation per `NoFieldGKRRelation` variant.
// ---------------------------------------------------------------------------

/// Static variant name for a `NoFieldGKRRelation` (the variant identifier).
/// Exhaustive with NO `_` arm so a future variant breaks the build.
pub fn variant_name(rel: &NoFieldGKRRelation) -> &'static str {
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

/// One constructed relation per `NoFieldGKRRelation` variant, paired with its
/// expected [`RelationMeta`]. Single source of truth for per-variant relation
/// fixtures, cross-validated against `relation_metadata()` /
/// `NoFieldGKRRelation::num_challenges()`.
pub fn metadata_fixtures() -> Vec<(NoFieldGKRRelation, RelationMeta)> {
    use super::{
        CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
        InitsOrTeardownsTimestampAndValue, NoFieldGKRRelation as R,
        NoFieldMaxQuadraticConstraintsGKRRelation, NoFieldMaxQuadraticGKRRelation,
        NoFieldSpecialMemoryContributionRelation, NoFieldStructuredExpression as E,
    };
    use crate::definitions::gkr::{
        NoFieldLinearRelation, NoFieldSingleColumnLookupRelation, NoFieldVectorLookupRelation,
        RamWordRepresentation,
    };

    let a0 = blw(0);
    let a1 = blw(1);
    let out0 = inner(1, 0);
    let out1 = inner(1, 1);

    let lin = NoFieldLinearRelation {
        linear_terms: vec![(1u32, a0)].into_boxed_slice(),
        constant: 0,
    };
    let mq = NoFieldMaxQuadraticGKRRelation {
        quadratic_terms: vec![].into_boxed_slice(),
        linear_terms: vec![(1u32, a0)].into_boxed_slice(),
        constant: 0,
    };
    let mem_desc = NoFieldSpecialMemoryContributionRelation {
        address_space: CompiledAddressSpaceRelationStrict::Constant(0),
        address: CompiledAddressStrict::Constant(0),
        timestamp: CompiledMemoryTimestamp::Zero,
        value: RamWordRepresentation::Zero,
        timestamp_offset: 0,
    };
    let scl = NoFieldSingleColumnLookupRelation {
        input: lin.clone(),
        lookup_set_index: 0,
    };
    let vl = NoFieldVectorLookupRelation {
        columns: vec![lin.clone()].into_boxed_slice(),
        lookup_set_index: 0,
    };

    let m_base_1_1 = RelationMeta {
        outputs: 1,
        num_challenges: 1,
        out_domain: Domain::Base,
    };
    let m_base_0_1 = RelationMeta {
        outputs: 0,
        num_challenges: 1,
        out_domain: Domain::Base,
    };
    let m_ext_1_1 = RelationMeta {
        outputs: 1,
        num_challenges: 1,
        out_domain: Domain::Ext,
    };
    let m_ext_2_2 = RelationMeta {
        outputs: 2,
        num_challenges: 2,
        out_domain: Domain::Ext,
    };

    vec![
        // --- class (1, 1, Base) ---
        (
            R::LinearBaseFieldRelation {
                input: lin.clone(),
                output: out0,
            },
            m_base_1_1,
        ),
        (
            R::MaxQuadratic {
                input: mq.clone(),
                expression: E::Constant(0),
                output: out0,
            },
            m_base_1_1,
        ),
        (
            R::CopyInBaseField {
                input: a0,
                output: out0,
            },
            m_base_1_1,
        ),
        (
            R::MaterializeSingleLookupInput {
                input: scl.clone(),
                output: out0,
                range_check_width: 16,
            },
            m_base_1_1,
        ),
        // --- class (0, 1, Base) ---
        (
            R::EnforceSingleMaxQuadraticConstraint {
                input: mq.clone(),
                expression: E::Constant(0),
            },
            m_base_0_1,
        ),
        (
            R::EnforceConstraintsMaxQuadratic {
                input: NoFieldMaxQuadraticConstraintsGKRRelation {
                    quadratic_terms: vec![].into_boxed_slice(),
                    linear_terms: vec![].into_boxed_slice(),
                    constants: vec![].into_boxed_slice(),
                },
            },
            m_base_0_1,
        ),
        // --- class (1, 1, Ext) ---
        (
            R::CopyInExtensionField {
                input: a0,
                output: out0,
            },
            m_ext_1_1,
        ),
        (
            R::InitialGrandProductFromCaches {
                input: [a0, a1],
                output: out0,
            },
            m_ext_1_1,
        ),
        (
            R::InitialGrandProductWithoutCaches {
                input: [mem_desc.clone(), mem_desc.clone()],
                output: out0,
            },
            m_ext_1_1,
        ),
        (
            R::UnbalancedGrandProductWithCache {
                scalar: a0,
                input: a1,
                output: out0,
            },
            m_ext_1_1,
        ),
        // MaterializeGrandProductTermExpression: panicking variant — still covered by metadata
        (
            R::MaterializeGrandProductTermExpression {
                input: mem_desc.clone(),
                output: out0,
            },
            m_ext_1_1,
        ),
        (
            R::TrivialProduct {
                input: [a0, a1],
                output: out0,
            },
            m_ext_1_1,
        ),
        (
            R::MaskIntoIdentityProduct {
                input: a0,
                mask: a1,
                output: out0,
            },
            m_ext_1_1,
        ),
        (
            R::MaterializedVectorLookupInput {
                input: vl.clone(),
                output: out0,
            },
            m_ext_1_1,
        ),
        (
            R::InitsOrTeardownsInitialPair {
                timestamp_and_value: InitsOrTeardownsTimestampAndValue::Init,
                setup: [a0, a1],
                output: out0,
                set_idxes: [0, 1],
            },
            m_ext_1_1,
        ),
        // --- class (2, 2, Ext) ---
        (
            R::LookupWithCachedDensAndSetup {
                input: [a0, a1],
                setup: [a0, a1],
                output: [out0, out1],
            },
            m_ext_2_2,
        ),
        (
            R::LookupWithDensAndSetupExpressions {
                input: (a0, vl.clone()),
                setup: (a0, vec![a1].into_boxed_slice()),
                output: [out0, out1],
            },
            m_ext_2_2,
        ),
        (
            R::LookupWithDensAndCachedSetup {
                input: (a0, vl.clone()),
                setup: (a0, a1),
                output: [out0, out1],
            },
            m_ext_2_2,
        ),
        (
            R::LookupPairFromBaseInputs {
                input: [scl.clone(), scl.clone()],
                output: [out0, out1],
                range_check_width: 16,
            },
            m_ext_2_2,
        ),
        (
            R::LookupPairFromMaterializedBaseInputs {
                input: [a0, a1],
                output: [out0, out1],
            },
            m_ext_2_2,
        ),
        (
            R::LookupFromMaterializedBaseInputWithSetup {
                input: a0,
                setup: [a0, a1],
                output: [out0, out1],
            },
            m_ext_2_2,
        ),
        (
            R::LookupUnbalancedPairWithMaterializedBaseInputs {
                input: [a0, a1],
                remainder: a0,
                output: [out0, out1],
            },
            m_ext_2_2,
        ),
        (
            R::LookupPairFromVectorInputs {
                input: [vl.clone(), vl.clone()],
                output: [out0, out1],
            },
            m_ext_2_2,
        ),
        (
            R::LookupPairFromMaterializedVectorInputs {
                input: [a0, a1],
                output: [out0, out1],
            },
            m_ext_2_2,
        ),
        // LookupFromVectorInputWithSetup: panicking variant — still covered by metadata
        (
            R::LookupFromVectorInputWithSetup {
                input: vl.clone(),
                setup: (a0, vec![a1].into_boxed_slice()),
                output: [out0, out1],
            },
            m_ext_2_2,
        ),
        (
            R::LookupFromMaterializedVectorInputWithSetup {
                input: a0,
                setup: [a0, a1],
                output: [out0, out1],
            },
            m_ext_2_2,
        ),
        (
            R::LookupPairFromCachedVectorInputs {
                input: [a0, a1],
                output: [out0, out1],
            },
            m_ext_2_2,
        ),
        // LookupUnbalancedPairWithVectorInputs: panicking variant — still covered by metadata
        (
            R::LookupUnbalancedPairWithVectorInputs {
                input: [a0, a1],
                remainder: vl.clone(),
                output: [out0, out1],
            },
            m_ext_2_2,
        ),
        // LookupUnbalancedPairWithMaterializedVectorInputs: panicking variant — still covered by metadata
        (
            R::LookupUnbalancedPairWithMaterializedVectorInputs {
                input: [a0, a1],
                remainder: a0,
                output: [out0, out1],
            },
            m_ext_2_2,
        ),
        (
            R::AggregateLookupRationalPair {
                input: [[a0, a1], [a0, a1]],
                output: [out0, out1],
            },
            m_ext_2_2,
        ),
    ]
}

/// One representative relation per `NoFieldGKRRelation` variant, with a stable
/// name (the variant identifier). Derived from [`metadata_fixtures`] so the
/// relation list has a single source of truth. Two-output (num/den) relations
/// write to `inner(1, 0)` and `inner(1, 1)`.
pub fn sample_relations() -> Vec<(&'static str, NoFieldGKRRelation)> {
    metadata_fixtures()
        .into_iter()
        .map(|(rel, _)| (variant_name(&rel), rel))
        .collect()
}

/// Named semantic subcases beyond one-per-variant. These exercise specific
/// memory-tuple descriptor forms, init-vs-teardown of the inits/teardowns gate,
/// and the range-check vs timestamp single-column lookup widths.
///
/// Tasks 9/13 assert these explicitly; one representative per enum discriminant
/// is not enough.
pub fn sample_relation_cases() -> Vec<(&'static str, NoFieldGKRRelation)> {
    use super::{
        CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
        InitsOrTeardownsTimestampAndValue, NoFieldGKRRelation as R,
        NoFieldSpecialMemoryContributionRelation,
    };
    use crate::definitions::gkr::{
        NoFieldLinearRelation, NoFieldSingleColumnLookupRelation, RamWordRepresentation,
    };
    use crate::definitions::{VirtualSetupPoly, REGISTER_SIZE};
    use common_constants::{NUM_TIMESTAMP_COLUMNS_FOR_RAM, TIMESTAMP_COLUMNS_NUM_BITS};

    let out0 = inner(1, 0);
    let a0 = blw(0);

    // Build a memory-tuple descriptor with a chosen address-space / address /
    // value form, embedded in `InitialGrandProductWithoutCaches` (the
    // non-panicking grand-product gate that carries the descriptor).
    let mem_relation = |desc: NoFieldSpecialMemoryContributionRelation| R::InitialGrandProductWithoutCaches {
        input: [
            desc.clone(),
            NoFieldSpecialMemoryContributionRelation {
                address_space: CompiledAddressSpaceRelationStrict::Constant(0),
                address: CompiledAddressStrict::Constant(0),
                timestamp: CompiledMemoryTimestamp::Zero,
                value: RamWordRepresentation::Zero,
                timestamp_offset: 0,
            },
        ],
        output: out0,
    };

    // --- memory-tuple descriptor forms ---
    // IsRegister: address-space contributes 0 (register) / 1 (RAM) by `1 - bit`.
    let is_register = NoFieldSpecialMemoryContributionRelation {
        address_space: CompiledAddressSpaceRelationStrict::IsRegister(0),
        address: CompiledAddressStrict::U16Space(1),
        timestamp: CompiledMemoryTimestamp::Zero,
        value: RamWordRepresentation::Zero,
        timestamp_offset: 0,
    };
    // IsRam: address-space contributes `bit`.
    let is_ram = NoFieldSpecialMemoryContributionRelation {
        address_space: CompiledAddressSpaceRelationStrict::IsRam(0),
        address: CompiledAddressStrict::U16Space(1),
        timestamp: CompiledMemoryTimestamp::Zero,
        value: RamWordRepresentation::Zero,
        timestamp_offset: 0,
    };
    // SpecialIndirectLow: the dynamic indirect low-address form.
    let special_indirect_low = NoFieldSpecialMemoryContributionRelation {
        address_space: CompiledAddressSpaceRelationStrict::Constant(0),
        address: CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base: 0,
            low_dynamic_offset: Some((1, 1)),
            low_offset: 0,
            high: 2,
        },
        timestamp: CompiledMemoryTimestamp::Zero,
        value: RamWordRepresentation::Zero,
        timestamp_offset: 0,
    };
    // U8Limbs: two-byte value-limb decomposition (`b0 + 2^8 * b1`), one byte per
    // half-register limb.
    let u8_limbs = NoFieldSpecialMemoryContributionRelation {
        address_space: CompiledAddressSpaceRelationStrict::Constant(0),
        address: CompiledAddressStrict::U16Space(0),
        timestamp: CompiledMemoryTimestamp::Normal(
            std::array::from_fn::<usize, NUM_TIMESTAMP_COLUMNS_FOR_RAM, _>(|i| i + 1),
        ),
        value: RamWordRepresentation::U8Limbs(std::array::from_fn::<
            usize,
            { REGISTER_SIZE * 2 },
            _,
        >(|i| i + 3)),
        timestamp_offset: 0,
    };

    // --- single-column lookup widths: range-check (16) vs timestamp (19). ---
    let lin = NoFieldLinearRelation {
        linear_terms: vec![(1u32, a0)].into_boxed_slice(),
        constant: 0,
    };
    let scl = |set: usize| NoFieldSingleColumnLookupRelation {
        input: lin.clone(),
        lookup_set_index: set,
    };

    vec![
        ("MemoryTuple::IsRegister", mem_relation(is_register)),
        ("MemoryTuple::IsRam", mem_relation(is_ram)),
        (
            "MemoryTuple::SpecialIndirectLow",
            mem_relation(special_indirect_low),
        ),
        ("MemoryTuple::U8Limbs", mem_relation(u8_limbs)),
        (
            "InitsOrTeardownsInitialPair::Init",
            R::InitsOrTeardownsInitialPair {
                timestamp_and_value: InitsOrTeardownsTimestampAndValue::Init,
                setup: [
                    GKRAddress::VirtualSetup(
                        VirtualSetupPoly::InitsAndTeardownsLow,
                    ),
                    GKRAddress::VirtualSetup(
                        VirtualSetupPoly::InitsAndTeardownsHigh,
                    ),
                ],
                output: out0,
                set_idxes: [0, 1],
            },
        ),
        (
            "InitsOrTeardownsInitialPair::Teardown",
            R::InitsOrTeardownsInitialPair {
                timestamp_and_value: InitsOrTeardownsTimestampAndValue::Teardown {
                    lhs_timestamp: std::array::from_fn(|i| i),
                    lhs_value: [0, 1],
                    rhs_timestamp: std::array::from_fn(|i| i + 2),
                    rhs_value: [4, 5],
                },
                setup: [
                    GKRAddress::VirtualSetup(
                        VirtualSetupPoly::InitsAndTeardownsLow,
                    ),
                    GKRAddress::VirtualSetup(
                        VirtualSetupPoly::InitsAndTeardownsHigh,
                    ),
                ],
                output: out0,
                set_idxes: [0, 1],
            },
        ),
        (
            "SingleColumnLookup::RangeCheck16",
            R::MaterializeSingleLookupInput {
                input: scl(0),
                output: out0,
                range_check_width: 16,
            },
        ),
        (
            "SingleColumnLookup::Timestamp",
            R::MaterializeSingleLookupInput {
                input: scl(1),
                output: out0,
                range_check_width: TIMESTAMP_COLUMNS_NUM_BITS,
            },
        ),
    ]
}

// ---------------------------------------------------------------------------
// Single-relation artifact (relocated `single_gate_layer` + minimal artifact).
// ---------------------------------------------------------------------------

/// Build a one-gate `GKRLayerDescription` containing exactly `rel`.
///
/// The intermediate layer is sized so that all output addresses of the relation
/// fit. Two-output (num/den) relations write to `inner(1, 0)` and `inner(1, 1)`,
/// so a fixed width of 1 would be too small. The output count is taken from
/// `relation_metadata` (exhaustive, panic-free) rather than `dump_outputs`,
/// which panics for the no-output constraint variants.
pub fn single_gate_layer(rel: NoFieldGKRRelation) -> GKRLayerDescription {
    use super::codegen_ir::relation_metadata;
    // By fixture convention, a relation with `k` outputs writes to inner(1, 0..k);
    // size the intermediate layer to hold them (minimum width 1).
    let width = (relation_metadata(&rel).outputs as usize).max(1);

    GKRLayerDescription {
        layer: 0,
        gates_with_external_connections: vec![],
        cached_relations: BTreeMap::new(),
        gates: vec![GateArtifacts {
            output_layer: 1,
            enforced_relation: rel,
        }],
        intermediate_layer_width: Some(width),
    }
}

/// Build a one-layer [`GKRCircuitArtifact`] containing exactly `rel`, via
/// [`single_gate_layer`].
pub fn single_relation_artifact(rel: NoFieldGKRRelation) -> GKRCircuitArtifact<ConcreteField> {
    let layer = single_gate_layer(rel);
    GKRCircuitArtifact {
        trace_len: 1,
        table_offsets: Vec::new(),
        total_tables_size: 0,
        offset_for_decoder_table: 0,
        has_decoder_lookup: false,
        layers: vec![layer],
        global_output_map: BTreeMap::new(),
        memory_layout: GKRMemoryLayout {
            ram_access_sets: Vec::new(),
            machine_state: None,
            delegation_state: None,
            decoder_input: None,
            indirect_access_variable_offsets: Vec::new(),
            teardown_sets: Vec::new(),
            total_width: 0,
            inits_and_teardowns_word_bits: None,
        },
        witness_layout: GKRWitnessLayout {
            multiplicities_columns_for_range_check_16: 0..0,
            multiplicities_columns_for_timestamp_range_check: 0..0,
            multiplicities_columns_for_generic_lookup: 0..0,
            total_width: 0,
        },
        scratch_space_size: 0,
        num_generic_lookups: 0,
        placement_data: BTreeMap::new(),
        generic_lookup_tables_width: 0,
        decode_table_columns_mask: Vec::new(),
        tables_ids_in_generic_lookups: false,
        degree_2_constraints: Vec::new(),
        degree_1_constraints: Vec::new(),
        structured_statements: Vec::new(),
        generic_lookups: Vec::new(),
        range_check_16_lookup_expressions: Vec::new(),
        timestamp_range_check_lookup_expressions: Vec::new(),
        variable_names: BTreeMap::new(),
        scratch_space_mapping: BTreeMap::new(),
        scratch_space_mapping_rev: BTreeMap::new(),
        aux_layout_data: GKRAuxLayoutData {
            shuffle_ram_timestamp_comparison_aux_vars: Vec::new(),
        },
        _marker: core::marker::PhantomData,
    }
}

// ---------------------------------------------------------------------------
// Golden circuit artifacts (the enforced M1 subset, spec §8).
// ---------------------------------------------------------------------------

/// The enforced Milestone-1 golden-circuit subset (spec §8). All four are
/// required:
/// - `add_sub`            — caches, multi-layer family circuit
/// - `mem_word_only`      — memory tuples
/// - `blake2_g_function`  — heavy lookups (delegation circuit)
/// - `inits_and_teardowns`— virtual setup
///
/// Remaining golden circuits are a tracked post-M1 follow-up.
pub fn golden_circuit_artifacts() -> Vec<(&'static str, GKRCircuitArtifact<ConcreteField>)> {
    vec![
        ("add_sub", build_add_sub_artifact()),
        ("mem_word_only", build_mem_word_only_artifact()),
        ("blake2_g_function", build_blake2_g_function_artifact()),
        ("inits_and_teardowns", build_inits_and_teardowns_artifact()),
    ]
}

/// `mem_word_only` golden artifact (memory tuples), WITH caches.
pub fn build_mem_word_only_artifact() -> GKRCircuitArtifact<ConcreteField> {
    use crate::cs::circuit_trait::Circuit;
    use crate::gkr_circuits::mem_word_only::{
        create_mem_word_only_special_tables,
        mem_word_only_circuit_with_preprocessed_bytecode_for_gkr, mem_word_only_table_addition_fn,
    };
    use crate::gkr_compiler::compile_unrolled_circuit_state_transition_into_gkr;

    let table_fn = |cs: &mut crate::cs::circuit_impl::BasicAssembly<ConcreteField>| {
        mem_word_only_table_addition_fn(cs);
        // ROM tables must be added here (with dummy bytecode) so that
        // offset_for_decoder_table reflects the correct total_tables_len at
        // prove time, when real ROM tables are present.
        for (table_type, table) in create_mem_word_only_special_tables::<
            ConcreteField,
            { common_constants::ROM_SECOND_WORD_BITS },
        >(&[])
        {
            cs.add_table_with_content(table_type, table);
        }
    };

    compile_unrolled_circuit_state_transition_into_gkr::<ConcreteField>(
        &table_fn,
        &|cs| mem_word_only_circuit_with_preprocessed_bytecode_for_gkr(cs),
        common_constants::ROM_WORD_SIZE,
        24,
    )
}

/// `blake2_g_function` golden artifact (heavy lookups), WITH caches.
pub fn build_blake2_g_function_artifact() -> GKRCircuitArtifact<ConcreteField> {
    use crate::gkr_circuits::delegation::blake2_g_function::{
        blake2_g_function_table_addition_fn, define_blake2_g_function_delegation_circuit,
    };
    use crate::gkr_compiler::compile_delegation_circuit_into_gkr;

    compile_delegation_circuit_into_gkr::<ConcreteField>(
        &|cs| blake2_g_function_table_addition_fn(cs),
        &|cs| {
            let _ = define_blake2_g_function_delegation_circuit(cs);
        },
        22,
    )
}

/// `inits_and_teardowns` golden artifact (virtual setup), WITH caches.
pub fn build_inits_and_teardowns_artifact() -> GKRCircuitArtifact<ConcreteField> {
    use crate::gkr_compiler::compile_inits_and_teardowns_circuit;
    compile_inits_and_teardowns_circuit::<ConcreteField, 2>(16, 24, true)
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---------------------------------------------------------------------
    // Step 1 (TDD RED): the contract the implementation must satisfy.
    // ---------------------------------------------------------------------

    #[test]
    fn add_sub_artifact_has_layers() {
        assert!(
            build_add_sub_artifact().layers.len() > 0,
            "add_sub artifact must have at least one layer"
        );
    }

    #[test]
    fn single_relation_artifact_is_one_layer() {
        // A trivial single-output base-field relation.
        let linear_rel = sample_relations()
            .into_iter()
            .find(|(name, _)| *name == "LinearBaseFieldRelation")
            .expect("LinearBaseFieldRelation must be a sample relation")
            .1;
        assert_eq!(
            single_relation_artifact(linear_rel).layers.len(),
            1,
            "single_relation_artifact must produce exactly one layer"
        );
    }

    #[test]
    fn golden_circuit_artifacts_has_exactly_the_enforced_set() {
        use std::collections::BTreeSet;
        let names: BTreeSet<&'static str> = golden_circuit_artifacts()
            .into_iter()
            .map(|(name, _)| name)
            .collect();
        let expected: BTreeSet<&'static str> =
            ["add_sub", "mem_word_only", "blake2_g_function", "inits_and_teardowns"]
                .into_iter()
                .collect();
        assert_eq!(
            names, expected,
            "golden_circuit_artifacts must contain exactly the four enforced names"
        );
    }

    #[test]
    fn single_relation_artifact_sizes_width_for_two_output_relations() {
        // A two-output (num/den) relation must size the intermediate layer to 2,
        // so both inner(1, 0) and inner(1, 1) fit (resolution #3).
        let two_output = sample_relations()
            .into_iter()
            .find(|(name, _)| *name == "LookupPairFromMaterializedBaseInputs")
            .expect("LookupPairFromMaterializedBaseInputs must be a sample relation")
            .1;
        let artifact = single_relation_artifact(two_output);
        assert_eq!(artifact.layers.len(), 1);
        assert_eq!(
            artifact.layers[0].intermediate_layer_width,
            Some(2),
            "two-output relation must size the intermediate layer to width 2"
        );
    }

    #[test]
    fn sample_relations_cover_every_variant_with_unique_names() {
        use std::collections::BTreeSet;
        let rels = sample_relations();
        // Every name is the variant identifier and they are all distinct.
        let names: BTreeSet<&'static str> = rels.iter().map(|(n, _)| *n).collect();
        assert_eq!(names.len(), rels.len(), "sample relation names must be unique");
        // Cross-check against `relation_metadata` totality: the list must include
        // one entry per variant (currently 30).
        assert_eq!(rels.len(), 30, "expected one sample relation per variant");
    }

    #[test]
    fn metadata_fixtures_match_relation_metadata() {
        use super::super::codegen_ir::relation_metadata;
        for (rel, meta) in metadata_fixtures() {
            let m = relation_metadata(&rel);
            assert_eq!(m.outputs, meta.outputs, "{:?}", rel);
            assert_eq!(m.num_challenges, meta.num_challenges, "{:?}", rel);
            assert_eq!(m.out_domain, meta.out_domain, "{:?}", rel);
        }
    }

    #[test]
    fn sample_relation_cases_contain_named_subcases() {
        use std::collections::BTreeSet;
        let names: BTreeSet<&'static str> = sample_relation_cases()
            .into_iter()
            .map(|(name, _)| name)
            .collect();
        for required in [
            "MemoryTuple::IsRegister",
            "MemoryTuple::IsRam",
            "MemoryTuple::SpecialIndirectLow",
            "MemoryTuple::U8Limbs",
            "InitsOrTeardownsInitialPair::Init",
            "InitsOrTeardownsInitialPair::Teardown",
            "SingleColumnLookup::RangeCheck16",
            "SingleColumnLookup::Timestamp",
        ] {
            assert!(
                names.contains(required),
                "sample_relation_cases must contain {required}"
            );
        }
    }
}
