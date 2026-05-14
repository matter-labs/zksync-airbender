use super::super::*;
use crate::primitives::field::{BF, E4};

use std::collections::BTreeMap;

use super::{build_main_layer_kernel_blueprints, sample_ext, sample_external_challenges};
use crate::upstream::{
    high_bits_offset_for_inits_and_teardowns, Field, GKRAddress, GKRLayerDescription,
    GateArtifacts, InitsOrTeardownsTimestampAndValue, NoFieldGKRRelation,
    NoFieldMaxQuadraticGKRRelation, VirtualSetupPoly,
};

#[test]
fn single_max_quadratic_constraint_uses_direct_metadata_and_no_outputs() {
    let storage = crate::prover::gkr::GpuGKRStorage::<BF, E4> {
        layers: vec![Default::default()],
        layout: None,
    };
    let constraint_input = NoFieldMaxQuadraticGKRRelation {
        quadratic_terms: vec![
            (
                GKRAddress::BaseLayerMemory(0),
                vec![
                    (2u32, GKRAddress::BaseLayerWitness(1)),
                    (3u32, GKRAddress::BaseLayerMemory(0)),
                ]
                .into_boxed_slice(),
            ),
            (
                GKRAddress::BaseLayerWitness(2),
                vec![(5u32, GKRAddress::BaseLayerWitness(1))].into_boxed_slice(),
            ),
        ]
        .into_boxed_slice(),
        linear_terms: vec![
            (7u32, GKRAddress::BaseLayerMemory(3)),
            (11u32, GKRAddress::BaseLayerWitness(2)),
        ]
        .into_boxed_slice(),
        constant: 13,
    };
    let layer = GKRLayerDescription {
        layer: 0,
        gates_with_external_connections: Vec::new(),
        cached_relations: BTreeMap::new(),
        intermediate_layer_width: None,
        gates: vec![GateArtifacts {
            output_layer: 1,
            enforced_relation: NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint {
                input: constraint_input.clone(),
            },
        }],
    };

    let external_challenges = sample_external_challenges(40);
    let blueprints = build_main_layer_kernel_blueprints(
        &layer,
        0,
        &storage,
        &external_challenges,
        &[],
        0,
        sample_ext(10),
        sample_ext(20),
        sample_ext(20),
        2,
        2,
    );
    assert_eq!(blueprints.len(), 1);
    let blueprint = &blueprints[0];
    let (expected_inputs, expected_metadata) =
        build_single_max_quadratic_constraint_inputs_and_metadata::<E4>(&constraint_input);

    assert_eq!(
        blueprint.kind,
        GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic
    );
    assert_eq!(blueprint.batch_challenges, vec![E4::ONE]);
    assert_eq!(blueprint.inputs, expected_inputs);
    assert!(blueprint.inputs.outputs_in_base.is_empty());
    assert!(blueprint.inputs.outputs_in_extension.is_empty());

    let metadata = blueprint
        .constraint_metadata_source
        .as_ref()
        .expect("constraint metadata must be present");
    let metadata = match metadata {
        super::GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata) => metadata,
        super::GpuGKRMainLayerConstraintMetadataSource::Deferred(..) => {
            panic!("single max quadratic constraint must use immediate metadata")
        }
    };
    assert_eq!(metadata, &expected_metadata);
}

#[test]
fn max_quadratic_relation_dispatches_with_base_output() {
    let storage = crate::prover::gkr::GpuGKRStorage::<BF, E4> {
        layers: vec![Default::default()],
        layout: None,
    };
    let constraint_input = NoFieldMaxQuadraticGKRRelation {
        quadratic_terms: vec![
            (
                GKRAddress::BaseLayerMemory(0),
                vec![
                    (2u32, GKRAddress::BaseLayerWitness(1)),
                    (3u32, GKRAddress::BaseLayerMemory(0)),
                ]
                .into_boxed_slice(),
            ),
            (
                GKRAddress::BaseLayerWitness(2),
                vec![(5u32, GKRAddress::BaseLayerWitness(1))].into_boxed_slice(),
            ),
        ]
        .into_boxed_slice(),
        linear_terms: vec![
            (7u32, GKRAddress::BaseLayerMemory(3)),
            (11u32, GKRAddress::BaseLayerWitness(2)),
        ]
        .into_boxed_slice(),
        constant: 13,
    };
    let output_address = GKRAddress::ScratchSpace(0);
    let layer = GKRLayerDescription {
        layer: 0,
        gates_with_external_connections: Vec::new(),
        cached_relations: BTreeMap::new(),
        intermediate_layer_width: None,
        gates: vec![GateArtifacts {
            output_layer: 1,
            enforced_relation: NoFieldGKRRelation::MaxQuadratic {
                input: constraint_input.clone(),
                output: output_address,
            },
        }],
    };

    let external_challenges = sample_external_challenges(40);
    let blueprints = build_main_layer_kernel_blueprints(
        &layer,
        0,
        &storage,
        &external_challenges,
        &[],
        0,
        sample_ext(10),
        sample_ext(20),
        sample_ext(20),
        2,
        2,
    );
    assert_eq!(blueprints.len(), 1);
    let blueprint = &blueprints[0];
    let (expected_inputs, expected_metadata) =
        build_max_quadratic_relation_inputs_and_metadata::<E4>(&constraint_input, output_address);

    assert_eq!(
        blueprint.kind,
        GpuGKRMainLayerKernelKind::MaxQuadraticBaseOutput
    );
    assert_eq!(blueprint.batch_challenges, vec![E4::ONE]);
    assert_eq!(blueprint.inputs, expected_inputs);
    assert_eq!(blueprint.inputs.outputs_in_base, vec![output_address]);
    assert!(blueprint.inputs.outputs_in_extension.is_empty());

    let metadata = blueprint
        .constraint_metadata_source
        .as_ref()
        .expect("constraint metadata must be present");
    let metadata = match metadata {
        super::GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata) => metadata,
        super::GpuGKRMainLayerConstraintMetadataSource::Deferred(..) => {
            panic!("max quadratic relation must use immediate metadata")
        }
    };
    assert_eq!(metadata, &expected_metadata);
    // The MaxQuadraticBaseOutput kernel reuses the constraint helper
    // unchanged, only attaching the output to outputs_in_base — the
    // metadata's linear and quadratic terms match the constraint-only
    // build exactly.
    let (_, base_metadata) =
        build_single_max_quadratic_constraint_inputs_and_metadata::<E4>(&constraint_input);
    assert_eq!(metadata.linear_terms, base_metadata.linear_terms);
    assert_eq!(metadata.quadratic_terms, base_metadata.quadratic_terms);
}

#[test]
fn main_layer_blueprints_for_inits_and_teardowns_initial_pair_use_canonical_top_bits() {
    let storage = crate::prover::gkr::GpuGKRStorage::<BF, E4> {
        layers: vec![Default::default()],
        layout: None,
    };
    let init_output = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };
    let teardown_output = GKRAddress::InnerLayer {
        layer: 1,
        offset: 1,
    };
    let layer = GKRLayerDescription {
        layer: 0,
        gates_with_external_connections: Vec::new(),
        cached_relations: BTreeMap::new(),
        intermediate_layer_width: None,
        gates: vec![
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::InitsOrTeardownsInitialPair {
                    timestamp_and_value: InitsOrTeardownsTimestampAndValue::Init,
                    setup: [
                        GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
                        GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
                    ],
                    output: init_output,
                    set_idxes: [1, 4],
                },
            },
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::InitsOrTeardownsInitialPair {
                    timestamp_and_value: InitsOrTeardownsTimestampAndValue::Teardown {
                        lhs_timestamp: [0, 1],
                        lhs_value: [2, 3],
                        rhs_timestamp: [1, 0],
                        rhs_value: [3, 2],
                    },
                    setup: [
                        GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
                        GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
                    ],
                    output: teardown_output,
                    set_idxes: [0, 5],
                },
            },
        ],
    };
    let external_challenges = sample_external_challenges(60);
    let canonical_top_bits = canonical_inits_and_teardowns_top_bits(6);
    let high_bits_shift = high_bits_offset_for_inits_and_teardowns::<2>(1 << 16);

    let dynamic_blueprints = build_main_layer_kernel_blueprints(
        &layer,
        0,
        &storage,
        &external_challenges,
        &canonical_top_bits,
        high_bits_shift,
        sample_ext(10),
        sample_ext(15),
        sample_ext(20),
        4,
        0,
    );
    let static_blueprints = build_main_layer_kernel_blueprints_static(
        &layer,
        0,
        &|addr| storage.layers[0].base_field_inputs.contains_key(addr),
        &external_challenges,
        &canonical_top_bits,
        high_bits_shift,
        4,
        0,
    );

    assert_eq!(dynamic_blueprints.len(), 2);
    assert_eq!(static_blueprints.len(), 2);

    let expected_specs = [
        (
            InitsOrTeardownsTimestampAndValue::Init,
            init_output,
            [canonical_top_bits[1], canonical_top_bits[4]],
        ),
        (
            InitsOrTeardownsTimestampAndValue::Teardown {
                lhs_timestamp: [0, 1],
                lhs_value: [2, 3],
                rhs_timestamp: [1, 0],
                rhs_value: [3, 2],
            },
            teardown_output,
            [canonical_top_bits[0], canonical_top_bits[5]],
        ),
    ];

    for ((dynamic_blueprint, static_blueprint), (timestamp_and_value, output, top_bits)) in
        dynamic_blueprints
            .iter()
            .zip(static_blueprints.iter())
            .zip(expected_specs.iter())
    {
        let (expected_inputs, expected_metadata) =
            build_inits_and_teardowns_initial_pair_inputs_and_metadata(
                timestamp_and_value,
                [
                    GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
                    GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
                ],
                *output,
                *top_bits,
                high_bits_shift,
                &external_challenges,
            );

        for blueprint in [dynamic_blueprint, static_blueprint] {
            assert_eq!(
                blueprint.kind,
                GpuGKRMainLayerKernelKind::InitsAndTeardownsInitialPair
            );
            assert_eq!(blueprint.inputs, expected_inputs);
            let metadata = blueprint
                .constraint_metadata_source
                .as_ref()
                .expect("init/teardown metadata must be present");
            let metadata = match metadata {
                super::GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata) => metadata,
                super::GpuGKRMainLayerConstraintMetadataSource::Deferred(..) => {
                    panic!("init/teardown metadata must be materialized immediately")
                }
            };
            assert_eq!(metadata, &expected_metadata);
        }
    }

    assert_eq!(dynamic_blueprints[0].batch_challenges, vec![E4::ONE]);
    assert_eq!(dynamic_blueprints[1].batch_challenges, vec![sample_ext(10)]);
    assert!(static_blueprints[0].batch_challenges.is_empty());
    assert!(static_blueprints[1].batch_challenges.is_empty());
}

#[test]
fn compute_main_layer_orphan_output_addresses_picks_unconsumed_outputs() {
    // Three layers; layer 0 produces an InnerLayer{1,0} output that
    // layer-1's kernels do not read — exactly the MaxQuadratic-with-
    // higher-layer-consumer case the GPU port now handles. Bottom
    // layer (layer_idx == 0) is always empty (no layer below). Top
    // layer's slot lists orphans of the layer below it (here:
    // layer-1 outputs that layer 2 doesn't consume).
    let layer0_inputs = vec![GKRAddress::BaseLayerWitness(0)];
    let layer1_inputs = vec![GKRAddress::BaseLayerWitness(1)];
    let layer2_inputs = vec![
        GKRAddress::ScratchSpace(7),
        GKRAddress::InnerLayer {
            layer: 2,
            offset: 0,
        },
    ];
    let inputs_per_layer = vec![layer0_inputs, layer1_inputs, layer2_inputs];

    let layer0_outputs = vec![GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    }];
    let layer1_outputs = vec![
        GKRAddress::ScratchSpace(7),
        GKRAddress::InnerLayer {
            layer: 2,
            offset: 0,
        },
    ];
    let layer2_outputs = vec![GKRAddress::InnerLayer {
        layer: 3,
        offset: 0,
    }];
    let outputs_per_layer = vec![layer0_outputs, layer1_outputs, layer2_outputs];

    let orphans = super::compute_main_layer_orphan_output_addresses_per_layer::<E4>(
        &inputs_per_layer,
        &outputs_per_layer,
    );

    // Bottom layer (layer 0): nothing below it — always empty.
    assert!(orphans[0].is_empty());
    // Layer 1's orphan list = layer-0 outputs not consumed by layer 1.
    // layer 0's output InnerLayer{1,0} is NOT in layer 1's inputs
    // (which is BaseLayerWitness(1)) — so it IS an orphan emitted at
    // scheduler 1.
    assert_eq!(
        orphans[1],
        vec![GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        }],
    );
    // Layer 2's orphan list = layer-1 outputs not consumed by layer 2.
    // both ScratchSpace(7) and InnerLayer{2,0} ARE in layer 2's
    // inputs, so neither is an orphan.
    assert!(orphans[2].is_empty());
}

#[test]
fn compute_main_layer_orphan_output_addresses_handles_empty() {
    let orphans = super::compute_main_layer_orphan_output_addresses_per_layer::<E4>(&[], &[]);
    assert!(orphans.is_empty());
}
