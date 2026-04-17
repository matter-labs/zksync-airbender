use std::collections::BTreeMap;

use cs::definitions::GKRAddress;
use cs::gkr_compiler::{
    GKRLayerDescription, GateArtifacts, NoFieldGKRCacheRelation, NoFieldGKRRelation,
};

#[derive(Clone, Debug, Default)]
pub(crate) struct LayerNoCacheLoweringPlan {
    pub(crate) internal_helper_relations: BTreeMap<GKRAddress, NoFieldGKRCacheRelation>,
    pub(crate) lowered_gates: Vec<GateArtifacts>,
    pub(crate) lowered_gates_with_external_connections: Vec<GateArtifacts>,
}

impl LayerNoCacheLoweringPlan {
    pub(crate) fn new(layer_idx: usize, layer: &GKRLayerDescription) -> Self {
        Self::build(layer_idx, layer, lower_gate_relation)
    }

    pub(crate) fn grand_product_only(layer_idx: usize, layer: &GKRLayerDescription) -> Self {
        Self::build(layer_idx, layer, lower_gate_relation_grand_product_only)
    }

    fn build(layer_idx: usize, layer: &GKRLayerDescription, lower: LowerRelationFn) -> Self {
        let mut next_cached_offset = layer
            .cached_relations
            .keys()
            .filter_map(|address| match address {
                GKRAddress::Cached {
                    layer: cached_layer,
                    offset,
                } if *cached_layer == layer_idx => Some(*offset + 1),
                _ => None,
            })
            .max()
            .unwrap_or(0);
        let mut internal_helper_relations = BTreeMap::new();
        let lowered_gates = lower_gate_list(
            layer_idx,
            &layer.gates,
            &mut next_cached_offset,
            &mut internal_helper_relations,
            lower,
        );
        let lowered_gates_with_external_connections = lower_gate_list(
            layer_idx,
            &layer.gates_with_external_connections,
            &mut next_cached_offset,
            &mut internal_helper_relations,
            lower,
        );

        Self {
            internal_helper_relations,
            lowered_gates,
            lowered_gates_with_external_connections,
        }
    }
}

type LowerRelationFn = fn(
    usize,
    &NoFieldGKRRelation,
    &mut usize,
    &mut BTreeMap<GKRAddress, NoFieldGKRCacheRelation>,
) -> NoFieldGKRRelation;

fn lower_gate_list(
    layer_idx: usize,
    gates: &[GateArtifacts],
    next_cached_offset: &mut usize,
    internal_helper_relations: &mut BTreeMap<GKRAddress, NoFieldGKRCacheRelation>,
    lower: LowerRelationFn,
) -> Vec<GateArtifacts> {
    gates
        .iter()
        .map(|gate| GateArtifacts {
            output_layer: gate.output_layer,
            enforced_relation: lower(
                layer_idx,
                &gate.enforced_relation,
                next_cached_offset,
                internal_helper_relations,
            ),
        })
        .collect()
}

fn next_internal_helper_address(
    layer_idx: usize,
    next_cached_offset: &mut usize,
    relation: NoFieldGKRCacheRelation,
    internal_helper_relations: &mut BTreeMap<GKRAddress, NoFieldGKRCacheRelation>,
) -> GKRAddress {
    let address = GKRAddress::Cached {
        layer: layer_idx,
        offset: *next_cached_offset,
    };
    *next_cached_offset += 1;
    let previous = internal_helper_relations.insert(address, relation);
    assert!(
        previous.is_none(),
        "fresh internal helper address must be unique"
    );
    address
}

fn lower_gate_relation(
    layer_idx: usize,
    relation: &NoFieldGKRRelation,
    next_cached_offset: &mut usize,
    internal_helper_relations: &mut BTreeMap<GKRAddress, NoFieldGKRCacheRelation>,
) -> NoFieldGKRRelation {
    match relation {
        NoFieldGKRRelation::InitialGrandProductWithoutCaches { input, output } => {
            let lowered_inputs = input.clone().map(|memory_term| {
                next_internal_helper_address(
                    layer_idx,
                    next_cached_offset,
                    NoFieldGKRCacheRelation::MemoryTuple(memory_term),
                    internal_helper_relations,
                )
            });
            NoFieldGKRRelation::InitialGrandProductFromCaches {
                input: lowered_inputs,
                output: *output,
            }
        }
        NoFieldGKRRelation::MaterializeGrandProductTermExpression { input, output } => {
            let lowered_input = next_internal_helper_address(
                layer_idx,
                next_cached_offset,
                NoFieldGKRCacheRelation::MemoryTuple(input.clone()),
                internal_helper_relations,
            );
            NoFieldGKRRelation::Copy {
                input: lowered_input,
                output: *output,
            }
        }
        NoFieldGKRRelation::LookupPairFromBaseInputs {
            input,
            output,
            range_check_width,
        } => {
            let lowered_inputs = input.clone().map(|lookup_input| {
                next_internal_helper_address(
                    layer_idx,
                    next_cached_offset,
                    NoFieldGKRCacheRelation::SingleColumnLookup {
                        relation: lookup_input,
                        range_check_width: *range_check_width as usize,
                    },
                    internal_helper_relations,
                )
            });
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs {
                input: lowered_inputs,
                output: *output,
            }
        }
        NoFieldGKRRelation::LookupWithDensAndSetupExpressions {
            input,
            setup,
            output,
        } => {
            let lowered_input = next_internal_helper_address(
                layer_idx,
                next_cached_offset,
                NoFieldGKRCacheRelation::VectorizedLookup(input.1.clone()),
                internal_helper_relations,
            );
            let lowered_setup = next_internal_helper_address(
                layer_idx,
                next_cached_offset,
                NoFieldGKRCacheRelation::VectorizedLookupSetup(setup.1.clone()),
                internal_helper_relations,
            );
            NoFieldGKRRelation::LookupWithCachedDensAndSetup {
                input: [input.0, lowered_input],
                setup: [setup.0, lowered_setup],
                output: *output,
            }
        }
        NoFieldGKRRelation::LookupPairFromVectorInputs { input, output } => {
            let lowered_inputs = input.clone().map(|lookup_input| {
                next_internal_helper_address(
                    layer_idx,
                    next_cached_offset,
                    NoFieldGKRCacheRelation::VectorizedLookup(lookup_input),
                    internal_helper_relations,
                )
            });
            NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs {
                input: lowered_inputs,
                output: *output,
            }
        }
        NoFieldGKRRelation::LookupFromVectorInputWithSetup {
            input,
            setup,
            output,
        } => {
            let lowered_input = next_internal_helper_address(
                layer_idx,
                next_cached_offset,
                NoFieldGKRCacheRelation::VectorizedLookup(input.clone()),
                internal_helper_relations,
            );
            let lowered_setup = next_internal_helper_address(
                layer_idx,
                next_cached_offset,
                NoFieldGKRCacheRelation::VectorizedLookupSetup(setup.1.clone()),
                internal_helper_relations,
            );
            NoFieldGKRRelation::LookupFromMaterializedVectorInputWithSetup {
                input: lowered_input,
                setup: [setup.0, lowered_setup],
                output: *output,
            }
        }
        NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs {
            input,
            remainder,
            output,
        } => {
            let lowered_remainder = next_internal_helper_address(
                layer_idx,
                next_cached_offset,
                NoFieldGKRCacheRelation::VectorizedLookup(remainder.clone()),
                internal_helper_relations,
            );
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs {
                input: *input,
                remainder: lowered_remainder,
                output: *output,
            }
        }
        _ => relation.clone(),
    }
}

fn lower_gate_relation_grand_product_only(
    layer_idx: usize,
    relation: &NoFieldGKRRelation,
    next_cached_offset: &mut usize,
    internal_helper_relations: &mut BTreeMap<GKRAddress, NoFieldGKRCacheRelation>,
) -> NoFieldGKRRelation {
    match relation {
        NoFieldGKRRelation::InitialGrandProductWithoutCaches { .. }
        | NoFieldGKRRelation::MaterializeGrandProductTermExpression { .. } => lower_gate_relation(
            layer_idx,
            relation,
            next_cached_offset,
            internal_helper_relations,
        ),
        _ => relation.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cs::definitions::{gkr::NoFieldLinearRelation, GKRAddress, VirtualSetupPoly};
    use cs::gkr_compiler::{
        CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
        InitsOrTeardownsTimestampAndValue, NoFieldMaxQuadraticGKRRelation,
        NoFieldSpecialMemoryContributionRelation,
    };

    fn linear(input: GKRAddress) -> NoFieldLinearRelation {
        NoFieldLinearRelation::from_single_input(input)
    }

    fn base_lookup(
        set_idx: usize,
        input: GKRAddress,
    ) -> cs::definitions::gkr::NoFieldSingleColumnLookupRelation {
        cs::definitions::gkr::NoFieldSingleColumnLookupRelation {
            input: linear(input),
            lookup_set_index: set_idx,
        }
    }

    fn vector_lookup(
        set_idx: usize,
        inputs: &[GKRAddress],
    ) -> cs::definitions::gkr::NoFieldVectorLookupRelation {
        cs::definitions::gkr::NoFieldVectorLookupRelation {
            columns: inputs
                .iter()
                .copied()
                .map(linear)
                .collect::<Vec<_>>()
                .into_boxed_slice(),
            lookup_set_index: set_idx,
        }
    }

    fn memory_term(offset: usize) -> NoFieldSpecialMemoryContributionRelation {
        NoFieldSpecialMemoryContributionRelation {
            address_space: CompiledAddressSpaceRelationStrict::Constant(0),
            address: CompiledAddressStrict::U16Space(offset),
            timestamp: CompiledMemoryTimestamp::Zero,
            value: cs::definitions::gkr::RamWordRepresentation::Zero,
            timestamp_offset: 0,
        }
    }

    fn layer_with_gate(relation: NoFieldGKRRelation) -> GKRLayerDescription {
        GKRLayerDescription {
            layer: 0,
            gates_with_external_connections: Vec::new(),
            cached_relations: BTreeMap::from([(
                GKRAddress::Cached {
                    layer: 0,
                    offset: 3,
                },
                NoFieldGKRCacheRelation::VectorizedLookup(vector_lookup(
                    9,
                    &[GKRAddress::BaseLayerMemory(99)],
                )),
            )]),
            gates: vec![GateArtifacts {
                output_layer: 1,
                enforced_relation: relation,
            }],
        }
    }

    #[test]
    fn lowers_initial_grand_product_without_caches_into_memory_helpers_and_product() {
        let output = GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        };
        let plan = LayerNoCacheLoweringPlan::new(
            0,
            &layer_with_gate(NoFieldGKRRelation::InitialGrandProductWithoutCaches {
                input: [memory_term(0), memory_term(1)],
                output,
            }),
        );

        assert_eq!(plan.internal_helper_relations.len(), 2);
        assert_eq!(
            plan.internal_helper_relations[&GKRAddress::Cached {
                layer: 0,
                offset: 4
            }],
            NoFieldGKRCacheRelation::MemoryTuple(memory_term(0))
        );
        assert_eq!(
            plan.internal_helper_relations[&GKRAddress::Cached {
                layer: 0,
                offset: 5
            }],
            NoFieldGKRCacheRelation::MemoryTuple(memory_term(1))
        );
        assert_eq!(
            plan.lowered_gates[0].enforced_relation,
            NoFieldGKRRelation::InitialGrandProductFromCaches {
                input: [
                    GKRAddress::Cached {
                        layer: 0,
                        offset: 4
                    },
                    GKRAddress::Cached {
                        layer: 0,
                        offset: 5
                    },
                ],
                output,
            }
        );
    }

    #[test]
    fn lowers_materialize_memory_term_into_memory_helper_and_extension_copy() {
        let output = GKRAddress::InnerLayer {
            layer: 1,
            offset: 1,
        };
        let plan = LayerNoCacheLoweringPlan::new(
            0,
            &layer_with_gate(NoFieldGKRRelation::MaterializeGrandProductTermExpression {
                input: memory_term(2),
                output,
            }),
        );

        assert_eq!(plan.internal_helper_relations.len(), 1);
        assert_eq!(
            plan.lowered_gates[0].enforced_relation,
            NoFieldGKRRelation::Copy {
                input: GKRAddress::Cached {
                    layer: 0,
                    offset: 4
                },
                output,
            }
        );
    }

    #[test]
    fn lowers_lookup_pair_from_base_inputs_into_single_column_helpers() {
        let output = [
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 2,
            },
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 3,
            },
        ];
        let plan = LayerNoCacheLoweringPlan::new(
            0,
            &layer_with_gate(NoFieldGKRRelation::LookupPairFromBaseInputs {
                input: [
                    base_lookup(0, GKRAddress::BaseLayerMemory(0)),
                    base_lookup(1, GKRAddress::BaseLayerWitness(0)),
                ],
                output,
                range_check_width: 16,
            }),
        );

        assert_eq!(plan.internal_helper_relations.len(), 2);
        assert!(matches!(
            plan.internal_helper_relations[&GKRAddress::Cached {
                layer: 0,
                offset: 4
            }],
            NoFieldGKRCacheRelation::SingleColumnLookup {
                range_check_width: 16,
                ..
            }
        ));
        assert_eq!(
            plan.lowered_gates[0].enforced_relation,
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs {
                input: [
                    GKRAddress::Cached {
                        layer: 0,
                        offset: 4
                    },
                    GKRAddress::Cached {
                        layer: 0,
                        offset: 5
                    },
                ],
                output,
            }
        );
    }

    #[test]
    fn lowers_lookup_with_dens_and_setup_expressions_into_cached_lookup() {
        let output = [
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 4,
            },
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 5,
            },
        ];
        let plan = LayerNoCacheLoweringPlan::new(
            0,
            &layer_with_gate(NoFieldGKRRelation::LookupWithDensAndSetupExpressions {
                input: (
                    GKRAddress::BaseLayerMemory(7),
                    vector_lookup(
                        2,
                        &[
                            GKRAddress::BaseLayerMemory(1),
                            GKRAddress::BaseLayerMemory(2),
                        ],
                    ),
                ),
                setup: (
                    GKRAddress::BaseLayerWitness(3),
                    vec![GKRAddress::Setup(0), GKRAddress::Setup(0)].into_boxed_slice(),
                ),
                output,
            }),
        );

        assert_eq!(plan.internal_helper_relations.len(), 2);
        assert!(matches!(
            plan.internal_helper_relations[&GKRAddress::Cached {
                layer: 0,
                offset: 4
            }],
            NoFieldGKRCacheRelation::VectorizedLookup(_)
        ));
        assert!(matches!(
            plan.internal_helper_relations[&GKRAddress::Cached {
                layer: 0,
                offset: 5
            }],
            NoFieldGKRCacheRelation::VectorizedLookupSetup(_)
        ));
        assert_eq!(
            plan.lowered_gates[0].enforced_relation,
            NoFieldGKRRelation::LookupWithCachedDensAndSetup {
                input: [
                    GKRAddress::BaseLayerMemory(7),
                    GKRAddress::Cached {
                        layer: 0,
                        offset: 4
                    },
                ],
                setup: [
                    GKRAddress::BaseLayerWitness(3),
                    GKRAddress::Cached {
                        layer: 0,
                        offset: 5
                    },
                ],
                output,
            }
        );
    }

    #[test]
    fn lowers_lookup_pair_from_vector_inputs_into_vector_helpers() {
        let output = [
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 6,
            },
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 7,
            },
        ];
        let plan = LayerNoCacheLoweringPlan::new(
            0,
            &layer_with_gate(NoFieldGKRRelation::LookupPairFromVectorInputs {
                input: [
                    vector_lookup(3, &[GKRAddress::BaseLayerMemory(1)]),
                    vector_lookup(4, &[GKRAddress::BaseLayerMemory(2)]),
                ],
                output,
            }),
        );

        assert_eq!(
            plan.lowered_gates[0].enforced_relation,
            NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs {
                input: [
                    GKRAddress::Cached {
                        layer: 0,
                        offset: 4
                    },
                    GKRAddress::Cached {
                        layer: 0,
                        offset: 5
                    },
                ],
                output,
            }
        );
    }

    #[test]
    fn lowers_lookup_from_vector_input_with_setup_into_vector_and_setup_helpers() {
        let output = [
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 8,
            },
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 9,
            },
        ];
        let plan = LayerNoCacheLoweringPlan::new(
            0,
            &layer_with_gate(NoFieldGKRRelation::LookupFromVectorInputWithSetup {
                input: vector_lookup(5, &[GKRAddress::BaseLayerMemory(3)]),
                setup: (
                    GKRAddress::BaseLayerMemory(4),
                    vec![GKRAddress::Setup(0), GKRAddress::Setup(1)].into_boxed_slice(),
                ),
                output,
            }),
        );

        assert_eq!(
            plan.lowered_gates[0].enforced_relation,
            NoFieldGKRRelation::LookupFromMaterializedVectorInputWithSetup {
                input: GKRAddress::Cached {
                    layer: 0,
                    offset: 4
                },
                setup: [
                    GKRAddress::BaseLayerMemory(4),
                    GKRAddress::Cached {
                        layer: 0,
                        offset: 5
                    },
                ],
                output,
            }
        );
    }

    #[test]
    fn lowers_unbalanced_vector_lookup_into_remainder_helper() {
        let output = [
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 10,
            },
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 11,
            },
        ];
        let plan = LayerNoCacheLoweringPlan::new(
            0,
            &layer_with_gate(NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs {
                input: [
                    GKRAddress::InnerLayer {
                        layer: 0,
                        offset: 0,
                    },
                    GKRAddress::InnerLayer {
                        layer: 0,
                        offset: 1,
                    },
                ],
                remainder: vector_lookup(6, &[GKRAddress::BaseLayerMemory(5)]),
                output,
            }),
        );

        assert_eq!(plan.internal_helper_relations.len(), 1);
        assert_eq!(
            plan.lowered_gates[0].enforced_relation,
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs {
                input: [
                    GKRAddress::InnerLayer {
                        layer: 0,
                        offset: 0
                    },
                    GKRAddress::InnerLayer {
                        layer: 0,
                        offset: 1
                    },
                ],
                remainder: GKRAddress::Cached {
                    layer: 0,
                    offset: 4
                },
                output,
            }
        );
    }

    #[test]
    fn leaves_single_constraint_and_inits_teardowns_explicit() {
        let constraint = NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint {
            input: NoFieldMaxQuadraticGKRRelation {
                quadratic_terms: vec![(
                    GKRAddress::BaseLayerMemory(0),
                    vec![(2, GKRAddress::BaseLayerMemory(1))].into_boxed_slice(),
                )]
                .into_boxed_slice(),
                linear_terms: vec![(3, GKRAddress::BaseLayerMemory(2))].into_boxed_slice(),
                constant: 5,
            },
        };
        let constraint_plan =
            LayerNoCacheLoweringPlan::new(0, &layer_with_gate(constraint.clone()));
        assert!(constraint_plan.internal_helper_relations.is_empty());
        assert_eq!(
            constraint_plan.lowered_gates[0].enforced_relation,
            constraint
        );

        let unsupported = NoFieldGKRRelation::InitsOrTeardownsInitialPair {
            timestamp_and_value: InitsOrTeardownsTimestampAndValue::Init,
            setup: [
                GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
                GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
            ],
            output: GKRAddress::InnerLayer {
                layer: 1,
                offset: 12,
            },
            set_idxes: [0, 1],
        };
        let unsupported_plan =
            LayerNoCacheLoweringPlan::new(0, &layer_with_gate(unsupported.clone()));
        assert!(unsupported_plan.internal_helper_relations.is_empty());
        assert_eq!(
            unsupported_plan.lowered_gates[0].enforced_relation,
            unsupported
        );
    }
}
