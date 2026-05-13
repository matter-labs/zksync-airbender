use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExpectedMainLayerConstraintMetadata<E> {
    pub(crate) quadratic_terms:
        Vec<crate::prover::gkr::backward::GpuGKRMainLayerConstraintQuadraticTerm<E>>,
    pub(crate) linear_terms:
        Vec<crate::prover::gkr::backward::GpuGKRMainLayerConstraintLinearTerm<E>>,
    pub(crate) constant_offset: E,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExpectedMainLayerKernelSpec<E> {
    pub(crate) kind: GpuGKRMainLayerKernelKind,
    pub(crate) inputs: GKRInputs,
    pub(crate) batch_challenges: Vec<E>,
    pub(crate) auxiliary_challenge: E,
    pub(crate) constraint_metadata: Option<ExpectedMainLayerConstraintMetadata<E>>,
}

fn remap_expected_constraint_input(
    mapping: &mut BTreeMap<GKRAddress, usize>,
    inputs: &mut Vec<GKRAddress>,
    address: GKRAddress,
) -> usize {
    if let Some(idx) = mapping.get(&address).copied() {
        idx
    } else {
        let idx = mapping.len();
        mapping.insert(address, idx);
        inputs.push(address);
        idx
    }
}

fn expected_single_max_quadratic_constraint_inputs_and_metadata<E: Field + FieldExtension<BF>>(
    relation: &NoFieldMaxQuadraticGKRRelation,
) -> (GKRInputs, ExpectedMainLayerConstraintMetadata<E>) {
    let mut mapping = BTreeMap::new();
    let mut inputs = Vec::new();
    let mut quadratic_terms = Vec::new();
    let mut linear_terms = Vec::new();

    for (lhs, rhs_terms) in relation.quadratic_terms.iter() {
        let lhs_idx = remap_expected_constraint_input(&mut mapping, &mut inputs, *lhs);
        for (coeff, rhs) in rhs_terms.iter() {
            let coeff_bf = BF::from_u32_with_reduction(*coeff);
            let rhs_idx = if *lhs == *rhs {
                lhs_idx
            } else {
                remap_expected_constraint_input(&mut mapping, &mut inputs, *rhs)
            };
            quadratic_terms.push(
                crate::prover::gkr::backward::GpuGKRMainLayerConstraintQuadraticTerm {
                    lhs: lhs_idx as u32,
                    rhs: rhs_idx as u32,
                    challenge: E::from_base(coeff_bf),
                    immediate_recipe:
                        crate::prover::gkr::immediate_factors::ImmediateFactorRecipeStructural::from_base(
                            coeff_bf,
                        ),
                },
            );
        }
    }

    for (coeff, input) in relation.linear_terms.iter() {
        let coeff_bf = BF::from_u32_with_reduction(*coeff);
        let input_idx = remap_expected_constraint_input(&mut mapping, &mut inputs, *input);
        linear_terms.push(
            crate::prover::gkr::backward::GpuGKRMainLayerConstraintLinearTerm {
                input: input_idx as u32,
                challenge: E::from_base(coeff_bf),
                immediate_recipe:
                    crate::prover::gkr::immediate_factors::ImmediateFactorRecipeStructural::from_base(
                        coeff_bf,
                    ),
            },
        );
    }

    (
        GKRInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: Vec::new(),
        },
        ExpectedMainLayerConstraintMetadata {
            quadratic_terms,
            linear_terms,
            constant_offset: E::from_base(BF::from_u32_with_reduction(relation.constant)),
        },
    )
}

fn expected_linear_base_kernel_inputs_and_metadata<E: Field + FieldExtension<BF>>(
    relation: &cs::definitions::gkr::NoFieldLinearRelation,
    output: GKRAddress,
) -> (GKRInputs, ExpectedMainLayerConstraintMetadata<E>) {
    let mut mapping = BTreeMap::new();
    let mut inputs = Vec::new();
    let mut linear_terms = Vec::new();

    for (coeff, input) in relation.linear_terms.iter() {
        let coeff_bf = BF::from_u32_with_reduction(*coeff);
        let input_idx = remap_expected_constraint_input(&mut mapping, &mut inputs, *input);
        linear_terms.push(
            crate::prover::gkr::backward::GpuGKRMainLayerConstraintLinearTerm {
                input: input_idx as u32,
                challenge: E::from_base(coeff_bf),
                immediate_recipe:
                    crate::prover::gkr::immediate_factors::ImmediateFactorRecipeStructural::from_base(
                        coeff_bf,
                    ),
            },
        );
    }

    (
        GKRInputs {
            inputs_in_base: inputs,
            inputs_in_extension: Vec::new(),
            outputs_in_base: vec![output],
            outputs_in_extension: Vec::new(),
        },
        ExpectedMainLayerConstraintMetadata {
            quadratic_terms: Vec::new(),
            linear_terms,
            constant_offset: E::from_base(BF::from_u32_with_reduction(relation.constant)),
        },
    )
}

pub(crate) fn expected_main_layer_kernel_specs_for_test<E: Field + FieldExtension<BF>>(
    layer: &GKRLayerDescription,
    layer_idx: usize,
    storage: &GpuGKRStorage<BF, E>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    batch_challenge_base: E,
    _lookup_multiplicative_challenge: E,
    lookup_additive_challenge: E,
    _num_base_layer_memory_polys: usize,
    _num_base_layer_witness_polys: usize,
) -> Vec<ExpectedMainLayerKernelSpec<E>> {
    let trace_len = storage.layers[layer_idx]
        .base_field_inputs
        .values()
        .next()
        .map(|poly| poly.len())
        .or_else(|| {
            storage.layers[layer_idx]
                .extension_field_inputs
                .values()
                .next()
                .map(|poly| poly.len())
        })
        .expect("expected at least one input poly in storage layer");
    let mut current_batch_challenge = E::ONE;
    let mut get_challenge = || {
        let challenge = current_batch_challenge;
        current_batch_challenge.mul_assign(&batch_challenge_base);
        challenge
    };

    let mut specs = Vec::new();
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        match &gate.enforced_relation {
            NoFieldGKRRelation::CopyInBaseField { input, output }
            | NoFieldGKRRelation::CopyInExtensionField { input, output } => {
                let batch_challenges = vec![get_challenge()];
                if storage.layers[layer_idx]
                    .base_field_inputs
                    .contains_key(input)
                {
                    let relation = BaseFieldCopyGKRRelation {
                        input: *input,
                        output: *output,
                    };
                    specs.push(ExpectedMainLayerKernelSpec {
                        kind: GpuGKRMainLayerKernelKind::BaseCopy,
                        inputs: <BaseFieldCopyGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                        batch_challenges,
                        auxiliary_challenge: E::ZERO,
                        constraint_metadata: None,
                    });
                } else {
                    let relation = ExtensionCopyGKRRelation {
                        input: *input,
                        output: *output,
                    };
                    specs.push(ExpectedMainLayerKernelSpec {
                        kind: GpuGKRMainLayerKernelKind::ExtCopy,
                        inputs: <ExtensionCopyGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                        batch_challenges,
                        auxiliary_challenge: E::ZERO,
                        constraint_metadata: None,
                    });
                }
            }
            NoFieldGKRRelation::InitialGrandProductWithoutCaches { input, output } => {
                let (inputs, constraint_metadata) = crate::prover::gkr::backward::build_initial_grand_product_without_caches_inputs_and_metadata::<E>(
                    input,
                    *output,
                    external_challenges,
                );
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::InitialGrandProductWithoutCaches,
                    inputs,
                    batch_challenges: vec![get_challenge()],
                    auxiliary_challenge: E::ZERO,
                    constraint_metadata: Some(ExpectedMainLayerConstraintMetadata {
                        quadratic_terms: constraint_metadata.quadratic_terms,
                        linear_terms: constraint_metadata.linear_terms,
                        constant_offset: constraint_metadata.constant_offset,
                    }),
                });
            }
            NoFieldGKRRelation::InitialGrandProductFromCaches { input, output }
            | NoFieldGKRRelation::TrivialProduct { input, output } => {
                let relation = SameSizeProductGKRRelation {
                    inputs: *input,
                    output: *output,
                };
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::Product,
                    inputs: <SameSizeProductGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenges: vec![get_challenge()],
                    auxiliary_challenge: E::ZERO,
                    constraint_metadata: None,
                });
            }
            NoFieldGKRRelation::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                let relation = MaskIntoIdentityProductGKRRelation {
                    input: *input,
                    mask: *mask,
                    output: *output,
                };
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::MaskIdentity,
                    inputs:
                        <MaskIntoIdentityProductGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                    batch_challenges: vec![get_challenge()],
                    auxiliary_challenge: E::ZERO,
                    constraint_metadata: None,
                });
            }
            NoFieldGKRRelation::AggregateLookupRationalPair { input, output } => {
                let relation = LookupPairGKRRelation {
                    inputs: *input,
                    outputs: *output,
                };
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::LookupPair,
                    inputs: <LookupPairGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenges: vec![get_challenge(), get_challenge()],
                    auxiliary_challenge: E::ZERO,
                    constraint_metadata: None,
                });
            }
            NoFieldGKRRelation::LookupPairFromBaseInputs { input, output, .. } => {
                let (inputs, constraint_metadata) = crate::prover::gkr::backward::build_lookup_pair_from_base_inputs_inputs_and_metadata::<E>(
                    input,
                    *output,
                    lookup_additive_challenge,
                );
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::LookupPairFromBaseInputs,
                    inputs,
                    batch_challenges: vec![get_challenge(), get_challenge()],
                    auxiliary_challenge: E::ZERO,
                    constraint_metadata: Some(ExpectedMainLayerConstraintMetadata {
                        quadratic_terms: constraint_metadata.quadratic_terms,
                        linear_terms: constraint_metadata.linear_terms,
                        constant_offset: constraint_metadata.constant_offset,
                    }),
                });
            }
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, output } => {
                let relation = LookupBasePairGKRRelation::<BF, E> {
                    inputs: *input,
                    outputs: *output,
                    lookup_additive_challenge,
                    _marker: core::marker::PhantomData,
                };
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::LookupBasePair,
                    inputs:
                        <LookupBasePairGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                    batch_challenges: vec![get_challenge(), get_challenge()],
                    auxiliary_challenge: lookup_additive_challenge,
                    constraint_metadata: None,
                });
            }
            NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {
                let relation = LookupBaseMinusMultiplicityByBaseGKRRelation::<BF, E> {
                    input: *input,
                    setup: *setup,
                    outputs: *output,
                    lookup_additive_challenge,
                    _marker: core::marker::PhantomData,
                };
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase,
                    inputs:
                        <LookupBaseMinusMultiplicityByBaseGKRRelation<BF, E> as BatchedGKRKernel<
                            BF,
                            E,
                        >>::get_inputs(&relation),
                    batch_challenges: vec![get_challenge(), get_challenge()],
                    auxiliary_challenge: lookup_additive_challenge,
                    constraint_metadata: None,
                });
            }
            NoFieldGKRRelation::LookupWithDensAndSetupExpressions {
                input,
                setup,
                output,
            } => {
                let (inputs, constraint_metadata) = crate::prover::gkr::backward::build_lookup_with_dens_and_setup_expressions_inputs_and_metadata::<E>(
                    input,
                    setup,
                    *output,
                    _lookup_multiplicative_challenge,
                    lookup_additive_challenge,
                );
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::LookupWithDensAndSetupExpressions,
                    inputs,
                    batch_challenges: vec![get_challenge(), get_challenge()],
                    auxiliary_challenge: E::ZERO,
                    constraint_metadata: Some(ExpectedMainLayerConstraintMetadata {
                        quadratic_terms: constraint_metadata.quadratic_terms,
                        linear_terms: constraint_metadata.linear_terms,
                        constant_offset: constraint_metadata.constant_offset,
                    }),
                });
            }
            NoFieldGKRRelation::LookupFromMaterializedVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                let relation = LookupExtensionMinusMultiplicityByExtensionGKRRelation::<BF, E> {
                    input: *input,
                    setup: *setup,
                    outputs: *output,
                    lookup_additive_challenge,
                    _marker: core::marker::PhantomData,
                };
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::LookupExtMinusMultiplicityByExt,
                    inputs: <LookupExtensionMinusMultiplicityByExtensionGKRRelation<BF, E> as BatchedGKRKernel<
                        BF,
                        E,
                    >>::get_inputs(&relation),
                    batch_challenges: vec![get_challenge(), get_challenge()],
                    auxiliary_challenge: lookup_additive_challenge,
                    constraint_metadata: None,
                });
            }
            NoFieldGKRRelation::LookupPairFromVectorInputs { input, output } => {
                let (inputs, constraint_metadata) = crate::prover::gkr::backward::build_lookup_pair_from_vector_inputs_inputs_and_metadata::<E>(
                    input,
                    *output,
                    _lookup_multiplicative_challenge,
                    lookup_additive_challenge,
                );
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::LookupPairFromVectorInputs,
                    inputs,
                    batch_challenges: vec![get_challenge(), get_challenge()],
                    auxiliary_challenge: E::ZERO,
                    constraint_metadata: Some(ExpectedMainLayerConstraintMetadata {
                        quadratic_terms: constraint_metadata.quadratic_terms,
                        linear_terms: constraint_metadata.linear_terms,
                        constant_offset: constraint_metadata.constant_offset,
                    }),
                });
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                let relation = LookupRationalPairWithUnbalancedBaseGKRRelation::<BF, E> {
                    inputs: *input,
                    remainder: *remainder,
                    outputs: *output,
                    lookup_additive_challenge,
                    _marker: core::marker::PhantomData,
                };
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalanced,
                    inputs: <LookupRationalPairWithUnbalancedBaseGKRRelation<BF, E> as BatchedGKRKernel<
                        BF,
                        E,
                    >>::get_inputs(&relation),
                    batch_challenges: vec![get_challenge(), get_challenge()],
                    auxiliary_challenge: lookup_additive_challenge,
                    constraint_metadata: None,
                });
            }
            NoFieldGKRRelation::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                let relation = LookupBaseExtMinusBaseExtGKRRelation::<BF, E> {
                    nums: [input[0], setup[0]],
                    dens: [input[1], setup[1]],
                    outputs: *output,
                    lookup_additive_challenge,
                    _marker: core::marker::PhantomData,
                };
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup,
                    inputs: <LookupBaseExtMinusBaseExtGKRRelation<BF, E> as BatchedGKRKernel<
                        BF,
                        E,
                    >>::get_inputs(&relation),
                    batch_challenges: vec![get_challenge(), get_challenge()],
                    auxiliary_challenge: lookup_additive_challenge,
                    constraint_metadata: None,
                });
            }
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { .. } => {
                unreachable!(
                    "batched max-quadratic constraints not supported on GPU; cs/ must emit EnforceSingleMaxQuadraticConstraint (USE_BATCHING=false)"
                );
            }
            NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input } => {
                let (inputs, constraint_metadata) =
                    expected_single_max_quadratic_constraint_inputs_and_metadata::<E>(input);
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
                    inputs,
                    batch_challenges: vec![get_challenge()],
                    auxiliary_challenge: E::ZERO,
                    constraint_metadata: Some(constraint_metadata),
                });
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs {
                input,
                remainder,
                output,
            } => {
                let (inputs, constraint_metadata) = crate::prover::gkr::backward::build_lookup_unbalanced_pair_with_vector_inputs_inputs_and_metadata::<E>(
                    *input,
                    remainder,
                    *output,
                    _lookup_multiplicative_challenge,
                    lookup_additive_challenge,
                );
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalancedPairWithVectorInputs,
                    inputs,
                    batch_challenges: vec![get_challenge(), get_challenge()],
                    auxiliary_challenge: E::ZERO,
                    constraint_metadata: Some(ExpectedMainLayerConstraintMetadata {
                        quadratic_terms: constraint_metadata.quadratic_terms,
                        linear_terms: constraint_metadata.linear_terms,
                        constant_offset: constraint_metadata.constant_offset,
                    }),
                });
            }
            NoFieldGKRRelation::LookupFromVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                let (inputs, constraint_metadata) = crate::prover::gkr::backward::build_lookup_from_vector_input_with_setup_inputs_and_metadata::<E>(
                    input,
                    setup,
                    *output,
                    _lookup_multiplicative_challenge,
                    lookup_additive_challenge,
                );
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::LookupFromVectorInputWithSetup,
                    inputs,
                    batch_challenges: vec![get_challenge(), get_challenge()],
                    auxiliary_challenge: E::ZERO,
                    constraint_metadata: Some(ExpectedMainLayerConstraintMetadata {
                        quadratic_terms: constraint_metadata.quadratic_terms,
                        linear_terms: constraint_metadata.linear_terms,
                        constant_offset: constraint_metadata.constant_offset,
                    }),
                });
            }
            NoFieldGKRRelation::MaterializeGrandProductTermExpression { input, output } => {
                let (inputs, constraint_metadata) = crate::prover::gkr::backward::build_materialize_grand_product_term_expression_inputs_and_metadata::<E>(
                    input,
                    *output,
                    external_challenges,
                );
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::MaterializeGrandProductTermExpression,
                    inputs,
                    batch_challenges: vec![get_challenge()],
                    auxiliary_challenge: E::ZERO,
                    constraint_metadata: Some(ExpectedMainLayerConstraintMetadata {
                        quadratic_terms: constraint_metadata.quadratic_terms,
                        linear_terms: constraint_metadata.linear_terms,
                        constant_offset: constraint_metadata.constant_offset,
                    }),
                });
            }
            NoFieldGKRRelation::MaterializeSingleLookupInput { input, output, .. } => {
                let (inputs, constraint_metadata) =
                    expected_linear_base_kernel_inputs_and_metadata::<E>(&input.input, *output);
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::LinearBaseOutput,
                    inputs,
                    batch_challenges: vec![get_challenge()],
                    auxiliary_challenge: E::ZERO,
                    constraint_metadata: Some(constraint_metadata),
                });
            }
            NoFieldGKRRelation::LinearBaseFieldRelation { input, output } => {
                let (inputs, constraint_metadata) =
                    expected_linear_base_kernel_inputs_and_metadata::<E>(input, *output);
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::LinearBaseOutput,
                    inputs,
                    batch_challenges: vec![get_challenge()],
                    auxiliary_challenge: E::ZERO,
                    constraint_metadata: Some(constraint_metadata),
                });
            }
            NoFieldGKRRelation::InitsOrTeardownsInitialPair {
                timestamp_and_value,
                setup,
                output,
                set_idxes,
            } => {
                let top_bits = set_idxes.map(|idx| idx as u32);
                let high_bits_shift =
                    prover::gkr::high_bits_offset_for_inits_and_teardowns::<2>(trace_len);
                let (inputs, constraint_metadata) = crate::prover::gkr::backward::build_inits_and_teardowns_initial_pair_inputs_and_metadata(
                    timestamp_and_value,
                    *setup,
                    *output,
                    top_bits,
                    high_bits_shift,
                    external_challenges,
                );
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::InitsAndTeardownsInitialPair,
                    inputs,
                    batch_challenges: vec![get_challenge()],
                    auxiliary_challenge: E::ZERO,
                    constraint_metadata: Some(ExpectedMainLayerConstraintMetadata {
                        quadratic_terms: constraint_metadata.quadratic_terms,
                        linear_terms: constraint_metadata.linear_terms,
                        constant_offset: constraint_metadata.constant_offset,
                    }),
                });
            }
            NoFieldGKRRelation::UnbalancedGrandProductWithCache { .. }
            | NoFieldGKRRelation::MaterializedVectorLookupInput { .. }
            | NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs { .. }
            | NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs { .. }
            | NoFieldGKRRelation::LookupPairFromCachedVectorInputs { .. }
            | NoFieldGKRRelation::MaxQuadratic { .. } => {
                panic!(
                    "unsupported main-layer relation in test: {:?}",
                    gate.enforced_relation
                )
            }
        }
    }

    specs
}
