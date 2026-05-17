use super::super::*;
use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::field::E4;

use era_cudart::memory::memory_copy_async;
use era_cudart::slice::CudaSlice;

use serial_test::serial;
use std::collections::BTreeMap;

use super::{build_dimension_reducing_kernel_blueprints, sample_ext, successive_powers};
use crate::upstream::{DimensionReducingInputOutput, Field, OutputType};

#[test]
#[serial]
fn shared_state_dimension_reduction_purges_storage_after_each_layer() {
    let fixture = crate::prover::tests::prepare_basic_unrolled_async_backward_fixture(8);
    let context = &fixture.context;
    let expected_dimension_reducing_layers =
        fixture.initial_output_layer_idx - fixture.compiled_circuit.layers.len();
    assert!(
        expected_dimension_reducing_layers >= 2,
        "fixture must include multiple dimension-reducing layers"
    );

    let mut backward_state = fixture.gpu_backward_state;
    let mut shared_state = make_deferred_backward_workflow_state();
    let shared_state_handle =
        crate::primitives::context::UnsafeMutAccessor::new(shared_state.as_mut());
    let fixture_evaluation_point_for_device = fixture.evaluation_point.clone();
    let fixture_top_layer_claims_for_device = fixture.top_layer_claims.clone();
    populate_backward_workflow_state(
        shared_state_handle,
        fixture.initial_output_layer_idx,
        fixture.top_layer_claims,
        fixture.evaluation_point,
        fixture.seed,
        fixture.batching_challenge,
        fixture.lookup_multiplicative_part,
        fixture.lookup_additive_part,
    );

    let mut initial_callbacks = crate::primitives::callbacks::Callbacks::new();
    let mut shared_device_seed = crate::prover::gkr::backward::h2d_seed_from_host(
        context,
        &mut initial_callbacks,
        &fixture.seed,
    )
    .unwrap();

    let shared_device_claim_point_initial =
        crate::prover::gkr::backward::h2d_claim_point_and_batching_from_host::<E4>(
            context,
            &mut initial_callbacks,
            &fixture_evaluation_point_for_device,
            fixture.batching_challenge,
        )
        .unwrap();
    let mut shared_device_claim_point =
        DeviceClaimPointAndBatching::from_allocation(shared_device_claim_point_initial);
    let (mut shared_device_claims, mut shared_claim_layout) =
        crate::prover::gkr::backward::h2d_claims_from_host::<E4>(
            context,
            &mut initial_callbacks,
            &fixture_top_layer_claims_for_device,
        )
        .unwrap();

    let proof_layout = crate::prover::proof::layout::ProofLayout::new(
        &crate::prover::proof::layout::placeholder_inputs_for_prove(),
    );
    // Minimal placeholder slab: the placeholder layout has total_bytes == 0,
    // so per-field length checks inside the scheduler resolve to no-op
    // writes against a single-E4 dummy allocation.
    let proof_slab: crate::primitives::context::DeviceAllocation<E4> = context
        .alloc_with_extra_alignment::<E4, 4>(1, AllocationPlacement::Bottom)
        .unwrap();
    let mut dimension_reducing_layers = Vec::new();
    let mut purged_layers = 0usize;
    let mut layer_slot = 0usize;
    while let Some(mut prepared_layer) = backward_state.prepare_next_layer_static(context).unwrap()
    {
        let layer_idx = prepared_layer.layer_idx;
        let mut scheduled = prepared_layer
            .schedule_execute_dimension_reducing_layer_from_workflow_state(
                shared_state_handle,
                shared_device_seed,
                shared_device_claim_point,
                shared_device_claims,
                &shared_claim_layout,
                &proof_slab,
                &proof_layout,
                layer_slot,
                true,
                context,
            )
            .unwrap();
        layer_slot += 1;
        shared_device_seed = scheduled.device_seed.take().unwrap();
        shared_device_claim_point = scheduled.device_claim_point_for_next_layer.take().unwrap();
        shared_device_claims = scheduled.device_claims_for_next_layer.take().unwrap();
        shared_claim_layout = scheduled.claim_layout_for_next_layer.take().unwrap();
        dimension_reducing_layers.push(scheduled);
        backward_state.purge_up_to_layer(layer_idx);
        purged_layers += 1;

        assert_eq!(
            backward_state.storage().layers.len(),
            layer_idx + 1,
            "storage should be truncated through scheduled dimension-reducing layer {layer_idx}"
        );
        assert!(
            backward_state.storage().layers.get(layer_idx + 1).is_none(),
            "layers above {layer_idx} should be purged after scheduling"
        );
    }

    assert_eq!(purged_layers, expected_dimension_reducing_layers);

    let fixture_external_challenges_for_device = fixture.external_challenges.clone();
    let mut main_state = backward_state.into_main_layer_backward_state(
        fixture.compiled_circuit,
        fixture.external_challenges,
        fixture.lookup_multiplicative_part,
        E4::ZERO,
        false,
    );
    let mut first_main_layer = main_state
        .prepare_next_layer_static(context)
        .unwrap()
        .expect("expected first main-layer plan after dimension reduction");
    let first_main_layer_idx = first_main_layer.layer_idx;
    let device_lookup_and_constraint =
        crate::prover::gkr::backward::h2d_lookup_and_constraint_from_shared_state::<E4>(
            context,
            &mut initial_callbacks,
            shared_state_handle,
        )
        .unwrap();
    let mut external_challenges_flat = fixture_external_challenges_for_device
        .permutation_argument_linearization_challenges
        .to_vec();
    external_challenges_flat
        .push(fixture_external_challenges_for_device.permutation_argument_additive_part);
    let mut external_challenges_host =
        unsafe { context.alloc_host_uninit_slice(external_challenges_flat.len()) };
    unsafe {
        external_challenges_host
            .get_mut_accessor()
            .get_mut()
            .copy_from_slice(&external_challenges_flat);
    }
    let mut device_external_challenges = context
        .alloc(external_challenges_host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(
        &mut device_external_challenges,
        &external_challenges_host,
        context.get_exec_stream(),
    )
    .unwrap();
    drop(external_challenges_host);
    let main_proof_layout = crate::prover::proof::layout::ProofLayout::new(
        &crate::prover::proof::layout::placeholder_inputs_for_prove(),
    );
    let _first_main_layer_execution = first_main_layer
        .schedule_execute_main_layer_from_workflow_state(
            shared_state_handle,
            shared_device_seed,
            shared_device_claim_point,
            shared_device_claims,
            &shared_claim_layout,
            device_lookup_and_constraint.as_ptr(),
            device_external_challenges.as_ptr(),
            &proof_slab,
            &main_proof_layout,
            0,
            true,
            // Test path: placeholder proof layout has empty
            // `extra_evaluations_addresses` for every slot, so no
            // extras work runs and storage isn't dereferenced.
            None,
            context,
        )
        .unwrap();

    context.get_exec_stream().synchronize().unwrap();
    drop(initial_callbacks);

    let execution = super::take_backward_execution_from_shared_state(shared_state_handle);
    assert!(
        execution
            .claims_for_layers
            .contains_key(&first_main_layer_idx),
        "shared-state workflow should still schedule the first main layer after purging"
    );
}

#[test]
fn main_layer_kind_batch_challenge_count_matches_all_supported_kinds() {
    let one_challenge_kinds = [
        GpuGKRMainLayerKernelKind::BaseCopy,
        GpuGKRMainLayerKernelKind::ExtCopy,
        GpuGKRMainLayerKernelKind::Product,
        GpuGKRMainLayerKernelKind::MaskIdentity,
        GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
        GpuGKRMainLayerKernelKind::MaxQuadraticBaseOutput,
        GpuGKRMainLayerKernelKind::LinearBaseOutput,
        GpuGKRMainLayerKernelKind::InitsAndTeardownsInitialPair,
        GpuGKRMainLayerKernelKind::InitialGrandProductWithoutCaches,
        GpuGKRMainLayerKernelKind::MaterializeGrandProductTermExpression,
    ];
    let two_challenge_kinds = [
        GpuGKRMainLayerKernelKind::LookupPair,
        GpuGKRMainLayerKernelKind::LookupBasePair,
        GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase,
        GpuGKRMainLayerKernelKind::LookupExtMinusMultiplicityByExt,
        GpuGKRMainLayerKernelKind::LookupUnbalanced,
        GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup,
        GpuGKRMainLayerKernelKind::LookupPairFromBaseInputs,
        GpuGKRMainLayerKernelKind::LookupWithDensAndSetupExpressions,
        GpuGKRMainLayerKernelKind::LookupPairFromVectorInputs,
        GpuGKRMainLayerKernelKind::LookupFromVectorInputWithSetup,
        GpuGKRMainLayerKernelKind::LookupUnbalancedPairWithVectorInputs,
        GpuGKRMainLayerKernelKind::LookupExtPair,
        GpuGKRMainLayerKernelKind::LookupUnbalancedExtension,
    ];

    for kind in one_challenge_kinds {
        assert_eq!(super::main_layer_kind_batch_challenge_count(kind), 1);
    }
    for kind in two_challenge_kinds {
        assert_eq!(super::main_layer_kind_batch_challenge_count(kind), 2);
    }
}

#[test]
fn dimension_reducing_kernel_blueprints_match_cpu_order_and_challenges() {
    let layer = BTreeMap::from([
        (
            OutputType::PermutationProduct,
            DimensionReducingInputOutput {
                inputs: vec![
                    cs::definitions::GKRAddress::InnerLayer {
                        layer: 10,
                        offset: 0,
                    },
                    cs::definitions::GKRAddress::InnerLayer {
                        layer: 10,
                        offset: 1,
                    },
                ],
                output: vec![
                    cs::definitions::GKRAddress::InnerLayer {
                        layer: 11,
                        offset: 0,
                    },
                    cs::definitions::GKRAddress::InnerLayer {
                        layer: 11,
                        offset: 1,
                    },
                ],
            },
        ),
        (
            OutputType::Lookup16Bits,
            DimensionReducingInputOutput {
                inputs: vec![
                    cs::definitions::GKRAddress::InnerLayer {
                        layer: 10,
                        offset: 2,
                    },
                    cs::definitions::GKRAddress::InnerLayer {
                        layer: 10,
                        offset: 3,
                    },
                ],
                output: vec![
                    cs::definitions::GKRAddress::InnerLayer {
                        layer: 11,
                        offset: 2,
                    },
                    cs::definitions::GKRAddress::InnerLayer {
                        layer: 11,
                        offset: 3,
                    },
                ],
            },
        ),
        (
            OutputType::LookupTimestamps,
            DimensionReducingInputOutput {
                inputs: vec![
                    cs::definitions::GKRAddress::InnerLayer {
                        layer: 10,
                        offset: 4,
                    },
                    cs::definitions::GKRAddress::InnerLayer {
                        layer: 10,
                        offset: 5,
                    },
                ],
                output: vec![
                    cs::definitions::GKRAddress::InnerLayer {
                        layer: 11,
                        offset: 4,
                    },
                    cs::definitions::GKRAddress::InnerLayer {
                        layer: 11,
                        offset: 5,
                    },
                ],
            },
        ),
        (
            OutputType::GenericLookup,
            DimensionReducingInputOutput {
                inputs: vec![
                    cs::definitions::GKRAddress::InnerLayer {
                        layer: 10,
                        offset: 6,
                    },
                    cs::definitions::GKRAddress::InnerLayer {
                        layer: 10,
                        offset: 7,
                    },
                ],
                output: vec![
                    cs::definitions::GKRAddress::InnerLayer {
                        layer: 11,
                        offset: 6,
                    },
                    cs::definitions::GKRAddress::InnerLayer {
                        layer: 11,
                        offset: 7,
                    },
                ],
            },
        ),
    ]);

    let batch_challenge_base = sample_ext(10);
    let blueprints = build_dimension_reducing_kernel_blueprints(&layer, batch_challenge_base);
    let powers = successive_powers(batch_challenge_base, 8);

    assert_eq!(blueprints.len(), 5);
    assert_eq!(
        blueprints[0].inputs.inputs_in_extension,
        vec![layer[&OutputType::PermutationProduct].inputs[0]]
    );
    assert_eq!(
        blueprints[0].inputs.outputs_in_extension,
        vec![layer[&OutputType::PermutationProduct].output[0]]
    );
    assert_eq!(blueprints[0].batch_challenges, vec![powers[0]]);

    assert_eq!(
        blueprints[1].inputs.inputs_in_extension,
        vec![layer[&OutputType::PermutationProduct].inputs[1]]
    );
    assert_eq!(
        blueprints[1].inputs.outputs_in_extension,
        vec![layer[&OutputType::PermutationProduct].output[1]]
    );
    assert_eq!(blueprints[1].batch_challenges, vec![powers[1]]);

    assert_eq!(
        blueprints[2].inputs.inputs_in_extension,
        layer[&OutputType::Lookup16Bits].inputs
    );
    assert_eq!(
        blueprints[2].inputs.outputs_in_extension,
        layer[&OutputType::Lookup16Bits].output
    );
    assert_eq!(blueprints[2].batch_challenges, vec![powers[2], powers[3]]);

    assert_eq!(
        blueprints[3].inputs.inputs_in_extension,
        layer[&OutputType::LookupTimestamps].inputs
    );
    assert_eq!(
        blueprints[3].inputs.outputs_in_extension,
        layer[&OutputType::LookupTimestamps].output
    );
    assert_eq!(blueprints[3].batch_challenges, vec![powers[4], powers[5]]);

    assert_eq!(
        blueprints[4].inputs.inputs_in_extension,
        layer[&OutputType::GenericLookup].inputs
    );
    assert_eq!(
        blueprints[4].inputs.outputs_in_extension,
        layer[&OutputType::GenericLookup].output
    );
    assert_eq!(blueprints[4].batch_challenges, vec![powers[6], powers[7]]);
}
