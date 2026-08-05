//! Relocated from gpu_gkr's `backward/tests/dimension_reduction_tests.rs`.
//! This test drives the full backward workflow off the apex-only
//! `prepare_basic_unrolled_async_backward_fixture` (built via
//! `proof::layout::build_proof_layout_inputs`, which stays in the apex),
//! so it belongs in the apex e2e suite — see the split test-seam manifest gap note.

use crate::upstream::Field;
use era_cudart::memory::memory_copy_async;
use era_cudart::slice::CudaSlice;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::field::E4;
use gpu_gkr::backward::kernels::{
    make_deferred_backward_workflow_state, populate_backward_workflow_state,
    DeviceClaimPointAndBatching,
};

#[test]
fn shared_state_dimension_reduction_purges_storage_after_each_layer() {
    let fixture = super::prepare_basic_unrolled_async_backward_fixture();
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
        gpu_core::primitives::context::UnsafeMutAccessor::new(shared_state.as_mut());
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

    let mut initial_callbacks = gpu_core::primitives::callbacks::Callbacks::new();
    let mut shared_device_seed = gpu_gkr::backward::kernels::h2d_seed_from_host(
        context,
        &mut initial_callbacks,
        &fixture.seed,
    )
    .unwrap();

    let shared_device_claim_point_initial =
        gpu_gkr::backward::kernels::h2d_claim_point_and_batching_from_host::<E4>(
            context,
            &mut initial_callbacks,
            &fixture_evaluation_point_for_device,
            fixture.batching_challenge,
        )
        .unwrap();
    let mut shared_device_claim_point =
        DeviceClaimPointAndBatching::from_allocation(shared_device_claim_point_initial);
    let (mut shared_device_claims, mut shared_claim_layout) =
        gpu_gkr::backward::kernels::h2d_claims_from_host::<E4>(
            context,
            &mut initial_callbacks,
            &fixture_top_layer_claims_for_device,
        )
        .unwrap();

    let proof_layout = fixture.proof_layout.clone();
    let proof_slab = fixture.proof_slab;
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
                backward_state.storage_mut(),
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

    let fixture_external_challenges_for_device = fixture.external_challenges;
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
        gpu_gkr::backward::kernels::h2d_lookup_and_constraint_from_shared_state::<E4>(
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
    // Use the real fixture layout for the main-layer scheduler too. The
    // main-layer slot starts at `num_dim_reducing_layers` per
    // `build_proof_layout_inputs`'s scheduler-order numbering.
    let main_layer_slot = expected_dimension_reducing_layers;
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
            &proof_layout,
            main_layer_slot,
            true,
            Some(main_state.storage_mut()),
            context,
        )
        .unwrap();

    context.get_exec_stream().synchronize().unwrap();
    drop(initial_callbacks);

    let execution =
        gpu_gkr::backward::kernels::take_backward_execution_from_shared_state(shared_state_handle);
    assert!(
        execution
            .claims_for_layers
            .contains_key(&first_main_layer_idx),
        "shared-state workflow should still schedule the first main layer after purging"
    );
}
