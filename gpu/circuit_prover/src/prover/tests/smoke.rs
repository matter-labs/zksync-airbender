use super::*;

#[test]
#[serial]
fn run_basic_unrolled_async_scheduler_smoke_test() {
    let BasicUnrolledAsyncBackwardFixture {
        context,
        compiled_circuit,
        external_challenges,
        gpu_backward_state,
        initial_output_layer_idx,
        top_layer_claims,
        evaluation_point,
        seed,
        batching_challenge,
        lookup_multiplicative_part,
        lookup_additive_part,
        constraints_batch_challenge: _,
        expected_proof_layers,
        proof_layout,
        proof_slab,
    } = prepare_basic_unrolled_async_backward_fixture(8);

    let scheduled = gpu_backward_state
        .schedule_execute_backward_workflow(
            compiled_circuit,
            external_challenges,
            initial_output_layer_idx,
            top_layer_claims,
            evaluation_point,
            seed,
            batching_challenge,
            lookup_multiplicative_part,
            lookup_additive_part,
            &proof_slab,
            &proof_layout,
            &context,
        )
        .unwrap();

    let completion_event =
        CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING).unwrap();
    completion_event.record(context.get_exec_stream()).unwrap();
    assert!(
        !completion_event.query().unwrap(),
        "workflow scheduling should enqueue work without waiting for completion"
    );

    let execution = scheduled.wait(&context).unwrap();
    // `claims_for_layers` carries one entry per proof-producing layer plus the
    // initial top-layer claim seeded before scheduling.
    assert_eq!(execution.claims_for_layers.len(), expected_proof_layers + 1);
    assert!(execution.claims_for_layers.contains_key(&0));
    assert!(execution.points_for_claims_at_layer.contains_key(&0));
    assert!(!execution.points_for_claims_at_layer[&0].is_empty());
}

#[test]
#[serial]
fn run_basic_unrolled_main_layer0_plan_matches_cpu_test() {
    fn copy_device_values<T: Copy>(
        context: &ProverContext,
        values: &crate::primitives::context::DeviceAllocation<T>,
    ) -> Vec<T> {
        let mut allocation = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy_async(&mut allocation, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        unsafe { allocation.get_accessor().get().to_vec() }
    }

    let BasicUnrolledAsyncBackwardFixture {
        context,
        compiled_circuit,
        external_challenges,
        mut gpu_backward_state,
        initial_output_layer_idx: _,
        top_layer_claims: _,
        evaluation_point: _,
        seed: _,
        batching_challenge,
        lookup_multiplicative_part,
        lookup_additive_part,
        constraints_batch_challenge: _,
        expected_proof_layers: _,
        proof_layout: _,
        proof_slab: _,
    } = prepare_basic_unrolled_async_backward_fixture(8);

    while let Some(layer_plan) = gpu_backward_state
        .prepare_next_layer_static(&context)
        .unwrap()
    {
        drop(layer_plan);
    }

    // The backward state (and the storage it inherits from the forward
    // pass) lives in normalized-address space — every scratch-mapped
    // `InnerLayer` was rewritten to `ScratchSpace` by
    // `normalize_compiled_circuit_for_gpu`. Match the expected helper to
    // that space so storage lookups resolve.
    let normalized_compiled_circuit =
        crate::prover::gkr::transform::normalize_compiled_circuit_for_gpu(compiled_circuit.clone());

    let mut main_layer_state = gpu_backward_state.into_main_layer_backward_state(
        compiled_circuit.clone(),
        external_challenges,
        lookup_multiplicative_part,
        lookup_additive_part,
        false,
    );

    let layer0_plan = loop {
        let Some(layer_plan) = main_layer_state
            .prepare_next_layer(batching_challenge, &context)
            .unwrap()
        else {
            panic!("expected to reach main layer 0 plan");
        };
        if layer_plan.layer_idx == 0 {
            break layer_plan;
        }
        drop(layer_plan);
    };

    let expected = expected_main_layer_kernel_specs_for_test(
        &normalized_compiled_circuit.layers[0],
        0,
        main_layer_state.storage(),
        &external_challenges,
        batching_challenge,
        lookup_multiplicative_part,
        lookup_additive_part,
        normalized_compiled_circuit.memory_layout.total_width,
        normalized_compiled_circuit.witness_layout.total_width,
    );

    context.get_exec_stream().synchronize().unwrap();
    assert_main_layer_plan_for_test(&layer0_plan, main_layer_state.storage(), &expected);

    let mut callbacks = crate::primitives::callbacks::Callbacks::new();
    let round1 = layer0_plan
        .schedule_round_1(&mut callbacks, &context)
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    for (idx, (scheduled, kernel)) in round1
        .iter()
        .zip(layer0_plan.kernel_plans().iter())
        .enumerate()
    {
        let base_inputs: Vec<
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<BF, E4>,
        > = copy_device_values(&context, &scheduled.device.base_field_inputs);
        let ext_inputs: Vec<
            crate::prover::gkr::GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>,
        > = copy_device_values(&context, &scheduled.device.extension_field_inputs);

        for (descriptor, address) in base_inputs.iter().zip(kernel.inputs.inputs_in_base.iter()) {
            if *address == GKRAddress::placeholder() {
                assert!(descriptor.base_input_start.is_null());
                continue;
            }
            // VirtualSetup polys have no backing storage entry.
            if matches!(address, GKRAddress::VirtualSetup(_)) {
                assert!(descriptor.base_input_start.is_null());
                continue;
            }
            let poly = main_layer_state.storage().get_base_layer(*address);
            assert_eq!(
                descriptor.base_input_start,
                poly.as_ptr(),
                "kernel {idx} round1 base input {:?} start mismatch",
                address
            );
            assert_eq!(
                descriptor.base_layer_half_size,
                poly.len() / 2,
                "kernel {idx} round1 base input {:?} half-size mismatch",
                address
            );
            assert_eq!(
                descriptor.next_layer_size,
                poly.len() / 4,
                "kernel {idx} round1 base input {:?} next-layer mismatch",
                address
            );
        }
        for (descriptor, address) in ext_inputs
            .iter()
            .zip(kernel.inputs.inputs_in_extension.iter())
        {
            if *address == GKRAddress::placeholder() {
                assert!(descriptor.previous_layer_start.is_null());
                continue;
            }
            let poly = main_layer_state.storage().get_ext_poly(*address);
            assert_eq!(
                descriptor.previous_layer_start,
                poly.as_ptr(),
                "kernel {idx} round1 ext input {:?} start mismatch",
                address
            );
            assert_eq!(
                descriptor.this_layer_size,
                poly.len() / 2,
                "kernel {idx} round1 ext input {:?} this-layer mismatch",
                address
            );
            assert_eq!(
                descriptor.next_layer_size,
                poly.len() / 4,
                "kernel {idx} round1 ext input {:?} next-layer mismatch",
                address
            );
            assert!(
                descriptor.first_access,
                "kernel {idx} round1 ext input {:?} should be first access",
                address
            );
        }
    }
}

#[test]
#[serial]
fn run_basic_unrolled_main_layer0_static_plan_matches_cpu_test() {
    let BasicUnrolledAsyncBackwardFixture {
        context,
        compiled_circuit,
        external_challenges,
        mut gpu_backward_state,
        initial_output_layer_idx: _,
        top_layer_claims: _,
        evaluation_point: _,
        seed: _,
        batching_challenge,
        lookup_multiplicative_part,
        lookup_additive_part,
        constraints_batch_challenge: _,
        expected_proof_layers: _,
        proof_layout: _,
        proof_slab: _,
    } = prepare_basic_unrolled_async_backward_fixture(8);

    while let Some(layer_plan) = gpu_backward_state
        .prepare_next_layer_static(&context)
        .unwrap()
    {
        drop(layer_plan);
    }

    let mut main_layer_state = gpu_backward_state.into_main_layer_backward_state(
        compiled_circuit.clone(),
        external_challenges,
        lookup_multiplicative_part,
        lookup_additive_part,
        false,
    );

    let layer0_plan = loop {
        let Some(layer_plan) = main_layer_state
            .prepare_next_layer_static(&context)
            .unwrap()
        else {
            panic!("expected to reach main layer 0 static plan");
        };
        if layer_plan.layer_idx == 0 {
            break layer_plan;
        }
        drop(layer_plan);
    };

    let expected = expected_main_layer_kernel_specs_for_test(
        &compiled_circuit.layers[0],
        0,
        main_layer_state.storage(),
        &external_challenges,
        batching_challenge,
        lookup_multiplicative_part,
        lookup_additive_part,
        compiled_circuit.memory_layout.total_width,
        compiled_circuit.witness_layout.total_width,
    );

    context.get_exec_stream().synchronize().unwrap();
    assert_eq!(layer0_plan.kernel_plans().len(), expected.len());

    let mut expected_offset = 0usize;
    for (idx, (kernel_plan, expected_spec)) in layer0_plan
        .kernel_plans()
        .iter()
        .zip(expected.iter())
        .enumerate()
    {
        assert_eq!(
            kernel_plan.kind, expected_spec.kind,
            "kernel {idx} kind mismatch"
        );
        assert_eq!(
            kernel_plan.inputs, expected_spec.inputs,
            "kernel {idx} inputs mismatch"
        );
        assert!(
            kernel_plan.batch_challenges.is_empty(),
            "kernel {idx} static plan should not embed immediate batch challenges"
        );
        assert_eq!(
            kernel_plan.batch_challenge_offset, expected_offset,
            "kernel {idx} batch challenge offset mismatch"
        );
        assert_eq!(
            kernel_plan.batch_challenge_count,
            expected_spec.batch_challenges.len(),
            "kernel {idx} batch challenge count mismatch"
        );
        expected_offset += expected_spec.batch_challenges.len();

        match expected_spec.kind {
            GpuGKRMainLayerKernelKind::LookupBasePair
            | GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase
            | GpuGKRMainLayerKernelKind::LookupUnbalanced
            | GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup => {
                assert_eq!(
                    kernel_plan.auxiliary_challenge_summary(),
                    None,
                    "kernel {idx} should defer lookup additive challenge"
                );
            }
            _ => {
                assert_eq!(
                    kernel_plan.auxiliary_challenge_summary(),
                    Some(E4::ZERO),
                    "kernel {idx} should not depend on deferred auxiliary challenge"
                );
            }
        }

        match expected_spec.constraint_metadata.as_ref() {
            Some(metadata) => {
                // The static plan exposes the per-kernel constraint
                // metadata summary as `(quadratic_count, linear_count,
                // constant_offset)`. The static blueprint materializes
                // `constant_offset` eagerly when it depends only on
                // scheduling-time inputs (e.g. external challenges) and
                // defers it (returning `ZERO`) when it depends on
                // per-run lookup challenges. Both choices are correct;
                // accept either to keep this test agnostic of that
                // per-kind optimization.
                let summary = kernel_plan
                    .constraint_metadata_summary()
                    .expect("kernel with constraint metadata must report a summary");
                assert_eq!(
                    summary.0,
                    metadata.quadratic_terms.len(),
                    "kernel {idx} quadratic term count mismatch",
                );
                assert_eq!(
                    summary.1,
                    metadata.linear_terms.len(),
                    "kernel {idx} linear term count mismatch",
                );
                assert!(
                    summary.2 == E4::ZERO || summary.2 == metadata.constant_offset,
                    "kernel {idx} constraint metadata constant_offset {:?} matches neither deferred (ZERO) nor immediate ({:?})",
                    summary.2,
                    metadata.constant_offset,
                );
            }
            None => {
                assert_eq!(
                    kernel_plan.constraint_metadata_summary(),
                    None,
                    "kernel {idx} unexpected constraint metadata"
                );
            }
        }
    }
}

#[test]
#[serial]
fn run_basic_unrolled_main_layer0_kernel_kind_trace_test() {
    let BasicUnrolledAsyncBackwardFixture {
        context,
        compiled_circuit,
        external_challenges,
        mut gpu_backward_state,
        batching_challenge,
        lookup_multiplicative_part,
        lookup_additive_part,
        constraints_batch_challenge: _,
        ..
    } = prepare_basic_unrolled_async_backward_fixture(8);

    while let Some(layer_plan) = gpu_backward_state
        .prepare_next_layer_static(&context)
        .unwrap()
    {
        drop(layer_plan);
    }

    let mut main_layer_state = gpu_backward_state.into_main_layer_backward_state(
        compiled_circuit,
        external_challenges,
        lookup_multiplicative_part,
        lookup_additive_part,
        false,
    );

    let layer0_plan = loop {
        let Some(layer_plan) = main_layer_state
            .prepare_next_layer(batching_challenge, &context)
            .unwrap()
        else {
            panic!("expected to reach main layer 0 plan");
        };
        if layer_plan.layer_idx == 0 {
            break layer_plan;
        }
        drop(layer_plan);
    };

    let kernel_kinds = layer0_plan
        .kernel_plans()
        .iter()
        .map(|kernel| kernel.kind)
        .collect_vec();
    eprintln!("layer0 kernel kinds: {kernel_kinds:?}");
}

#[test]
#[serial]
fn run_basic_unrolled_async_allocator_regression_test() {
    let BasicUnrolledAsyncBackwardFixture {
        context,
        compiled_circuit,
        external_challenges,
        gpu_backward_state,
        initial_output_layer_idx,
        top_layer_claims,
        evaluation_point,
        seed,
        batching_challenge,
        lookup_multiplicative_part,
        lookup_additive_part,
        constraints_batch_challenge: _,
        expected_proof_layers: _,
        proof_layout,
        proof_slab,
    } = prepare_basic_unrolled_async_backward_fixture(8);

    let host_before = context.get_host_used_mem_current();
    context.reset_host_used_mem_peak();
    let scheduled = gpu_backward_state
        .schedule_execute_backward_workflow(
            compiled_circuit,
            external_challenges,
            initial_output_layer_idx,
            top_layer_claims,
            evaluation_point,
            seed,
            batching_challenge,
            lookup_multiplicative_part,
            lookup_additive_part,
            &proof_slab,
            &proof_layout,
            &context,
        )
        .unwrap();

    assert!(
        context.get_host_used_mem_peak() > host_before,
        "backward scheduling should allocate from the host allocator"
    );

    let execution = scheduled.wait(&context).unwrap();
    drop(execution);

    assert_eq!(
        context.get_host_used_mem_current(),
        host_before,
        "host allocator usage should return to baseline after drop"
    );
}

#[test]
#[serial]
#[ignore]
fn forward_to_backward_handoff_releases_forward_scratch() {
    let (base, expected_cpu_proof) =
        prepare_basic_unrolled_fixture(BasicUnrolledFixtureBuildConfig {
            binary_path: BASIC_UNROLLED_CPU_PARITY_BINARY_PATH,
            text_path: BASIC_UNROLLED_CPU_PARITY_TEXT_PATH,
            layout_path: BASIC_UNROLLED_ADD_SUB_LAYOUT_PATH,
            circuit_type: CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
            )),
            non_determinism_reads: &[15, 1],
            compute_cpu_reference: false,
            device_allocator_block_log_size: default_fixture_device_allocator_block_log_size(),
        });
    assert!(expected_cpu_proof.is_none());

    let _worker = Worker::new_with_num_threads(8);
    let context = make_test_context(64 * 1024, 1024);
    let mut transfers = base.create_transfers_for_context(&context).unwrap();
    transfers.schedule(&context).unwrap();
    context.get_h2d_stream().synchronize().unwrap();

    let setup_ref = transfers
        .setup
        .as_ref()
        .expect("fixture transfers always include setup");
    let mut stage1_output = generate_stage1_output_for_test(
        base.circuit_type,
        &base.compiled_circuit,
        setup_ref,
        transfers
            .decoder
            .as_ref()
            .map(|transfer| &transfer.data_device[..]),
        None,
        &transfers
            .tracing_data
            .as_ref()
            .expect("fixture transfers always include tracing_data")
            .data_device,
        &context,
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let mut lookup_challenges_host = unsafe { context.alloc_host_uninit_slice(3) };
    let mut transcript_input = vec![];
    base.external_challenges
        .flatten_into_buffer(&mut transcript_input);
    flatten_merkle_caps_iter_into(
        setup_ref
            .trace_holder
            .read_per_coset_caps_synchronously(&context)
            .unwrap()
            .into_iter(),
        &mut transcript_input,
    );
    flatten_merkle_caps_iter_into(
        base.memory_tree_caps.clone().into_iter(),
        &mut transcript_input,
    );
    flatten_merkle_caps_iter_into(
        stage1_output
            .witness_trace_holder
            .read_per_coset_caps_synchronously(&context)
            .unwrap()
            .into_iter(),
        &mut transcript_input,
    );
    let mut seed = Transcript::commit_initial(&transcript_input);
    let challenges: Vec<E4> = draw_random_field_els::<BF, E4>(&mut seed, 3);
    let [lookup_alpha, lookup_additive_part, constraints_batch_challenge] =
        challenges.try_into().unwrap();
    unsafe {
        lookup_challenges_host
            .get_mut_accessor()
            .get_mut()
            .copy_from_slice(&[
                lookup_alpha,
                lookup_additive_part,
                constraints_batch_challenge,
            ]);
    }
    let mut gpu_forward_setup = setup_ref
        .schedule_forward_setup(
            &base.compiled_circuit,
            upload_lookup_challenges_for_test(&lookup_challenges_host, &context),
            &context,
        )
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let gpu_forward_output = schedule_forward_pass(
        setup_ref,
        &mut stage1_output,
        &mut gpu_forward_setup,
        &base.compiled_circuit,
        &base.external_challenges,
        base.final_trace_size_log_2,
        &context,
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    drop(gpu_forward_setup);
    drop(transfers);
    drop(stage1_output);

    let before_handoff = context.get_used_mem_current();
    let backward_state = gpu_forward_output.into_dimension_reducing_backward_state();
    let after_handoff = context.get_used_mem_current();

    assert_eq!(
        after_handoff, before_handoff,
        "forward scratch is now released inside schedule_forward_pass, not at the handoff"
    );
    drop(backward_state);
}

#[test]
#[serial]
#[ignore]
fn run_basic_unrolled_test() {
    let fixture = prepare_basic_unrolled_proof_fixture();
    let proof_job = fixture.schedule_prove().unwrap();

    assert!(
        !proof_job.is_finished().unwrap(),
        "prove() should return before the scheduled proof completes"
    );

    let (gpu_proof, _proof_time_ms) = proof_job.finish().unwrap();
    assert_gkr_proof_eq_for_test(&gpu_proof, &fixture.expected_cpu_proof);
}

#[test]
#[serial]
#[ignore]
fn run_basic_unrolled_no_caches_test() {
    let (base, expected_cpu_proof) =
        prepare_basic_unrolled_fixture(BasicUnrolledFixtureBuildConfig {
            binary_path: BASIC_UNROLLED_CPU_PARITY_BINARY_PATH,
            text_path: BASIC_UNROLLED_CPU_PARITY_TEXT_PATH,
            layout_path: BASIC_UNROLLED_ADD_SUB_NO_CACHES_LAYOUT_PATH,
            circuit_type: CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
            )),
            non_determinism_reads: &[15, 1],
            compute_cpu_reference: true,
            device_allocator_block_log_size: default_fixture_device_allocator_block_log_size(),
        });
    let fixture = BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: expected_cpu_proof
            .expect("no-caches proof fixture must include the CPU reference proof"),
    };
    let proof_job = fixture.schedule_prove().unwrap();
    let (gpu_proof, _proof_time_ms) = proof_job.finish().unwrap();
    assert_gkr_proof_eq_for_test(&gpu_proof, &fixture.expected_cpu_proof);
}

#[test]
#[serial]
#[ignore]
fn run_basic_unrolled_proof_job_default_pow_smoke_test() {
    let fixture = prepare_basic_unrolled_proof_fixture();
    let proof_job = fixture.schedule_prove().unwrap();

    assert!(
        !proof_job.is_finished().unwrap(),
        "prove() should remain non-blocking"
    );

    let (gpu_proof, _proof_time_ms) = proof_job.finish().unwrap();
    assert_gkr_proof_eq_for_test(&gpu_proof, &fixture.expected_cpu_proof);
}

