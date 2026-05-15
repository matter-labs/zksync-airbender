use super::*;

pub(super) fn assert_main_layer_plan_for_test<E: Field + std::fmt::Debug>(
    layer_plan: &GpuGKRMainLayerSumcheckLayerPlan<E>,
    storage: &GpuGKRStorage<BF, E>,
    expected_specs: &[ExpectedMainLayerKernelSpec<E>],
) {
    assert_eq!(layer_plan.kernel_plans().len(), expected_specs.len());
    assert_eq!(layer_plan.round0_descriptors().len(), expected_specs.len());

    for (idx, expected) in expected_specs.iter().enumerate() {
        let kernel_plan = &layer_plan.kernel_plans()[idx];
        assert_eq!(kernel_plan.kind, expected.kind);
        assert_eq!(kernel_plan.inputs, expected.inputs);
        assert_eq!(kernel_plan.batch_challenges, expected.batch_challenges);
        assert_eq!(
            kernel_plan.auxiliary_challenge_summary(),
            Some(expected.auxiliary_challenge)
        );
        assert_eq!(
            kernel_plan.constraint_metadata_summary(),
            expected.constraint_metadata.as_ref().map(|metadata| {
                (
                    metadata.quadratic_terms.len(),
                    metadata.linear_terms.len(),
                    metadata.constant_offset,
                )
            })
        );

        let round0 = &layer_plan.round0_descriptors()[idx];
        let base_inputs = round0.base_field_inputs.as_slice();
        let ext_inputs = round0.extension_field_inputs.as_slice();
        let base_outputs = round0.base_field_outputs.as_slice();
        let ext_outputs = round0.extension_field_outputs.as_slice();

        assert_eq!(base_inputs.len(), expected.inputs.inputs_in_base.len());
        assert_eq!(ext_inputs.len(), expected.inputs.inputs_in_extension.len());
        assert_eq!(base_outputs.len(), expected.inputs.outputs_in_base.len());
        assert_eq!(
            ext_outputs.len(),
            expected.inputs.outputs_in_extension.len()
        );

        for (descriptor, address) in base_inputs
            .iter()
            .zip(expected.inputs.inputs_in_base.iter())
        {
            if *address == GKRAddress::placeholder() {
                assert!(descriptor.start.is_null());
                assert_eq!(descriptor.next_layer_size, 0);
                continue;
            }
            let poly = storage.get_base_layer(*address);
            assert_eq!(
                descriptor.start,
                poly.as_ptr(),
                "kernel {idx} base input {:?} start mismatch",
                address
            );
            assert_eq!(
                descriptor.next_layer_size,
                poly.len() / 2,
                "kernel {idx} base input {:?} size mismatch",
                address
            );
        }
        for (descriptor, address) in ext_inputs
            .iter()
            .zip(expected.inputs.inputs_in_extension.iter())
        {
            if *address == GKRAddress::placeholder() {
                assert!(descriptor.start.is_null());
                assert_eq!(descriptor.next_layer_size, 0);
                continue;
            }
            let poly = storage.get_ext_poly(*address);
            assert_eq!(
                descriptor.start,
                poly.as_ptr(),
                "kernel {idx} ext input {:?} start mismatch",
                address
            );
            assert_eq!(
                descriptor.next_layer_size,
                poly.len() / 2,
                "kernel {idx} ext input {:?} size mismatch",
                address
            );
        }
        for (descriptor, address) in base_outputs
            .iter()
            .zip(expected.inputs.outputs_in_base.iter())
        {
            let poly = storage.get_base_layer(*address);
            assert_eq!(
                descriptor.start,
                poly.as_ptr(),
                "kernel {idx} base output {:?} start mismatch",
                address
            );
            assert_eq!(
                descriptor.next_layer_size,
                poly.len() / 2,
                "kernel {idx} base output {:?} size mismatch",
                address
            );
        }
        for (descriptor, address) in ext_outputs
            .iter()
            .zip(expected.inputs.outputs_in_extension.iter())
        {
            let poly = storage.get_ext_poly(*address);
            assert_eq!(
                descriptor.start,
                poly.as_ptr(),
                "kernel {idx} ext output {:?} start mismatch",
                address
            );
            assert_eq!(
                descriptor.next_layer_size,
                poly.len() / 2,
                "kernel {idx} ext output {:?} size mismatch",
                address
            );
        }
    }
}

pub(super) fn assert_sumcheck_intermediate_values_eq_for_test_with_layer<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    actual: &prover::gkr::prover::SumcheckIntermediateProofValues<F, E>,
    expected: &prover::gkr::prover::SumcheckIntermediateProofValues<F, E>,
    layer_idx: usize,
) {
    assert_eq!(
        actual.sumcheck_num_rounds, expected.sumcheck_num_rounds,
        "layer {layer_idx}: sumcheck_num_rounds mismatch"
    );
    assert_eq!(
        actual.internal_round_coefficients.len(),
        expected.internal_round_coefficients.len(),
        "layer {layer_idx}: internal_round_coefficients length mismatch"
    );
    for (round_idx, (actual_coeffs, expected_coeffs)) in actual
        .internal_round_coefficients
        .iter()
        .zip(expected.internal_round_coefficients.iter())
        .enumerate()
    {
        for (coeff_idx, (&actual_coeff, &expected_coeff)) in
            actual_coeffs.iter().zip(expected_coeffs.iter()).enumerate()
        {
            assert_eq!(
                actual_coeff, expected_coeff,
                "layer {layer_idx}: internal_round_coefficients mismatch at round {round_idx}, coeff {coeff_idx}"
            );
        }
    }
    assert_eq!(
        actual.final_step_evaluations, expected.final_step_evaluations,
        "layer {layer_idx}: final_step_evaluations mismatch"
    );
}

pub(super) fn assert_layer_points_eq_for_test<E: Field + std::fmt::Debug>(
    actual: &BTreeMap<usize, Vec<E>>,
    expected: &BTreeMap<usize, Vec<E>>,
) {
    assert_eq!(
        actual.len(),
        expected.len(),
        "layer-point map sizes differ: actual keys {:?}, expected keys {:?}",
        actual.keys().collect::<Vec<_>>(),
        expected.keys().collect::<Vec<_>>(),
    );
    for (layer_idx, expected_point) in expected.iter() {
        let actual_point = actual
            .get(layer_idx)
            .unwrap_or_else(|| panic!("missing actual point for layer {layer_idx}"));
        assert_eq!(
            actual_point, expected_point,
            "layer point mismatch at layer {layer_idx}: actual={actual_point:?} expected={expected_point:?}"
        );
    }
}

pub(super) fn assert_backward_claims_eq_before_base_layer_expansion<E: Field + std::fmt::Debug>(
    actual: &BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    expected: &BTreeMap<usize, BTreeMap<GKRAddress, E>>,
) {
    assert_eq!(
        actual.len(),
        expected.len(),
        "layer-claim map sizes differ: actual keys {:?}, expected keys {:?}",
        actual.keys().collect::<Vec<_>>(),
        expected.keys().collect::<Vec<_>>(),
    );

    for (layer_idx, expected_claims) in expected.iter() {
        let actual_claims = actual
            .get(layer_idx)
            .unwrap_or_else(|| panic!("missing actual claims for layer {layer_idx}"));
        if *layer_idx == 0 {
            let filtered_expected = expected_claims
                .iter()
                .filter_map(|(address, claim)| {
                    actual_claims
                        .contains_key(address)
                        .then_some((*address, *claim))
                })
                .collect::<BTreeMap<_, _>>();
            assert_eq!(
                actual_claims, &filtered_expected,
                "layer 0 claims diverged before base-layer dependency expansion"
            );
        } else {
            assert_eq!(
                actual_claims, expected_claims,
                "layer {layer_idx} claims diverged before base-layer dependency expansion"
            );
        }
    }
}

pub(super) fn assert_base_field_query_eq_for_test(
    actual: &prover::gkr::whir::BaseFieldQuery<BF, DefaultTreeConstructor>,
    expected: &prover::gkr::whir::BaseFieldQuery<BF, DefaultTreeConstructor>,
) {
    assert_eq!(actual.index, expected.index);
    assert_eq!(
        actual.leaf_values_concatenated,
        expected.leaf_values_concatenated
    );
    assert_eq!(actual.path, expected.path);
}

pub(super) fn assert_extension_field_query_eq_for_test(
    actual: &prover::gkr::whir::ExtensionFieldQuery<BF, E4, DefaultTreeConstructor>,
    expected: &prover::gkr::whir::ExtensionFieldQuery<BF, E4, DefaultTreeConstructor>,
) {
    assert_eq!(actual.index, expected.index);
    assert_eq!(
        actual.leaf_values_concatenated,
        expected.leaf_values_concatenated
    );
    assert_eq!(actual.path, expected.path);
}

pub(super) fn assert_whir_proof_eq_for_test(
    actual: &prover::gkr::whir::WhirPolyCommitProof<BF, E4, DefaultTreeConstructor>,
    expected: &prover::gkr::whir::WhirPolyCommitProof<BF, E4, DefaultTreeConstructor>,
) {
    assert_eq!(
        actual.sumcheck_polys.len(),
        expected.sumcheck_polys.len(),
        "WHIR sumcheck round count diverged",
    );
    for (round_idx, (actual_poly, expected_poly)) in actual
        .sumcheck_polys
        .iter()
        .zip(expected.sumcheck_polys.iter())
        .enumerate()
    {
        assert_eq!(
            actual_poly.len(),
            expected_poly.len(),
            "WHIR sumcheck polynomial degree diverged at round {round_idx}",
        );
        for (coeff_idx, (&actual_coeff, &expected_coeff)) in
            actual_poly.iter().zip(expected_poly.iter()).enumerate()
        {
            assert_eq!(
                actual_coeff, expected_coeff,
                "WHIR sumcheck coefficient diverged at round {round_idx}, coeff {coeff_idx}",
            );
        }
    }
    assert_eq!(
        actual.ood_samples, expected.ood_samples,
        "WHIR OOD samples diverged"
    );
    assert_eq!(
        actual.pow_nonces, expected.pow_nonces,
        "WHIR PoW nonces diverged"
    );
    assert_eq!(
        actual.final_monomials, expected.final_monomials,
        "WHIR final monomials diverged",
    );

    for (actual_commitment, expected_commitment) in [
        (&actual.memory_commitment, &expected.memory_commitment),
        (&actual.witness_commitment, &expected.witness_commitment),
        (&actual.setup_commitment, &expected.setup_commitment),
    ] {
        assert_eq!(
            actual_commitment.commitment.cap,
            expected_commitment.commitment.cap
        );
        assert_eq!(
            actual_commitment.num_columns,
            expected_commitment.num_columns
        );
        assert_eq!(actual_commitment.evals, expected_commitment.evals);
        assert_eq!(
            actual_commitment.queries.len(),
            expected_commitment.queries.len()
        );
        for (actual_query, expected_query) in actual_commitment
            .queries
            .iter()
            .zip(expected_commitment.queries.iter())
        {
            assert_base_field_query_eq_for_test(actual_query, expected_query);
        }
    }

    assert_eq!(
        actual.intermediate_whir_oracles.len(),
        expected.intermediate_whir_oracles.len()
    );
    for (actual_oracle, expected_oracle) in actual
        .intermediate_whir_oracles
        .iter()
        .zip(expected.intermediate_whir_oracles.iter())
    {
        assert_eq!(actual_oracle.commitment.cap, expected_oracle.commitment.cap);
        assert_eq!(actual_oracle.queries.len(), expected_oracle.queries.len());
        for (actual_query, expected_query) in actual_oracle
            .queries
            .iter()
            .zip(expected_oracle.queries.iter())
        {
            assert_extension_field_query_eq_for_test(actual_query, expected_query);
        }
    }
}

pub(super) fn assert_gkr_proof_eq_for_test(
    actual: &GKRProof<BF, E4, DefaultTreeConstructor>,
    expected: &GKRProof<BF, E4, DefaultTreeConstructor>,
) {
    assert_eq!(actual.external_challenges, expected.external_challenges);
    assert_eq!(
        actual.final_explicit_evaluations,
        expected.final_explicit_evaluations
    );
    assert_eq!(
        actual.grand_product_accumulator_computed,
        expected.grand_product_accumulator_computed
    );
    assert_eq!(
        actual.sumcheck_intermediate_values.len(),
        expected.sumcheck_intermediate_values.len()
    );
    for (layer_idx, expected_values) in expected.sumcheck_intermediate_values.iter() {
        let actual_values = actual
            .sumcheck_intermediate_values
            .get(layer_idx)
            .unwrap_or_else(|| panic!("missing proof layer {layer_idx}"));
        assert_sumcheck_intermediate_values_eq_for_test_with_layer(
            actual_values,
            expected_values,
            *layer_idx,
        );
    }
    assert_whir_proof_eq_for_test(&actual.whir_proof, &expected.whir_proof);
}

pub(super) fn assert_gkr_proof_structure_for_test(
    proof: &GKRProof<BF, E4, DefaultTreeConstructor>,
    whir_schedule: &WhirSchedule,
) {
    assert!(
        !proof.sumcheck_intermediate_values.is_empty(),
        "proof must contain sumcheck intermediate values",
    );
    for key in [
        OutputType::PermutationProduct,
        OutputType::Lookup16Bits,
        OutputType::LookupTimestamps,
        OutputType::GenericLookup,
    ] {
        assert!(
            proof.final_explicit_evaluations.contains_key(&key),
            "proof must contain explicit evaluations for {key:?}",
        );
    }
    assert_eq!(
        proof.whir_proof.pow_nonces.len(),
        whir_schedule.whir_pow_schedule.len(),
        "proof must contain one PoW nonce per WHIR round",
    );
}

pub(super) fn stage1_caps_from_tree<T: ColumnMajorMerkleTreeConstructor<BF>>(
    tree: &T,
    subcap_size: usize,
) -> Vec<MerkleTreeCapVarLength> {
    tree.get_cap()
        .cap
        .chunks_exact(subcap_size)
        .map(|chunk| MerkleTreeCapVarLength {
            cap: chunk.to_vec(),
        })
        .collect_vec()
}

pub(super) fn copy_bf_device_slice_to_host(
    values: &DeviceSlice<BF>,
    context: &ProverContext,
) -> Vec<BF> {
    copy_device_slice_to_host(values, context)
}

pub(super) fn copy_u32_device_slice_to_host(
    values: &DeviceSlice<u32>,
    context: &ProverContext,
) -> Vec<u32> {
    copy_device_slice_to_host(values, context)
}

pub(super) fn copy_base_poly_from_gpu_storage<E: Field>(
    storage: &GpuGKRStorage<BF, E>,
    address: GKRAddress,
    context: &ProverContext,
) -> Vec<BF> {
    let poly = storage.get_base_layer(address);
    let mut tmp = context
        .alloc(poly.len(), AllocationPlacement::BestFit)
        .unwrap();
    set_by_ref(
        &poly.as_device_chunk(),
        tmp.deref_mut(),
        context.get_exec_stream(),
    )
    .unwrap();

    let mut host = unsafe { context.alloc_host_uninit_slice(poly.len()) };
    memory_copy_async(&mut host, &tmp, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    unsafe { host.get_accessor().get().to_vec() }
}

pub(super) fn copy_ext_poly_from_gpu_storage<E: Field + SetByRef>(
    storage: &GpuGKRStorage<BF, E>,
    address: GKRAddress,
    context: &ProverContext,
) -> Vec<E> {
    let poly = storage
        .try_get_ext_poly(address)
        .unwrap_or_else(|| panic!("missing GPU extension poly for {:?}", address));
    let mut tmp = context
        .alloc(poly.len(), AllocationPlacement::BestFit)
        .unwrap();
    set_by_ref(
        &poly.as_device_chunk(),
        tmp.deref_mut(),
        context.get_exec_stream(),
    )
    .unwrap();

    let mut host = vec![E::ZERO; poly.len()];
    memory_copy_async(&mut host, &tmp, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

pub(super) fn describe_first_trace_holder_column_mismatch<Column: AsRef<[BF]>>(
    trace_holder: &TraceHolder<BF>,
    cpu_columns: &[Column],
    trace_len: usize,
    context: &ProverContext,
) -> std::option::Option<String> {
    if trace_holder.columns_count != cpu_columns.len() {
        return Some(format!(
            "gpu columns {} != cpu columns {}",
            trace_holder.columns_count,
            cpu_columns.len()
        ));
    }
    if (1usize << trace_holder.log_domain_size) != trace_len {
        return Some(format!(
            "gpu trace len {} != cpu trace len {}",
            1usize << trace_holder.log_domain_size,
            trace_len
        ));
    }

    let raw = trace_holder.get_hypercube_evals();
    for (column_idx, cpu_column) in cpu_columns.iter().enumerate() {
        let gpu_column = copy_bf_device_slice_to_host(
            &raw[column_idx * trace_len..(column_idx + 1) * trace_len],
            context,
        );
        let cpu_column = cpu_column.as_ref();
        if let Some((row_idx, (gpu_value, cpu_value))) = gpu_column
            .iter()
            .zip(cpu_column.iter())
            .enumerate()
            .find(|(_, (gpu_value, cpu_value))| gpu_value != cpu_value)
        {
            return Some(format!(
                "column {column_idx}, row {row_idx}: gpu={gpu_value:?}, cpu={cpu_value:?}"
            ));
        }
    }

    None
}

pub(super) fn describe_first_trace_holder_subrange_mismatch<Column: AsRef<[BF]>>(
    trace_holder: &TraceHolder<BF>,
    cpu_columns: &[Column],
    column_range: std::ops::Range<usize>,
    trace_len: usize,
    context: &ProverContext,
) -> std::option::Option<String> {
    if column_range.end > trace_holder.columns_count {
        return Some(format!(
            "gpu column range {:?} exceeds total columns {}",
            column_range, trace_holder.columns_count
        ));
    }
    if column_range.end > cpu_columns.len() {
        return Some(format!(
            "cpu column range {:?} exceeds total columns {}",
            column_range,
            cpu_columns.len()
        ));
    }
    if (1usize << trace_holder.log_domain_size) != trace_len {
        return Some(format!(
            "gpu trace len {} != cpu trace len {}",
            1usize << trace_holder.log_domain_size,
            trace_len
        ));
    }

    let raw = trace_holder.get_hypercube_evals();
    for column_idx in column_range {
        let gpu_column = copy_bf_device_slice_to_host(
            &raw[column_idx * trace_len..(column_idx + 1) * trace_len],
            context,
        );
        let cpu_column = cpu_columns[column_idx].as_ref();
        if let Some((row_idx, (gpu_value, cpu_value))) = gpu_column
            .iter()
            .zip(cpu_column.iter())
            .enumerate()
            .find(|(_, (gpu_value, cpu_value))| gpu_value != cpu_value)
        {
            return Some(format!(
                "column {column_idx}, row {row_idx}: gpu={gpu_value:?}, cpu={cpu_value:?}"
            ));
        }
    }

    None
}

pub(super) fn describe_first_vec_mismatch<T: PartialEq + core::fmt::Debug>(
    gpu_values: &[T],
    cpu_values: &[T],
) -> std::option::Option<String> {
    if gpu_values.len() != cpu_values.len() {
        return Some(format!(
            "gpu len {} != cpu len {}",
            gpu_values.len(),
            cpu_values.len()
        ));
    }

    gpu_values
        .iter()
        .zip(cpu_values.iter())
        .enumerate()
        .find(|(_, (gpu_value, cpu_value))| gpu_value != cpu_value)
        .map(|(idx, (gpu_value, cpu_value))| {
            format!("index {idx}: gpu={gpu_value:?}, cpu={cpu_value:?}")
        })
}
