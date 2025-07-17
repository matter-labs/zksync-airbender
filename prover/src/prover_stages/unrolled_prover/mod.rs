use super::*;

pub(crate) mod quotient_parts;
pub mod stage2;
pub mod stage3;
// pub mod stage4;
// pub mod stage5;
pub(crate) mod stage_2_ram_shared;
pub(crate) mod stage_2_shared;

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct UnrolledModeProof {
    pub external_challenges: ExternalChallenges,
    pub public_inputs: Vec<Mersenne31Field>,
    pub witness_tree_caps: Vec<MerkleTreeCapVarLength>,
    pub memory_tree_caps: Vec<MerkleTreeCapVarLength>,
    pub setup_tree_caps: Vec<MerkleTreeCapVarLength>,
    pub stage_2_tree_caps: Vec<MerkleTreeCapVarLength>,
    pub memory_grand_product_accumulator: Mersenne31Quartic,
    pub delegation_argument_accumulator: Option<Mersenne31Quartic>,
    pub quotient_tree_caps: Vec<MerkleTreeCapVarLength>,
    pub evaluations_at_random_points: Vec<Mersenne31Quartic>,
    pub deep_poly_caps: Vec<MerkleTreeCapVarLength>,
    pub intermediate_fri_oracle_caps: Vec<Vec<MerkleTreeCapVarLength>>,
    pub last_fri_step_plain_leaf_values: Vec<Vec<Mersenne31Quartic>>,
    pub final_monomial_form: Vec<Mersenne31Quartic>,
    pub queries: Vec<QuerySet>,
    pub pow_nonce: u64,
    pub delegation_type: u16,
    pub aux_boundary_values: Vec<AuxArgumentsBoundaryValues>,
}

pub fn prove_configured_for_unrolled_circuits<
    const N: usize,
    A: GoodAllocator,
    T: MerkleTreeConstructor,
>(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    public_inputs: &[Mersenne31Field],
    external_challenges: &ExternalChallenges,
    witness_eval_data: WitnessEvaluationDataForExecutionFamily<N, A>,
    aux_boundary_values: &[AuxArgumentsBoundaryValues],
    setup_precomputations: &SetupPrecomputations<N, A, T>,
    precomputations: &Twiddles<Mersenne31Complex, A>,
    lde_precomputations: &LdePrecomputations<A>,
    delegation_processing_type: Option<u16>,
    lde_factor: usize,
    _tree_cap_size: usize,
    num_queries: usize,
    pow_bits: u32,
    worker: &Worker,
) -> (ProverData<N, A, T>, UnrolledModeProof) {
    let WitnessEvaluationDataForExecutionFamily {
        aux_data: _,
        exec_trace,
        num_witness_columns,
        lookup_mapping,
    } = witness_eval_data;

    assert_eq!(
        num_witness_columns,
        compiled_circuit.witness_layout.total_width
    );

    let trace_len = exec_trace.len();
    assert!(trace_len.is_power_of_two());
    let trace_width = exec_trace.width();

    // VERY important - we will use the fact that final borrow value is unconstrainted
    // when we will define lazy init/teardown padding constraint, so we manually right here write it
    // to the proper value - it must be `1`
    if compiled_circuit.lazy_init_address_aux_vars.len() > 0 {
        for lazy_init_address_aux_vars in compiled_circuit.lazy_init_address_aux_vars.iter() {
            let ShuffleRamAuxComparisonSet { final_borrow, .. } = *lazy_init_address_aux_vars;

            let row_of_interest = trace_len - 2; // one before last
            let mut exec_trace_view = exec_trace.row_view(row_of_interest..row_of_interest + 1);
            let (witness_row, _) = exec_trace_view
                .current_row()
                .split_at_mut(num_witness_columns);
            let ColumnAddress::WitnessSubtree(offset) = final_borrow else {
                unreachable!()
            };
            witness_row[offset] = Mersenne31Field::ONE;
        }
    }

    let optimal_folding =
        crate::definitions::OPTIMAL_FOLDING_PROPERTIES[trace_len.trailing_zeros() as usize];

    let delegation_processing_type = delegation_processing_type.unwrap_or(0);
    assert_eq!(public_inputs.len(), compiled_circuit.public_inputs.len());
    // first we commit setup, external challenges, extra compiler-defined variables and public inputs

    let mut transcript_input = vec![];
    // we should commit all "external" variables,
    // that are still part of the circuit, even though they are not formally the public input

    // circuit sequence and delegation type
    transcript_input.push(delegation_processing_type as u32);
    // public inputs
    transcript_input.extend(public_inputs.iter().map(|el| el.to_reduced_u32()));
    // commit our setup
    flatten_merkle_caps_into(&setup_precomputations.trees, &mut transcript_input);
    transcript_input.extend(external_challenges.memory_argument.flatten().into_iter());
    if let Some(delegation_argument_challenges) = external_challenges.delegation_argument.as_ref() {
        transcript_input.extend(delegation_argument_challenges.flatten().into_iter());
    }
    if let Some(machine_state_challenges) = external_challenges
        .machine_state_permutation_argument
        .as_ref()
    {
        transcript_input.extend(machine_state_challenges.flatten().into_iter());
    }

    let stage_1_output = stage1::prover_stage_1(
        compiled_circuit,
        exec_trace,
        num_witness_columns,
        precomputations,
        lde_precomputations,
        lde_factor,
        &optimal_folding,
        worker,
    );

    // and we can commit witness and memory trees
    flatten_merkle_caps_into(&stage_1_output.witness_tree, &mut transcript_input);
    flatten_merkle_caps_into(&stage_1_output.memory_tree, &mut transcript_input);

    let cached_data_values = self::cached_data::ProverCachedData::new(
        compiled_circuit,
        external_challenges,
        trace_len,
        0,
        delegation_processing_type,
    );

    let mut seed = Transcript::commit_initial(&transcript_input);

    let stage_2_output = stage2::prover_stage_2_for_unrolled_circuit(
        &mut seed,
        compiled_circuit,
        &cached_data_values,
        &stage_1_output,
        &setup_precomputations,
        lookup_mapping,
        precomputations,
        lde_precomputations,
        lde_factor,
        &optimal_folding,
        worker,
    );

    let mut transcript_input = vec![];
    flatten_merkle_caps_into(&stage_2_output.trees, &mut transcript_input);
    // and memory grand product
    transcript_input.extend(
        stage_2_output
            .grand_product_accumulator
            .into_coeffs_in_base()
            .map(|el: Mersenne31Field| el.to_reduced_u32()),
    );
    // and delegation argument scalar
    if compiled_circuit
        .stage_2_layout
        .delegation_processing_aux_poly
        .is_some()
    {
        transcript_input.extend(
            stage_2_output
                .sum_over_delegation_poly
                .into_coeffs_in_base()
                .map(|el: Mersenne31Field| el.to_reduced_u32()),
        );
    }
    Transcript::commit_with_seed(&mut seed, &transcript_input);

    let domain_index = if DEBUG_QUOTIENT { 0 } else { 1 };
    let tau = lde_precomputations.domain_bound_precomputations[domain_index]
        .as_ref()
        .unwrap()
        .coset_offset;

    if DEBUG_QUOTIENT {
        assert_eq!(tau, Mersenne31Complex::ONE);
    }

    let compiled_constraints = CompiledConstraintsForDomain::from_compiled_circuit(
        compiled_circuit,
        tau,
        trace_len as u32,
    );

    let stage_3_output = stage3::prover_stage_3_for_unrolled_circuit(
        &mut seed,
        compiled_circuit,
        &cached_data_values,
        &compiled_constraints,
        public_inputs,
        &stage_1_output,
        &stage_2_output,
        &setup_precomputations,
        vec![],
        vec![],
        aux_boundary_values,
        precomputations,
        lde_precomputations,
        lde_factor,
        &optimal_folding,
        worker,
    );

    let mut transcript_input = vec![];
    flatten_merkle_caps_into(&stage_3_output.trees, &mut transcript_input);
    Transcript::commit_with_seed(&mut seed, &transcript_input);

    // now we should compute deep-poly

    let stage_4_output = stage4::prover_stage_4(
        &mut seed,
        compiled_circuit,
        &cached_data_values,
        &stage_1_output,
        &stage_2_output,
        &stage_3_output,
        &setup_precomputations,
        precomputations,
        lde_precomputations,
        lde_factor,
        &optimal_folding,
        worker,
    );

    let mut transcript_input = vec![];
    flatten_merkle_caps_into(&stage_4_output.trees, &mut transcript_input);
    Transcript::commit_with_seed(&mut seed, &transcript_input);

    let stage_5_output = stage5::prover_stage_5(
        &mut seed,
        &stage_4_output,
        precomputations,
        lde_factor,
        &optimal_folding,
        num_queries,
        worker,
    );

    #[cfg(feature = "debug_logs")]
    println!("Searching for PoW for {} bits", pow_bits);

    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();
    let (mut seed, pow_challenge) = Transcript::search_pow(&seed, pow_bits, worker);
    #[cfg(feature = "timing_logs")]
    println!("PoW for {} took {:?}", pow_bits, now.elapsed());

    let mut queries = Vec::with_capacity(num_queries);
    let tree_index_bits = trace_len.trailing_zeros();
    let tree_index_mask = (1 << tree_index_bits) - 1;
    let coset_index_bits = lde_factor.trailing_zeros();
    let query_index_bits = tree_index_bits + coset_index_bits;
    let num_required_bits = (query_index_bits as usize) * num_queries;
    let num_required_words =
        num_required_bits.next_multiple_of(u32::BITS as usize) / (u32::BITS as usize);
    // we used 1 top word for PoW
    let num_required_words_padded =
        (num_required_words + 1).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);

    let mut source = vec![0u32; num_required_words_padded];
    Transcript::draw_randomness(&mut seed, &mut source);
    // Remember - skip top word
    let mut bit_source = BitSource::new(source[1..].to_vec());

    for _i in 0..num_queries {
        let query_index = assemble_query_index(query_index_bits as usize, &mut bit_source);
        let tree_index = query_index & tree_index_mask;
        let coset_index = query_index >> tree_index_bits;
        // now we need to make queries to witness, memory, setup, stage_2, quotient, initial FRI oracle, and intermediate
        // FRI oracles
        let witness_query = produce_query_from_row_major_source_with_range(
            query_index,
            &stage_1_output.ldes[coset_index],
            0..num_witness_columns,
            &stage_1_output.witness_tree[coset_index],
            tree_index,
            false,
        );
        let memory_query = produce_query_from_row_major_source_with_range(
            query_index,
            &stage_1_output.ldes[coset_index],
            num_witness_columns..trace_width,
            &stage_1_output.memory_tree[coset_index],
            tree_index,
            false,
        );
        let setup_query = produce_query_from_row_major_source(
            query_index,
            &setup_precomputations.ldes[coset_index],
            &setup_precomputations.trees[coset_index],
            tree_index,
            false,
        );
        let stage_2_query = produce_query_from_row_major_source(
            query_index,
            &stage_2_output.ldes[coset_index],
            &stage_2_output.trees[coset_index],
            tree_index,
            false,
        );
        let quotient_query = produce_query_from_row_major_source(
            query_index,
            &stage_3_output.ldes[coset_index],
            &stage_3_output.trees[coset_index],
            tree_index,
            false,
        );
        // here query will take care of the index
        let combine_by = 1 << optimal_folding.folding_sequence[0];
        let initial_fri_query = produce_query_from_column_major_source(
            query_index,
            &stage_4_output.ldes[coset_index],
            &stage_4_output.trees[coset_index],
            tree_index,
            combine_by,
            true,
        );

        let mut intermediate_fri_queries = vec![];
        let mut tree_index = tree_index;
        let num_elements = stage_5_output.fri_oracles.len();
        for (i, intermediate_oracle) in stage_5_output.fri_oracles.iter().enumerate() {
            let last_oracle = i == num_elements - 1;
            if last_oracle == false || stage_5_output.expose_all_leafs_at_last_step_instead == false
            {
                // here index needs to be adjusted
                tree_index >>= optimal_folding.folding_sequence[i];
                let combine_by = 1 << optimal_folding.folding_sequence[i + 1];
                let fri_intermedaite_query = produce_query_from_column_major_source(
                    query_index,
                    &intermediate_oracle.ldes[coset_index],
                    &intermediate_oracle.trees[coset_index],
                    tree_index,
                    combine_by,
                    true,
                );
                intermediate_fri_queries.push(fri_intermedaite_query);
            } else {
                // there is no query to make - all leafs will be in plain text, and we just need to access one
            }
        }

        let query_set = QuerySet {
            witness_query,
            memory_query,
            setup_query,
            stage_2_query,
            quotient_query,
            initial_fri_query,
            intermediate_fri_queries,
        };

        queries.push(query_set);
    }

    let dump_fn = |caps: &[T]| {
        let mut result = Vec::with_capacity(caps.len());
        for el in caps.iter() {
            result.push(el.get_cap());
        }

        result
    };

    let witness_tree_caps = dump_fn(&stage_1_output.witness_tree);
    let memory_tree_caps = dump_fn(&stage_1_output.memory_tree);
    let setup_tree_caps = dump_fn(&setup_precomputations.trees);
    let stage_2_tree_caps = dump_fn(&stage_2_output.trees);
    let quotient_tree_caps = dump_fn(&stage_3_output.trees);
    let deep_poly_caps = dump_fn(&stage_4_output.trees);
    let intermediate_fri_oracle_caps: Vec<_> =
        if stage_5_output.expose_all_leafs_at_last_step_instead == false {
            stage_5_output
                .fri_oracles
                .iter()
                .map(|el| dump_fn(&el.trees))
                .collect()
        } else {
            let num_to_take = stage_5_output.fri_oracles.len() - 1;

            stage_5_output
                .fri_oracles
                .iter()
                .take(num_to_take)
                .map(|el| dump_fn(&el.trees))
                .collect()
        };
    let last_fri_step_plain_leaf_values: Vec<_> =
        if stage_5_output.expose_all_leafs_at_last_step_instead {
            stage_5_output.last_fri_step_plain_leaf_values.clone()
        } else {
            vec![]
        };

    let delegation_argument_accumulator = if cached_data_values.execute_delegation_argument {
        Some(stage_2_output.sum_over_delegation_poly)
    } else {
        None
    };

    let proof = UnrolledModeProof {
        external_challenges: *external_challenges,
        public_inputs: public_inputs.to_vec(),
        witness_tree_caps,
        memory_tree_caps,
        setup_tree_caps,
        stage_2_tree_caps,
        memory_grand_product_accumulator: stage_2_output.grand_product_accumulator,
        delegation_argument_accumulator,
        quotient_tree_caps,
        evaluations_at_random_points: stage_4_output.values_at_z.clone(),
        deep_poly_caps,
        intermediate_fri_oracle_caps,
        last_fri_step_plain_leaf_values,
        final_monomial_form: stage_5_output.final_monomials.clone(),
        queries,
        pow_nonce: pow_challenge,
        aux_boundary_values: aux_boundary_values.to_vec(),
        delegation_type: cached_data_values.delegation_type.to_reduced_u32() as u16,
    };

    // Temporary
    let prover_data = ProverData {
        external_values: ExternalValues {
            challenges: Default::default(),
            aux_boundary_values: Default::default(),
        },
        public_inputs: public_inputs.to_vec(),
        stage_1_result: stage_1_output,
        stage_2_result: stage_2_output,
        quotient_commitment_result: stage_3_output,
        deep_poly_result: stage_4_output,
        fri_result: stage_5_output,
    };

    (prover_data, proof)
}
