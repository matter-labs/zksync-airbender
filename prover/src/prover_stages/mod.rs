use super::*;
use crate::definitions::*;
use crate::merkle_trees::DefaultTreeConstructor;
use crate::merkle_trees::MerkleTreeConstructor;
use ::field::*;
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use cs::definitions::*;
use cs::one_row_compiler::*;
use cs::tables::*;
use fft::*;
use merkle_trees::MerkleTreeCapVarLength;
use query_producer::assemble_query_index;
use query_producer::produce_query_from_column_major_source;
use query_producer::produce_query_from_row_major_source;
use query_producer::produce_query_from_row_major_source_with_range;
use query_producer::BitSource;
use stage1::compute_wide_ldes;
use stage1::FirstStageOutput;
use stage2::SecondStageOutput;
use stage3::ThirdStageOutput;
use stage4::FourthStageOutput;
use stage5::FifthStageOutput;
use stage5::Query;
use std::alloc::Allocator;
use trace_holder::*;
use transcript::Seed;
use worker::Worker;

pub mod cached_data;
pub mod query_producer;
pub mod stage1;
pub mod stage2;
pub mod stage3;
pub mod stage4;
pub mod stage5;

pub(crate) mod stage2_utils;

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct Proof {
    pub external_values: ExternalValues,
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
    pub circuit_sequence: u16,
    pub delegation_type: u16,
}

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct QuerySet {
    pub witness_query: Query,
    pub memory_query: Query,
    pub setup_query: Query,
    pub stage_2_query: Query,
    pub quotient_query: Query,
    pub initial_fri_query: Query,
    pub intermediate_fri_queries: Vec<Query>,
}

#[derive(Clone, Debug)]
pub struct CosetBoundTracePart<const N: usize, A: Allocator + Clone> {
    pub trace: RowMajorTrace<Mersenne31Field, N, A>,
    pub tau: Mersenne31Complex,
}

#[derive(Clone, Debug)]
pub struct CosetBoundColumnMajorTracePart<A: Allocator + Clone> {
    pub trace: ColumnMajorTrace<Mersenne31Quartic, A>,
    pub tau: Mersenne31Complex,
}

pub struct SetupPrecomputations<const N: usize, A: GoodAllocator, T: MerkleTreeConstructor> {
    pub ldes: Vec<CosetBoundTracePart<N, A>>,
    pub trees: Vec<T>,
}

#[inline(always)]
pub(crate) fn compute_aggregated_key_value<const N: usize>(
    base_value: Mersenne31Field,
    key_values_to_aggregate: [Mersenne31Field; N],
    aggregation_challenges: [Mersenne31Quartic; N],
    additive_part: Mersenne31Quartic,
) -> Mersenne31Quartic {
    let mut result = additive_part;
    result.add_assign_base(&base_value);
    for (a, b) in key_values_to_aggregate
        .into_iter()
        .zip(aggregation_challenges.into_iter())
    {
        let mut t = b;
        t.mul_assign_by_base(&a);
        result.add_assign(&t);
    }

    result
}

#[inline(always)]
pub(crate) fn quotient_compute_aggregated_key_value<const N: usize>(
    base_value: Mersenne31Field,
    key_values_to_aggregate: [Mersenne31Field; N],
    aggregation_challenges: [Mersenne31Quartic; N],
    additive_part: Mersenne31Quartic,
    tau_in_domain_by_half: Mersenne31Complex,
) -> Mersenne31Quartic {
    let mut denom = Mersenne31Quartic::from_base(base_value);
    for (a, b) in key_values_to_aggregate
        .into_iter()
        .zip(aggregation_challenges.into_iter())
    {
        let mut t = b;
        t.mul_assign_by_base(&a);
        denom.add_assign(&t);
    }

    // all terms are linear over witness
    denom.mul_assign_by_base(&tau_in_domain_by_half);

    denom.add_assign(&additive_part);

    denom
}

#[inline(always)]
pub(crate) fn quotient_compute_aggregated_key_value_in_ext2<const N: usize>(
    base_value: Mersenne31Complex,
    key_values_to_aggregate: [Mersenne31Complex; N],
    aggregation_challenges: [Mersenne31Quartic; N],
    additive_part: Mersenne31Quartic,
) -> Mersenne31Quartic {
    let mut denom = Mersenne31Quartic::from_base(base_value);
    for (a, b) in key_values_to_aggregate
        .into_iter()
        .zip(aggregation_challenges.into_iter())
    {
        let mut t = b;
        t.mul_assign_by_base(&a);
        denom.add_assign(&t);
    }

    denom.add_assign(&additive_part);

    denom
}

#[inline(always)]
pub(crate) unsafe fn add_quotient_term_contribution_in_ext2(
    other_challenges_ptr: &mut *const Mersenne31Quartic,
    term_contribution: Mersenne31Complex,
    quotient_term: &mut Mersenne31Quartic,
) {
    let mut challenge = (*other_challenges_ptr).read();
    challenge.mul_assign_by_base(&term_contribution);
    quotient_term.add_assign(&challenge);
    *other_challenges_ptr = other_challenges_ptr.add(1);
}

#[inline(always)]
pub(crate) unsafe fn add_quotient_term_contribution_in_ext4(
    other_challenges_ptr: &mut *const Mersenne31Quartic,
    term_contribution: Mersenne31Quartic,
    quotient_term: &mut Mersenne31Quartic,
) {
    let mut challenge = (*other_challenges_ptr).read();
    challenge.mul_assign(&term_contribution);
    quotient_term.add_assign(&challenge);
    *other_challenges_ptr = other_challenges_ptr.add(1);
}

pub struct ProverData<const N: usize, A: GoodAllocator, T: MerkleTreeConstructor> {
    pub external_values: ExternalValues,
    pub public_inputs: Vec<Mersenne31Field>,
    pub stage_1_result: FirstStageOutput<N, A, T>,
    pub stage_2_result: SecondStageOutput<N, A, T>,
    pub quotient_commitment_result: ThirdStageOutput<N, A, T>,
    pub deep_poly_result: FourthStageOutput<N, A, T>,
    pub fri_result: FifthStageOutput<A, T>,
}

impl<const N: usize, A: GoodAllocator, T: MerkleTreeConstructor> SetupPrecomputations<N, A, T> {
    pub fn from_tables_and_trace_len(
        table_driver: &TableDriver<Mersenne31Field>,
        trace_len: usize,
        setup_layout: &SetupLayout,
        twiddles: &Twiddles<Mersenne31Complex, A>,
        lde_precomputations: &LdePrecomputations<A>,
        lde_factor: usize,
        _tree_cap_size: usize,
        worker: &Worker,
    ) -> Self {
        assert!(trace_len.is_power_of_two());

        let optimal_folding =
            crate::definitions::OPTIMAL_FOLDING_PROPERTIES[trace_len.trailing_zeros() as usize];
        let subtree_cap_size = (1 << optimal_folding.total_caps_size_log2) / lde_factor;
        assert!(subtree_cap_size > 0);

        let mut main_domain_trace =
            RowMajorTrace::new_zeroed_for_size(trace_len, setup_layout.total_width, A::default());

        let table_encoding_capacity_per_tuple = trace_len - 1;

        let mut num_table_subsets =
            table_driver.total_tables_len / table_encoding_capacity_per_tuple;
        if table_driver.total_tables_len % table_encoding_capacity_per_tuple != 0 {
            num_table_subsets += 1;
        }

        assert_eq!(
            num_table_subsets,
            setup_layout.generic_lookup_setup_columns.num_elements()
        );

        // dump tables
        let all_generic_tables = table_driver.dump_tables();
        assert_eq!(all_generic_tables.len(), table_driver.total_tables_len);

        let range_check_16_table: Vec<_> = (0..(1 << 16))
            .map(|el| Mersenne31Field(el as u32))
            .collect();

        let timestamp_range_check_table: Vec<_> = (0..(1 << TIMESTAMP_COLUMNS_NUM_BITS))
            .map(|el| Mersenne31Field(el as u32))
            .collect();

        // chunk generic tables encoding
        let generic_tables_chunks: Vec<_> = all_generic_tables
            .chunks(table_encoding_capacity_per_tuple)
            .collect();
        assert_eq!(
            generic_tables_chunks.len(),
            setup_layout.generic_lookup_setup_columns.num_elements()
        );

        let range_check_16_table_content_len = range_check_16_table.len();
        let range_check_16_table_content_ref = &range_check_16_table;

        let timestamp_range_check_table_content_len = timestamp_range_check_table.len();
        let timestamp_range_check_table_content_ref = &timestamp_range_check_table;

        let all_generic_tables_ref = &generic_tables_chunks;

        worker.scope(trace_len - 1, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let range = chunk_start..(chunk_start + chunk_size);
                let mut trace_view = main_domain_trace.row_view(range);

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    for i in 0..chunk_size {
                        let absolute_row_idx = chunk_start + i;

                        let trace_view_row = trace_view.current_row();

                        if absolute_row_idx < range_check_16_table_content_len {
                            trace_view_row[setup_layout.range_check_16_setup_column.start()] =
                                range_check_16_table_content_ref[absolute_row_idx];
                        }

                        if absolute_row_idx < timestamp_range_check_table_content_len {
                            trace_view_row
                                [setup_layout.timestamp_range_check_setup_column.start()] =
                                timestamp_range_check_table_content_ref[absolute_row_idx];
                        }

                        for (tuple_idx, encoding_chunk) in all_generic_tables_ref.iter().enumerate()
                        {
                            if absolute_row_idx < encoding_chunk.len() {
                                let table_row = encoding_chunk[absolute_row_idx];
                                let range = setup_layout
                                    .generic_lookup_setup_columns
                                    .get_range(tuple_idx);
                                trace_view_row[range].copy_from_slice(&table_row);
                            }
                        }

                        if setup_layout.timestamp_setup_columns.num_elements() > 0 {
                            let timestamp = (absolute_row_idx as u64) + 1;
                            let timestamp_shifted = timestamp << NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP;
                            let timestamp_low =
                                timestamp_shifted & ((1 << TIMESTAMP_COLUMNS_NUM_BITS) - 1);
                            let timestamp_high = timestamp_shifted >> TIMESTAMP_COLUMNS_NUM_BITS;

                            trace_view_row[setup_layout.timestamp_setup_columns.start()] =
                                Mersenne31Field(timestamp_low as u32);
                            trace_view_row[setup_layout.timestamp_setup_columns.start() + 1] =
                                Mersenne31Field(timestamp_high as u32);
                        }

                        trace_view.advance_row();
                    }
                });
            }
        });

        // NOTE: we do not use last row of the setup (and in general last of of circuit),
        // and we must adjust it to be c0 == 0
        adjust_to_zero_c0_var_length(&mut main_domain_trace, 0..setup_layout.total_width, worker);

        // LDE them
        let ldes = compute_wide_ldes(
            main_domain_trace,
            twiddles,
            lde_precomputations,
            0,
            lde_factor,
            worker,
        );

        assert_eq!(ldes.len(), lde_factor);

        let mut trees = Vec::with_capacity(lde_factor);
        for domain in ldes.iter() {
            let tree = T::construct_for_coset(&domain.trace, subtree_cap_size, true, worker);
            trees.push(tree);
        }

        Self { ldes, trees }
    }
}

use transcript::Blake2sTranscript;

pub type Transcript = Blake2sTranscript;

pub fn prove<const N: usize, A: GoodAllocator>(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    public_inputs: &[Mersenne31Field],
    external_values: &ExternalValues,
    witness_eval_data: WitnessEvaluationData<N, A>,
    setup_precomputations: &SetupPrecomputations<N, A, DefaultTreeConstructor>,
    precomputations: &Twiddles<Mersenne31Complex, A>,
    lde_precomputations: &LdePrecomputations<A>,
    circuit_sequence: usize,
    delegation_processing_type: Option<u16>,
    lde_factor: usize,
    _tree_cap_size: usize,
    num_queries: usize,
    pow_bits: u32,
    worker: &Worker,
) -> (ProverData<N, A, DefaultTreeConstructor>, Proof) {
    prove_configured::<N, A, DefaultTreeConstructor>(
        compiled_circuit,
        public_inputs,
        external_values,
        witness_eval_data,
        setup_precomputations,
        precomputations,
        lde_precomputations,
        circuit_sequence,
        delegation_processing_type,
        lde_factor,
        _tree_cap_size,
        num_queries,
        pow_bits,
        worker,
    )
}

pub fn prove_configured<const N: usize, A: GoodAllocator, T: MerkleTreeConstructor>(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    public_inputs: &[Mersenne31Field],
    external_values: &ExternalValues,
    witness_eval_data: WitnessEvaluationData<N, A>,
    setup_precomputations: &SetupPrecomputations<N, A, T>,
    precomputations: &Twiddles<Mersenne31Complex, A>,
    lde_precomputations: &LdePrecomputations<A>,
    circuit_sequence: usize,
    delegation_processing_type: Option<u16>,
    lde_factor: usize,
    _tree_cap_size: usize,
    num_queries: usize,
    pow_bits: u32,
    worker: &Worker,
) -> (ProverData<N, A, T>, Proof) {
    let WitnessEvaluationData {
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

    // VERY important - we will use the fact that final borrow value is unconstrained
    // when we will define lazy init/teardown padding constraint, so we manually right here write it
    // to the proper value - it must be `1`
    if let Some(lazy_init_address_aux_vars) = compiled_circuit.lazy_init_address_aux_vars {
        let ShuffleRamAuxComparisonSet { final_borrow, .. } = lazy_init_address_aux_vars;

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

    let optimal_folding =
        crate::definitions::OPTIMAL_FOLDING_PROPERTIES[trace_len.trailing_zeros() as usize];

    assert!(circuit_sequence <= u16::MAX as usize);
    let delegation_processing_type = delegation_processing_type.unwrap_or(0);
    assert_eq!(public_inputs.len(), compiled_circuit.public_inputs.len());
    // first we commit setup, external challenges, extra compiler-defined variables and public inputs

    let mut transcript_input = vec![];
    // we should commit all "external" variables,
    // that are still part of the circuit, even though they are not formally the public input

    // circuit sequence and delegation type
    transcript_input.push(circuit_sequence as u32);
    transcript_input.push(delegation_processing_type as u32);
    // public inputs
    transcript_input.extend(public_inputs.iter().map(|el| el.to_reduced_u32()));
    // commit our setup
    flatten_merkle_caps_into(&setup_precomputations.trees, &mut transcript_input);
    transcript_input.extend(
        external_values
            .challenges
            .memory_argument
            .flatten()
            .into_iter(),
    );
    if let Some(delegation_argument_challenges) =
        external_values.challenges.delegation_argument.as_ref()
    {
        transcript_input.extend(delegation_argument_challenges.flatten().into_iter());
    }
    if compiled_circuit
        .memory_layout
        .shuffle_ram_inits_and_teardowns
        .is_some()
    {
        transcript_input.extend(external_values.aux_boundary_values.flatten().into_iter());
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
        external_values,
        trace_len,
        circuit_sequence,
        delegation_processing_type,
    );

    let mut seed = Transcript::commit_initial(&transcript_input);

    let stage_2_output = stage2::prover_stage_2(
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

    // TODO: move to precomputations

    let domain_index = if DEBUG_QUOTIENT { 0 } else { 1 };
    let tau = lde_precomputations.domain_bound_precomputations[domain_index]
        .as_ref()
        .unwrap()
        .coset_offset;

    #[cfg(feature = "debug_logs")]
    dbg!(tau);

    if DEBUG_QUOTIENT {
        assert_eq!(tau, Mersenne31Complex::ONE);
    }

    let compiled_constraints = CompiledConstraintsForDomain::from_compiled_circuit(
        compiled_circuit,
        tau,
        trace_len as u32,
    );

    let stage_3_output = stage3::prover_stage_3(
        &mut seed,
        compiled_circuit,
        &cached_data_values,
        &compiled_constraints,
        public_inputs,
        &stage_1_output,
        &stage_2_output,
        &setup_precomputations,
        external_values,
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

    #[cfg(feature = "debug_logs")]
    {
        dbg!(query_index_bits);
        dbg!(num_required_bits);
        dbg!(num_required_words);
        dbg!(num_required_words_padded);
    }

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

    let proof = Proof {
        external_values: *external_values,
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
        circuit_sequence: circuit_sequence as u16,
        delegation_type: cached_data_values.delegation_type.to_reduced_u32() as u16,
    };

    let prover_data = ProverData {
        external_values: *external_values,
        public_inputs: public_inputs.to_vec(),
        stage_1_result: stage_1_output,
        stage_2_result: stage_2_output,
        quotient_commitment_result: stage_3_output,
        deep_poly_result: stage_4_output,
        fri_result: stage_5_output,
    };

    (prover_data, proof)
}

pub fn flatten_merkle_caps_into<T: MerkleTreeConstructor>(trees: &[T], dst: &mut Vec<u32>) {
    for subtree in trees.iter() {
        for cap_element in subtree.get_cap().cap.iter() {
            dst.extend_from_slice(cap_element);
        }
    }
}

pub fn flatten_merkle_caps<T: MerkleTreeConstructor>(trees: &[T]) -> Vec<u32> {
    let mut result = vec![];
    flatten_merkle_caps_into(trees, &mut result);

    result
}

pub fn bitreverse_and_change_trace_form<const N: usize, A: GoodAllocator>(
    source: &RowMajorTrace<Mersenne31Field, N, A>,
    worker: &Worker,
) -> ColumnMajorTrace<Mersenne31Quartic, A> {
    let trace_len = source.len();
    assert_eq!(source.width(), 4); // one complex field element
    let mut dst =
        ColumnMajorTrace::<Mersenne31Quartic, A>::new_uninit_for_size(trace_len, 1, A::default());
    let mut it = dst.columns_iter_mut();
    let mut dst_column = it.next().unwrap();
    assert_eq!(dst_column.len(), trace_len);
    let num_index_bits = trace_len.trailing_zeros();

    unsafe {
        worker.scope(trace_len, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let (dst_chunk, rest) = dst_column.split_at_mut(chunk_size);
                dst_column = rest;

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let mut dst_ptr = dst_chunk.as_mut_ptr();
                    for i in 0..chunk_size {
                        let absolute_row_idx = chunk_start + i;
                        let input_index = bitreverse_index(absolute_row_idx, num_index_bits);
                        // we work sequentially over dst, and non-sequentially over source
                        let src_row = source
                            .get_row(input_index)
                            .as_ptr()
                            .cast::<Mersenne31Quartic>();
                        debug_assert!(src_row.is_aligned());
                        dst_ptr.write(src_row.read());

                        dst_ptr = dst_ptr.add(1);
                    }
                });
            }
        });
    }
    drop(it);

    dst
}
