use super::*;

// standalone helpers needed by GPU witness generation
pub fn get_timestamp_range_check_lookup_accesses(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
) -> (
    Vec<LookupWidth1SourceDestInformationForExpressions<Mersenne31Field>>,
    Vec<LookupWidth1SourceDestInformationForExpressions<Mersenne31Field>>,
) {
    let timestamp_range_check_dst = compiled_circuit
        .stage_2_layout
        .intermediate_polys_for_timestamp_range_checks
        .base_field_oracles
        .clone();
    assert_eq!(
        compiled_circuit
            .witness_layout
            .timestamp_range_check_lookup_expressions
            .len()
            / 2,
        timestamp_range_check_dst.num_elements()
    );
    assert_eq!(
        compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_timestamp_range_checks
            .ext_4_field_oracles
            .num_elements(),
        timestamp_range_check_dst.num_elements(),
    );

    let mut timestamp_range_check_dst_it = timestamp_range_check_dst.iter().zip(
        compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_timestamp_range_checks
            .ext_4_field_oracles
            .iter(),
    );

    let mut timestamp_range_check_16_exprs_it = compiled_circuit
        .witness_layout
        .timestamp_range_check_lookup_expressions
        .iter();

    let offset = compiled_circuit
        .witness_layout
        .offset_for_special_shuffle_ram_timestamps_range_check_expressions;
    let mut timestamp_range_check_width_1_lookups_access_via_expressions = vec![];
    let src = &compiled_circuit
        .witness_layout
        .timestamp_range_check_lookup_expressions[..offset];
    assert!(src.len() % 2 == 0);
    for [a, b] in src.as_chunks::<2>().0.iter() {
        let (base_col, ext_col) = timestamp_range_check_dst_it.next().unwrap();
        assert_eq!(base_col.len(), 1);
        let dst_col = base_col.start;
        assert_eq!(ext_col.len(), 4);
        let ext_start = ext_col.start;

        let inf = LookupWidth1SourceDestInformationForExpressions {
            a_expr: a.clone(),
            b_expr: b.clone(),
            base_field_quadratic_oracle_col: dst_col,
            ext4_field_inverses_columns_start: ext_start,
        };

        // double check
        let expr = timestamp_range_check_16_exprs_it.next().unwrap();
        let LookupExpression::Expression(..) = expr else {
            panic!("first one must encounter simple lookup expressions");
        };
        let expr = timestamp_range_check_16_exprs_it.next().unwrap();
        let LookupExpression::Expression(..) = expr else {
            panic!("first one must encounter simple lookup expressions");
        };

        timestamp_range_check_width_1_lookups_access_via_expressions.push(inf);
    }

    let mut timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram = vec![];
    let src = &compiled_circuit
        .witness_layout
        .timestamp_range_check_lookup_expressions[offset..];
    assert!(src.len() % 2 == 0);
    for [a, b] in src.as_chunks::<2>().0.iter() {
        let (base_col, ext_col) = timestamp_range_check_dst_it.next().unwrap();
        assert_eq!(base_col.len(), 1);
        let dst_col = base_col.start;
        assert_eq!(ext_col.len(), 4);
        let ext_start = ext_col.start;

        let inf = LookupWidth1SourceDestInformationForExpressions {
            a_expr: a.clone(),
            b_expr: b.clone(),
            base_field_quadratic_oracle_col: dst_col,
            ext4_field_inverses_columns_start: ext_start,
        };

        // double check
        let expr = timestamp_range_check_16_exprs_it.next().unwrap();
        let LookupExpression::Expression(..) = expr else {
            panic!("first one must encounter simple lookup expressions");
        };
        let expr = timestamp_range_check_16_exprs_it.next().unwrap();
        let LookupExpression::Expression(..) = expr else {
            panic!("first one must encounter simple lookup expressions");
        };

        timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram.push(inf);
    }

    assert!(timestamp_range_check_dst_it.next().is_none());
    assert!(timestamp_range_check_16_exprs_it.next().is_none());

    (
        timestamp_range_check_width_1_lookups_access_via_expressions,
        timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram,
    )
}

pub fn get_range_check_16_lookup_accesses(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
) -> (
    Vec<LookupWidth1SourceDestInformation>,
    Vec<LookupWidth1SourceDestInformationForExpressions<Mersenne31Field>>,
) {
    let range_check_16_dst = compiled_circuit
        .stage_2_layout
        .intermediate_polys_for_range_check_16
        .base_field_oracles
        .clone();
    assert_eq!(
        compiled_circuit
            .witness_layout
            .range_check_16_lookup_expressions
            .len()
            / 2,
        range_check_16_dst.num_elements()
    );
    assert_eq!(
        compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_range_check_16
            .ext_4_field_oracles
            .num_elements(),
        range_check_16_dst.num_elements(),
    );

    let mut range_check_16_dst_it = range_check_16_dst.iter().zip(
        compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_range_check_16
            .ext_4_field_oracles
            .iter(),
    );
    let mut range_check_16_exprs_it = compiled_circuit
        .witness_layout
        .range_check_16_lookup_expressions
        .iter();

    assert!(
        compiled_circuit
            .witness_layout
            .range_check_16_columns
            .num_elements()
            % 2
            == 0
    );

    assert!(
        compiled_circuit
            .witness_layout
            .range_check_16_lookup_expressions
            .len()
            % 2
            == 0
    );

    let mut range_check_16_width_1_lookups_access = vec![];
    for i in 0..compiled_circuit
        .witness_layout
        .range_check_16_columns
        .num_elements()
        / 2
    {
        let (base_col, ext_col) = range_check_16_dst_it.next().unwrap();
        assert_eq!(base_col.len(), 1);
        let dst_col = base_col.start;
        assert_eq!(ext_col.len(), 4);
        let ext_start = ext_col.start;
        let a_range = &compiled_circuit
            .witness_layout
            .range_check_16_columns
            .get_range(2 * i);
        assert_eq!(a_range.len(), 1);
        let b_range = &compiled_circuit
            .witness_layout
            .range_check_16_columns
            .get_range(2 * i + 1);
        assert_eq!(b_range.len(), 1);
        let inf = LookupWidth1SourceDestInformation {
            a_col: a_range.start,
            b_col: b_range.start,
            base_field_quadratic_oracle_col: dst_col,
            ext4_field_inverses_columns_start: ext_start,
        };

        // double check
        let expr = range_check_16_exprs_it.next().unwrap();
        let LookupExpression::Variable(..) = expr else {
            panic!("first one must encounter simple lookup expressions");
        };
        let expr = range_check_16_exprs_it.next().unwrap();
        let LookupExpression::Variable(..) = expr else {
            panic!("first one must encounter simple lookup expressions");
        };

        range_check_16_width_1_lookups_access.push(inf);
    }

    // map the rest
    let mut range_check_16_width_1_lookups_access_via_expressions = vec![];
    let src = &compiled_circuit
        .witness_layout
        .range_check_16_lookup_expressions[compiled_circuit
        .witness_layout
        .range_check_16_columns
        .num_elements()..];
    assert!(src.len() % 2 == 0);
    for [a, b] in src.as_chunks::<2>().0.iter() {
        let (base_col, ext_col) = range_check_16_dst_it.next().unwrap();
        assert_eq!(base_col.len(), 1);
        let dst_col = base_col.start;
        assert_eq!(ext_col.len(), 4);
        let ext_start = ext_col.start;

        let inf = LookupWidth1SourceDestInformationForExpressions {
            a_expr: a.clone(),
            b_expr: b.clone(),
            base_field_quadratic_oracle_col: dst_col,
            ext4_field_inverses_columns_start: ext_start,
        };

        // double check
        let expr = range_check_16_exprs_it.next().unwrap();
        let LookupExpression::Expression(..) = expr else {
            panic!("first one must encounter simple lookup expressions");
        };
        let expr = range_check_16_exprs_it.next().unwrap();
        let LookupExpression::Expression(..) = expr else {
            panic!("first one must encounter simple lookup expressions");
        };

        range_check_16_width_1_lookups_access_via_expressions.push(inf);
    }

    assert!(range_check_16_dst_it.next().is_none());

    if let Some(_remainder_for_range_check_16) = compiled_circuit
        .stage_2_layout
        .remainder_for_range_check_16
        .as_ref()
    {
        todo!()
        // let offset = range_check_16_dst.num_elements() * 2;
        // let src = offset;
        // let dst = remainder_for_range_check_16.start();
        // remainder_for_width_1_lookups.push((src, dst));
    }

    (
        range_check_16_width_1_lookups_access,
        range_check_16_width_1_lookups_access_via_expressions,
    )
}

#[derive(Clone, Debug)]
pub struct ProverCachedData {
    pub trace_len: usize,

    pub memory_timestamp_high_from_circuit_idx: Mersenne31Field,
    pub delegation_type: Mersenne31Field,

    pub memory_argument_challenges: ExternalMemoryArgumentChallenges,

    pub execute_delegation_argument: bool,
    pub delegation_challenges: ExternalDelegationArgumentChallenges,

    pub process_shuffle_ram_init: bool,
    pub shuffle_ram_inits_and_teardowns: ShuffleRamInitAndTeardownLayout,
    pub lazy_init_address_range_check_16: OptimizedOraclesForLookupWidth1,

    pub handle_delegation_requests: bool,
    pub delegation_request_layout: DelegationRequestLayout,

    pub process_batch_ram_access: bool,
    pub process_registers_and_indirect_access: bool,
    pub delegation_processor_layout: DelegationProcessingLayout,

    pub process_delegations: bool,
    pub delegation_processing_aux_poly: AlignedColumnSet<4>,

    pub num_set_polys_for_memory_shuffle: usize,
    pub offset_for_grand_product_accumulation_poly: usize,

    pub range_check_16_multiplicities_src: usize,
    pub range_check_16_multiplicities_dst: usize,
    pub range_check_16_setup_column: usize,

    pub timestamp_range_check_multiplicities_src: usize,
    pub timestamp_range_check_multiplicities_dst: usize,
    pub timestamp_range_check_setup_column: usize,

    pub generic_lookup_multiplicities_src_start: usize,
    pub generic_lookup_multiplicities_dst_start: usize,
    pub generic_lookup_setup_columns_start: usize,

    pub range_check_16_width_1_lookups_access: Vec<LookupWidth1SourceDestInformation>,
    pub range_check_16_width_1_lookups_access_via_expressions:
        Vec<LookupWidth1SourceDestInformationForExpressions<Mersenne31Field>>,
    pub timestamp_range_check_width_1_lookups_access_via_expressions:
        Vec<LookupWidth1SourceDestInformationForExpressions<Mersenne31Field>>,
    pub timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram:
        Vec<LookupWidth1SourceDestInformationForExpressions<Mersenne31Field>>,

    pub width_3_lookups_with_fixed_col_id: Vec<(
        [LookupExpression<Mersenne31Field>; COMMON_TABLE_WIDTH],
        usize,
        Mersenne31Field,
    )>,
    pub width_3_lookups_with_variable_col_id: Vec<(
        [LookupExpression<Mersenne31Field>; COMMON_TABLE_WIDTH],
        usize,
        usize,
    )>,

    pub memory_accumulator_dst_start: usize,
    pub num_stage_3_quotient_terms: usize,

    pub circuit_sequence: u32,
}

impl ProverCachedData {
    pub fn new(
        compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
        external_values: &ExternalValues,
        trace_len: usize,
        circuit_sequence: usize,
        delegation_processing_type: u16,
    ) -> Self {
        let memory_timestamp_high_from_circuit_idx =
            if compiled_circuit.memory_layout.shuffle_ram_access_sets.len() > 0 {
                let num_bits_in_timestamp_for_index_log_2 = compiled_circuit
                    .memory_layout
                    .shuffle_ram_access_sets
                    .len()
                    .next_power_of_two()
                    .trailing_zeros();
                assert_eq!(
                    num_bits_in_timestamp_for_index_log_2,
                    NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP
                );

                let circuit_sequence_bits_shift = (trace_len.trailing_zeros()
                    + num_bits_in_timestamp_for_index_log_2)
                    - TIMESTAMP_COLUMNS_NUM_BITS;
                assert!(
                    (circuit_sequence << circuit_sequence_bits_shift)
                        < (1 << TIMESTAMP_COLUMNS_NUM_BITS)
                );

                let memory_timestamp_high_from_circuit_idx =
                    Mersenne31Field::from_u64_with_reduction(
                        (circuit_sequence as u64) << circuit_sequence_bits_shift,
                    );

                memory_timestamp_high_from_circuit_idx
            } else {
                assert!(
                    compiled_circuit.memory_layout.batched_ram_accesses.len() > 0
                        || compiled_circuit
                            .memory_layout
                            .register_and_indirect_accesses
                            .len()
                            > 0
                );
                Mersenne31Field::ZERO
            };

        let delegation_type = Mersenne31Field(delegation_processing_type as u32);

        //
        let num_set_polys_for_memory_shuffle =
            if compiled_circuit.memory_layout.shuffle_ram_access_sets.len() > 0 {
                assert!(compiled_circuit
                    .memory_layout
                    .batched_ram_accesses
                    .is_empty());

                assert!(compiled_circuit
                    .memory_layout
                    .register_and_indirect_accesses
                    .is_empty());

                1 + compiled_circuit.memory_layout.shuffle_ram_access_sets.len() + 1
            } else {
                assert!(
                    compiled_circuit.memory_layout.batched_ram_accesses.len() > 0
                        || compiled_circuit
                            .memory_layout
                            .register_and_indirect_accesses
                            .len()
                            > 0
                );

                let num_intermediate_polys_for_batched_ram =
                    compiled_circuit.memory_layout.batched_ram_accesses.len();
                let mut num_intermediate_polys_for_register_accesses = 0;
                for el in compiled_circuit
                    .memory_layout
                    .register_and_indirect_accesses
                    .iter()
                {
                    num_intermediate_polys_for_register_accesses += 1;
                    num_intermediate_polys_for_register_accesses += el.indirect_accesses.len();
                }
                // intermediate accumulators per access + grand product accumulator
                let num_set_polys_for_memory_shuffle = num_intermediate_polys_for_batched_ram
                    + num_intermediate_polys_for_register_accesses
                    + 1;

                num_set_polys_for_memory_shuffle
            };

        let offset_for_grand_product_accumulation_poly = num_set_polys_for_memory_shuffle - 1;

        let process_shuffle_ram_init = compiled_circuit
            .memory_layout
            .shuffle_ram_inits_and_teardowns
            .is_some();
        if process_shuffle_ram_init {
            assert!(compiled_circuit
                .stage_2_layout
                .lazy_init_address_range_check_16
                .is_some());
        }
        let shuffle_ram_inits_and_teardowns = if let Some(shuffle_ram_inits_and_teardowns) =
            compiled_circuit
                .memory_layout
                .shuffle_ram_inits_and_teardowns
        {
            shuffle_ram_inits_and_teardowns
        } else {
            ShuffleRamInitAndTeardownLayout::empty()
        };
        let lazy_init_address_range_check_16 = if let Some(lazy_init_address_range_check_16) =
            compiled_circuit
                .stage_2_layout
                .lazy_init_address_range_check_16
        {
            lazy_init_address_range_check_16
        } else {
            OptimizedOraclesForLookupWidth1::empty()
        };

        if compiled_circuit.memory_layout.batched_ram_accesses.len() > 0
            || compiled_circuit
                .memory_layout
                .register_and_indirect_accesses
                .len()
                > 0
        {
            assert!(compiled_circuit
                .memory_layout
                .delegation_processor_layout
                .is_some());
        }

        let handle_delegation_requests = compiled_circuit
            .memory_layout
            .delegation_request_layout
            .is_some();
        let delegation_request_layout = if let Some(delegation_request_layout) =
            compiled_circuit.memory_layout.delegation_request_layout
        {
            delegation_request_layout
        } else {
            DelegationRequestLayout::empty()
        };

        let process_batch_ram_access =
            compiled_circuit.memory_layout.batched_ram_accesses.len() > 0;
        let process_registers_and_indirect_access = compiled_circuit
            .memory_layout
            .register_and_indirect_accesses
            .len()
            > 0;
        let delegation_processor_layout = if let Some(delegation_processor_layout) =
            compiled_circuit.memory_layout.delegation_processor_layout
        {
            delegation_processor_layout
        } else {
            DelegationProcessingLayout::empty()
        };

        let process_delegations = compiled_circuit
            .memory_layout
            .delegation_processor_layout
            .is_some();
        let delegation_processing_aux_poly = if let Some(delegation_processing_aux_poly) =
            compiled_circuit
                .stage_2_layout
                .delegation_processing_aux_poly
        {
            delegation_processing_aux_poly
        } else {
            AlignedColumnSet::empty()
        };

        let memory_argument_challenges = external_values.challenges.memory_argument;

        let execute_delegation_argument = external_values.challenges.delegation_argument.is_some();
        if execute_delegation_argument {
            assert!(handle_delegation_requests | process_delegations);
        }
        let delegation_challenges =
            if let Some(values) = external_values.challenges.delegation_argument {
                values
            } else {
                ExternalDelegationArgumentChallenges::default()
            };

        #[cfg(feature = "debug_logs")]
        {
            dbg!(execute_delegation_argument);
            dbg!(delegation_challenges);
        }

        // range check 16s
        let (
            range_check_16_width_1_lookups_access,
            range_check_16_width_1_lookups_access_via_expressions,
        ) = get_range_check_16_lookup_accesses(compiled_circuit);

        // timestamp range checks
        let (
            timestamp_range_check_width_1_lookups_access_via_expressions,
            timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram,
        ) = get_timestamp_range_check_lookup_accesses(compiled_circuit);

        // we augment lookup data to include a destination

        let mut dst_iter = compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_generic_lookup
            .iter();

        let mut width_3_lookups_with_fixed_col_id = vec![];
        for lookup in compiled_circuit.witness_layout.width_3_lookups.iter() {
            if let TableIndex::Constant(table_type) = lookup.table_index {
                let src = lookup.input_columns.clone();
                let dst = dst_iter.next().unwrap().start;
                let column_type =
                    Mersenne31Field::from_u64_with_reduction(table_type.to_table_id() as u64);
                width_3_lookups_with_fixed_col_id.push((src, dst, column_type));
            }
        }
        let mut width_3_lookups_with_variable_col_id = vec![];
        for lookup in compiled_circuit.witness_layout.width_3_lookups.iter() {
            if let TableIndex::Variable(table_type) = lookup.table_index {
                let src = lookup.input_columns.clone();
                let dst = dst_iter.next().unwrap().start;
                let ColumnAddress::WitnessSubtree(table_type_idx) = table_type else {
                    panic!();
                };
                width_3_lookups_with_variable_col_id.push((src, dst, table_type_idx));
            }
        }

        assert_eq!(
            width_3_lookups_with_fixed_col_id.len() + width_3_lookups_with_variable_col_id.len(),
            compiled_circuit
                .stage_2_layout
                .intermediate_polys_for_generic_lookup
                .num_elements()
        );
        assert!(dst_iter.next().is_none());

        assert_eq!(
            compiled_circuit
                .stage_2_layout
                .intermediate_polys_for_generic_multiplicities
                .width(),
            4
        );
        assert_eq!(
            compiled_circuit
                .stage_2_layout
                .intermediate_poly_for_range_check_16_multiplicity
                .width(),
            4
        );
        assert_eq!(
            compiled_circuit
                .witness_layout
                .multiplicities_columns_for_range_check_16
                .num_elements(),
            1
        );

        let range_check_16_multiplicities_src = compiled_circuit
            .witness_layout
            .multiplicities_columns_for_range_check_16
            .start();
        let range_check_16_multiplicities_dst = compiled_circuit
            .stage_2_layout
            .intermediate_poly_for_range_check_16_multiplicity
            .get_range(0)
            .start;
        let range_check_16_setup_column = compiled_circuit
            .setup_layout
            .range_check_16_setup_column
            .start();

        let timestamp_range_check_multiplicities_src = compiled_circuit
            .witness_layout
            .multiplicities_columns_for_timestamp_range_check
            .start();
        let timestamp_range_check_multiplicities_dst = compiled_circuit
            .stage_2_layout
            .intermediate_poly_for_timestamp_range_check_multiplicity
            .get_range(0)
            .start;
        let timestamp_range_check_setup_column = compiled_circuit
            .setup_layout
            .timestamp_range_check_setup_column
            .start();

        let generic_lookup_multiplicities_src_start = compiled_circuit
            .witness_layout
            .multiplicities_columns_for_generic_lookup
            .start();
        let generic_lookup_multiplicities_dst_start = if compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_generic_multiplicities
            .num_elements()
            > 0
        {
            compiled_circuit
                .stage_2_layout
                .intermediate_polys_for_generic_multiplicities
                .get_range(0)
                .start
        } else {
            0
        };
        assert_eq!(
            compiled_circuit
                .setup_layout
                .generic_lookup_setup_columns
                .width(),
            4
        );
        let generic_lookup_setup_columns_start = compiled_circuit
            .setup_layout
            .generic_lookup_setup_columns
            .start();

        let memory_accumulator_dst_start = compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_memory_argument
            .get_range(0)
            .start;

        let num_stage_3_quotient_terms = compiled_circuit.compute_num_quotient_terms();

        Self {
            trace_len,
            memory_timestamp_high_from_circuit_idx,
            delegation_type,
            memory_argument_challenges,
            execute_delegation_argument,
            delegation_challenges,
            process_shuffle_ram_init,
            shuffle_ram_inits_and_teardowns,
            lazy_init_address_range_check_16,
            handle_delegation_requests,
            delegation_request_layout,
            process_batch_ram_access,
            process_registers_and_indirect_access,
            delegation_processor_layout,
            process_delegations,
            delegation_processing_aux_poly,
            num_set_polys_for_memory_shuffle,
            offset_for_grand_product_accumulation_poly,

            range_check_16_multiplicities_src,
            range_check_16_multiplicities_dst,
            range_check_16_setup_column,

            timestamp_range_check_multiplicities_src,
            timestamp_range_check_multiplicities_dst,
            timestamp_range_check_setup_column,

            generic_lookup_multiplicities_src_start,
            generic_lookup_multiplicities_dst_start,
            generic_lookup_setup_columns_start,

            range_check_16_width_1_lookups_access,
            range_check_16_width_1_lookups_access_via_expressions,

            timestamp_range_check_width_1_lookups_access_via_expressions,
            timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram,

            width_3_lookups_with_fixed_col_id,
            width_3_lookups_with_variable_col_id,

            memory_accumulator_dst_start,

            num_stage_3_quotient_terms,
            circuit_sequence: circuit_sequence as u32,
        }
    }
}
