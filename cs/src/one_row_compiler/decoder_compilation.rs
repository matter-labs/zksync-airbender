use super::*;

impl<F: PrimeField> OneRowCompiler<F> {
    pub fn compile_decoder_circuit(
        &self,
        circuit_output: CircuitOutput<F>,
        trace_len_log2: usize,
    ) -> CompiledCircuitArtifact<F> {
        // our main purposes are:
        // - place variables in particular grid places
        // - select whether they go into witness subtree or memory subtree
        // - normalize constraints to address particular columns insteap of variable indexes
        // - try to apply some heuristrics

        let CircuitOutput {
            state_input,
            state_output,
            table_driver,
            num_of_variables,
            constraints,
            lookups,
            shuffle_ram_queries,
            linked_variables,
            range_check_expressions,
            boolean_vars,
            substitutions,
            delegated_computation_requests,
            degegated_request_to_process,
            register_and_indirect_memory_accesses,
            decoder_machine_state,
            executor_machine_state,
        } = circuit_output;

        assert!(trace_len_log2 > TIMESTAMP_COLUMNS_NUM_BITS as usize);

        // we compile decoder circuit that doesn't perform memory accesses,
        // delegations, etc

        assert!(state_input.is_empty());
        assert!(state_output.is_empty());
        assert!(shuffle_ram_queries.is_empty());
        assert!(linked_variables.is_empty());
        assert!(degegated_request_to_process.is_none());
        assert!(delegated_computation_requests.is_empty());
        assert!(register_and_indirect_memory_accesses.is_empty());
        assert!(executor_machine_state.is_none());
        assert!(range_check_expressions.is_empty());

        for el in lookups.iter() {
            let LookupQueryTableType::Constant(table_type) = el.table else {
                panic!("all lookups must use fixed table IDx");
            };
            let t = table_driver.get_table(table_type);
            assert!(
                t.is_initialized(),
                "trying to use table with ID {:?}, but it's not initialized in table driver",
                table_type
            );
        }

        let trace_len = 1usize << trace_len_log2;
        let total_tables_size = table_driver.total_tables_len;
        let lookup_table_encoding_capacity = trace_len - 1;
        let mut num_required_tuples_for_generic_lookup_setup =
            total_tables_size / lookup_table_encoding_capacity;
        if total_tables_size % lookup_table_encoding_capacity != 0 {
            num_required_tuples_for_generic_lookup_setup += 1;
        }

        drop(linked_variables);

        let decoder_machine_state =
            decoder_machine_state.expect("must be present in decoder circuit");

        // we do NOT need timestamps in the setup anymore
        let setup_layout = SetupLayout::layout_for_lookup_size(
            total_tables_size,
            trace_len,
            false,
            false,
            false,
            false,
        );

        let boolean_vars = boolean_vars;
        let num_variables = num_of_variables as u64;

        let mut all_variables_to_place = BTreeSet::new();
        for variable_idx in 0..num_variables {
            all_variables_to_place.insert(Variable(variable_idx));
        }

        let mut memory_tree_offset = 0;
        // as a byproduct we will also create a map of witness generation functions
        let mut layout = BTreeMap::<Variable, ColumnAddress>::new();

        // we do NOT bump timestamps in any form, so we do not need to layout anything about them here -
        // we mainly need to layout the decoder machine state into memory columns,
        // and then layout witness around it

        let (machine_state, executor_state) = layout_decoder_state_into_memory(
            &mut memory_tree_offset,
            &mut all_variables_to_place,
            &mut layout,
            &decoder_machine_state,
        );

        // and that's it for memory layout here

        let memory_layout = MemorySubtree {
            shuffle_ram_inits_and_teardowns: Vec::new(),
            shuffle_ram_access_sets: Vec::new(),
            delegation_request_layout: None,
            delegation_processor_layout: None,
            batched_ram_accesses: Vec::new(),
            register_and_indirect_accesses: Vec::new(),
            machine_state_layout: Some(machine_state),
            intermediate_state_layout: Some(executor_state),
            total_width: memory_tree_offset,
        };

        let mut witness_tree_offset = 0usize;

        // we do not have special-cased range checks, but have generic lookup
        let multiplicities_columns_for_generic_lookup = ColumnSet::layout_at(
            &mut witness_tree_offset,
            num_required_tuples_for_generic_lookup_setup,
        );

        // Now we will pause and place boolean variables, as those can have their contraints special-handled in quotient

        let mut constraints = constraints;
        // normalize again just in case
        for (el, _) in constraints.iter_mut() {
            el.normalize();
        }
        // now we should just place boolean variables, and then everything from scratch space

        // now we can remap all the constraints into placements
        let mut compiled_quadratic_terms = vec![];
        let mut compiled_linear_terms = vec![];

        let mut boolean_vars_start = witness_tree_offset;
        let num_boolean_vars = boolean_vars.len();
        let boolean_vars_columns_range =
            ColumnSet::layout_at(&mut boolean_vars_start, num_boolean_vars);

        // first we can layout booleans
        for variable in boolean_vars.into_iter() {
            assert!(
                all_variables_to_place.remove(&variable),
                "variable {:?} was already placed",
                variable
            );
            let place = ColumnAddress::WitnessSubtree(witness_tree_offset);
            layout.insert(variable, place);
            witness_tree_offset += 1;

            let mut quadratic_terms = vec![];
            let mut linear_terms = vec![];
            quadratic_terms.push((F::ONE, place, place));
            linear_terms.push((F::MINUS_ONE, place));

            // we also need to make constraints for them
            let compiled_term = CompiledDegree2Constraint {
                quadratic_terms: quadratic_terms.into_boxed_slice(),
                linear_terms: linear_terms.into_boxed_slice(),
                constant_term: F::ZERO,
            };

            compiled_quadratic_terms.push(compiled_term);
        }

        assert_eq!(
            boolean_vars_columns_range.full_range().end,
            witness_tree_offset
        );
        assert_eq!(compiled_quadratic_terms.len(), num_boolean_vars);

        // after we placed booleans, we can finally compiled lookup expressions, and other compiler-provided things like timestamp comparisons

        let mut width_3_lookups = allocate_width_3_lookups(
            trace_len,
            lookups,
            &mut witness_tree_offset,
            &mut all_variables_to_place,
            &mut layout,
        );

        // NOTE: we perform artificial range check for circuit family as coarse 8-bit

        {
            let place = layout[&decoder_machine_state.decoder_data.circuit_family];
            let input_columns = [
                LookupExpression::Variable(place),
                LookupExpression::zero(),
                LookupExpression::zero(),
            ];
            let lookup = LookupSetDescription {
                input_columns,
                table_index: TableIndex::Constant(TableType::RangeCheckSmall),
            };
            width_3_lookups.push(lookup);
        }

        let total_generic_lookups = width_3_lookups.len() as u64 * trace_len as u64;
        assert!(total_generic_lookups < F::CHARACTERISTICS, "total number of generic lookups in circuit is {} that is larger that field characteristics {}", total_generic_lookups, F::CHARACTERISTICS);

        let (optimized_out_variables, constraints) = optimize_out_linear_constraints(
            &state_input,
            &state_output,
            &substitutions,
            constraints,
            &mut all_variables_to_place,
        );

        let scratch_space_size_for_witness_gen = optimized_out_variables.len();

        let scratch_space_columns_range = layout_scratch_space(
            &mut compiled_quadratic_terms,
            &mut compiled_linear_terms,
            optimized_out_variables,
            constraints,
            &mut witness_tree_offset,
            all_variables_to_place,
            &mut layout,
        );

        // there are no inputs or outputs, or linkage

        let witness_layout = WitnessSubtree {
            multiplicities_columns_for_range_check_16: ColumnSet::empty(),
            multiplicities_columns_for_timestamp_range_check: ColumnSet::empty(),
            multiplicities_columns_for_decoder_in_executor_families: ColumnSet::empty(),
            multiplicities_columns_for_generic_lookup,
            range_check_8_columns: ColumnSet::empty(),
            range_check_16_columns: ColumnSet::empty(),
            width_3_lookups,
            range_check_16_lookup_expressions: Vec::new(),
            timestamp_range_check_lookup_expressions: Vec::new(),
            offset_for_special_shuffle_ram_timestamps_range_check_expressions: 0,
            boolean_vars_columns_range,
            scratch_space_columns_range,
            total_width: witness_tree_offset,
        };

        // then produce specific sets, that make our descriptions easier
        let memory_queries_timestamp_comparison_aux_vars = Vec::new();

        let batched_memory_access_timestamp_comparison_aux_vars =
            BatchedRamTimestampComparisonAuxVars {
                predicate: ColumnAddress::placeholder(),
                write_timestamp: [ColumnAddress::placeholder(); 2],
                write_timestamp_columns: ColumnSet::empty(),
                aux_borrow_vars: vec![],
            };

        let register_and_indirect_access_timestamp_comparison_aux_vars =
            RegisterAndIndirectAccessTimestampComparisonAuxVars {
                predicate: ColumnAddress::placeholder(),
                write_timestamp: [ColumnAddress::placeholder(); 2],
                write_timestamp_columns: ColumnSet::empty(),
                aux_borrow_sets: vec![],
            };

        assert_eq!(
            setup_layout.generic_lookup_setup_columns.num_elements(),
            num_required_tuples_for_generic_lookup_setup
        );

        let stage_2_layout = LookupAndMemoryArgumentLayout::from_compiled_parts::<_, true>(
            &witness_layout,
            &memory_layout,
            &setup_layout,
            true,
            true,
        );

        for el in compiled_quadratic_terms.iter_mut() {
            el.normalize();
        }

        for el in compiled_linear_terms.iter_mut() {
            el.normalize();
        }

        let table_offsets = table_driver
            .table_starts_offsets()
            .map(|el| el as u32)
            .to_vec();

        let result = CompiledCircuitArtifact {
            witness_layout,
            memory_layout,
            setup_layout,
            stage_2_layout,
            degree_2_constraints: compiled_quadratic_terms,
            degree_1_constraints: compiled_linear_terms,
            state_linkage_constraints: Vec::new(),
            public_inputs: Vec::new(),
            scratch_space_size_for_witness_gen,
            variable_mapping: layout,
            lazy_init_address_aux_vars: Vec::new(),
            memory_queries_timestamp_comparison_aux_vars,
            batched_memory_access_timestamp_comparison_aux_vars,
            register_and_indirect_access_timestamp_comparison_aux_vars,
            executor_family_circuit_next_timestamp_aux_var: None,
            executor_family_decoder_table_size: 0,
            trace_len,
            table_offsets,
            total_tables_size,
        };

        result
    }
}
