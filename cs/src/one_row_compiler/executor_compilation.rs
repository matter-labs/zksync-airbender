use super::*;
use crate::one_row_compiler::compile_layout::*;
use crate::one_row_compiler::delegation::*;

impl<F: PrimeField> OneRowCompiler<F> {
    pub fn compile_executor_circuit(
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

        assert!(state_input.is_empty());
        assert!(state_output.is_empty());
        assert!(linked_variables.is_empty());
        assert!(degegated_request_to_process.is_none());
        assert!(register_and_indirect_memory_accesses.is_empty());
        assert!(decoder_machine_state.is_none());

        let trace_len = 1usize << trace_len_log2;
        let total_tables_size = table_driver.total_tables_len;
        let lookup_table_encoding_capacity = trace_len - 1;
        let mut num_required_tuples_for_generic_lookup_setup =
            total_tables_size / lookup_table_encoding_capacity;
        if total_tables_size % lookup_table_encoding_capacity != 0 {
            num_required_tuples_for_generic_lookup_setup += 1;
        }

        drop(linked_variables);

        let executor_machine_state =
            executor_machine_state.expect("must be present in executor circuit");

        // we do NOT need timestamps in the setup anymore
        let setup_layout = SetupLayout::layout_for_lookup_size(
            total_tables_size,
            trace_len,
            true,
            true,
            false,
            false,
        );

        let mut boolean_vars = boolean_vars;
        let mut num_variables = num_of_variables as u64;

        let mut all_variables_to_place = BTreeSet::new();
        for variable_idx in 0..num_variables {
            all_variables_to_place.insert(Variable(variable_idx));
        }

        let mut memory_tree_offset = 0;
        // as a byproduct we will also create a map of witness generation functions
        let mut layout = BTreeMap::<Variable, ColumnAddress>::new();

        assert!(
            delegated_computation_requests.len() <= 1,
            "at most one delegation is allowed per cycle"
        );

        // we do NOT bump timestamps in any form, so we do not need to layout anything about them here -
        // we mainly need to layout the decoder machine state into memory columns,
        // and then layout witness around it

        let (machine_state, executor_state) = layout_executor_state_into_memory(
            &mut memory_tree_offset,
            &mut all_variables_to_place,
            &mut layout,
            &executor_machine_state,
        );

        // then we need to compile memory queries
        // and timestamp range checks for them

        // we only need to compile timestamp comparison range checks

        let mut shuffle_ram_timestamp_range_check_partial_sets = vec![];
        let mut memory_timestamp_comparison_sets = vec![];

        let mut shuffle_ram_access_sets = vec![];

        assert!(shuffle_ram_queries.len() < 4);
        assert!(shuffle_ram_queries
            .is_sorted_by(|a, b| a.local_timestamp_in_cycle < b.local_timestamp_in_cycle));
        shuffle_ram_queries.windows(2).for_each(|el| {
            assert!(el[0].local_timestamp_in_cycle + 1 == el[1].local_timestamp_in_cycle)
        });

        // NOTE: we only need to make sure that read timestamp < write timestamp, and we will do the following way:
        // - read timestamps do NOT need to be range-checked by itself, as if permutation works,
        // then those are from write set timestamps, so - range checked
        // - this cycle timestamp is a result of permutation of final timestamp at the end of the cycle, that is range checked,
        // so also do not need range check
        // - so we just compare that read timestamp < this cycle timestamp + in-cycle timestamp
        // - then we will make a constraint that final timestamp = initial + step (and 0 mod 4)

        for (query_idx, memory_query) in shuffle_ram_queries.clone().into_iter().enumerate() {
            assert_eq!(memory_query.local_timestamp_in_cycle, query_idx);

            let [read_timestamp_low, read_timestamp_high] =
                add_multiple_compiler_defined_variables::<NUM_TIMESTAMP_COLUMNS_FOR_RAM>(
                    &mut num_variables,
                    &mut all_variables_to_place,
                );
            let read_timestamp = layout_memory_subtree_multiple_variables(
                &mut memory_tree_offset,
                [read_timestamp_low, read_timestamp_high],
                &mut all_variables_to_place,
                &mut layout,
            );

            // we do NOT need to allocate any range check variable, as:
            // write timestamp low limb

            // now that we have declared timestamps, we can produce comparison expressions for range checks
            let borrow_var =
                add_compiler_defined_variable(&mut num_variables, &mut all_variables_to_place);
            boolean_vars.push(borrow_var);

            let partial_data = ShuffleRamTimestampComparisonPartialData {
                intermediate_borrow: borrow_var,
                read_timestamp: [read_timestamp_low, read_timestamp_high],
                local_timestamp_in_cycle: memory_query.local_timestamp_in_cycle,
            };
            shuffle_ram_timestamp_range_check_partial_sets.push(partial_data);

            let set = borrow_var;
            memory_timestamp_comparison_sets.push(set);

            let read_value = layout_memory_subtree_multiple_variables(
                &mut memory_tree_offset,
                memory_query.read_value,
                &mut all_variables_to_place,
                &mut layout,
            );

            let address = match memory_query.query_type {
                ShuffleRamQueryType::RegisterOnly { register_index } => {
                    let register_index = layout_memory_subtree_variable(
                        &mut memory_tree_offset,
                        register_index,
                        &mut all_variables_to_place,
                        &mut layout,
                    );

                    ShuffleRamAddress::RegisterOnly(RegisterOnlyAccessAddress { register_index })
                }
                ShuffleRamQueryType::RegisterOrRam {
                    is_register,
                    address,
                } => {
                    let is_register = layout_memory_subtree_variable(
                        &mut memory_tree_offset,
                        is_register.get_variable().unwrap(),
                        &mut all_variables_to_place,
                        &mut layout,
                    );
                    let address = layout_memory_subtree_multiple_variables(
                        &mut memory_tree_offset,
                        address,
                        &mut all_variables_to_place,
                        &mut layout,
                    );

                    ShuffleRamAddress::RegisterOrRam(RegisterOrRamAccessAddress {
                        is_register,
                        address,
                    })
                }
            };

            let query_columns = if memory_query.is_readonly() {
                assert_eq!(memory_query.read_value, memory_query.write_value);

                let query_columns = ShuffleRamQueryReadColumns {
                    in_cycle_write_index: memory_query.local_timestamp_in_cycle as u32,
                    address,
                    read_timestamp,
                    read_value,
                };

                ShuffleRamQueryColumns::Readonly(query_columns)
            } else {
                let write_value = layout_memory_subtree_multiple_variables(
                    &mut memory_tree_offset,
                    memory_query.write_value,
                    &mut all_variables_to_place,
                    &mut layout,
                );

                let query_columns = ShuffleRamQueryWriteColumns {
                    in_cycle_write_index: memory_query.local_timestamp_in_cycle as u32,
                    address,
                    read_timestamp,
                    read_value,
                    write_value,
                };

                ShuffleRamQueryColumns::Write(query_columns)
            };

            shuffle_ram_access_sets.push(query_columns);
        }

        // and we need to make a constraint that next timestamp = current + 4. There are various ways to do it,
        // but for simplicity we will just do the same - add extra boolean variable, and we will explicitly require
        // that next cycle timestamp is range checked

        let next_timestamp_intermediate_carry = {
            let borrow_var =
                add_compiler_defined_variable(&mut num_variables, &mut all_variables_to_place);
            boolean_vars.push(borrow_var);

            borrow_var
        };

        let read_timestamps: Vec<_> = shuffle_ram_queries
            .iter()
            .filter_map(|el| {
                if el.is_readonly() {
                    Some(el.local_timestamp_in_cycle)
                } else {
                    None
                }
            })
            .collect();
        let min_read = *read_timestamps.iter().min().unwrap();
        let max_read = *read_timestamps.iter().max().unwrap();

        assert_eq!(min_read, 0);

        let write_timestamps: Vec<_> = shuffle_ram_queries
            .iter()
            .filter_map(|el| {
                if el.is_readonly() == false {
                    Some(el.local_timestamp_in_cycle)
                } else {
                    None
                }
            })
            .collect();
        let min_write = *write_timestamps.iter().min().unwrap();
        let max_write = *write_timestamps.iter().max().unwrap();

        assert!(max_read < min_write);

        // we use a write timestamp for delegation
        let delegation_timestamp_offset = max_write + 1;
        assert!(delegation_timestamp_offset < (1 << NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP));

        let delegation_request_layout = if delegated_computation_requests.len() > 0 {
            assert_eq!(delegated_computation_requests.len(), 1);
            let request = delegated_computation_requests[0];

            let DelegatedComputationRequest {
                execute,
                delegation_type,
                memory_offset_high,
            } = request;

            let multiplicity = layout_memory_subtree_variable(
                &mut memory_tree_offset,
                execute,
                &mut all_variables_to_place,
                &mut layout,
            );
            let delegation_type = layout_memory_subtree_variable(
                &mut memory_tree_offset,
                delegation_type,
                &mut all_variables_to_place,
                &mut layout,
            );
            let abi_mem_offset_high = layout_memory_subtree_variable(
                &mut memory_tree_offset,
                memory_offset_high,
                &mut all_variables_to_place,
                &mut layout,
            );

            let layout = DelegationRequestLayout {
                multiplicity,
                delegation_type,
                abi_mem_offset_high,
                in_cycle_write_index: delegation_timestamp_offset as u16,
            };

            Some(layout)
        } else {
            None
        };

        let memory_layout = MemorySubtree {
            shuffle_ram_inits_and_teardowns: Vec::new(),
            shuffle_ram_access_sets,
            delegation_request_layout,
            delegation_processor_layout: None,
            batched_ram_accesses: Vec::new(),
            register_and_indirect_accesses: Vec::new(),
            machine_state_layout: Some(machine_state),
            intermediate_state_layout: Some(executor_state),
            total_width: memory_tree_offset,
        };

        // we would need to wait until boolean allocation to finish compiling shuffle ram timestamp constraints

        let mut witness_tree_offset = 0usize;

        let multiplicities_columns_for_range_check_16 =
            ColumnSet::layout_at(&mut witness_tree_offset, 1);
        let multiplicities_columns_for_timestamp_range_check =
            ColumnSet::layout_at(&mut witness_tree_offset, 1);

        // we do not have special-cased range checks, but have generic lookup
        let multiplicities_columns_for_generic_lookup = ColumnSet::layout_at(
            &mut witness_tree_offset,
            num_required_tuples_for_generic_lookup_setup,
        );

        let (range_check_8_columns, range_check_16_columns, range_check_16_lookup_expressions) =
            allocate_range_check_expressions(
                trace_len,
                vec![],
                &range_check_expressions,
                &mut witness_tree_offset,
                &mut all_variables_to_place,
                &mut layout,
                0,
            );

        let mut compiled_quadratic_terms = vec![];
        let mut compiled_linear_terms = vec![];

        // Now we will pause and place boolean variables, as those can have their contraints special-handled in quotient

        let mut constraints = constraints;
        // normalize again just in case
        for (el, _) in constraints.iter_mut() {
            el.normalize();
        }
        // now we should just place boolean variables, and then everything from scratch space

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

        let width_3_lookups = allocate_width_3_lookups(
            trace_len,
            lookups,
            &mut witness_tree_offset,
            &mut all_variables_to_place,
            &mut layout,
        );

        let mut timestamp_range_check_expressions_to_compile = vec![];
        // we know that at the start of the cycle we do have range checked value,
        // and so we want at the end. We do not add any explicit constraint here
        // and it'll be a part of the quotient special-case associated with that argument,
        // so we just add simple ones
        timestamp_range_check_expressions_to_compile.push(LookupInput::Variable(
            executor_machine_state.cycle_end_state.timestamp[0],
        ));
        timestamp_range_check_expressions_to_compile.push(LookupInput::Variable(
            executor_machine_state.cycle_end_state.timestamp[1],
        ));

        let (
            offset_for_special_shuffle_ram_timestamps_range_check_expressions,
            timestamp_range_check_lookup_expressions,
        ) = compile_timestamp_range_check_expressions::<F, false>(
            trace_len,
            timestamp_range_check_expressions_to_compile,
            shuffle_ram_timestamp_range_check_partial_sets,
            &layout,
            &setup_layout,
            Some(executor_state.timestamp),
        );

        // now check if there exist any variables that are
        // - not yet placed (so - not lookup ins/outs)
        // - can be expressed via linear constraint
        // - can be substituted into other places

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
            multiplicities_columns_for_range_check_16,
            multiplicities_columns_for_timestamp_range_check,
            multiplicities_columns_for_decoder_in_executor_families: ColumnSet::empty(),
            multiplicities_columns_for_generic_lookup,
            range_check_8_columns,
            range_check_16_columns,
            width_3_lookups,
            range_check_16_lookup_expressions,
            timestamp_range_check_lookup_expressions,
            offset_for_special_shuffle_ram_timestamps_range_check_expressions,
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

        let stage_2_layout = LookupAndMemoryArgumentLayout::from_compiled_parts(
            &witness_layout,
            &memory_layout,
            &setup_layout,
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

        let executor_family_circuit_next_timestamp_aux_var = layout
            .get(&next_timestamp_intermediate_carry)
            .copied()
            .unwrap();

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
            executor_family_circuit_next_timestamp_aux_var: Some(
                executor_family_circuit_next_timestamp_aux_var,
            ),
            executor_family_decoder_table_size: 0,
            trace_len,
            table_offsets,
            total_tables_size,
        };

        result
    }
}
