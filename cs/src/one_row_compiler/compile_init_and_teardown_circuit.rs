use super::*;
use crate::{one_row_compiler::delegation::*, tables::TableDriver};

impl<F: PrimeField> OneRowCompiler<F> {
    pub(crate) fn compile_inits_and_teardowns(
        num_sets: usize,
        boolean_vars: &mut Vec<Variable>,
        range_check_expressions: &mut Vec<RangeCheckQuery<F>>,
        num_variables: &mut u64,
        memory_tree_offset: &mut usize,
        all_variables_to_place: &mut BTreeSet<Variable>,
        layout: &mut BTreeMap<Variable, ColumnAddress>,
    ) -> (
        Vec<ShuffleRamInitAndTeardownLayout>,
        Vec<([Variable; REGISTER_SIZE], Variable, Variable)>,
    ) {
        let mut result = Vec::with_capacity(num_sets);

        // first we will manually add extra space for constraint that lazy init values are unique

        // In general, if we do not want to remove restriction that number of cycles can be larger than formal
        // RAM address space, we could use constraint in the form
        // - (borrow(this) << 16) + addr_low(this) - addr_low(next) = tmp_low(this),
        // - 2^16 + addr_high(this) - addr_high(next) - borrow(this) = tmp_high(this),
        // reflecting that address(next) > address(this), of that address(this) - address(next) is with borrow

        // And to allow pre-padding of lazy init with just multiple rows with values that "cancel" each other in
        // a sense that their controbutions to read and write set are trivial and equal, we modily the constraint
        // - (intermediate_borrow(this) << 16) + addr_low(this) - addr_low(next) = tmp_low(this),
        // - (final_borrow(this) << 16 + addr_high(this) - addr_high(next) - borrow(this) = tmp_high(this)
        // - (1 - final_borrow(this)) * addr_low(this) = 0
        // - (1 - final_borrow(this)) * addr_high(this) = 0
        // - (1 - final_borrow(this)) * teardown_value_low(this) = 0
        // - (1 - final_borrow(this)) * teardown_value_high(this) = 0
        // - (1 - final_borrow(this)) * teardown_timestamp_low(this) = 0
        // - (1 - final_borrow(this)) * teardown_timestamp_high(this) = 0

        // this way we require that unless values are ordered as this < next, we have formal init record of
        // address = 0 (constrained), ts = 0 (hardcoded), value = 0 (hardcoded), and teardown record also
        // address = 0 (same variable), ts = 0 (constrained), value = 0 (constrained), canceling each other in permutation grand product

        // NOTE: lookup expressions do not allow to express a relation between two rows,
        // so we will pay to materialize intermediate subtraction result variables

        let mut lazy_init_aux_set = Vec::with_capacity(num_sets);

        for _ in 0..num_sets {
            let tmp_low_var = add_compiler_defined_variable(num_variables, all_variables_to_place);
            let tmp_high_var = add_compiler_defined_variable(num_variables, all_variables_to_place);
            let intermediate_borrow_var =
                add_compiler_defined_variable(num_variables, all_variables_to_place);
            let final_borrow_var =
                add_compiler_defined_variable(num_variables, all_variables_to_place);

            lazy_init_aux_set.push((
                [tmp_low_var, tmp_high_var],
                intermediate_borrow_var,
                final_borrow_var,
            ));
            range_check_expressions.push(RangeCheckQuery::new(
                tmp_low_var,
                LARGE_RANGE_CHECK_TABLE_WIDTH,
            ));
            range_check_expressions.push(RangeCheckQuery::new(
                tmp_high_var,
                LARGE_RANGE_CHECK_TABLE_WIDTH,
            ));
            boolean_vars.push(intermediate_borrow_var);
            boolean_vars.push(final_borrow_var);

            let shuffle_ram_init_addresses = add_multiple_compiler_defined_variables::<REGISTER_SIZE>(
                num_variables,
                all_variables_to_place,
            );
            let shuffle_ram_teardown_values = add_multiple_compiler_defined_variables::<
                REGISTER_SIZE,
            >(num_variables, all_variables_to_place);
            let shuffle_ram_teardown_timestamps = add_multiple_compiler_defined_variables::<
                NUM_TIMESTAMP_COLUMNS_FOR_RAM,
            >(
                num_variables, all_variables_to_place
            );

            // NOTE: here we use only register width because it's implied 0-value column for "is_register",
            // as we zero-init only RAM and not the registers

            // NOTE: we will separately add to the quotient and range check 16 layouts in stage 2 parts the fact that
            // lazy init addresses are under range check 16
            let lazy_init_addresses_columns = layout_memory_subtree_multiple_variables(
                memory_tree_offset,
                shuffle_ram_init_addresses,
                all_variables_to_place,
                layout,
            );
            let lazy_teardown_values_columns = layout_memory_subtree_multiple_variables(
                memory_tree_offset,
                shuffle_ram_teardown_values,
                all_variables_to_place,
                layout,
            );
            let lazy_teardown_timestamps_columns = layout_memory_subtree_multiple_variables(
                memory_tree_offset,
                shuffle_ram_teardown_timestamps,
                all_variables_to_place,
                layout,
            );

            let shuffle_ram_inits_and_teardowns = ShuffleRamInitAndTeardownLayout {
                lazy_init_addresses_columns,
                lazy_teardown_values_columns,
                lazy_teardown_timestamps_columns,
            };

            result.push(shuffle_ram_inits_and_teardowns);
        }

        (result, lazy_init_aux_set)
    }

    pub fn compile_init_and_teardown_circuit(
        &self,
        num_init_and_teardown_column_sets: usize,
        trace_len_log2: usize,
    ) -> CompiledCircuitArtifact<F> {
        assert!(trace_len_log2 > TIMESTAMP_COLUMNS_NUM_BITS as usize);
        let trace_len = 1usize << trace_len_log2;

        // This circuit has no general purpose lookups, and only contains special-cased logic for inits and teardowns,
        // such as comparison over rows for addresses and that's it

        // we do NOT need timestamps in the setup anymore
        let setup_layout =
            SetupLayout::layout_for_lookup_size(0, trace_len, true, false, false, false);

        let mut boolean_vars = Vec::new();
        let mut range_check_expressions = Vec::new();

        let mut num_variables = 0u64;
        let mut all_variables_to_place = BTreeSet::new();

        for variable_idx in 0..num_variables {
            all_variables_to_place.insert(Variable(variable_idx));
        }

        let mut memory_tree_offset = 0;
        // as a byproduct we will also create a map of witness generation functions
        let mut layout = BTreeMap::<Variable, ColumnAddress>::new();

        let (shuffle_ram_inits_and_teardowns, lazy_init_aux_set) =
            Self::compile_inits_and_teardowns(
                num_init_and_teardown_column_sets,
                &mut boolean_vars,
                &mut range_check_expressions,
                &mut num_variables,
                &mut memory_tree_offset,
                &mut all_variables_to_place,
                &mut layout,
            );

        let memory_layout = MemorySubtree {
            shuffle_ram_inits_and_teardowns,
            shuffle_ram_access_sets: vec![],
            delegation_request_layout: None,
            delegation_processor_layout: None,
            batched_ram_accesses: vec![],
            register_and_indirect_accesses: vec![],
            machine_state_layout: None,
            intermediate_state_layout: None,
            total_width: memory_tree_offset,
        };

        let mut witness_tree_offset = 0usize;

        let multiplicities_columns_for_range_check_16 =
            ColumnSet::layout_at(&mut witness_tree_offset, 1);
        let multiplicities_columns_for_timestamp_range_check = ColumnSet::empty();

        // No generic lookup
        let (range_check_8_columns, range_check_16_columns, range_check_16_lookup_expressions) =
            allocate_range_check_expressions(
                trace_len,
                vec![],
                &range_check_expressions,
                &mut witness_tree_offset,
                &mut all_variables_to_place,
                &mut layout,
                memory_layout.shuffle_ram_inits_and_teardowns.len() * 2,
            );

        // no generic lookup
        let multiplicities_columns_for_generic_lookup = ColumnSet::empty();

        // Now we will pause and place boolean variables, as those can have their contraints special-handled in quotient

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

        // No generic lookups

        // no optimizer is needed too

        let scratch_space_size_for_witness_gen = 0;

        let scratch_space_columns_range = layout_scratch_space(
            &mut compiled_quadratic_terms,
            &mut compiled_linear_terms,
            vec![],
            vec![],
            &mut witness_tree_offset,
            all_variables_to_place,
            &mut layout,
        );

        let lazy_init_address_aux_vars = lazy_init_aux_set
            .into_iter()
            .map(|(comparison_aux_vars, intermediate_borrow, final_borrow)| {
                let address_aux = comparison_aux_vars
                    .map(|el| layout.get(&el).copied().expect("must be compiled"));
                let intermediate_borrow = layout
                    .get(&intermediate_borrow)
                    .copied()
                    .expect("must be compiled");
                let final_borrow = layout
                    .get(&final_borrow)
                    .copied()
                    .expect("must be compiled");

                let lazy_init_address_aux_vars = ShuffleRamAuxComparisonSet {
                    aux_low_high: address_aux,
                    intermediate_borrow,
                    final_borrow,
                };

                lazy_init_address_aux_vars
            })
            .collect();

        let witness_layout = WitnessSubtree {
            multiplicities_columns_for_range_check_16,
            multiplicities_columns_for_timestamp_range_check,
            multiplicities_columns_for_generic_lookup,
            multiplicities_columns_for_decoder_in_executor_families: ColumnSet::empty(),
            range_check_8_columns,
            range_check_16_columns,
            width_3_lookups: Vec::new(),
            range_check_16_lookup_expressions,
            timestamp_range_check_lookup_expressions: Vec::new(),
            offset_for_special_shuffle_ram_timestamps_range_check_expressions: 0,
            boolean_vars_columns_range,
            scratch_space_columns_range,
            total_width: witness_tree_offset,
        };

        let stage_2_layout = LookupAndMemoryArgumentLayout::from_compiled_parts(
            &witness_layout,
            &memory_layout,
            &setup_layout,
            false,
            false,
        );

        for el in compiled_quadratic_terms.iter_mut() {
            el.normalize();
        }

        for el in compiled_linear_terms.iter_mut() {
            el.normalize();
        }

        let table_offsets = TableDriver::<F>::new()
            .table_starts_offsets()
            .map(|el| el as u32)
            .to_vec();

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
            lazy_init_address_aux_vars,
            memory_queries_timestamp_comparison_aux_vars: Vec::new(),
            batched_memory_access_timestamp_comparison_aux_vars,
            register_and_indirect_access_timestamp_comparison_aux_vars,
            executor_family_circuit_next_timestamp_aux_var: None,
            executor_family_decoder_table_size: 0,
            trace_len,
            table_offsets,
            total_tables_size: 0,
        };

        result
    }
}
