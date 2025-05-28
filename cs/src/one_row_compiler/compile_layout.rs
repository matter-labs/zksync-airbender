use delegation::*;

use super::*;

struct ShuffleRamTimestampComparisonPartialData {
    intermediate_borrow: Variable,
    read_timestamp: [Variable; 2],
    local_timestamp_in_cycle: usize,
}

struct DelegationMemoryAccessesAuxVars {
    pub predicate: ColumnAddress,
    pub write_timestamp_for_comparison: [ColumnAddress; 2],
    pub write_timestamp_columns: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    pub batched_ram_access_timestamp_aux_sets: Vec<Variable>,
    pub register_and_indirect_access_timestamp_aux_sets: Vec<(Variable, Vec<Variable>)>,
}

// NOTE: even though we saved range check for 8 bits, we will put them into generic lookups and pack them by 2

impl<F: PrimeField> OneRowCompiler<F> {
    pub fn compile_output_for_chunked_memory_argument(
        &self,
        circuit_output: CircuitOutput<F>,
        trace_len_log2: usize,
    ) -> CompiledCircuitArtifact<F> {
        Self::compile_inner::<false>(self, circuit_output, trace_len_log2)
    }

    pub fn compile_to_evaluate_delegations(
        &self,
        circuit_output: CircuitOutput<F>,
        trace_len_log2: usize,
    ) -> CompiledCircuitArtifact<F> {
        Self::compile_inner::<true>(self, circuit_output, trace_len_log2)
    }

    fn compile_inner<const FOR_DELEGATION: bool>(
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
            batched_memory_accesses,
            register_and_indirect_memory_accesses,
        } = circuit_output;

        assert!(trace_len_log2 > TIMESTAMP_COLUMNS_NUM_BITS as usize);

        if FOR_DELEGATION {
            assert!(state_input.is_empty());
            assert!(state_output.is_empty());
            assert!(shuffle_ram_queries.is_empty());
            assert!(linked_variables.is_empty());
            assert!(degegated_request_to_process.is_some());
            assert!(delegated_computation_requests.is_empty());
            assert!(
                batched_memory_accesses.len() > 0
                    || register_and_indirect_memory_accesses.len() > 0
            );

            assert!(
                batched_memory_accesses.is_empty(),
                "batched RAM accesses are deprecated"
            );

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
        } else {
            assert_eq!(shuffle_ram_queries.len(), 3);
            assert!(linked_variables.is_empty());
            assert!(degegated_request_to_process.is_none());
            assert!(batched_memory_accesses.is_empty());
            assert!(register_and_indirect_memory_accesses.is_empty());
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

        // we can immediately make setup layout
        let need_timestamps = !FOR_DELEGATION;
        let setup_layout =
            SetupLayout::layout_for_lookup_size(total_tables_size, trace_len, need_timestamps);

        assert!(
            delegated_computation_requests.len() <= 1,
            "at most one delegation is allowed per cycle"
        );

        let mut boolean_vars = boolean_vars;
        let mut range_check_expressions = range_check_expressions;

        let mut num_variables = num_of_variables as u64;

        let mut all_variables_to_place = BTreeSet::new();
        for variable_idx in 0..num_variables {
            all_variables_to_place.insert(Variable(variable_idx));
        }

        let mut memory_tree_offset = 0;
        // as a byproduct we will also create a map of witness generation functions
        let mut layout = BTreeMap::<Variable, ColumnAddress>::new();

        const SHIFT_16: u64 = 1 << 16;

        let mut shuffle_ram_extra_range_check_16_partial_sets = vec![];
        // These expressions mix variables between memory and witness subtree (e.g boolean carries),
        // and so we will compile it later when booleans are allocated
        let mut timestamp_range_check_expressions_to_compile = vec![];

        // These expressions only touch memory subtree and can be used as-is
        let mut compiled_extra_range_check_16_expressions = vec![];

        let (
            memory_subtree_placement,
            lazy_init_aux_set,
            memory_timestamp_comparison_sets,
            delegation_ram_access_aux_vars,
        ) = if FOR_DELEGATION {
            // Here we first layout the delegation request itself, and then put all memory queries.
            // For the queries we assume address to be just a sequential shift from delegation request's
            // 16-bit high offset

            let degegated_request_to_process = degegated_request_to_process.unwrap();
            let DelegatedProcessingData {
                execute,
                memory_offset_high,
            } = degegated_request_to_process;
            let predicate_variable = execute;
            let delegation_request_predicate_column = layout_memory_subtree_variable(
                &mut memory_tree_offset,
                predicate_variable,
                &mut all_variables_to_place,
                &mut layout,
            );
            let delegation_request_mem_offset_high_column = layout_memory_subtree_variable(
                &mut memory_tree_offset,
                memory_offset_high,
                &mut all_variables_to_place,
                &mut layout,
            );
            // now we need to add delegation timestamp columns that are compiler-defined
            let delegation_timestamp_low_var =
                add_compiler_defined_variable(&mut num_variables, &mut all_variables_to_place);
            let delegation_timestamp_high_var =
                add_compiler_defined_variable(&mut num_variables, &mut all_variables_to_place);
            let delegation_request_timestamp = layout_memory_subtree_multiple_variables(
                &mut memory_tree_offset,
                [delegation_timestamp_low_var, delegation_timestamp_high_var],
                &mut all_variables_to_place,
                &mut layout,
            );

            let [predicate] =
                memory_tree_columns_into_addresses(delegation_request_predicate_column, 0);
            let write_timestamp_for_comparison =
                memory_tree_columns_into_addresses(delegation_request_timestamp, 0);

            let mut aux_vars = DelegationMemoryAccessesAuxVars {
                predicate,
                write_timestamp_columns: delegation_request_timestamp,
                write_timestamp_for_comparison: write_timestamp_for_comparison,
                batched_ram_access_timestamp_aux_sets: vec![],
                register_and_indirect_access_timestamp_aux_sets: vec![],
            };

            let mut register_and_indirect_accesses = vec![];

            // similar work for registers and indirect accesses
            for (_idx, access) in register_and_indirect_memory_accesses
                .into_iter()
                .enumerate()
            {
                // here we do the trick - all intermediate variables are participating in linear constraints,
                // where in a < b comparison `a` and `b` (or their limbs) are range-checked already,
                // so we can require that 2^16 + a - b < 2^16 and just do linear expression for lookup
                let register_timestamp_borrow_var =
                    add_compiler_defined_variable(&mut num_variables, &mut all_variables_to_place);
                boolean_vars.push(register_timestamp_borrow_var);

                let register_read_timestamp_low =
                    add_compiler_defined_variable(&mut num_variables, &mut all_variables_to_place);
                let register_read_timestamp_high =
                    add_compiler_defined_variable(&mut num_variables, &mut all_variables_to_place);

                let read_timestamp_columns = layout_memory_subtree_multiple_variables(
                    &mut memory_tree_offset,
                    [register_read_timestamp_low, register_read_timestamp_high],
                    &mut all_variables_to_place,
                    &mut layout,
                );

                // compare that read timestamp < write timestamp, unless we are in the padding
                {
                    let expr_low = LookupInput::from(
                        Constraint::empty()
                            + Term::from((
                                F::from_u64_unchecked(1 << TIMESTAMP_COLUMNS_NUM_BITS),
                                register_timestamp_borrow_var,
                            ))
                            + Term::from(register_read_timestamp_low)
                            - Term::from(delegation_timestamp_low_var),
                    );
                    timestamp_range_check_expressions_to_compile.push(LookupInput::from(expr_low));

                    // for high part we need to use a predicate, so our comparison is only valid when we actually delegate,
                    // and can pad the rest with 0s
                    let expr_high = LookupInput::from(
                        Constraint::empty()
                            + Term::from((
                                F::from_u64_unchecked(1 << TIMESTAMP_COLUMNS_NUM_BITS),
                                predicate_variable,
                            ))
                            + Term::from(register_read_timestamp_high)
                            - Term::from(delegation_timestamp_high_var)
                            - Term::from(register_timestamp_borrow_var),
                    );
                    timestamp_range_check_expressions_to_compile.push(LookupInput::from(expr_high));
                }

                let RegisterAndIndirectAccesses {
                    register_index,
                    indirects_alignment_log2,
                    register_access,
                    indirect_accesses,
                } = access;

                assert!(register_index > 0);
                assert!(register_index < 32);

                // now we all memory tree-related variables at once, but witness tree will be processed separately below,
                // as we need to place range checks and booleans
                let register_access = match register_access {
                    RegisterAccessType::Read { read_value } => {
                        let read_value_columns = layout_memory_subtree_multiple_variables(
                            &mut memory_tree_offset,
                            read_value,
                            &mut all_variables_to_place,
                            &mut layout,
                        );

                        let request = RegisterAccessColumns::ReadAccess {
                            register_index,
                            read_timestamp: read_timestamp_columns,
                            read_value: read_value_columns,
                        };

                        request
                    }
                    RegisterAccessType::Write {
                        read_value,
                        write_value,
                    } => {
                        let read_value_columns = layout_memory_subtree_multiple_variables(
                            &mut memory_tree_offset,
                            read_value,
                            &mut all_variables_to_place,
                            &mut layout,
                        );
                        let write_value_columns = layout_memory_subtree_multiple_variables(
                            &mut memory_tree_offset,
                            write_value,
                            &mut all_variables_to_place,
                            &mut layout,
                        );

                        let request = RegisterAccessColumns::WriteAccess {
                            register_index,
                            read_timestamp: read_timestamp_columns,
                            read_value: read_value_columns,
                            write_value: write_value_columns,
                        };

                        request
                    }
                };

                let mut request = RegisterAndIndirectAccessDescription {
                    register_access,
                    indirect_accesses: vec![],
                };

                let mut indirect_timestamp_comparison_borrows = vec![];

                // here is another trick - we will not create variables to derive memory address explicitly,
                // but instead accumulate linear expressions as a part of the grand product, so we only need to create
                // exactly one intermediate carry flag, and our permutation argument ensures that all intermediate
                // address chunks are 16 bits range

                if indirect_accesses.len() > 0 {
                    assert!(
                        indirects_alignment_log2 >= std::mem::align_of::<u32>().trailing_zeros()
                    );

                    // and we also enforce that pointer is aligned, by performing an extra range-check over shifted one
                    let mut compiled_linear_terms = vec![];
                    let place = ColumnAddress::MemorySubtree(
                        request.register_access.get_read_value_columns().start(),
                    );
                    compiled_linear_terms.push((
                        F::from_u64_unchecked(1 << indirects_alignment_log2)
                            .inverse()
                            .unwrap(),
                        place,
                    ));
                    let compiled_constraint = CompiledDegree1Constraint {
                        linear_terms: compiled_linear_terms.into_boxed_slice(),
                        constant_term: F::ZERO,
                    };
                    let expression = LookupExpression::Expression(compiled_constraint);
                    compiled_extra_range_check_16_expressions.push(expression);
                }

                let consider_aligned =
                    if indirects_alignment_log2 < std::mem::align_of::<u32>().trailing_zeros() {
                        false
                    } else {
                        indirect_accesses.len()
                            <= 1 << (indirects_alignment_log2
                                - std::mem::size_of::<u32>().trailing_zeros())
                    };

                // now process potential indirects
                for (idx, access) in indirect_accesses.into_iter().enumerate() {
                    let indirect_timestamp_borrow_var = add_compiler_defined_variable(
                        &mut num_variables,
                        &mut all_variables_to_place,
                    );
                    // NOTE: we do NOT add it into boolean vars array, otherwise it would be placed in the witness tree

                    boolean_vars.push(indirect_timestamp_borrow_var);

                    let indirect_read_timestamp_low = add_compiler_defined_variable(
                        &mut num_variables,
                        &mut all_variables_to_place,
                    );
                    let indirect_read_timestamp_high = add_compiler_defined_variable(
                        &mut num_variables,
                        &mut all_variables_to_place,
                    );

                    let indirect_read_timestamp_columns = layout_memory_subtree_multiple_variables(
                        &mut memory_tree_offset,
                        [indirect_read_timestamp_low, indirect_read_timestamp_high],
                        &mut all_variables_to_place,
                        &mut layout,
                    );

                    // compare that read timestamp < write timestamp, unless we are in the padding
                    {
                        let expr_low = LookupInput::from(
                            Constraint::empty()
                                + Term::from((
                                    F::from_u64_unchecked(1 << TIMESTAMP_COLUMNS_NUM_BITS),
                                    indirect_timestamp_borrow_var,
                                ))
                                + Term::from(indirect_read_timestamp_low)
                                - Term::from(delegation_timestamp_low_var),
                        );
                        timestamp_range_check_expressions_to_compile
                            .push(LookupInput::from(expr_low));

                        // for high part we need to use a predicate, so our comparison is only valid when we actually delegate,
                        // and can pad the rest with 0s
                        let expr_high = LookupInput::from(
                            Constraint::empty()
                                + Term::from((
                                    F::from_u64_unchecked(1 << TIMESTAMP_COLUMNS_NUM_BITS),
                                    predicate_variable,
                                ))
                                + Term::from(indirect_read_timestamp_high)
                                - Term::from(delegation_timestamp_high_var)
                                - Term::from(indirect_timestamp_borrow_var),
                        );
                        timestamp_range_check_expressions_to_compile
                            .push(LookupInput::from(expr_high));
                    }

                    // NOTE: we do NOT add it into boolean vars array, otherwise it would be placed in the witness tree.
                    // Instead we manually place it
                    let address_carry_column = if idx == 0 {
                        // nothing is needed
                        ColumnSet::empty()
                    } else {
                        if consider_aligned {
                            // we do not need to perform additional comparison, as adding constant offset
                            // would not trigger carries

                            ColumnSet::empty()
                        } else {
                            let address_carry_var = add_compiler_defined_variable(
                                &mut num_variables,
                                &mut all_variables_to_place,
                            );

                            layout_memory_subtree_variable(
                                &mut memory_tree_offset,
                                address_carry_var,
                                &mut all_variables_to_place,
                                &mut layout,
                            )
                        }
                    };

                    let offset = (idx * core::mem::size_of::<u32>()) as u32;
                    assert!(
                        offset < 1 << 16,
                        "offset {} is too large and not supported",
                        offset
                    );

                    // we enforce address derivation for our indirect accesses via lookup expressions
                    if idx > 0 {
                        // TODO: since we add constants and also have very small range of them,
                        // and do not want any overflows in high register, then we can save on range checks:
                        // - imagine register value as [low, high]
                        // - we need to somehow "materialize" and enforce lowest 16 limbs of the e.g. [low + 4],
                        // so we create a carry and place it into column, use range check to ensure that
                        // `low + 4 - 2^16 * carry` is 16 bits
                        // - for [high] part we do not allow overflows, so we want to ensure that [high + carry] != 2^16
                        // latter can be done via single extra witness (1 column), that is cheaper than range check (2.5 columns)

                        if consider_aligned == false {
                            assert!(address_carry_column.num_elements() > 0);

                            // low
                            let mut compiled_linear_terms = vec![];
                            let place = ColumnAddress::MemorySubtree(
                                request.register_access.get_read_value_columns().start(),
                            );
                            compiled_linear_terms.push((F::ONE, place));
                            let place = ColumnAddress::MemorySubtree(address_carry_column.start());
                            let mut coeff = F::from_u64_unchecked(SHIFT_16);
                            coeff.negate();
                            compiled_linear_terms.push((coeff, place));
                            let compiled_constraint = CompiledDegree1Constraint {
                                linear_terms: compiled_linear_terms.into_boxed_slice(),
                                constant_term: F::from_u64_unchecked(offset as u64),
                            };
                            let expression = LookupExpression::Expression(compiled_constraint);
                            compiled_extra_range_check_16_expressions.push(expression);

                            // high
                            let mut compiled_linear_terms = vec![];
                            let place = ColumnAddress::MemorySubtree(
                                request.register_access.get_read_value_columns().start() + 1,
                            );
                            compiled_linear_terms.push((F::ONE, place));
                            let place = ColumnAddress::MemorySubtree(address_carry_column.start());
                            compiled_linear_terms.push((F::ONE, place));
                            let compiled_constraint = CompiledDegree1Constraint {
                                linear_terms: compiled_linear_terms.into_boxed_slice(),
                                constant_term: F::ZERO,
                            };
                            let expression = LookupExpression::Expression(compiled_constraint);
                            compiled_extra_range_check_16_expressions.push(expression);
                        }
                    }

                    let indirect_access = match access {
                        IndirectAccessType::Read { read_value } => {
                            let indirect_read_value_columns =
                                layout_memory_subtree_multiple_variables(
                                    &mut memory_tree_offset,
                                    read_value,
                                    &mut all_variables_to_place,
                                    &mut layout,
                                );

                            let request = IndirectAccessColumns::ReadAccess {
                                read_timestamp: indirect_read_timestamp_columns,
                                read_value: indirect_read_value_columns,
                                offset,
                                address_derivation_carry_bit: address_carry_column,
                            };

                            request
                        }
                        IndirectAccessType::Write {
                            read_value,
                            write_value,
                        } => {
                            let indirect_read_value_columns =
                                layout_memory_subtree_multiple_variables(
                                    &mut memory_tree_offset,
                                    read_value,
                                    &mut all_variables_to_place,
                                    &mut layout,
                                );
                            let indirect_write_value_columns =
                                layout_memory_subtree_multiple_variables(
                                    &mut memory_tree_offset,
                                    write_value,
                                    &mut all_variables_to_place,
                                    &mut layout,
                                );

                            let request = IndirectAccessColumns::WriteAccess {
                                read_timestamp: indirect_read_timestamp_columns,
                                read_value: indirect_read_value_columns,
                                write_value: indirect_write_value_columns,
                                offset,
                                address_derivation_carry_bit: address_carry_column,
                            };

                            request
                        }
                    };

                    indirect_timestamp_comparison_borrows.push(indirect_timestamp_borrow_var);

                    request.indirect_accesses.push(indirect_access);
                }

                aux_vars
                    .register_and_indirect_access_timestamp_aux_sets
                    .push((
                        register_timestamp_borrow_var,
                        indirect_timestamp_comparison_borrows,
                    ));

                register_and_indirect_accesses.push(request);
            }

            let delegation_processor_layout = DelegationProcessingLayout {
                multiplicity: delegation_request_predicate_column,
                abi_mem_offset_high: delegation_request_mem_offset_high_column,
                write_timestamp: delegation_request_timestamp,
            };

            let memory_subtree_placement = MemorySubtree {
                shuffle_ram_inits_and_teardowns: None,
                shuffle_ram_access_sets: vec![],
                delegation_request_layout: None,
                delegation_processor_layout: Some(delegation_processor_layout),
                batched_ram_accesses: vec![],
                register_and_indirect_accesses,
                total_width: memory_tree_offset,
            };

            (memory_subtree_placement, None, vec![], Some(aux_vars))
        } else {
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

            let lazy_init_aux_set = {
                let tmp_low_var =
                    add_compiler_defined_variable(&mut num_variables, &mut all_variables_to_place);
                let tmp_high_var =
                    add_compiler_defined_variable(&mut num_variables, &mut all_variables_to_place);
                let intermediate_borrow_var =
                    add_compiler_defined_variable(&mut num_variables, &mut all_variables_to_place);
                let final_borrow_var =
                    add_compiler_defined_variable(&mut num_variables, &mut all_variables_to_place);

                let lazy_init_aux_set = (
                    [tmp_low_var, tmp_high_var],
                    intermediate_borrow_var,
                    final_borrow_var,
                );
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

                lazy_init_aux_set
            };

            let shuffle_ram_init_addresses = add_multiple_compiler_defined_variables::<REGISTER_SIZE>(
                &mut num_variables,
                &mut all_variables_to_place,
            );
            let shuffle_ram_teardown_values = add_multiple_compiler_defined_variables::<
                REGISTER_SIZE,
            >(
                &mut num_variables, &mut all_variables_to_place
            );
            let shuffle_ram_teardown_timestamps = add_multiple_compiler_defined_variables::<
                NUM_TIMESTAMP_COLUMNS_FOR_RAM,
            >(
                &mut num_variables, &mut all_variables_to_place
            );

            // NOTE: here we use only register width because it's implied 0-value column for "is_register",
            // as we zero-init only RAM and not the registers

            // NOTE: we will separately add to the quotient and range check 16 layouts in stage 2 parts the fact that
            // lazy init addresses are under range check 16
            let lazy_init_addresses_columns = layout_memory_subtree_multiple_variables(
                &mut memory_tree_offset,
                shuffle_ram_init_addresses,
                &mut all_variables_to_place,
                &mut layout,
            );
            let lazy_teardown_values_columns = layout_memory_subtree_multiple_variables(
                &mut memory_tree_offset,
                shuffle_ram_teardown_values,
                &mut all_variables_to_place,
                &mut layout,
            );
            let lazy_teardown_timestamps_columns = layout_memory_subtree_multiple_variables(
                &mut memory_tree_offset,
                shuffle_ram_teardown_timestamps,
                &mut all_variables_to_place,
                &mut layout,
            );

            assert!(shuffle_ram_queries
                .is_sorted_by(|a, b| a.local_timestamp_in_cycle < b.local_timestamp_in_cycle));
            shuffle_ram_queries.windows(2).for_each(|el| {
                assert!(el[0].local_timestamp_in_cycle + 1 == el[1].local_timestamp_in_cycle)
            });

            // and we need to check that read timestamp < write timestamp. This one is in-row, so we are good, but we first will finish
            // with lazy init/teardown and declare teardown variables

            // Note that write timestamp is virtual and is formed from in-cycle index, cycle timestamp coming from setup,
            // and circuit index coming from prover and checked in recursion, but we will need to put all the same variables
            // to check `less than` constraints

            let mut shuffle_ram_access_sets = vec![];
            let mut memory_timestamp_comparison_sets = vec![];

            for (query_idx, memory_query) in shuffle_ram_queries.iter().enumerate() {
                assert_eq!(query_idx, memory_query.local_timestamp_in_cycle);

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

                // now that we have declared timestamps, we can produce comparison expressions for range checks
                let borrow_var =
                    add_compiler_defined_variable(&mut num_variables, &mut all_variables_to_place);
                boolean_vars.push(borrow_var);

                let partial_data = ShuffleRamTimestampComparisonPartialData {
                    intermediate_borrow: borrow_var,
                    read_timestamp: [read_timestamp_low, read_timestamp_high],
                    local_timestamp_in_cycle: memory_query.local_timestamp_in_cycle,
                };
                shuffle_ram_extra_range_check_16_partial_sets.push(partial_data);

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

                        ShuffleRamAddress::RegisterOnly(RegisterOnlyAccessAddress {
                            register_index,
                        })
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
                        // write_timestamp,
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
                        // write_timestamp,
                        read_value,
                        write_value,
                    };

                    ShuffleRamQueryColumns::Write(query_columns)
                };

                shuffle_ram_access_sets.push(query_columns);
            }

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
                    degegation_type,
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
                    degegation_type,
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

            let shuffle_ram_inits_and_teardowns = ShuffleRamInitAndTeardownLayout {
                lazy_init_addresses_columns,
                lazy_teardown_values_columns,
                lazy_teardown_timestamps_columns,
            };

            let memory_subtree_placement = MemorySubtree {
                shuffle_ram_inits_and_teardowns: Some(shuffle_ram_inits_and_teardowns),
                shuffle_ram_access_sets,
                delegation_request_layout,
                delegation_processor_layout: None,
                batched_ram_accesses: vec![],
                register_and_indirect_accesses: vec![],
                total_width: memory_tree_offset,
            };

            // NOTE: we do NOT need extra constraints here, as they will be evaluated by specialized prover as
            // - timestamp_low = setup_timestamp_low + 0/1/2/3
            // - timestamp_high = setup_timestamp_high + circuit index_offset

            (
                memory_subtree_placement,
                Some(lazy_init_aux_set),
                memory_timestamp_comparison_sets,
                None,
            )
        };

        // now we need to satisfy placement that have constraints on their layout. Luckily there is only one such kind here
        // - we need to put lookup variables into corresponding columns, as well as memory ones

        // We placed ALL memory related values, and now we can place witness subtree.

        // We start with multiplicities

        // then lookup ones

        let mut witness_tree_offset = 0;
        let multiplicities_columns_for_range_check_16 =
            ColumnSet::layout_at(&mut witness_tree_offset, 1);
        let multiplicities_columns_for_timestamp_range_check =
            ColumnSet::layout_at(&mut witness_tree_offset, 1);

        let multiplicities_columns_for_generic_lookup = ColumnSet::layout_at(
            &mut witness_tree_offset,
            num_required_tuples_for_generic_lookup_setup,
        );

        for range_check in range_check_expressions.iter() {
            let RangeCheckQuery { input, width } = range_check;
            let LookupInput::Variable(..) = input else {
                unimplemented!()
            };
            assert!(
                *width == LARGE_RANGE_CHECK_TABLE_WIDTH || *width == SMALL_RANGE_CHECK_TABLE_WIDTH
            );
        }

        // We will place 8-bit range check variables, and then 16-bit ones

        let range_check_8_iter = range_check_expressions
            .iter()
            .filter(|el| el.width == SMALL_RANGE_CHECK_TABLE_WIDTH);
        let range_check_16_iter = range_check_expressions
            .iter()
            .filter(|el| el.width == LARGE_RANGE_CHECK_TABLE_WIDTH);

        let num_range_check_8 = range_check_8_iter.clone().count();
        let num_range_check_16 = range_check_16_iter.clone().count();

        let range_check_8_columns: ColumnSet<1> =
            ColumnSet::layout_at(&mut witness_tree_offset, num_range_check_8);
        let range_check_8_columns_it = range_check_8_columns.iter();

        for (input, mut layout_part) in range_check_8_iter.zip(range_check_8_columns_it) {
            let LookupInput::Variable(input) = input.input else {
                unimplemented!()
            };
            let offset = layout_part.next().unwrap();
            let _place = layout_witness_subtree_variable_at_column(
                offset,
                input,
                &mut all_variables_to_place,
                &mut layout,
            );
        }

        // range checks 16 deserve their own treatment and own table, and for lookups over explicit variables
        // we just layout those continuously in the row. We will also declare formal lookup expressions over them,
        // as below we will declare less-trivial range-check 16 expressions

        let mut range_check_16_lookup_expressions = vec![];

        // TODO
        // we may have special case where we required invariant for some variable, that would end up in
        // memory columns, but we do NOT handle it yet and will panic on it below

        let range_check_16_columns: ColumnSet<1> =
            ColumnSet::layout_at(&mut witness_tree_offset, num_range_check_16);

        for (range_check, layout_part) in range_check_16_iter.zip(range_check_16_columns.iter()) {
            let RangeCheckQuery { input, .. } = range_check;
            let LookupInput::Variable(variable) = input else {
                unimplemented!()
            };
            let mut layout_part = layout_part;
            let offset = layout_part.next().unwrap();
            let place = layout_witness_subtree_variable_at_column(
                offset,
                *variable,
                &mut all_variables_to_place,
                &mut layout,
            );
            let lookup_expr = LookupExpression::Variable(place);
            range_check_16_lookup_expressions.push(lookup_expr)
        }

        range_check_16_lookup_expressions.extend(compiled_extra_range_check_16_expressions);

        // Now we will pause and place boolean variables, as those can have their constraints special-handled in quotient

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

        // width 3 tables

        let mut width_3_lookups = vec![];

        for lookup_query in lookups {
            let LookupQuery { row, table } = lookup_query;
            assert_eq!(row.len(), 3);

            let mut input_columns = Vec::with_capacity(3);
            for el in row.into_iter() {
                match el {
                    LookupInput::Variable(single_var) => {
                        let place = if let Some(place) = layout.get(&single_var) {
                            // it's already placed
                            *place
                        } else {
                            let column = layout_witness_subtree_variable(
                                &mut witness_tree_offset,
                                single_var,
                                &mut all_variables_to_place,
                                &mut layout,
                            );
                            let place = ColumnAddress::WitnessSubtree(column.start);

                            place
                        };

                        let lookup_expr = LookupExpression::Variable(place);
                        input_columns.push(lookup_expr);
                    }
                    LookupInput::Expression {
                        linear_terms,
                        constant_coeff,
                    } => {
                        // place all of them
                        let mut compiled_linear_terms = vec![];
                        for (coeff, var) in linear_terms.iter() {
                            let place = if let Some(place) = layout.get(var) {
                                // it's already placed
                                *place
                            } else {
                                let column = layout_witness_subtree_variable(
                                    &mut witness_tree_offset,
                                    *var,
                                    &mut all_variables_to_place,
                                    &mut layout,
                                );
                                let place = ColumnAddress::WitnessSubtree(column.start);

                                place
                            };
                            compiled_linear_terms.push((*coeff, place));
                        }
                        let compiled_constraint = CompiledDegree1Constraint {
                            linear_terms: compiled_linear_terms.into_boxed_slice(),
                            constant_term: constant_coeff,
                        };
                        let lookup_expr = LookupExpression::Expression(compiled_constraint);
                        input_columns.push(lookup_expr);
                    }
                }
            }

            let table_index = match table {
                LookupQueryTableType::Constant(constant) => TableIndex::Constant(constant),
                LookupQueryTableType::Variable(variable) => {
                    let column = layout_witness_subtree_variable(
                        &mut witness_tree_offset,
                        variable,
                        &mut all_variables_to_place,
                        &mut layout,
                    );
                    let place = ColumnAddress::WitnessSubtree(column.start);
                    TableIndex::Variable(place)
                }
            };

            let lookup = LookupSetDescription {
                input_columns: input_columns.try_into().unwrap(),
                table_index,
            };
            width_3_lookups.push(lookup);
        }

        let total_generic_lookups = width_3_lookups.len() as u64 * trace_len as u64;
        assert!(total_generic_lookups < F::CHARACTERISTICS, "total number of generic lookups in circuit is {} that is larger that field characteristics {}", total_generic_lookups, F::CHARACTERISTICS);

        let mut compiled_timestamp_comparison_expressions = vec![];

        // we already have enough information to compile range check expressions that are left from memory accesses layout
        for input in timestamp_range_check_expressions_to_compile.into_iter() {
            let LookupInput::Expression {
                linear_terms,
                constant_coeff,
            } = input
            else {
                panic!()
            };
            // place all of them
            let mut compiled_linear_terms = vec![];
            for (coeff, var) in linear_terms.iter() {
                let place = layout
                    .get(var)
                    .copied()
                    .expect("all variables must be already placed");
                compiled_linear_terms.push((*coeff, place));
            }
            let compiled_constraint = CompiledDegree1Constraint {
                linear_terms: compiled_linear_terms.into_boxed_slice(),
                constant_term: constant_coeff,
            };
            let lookup_expr = LookupExpression::Expression(compiled_constraint);
            compiled_timestamp_comparison_expressions.push(lookup_expr);
        }

        let offset_for_special_shuffle_ram_timestamps_range_check_expressions = {
            // timestamps deserve separate range checks for shuffle RAM in the main circuit,
            // as those also take contribution from circuit index in the sequence

            // NOTE: these expressions are separate, as we will have to add to them a circuit sequence constant
            // that comes during the proving only

            let offset_for_special_shuffle_ram_timestamps_range_check_expressions =
                compiled_timestamp_comparison_expressions.len();

            for data in shuffle_ram_extra_range_check_16_partial_sets.into_iter() {
                let ShuffleRamTimestampComparisonPartialData {
                    intermediate_borrow,
                    read_timestamp,
                    local_timestamp_in_cycle,
                } = data;
                let [read_low, read_high] = read_timestamp;
                // we know all the places, but will have to manually compile it into degree-1 constraint

                // low part
                {
                    let mut compiled_linear_terms = vec![];
                    let borrow_place = *layout.get(&intermediate_borrow).unwrap();
                    compiled_linear_terms.push((
                        F::from_u64_unchecked(1 << TIMESTAMP_COLUMNS_NUM_BITS),
                        borrow_place,
                    ));
                    let read_low_place = *layout.get(&read_low).unwrap();
                    compiled_linear_terms.push((F::ONE, read_low_place));

                    // have to manually create write low place
                    let write_low_place =
                        ColumnAddress::SetupSubtree(setup_layout.timestamp_setup_columns.start());
                    compiled_linear_terms.push((F::MINUS_ONE, write_low_place));

                    // and we also have a constant of `- in cycle local write`
                    let mut constant_coeff = F::from_u64_unchecked(local_timestamp_in_cycle as u64);
                    constant_coeff.negate();

                    let compiled_constraint = CompiledDegree1Constraint {
                        linear_terms: compiled_linear_terms.into_boxed_slice(),
                        constant_term: constant_coeff,
                    };
                    let lookup_expr = LookupExpression::Expression(compiled_constraint);
                    compiled_timestamp_comparison_expressions.push(lookup_expr);
                }
                // and almost the same for high part
                {
                    let mut compiled_linear_terms = vec![];
                    let read_high_place = *layout.get(&read_high).unwrap();
                    compiled_linear_terms.push((F::ONE, read_high_place));

                    let write_high_place = ColumnAddress::SetupSubtree(
                        setup_layout.timestamp_setup_columns.start() + 1,
                    );
                    compiled_linear_terms.push((F::MINUS_ONE, write_high_place));

                    // subtract borrow
                    let borrow_place = *layout.get(&intermediate_borrow).unwrap();
                    compiled_linear_terms.push((F::MINUS_ONE, borrow_place));

                    let constant_coeff = F::from_u64_unchecked(1 << TIMESTAMP_COLUMNS_NUM_BITS);
                    let compiled_constraint = CompiledDegree1Constraint {
                        linear_terms: compiled_linear_terms.into_boxed_slice(),
                        constant_term: constant_coeff,
                    };
                    let lookup_expr = LookupExpression::Expression(compiled_constraint);
                    compiled_timestamp_comparison_expressions.push(lookup_expr);
                }
            }

            offset_for_special_shuffle_ram_timestamps_range_check_expressions
        };

        #[cfg(feature = "debug_logs")]
        {
            dbg!(range_check_16_lookup_expressions.len());
        }

        let total_lookups_for_range_checks_16 =
            range_check_16_lookup_expressions.len() as u64 * trace_len as u64;
        assert!(total_lookups_for_range_checks_16 < F::CHARACTERISTICS, "total number of range-check-16 lookups in circuit is {} that is larger that field characteristics {}", total_lookups_for_range_checks_16, F::CHARACTERISTICS);

        let total_timestamp_range_check_lookups =
            compiled_timestamp_comparison_expressions.len() as u64 * trace_len as u64;
        assert!(total_timestamp_range_check_lookups < F::CHARACTERISTICS, "total number of timestamp range check lookups in circuit is {} that is larger that field characteristics {}", total_timestamp_range_check_lookups, F::CHARACTERISTICS);

        // now check if there exist any variables that are
        // - not yet placed (so - not lookup ins/outs)
        // - can be expressed via linear constraint
        // - can be substituted into other places

        // TODO: make multiple runs
        let optimized_out_variables = {
            let initial_len = all_variables_to_place.len();
            let mut optimized_out_variables = vec![];
            let mut tried_variables = BTreeSet::new();
            'outer: loop {
                // we will try to remove every variable in there
                let mut to_remove: Option<(Variable, Vec<usize>, Vec<usize>)> = None;
                for variable in all_variables_to_place.iter() {
                    if optimized_out_variables.contains(variable) {
                        continue;
                    }

                    if tried_variables.contains(variable) {
                        continue;
                    }

                    // we need
                    // - some "defining" constraint where variable comes as the first degree
                    // - potentially other constraints that contain such variable
                    let mut defining_constraints = vec![];

                    for (constraint_id, (constraint, prevent_optimizations)) in
                        constraints.iter().enumerate()
                    {
                        if *prevent_optimizations {
                            continue;
                        }
                        if constraint.degree() > 1 {
                            continue;
                        }
                        if constraint.degree_for_var(variable) == 0 {
                            continue;
                        }
                        defining_constraints.push((constraint_id, constraint));
                    }

                    // check if variable is not a placeholder
                    for (_, v) in substitutions.iter() {
                        if v == variable {
                            continue 'outer;
                        }
                    }

                    // it also can not be state input or output
                    if state_input.contains(&variable) {
                        continue;
                    }

                    if state_output.contains(&variable) {
                        continue;
                    }

                    if defining_constraints.len() > 0 {
                        let mut occurrences = vec![];

                        for (constraint_id, (constraint, _)) in constraints.iter().enumerate() {
                            if constraint.contains_var(variable)
                                && constraint.degree_for_var(variable) < 2
                            {
                                occurrences.push((constraint_id, constraint));
                            }
                        }

                        if occurrences.len() > 1 {
                            // defining constraint will be here too
                            to_remove = Some((
                                *variable,
                                defining_constraints.iter().map(|el| el.0).collect(),
                                occurrences.iter().map(|el| el.0).collect(),
                            ));
                            break;
                        }
                    }
                }

                //     println!("===============================================");
                //     println!("Can try to optimize out variable {:?}", variable);
                //     for (_, el) in defining_constraints.into_iter() {
                //         println!("Can be defined via {:?}", el);
                //     }
                //     println!("-----------------------------------------------");
                //     for (_, el) in occurrences.into_iter() {
                //         println!("Can be substituted into {:?}", el);
                //     }
                //     println!("===============================================");

                //     candidates.insert(*variable);
                // }

                if to_remove.is_none() {
                    break 'outer;
                }

                let Some((variable_to_optimize_out, defining_constraints, occurrences)) = to_remove
                else {
                    panic!();
                };

                let mut optimized_out_params = None;

                for defining_constraint_idx in defining_constraints.into_iter() {
                    // for now there is no heuristics to prefer one defining constraint over another,
                    // but let's try all

                    let defining_constraint = constraints[defining_constraint_idx].0.clone();
                    // now we should rewrite it to factor out linear term
                    let mut expression =
                        defining_constraint.express_variable(variable_to_optimize_out);
                    expression.normalize();

                    #[cfg(feature = "debug_logs")]
                    {
                        println!("===============================================");
                        println!(
                            "Will try to optimize out the variable {:?} using constraint {:?}",
                            variable_to_optimize_out, &defining_constraint
                        );
                        println!(
                            "Expression for variable {:?} is degree {} = {:?}",
                            variable_to_optimize_out,
                            expression.degree(),
                            &expression
                        );
                    }

                    let mut can_be_optimized_out = true;
                    let mut replacement_constraints = vec![];
                    // now we should walk over other constraints and rewrite them
                    for occurrence_constraint_idx in occurrences.iter().copied() {
                        if occurrence_constraint_idx == defining_constraint_idx {
                            continue;
                        }

                        let existing_constraint = constraints[occurrence_constraint_idx].0.clone();
                        let rewritten_constraint = existing_constraint
                            .clone()
                            .substitute_variable(variable_to_optimize_out, expression.clone());
                        #[cfg(feature = "debug_logs")]
                        {
                            println!("-----------------------------------------------");
                            println!(
                                "Will try to rewrite {:?} as {:?}",
                                &existing_constraint, &rewritten_constraint
                            );
                        }

                        if rewritten_constraint.degree() > 2 {
                            #[cfg(feature = "debug_logs")]
                            {
                                println!(
                                    "Resultring constraint {:?} is of degree {}",
                                    &rewritten_constraint,
                                    rewritten_constraint.degree()
                                );
                            }
                            can_be_optimized_out = false;
                            break;
                        } else {
                            replacement_constraints
                                .push((occurrence_constraint_idx, rewritten_constraint));
                        }
                    }

                    #[cfg(feature = "debug_logs")]
                    {
                        println!("-----------------------------------------------");
                    }
                    if can_be_optimized_out {
                        optimized_out_params =
                            Some((defining_constraint_idx, replacement_constraints));
                    } else {
                        tried_variables.insert(variable_to_optimize_out);
                    }
                }

                if let Some((defining_constraint_idx, replacement_constraints)) =
                    optimized_out_params
                {
                    #[cfg(feature = "debug_logs")]
                    {
                        println!(
                            "Successfully removed variable {:?}",
                            variable_to_optimize_out
                        );
                    }
                    let existed = all_variables_to_place.remove(&variable_to_optimize_out);
                    assert!(existed);
                    optimized_out_variables.push(variable_to_optimize_out);
                    // now we should carefully remove all the constraints
                    let mut removal_set = BTreeMap::new();
                    removal_set.insert(defining_constraint_idx, None);
                    for (k, v) in replacement_constraints.into_iter() {
                        removal_set.insert(k, Some(v));
                    }

                    let mut new_constraints = vec![];
                    for (idx, constraint) in std::mem::replace(&mut constraints, vec![])
                        .into_iter()
                        .enumerate()
                    {
                        if let Some(replacement) = removal_set.get(&idx) {
                            let mut constraint = constraint;
                            if let Some(replacement) = replacement {
                                constraint.0 = replacement.clone();
                                new_constraints.push(constraint);
                            } else {
                                // just remove
                            }
                        } else {
                            new_constraints.push(constraint);
                        }
                    }

                    constraints = new_constraints;
                } else {
                    #[cfg(feature = "debug_logs")]
                    {
                        println!("Can not remove variable {:?}", variable_to_optimize_out);
                    }
                }
                #[cfg(feature = "debug_logs")]
                {
                    println!("===============================================");
                }
            }

            #[cfg(feature = "debug_logs")]
            {
                dbg!(optimized_out_variables.len());
            }
            // dbg!(&optimized_out_variables);

            assert_eq!(
                initial_len,
                optimized_out_variables.len() + all_variables_to_place.len()
            );

            optimized_out_variables
        };

        #[cfg(feature = "debug_logs")]
        {
            println!(
                "{} variables were optimized out via linear constraint substitution",
                optimized_out_variables.len()
            );
        }

        let scratch_space_size_for_witness_gen = optimized_out_variables.len();

        // those can be placed into scratch space right now
        let mut optimized_out_offset = 0;
        for var in optimized_out_variables.into_iter() {
            layout.insert(var, ColumnAddress::OptimizedOut(optimized_out_offset));
            optimized_out_offset += 1;
        }

        let mut scratch_space_columns_start = witness_tree_offset;
        let scratch_space_columns_range = ColumnSet::layout_at(
            &mut scratch_space_columns_start,
            all_variables_to_place.len(),
        );

        // and then we will just place all other variable
        for variable in all_variables_to_place.into_iter() {
            layout.insert(variable, ColumnAddress::WitnessSubtree(witness_tree_offset));
            witness_tree_offset += 1;
        }

        assert_eq!(
            scratch_space_columns_range.full_range().end,
            witness_tree_offset
        );

        for (constraint, _) in constraints.into_iter() {
            assert!(constraint
                .terms
                .is_sorted_by(|a, b| a.degree() >= b.degree()));

            match constraint.degree() {
                2 => {
                    let mut quadratic_terms = vec![];
                    let mut linear_terms = vec![];
                    let mut constant_term = F::ZERO;
                    for term in constraint.terms.into_iter() {
                        match term.degree() {
                            2 => {
                                let coeff = term.get_coef();
                                let [a, b] = term.as_slice() else { panic!() };
                                assert!(*a <= *b);
                                let a = layout.get(a).copied().unwrap();
                                let b = layout.get(b).copied().unwrap();
                                quadratic_terms.push((coeff, a, b));
                            }
                            1 => {
                                let coeff = term.get_coef();
                                let [a] = term.as_slice() else { panic!() };
                                let a = layout.get(a).copied().unwrap();
                                linear_terms.push((coeff, a));
                            }
                            0 => {
                                constant_term.add_assign(&term.get_coef());
                            }
                            _ => {
                                unreachable!()
                            }
                        }
                    }

                    let compiled_term = CompiledDegree2Constraint {
                        quadratic_terms: quadratic_terms.into_boxed_slice(),
                        linear_terms: linear_terms.into_boxed_slice(),
                        constant_term,
                    };

                    compiled_quadratic_terms.push(compiled_term);
                }
                1 => {
                    let mut linear_terms = vec![];
                    let mut constant_term = F::ZERO;
                    for term in constraint.terms.into_iter() {
                        match term.degree() {
                            1 => {
                                let coeff = term.get_coef();
                                let [a] = term.as_slice() else { panic!() };
                                let a = layout.get(a).copied().unwrap();
                                linear_terms.push((coeff, a));
                            }
                            0 => {
                                constant_term.add_assign(&term.get_coef());
                            }
                            _ => {
                                unreachable!()
                            }
                        }
                    }

                    let compiled_term = CompiledDegree1Constraint {
                        linear_terms: linear_terms.into_boxed_slice(),
                        constant_term,
                    };

                    compiled_linear_terms.push(compiled_term);
                }
                _ => {
                    unreachable!()
                }
            }
        }

        #[cfg(feature = "debug_logs")]
        {
            dbg!(compiled_quadratic_terms.len());
            dbg!(compiled_linear_terms.len());
        }

        // we need only the following public inputs
        // - initial state variable at FIRST row
        // - final state variable at one row before last
        // - memory argument lazy init address at first and one row before last

        // we should add our only single linking constraint to link state -> state
        assert_eq!(state_input.len(), state_output.len());
        let mut linking_constraints = vec![];
        let mut public_inputs_first_row = vec![];
        let mut public_inputs_one_row_before_last = vec![];
        for (i, f) in state_input.into_iter().zip(state_output.into_iter()) {
            // final -> NEXT initial
            let i = layout.get(&i).expect("must be compiled");
            let f = layout.get(&f).expect("must be compiled");
            linking_constraints.push((*f, *i));
            public_inputs_first_row.push((BoundaryConstraintLocation::FirstRow, *i));
            public_inputs_one_row_before_last
                .push((BoundaryConstraintLocation::OneBeforeLastRow, *f));
        }

        let mut public_inputs = public_inputs_first_row;
        public_inputs.extend(public_inputs_one_row_before_last);

        if FOR_DELEGATION {
            assert!(public_inputs.is_empty());
        } else {
            assert!(public_inputs.len() > 0);
        }

        // NOTE: we do not need to add lazy init into boundary constraints as we will handle them manually

        // all substitutions will be processed by witness generators before the main routine, so we can just use a vector for them
        let mut compiled_substitutions = Vec::with_capacity(substitutions.len());

        for (k, v) in substitutions.iter() {
            let place = layout.get(&v).copied().expect("must be compiled");
            compiled_substitutions.push((*k, place));
        }

        let lazy_init_address_aux_vars =
            lazy_init_aux_set.map(|(comparison_aux_vars, intermediate_borrow, final_borrow)| {
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
            });

        let witness_layout = WitnessSubtree {
            multiplicities_columns_for_range_check_16,
            multiplicities_columns_for_timestamp_range_check,
            multiplicities_columns_for_generic_lookup,
            range_check_8_columns,
            range_check_16_columns,
            width_3_lookups,
            range_check_16_lookup_expressions,
            timestamp_range_check_lookup_expressions: compiled_timestamp_comparison_expressions,
            offset_for_special_shuffle_ram_timestamps_range_check_expressions,
            boolean_vars_columns_range,
            scratch_space_columns_range,
            total_width: witness_tree_offset,
        };

        // then produce specific sets, that make our descriptions easier
        let memory_queries_timestamp_comparison_aux_vars = if FOR_DELEGATION {
            vec![]
        } else {
            let memory_queries_timestamp_comparison_aux_vars: Vec<_> =
                memory_timestamp_comparison_sets
                    .into_iter()
                    .map(|el| {
                        let borrow = layout.get(&el).copied().expect("must be compiled");

                        borrow
                    })
                    .collect();

            memory_queries_timestamp_comparison_aux_vars
        };

        let batched_memory_access_timestamp_comparison_aux_vars = if FOR_DELEGATION {
            let aux_vars = delegation_ram_access_aux_vars.as_ref().unwrap();

            let mut data = BatchedRamTimestampComparisonAuxVars {
                predicate: aux_vars.predicate,
                write_timestamp: aux_vars.write_timestamp_for_comparison,
                write_timestamp_columns: aux_vars.write_timestamp_columns,
                aux_borrow_vars: vec![],
            };

            data.aux_borrow_vars = aux_vars
                .batched_ram_access_timestamp_aux_sets
                .iter()
                .map(|el| {
                    let borrow = layout.get(el).copied().expect("must be compiled");

                    borrow
                })
                .collect();

            data
        } else {
            BatchedRamTimestampComparisonAuxVars {
                predicate: ColumnAddress::placeholder(),
                write_timestamp: [ColumnAddress::placeholder(); 2],
                write_timestamp_columns: ColumnSet::empty(),
                aux_borrow_vars: vec![],
            }
        };

        let register_and_indirect_access_timestamp_comparison_aux_vars = if FOR_DELEGATION {
            let aux_vars = delegation_ram_access_aux_vars.as_ref().unwrap();

            let mut data = RegisterAndIndirectAccessTimestampComparisonAuxVars {
                predicate: aux_vars.predicate,
                write_timestamp: aux_vars.write_timestamp_for_comparison,
                write_timestamp_columns: aux_vars.write_timestamp_columns,
                aux_borrow_sets: vec![],
            };

            data.aux_borrow_sets = aux_vars
                .register_and_indirect_access_timestamp_aux_sets
                .iter()
                .map(|(el, set)| {
                    let borrow = layout.get(el).copied().expect("must be compiled");
                    let set: Vec<_> = set
                        .iter()
                        .map(|el| layout.get(el).copied().expect("must be compiled"))
                        .collect();

                    (borrow, set)
                })
                .collect();

            data
        } else {
            RegisterAndIndirectAccessTimestampComparisonAuxVars {
                predicate: ColumnAddress::placeholder(),
                write_timestamp: [ColumnAddress::placeholder(); 2],
                write_timestamp_columns: ColumnSet::empty(),
                aux_borrow_sets: vec![],
            }
        };

        assert_eq!(
            setup_layout.generic_lookup_setup_columns.num_elements(),
            num_required_tuples_for_generic_lookup_setup
        );

        let stage_2_layout = LookupAndMemoryArgumentLayout::from_compiled_parts(
            &witness_layout,
            &memory_subtree_placement,
            &setup_layout,
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
            memory_layout: memory_subtree_placement,
            setup_layout,
            stage_2_layout,
            degree_2_constraints: compiled_quadratic_terms,
            degree_1_constraints: compiled_linear_terms,
            state_linkage_constraints: linking_constraints,
            public_inputs,
            scratch_space_size_for_witness_gen,
            variable_mapping: layout,
            lazy_init_address_aux_vars,
            memory_queries_timestamp_comparison_aux_vars,
            batched_memory_access_timestamp_comparison_aux_vars,
            register_and_indirect_access_timestamp_comparison_aux_vars,
            trace_len,
            table_offsets,
            total_tables_size,
        };

        result
    }
}
