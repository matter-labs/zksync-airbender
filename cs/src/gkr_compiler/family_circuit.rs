use super::*;

use crate::constraint::Constraint;
use crate::constraint::Term;
use crate::cs::circuit::LookupQuery;
use crate::cs::circuit_output::CircuitOutput;
use crate::cs::circuit_trait::MemoryAccess;
use crate::cs::circuit_trait::RegisterAccess;
use crate::cs::circuit_trait::RegisterOrRamAccess;
use crate::cs::circuit_trait::WordRepresentation;
use crate::definitions::gkr::*;
use crate::definitions::GKRAddress;
use crate::definitions::LookupInput;
use crate::definitions::Variable;
use crate::gkr_compiler::graph::GKRGraph;
use crate::gkr_compiler::graph::GraphHolder;
use crate::gkr_compiler::layout::LookupOutput;
use crate::types::Boolean;

impl<F: PrimeField> GKRCompiler<F> {
    pub fn compile_family_circuit(
        &self,
        circuit_output: CircuitOutput<F>,
        max_bytecode_size_in_words: usize,
        num_inits_and_teardowns: usize,
        trace_len_log2: usize,
    ) -> GKRCircuitArtifact<F> {
        assert!(max_bytecode_size_in_words.is_power_of_two());
        assert_eq!(num_inits_and_teardowns, 0, "TODO");

        let CircuitOutput {
            table_driver,
            num_of_variables,
            constraints,
            lookups,
            memory_queries,
            range_check_expressions,
            boolean_vars,
            substitutions,
            register_and_indirect_memory_accesses,
            executor_machine_state,
            delegation_circuit_state,
            circuit_family_bitmask,
            variable_names,
            variables_from_constraints,
            layers_mapping,
            ..
        } = circuit_output;

        assert!(trace_len_log2 >= TIMESTAMP_COLUMNS_NUM_BITS as usize);

        assert!(register_and_indirect_memory_accesses.is_empty());
        assert!(delegation_circuit_state.is_none());

        let trace_len = 1usize << trace_len_log2;

        let mut variable_names = variable_names;

        // we merge decoder and generic tables as it's always beneficial
        let mut total_tables_size = table_driver.total_tables_len;
        let offset_for_decoder_table = total_tables_size;
        total_tables_size += max_bytecode_size_in_words;

        let lookup_table_encoding_capacity = trace_len;
        let num_required_tuples_for_lookup_setup =
            total_tables_size.div_ceil(lookup_table_encoding_capacity);
        assert!(num_required_tuples_for_lookup_setup <= 1);

        let mut constraints = constraints;
        let mut variables_from_constraints = variables_from_constraints;
        let mut layers_mapping = layers_mapping;

        let executor_machine_state =
            executor_machine_state.expect("must be present in executor circuit");

        let mut boolean_vars = boolean_vars;
        let mut num_variables = num_of_variables as u64;

        // quickly compute generic lookup table width

        let (range_check_16_expressions, mut generic_lookups) =
            super::range_check_exprs::split_range_check_exprs_from_compiler::<F>(
                &range_check_expressions,
            );
        let total_lookups_for_range_checks_16 =
            (range_check_16_expressions.len() as u64) * trace_len as u64;
        assert!(total_lookups_for_range_checks_16 < F::CHARACTERISTICS as u64, "total number of range-check-16 lookups in circuit is {} that is larger that field characteristics {}", total_lookups_for_range_checks_16, F::CHARACTERISTICS);

        let mut expect_table_id_for_generic_lookup = false;
        let mut decode_table_columns_mask = Vec::new();

        let (generic_lookup_width, decoder_lookup_pair) = {
            // and then all lookups from circuit + decoder are "generic" ones
            for lookup in lookups.iter() {
                let LookupQuery { row, table } = lookup.clone();
                generic_lookups.push((row.to_vec(), table));
            }

            let mut decoder_lookup_pair = None;
            let mut decoder_table_width;
            // and decoder - we tightly pack it, and will need to do the same in the setup generator
            {
                // pub pc: [F; 2],
                // pub rs1_index: F,
                // pub rs2_index: F,
                // pub rd_index: F,
                // pub imm: [F; REGISTER_SIZE],
                // pub funct3: F,
                // pub circuit_family_extra_mask: F,

                let mut decoder_lookup_trivial_vars = vec![];
                decoder_lookup_trivial_vars.extend(executor_machine_state.cycle_start_state.pc);
                decoder_lookup_trivial_vars.extend([executor_machine_state.decoder_data.rs1_index]);
                decoder_lookup_trivial_vars.extend([executor_machine_state.decoder_data.rs2_index]);
                decoder_lookup_trivial_vars.extend([executor_machine_state.decoder_data.rd_index]);
                decoder_lookup_trivial_vars.extend(executor_machine_state.decoder_data.imm);
                decoder_table_width = 2 + 1 + 1 + 1 + REGISTER_SIZE;
                decode_table_columns_mask.resize(decoder_table_width, true);

                if let Some(funct3) = executor_machine_state.decoder_data.funct3 {
                    decoder_lookup_trivial_vars.extend([funct3]);
                    decoder_table_width += 1;
                    decode_table_columns_mask.push(true);
                } else {
                    decode_table_columns_mask.push(false);
                }

                let mut decoder_lookup: Vec<_> = decoder_lookup_trivial_vars
                    .into_iter()
                    .map(|el| LookupInput::<F>::Variable(el))
                    .collect();
                if circuit_family_bitmask.is_empty() {
                    // we do not need this data
                    decode_table_columns_mask.push(false);
                } else {
                    decoder_table_width += 1;
                    decode_table_columns_mask.push(true);
                    if circuit_family_bitmask.len() == 1 {
                        // just variable itself
                        decoder_lookup.push(LookupInput::<F>::Variable(circuit_family_bitmask[0]));
                    } else {
                        // constraint
                        assert!(circuit_family_bitmask.len() < F::CHAR_BITS);
                        let mut mask_constraint = Constraint::empty();
                        for (i, var) in circuit_family_bitmask.iter().enumerate() {
                            mask_constraint += Term::from((F::from_u32_unchecked(1 << i), *var));
                        }
                        mask_constraint.normalize();
                        let (_, linear_terms, _) = mask_constraint.split_max_quadratic();
                        decoder_lookup.push(LookupInput::Expression {
                            linear_terms,
                            constant_coeff: F::ZERO,
                        });
                    }
                }
                decoder_lookup_pair = Some((executor_machine_state.execute, decoder_lookup));
            }

            assert_eq!(
                decode_table_columns_mask
                    .iter()
                    .filter(|el| **el == true)
                    .count(),
                decoder_table_width
            );

            let total_generic_lookups = (generic_lookups.len() as u64
                + decoder_lookup_pair.is_some() as u64)
                * trace_len as u64;
            assert!(total_generic_lookups < F::CHARACTERISTICS as u64, "total number of generic lookups in circuit is {} that is larger that field characteristics {}", total_generic_lookups, F::CHARACTERISTICS);

            let max_width_without_decoder = generic_lookups
                .iter()
                .map(|el| el.0.len())
                .max()
                .unwrap_or(0);
            let decoder_width = if let Some(decoder_lookup) = decoder_lookup_pair.as_ref() {
                decoder_lookup.1.len()
            } else {
                0
            };

            let generic_lookup_width = if decoder_width > 0 && max_width_without_decoder > 0 {
                // account for table ID
                expect_table_id_for_generic_lookup = true;
                core::cmp::max(decoder_width, max_width_without_decoder) + 1
            } else {
                core::cmp::max(decoder_width, max_width_without_decoder)
            };

            println!(
                "Generic lookup total tables in setup: {}",
                generic_lookup_width
            );

            assert!(generic_lookup_width >= decoder_table_width);

            (generic_lookup_width, decoder_lookup_pair)
        };

        let mut graph = GKRGraph::new(generic_lookup_width);

        let mut all_variables_to_place = BTreeSet::new();
        for variable_idx in 0..num_variables {
            all_variables_to_place.insert(Variable(variable_idx));
        }

        let mut range_check_expressions = range_check_expressions;
        // let (shuffle_ram_inits_and_teardowns, lazy_init_aux_set) =
        //     Self::compile_inits_and_teardowns(
        //         num_inits_and_teardowns,
        //         &mut boolean_vars,
        //         &mut range_check_expressions,
        //         &mut num_variables,
        //         &mut memory_tree_offset,
        //         &mut all_variables_to_place,
        //         &mut layout,
        //     );

        let mut ram_access_sets = vec![];

        assert!(memory_queries.len() < 4);
        assert!(memory_queries
            .is_sorted_by(|a, b| a.local_timestamp_in_cycle() < b.local_timestamp_in_cycle()));
        memory_queries.windows(2).for_each(|el| {
            assert!(el[0].local_timestamp_in_cycle() + 1 == el[1].local_timestamp_in_cycle())
        });

        let mut ram_augmented_sets = vec![];

        for (query_idx, memory_query) in memory_queries.clone().into_iter().enumerate() {
            assert_eq!(memory_query.local_timestamp_in_cycle() as usize, query_idx);
            let [read_timestamp_low, read_timestamp_high] = memory_query.read_timestamp();
            variable_names.insert(
                read_timestamp_low,
                format!("query {}, read_ts[0]", query_idx),
            );
            variable_names.insert(
                read_timestamp_high,
                format!("query {}, read_ts[1]", query_idx),
            );
            let read_timestamp = graph.layout_memory_subtree_multiple_variables(
                [read_timestamp_low, read_timestamp_high],
                &mut all_variables_to_place,
                &layers_mapping,
            );

            let borrow_var = {
                // now that we have declared timestamps, we can produce comparison expressions for range checks
                let borrow_var = add_compiler_defined_base_layer_variable(
                    &mut num_variables,
                    &mut all_variables_to_place,
                    &mut layers_mapping,
                );
                boolean_vars.push(borrow_var);
                variable_names.insert(borrow_var, format!("query {}, interm ts borrow", query_idx));

                borrow_var
            };

            let partial_data = ShuffleRamTimestampComparisonPartialData {
                intermediate_borrow: borrow_var,
                read_timestamp: [read_timestamp_low, read_timestamp_high],
                local_timestamp_in_cycle: memory_query.local_timestamp_in_cycle() as usize,
            };

            ram_augmented_sets.push((memory_query.clone(), partial_data));

            let read_timestamp = read_timestamp.map(|el| {
                let GKRAddress::BaseLayerMemory(el) = el else {
                    unreachable!()
                };

                el
            });

            let read_value = match memory_query.read_value() {
                WordRepresentation::Zero => {
                    unreachable!()
                }
                WordRepresentation::U16Limbs(read_value) => {
                    let read_value = graph.layout_memory_subtree_multiple_variables(
                        read_value,
                        &mut all_variables_to_place,
                        &layers_mapping,
                    );
                    let read_value = read_value.map(|el| {
                        let GKRAddress::BaseLayerMemory(el) = el else {
                            unreachable!()
                        };

                        el
                    });

                    RamWordRepresentation::U16Limbs(read_value)
                }

                WordRepresentation::U8Limbs(read_value) => {
                    let read_value = graph.layout_memory_subtree_multiple_variables(
                        read_value,
                        &mut all_variables_to_place,
                        &layers_mapping,
                    );
                    let read_value = read_value.map(|el| {
                        let GKRAddress::BaseLayerMemory(el) = el else {
                            unreachable!()
                        };

                        el
                    });

                    RamWordRepresentation::U8Limbs(read_value)
                }
            };

            let address = match memory_query.clone() {
                MemoryAccess::RegisterOnly(RegisterAccess { reg_idx, .. }) => {
                    let [register_index] = graph.layout_memory_subtree_multiple_variables(
                        [reg_idx],
                        &mut all_variables_to_place,
                        &layers_mapping,
                    );
                    let GKRAddress::BaseLayerMemory(register_index) = register_index else {
                        unreachable!()
                    };

                    RamAddress::RegisterOnly(RegisterOnlyAccessAddress { register_index })
                }
                MemoryAccess::RegisterOrRam(RegisterOrRamAccess {
                    is_register,
                    address,
                    ..
                }) => {
                    let (Boolean::Is(is_register_var) | Boolean::Not(is_register_var)) =
                        is_register
                    else {
                        todo!()
                    };
                    let [addr_lo_var, addr_hi_var] = address;
                    dbg!();
                    // some optimisations re-use is_register
                    let GKRAddress::BaseLayerMemory(is_register_col) = graph
                        .get_fixed_layout_pos(&is_register_var)
                        .unwrap_or_else(|| {
                            let [gkraddr] = graph.layout_memory_subtree_multiple_variables(
                                [is_register_var],
                                &mut all_variables_to_place,
                                &layers_mapping,
                            );
                            gkraddr
                        })
                    else {
                        unreachable!()
                    };
                    let [GKRAddress::BaseLayerMemory(addr_lo_col), GKRAddress::BaseLayerMemory(addr_hi_col)] =
                        graph.layout_memory_subtree_multiple_variables(
                            [addr_lo_var, addr_hi_var],
                            &mut all_variables_to_place,
                            &layers_mapping,
                        )
                    else {
                        unreachable!()
                    };
                    let is_register = match is_register {
                        Boolean::Is(_) => IsRegisterAddress::Is(is_register_col),
                        Boolean::Not(_) => IsRegisterAddress::Not(is_register_col),
                        Boolean::Constant(_) => todo!(),
                    };
                    RamAddress::RegisterOrRam(RegisterOrRamAccessAddress {
                        is_register,
                        address: [addr_lo_col, addr_hi_col],
                    })
                    // from aleksander:
                    //
                    // let is_register = match is_register {
                    //     Boolean::Is(var) => {
                    //         let [is_register] = graph.layout_memory_subtree_multiple_variables(
                    //             [var],
                    //             &mut all_variables_to_place,
                    //         );
                    //         let GKRAddress::BaseLayerMemory(is_register) = is_register else {
                    //             unreachable!()
                    //         };
                    //         IsRegisterAddress::Is(is_register)
                    //     }
                    //     Boolean::Not(not_var) => {
                    //         let [is_not_register] = graph.layout_memory_subtree_multiple_variables(
                    //             [not_var],
                    //             &mut all_variables_to_place,
                    //         );
                    //         let GKRAddress::BaseLayerMemory(is_not_register) = is_not_register
                    //         else {
                    //             unreachable!()
                    //         };
                    //         IsRegisterAddress::Not(is_not_register)
                    //     }
                    //     Boolean::Constant(..) => {
                    //         unreachable!()
                    //     }
                    // };
                    // let address = graph.layout_memory_subtree_multiple_variables(
                    //     address,
                    //     &mut all_variables_to_place,
                    // );
                    // let address = address.map(|el| {
                    //     let GKRAddress::BaseLayerMemory(el) = el else {
                    //         unreachable!()
                    //     };

                    //     el
                    // });

                    // RamAddress::RegisterOrRam(RegisterOrRamAccessAddress {
                    //     is_register,
                    //     address,
                    // })
                }
                _ => {
                    unreachable!()
                }
            };

            let query_columns = if memory_query.is_readonly() {
                assert_eq!(memory_query.read_value(), memory_query.write_value());

                let query_columns = RamReadQuery {
                    in_cycle_write_index: memory_query.local_timestamp_in_cycle(),
                    address,
                    read_timestamp,
                    read_value,
                };

                RamQuery::Readonly(query_columns)
            } else {
                let write_value = match memory_query.write_value() {
                    WordRepresentation::Zero => {
                        unreachable!()
                    }
                    WordRepresentation::U16Limbs(write_value) => {
                        let write_value = graph.layout_memory_subtree_multiple_variables(
                            write_value,
                            &mut all_variables_to_place,
                            &layers_mapping,
                        );
                        let write_value = write_value.map(|el| {
                            let GKRAddress::BaseLayerMemory(el) = el else {
                                unreachable!()
                            };

                            el
                        });

                        RamWordRepresentation::U16Limbs(write_value)
                    }

                    WordRepresentation::U8Limbs(write_value) => {
                        unreachable!();
                        let write_value = graph.layout_memory_subtree_multiple_variables(
                            write_value,
                            &mut all_variables_to_place,
                            &layers_mapping,
                        );
                        let write_value = write_value.map(|el| {
                            let GKRAddress::BaseLayerMemory(el) = el else {
                                unreachable!()
                            };

                            el
                        });

                        RamWordRepresentation::U8Limbs(write_value)
                    }
                };
                let query_columns = RamWriteQuery {
                    in_cycle_write_index: memory_query.local_timestamp_in_cycle(),
                    address,
                    read_timestamp,
                    read_value,
                    write_value,
                };

                RamQuery::Write(query_columns)
            };

            ram_access_sets.push(query_columns);
        }

        // we can add explicit nodes for memory access accumulation, and we also explicitly check write timestamps to be in range
        let mut timestamp_range_check_expressions_to_compile = vec![];
        {
            // As all timestamps make a permutation, we only constraint write set
            timestamp_range_check_expressions_to_compile.push(LookupInput::<F>::Variable(
                executor_machine_state.cycle_end_state.timestamp[0],
            ));
            timestamp_range_check_expressions_to_compile.push(LookupInput::<F>::Variable(
                executor_machine_state.cycle_end_state.timestamp[1],
            ));

            // As initial and final timestamps are material and there are range checks on them (output var),
            // we can just do constraints here, as this carry is purely ephemeral

            // We add a constraint (normal one), to perform timestamp += 4 constraint, without
            // carry over top limb, as we want to have upper bound anyway

            // we need to ensure that constraint the describes a carry is boolean
            let mut t = Constraint::from(executor_machine_state.cycle_start_state.timestamp[0])
                + Term::from(TIMESTAMP_STEP as u32)
                - Term::from(executor_machine_state.cycle_end_state.timestamp[0]);
            t.scale(
                F::from_u64_with_reduction(1 << TIMESTAMP_COLUMNS_NUM_BITS)
                    .inverse()
                    .unwrap(),
            );

            // low
            let constraint = t.clone() * t.clone() - t.clone();
            constraints.push((constraint, true));

            // high - carryless
            constraints.push((
                Constraint::from(executor_machine_state.cycle_end_state.timestamp[1])
                    - Term::from(executor_machine_state.cycle_start_state.timestamp[1])
                    - t,
                true,
            ));
        };

        let machine_state = layout_machine_state_for_preprocessed_bytecode(
            &mut graph,
            &mut all_variables_to_place,
            &executor_machine_state,
            circuit_family_bitmask.clone(),
            &layers_mapping,
        );

        use crate::gkr_compiler::memory_like_grand_product::layout_initial_grand_product_accumulation;

        let (
            (grand_product_read_accumulation_nodes, grand_product_write_accumulation_nodes),
            copied_predicate_for_grand_product_masking,
        ) = layout_initial_grand_product_accumulation(
            &mut graph,
            executor_machine_state.execute,
            &ram_augmented_sets,
            Some((
                (
                    executor_machine_state.cycle_start_state.pc,
                    executor_machine_state.cycle_start_state.timestamp,
                ),
                (
                    executor_machine_state.cycle_end_state.pc,
                    executor_machine_state.cycle_end_state.timestamp,
                ),
            )),
            None,
            executor_machine_state.cycle_start_state.timestamp,
        );

        // now we can follow up with lookup subarguments. We separate "hot" range check 16 and 19 bit
        // ones, and "generic" ones (that includes decoder)

        // Timestamps are the easiest - we collect them, and will transform into GKR layers very separately
        super::range_check_exprs::compile_timestamp_comparison_range_checks(
            &mut timestamp_range_check_expressions_to_compile,
            &ram_augmented_sets,
            executor_machine_state.cycle_start_state.timestamp,
        );

        let total_timestamp_range_check_lookups =
            timestamp_range_check_expressions_to_compile.len() as u64 * trace_len as u64;
        assert!(total_timestamp_range_check_lookups < F::CHARACTERISTICS as u64, "total number of timestamp range check lookups in circuit is {} that is larger that field characteristics {}", total_timestamp_range_check_lookups, F::CHARACTERISTICS);

        // for all boolean vars we add booleanity constraint here

        for boolean in boolean_vars.iter() {
            let t = Term::<F>::from(*boolean);
            let c = t.clone() * t.clone() - t;
            constraints.push((c, false));
        }

        // // now we can optimize the constraints and all remaining variables
        // for c in constraints.iter_mut() {
        //     c.0.normalize();
        // }

        // let (optimized_out_variables, mut constraints) = optimize_out_linear_constraints(
        //     &[],
        //     &[],
        //     &substitutions,
        //     constraints,
        //     &mut all_variables_to_place,
        // );

        // println!(
        //     "{} variables were optimized out",
        //     optimized_out_variables.len()
        // );
        // let scratch_space_size = optimized_out_variables.len();

        // for var in optimized_out_variables.iter() {
        //     if let Some(c) = variables_from_constraints.remove(var) {
        //         assert!(c.degree() < 2);
        //     }
        // }

        // normalize constraint for next steps
        for c in constraints.iter_mut() {
            c.0.normalize();
        }

        // and now we can finally layout all the variables. We do want to push all of them into intermediate layers

        // at the end of the day we are only left with:
        // - grand product accumulations
        // - lookup accumulations
        // - constraints

        // And we can transform them into (potentially intersecting) sub-GKRs

        // filter constraints that define variables
        let len_before = constraints.len();
        for (_, c) in variables_from_constraints.iter_mut() {
            c.normalize();
            let mut to_remove = None;
            for (idx, (cc, _)) in constraints.iter().enumerate() {
                if cc == &*c {
                    assert!(to_remove.is_none());
                    to_remove = Some(idx);
                }
            }
            if let Some(to_remove) = to_remove {
                constraints.remove(to_remove);
            }
        }
        let len_after = constraints.len();
        println!(
            "{} constraints removed as they define variables, will be used separately",
            len_before - len_after
        );

        // Above we only placed in the graph variables that have strict constraint on being at the base (input) layer of the proof.
        // Now we should try to move from the base layer and place the rest.
        // As we explicitly track variables that can be made "virtual" (by pushing them into intermediate GKR layers),
        // it should be relatively easy task.

        println!(
            "In total of {} variables are defined via constraints",
            variables_from_constraints.len()
        );
        for (var, _c) in variables_from_constraints.iter() {
            if let Some(name) = variable_names.get(var) {
                println!("Variable {:?}: `{}` is defined via constraint", var, name);
            }
        }

        // first define if any of the constraints depends on the variables defined via other constraints
        let mut variables_via_constraints_are_disjoint = true;
        let mut all_variables_in_constraints = HashSet::new();
        for (c, _) in constraints.iter() {
            for (var, _) in variables_from_constraints.iter() {
                if c.contains_var(var) {
                    variables_via_constraints_are_disjoint = false;
                }
            }
            c.dump_variables(&mut all_variables_in_constraints);
        }

        println!(
            "Variables defined via constraints are disjoint = {}",
            variables_via_constraints_are_disjoint
        );

        if variables_from_constraints.len() > 0 {
            assert!(all_variables_to_place.len() > 0);

            // put all variables into base layer that are not defined via constraints
            for var in all_variables_to_place.clone().iter() {
                if variables_from_constraints.contains_key(var) {
                    continue;
                }
                let _ = graph.layout_witness_subtree_multiple_variables(
                    [*var],
                    &mut all_variables_to_place,
                    &layers_mapping,
                );
            }
            assert_eq!(
                all_variables_to_place.len(),
                variables_from_constraints.len()
            );

            // now we should walk over constraints that define variables
            let mut intermediate_layer = 1;
            loop {
                let initial_len = variables_from_constraints.len();
                for (var, constraint) in variables_from_constraints.clone().into_iter() {
                    let all_vars = constraint.stable_variable_set();
                    let expected_layer = *layers_mapping.get(&var).expect("must be known");
                    let inputs_layer = get_input_layer_ensure_same(&all_vars, &layers_mapping);
                    assert_eq!(expected_layer, inputs_layer + 1);
                    if intermediate_layer != inputs_layer + 1 {
                        continue;
                    }
                    let _ = graph.place_intermediate_variable_from_constraint_at_layer(
                        intermediate_layer,
                        var,
                        &mut all_variables_to_place,
                        &layers_mapping,
                        constraint,
                    );
                    variables_from_constraints.remove(&var);
                }

                assert_ne!(
                    initial_len,
                    variables_from_constraints.len(),
                    "intermediate layers places is stuck"
                );
                intermediate_layer += 1;

                if variables_from_constraints.is_empty() {
                    break;
                }
            }

            assert!(all_variables_to_place.is_empty());
        } else {
            // put all variables into base layer
            for var in all_variables_to_place.clone().iter() {
                let _ = graph.layout_witness_subtree_multiple_variables(
                    [*var],
                    &mut all_variables_to_place,
                    &layers_mapping,
                );
            }
            assert!(all_variables_to_place.is_empty());
        }

        // Accumulate grand product - pairwise as much as we can
        use crate::gkr_compiler::memory_like_grand_product::accumulate_memory_like_grand_product;

        let (final_read_node, final_write_node) = accumulate_memory_like_grand_product(
            &mut graph,
            copied_predicate_for_grand_product_masking,
            grand_product_read_accumulation_nodes,
            grand_product_write_accumulation_nodes,
        );

        let mut lookup_outputs = BTreeMap::new();

        let mut range_check_16_multiplicity = None;
        let mut timestamp_multiplicity = None;
        let mut generic_lookup_multiplicity = None;
        let mut num_generic_lookups = 0;

        let mut generic_lookups_compiled = vec![];
        let mut range_check_16_lookups_compiled = vec![];
        let mut timestamp_range_check_lookups_compiled = vec![];

        // placing lookup is move involved
        {
            if range_check_16_expressions.len() > 0 {
                let (multiplicity, final_pair, final_rel, rels_for_witness_eval) =
                    layout_width_1_lookup_expressions(
                        &mut graph,
                        range_check_16_expressions,
                        &mut num_variables,
                        &mut all_variables_to_place,
                        &mut variable_names,
                        &mut layers_mapping,
                        "range check 16",
                        LookupType::RangeCheck16,
                    );
                range_check_16_multiplicity = Some(multiplicity);
                range_check_16_lookups_compiled = rels_for_witness_eval;
                lookup_outputs.insert(LookupType::RangeCheck16, (final_pair, final_rel));
            }

            if timestamp_range_check_expressions_to_compile.len() > 0 {
                let (multiplicity, final_pair, final_rel, rels_for_witness_eval) =
                    layout_width_1_lookup_expressions(
                        &mut graph,
                        timestamp_range_check_expressions_to_compile,
                        &mut num_variables,
                        &mut all_variables_to_place,
                        &mut variable_names,
                        &mut layers_mapping,
                        "timestamp range check",
                        LookupType::TimestampRangeCheck,
                    );
                timestamp_multiplicity = Some(multiplicity);
                timestamp_range_check_lookups_compiled = rels_for_witness_eval;
                lookup_outputs.insert(LookupType::TimestampRangeCheck, (final_pair, final_rel));
            }

            if generic_lookups.len() > 0 || decoder_lookup_pair.is_some() {
                let decoder_lookup_is_present = decoder_lookup_pair.is_some();
                num_generic_lookups += decoder_lookup_is_present as usize;
                num_generic_lookups += generic_lookups.len();
                let (multiplicity, final_pair, final_rel, rels_for_witness_eval) =
                    layout_lookup_expressions::<F, false>(
                        &mut graph,
                        generic_lookups,
                        &mut num_variables,
                        &mut all_variables_to_place,
                        &mut variable_names,
                        &mut layers_mapping,
                        "generic lookup",
                        decoder_lookup_pair,
                        LookupType::Generic,
                        generic_lookup_width,
                        expect_table_id_for_generic_lookup,
                    );
                generic_lookup_multiplicity = Some(multiplicity);
                generic_lookups_compiled = rels_for_witness_eval;
                assert_eq!(
                    generic_lookups_compiled.len() + (decoder_lookup_is_present as usize),
                    num_generic_lookups
                );
                lookup_outputs.insert(LookupType::Generic, (final_pair, final_rel));
            }
        }

        // Place a gate for constraints batch eval
        let (degree_2_constraints, degree_1_constraints) =
            layout_constraints_at_layers(&mut graph, constraints, &layers_mapping);

        // work out the outputs
        let lookup_outputs = BTreeMap::from_iter(
            lookup_outputs
                .into_iter()
                .map(|(k, v)| (k, (v.0, LookupOutput::Direct(v.1)))),
        );

        let (layers, global_output_map) =
            graph.layout_layers([final_read_node, final_write_node], lookup_outputs);

        let table_offsets = table_driver
            .table_starts_offsets()
            .map(|el| el as u32)
            .to_vec();

        // make separation for memory layout
        let initial_pc = executor_machine_state.cycle_start_state.pc.map(|el| {
            let GKRAddress::BaseLayerMemory(offset) = graph.get_address_for_variable(el) else {
                unreachable!()
            };
            offset
        });
        let initial_ts = executor_machine_state
            .cycle_start_state
            .timestamp
            .map(|el| {
                let GKRAddress::BaseLayerMemory(offset) = graph.get_address_for_variable(el) else {
                    unreachable!()
                };
                offset
            });

        let final_pc = executor_machine_state.cycle_end_state.pc.map(|el| {
            let GKRAddress::BaseLayerMemory(offset) = graph.get_address_for_variable(el) else {
                unreachable!()
            };
            offset
        });
        let final_ts = executor_machine_state.cycle_end_state.timestamp.map(|el| {
            let GKRAddress::BaseLayerMemory(offset) = graph.get_address_for_variable(el) else {
                unreachable!()
            };
            offset
        });

        let machine_initial_state = GKRMachineState {
            pc: initial_pc,
            timestamp: initial_ts,
        };

        let machine_final_state = GKRMachineState {
            pc: final_pc,
            timestamp: final_ts,
        };

        let GKRAddress::BaseLayerMemory(execute) =
            graph.get_address_for_variable(executor_machine_state.execute)
        else {
            unreachable!()
        };
        let machine_state = MachineStatePermutationDescription {
            execute,
            initial_state: machine_initial_state,
            final_state: machine_final_state,
        };

        let decoder_input = {
            let GKRAddress::BaseLayerMemory(rs1_index) =
                graph.get_address_for_variable(executor_machine_state.decoder_data.rs1_index)
            else {
                unreachable!()
            };

            let rs2_index =
                graph.get_address_for_variable(executor_machine_state.decoder_data.rs2_index);
            let rd_index =
                graph.get_address_for_variable(executor_machine_state.decoder_data.rd_index);

            let [imm_low, imm_high] = executor_machine_state
                .decoder_data
                .imm
                .map(|el| graph.get_address_for_variable(el));
            let funct3 = if let Some(funct3) = executor_machine_state.decoder_data.funct3 {
                Some(graph.get_address_for_variable(funct3))
            } else {
                None
            };
            let mut circuit_family_mask_bits = vec![];
            for el in circuit_family_bitmask.iter() {
                let pos = graph.get_address_for_variable(*el);
                circuit_family_mask_bits.push(pos);
            }

            let (decoder_witness_is_in_memory, (imm_low, imm_high, funct3)) =
                match (imm_low, imm_high, funct3) {
                    (
                        GKRAddress::BaseLayerMemory(imm_low),
                        GKRAddress::BaseLayerMemory(imm_high),
                        Some(GKRAddress::BaseLayerMemory(funct3)),
                    ) => (true, (imm_low, imm_high, Some(funct3))),
                    (
                        GKRAddress::BaseLayerMemory(imm_low),
                        GKRAddress::BaseLayerMemory(imm_high),
                        None,
                    ) => (true, (imm_low, imm_high, None)),
                    (
                        GKRAddress::BaseLayerWitness(imm_low),
                        GKRAddress::BaseLayerWitness(imm_high),
                        Some(GKRAddress::BaseLayerWitness(funct3)),
                    ) => (false, (imm_low, imm_high, Some(funct3))),
                    (
                        GKRAddress::BaseLayerWitness(imm_low),
                        GKRAddress::BaseLayerWitness(imm_high),
                        None,
                    ) => (false, (imm_low, imm_high, None)),
                    _ => {
                        unreachable!()
                    }
                };

            DecoderPlacementDescription {
                rs1_index,
                rs2_index,
                rd_index,
                circuit_family_mask_bits: circuit_family_mask_bits.into_boxed_slice(),
                decoder_witness_is_in_memory,
                imm: [imm_low, imm_high],
                funct3,
            }
        };

        let memory_layout = GKRMemoryLayout {
            ram_access_sets,
            machine_state: Some(machine_state),
            delegation_state: None,
            indirect_access_variable_offsets: vec![],
            total_width: graph.base_layer_memory.len(),
            decoder_input: Some(decoder_input),
        };

        let multiplicities_columns_for_range_check_16 =
            if let Some(range_check_16_multiplicity) = range_check_16_multiplicity {
                let GKRAddress::BaseLayerWitness(multiplicities_columns_for_range_check_16) =
                    graph.get_address_for_variable(range_check_16_multiplicity)
                else {
                    unreachable!()
                };
                multiplicities_columns_for_range_check_16
                    ..(multiplicities_columns_for_range_check_16 + 1)
            } else {
                0..0
            };
        let GKRAddress::BaseLayerWitness(multiplicities_columns_for_timestamp_range_check) =
            graph.get_address_for_variable(timestamp_multiplicity.expect("is some"))
        else {
            unreachable!()
        };
        let GKRAddress::BaseLayerWitness(multiplicities_columns_for_generic_lookup) =
            graph.get_address_for_variable(generic_lookup_multiplicity.expect("is some"))
        else {
            unreachable!()
        };

        let mut placement_data = BTreeMap::new();
        placement_data.extend(graph.base_layer_memory.iter().map(|(k, v)| (*k, *v)));
        placement_data.extend(graph.base_layer_witness.iter().map(|(k, v)| (*k, *v)));
        placement_data.extend(graph.intermediate_layers.iter().map(|(k, v)| (*k, *v)));

        let witness_layout = GKRWitnessLayout {
            multiplicities_columns_for_range_check_16,
            multiplicities_columns_for_timestamp_range_check,
            multiplicities_columns_for_generic_lookup: multiplicities_columns_for_generic_lookup
                ..multiplicities_columns_for_generic_lookup + 1,
            total_width: graph.base_layer_witness.len(),
        };

        let aux_layout_data = {
            let shuffle_ram_timestamp_comparison_aux_vars = ram_augmented_sets
                .iter()
                .map(|(_, el)| RamAuxComparisonSet {
                    intermediate_borrow: graph.get_address_for_variable(el.intermediate_borrow),
                })
                .collect();

            GKRAuxLayoutData {
                shuffle_ram_timestamp_comparison_aux_vars,
            }
        };

        let mut scratch_space_mapping = BTreeMap::new();
        let mut scratch_space_mapping_rev = BTreeMap::new();
        let mut scratch_space_counter = 0usize;
        for (_var, pos) in placement_data.iter() {
            match pos {
                GKRAddress::InnerLayer { .. } => {
                    scratch_space_mapping.insert(*pos, scratch_space_counter);
                    scratch_space_mapping_rev.insert(scratch_space_counter, *pos);
                    scratch_space_counter += 1;
                }
                _ => {}
            }
        }

        // We should remap lookups to reuse scratch space instead of layer/offset information
        // for simplicity if witness evaluator

        for rel in range_check_16_lookups_compiled
            .iter_mut()
            .map(|el: &mut NoFieldSingleColumnLookupRelation| &mut el.input)
            .chain(
                timestamp_range_check_lookups_compiled
                    .iter_mut()
                    .map(|el: &mut NoFieldSingleColumnLookupRelation| &mut el.input),
            )
            .chain(
                generic_lookups_compiled
                    .iter_mut()
                    .map(|el: &mut NoFieldVectorLookupRelation| el.columns.iter_mut())
                    .flatten(),
            )
        {
            for (_, addr) in rel.linear_terms.iter_mut() {
                let addr_copy = *addr;
                if let GKRAddress::InnerLayer { .. } = addr_copy {
                    let scratch_offset = *scratch_space_mapping
                        .get(&addr_copy)
                        .expect("must know scratch space index");
                    *addr = GKRAddress::ScratchSpace(scratch_offset);
                }
            }
        }

        GKRCircuitArtifact {
            trace_len,
            table_offsets,
            total_tables_size,
            offset_for_decoder_table,
            layers,
            global_output_map,
            memory_layout,
            witness_layout,
            scratch_space_size: scratch_space_counter,
            num_generic_lookups,
            placement_data,
            generic_lookup_tables_width: generic_lookup_width,
            tables_ids_in_generic_lookups: expect_table_id_for_generic_lookup,
            decode_table_columns_mask,
            has_decoder_lookup: true,

            degree_2_constraints,
            degree_1_constraints,

            generic_lookups: generic_lookups_compiled,
            range_check_16_lookup_expressions: range_check_16_lookups_compiled,
            timestamp_range_check_lookup_expressions: timestamp_range_check_lookups_compiled,

            variable_names: BTreeMap::from_iter(variable_names.into_iter()),
            scratch_space_mapping,
            scratch_space_mapping_rev,

            aux_layout_data,

            _marker: std::marker::PhantomData,
        }
    }
}
