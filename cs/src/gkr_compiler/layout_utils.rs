use super::*;
use crate::constraint::*;
use crate::definitions::*;
use crate::oracle::Placeholder;
use field::PrimeField;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;

// pub(crate) fn compile_timestamp_range_check_expressions<
//     F: PrimeField,
//     const USE_CIRCUIT_SEQ: bool,
// >(
//     trace_len: usize,
//     timestamp_range_check_expressions_to_compile: Vec<LookupInput<F>>,
//     shuffle_ram_timestamp_range_check_partial_sets: Vec<ShuffleRamTimestampComparisonPartialData>,
//     layout: &BTreeMap<Variable, ColumnAddress>,
//     setup_layout: &SetupLayout,
//     cycle_timestamp: Option<ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>>,
// ) -> (usize, std::vec::Vec<LookupExpression<F>>) {
//     let mut compiled_timestamp_comparison_expressions = vec![];

//     // we already have enough information to compile range check expressions that are left from memory accesses layout
//     for input in timestamp_range_check_expressions_to_compile.into_iter() {
//         let (linear_terms, constant_coeff) = match input {
//             LookupInput::Expression {
//                 linear_terms,
//                 constant_coeff,
//             } => (linear_terms, constant_coeff),
//             LookupInput::Variable(var) => (vec![(F::ONE, var)], F::ZERO),
//         };
//         // place all of them
//         let mut compiled_linear_terms = vec![];
//         for (coeff, var) in linear_terms.iter() {
//             let place = layout
//                 .get(var)
//                 .copied()
//                 .expect("all variables must be already placed");
//             compiled_linear_terms.push((*coeff, place));
//         }
//         let compiled_constraint = CompiledDegree1Constraint {
//             linear_terms: compiled_linear_terms.into_boxed_slice(),
//             constant_term: constant_coeff,
//         };
//         let lookup_expr = LookupExpression::Expression(compiled_constraint);
//         compiled_timestamp_comparison_expressions.push(lookup_expr);
//     }

//     // timestamps deserve separate range checks for shuffle RAM in the main circuit,
//     // as those also take contribution from circuit index in the sequence

//     // NOTE: these expressions are separate, as we will have to add to them a circuit sequence constant
//     // that comes during the proving only

//     let offset_for_special_shuffle_ram_timestamps_range_check_expressions =
//         compiled_timestamp_comparison_expressions.len();

//     for data in shuffle_ram_timestamp_range_check_partial_sets.into_iter() {
//         let ShuffleRamTimestampComparisonPartialData {
//             intermediate_borrow,
//             read_timestamp,
//             local_timestamp_in_cycle,
//         } = data;
//         let [read_low, read_high] = read_timestamp;
//         // we know all the places, but will have to manually compile it into degree-1 constraint

//         // low part
//         {
//             let mut compiled_linear_terms = vec![];
//             let borrow_place = *layout.get(&intermediate_borrow).unwrap();
//             compiled_linear_terms.push((
//                 F::from_u32_unchecked(1 << TIMESTAMP_COLUMNS_NUM_BITS),
//                 borrow_place,
//             ));
//             let read_low_place = *layout.get(&read_low).unwrap();
//             compiled_linear_terms.push((F::ONE, read_low_place));

//             // have to manually create write low place
//             let write_low_place = if let Some(cycle_timestamp) = cycle_timestamp {
//                 assert!(USE_CIRCUIT_SEQ == false);
//                 ColumnAddress::MemorySubtree(cycle_timestamp.start())
//             } else {
//                 assert!(USE_CIRCUIT_SEQ);
//                 ColumnAddress::SetupSubtree(setup_layout.timestamp_setup_columns.start())
//             };
//             compiled_linear_terms.push((F::MINUS_ONE, write_low_place));

//             // and we also have a constant of `- in cycle local write`
//             let mut constant_coeff = F::from_u32_unchecked(local_timestamp_in_cycle as u32);
//             constant_coeff.negate();

//             let compiled_constraint = CompiledDegree1Constraint {
//                 linear_terms: compiled_linear_terms.into_boxed_slice(),
//                 constant_term: constant_coeff,
//             };
//             let lookup_expr = LookupExpression::Expression(compiled_constraint);
//             compiled_timestamp_comparison_expressions.push(lookup_expr);
//         }
//         // and almost the same for high part
//         {
//             let mut compiled_linear_terms = vec![];
//             let read_high_place = *layout.get(&read_high).unwrap();
//             compiled_linear_terms.push((F::ONE, read_high_place));

//             let write_high_place = if let Some(cycle_timestamp) = cycle_timestamp {
//                 assert!(USE_CIRCUIT_SEQ == false);
//                 ColumnAddress::MemorySubtree(cycle_timestamp.start() + 1)
//             } else {
//                 assert!(USE_CIRCUIT_SEQ);
//                 ColumnAddress::SetupSubtree(setup_layout.timestamp_setup_columns.start() + 1)
//             };
//             compiled_linear_terms.push((F::MINUS_ONE, write_high_place));

//             // subtract borrow
//             let borrow_place = *layout.get(&intermediate_borrow).unwrap();
//             compiled_linear_terms.push((F::MINUS_ONE, borrow_place));

//             let constant_coeff = F::from_u32_unchecked(1 << TIMESTAMP_COLUMNS_NUM_BITS);
//             let compiled_constraint = CompiledDegree1Constraint {
//                 linear_terms: compiled_linear_terms.into_boxed_slice(),
//                 constant_term: constant_coeff,
//             };
//             let lookup_expr = LookupExpression::Expression(compiled_constraint);
//             compiled_timestamp_comparison_expressions.push(lookup_expr);
//         }
//     }

//     let offset_for_special_shuffle_ram_timestamps_range_check_expressions = if USE_CIRCUIT_SEQ {
//         offset_for_special_shuffle_ram_timestamps_range_check_expressions
//     } else {
//         compiled_timestamp_comparison_expressions.len()
//     };

//     let total_timestamp_range_check_lookups =
//         compiled_timestamp_comparison_expressions.len() as u64 * trace_len as u64;
//     assert!(
//         total_timestamp_range_check_lookups < u64::from(F::CHARACTERISTICS),
//         "total number of timestamp range check lookups in circuit is {} that is larger that field characteristics {}",
//         total_timestamp_range_check_lookups,
//         F::CHARACTERISTICS
//     );

//     (
//         offset_for_special_shuffle_ram_timestamps_range_check_expressions,
//         compiled_timestamp_comparison_expressions,
//     )
// }

pub(crate) fn optimize_out_linear_constraints<F: PrimeField>(
    state_input: &[Variable],
    state_output: &[Variable],
    substitutions: &HashMap<(Placeholder, usize), Variable>,
    mut constraints: Vec<(Constraint<F>, bool)>,
    all_variables_to_place: &mut BTreeSet<Variable>,
) -> (Vec<Variable>, Vec<(Constraint<F>, bool)>) {
    let initial_len = all_variables_to_place.len();
    let mut optimized_out_variables = vec![];
    let mut tried_variables = BTreeSet::new();
    'outer: loop {
        // we will try to remove every variable in there
        let mut to_remove: Option<(Variable, Vec<usize>, Vec<usize>)> = None;
        'inner: for variable in all_variables_to_place.iter() {
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
                    continue 'inner;
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
                    if constraint.contains_var(variable) && constraint.degree_for_var(variable) < 2
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

        if to_remove.is_none() {
            break 'outer;
        }

        let Some((variable_to_optimize_out, defining_constraints, occurrences)) = to_remove else {
            panic!();
        };

        let mut optimized_out_params = None;

        for defining_constraint_idx in defining_constraints.into_iter() {
            // for now there is no heuristics to prefer one defining constraint over another,
            // but let's try all

            let defining_constraint = constraints[defining_constraint_idx].0.clone();
            // now we should rewrite it to factor out linear term
            let mut expression = defining_constraint.express_variable(variable_to_optimize_out);
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
                    replacement_constraints.push((occurrence_constraint_idx, rewritten_constraint));
                }
            }

            #[cfg(feature = "debug_logs")]
            {
                println!("-----------------------------------------------");
            }
            if can_be_optimized_out {
                // we do not check whether one potential substitution or another will be the best,
                // so we will just use the latest one that will work
                optimized_out_params = Some((defining_constraint_idx, replacement_constraints));
            } else {
                tried_variables.insert(variable_to_optimize_out);
            }
        }

        if let Some((defining_constraint_idx, replacement_constraints)) = optimized_out_params {
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
        println!(
            "{} variables were optimized out via linear constraint substitution",
            optimized_out_variables.len()
        );
    }

    assert_eq!(
        initial_len,
        optimized_out_variables.len() + all_variables_to_place.len()
    );

    (optimized_out_variables, constraints)
}
