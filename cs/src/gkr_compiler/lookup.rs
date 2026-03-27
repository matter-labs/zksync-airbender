use super::*;
use crate::cs::circuit::LookupQueryTableType;
use crate::definitions::gkr::DECODER_LOOKUP_FORMAL_SET_INDEX;
use crate::definitions::LookupInput;
use crate::definitions::{Degree1Constraint, GKRAddress, Variable};
use crate::gkr_compiler::graph::{GKRGraph, GraphHolder};
use crate::gkr_compiler::lookup_nodes::{LookupDenominator, LookupInputRelation, LookupNumerator};
use crate::tables::TableType;

pub(crate) fn layout_width_1_lookup_expressions<F: PrimeField>(
    graph: &mut GKRGraph,
    expressions: Vec<LookupInput<F>>,
    num_variables: &mut u64,
    all_variables_to_place: &mut BTreeSet<Variable>,
    variable_names: &mut HashMap<Variable, String>,
    layers_mapping: &mut HashMap<Variable, usize>,
    lookup_type: &str,
    lookup: LookupType,
) -> (
    Variable,                               // multiplicity var
    [GKRAddress; 2],                        // final num/den pair
    NoFieldGKRRelation,                     // relation that gives rise to final pair
    Vec<NoFieldSingleColumnLookupRelation>, // all lookup relations for witness evaluation and multiplicity counting
) {
    let (a, b, c, rels) = layout_lookup_expressions::<F, true>(
        graph,
        expressions
            .into_iter()
            .map(|el| {
                (
                    vec![el],
                    LookupQueryTableType::Constant(TableType::DynamicPlaceholder),
                )
            })
            .collect(),
        num_variables,
        all_variables_to_place,
        variable_names,
        layers_mapping,
        lookup_type,
        None,
        lookup,
        1,
        false,
    );

    let rels = rels
        .into_iter()
        .map(|el| {
            assert_eq!(el.columns.len(), 1);

            NoFieldSingleColumnLookupRelation {
                input: el.columns[0].clone(),
                lookup_set_index: el.lookup_set_index,
            }
        })
        .collect();

    (a, b, c, rels)
}

fn input_layer_for_lookup_expression<F: PrimeField, const SINGLE_COLUMN: bool>(
    expr: &(Vec<LookupInput<F>>, LookupQueryTableType<F>),
    expect_table_id: bool,
    layers_mapping: &HashMap<Variable, usize>,
) -> usize {
    let (expr, table_type) = expr;
    if SINGLE_COLUMN {
        assert_eq!(expr.len(), 1);
        assert_eq!(
            *table_type,
            LookupQueryTableType::Constant(TableType::DynamicPlaceholder)
        );
    }

    let mut layer = None;
    for el in expr.iter() {
        match el {
            LookupInput::Variable(var) => {
                let input_layer = *layers_mapping.get(var).expect("must be known");
                if let Some(layer) = layer {
                    assert_eq!(input_layer, layer)
                } else {
                    layer = Some(input_layer);
                }
            }
            LookupInput::Expression { linear_terms, .. } => {
                for (_, var) in linear_terms.iter() {
                    let input_layer = *layers_mapping.get(var).expect("must be known");
                    if let Some(layer) = layer {
                        assert_eq!(input_layer, layer)
                    } else {
                        layer = Some(input_layer);
                    }
                }
            }
        }
    }

    if SINGLE_COLUMN == false && expect_table_id {
        assert_ne!(
            *table_type,
            LookupQueryTableType::Constant(TableType::DynamicPlaceholder)
        );
        match table_type {
            LookupQueryTableType::Constant(..) => {
                // nothing
            }
            LookupQueryTableType::Variable(var) => {
                let input_layer = *layers_mapping.get(var).expect("must be known");
                if let Some(layer) = layer {
                    assert_eq!(input_layer, layer)
                } else {
                    layer = Some(input_layer);
                }
            }
            LookupQueryTableType::Expression(expr) => match expr {
                LookupInput::Variable(var) => {
                    let input_layer = *layers_mapping.get(var).expect("must be known");
                    if let Some(layer) = layer {
                        assert_eq!(input_layer, layer)
                    } else {
                        layer = Some(input_layer);
                    }
                }
                LookupInput::Expression { linear_terms, .. } => {
                    for (_, var) in linear_terms.iter() {
                        let input_layer = *layers_mapping.get(var).expect("must be known");
                        if let Some(layer) = layer {
                            assert_eq!(input_layer, layer)
                        } else {
                            layer = Some(input_layer);
                        }
                    }
                }
            },
        }
    }

    layer.expect("input layer computed")
}

fn lookup_input_node_from_expr<F: PrimeField, const SINGLE_COLUMN: bool>(
    expr: &(Vec<LookupInput<F>>, LookupQueryTableType<F>),
    total_width: usize,
    expect_table_id: bool,
) -> LookupInputRelation<F> {
    let (expr, table_type) = expr;
    if SINGLE_COLUMN {
        assert!(expect_table_id == false);
        assert_eq!(total_width, 1);
        assert_eq!(expr.len(), 1);
        assert_eq!(
            *table_type,
            LookupQueryTableType::Constant(TableType::DynamicPlaceholder)
        );
    } else {
        assert!(expr.len() <= total_width)
    }

    let mut inputs = Vec::new();

    for el in expr.iter() {
        match el {
            LookupInput::Variable(var) => {
                inputs.push(Degree1Constraint {
                    linear_terms: vec![(F::ONE, *var)].into_boxed_slice(),
                    constant_term: F::ZERO,
                });
            }
            LookupInput::Expression {
                linear_terms,
                constant_coeff,
            } => {
                inputs.push(Degree1Constraint {
                    linear_terms: linear_terms.clone().into_boxed_slice(),
                    constant_term: *constant_coeff,
                });
            }
        }
    }
    let mut table_id = None;
    if SINGLE_COLUMN == false && expect_table_id {
        assert_ne!(
            *table_type,
            LookupQueryTableType::Constant(TableType::DynamicPlaceholder)
        );
        let table_id_constraint = match table_type {
            LookupQueryTableType::Constant(constant) => Degree1Constraint {
                linear_terms: vec![].into_boxed_slice(),
                constant_term: F::from_u32_unchecked(constant.to_table_id() as u32),
            },
            LookupQueryTableType::Variable(var) => Degree1Constraint {
                linear_terms: vec![(F::ONE, *var)].into_boxed_slice(),
                constant_term: F::ZERO,
            },
            LookupQueryTableType::Expression(expr) => match expr {
                LookupInput::Variable(var) => Degree1Constraint {
                    linear_terms: vec![(F::ONE, *var)].into_boxed_slice(),
                    constant_term: F::ZERO,
                },
                LookupInput::Expression {
                    linear_terms,
                    constant_coeff,
                } => Degree1Constraint {
                    linear_terms: linear_terms.clone().into_boxed_slice(),
                    constant_term: *constant_coeff,
                },
            },
        };
        table_id = Some(table_id_constraint);
    }

    assert!(
        inputs.len() + (table_id.is_some() as usize) <= total_width,
        "expression {:?} was compiled into {} terms and {} for table ID, but expected total width is {}",
        expr,
        inputs.len(),
        table_id.is_some() as usize,
        total_width
    );

    LookupInputRelation { inputs, table_id }
}

pub(crate) fn layout_lookup_expressions<F: PrimeField, const SINGLE_COLUMN: bool>(
    graph: &mut GKRGraph,
    expressions: Vec<(Vec<LookupInput<F>>, LookupQueryTableType<F>)>,
    num_variables: &mut u64,
    all_variables_to_place: &mut BTreeSet<Variable>,
    variable_names: &mut HashMap<Variable, String>,
    layers_mapping: &mut HashMap<Variable, usize>,
    lookup_type: &str,
    mut decoder_lookup: Option<(Variable, Vec<LookupInput<F>>)>,
    lookup: LookupType,
    total_width: usize,
    expect_table_id: bool,
) -> (
    Variable,                         // multiplicity var
    [GKRAddress; 2],                  // final num/den pair
    NoFieldGKRRelation,               // relation that gives rise to final pair
    Vec<NoFieldVectorLookupRelation>, // all lookup relations for witness evaluation and multiplicity counting
) {
    let mut all_relations_for_witness_eval = vec![];
    // sanity checks
    for (expr, table_type) in expressions.iter() {
        if SINGLE_COLUMN {
            assert_eq!(total_width, 1);
            assert_eq!(expr.len(), 1);
            assert_eq!(
                *table_type,
                LookupQueryTableType::Constant(TableType::DynamicPlaceholder)
            );
        } else {
            assert!(expr.len() <= total_width);
        }
    }

    // create multiplicity right away
    let multiplicity_var = add_compiler_defined_base_layer_variable(
        num_variables,
        all_variables_to_place,
        layers_mapping,
    );
    variable_names.insert(
        multiplicity_var,
        format!("Multiplicity for {}", lookup_type),
    );
    let [multiplicity_pos] = graph.layout_witness_subtree_multiple_variables(
        [multiplicity_var],
        all_variables_to_place,
        &*layers_mapping,
    );

    let mut all_relations_stable_set = BTreeMap::new();
    let mut inputs_at_layers = BTreeMap::new();
    let mut logup_intermediate_output_values_at_layers = BTreeMap::new();
    for (idx, rel) in expressions.into_iter().enumerate() {
        let input_layer = input_layer_for_lookup_expression::<F, SINGLE_COLUMN>(
            &rel,
            expect_table_id,
            &*layers_mapping,
        );
        let input =
            lookup_input_node_from_expr::<F, SINGLE_COLUMN>(&rel, total_width, expect_table_id);
        let input =
            lookup_input_into_relation::<F, SINGLE_COLUMN>(&input, idx, total_width, &*graph);
        all_relations_stable_set.insert(idx, (rel.clone(), input.clone()));
        let ent = inputs_at_layers
            .entry(input_layer)
            .or_insert(BTreeMap::new());
        ent.insert(idx, (rel, input));
    }

    if let Some((mask, decoder_lookup)) = decoder_lookup.as_ref() {
        let mask_layer = *layers_mapping.get(mask).expect("must be known");
        let layer = input_layer_for_lookup_expression::<F, SINGLE_COLUMN>(
            &(
                decoder_lookup.clone(),
                LookupQueryTableType::Constant(TableType::Decoder),
            ),
            expect_table_id,
            &*layers_mapping,
        );
        assert_eq!(mask_layer, 0);
        assert_eq!(layer, 0);
    }

    println!(
        "In total of {} lookups of type {}",
        all_relations_stable_set.len(),
        lookup_type
    );
    if decoder_lookup.is_some() {
        println!("Decoder lookup is present");
    }

    let mut multiplicity_pos = Some(multiplicity_pos);
    let mut relations_map = BTreeMap::new();
    let mut input_layer = 0;
    loop {
        let decoder_lookup = decoder_lookup.take();
        let multiplicity_pos = multiplicity_pos.take();
        drive_lookup_placement::<F, SINGLE_COLUMN>(
            graph,
            input_layer,
            lookup_type,
            lookup,
            total_width,
            expect_table_id,
            decoder_lookup,
            multiplicity_pos,
            &mut inputs_at_layers,
            &mut logup_intermediate_output_values_at_layers,
            &mut relations_map,
            &mut all_relations_for_witness_eval,
        );

        input_layer += 1;

        if inputs_at_layers
            .entry(input_layer)
            .or_insert(BTreeMap::new())
            .len()
            == 0
        {
            let ent = logup_intermediate_output_values_at_layers
                .entry(input_layer)
                .or_insert(vec![]);
            if ent.len() == 1 {
                let (num, den) = ent[0].clone();
                match (num, den) {
                    (
                        LookupNumerator::ExtensionValueWithAllConstantsMixed(num),
                        LookupDenominator::ExtensionValueWithAllConstantsMixed(den),
                    ) => {
                        let relation = relations_map
                            .get(&[num, den])
                            .expect("final relation")
                            .clone();
                        return (
                            multiplicity_var,
                            [num, den],
                            relation,
                            all_relations_for_witness_eval,
                        );
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }
        }
    }
}

fn drive_lookup_placement<F: PrimeField, const SINGLE_COLUMN: bool>(
    graph: &mut GKRGraph,
    input_layer: usize,
    lookup_type: &str,
    lookup: LookupType,
    total_width: usize,
    expect_table_id: bool,
    decoder_lookup: Option<(Variable, Vec<LookupInput<F>>)>,
    multiplicity: Option<GKRAddress>,
    inputs: &mut BTreeMap<
        usize,
        BTreeMap<
            usize,
            (
                (Vec<LookupInput<F>>, LookupQueryTableType<F>),
                NoFieldVectorLookupRelation,
            ),
        >,
    >,
    intermediate_values: &mut BTreeMap<usize, Vec<(LookupNumerator, LookupDenominator)>>,
    relations_map: &mut BTreeMap<[GKRAddress; 2], NoFieldGKRRelation>,
    all_relations_for_witness_eval: &mut Vec<NoFieldVectorLookupRelation>,
) {
    if decoder_lookup.is_some() || multiplicity.is_some() {
        assert_eq!(input_layer, 0);
    }

    let single_columns_lookup_width = match lookup {
        LookupType::RangeCheck16 => Some(16),
        LookupType::TimestampRangeCheck => Some(TIMESTAMP_COLUMNS_NUM_BITS),
        LookupType::Generic => None,
    };

    let num_inputs = inputs.entry(input_layer).or_insert(BTreeMap::new()).len();
    let num_intermediates = intermediate_values
        .entry(input_layer)
        .or_insert(vec![])
        .len();

    println!(
        "At layer {} have {} inputs and {} intermediate values for lookup {:?}",
        input_layer, num_inputs, num_intermediates, lookup
    );
    if decoder_lookup.is_some() {
        println!("Decoder lookup is present at layer {}", input_layer);
    }

    // in general if we want to use some input - we make a cache relation if needed, and then use it,
    // otherwise:
    // - for single column lookup that is non-trivial linear relation we add linear relation and go into next layer
    // - for vector lookup column we add linear relation that produces an extension field element without additive contribution
    // NOTE: cache relations do NOT include additive constant

    match (decoder_lookup, multiplicity) {
        (Some(decoder_lookup), Some(multiplicity)) => {
            assert_eq!(input_layer, 0);
            let (decoder_predicate_var, decoder_lookup) = decoder_lookup;
            let decoder_predicate = graph.get_address_for_variable(decoder_predicate_var);
            let input = lookup_input_node_from_expr::<F, SINGLE_COLUMN>(
                &(
                    decoder_lookup,
                    LookupQueryTableType::Constant(TableType::Decoder),
                ),
                total_width,
                expect_table_id,
            );
            let input = lookup_input_into_relation::<F, SINGLE_COLUMN>(
                &input,
                DECODER_LOOKUP_FORMAL_SET_INDEX,
                total_width,
                &*graph,
            );
            // NOTE: we do not put it into relations for witness eval, as it's
            // special
            assert_eq!(input.columns.len(), graph.setup_addresses(lookup).len());
            assert!(SINGLE_COLUMN == false);

            let setup = graph.setup_addresses(lookup).to_vec().into_boxed_slice();
            use crate::gkr_compiler::lookup_nodes::LookupMaskedWitnessMinusSetupInputNode;
            let node = LookupMaskedWitnessMinusSetupInputNode {
                mask: decoder_predicate,
                input: input,
                multiplicity,
                setup,
            };
            let ([num, den], rel) = node.add_at_layer(graph, input_layer + 1);
            // insert for next layer
            intermediate_values
                .entry(input_layer + 1)
                .or_insert(vec![])
                .push((
                    LookupNumerator::ExtensionValueWithAllConstantsMixed(num),
                    LookupDenominator::ExtensionValueWithAllConstantsMixed(den),
                ));
            relations_map.insert([num, den], rel);
        }
        (Some(_), None) => {
            unreachable!()
        }
        (None, Some(multiplicity)) => {
            // merge with something
            assert_eq!(input_layer, 0);
            let inputs = inputs.entry(input_layer).or_insert(BTreeMap::new());
            let num_inputs = inputs.len();
            let num_intermedaites = intermediate_values
                .entry(input_layer)
                .or_insert(vec![])
                .len();
            assert_eq!(num_intermedaites, 0);

            assert!(num_inputs > 0);
            // we merge with one of the inputs

            // TODO: we can choose which input to merge with, if e.g. there will one input left and pushed
            // to the next layer. Then it's better to push just single-valued one and not linear relation

            if SINGLE_COLUMN {
                let setup = graph.setup_addresses(lookup);
                assert_eq!(setup.len(), 1);

                let key = *inputs.keys().next().unwrap();
                let (_, rel) = inputs.remove(&key).unwrap();
                all_relations_for_witness_eval.push(rel.clone());
                assert_eq!(rel.columns.len(), 1);
                let input = NoFieldSingleColumnLookupRelation {
                    input: rel.columns[0].clone(),
                    lookup_set_index: rel.lookup_set_index,
                };

                use crate::gkr_compiler::lookup_nodes::LookupSingleColumnWitnessMinusSetupInputNode;
                let node = LookupSingleColumnWitnessMinusSetupInputNode {
                    input: input,
                    multiplicity,
                    setup: setup[0],
                    range_check_width: single_columns_lookup_width.unwrap(),
                };
                let ([num, den], rel) = node.add_at_layer(graph, input_layer + 1);
                // insert for next layer
                intermediate_values
                    .entry(input_layer + 1)
                    .or_insert(vec![])
                    .push((
                        LookupNumerator::ExtensionValueWithAllConstantsMixed(num),
                        LookupDenominator::ExtensionValueWithAllConstantsMixed(den),
                    ));
                relations_map.insert([num, den], rel);
            } else {
                let setup = graph.setup_addresses(lookup).to_vec().into_boxed_slice();

                let key = *inputs.keys().next().unwrap();
                let (_, rel) = inputs.remove(&key).unwrap();
                all_relations_for_witness_eval.push(rel.clone());
                assert_eq!(rel.columns.len(), graph.setup_addresses(lookup).len());

                use crate::gkr_compiler::lookup_nodes::VectorLookupWitnessMinusSetupInputNode;
                let node = VectorLookupWitnessMinusSetupInputNode {
                    input: rel,
                    multiplicity,
                    setup: setup,
                };
                let ([num, den], rel) = node.add_at_layer(graph, input_layer + 1);
                // insert for next layer
                intermediate_values
                    .entry(input_layer + 1)
                    .or_insert(vec![])
                    .push((
                        LookupNumerator::ExtensionValueWithAllConstantsMixed(num),
                        LookupDenominator::ExtensionValueWithAllConstantsMixed(den),
                    ));
                relations_map.insert([num, den], rel);
            }
        }
        (None, None) => {
            // nothing
        }
    }

    // we try to merge by pair between inputs and intermediates separately,
    // and then either merge between them, or copy something to the next layer

    let inputs = inputs.entry(input_layer).or_insert(BTreeMap::new());
    while inputs.len() > 1 {
        // merge inputs
        let t = inputs.len();
        merge_lookup_inputs_pair::<F, SINGLE_COLUMN>(
            graph,
            input_layer,
            lookup_type,
            lookup,
            total_width,
            expect_table_id,
            inputs,
            intermediate_values,
            relations_map,
            all_relations_for_witness_eval,
        );
        assert_eq!(inputs.len() + 2, t);
    }

    while intermediate_values
        .entry(input_layer)
        .or_insert(vec![])
        .len()
        > 1
    {
        // merge intermediates
        let t = intermediate_values
            .entry(input_layer)
            .or_insert(vec![])
            .len();
        merge_intermediate_lookup_pair::<F, SINGLE_COLUMN>(
            graph,
            input_layer,
            lookup_type,
            lookup,
            total_width,
            expect_table_id,
            intermediate_values,
            relations_map,
        );

        assert_eq!(
            intermediate_values
                .entry(input_layer)
                .or_insert(vec![])
                .len()
                + 2,
            t
        );
    }

    if inputs.len() == 1
        && intermediate_values
            .entry(input_layer)
            .or_insert(vec![])
            .len()
            == 1
    {
        // merge once between them
        let key = *inputs.keys().next().unwrap();
        let (_, input_rel) = inputs.remove(&key).unwrap();

        let intermediate_inputs = intermediate_values.entry(input_layer).or_insert(vec![]);
        let (num, den) = intermediate_inputs.pop().unwrap();

        all_relations_for_witness_eval.push(input_rel.clone());

        if SINGLE_COLUMN {
            assert_eq!(input_rel.columns.len(), 1);
            let rel = NoFieldSingleColumnLookupRelation {
                input: input_rel.columns[0].clone(),
                lookup_set_index: input_rel.lookup_set_index,
            };
            if rel.input.is_trivial_single_input() {
                todo!();
            } else {
                todo!();
            }
        } else {
            match (num, den) {
                (
                    LookupNumerator::ExtensionValueWithAllConstantsMixed(num),
                    LookupDenominator::ExtensionValueWithAllConstantsMixed(den),
                ) => {
                    use crate::gkr_compiler::lookup_nodes::VectorLookupExplicitPairWithInputAggregationNode;
                    let node = VectorLookupExplicitPairWithInputAggregationNode {
                        lhs_num: num,
                        lhs_den: den,
                        vector_input: input_rel,
                    };
                    let ([num, den], rel) = node.add_at_layer(graph, input_layer + 1);
                    intermediate_values
                        .entry(input_layer + 1)
                        .or_insert(vec![])
                        .push((
                            LookupNumerator::ExtensionValueWithAllConstantsMixed(num),
                            LookupDenominator::ExtensionValueWithAllConstantsMixed(den),
                        ));
                    relations_map.insert([num, den], rel);
                }
                (num, den) => {
                    panic!("combination of {:?}/{:?} is not yet supported", num, den);
                }
            }
        }
    }

    // copy to the next layer
    if inputs.len() == 1 {
        let key = *inputs.keys().next().unwrap();
        let (_, rel) = inputs.remove(&key).unwrap();
        all_relations_for_witness_eval.push(rel.clone());

        if SINGLE_COLUMN {
            let setup = graph.setup_addresses(lookup);
            assert_eq!(setup.len(), 1);

            assert_eq!(rel.columns.len(), 1);
            let input = NoFieldSingleColumnLookupRelation {
                input: rel.columns[0].clone(),
                lookup_set_index: rel.lookup_set_index,
            };

            use crate::gkr_compiler::lookup_nodes::MaterializeSingleInputNode;
            let node = MaterializeSingleInputNode {
                input: input.clone(),
                range_check_width: single_columns_lookup_width.unwrap(),
            };
            let (den_without_additive_constant, _) = node.add_at_layer(graph, input_layer + 1);
            // insert for next layer
            intermediate_values
                .entry(input_layer + 1)
                .or_insert(vec![])
                .push((
                    LookupNumerator::Identity,
                    LookupDenominator::BaseFieldValueWithoutAdditiveConstant(
                        den_without_additive_constant,
                    ),
                ));
        } else {
            use crate::gkr_compiler::lookup_nodes::MaterializeVectorInputNode;
            let node = MaterializeVectorInputNode(rel);
            let (den_without_additive_constant, _) = node.add_at_layer(graph, input_layer + 1);
            // insert for next layer
            intermediate_values
                .entry(input_layer + 1)
                .or_insert(vec![])
                .push((
                    LookupNumerator::Identity,
                    LookupDenominator::ExtensionFieldValueWithoutAdditiveConstant(
                        den_without_additive_constant,
                    ),
                ));
        }
    }

    if intermediate_values
        .entry(input_layer)
        .or_insert(vec![])
        .len()
        == 1
    {
        let intermediate_inputs = intermediate_values.entry(input_layer).or_insert(vec![]);
        let (num, den) = intermediate_inputs.pop().unwrap();

        match (num, den) {
            (
                LookupNumerator::Identity,
                LookupDenominator::BaseFieldValueWithoutAdditiveConstant(input),
            ) => {
                let output = graph.add_intermediate_variable_at_layer(input_layer + 1);
                let relation = NoFieldGKRRelation::Copy { input, output };
                graph.add_enforced_relation(relation.clone(), input_layer + 1);

                intermediate_values
                    .entry(input_layer + 1)
                    .or_insert(vec![])
                    .push((
                        LookupNumerator::Identity,
                        LookupDenominator::BaseFieldValueWithoutAdditiveConstant(output),
                    ));
            }
            (
                LookupNumerator::Identity,
                LookupDenominator::ExtensionFieldValueWithoutAdditiveConstant(input),
            ) => {
                let output = graph.add_intermediate_variable_at_layer(input_layer + 1);
                let relation = NoFieldGKRRelation::Copy { input, output };
                graph.add_enforced_relation(relation.clone(), input_layer + 1);

                intermediate_values
                    .entry(input_layer + 1)
                    .or_insert(vec![])
                    .push((
                        LookupNumerator::Identity,
                        LookupDenominator::ExtensionFieldValueWithoutAdditiveConstant(output),
                    ));
            }
            (
                LookupNumerator::ExtensionValueWithAllConstantsMixed(num),
                LookupDenominator::ExtensionValueWithAllConstantsMixed(den),
            ) => {
                // copy them
                let [num, den] = [num, den].map(|el| {
                    let output = graph.add_intermediate_variable_at_layer(input_layer + 1);
                    let relation = NoFieldGKRRelation::Copy { input: el, output };
                    graph.add_enforced_relation(relation.clone(), input_layer + 1);

                    output
                });
                intermediate_values
                    .entry(input_layer + 1)
                    .or_insert(vec![])
                    .push((
                        LookupNumerator::ExtensionValueWithAllConstantsMixed(num),
                        LookupDenominator::ExtensionValueWithAllConstantsMixed(den),
                    ));
            }
            (num, den) => {
                panic!("combination of {:?}/{:?} is not possible here", num, den);
            }
        }
    }
}

fn merge_lookup_inputs_pair<F: PrimeField, const SINGLE_COLUMN: bool>(
    graph: &mut GKRGraph,
    input_layer: usize,
    lookup_type: &str,
    lookup: LookupType,
    total_width: usize,
    expect_table_id: bool,
    inputs: &mut BTreeMap<
        usize,
        (
            (Vec<LookupInput<F>>, LookupQueryTableType<F>),
            NoFieldVectorLookupRelation,
        ),
    >,
    intermediate_values: &mut BTreeMap<usize, Vec<(LookupNumerator, LookupDenominator)>>,
    relations_map: &mut BTreeMap<[GKRAddress; 2], NoFieldGKRRelation>,
    all_relations_for_witness_eval: &mut Vec<NoFieldVectorLookupRelation>,
) {
    let single_columns_lookup_width = match lookup {
        LookupType::RangeCheck16 => Some(16),
        LookupType::TimestampRangeCheck => Some(TIMESTAMP_COLUMNS_NUM_BITS),
        LookupType::Generic => None,
    };

    let mut keys = inputs.keys();
    let k0 = *keys.next().unwrap();
    let k1 = *keys.next().unwrap();
    let (_input_0, rel_0) = inputs.remove(&k0).unwrap();
    let (_input_1, rel_1) = inputs.remove(&k1).unwrap();
    all_relations_for_witness_eval.push(rel_0.clone());
    all_relations_for_witness_eval.push(rel_1.clone());

    if SINGLE_COLUMN {
        use crate::gkr_compiler::lookup_nodes::LookupSingleColumnWitnessPairAggregationNode;

        let [lhs, rhs] = [rel_0, rel_1].map(|rel| {
            assert_eq!(rel.columns.len(), 1);
            NoFieldSingleColumnLookupRelation {
                input: rel.columns[0].clone(),
                lookup_set_index: rel.lookup_set_index,
            }
        });

        let node = LookupSingleColumnWitnessPairAggregationNode {
            lhs,
            rhs,
            range_check_width: single_columns_lookup_width.unwrap(),
        };
        let ([num, den], _) = node.add_at_layer(graph, input_layer + 1);
        intermediate_values
            .entry(input_layer + 1)
            .or_insert(vec![])
            .push((
                LookupNumerator::ExtensionValueWithAllConstantsMixed(num),
                LookupDenominator::ExtensionValueWithAllConstantsMixed(den),
            ));
    } else {
        use crate::gkr_compiler::lookup_nodes::VectorLookupWitnessPairAggregationFromCachesNode;

        let node = VectorLookupWitnessPairAggregationFromCachesNode {
            lhs: rel_0,
            rhs: rel_1,
        };
        let ([num, den], _) = node.add_at_layer(graph, input_layer + 1);
        intermediate_values
            .entry(input_layer + 1)
            .or_insert(vec![])
            .push((
                LookupNumerator::ExtensionValueWithAllConstantsMixed(num),
                LookupDenominator::ExtensionValueWithAllConstantsMixed(den),
            ));
    }
}

fn merge_intermediate_lookup_pair<F: PrimeField, const SINGLE_COLUMN: bool>(
    graph: &mut GKRGraph,
    input_layer: usize,
    lookup_type: &str,
    lookup: LookupType,
    total_width: usize,
    expect_table_id: bool,
    intermediate_values: &mut BTreeMap<usize, Vec<(LookupNumerator, LookupDenominator)>>,
    relations_map: &mut BTreeMap<[GKRAddress; 2], NoFieldGKRRelation>,
) {
    let single_columns_lookup_width = match lookup {
        LookupType::RangeCheck16 => Some(16),
        LookupType::TimestampRangeCheck => Some(TIMESTAMP_COLUMNS_NUM_BITS),
        LookupType::Generic => None,
    };

    assert!(input_layer > 0);
    let inputs = intermediate_values.get_mut(&input_layer).unwrap();
    let pair_0 = inputs.pop().unwrap();
    let pair_1 = inputs.pop().unwrap();
    match (pair_0, pair_1) {
        (
            (
                LookupNumerator::Identity,
                LookupDenominator::BaseFieldValueWithoutAdditiveConstant(base_den),
            ),
            (
                LookupNumerator::ExtensionValueWithAllConstantsMixed(num),
                LookupDenominator::ExtensionValueWithAllConstantsMixed(den),
            ),
        )
        | (
            (
                LookupNumerator::ExtensionValueWithAllConstantsMixed(num),
                LookupDenominator::ExtensionValueWithAllConstantsMixed(den),
            ),
            (
                LookupNumerator::Identity,
                LookupDenominator::BaseFieldValueWithoutAdditiveConstant(base_den),
            ),
        ) if SINGLE_COLUMN => {
            use crate::gkr_compiler::lookup_nodes::LookupExplicitPairWithSingleColumnMaterializedInputAggregationNode;
            let node = LookupExplicitPairWithSingleColumnMaterializedInputAggregationNode {
                lhs_num: num,
                lhs_den: den,
                base_input: base_den,
                range_check_width: single_columns_lookup_width.unwrap(),
            };
            let ([num, den], rel) = node.add_at_layer(graph, input_layer + 1);
            // insert for next layer
            intermediate_values
                .entry(input_layer + 1)
                .or_insert(vec![])
                .push((
                    LookupNumerator::ExtensionValueWithAllConstantsMixed(num),
                    LookupDenominator::ExtensionValueWithAllConstantsMixed(den),
                ));
            relations_map.insert([num, den], rel);
        }
        (
            (
                LookupNumerator::Identity,
                LookupDenominator::ExtensionFieldValueWithoutAdditiveConstant(ext_den),
            ),
            (
                LookupNumerator::ExtensionValueWithAllConstantsMixed(num),
                LookupDenominator::ExtensionValueWithAllConstantsMixed(den),
            ),
        )
        | (
            (
                LookupNumerator::ExtensionValueWithAllConstantsMixed(num),
                LookupDenominator::ExtensionValueWithAllConstantsMixed(den),
            ),
            (
                LookupNumerator::Identity,
                LookupDenominator::ExtensionFieldValueWithoutAdditiveConstant(ext_den),
            ),
        ) if SINGLE_COLUMN == false => {
            use crate::gkr_compiler::lookup_nodes::VectorLookupExplicitPairWithMaterializedInputAggregationNode;
            let node = VectorLookupExplicitPairWithMaterializedInputAggregationNode {
                lhs_num: num,
                lhs_den: den,
                vector_input: ext_den,
            };
            let ([num, den], rel) = node.add_at_layer(graph, input_layer + 1);
            // insert for next layer
            intermediate_values
                .entry(input_layer + 1)
                .or_insert(vec![])
                .push((
                    LookupNumerator::ExtensionValueWithAllConstantsMixed(num),
                    LookupDenominator::ExtensionValueWithAllConstantsMixed(den),
                ));
            relations_map.insert([num, den], rel);
        }
        (
            (
                LookupNumerator::ExtensionValueWithAllConstantsMixed(num_0),
                LookupDenominator::ExtensionValueWithAllConstantsMixed(den_0),
            ),
            (
                LookupNumerator::ExtensionValueWithAllConstantsMixed(num_1),
                LookupDenominator::ExtensionValueWithAllConstantsMixed(den_1),
            ),
        ) => {
            use crate::gkr_compiler::lookup_nodes::LookupExplicitPairAggregationNode;
            let node = LookupExplicitPairAggregationNode {
                lhs_num: num_0,
                lhs_den: den_0,
                rhs_num: num_1,
                rhs_den: den_1,
            };
            let ([num, den], rel) = node.add_at_layer(graph, input_layer + 1);
            // insert for next layer
            intermediate_values
                .entry(input_layer + 1)
                .or_insert(vec![])
                .push((
                    LookupNumerator::ExtensionValueWithAllConstantsMixed(num),
                    LookupDenominator::ExtensionValueWithAllConstantsMixed(den),
                ));
            relations_map.insert([num, den], rel);
        }

        (pair_0, pair_1) => {
            panic!(
                "combination of {:?}/{:?} is not yet supported",
                pair_0, pair_1
            );
        }
    }
}

//     // we need to rank values, such that

//     let total_rational_terms = expressions.len() + 1 + (decoder_lookup.is_some() as usize);

//     let mut initial_reduction_layer_nodes = vec![];
//     assert!(total_rational_terms > 0);
//     let mut placement_layer = 1;

//     if total_rational_terms % 2 == 0 {
//         if let Some(decoder_lookup) = decoder_lookup {
//             {
//                 let (decoder_predicate_var, decoder_lookup) = decoder_lookup;
//                 let decoder_predicate = graph.get_address_for_variable(decoder_predicate_var);
//                 let input = lookup_input_node_from_expr::<F, SINGLE_COLUMN>(
//                     &(
//                         decoder_lookup,
//                         LookupQueryTableType::Constant(TableType::Decoder),
//                     ),
//                     total_width,
//                     expect_table_id,
//                 );
//                 let input = lookup_input_into_relation::<F, SINGLE_COLUMN>(
//                     &input,
//                     DECODER_LOOKUP_FORMAL_SET_INDEX,
//                     &*graph,
//                 );
//                 assert_eq!(input.columns.len(), graph.setup_addresses(lookup).len());
//                 assert!(SINGLE_COLUMN == false);

//                 let a = LookupRationalPair {
//                     num: lookup_nodes::LookupNumerator::Positive(decoder_predicate),
//                     num_node: None,
//                     den: vector_or_single_input::<SINGLE_COLUMN>(input),
//                     den_node: None,
//                     lookup_type: lookup,
//                 };
//                 let b = LookupRationalPair {
//                     num: lookup_nodes::LookupNumerator::Negative(multiplicity_pos),
//                     num_node: None,
//                     den: vector_or_single_setup::<SINGLE_COLUMN>(graph, lookup),
//                     den_node: None,
//                     lookup_type: lookup,
//                 };

//                 let (next_pair, rel) = LookupRationalPair::accumulate_pair_into_graph(
//                     (a, b),
//                     graph,
//                     placement_layer,
//                     single_columns_lookup_width,
//                 );

//                 if expressions.is_empty() {
//                     return (multiplicity_var, next_pair, rel, initial_relations);
//                 }

//                 initial_reduction_layer_nodes.push((next_pair, rel));
//             }

//             // and continue over all other pairs
//             assert_eq!(expressions.len() % 2, 0);
//             let mut set_idx = 0;
//             for [a, b] in expressions.as_chunks::<2>().0 {
//                 // We will take 2 inputs with "1" in the numerator, and some witness in denominator
//                 let a = lookup_input_node_from_expr::<F, SINGLE_COLUMN>(
//                     &a,
//                     total_width,
//                     expect_table_id,
//                 );
//                 let b = lookup_input_node_from_expr::<F, SINGLE_COLUMN>(
//                     &b,
//                     total_width,
//                     expect_table_id,
//                 );
//                 let a = lookup_input_into_relation::<F, SINGLE_COLUMN>(&a, set_idx, &*graph);
//                 set_idx += 1;
//                 let b = lookup_input_into_relation::<F, SINGLE_COLUMN>(&b, set_idx, &*graph);
//                 set_idx += 1;
//                 let a = LookupRationalPair {
//                     num: lookup_nodes::LookupNumerator::Identity,
//                     num_node: None,
//                     den: vector_or_single_input::<SINGLE_COLUMN>(a),
//                     den_node: None,
//                     lookup_type: lookup,
//                 };
//                 let b = LookupRationalPair {
//                     num: lookup_nodes::LookupNumerator::Identity,
//                     num_node: None,
//                     den: vector_or_single_input::<SINGLE_COLUMN>(b),
//                     den_node: None,
//                     lookup_type: lookup,
//                 };
//                 let (next_pair, rel) = LookupRationalPair::accumulate_pair_into_graph(
//                     (a, b),
//                     graph,
//                     placement_layer,
//                     single_columns_lookup_width,
//                 );

//                 initial_reduction_layer_nodes.push((next_pair, rel));
//             }
//         } else {
//             // we will make a mixed node with one of the witnesses to avoid copying multiplicity
//             assert_eq!(expressions.len() % 2, 1);
//             let (first, expressions) = expressions.split_at(1);
//             let first = &first[0];
//             let mut set_idx = 0;
//             {
//                 let input = lookup_input_node_from_expr::<F, SINGLE_COLUMN>(
//                     first,
//                     total_width,
//                     expect_table_id,
//                 );
//                 let input =
//                     lookup_input_into_relation::<F, SINGLE_COLUMN>(&input, set_idx, &*graph);
//                 set_idx += 1;
//                 assert_eq!(input.columns.len(), graph.setup_addresses(lookup).len());

//                 let a = LookupRationalPair {
//                     num: lookup_nodes::LookupNumerator::Identity,
//                     num_node: None,
//                     den: vector_or_single_input::<SINGLE_COLUMN>(input),
//                     den_node: None,
//                     lookup_type: lookup,
//                 };
//                 let b = LookupRationalPair {
//                     num: lookup_nodes::LookupNumerator::Negative(multiplicity_pos),
//                     num_node: None,
//                     den: vector_or_single_setup::<SINGLE_COLUMN>(graph, lookup),
//                     den_node: None,
//                     lookup_type: lookup,
//                 };

//                 let (next_pair, rel) = LookupRationalPair::accumulate_pair_into_graph(
//                     (a, b),
//                     graph,
//                     placement_layer,
//                     single_columns_lookup_width,
//                 );

//                 if expressions.is_empty() {
//                     return (multiplicity_var, next_pair, rel, initial_relations);
//                 }

//                 initial_reduction_layer_nodes.push((next_pair, rel));
//             }

//             assert_eq!(expressions.len() % 2, 0);
//             for [a, b] in expressions.as_chunks::<2>().0 {
//                 let a = lookup_input_node_from_expr::<F, SINGLE_COLUMN>(
//                     &a,
//                     total_width,
//                     expect_table_id,
//                 );
//                 let b = lookup_input_node_from_expr::<F, SINGLE_COLUMN>(
//                     &b,
//                     total_width,
//                     expect_table_id,
//                 );
//                 let a = lookup_input_into_relation::<F, SINGLE_COLUMN>(&a, set_idx, &*graph);
//                 set_idx += 1;
//                 let b = lookup_input_into_relation::<F, SINGLE_COLUMN>(&b, set_idx, &*graph);
//                 set_idx += 1;
//                 let a = LookupRationalPair {
//                     num: lookup_nodes::LookupNumerator::Identity,
//                     num_node: None,
//                     den: vector_or_single_input::<SINGLE_COLUMN>(a),
//                     den_node: None,
//                     lookup_type: lookup,
//                 };
//                 let b = LookupRationalPair {
//                     num: lookup_nodes::LookupNumerator::Identity,
//                     num_node: None,
//                     den: vector_or_single_input::<SINGLE_COLUMN>(b),
//                     den_node: None,
//                     lookup_type: lookup,
//                 };
//                 let (next_pair, rel) = LookupRationalPair::accumulate_pair_into_graph(
//                     (a, b),
//                     graph,
//                     placement_layer,
//                     single_columns_lookup_width,
//                 );

//                 initial_reduction_layer_nodes.push((next_pair, rel));
//             }
//         }
//     } else {
//         // inevitably we will need to copy something, so we will try to copy the simplest case
//         if let Some(decoder_lookup) = decoder_lookup {
//             assert!(expressions.is_empty() == false);
//             {
//                 let (decoder_predicate_var, decoder_lookup) = decoder_lookup;
//                 let decoder_predicate = graph.get_address_for_variable(decoder_predicate_var);
//                 let input = lookup_input_node_from_expr::<F, SINGLE_COLUMN>(
//                     &(
//                         decoder_lookup,
//                         LookupQueryTableType::Constant(TableType::Decoder),
//                     ),
//                     total_width,
//                     expect_table_id,
//                 );
//                 let input = lookup_input_into_relation::<F, SINGLE_COLUMN>(
//                     &input,
//                     DECODER_LOOKUP_FORMAL_SET_INDEX,
//                     &*graph,
//                 );
//                 assert_eq!(input.columns.len(), graph.setup_addresses(lookup).len());

//                 let a = LookupRationalPair {
//                     num: lookup_nodes::LookupNumerator::Positive(decoder_predicate),
//                     num_node: None,
//                     den: vector_or_single_input::<SINGLE_COLUMN>(input),
//                     den_node: None,
//                     lookup_type: lookup,
//                 };
//                 let b = LookupRationalPair {
//                     num: lookup_nodes::LookupNumerator::Negative(multiplicity_pos),
//                     num_node: None,
//                     den: vector_or_single_setup::<SINGLE_COLUMN>(graph, lookup),
//                     den_node: None,
//                     lookup_type: lookup,
//                 };

//                 let (next_pair, rel) = LookupRationalPair::accumulate_pair_into_graph(
//                     (a, b),
//                     graph,
//                     placement_layer,
//                     single_columns_lookup_width,
//                 );

//                 if expressions.is_empty() {
//                     return (multiplicity_var, next_pair, rel, initial_relations);
//                 }

//                 initial_reduction_layer_nodes.push((next_pair, rel));
//             }

//             // and continue over all other pairs
//             assert_eq!(expressions.len() % 2, 1);
//             let mut set_idx = 0;
//             for [a, b] in expressions.as_chunks::<2>().0 {
//                 let a = lookup_input_node_from_expr::<F, SINGLE_COLUMN>(
//                     &a,
//                     total_width,
//                     expect_table_id,
//                 );
//                 let b = lookup_input_node_from_expr::<F, SINGLE_COLUMN>(
//                     &b,
//                     total_width,
//                     expect_table_id,
//                 );
//                 let a = lookup_input_into_relation::<F, SINGLE_COLUMN>(&a, set_idx, &*graph);
//                 set_idx += 1;
//                 let b = lookup_input_into_relation::<F, SINGLE_COLUMN>(&b, set_idx, &*graph);
//                 set_idx += 1;
//                 let a = LookupRationalPair {
//                     num: lookup_nodes::LookupNumerator::Identity,
//                     num_node: None,
//                     den: vector_or_single_input::<SINGLE_COLUMN>(a),
//                     den_node: None,
//                     lookup_type: lookup,
//                 };
//                 let b = LookupRationalPair {
//                     num: lookup_nodes::LookupNumerator::Identity,
//                     num_node: None,
//                     den: vector_or_single_input::<SINGLE_COLUMN>(b),
//                     den_node: None,
//                     lookup_type: lookup,
//                 };
//                 let (next_pair, rel) = LookupRationalPair::accumulate_pair_into_graph(
//                     (a, b),
//                     graph,
//                     placement_layer,
//                     single_columns_lookup_width,
//                 );

//                 initial_reduction_layer_nodes.push((next_pair, rel));
//             }
//             {
//                 let last_input = expressions.as_chunks::<2>().1[0].clone();
//                 let last_input = lookup_input_node_from_expr::<F, SINGLE_COLUMN>(
//                     &last_input,
//                     total_width,
//                     expect_table_id,
//                 );
//                 let last_input =
//                     lookup_input_into_relation::<F, SINGLE_COLUMN>(&last_input, set_idx, &*graph);
//                 let last_input = LookupRationalPair {
//                     num: lookup_nodes::LookupNumerator::Identity,
//                     num_node: None,
//                     den: copy_single_base_input_or_materialize_vector::<SINGLE_COLUMN>(last_input),
//                     den_node: None,
//                     lookup_type: lookup,
//                 };

//                 let (next_pair, rel) = LookupRationalPair::add_single_into_graph(
//                     last_input,
//                     graph,
//                     placement_layer,
//                     single_columns_lookup_width,
//                 );

//                 initial_reduction_layer_nodes.push((next_pair, rel));
//             }
//         } else {
//             // we will make a mixed node with one of the witnesses to avoid copying multiplicity and setup
//             assert_eq!(expressions.len() % 2, 0);
//             let (first, expressions) = expressions.split_at(1);
//             let first = &first[0];
//             let mut set_idx = 0;
//             {
//                 let input = lookup_input_node_from_expr::<F, SINGLE_COLUMN>(
//                     first,
//                     total_width,
//                     expect_table_id,
//                 );
//                 let input =
//                     lookup_input_into_relation::<F, SINGLE_COLUMN>(&input, set_idx, &*graph);
//                 set_idx += 1;
//                 let a = LookupRationalPair {
//                     num: lookup_nodes::LookupNumerator::Identity,
//                     num_node: None,
//                     den: vector_or_single_input::<SINGLE_COLUMN>(input),
//                     den_node: None,
//                     lookup_type: lookup,
//                 };
//                 let b = LookupRationalPair {
//                     num: lookup_nodes::LookupNumerator::Negative(multiplicity_pos),
//                     num_node: None,
//                     den: vector_or_single_setup::<SINGLE_COLUMN>(graph, lookup),
//                     den_node: None,
//                     lookup_type: lookup,
//                 };

//                 let (next_pair, rel) = LookupRationalPair::accumulate_pair_into_graph(
//                     (a, b),
//                     graph,
//                     placement_layer,
//                     single_columns_lookup_width,
//                 );

//                 initial_reduction_layer_nodes.push((next_pair, rel));
//             }

//             assert_eq!(expressions.len() % 2, 1);
//             for [a, b] in expressions.as_chunks::<2>().0 {
//                 let a = lookup_input_node_from_expr::<F, SINGLE_COLUMN>(
//                     &a,
//                     total_width,
//                     expect_table_id,
//                 );
//                 let b = lookup_input_node_from_expr::<F, SINGLE_COLUMN>(
//                     &b,
//                     total_width,
//                     expect_table_id,
//                 );
//                 let a = lookup_input_into_relation::<F, SINGLE_COLUMN>(&a, set_idx, &*graph);
//                 set_idx += 1;
//                 let b = lookup_input_into_relation::<F, SINGLE_COLUMN>(&b, set_idx, &*graph);
//                 set_idx += 1;
//                 let a = LookupRationalPair {
//                     num: lookup_nodes::LookupNumerator::Identity,
//                     num_node: None,
//                     den: vector_or_single_input::<SINGLE_COLUMN>(a),
//                     den_node: None,
//                     lookup_type: lookup,
//                 };
//                 let b = LookupRationalPair {
//                     num: lookup_nodes::LookupNumerator::Identity,
//                     num_node: None,
//                     den: vector_or_single_input::<SINGLE_COLUMN>(b),
//                     den_node: None,
//                     lookup_type: lookup,
//                 };
//                 let (next_pair, rel) = LookupRationalPair::accumulate_pair_into_graph(
//                     (a, b),
//                     graph,
//                     placement_layer,
//                     single_columns_lookup_width,
//                 );

//                 initial_reduction_layer_nodes.push((next_pair, rel));
//             }
//             {
//                 let last_input = expressions.as_chunks::<2>().1[0].clone();
//                 let last_input = lookup_input_node_from_expr::<F, SINGLE_COLUMN>(
//                     &last_input,
//                     total_width,
//                     expect_table_id,
//                 );
//                 let last_input =
//                     lookup_input_into_relation::<F, SINGLE_COLUMN>(&last_input, set_idx, &*graph);
//                 let last_input = LookupRationalPair {
//                     num: lookup_nodes::LookupNumerator::Identity,
//                     num_node: None,
//                     den: copy_single_base_input_or_materialize_vector::<SINGLE_COLUMN>(last_input),
//                     den_node: None,
//                     lookup_type: lookup,
//                 };

//                 let (next_pair, rel) = LookupRationalPair::add_single_into_graph(
//                     last_input,
//                     graph,
//                     placement_layer,
//                     single_columns_lookup_width,
//                 );

//                 initial_reduction_layer_nodes.push((next_pair, rel));
//             }
//         }
//     }

//     // now we resolved a problem of copying from base layer, but we still want to have all the relations to be between two
//     // nearby layers only

//     println!(
//         "Will continue placement of {} lookup rationals into layer {}",
//         initial_reduction_layer_nodes.len(),
//         placement_layer + 1
//     );

//     let mut current_layer = initial_reduction_layer_nodes;

//     loop {
//         if current_layer.len() == 1 {
//             let (last_pair, rel) = current_layer.pop().unwrap();
//             return (multiplicity_var, last_pair, rel, initial_relations);
//         }

//         placement_layer += 1;
//         let mut next_layer = vec![];
//         for [a, b] in current_layer.as_chunks::<2>().0.iter() {
//             let next_pair = LookupRationalPair::accumulate_pair_into_graph(
//                 (a.0.clone(), b.0.clone()),
//                 graph,
//                 placement_layer,
//                 single_columns_lookup_width,
//             );

//             next_layer.push(next_pair);
//         }
//         match current_layer.as_chunks::<2>().1 {
//             [] => {}
//             [last] => {
//                 let next_pair = LookupRationalPair::add_single_into_graph(
//                     last.0.clone(),
//                     graph,
//                     placement_layer,
//                     single_columns_lookup_width,
//                 );

//                 next_layer.push(next_pair);
//             }
//             _ => {
//                 unreachable!()
//             }
//         }

//         current_layer = next_layer;
//     }
// }
