use crate::{
    constraint::Constraint,
    definitions::{GKRAddress, Variable},
    gkr_compiler::graph::{GKRGraph, GraphHolder},
};

use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuadraticConstraintsPartNode<F: PrimeField> {
    pub parts: Vec<Vec<(F, Variable, Variable)>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstraintsCollapseNode<F: PrimeField> {
    pub predicate: Variable,
    pub quadratic_gate: QuadraticConstraintsPartNode<F>,
    pub linear_parts: Vec<Vec<(F, Variable)>>,
    pub constant_parts: Vec<F>,
}

// impl<F: PrimeField> DependentNode for QuadraticConstraintsPartNode<F> {
//     fn add_dependencies_into(
//         &self,
//         graph: &mut dyn graph::GraphHolder,
//         dst: &mut Vec<graph::NodeIndex>,
//     ) {
//         // FIXME: handle the case when some variables are indeed intermediate defined via other constraints
//         for c in self.parts.iter() {
//             for (_, a, b) in c.iter() {
//                 let a = graph.get_node_index_for_variable(*a);
//                 let b = graph.get_node_index_for_variable(*b);
//                 dst.push(a);
//                 dst.push(b);
//             }
//         }
//     }
// }

// impl<F: PrimeField> GraphElement for QuadraticConstraintsPartNode<F> {
//     fn as_dyn(&'_ self) -> &'_ (dyn GraphElement + 'static) {
//         self
//     }
//     fn dyn_clone(&self) -> Box<dyn GraphElement> {
//         Box::new(self.clone())
//     }
//     fn equals(&self, other: &dyn GraphElement) -> bool {
//         graph_element_equals_if_eq(self, other)
//     }
//     fn dependencies(&self, graph: &mut dyn graph::GraphHolder) -> Vec<graph::NodeIndex> {
//         let mut dst = vec![];
//         DependentNode::add_dependencies_into(self, graph, &mut dst);
//         dst
//     }
//     fn short_name(&self) -> String {
//         format!("Quadratic part of {} constraints", self.parts.len())
//     }
//     fn evaluation_description(&self, graph: &mut dyn GraphHolder) -> NoFieldGKRRelation {
//         // compute stats
//         let mut cross_terms_for_vars = HashMap::<Variable, HashSet<(F, Variable)>>::new();
//         for c in self.parts.iter() {
//             for (c, a, b) in c.iter() {
//                 if *a != *b {
//                     let p = cross_terms_for_vars.entry(*a).or_default().insert((*c, *b));
//                     assert!(p, "cross term for variable {:?} in a set for variable {:?} already exists", b, a);
//                     let p = cross_terms_for_vars.entry(*b).or_default().insert((*c, *a));
//                     assert!(p, "cross term for variable {:?} in a set for variable {:?} already exists", a, b);
//                 } else {
//                     let p = cross_terms_for_vars.entry(*a).or_default().insert((*c, *b));
//                     assert!(p);
//                 }
//             }
//         }

//         // we want to reduce number of multiplications
//         let mut selected_terms = vec![];
//         loop {
//             if cross_terms_for_vars.is_empty() {
//                 break;
//             }
//             let (next_best_candidate, _) = cross_terms_for_vars
//                 .iter()
//                 .map(|(k, v)| (*k, v.len()))
//                 .max_by(|a, b| a.1.cmp(&b.1))
//                 .unwrap();
//             let cross_terms = cross_terms_for_vars.remove(&next_best_candidate).unwrap();
//             // cleanup
//             for (c, other) in cross_terms.iter() {
//                 if *other != next_best_candidate {
//                     let exists = cross_terms_for_vars
//                         .get_mut(other)
//                         .unwrap()
//                         .remove(&(*c, next_best_candidate));
//                     assert!(exists);
//                     if cross_terms_for_vars.get(other).unwrap().is_empty() {
//                         cross_terms_for_vars.remove(other);
//                     }
//                 }
//             }
//             // we do not care yet about stable sort
//             let mut terms = vec![];
//             for (c, other) in cross_terms.iter() {
//                 let place = graph.get_address_for_variable(*other);
//                 terms.push((c.as_u32_reduced(), place));
//             }
//             terms.sort_by(|a, b| a.1.cmp(&b.1));
//             let next_best_candidate = graph.get_address_for_variable(next_best_candidate);
//             selected_terms.push((next_best_candidate, terms.into_boxed_slice()));
//         }

//         NoFieldGKRRelation::PureQuadratic(NoFieldPureQuadraticGKRRelation {
//             terms: selected_terms.into_boxed_slice(),
//         })
//     }
// }

// impl<F: PrimeField> DependentNode for ConstraintsCollapseNode<F> {
//     fn add_dependencies_into(
//         &self,
//         graph: &mut dyn graph::GraphHolder,
//         dst: &mut Vec<graph::NodeIndex>,
//     ) {
//         dst.push(graph.get_node_index_for_variable(self.predicate));
//         dst.push(
//             graph
//                 .get_node_index(&self.quadratic_gate)
//                 .expect("already placed"),
//         );

//         // FIXME: handle the case when some variables are indeed intermediate defined via other constraints
//         for c in self.linear_parts.iter() {
//             for (_, a) in c.iter() {
//                 let a = graph.get_node_index_for_variable(*a);
//                 dst.push(a);
//             }
//         }
//     }
// }

// impl<F: PrimeField> GraphElement for ConstraintsCollapseNode<F> {
//     fn as_dyn(&'_ self) -> &'_ (dyn GraphElement + 'static) {
//         self
//     }
//     fn dyn_clone(&self) -> Box<dyn GraphElement> {
//         Box::new(self.clone())
//     }
//     fn equals(&self, other: &dyn GraphElement) -> bool {
//         graph_element_equals_if_eq(self, other)
//     }
//     fn dependencies(&self, graph: &mut dyn graph::GraphHolder) -> Vec<graph::NodeIndex> {
//         let mut dst = vec![];
//         DependentNode::add_dependencies_into(self, graph, &mut dst);
//         dst
//     }
//     fn short_name(&self) -> String {
//         format!(
//             "Constraint collapse of {} constraints",
//             self.linear_parts.len()
//         )
//     }

//     fn evaluation_description(&self, graph: &mut dyn GraphHolder) -> NoFieldGKRRelation {
//         let predicate = graph.get_address_for_variable(self.predicate);
//         let remainder_from_quadratic = graph.get_address_for_node(&self.quadratic_gate);
//         let sparse_constant_remainders = self
//             .constant_parts
//             .iter()
//             .map(|el| el.as_u32_reduced())
//             .collect::<Vec<_>>()
//             .into_boxed_slice();
//         let num_terms = sparse_constant_remainders.len();
//         let mut sparse_linear_remainders = vec![];
//         for set in self.linear_parts.iter() {
//             let mut subset = vec![];
//             for (c, v) in set.iter() {
//                 let address = graph.get_address_for_variable(*v);
//                 subset.push((c.as_u32_reduced(), address));
//             }
//             subset.sort_by(|a, b| a.1.cmp(&b.1));
//             sparse_linear_remainders.push(subset.into_boxed_slice());
//         }

//         let sparse_linear_remainders = sparse_linear_remainders.into_boxed_slice();
//         assert_eq!(num_terms, sparse_linear_remainders.len());

//         NoFieldGKRRelation::SpecialConstraintCollapse(NoFieldSpecialConstraintCollapseGKRRelation {
//             predicate,
//             remainder_from_quadratic,
//             sparse_linear_remainders,
//             sparse_constant_remainders,
//             num_terms,
//         })
//     }
// }

pub(crate) fn layout_constraints<F: PrimeField>(
    graph: &mut GKRGraph,
    constraints: Vec<(Constraint<F>, bool)>,
    predicate: Variable,
) -> ConstraintsCollapseNode<F> {
    todo!();

    // let mut quadratic_parts = vec![];
    // let mut linear_parts = vec![];
    // let mut constant_parts = vec![];
    // for (c, _) in constraints.into_iter() {
    //     let (q, l, c) = c.split_max_quadratic();
    //     quadratic_parts.push(q);
    //     linear_parts.push(l);
    //     constant_parts.push(c);
    // }
    // let quadratic_node = QuadraticConstraintsPartNode {
    //     parts: quadratic_parts,
    // };
    // graph.add_node(quadratic_node.clone());

    // let final_node = ConstraintsCollapseNode {
    //     predicate,
    //     linear_parts,
    //     constant_parts,
    //     quadratic_gate: quadratic_node,
    // };
    // graph.add_node(final_node.clone());

    // final_node
}

// pub(crate) fn layout_constraints_on_single_layer<F: PrimeField>(
//     graph: &mut GKRGraph,
//     constraints: Vec<(Constraint<F>, bool)>,
// ) -> NaiveConstraintsEvaluationNode<F> {
//     let mut quadratic_parts = vec![];
//     let mut linear_parts = vec![];
//     let mut constant_parts = vec![];
//     for (c, _) in constraints.into_iter() {
//         let (q, l, c) = c.split_max_quadratic();
//         quadratic_parts.push(q);
//         linear_parts.push(l);
//         constant_parts.push(c);
//     }
//     let quadratic_node = QuadraticConstraintsPartNode {
//         parts: quadratic_parts,
//     };
//     graph.add_node(quadratic_node.clone());

//     let final_node = NaiveConstraintsEvaluationNode {
//         linear_parts,
//         constant_parts,
//         quadratic_gate: quadratic_node,
//     };
//     graph.add_node(final_node.clone());

//     final_node
// }

// #[derive(Clone, Debug, PartialEq, Eq)]
// pub struct NaiveConstraintsEvaluationNode<F: PrimeField> {
//     pub quadratic_gate: QuadraticConstraintsPartNode<F>,
//     pub linear_parts: Vec<Vec<(F, Variable)>>,
//     pub constant_parts: Vec<F>,
// }

// impl<F: PrimeField> DependentNode for NaiveConstraintsEvaluationNode<F> {
//     fn add_dependencies_into(
//         &self,
//         graph: &mut dyn graph::GraphHolder,
//         dst: &mut Vec<graph::NodeIndex>,
//     ) {
//         assert_eq!(self.quadratic_gate.parts.len(), self.linear_parts.len());
//         assert_eq!(self.quadratic_gate.parts.len(), self.constant_parts.len());
//         DependentNode::add_dependencies_into(&self.quadratic_gate, graph, dst);
//         for c in self.linear_parts.iter() {
//             for (_, a) in c.iter() {
//                 let a = graph.get_node_index_for_variable(*a);
//                 dst.push(a);
//             }
//         }
//     }
// }

// impl<F: PrimeField> GKRGate for NaiveConstraintsEvaluationNode<F> {
//     type Output = ();

//     fn short_name(&self) -> String {
//         format!("Constraint evaluation node of {} constraints", self.quadratic_gate.parts.len())
//     }

//     fn add_at_layer(&self, graph: &mut impl GraphHolder, output_layer: usize) -> Self::Output {
//         assert_eq!(output_layer, 1);

//         // compute stats
//         let mut cross_terms_for_vars = HashMap::<Variable, HashSet<(F, Variable)>>::new();
//         for c in self.quadratic_gate.parts.iter() {
//             for (c, a, b) in c.iter() {
//                 if *a != *b {
//                     let p = cross_terms_for_vars.entry(*a).or_default().insert((*c, *b));
//                     assert!(p);
//                     let p = cross_terms_for_vars.entry(*b).or_default().insert((*c, *a));
//                     assert!(p);
//                 } else {
//                     let p = cross_terms_for_vars.entry(*a).or_default().insert((*c, *b));
//                     assert!(p);
//                 }
//             }
//         }

//         // we want to reduce number of multiplications
//         let mut selected_terms = vec![];
//         loop {
//             if cross_terms_for_vars.is_empty() {
//                 break;
//             }
//             let (next_best_candidate, _) = cross_terms_for_vars
//                 .iter()
//                 .map(|(k, v)| (*k, v.len()))
//                 .max_by(|a, b| a.1.cmp(&b.1))
//                 .unwrap();
//             let cross_terms = cross_terms_for_vars.remove(&next_best_candidate).unwrap();
//             // cleanup
//             for (c, other) in cross_terms.iter() {
//                 if *other != next_best_candidate {
//                     let exists = cross_terms_for_vars
//                         .get_mut(other)
//                         .unwrap()
//                         .remove(&(*c, next_best_candidate));
//                     assert!(exists);
//                     if cross_terms_for_vars.get(other).unwrap().is_empty() {
//                         cross_terms_for_vars.remove(other);
//                     }
//                 }
//             }
//             // we do not care yet about stable sort
//             let mut terms = vec![];
//             for (c, other) in cross_terms.iter() {
//                 let place = graph.get_address_for_variable(*other);
//                 terms.push((c.as_u32_reduced(), place));
//             }
//             terms.sort_by(|a, b| a.1.cmp(&b.1));
//             let next_best_candidate = graph.get_address_for_variable(next_best_candidate);
//             selected_terms.push((next_best_candidate, terms.into_boxed_slice()));
//         }

//         let linear_terms = self.linear_parts.iter().map(|els| {
//             let mut inner = vec![];
//             for (c, v) in els.iter() {
//                 let c = c.as_u32_reduced();
//                 let pos = graph.get_address_for_variable(*v);
//                 inner.push((c, pos));
//             }
//             inner.into_boxed_slice()
//         }).collect::<Vec<_>>().into_boxed_slice();

//         let constants = self.constant_parts.iter().map(|c| {
//             c.as_u32_reduced()
//         }).collect::<Vec<_>>().into_boxed_slice();

//         let input = NoFieldMaxQuadraticGKRRelation {
//             quadratic_terms: selected_terms.into_boxed_slice(),
//             linear_terms,
//             constants
//         };

//         let node = NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { input };
//         graph.add_enforced_relation(node, output_layer);

//         ()
//     }
// }

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OneStepConstraintsEvaluationNode<F: PrimeField> {
    pub quadratic_parts: Vec<Vec<(F, Variable, Variable)>>,
    pub linear_parts: Vec<Vec<(F, Variable)>>,
    pub constant_parts: Vec<F>,
}

pub(crate) fn layout_constraints_at_layers<F: PrimeField>(
    graph: &mut GKRGraph,
    constraints: Vec<(Constraint<F>, bool)>,
    layers_mapping: &HashMap<Variable, usize>,
) -> (Vec<Degree2Constraint<F>>, Vec<Degree1Constraint<F>>) {
    // sort constraints by layers
    let mut layers = BTreeMap::new();
    let mut compiled_quadratic = vec![];
    let mut compiled_linear = vec![];

    for (c, _) in constraints.into_iter() {
        let all_vars = c.stable_variable_set();
        let mut layer = None;
        for var in all_vars.into_iter() {
            let var_layer = *layers_mapping.get(&var).expect("must be known");
            if let Some(layer) = layer {
                assert_eq!(layer, var_layer);
            } else {
                layer = Some(var_layer);
            }
        }
        let layer = layer.expect("placement layer");
        layers.entry(layer).or_insert(vec![]).push(c);
    }

    for (input_layer, constraints) in layers.into_iter() {
        let mut quadratic_parts = vec![];
        let mut linear_parts = vec![];
        let mut constant_parts = vec![];

        for c in constraints.into_iter() {
            let (q, l, c) = c.split_max_quadratic();

            if q.is_empty() {
                assert!(l.is_empty() == false);
                let compiled = Degree1Constraint {
                    linear_terms: l.clone().into_boxed_slice(),
                    constant_term: c,
                };
                compiled_linear.push(compiled);
            } else {
                let compiled = Degree2Constraint {
                    quadratic_terms: q.clone().into_boxed_slice(),
                    linear_terms: l.clone().into_boxed_slice(),
                    constant_term: c,
                };
                compiled_quadratic.push(compiled);
            }

            quadratic_parts.push(q);
            linear_parts.push(l);
            constant_parts.push(c);
        }

        assert_eq!(quadratic_parts.len(), linear_parts.len());
        assert_eq!(quadratic_parts.len(), constant_parts.len());

        let node = OneStepConstraintsEvaluationNode {
            quadratic_parts,
            linear_parts,
            constant_parts,
        };

        node.add_at_layer(graph, input_layer + 1);
    }

    (compiled_quadratic, compiled_linear)
}

impl<F: PrimeField> GKRGate for OneStepConstraintsEvaluationNode<F> {
    type Output = ();

    fn short_name(&self) -> String {
        format!(
            "Constraint evaluation node of {} constraints",
            self.quadratic_parts.len()
        )
    }

    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation) {
        assert_eq!(self.quadratic_parts.len(), self.linear_parts.len());
        assert_eq!(self.quadratic_parts.len(), self.constant_parts.len());

        let mut quadratic_sorted = BTreeMap::new();
        let mut linear_sorted = BTreeMap::new();
        let mut constant_sorted = vec![];

        for (i, ((q, l), c)) in self
            .quadratic_parts
            .iter()
            .zip(self.linear_parts.iter())
            .zip(self.constant_parts.iter())
            .enumerate()
        {
            for (coeff, a, b) in q.iter() {
                let a = graph.get_address_for_variable(*a);
                let b = graph.get_address_for_variable(*b);
                a.assert_as_layer(output_layer - 1);
                b.assert_as_layer(output_layer - 1);
                quadratic_sorted
                    .entry((a, b))
                    .or_insert(vec![])
                    .push((coeff.as_u32_reduced(), i));
            }
            for (coeff, a) in l.iter() {
                let a = graph.get_address_for_variable(*a);
                a.assert_as_layer(output_layer - 1);
                linear_sorted
                    .entry(a)
                    .or_insert(vec![])
                    .push((coeff.as_u32_reduced(), i));
            }
            if c.is_zero() == false {
                constant_sorted.push((c.as_u32_reduced(), i));
            }
        }

        let quadratic_terms = quadratic_sorted
            .into_iter()
            .map(|(k, v)| (k, v.into_boxed_slice()))
            .collect::<Vec<_>>()
            .into_boxed_slice();

        let linear_terms = linear_sorted
            .into_iter()
            .map(|(k, v)| (k, v.into_boxed_slice()))
            .collect::<Vec<_>>()
            .into_boxed_slice();

        let constants = constant_sorted.into_boxed_slice();

        let input = NoFieldMaxQuadraticConstraintsGKRRelation {
            quadratic_terms,
            linear_terms,
            constants,
        };

        let node = NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { input };
        graph.add_enforced_relation(node.clone(), output_layer);

        ((), node)
    }
}

// #[derive(Clone, Debug, PartialEq, Eq)]
// pub struct NaiveConstraintsEvaluationNode<F: PrimeField> {
//     pub quadratic_gate: QuadraticConstraintsPartNode<F>,
//     pub linear_parts: Vec<Vec<(F, Variable)>>,
//     pub constant_parts: Vec<F>,
// }

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct GKRCompiledLinearConstraint<F: PrimeField> {
    pub terms: Vec<(F, GKRAddress)>,
    pub constant: F,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct GKRCompiledQuadraticConstraint<F: PrimeField> {
    pub quadratic_terms: Vec<(GKRCompiledLinearConstraint<F>, GKRAddress)>,
    pub linear_terms: Vec<(F, GKRAddress)>,
    pub constant: F,
    pub unique_addresses: BTreeSet<GKRAddress>, // so we know all unique polys to claim about
}
