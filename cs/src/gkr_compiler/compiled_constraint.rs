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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OneStepConstraintsEvaluationNode<F: PrimeField> {
    pub quadratic_parts: Vec<Vec<(F, Variable, Variable)>>,
    pub linear_parts: Vec<Vec<(F, Variable)>>,
    pub constant_parts: Vec<F>,
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

pub(crate) fn layout_constraints_at_layers<F: PrimeField, const USE_BATCHING: bool>(
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

    if USE_BATCHING {
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
    } else {
        for (input_layer, constraints) in layers.into_iter() {
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

                let node = SingleConstraintEvaluationNode {
                    quadratic_part: q,
                    linear_part: l,
                    constant_part: c,
                };

                node.add_at_layer(graph, input_layer + 1);
            }
        }
    }

    (compiled_quadratic, compiled_linear)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SingleConstraintEvaluationNode<F: PrimeField> {
    pub quadratic_part: Vec<(F, Variable, Variable)>,
    pub linear_part: Vec<(F, Variable)>,
    pub constant_part: F,
}

impl<F: PrimeField> GKRGate for SingleConstraintEvaluationNode<F> {
    type Output = ();

    fn short_name(&self) -> String {
        format!("Constraint evaluation node",)
    }

    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation) {
        let mut quadratic_sorted = BTreeMap::<GKRAddress, BTreeMap<_, _>>::new();
        let mut linear_sorted = BTreeMap::new();

        for (coeff, a, b) in self.quadratic_part.iter() {
            let a = graph.get_address_for_variable(*a);
            let b = graph.get_address_for_variable(*b);
            a.assert_as_layer(output_layer - 1);
            b.assert_as_layer(output_layer - 1);
            if a <= b {
                assert!(quadratic_sorted
                    .entry(a)
                    .or_default()
                    .insert(b, coeff.as_u32_reduced())
                    .is_none());
            } else {
                assert!(quadratic_sorted
                    .entry(b)
                    .or_default()
                    .insert(a, coeff.as_u32_reduced())
                    .is_none());
            }
        }
        for (coeff, a) in self.linear_part.iter() {
            let a = graph.get_address_for_variable(*a);
            a.assert_as_layer(output_layer - 1);
            assert!(linear_sorted.insert(a, coeff.as_u32_reduced()).is_none());
        }

        let quadratic_terms = quadratic_sorted
            .into_iter()
            .map(|(k, v)| {
                (
                    k,
                    v.into_iter()
                        .map(|(k, v)| (v, k))
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                )
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();

        let linear_terms = linear_sorted
            .into_iter()
            .map(|(k, v)| (v, k))
            .collect::<Vec<_>>()
            .into_boxed_slice();

        let input = NoFieldMaxQuadraticGKRRelation {
            quadratic_terms,
            linear_terms,
            constant: self.constant_part.as_u32_reduced(),
        };

        let node = NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input };
        graph.add_enforced_relation(node.clone(), output_layer);

        ((), node)
    }
}
