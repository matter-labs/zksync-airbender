use super::{read_cell, write_cell};
use crate::gkr::witness_gen::family_circuits::GKRFullWitnessTrace;
use cs::definitions::GKRAddress;
use cs::gkr_compiler::{CompiledMaxQuadraticGKRRelation, GKRCircuitArtifact, GKRRelation};
use field::baby_bear::base::BabyBearField;
use field::Field;
use std::alloc::Global;
use std::collections::BTreeSet;

pub(super) type F = BabyBearField;
pub(super) type Trace = GKRFullWitnessTrace<F, Global, Global>;
pub(super) type Relation = CompiledMaxQuadraticGKRRelation<F>;

pub(super) fn lowered_constraints(circuit: &GKRCircuitArtifact<F>) -> Vec<&Relation> {
    let constraints: Vec<&Relation> = circuit
        .layers
        .iter()
        .flat_map(|layer| {
            layer
                .gates_with_external_connections
                .iter()
                .chain(layer.gates.iter())
        })
        .filter_map(|gate| match &gate.enforced_relation {
            GKRRelation::EnforceSingleMaxQuadraticConstraint { input, .. } => Some(input),
            _ => None,
        })
        .collect();
    assert_eq!(
        constraints.len(),
        circuit.degree_1_constraints.len() + circuit.degree_2_constraints.len()
    );
    constraints
}

pub(super) fn inputs(relation: &Relation) -> BTreeSet<GKRAddress> {
    relation
        .quadratic_terms
        .iter()
        .flat_map(|(a, terms)| std::iter::once(*a).chain(terms.iter().map(|(_, b)| *b)))
        .chain(relation.linear_terms.iter().map(|(_, a)| *a))
        .collect()
}

fn evaluate(relation: &Relation, trace: &Trace, row: usize) -> F {
    let mut result = relation.constant;
    for (a, terms) in relation.quadratic_terms.iter() {
        let mut inner = F::ZERO;
        for (coefficient, b) in terms.iter() {
            let mut term = *coefficient;
            term.mul_assign(&read_cell(trace, *b, row));
            inner.add_assign(&term);
        }
        inner.mul_assign(&read_cell(trace, *a, row));
        result.add_assign(&inner);
    }
    for (coefficient, a) in relation.linear_terms.iter() {
        let mut term = *coefficient;
        term.mul_assign(&read_cell(trace, *a, row));
        result.add_assign(&term);
    }
    result
}

pub(super) fn failing(
    constraints: &[&Relation],
    trace: &Trace,
    row: usize,
) -> Vec<BTreeSet<GKRAddress>> {
    constraints
        .iter()
        .filter(|relation| evaluate(relation, trace, row) != F::ZERO)
        .map(|relation| inputs(relation))
        .collect()
}

pub(super) fn tampered_failures(
    constraints: &[&Relation],
    trace: &mut Trace,
    row: usize,
    tampered: &[(GKRAddress, F)],
) -> Vec<BTreeSet<GKRAddress>> {
    let honest: Vec<F> = tampered
        .iter()
        .map(|(address, _)| read_cell(trace, *address, row))
        .collect();
    for (address, value) in tampered {
        write_cell(trace, *address, row, *value);
    }
    let result = failing(constraints, trace, row);
    for ((address, _), value) in tampered.iter().zip(honest) {
        write_cell(trace, *address, row, value);
    }
    result
}
