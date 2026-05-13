use cs::definitions::GKRAddress;
use cs::gkr_compiler::{GKRCircuitArtifact, NoFieldGKRRelation, NoFieldMaxQuadraticGKRRelation};
use field::PrimeField;
use std::collections::BTreeMap;

pub(crate) fn normalize_compiled_circuit_for_gpu<F: PrimeField>(
    mut compiled_circuit: GKRCircuitArtifact<F>,
) -> GKRCircuitArtifact<F> {
    // Make scratch a first-class trace-aligned class: rewrite every
    // scratch-mapped `InnerLayer` address that survives in
    // constraint/value-producing relations into its `ScratchSpace` alias.
    // cs/ already does this for lookup relations
    // (`family_circuit.rs:scratch_space_mapping` rewrite); we mirror the same
    // substitution here for the relations cs/ leaves untouched
    // (`MaxQuadratic`, `EnforceSingleMaxQuadraticConstraint`,
    // `EnforceConstraintsMaxQuadratic`). After this pass, no scratch-backed
    // value is referenced via its `InnerLayer` address; downstream forward /
    // backward / storage-layout code can treat scratch addresses uniformly
    // with witness/memory.
    let scratch_space_mapping = compiled_circuit.scratch_space_mapping.clone();
    if !scratch_space_mapping.is_empty() {
        for layer in compiled_circuit.layers.iter_mut() {
            for gate in layer
                .gates
                .iter_mut()
                .chain(layer.gates_with_external_connections.iter_mut())
            {
                rewrite_relation_scratch_addresses(
                    &mut gate.enforced_relation,
                    &scratch_space_mapping,
                );
            }
        }
    }
    compiled_circuit
}

fn rewrite_addr(addr: &mut GKRAddress, mapping: &BTreeMap<GKRAddress, usize>) {
    if let Some(scratch_idx) = mapping.get(addr).copied() {
        *addr = GKRAddress::ScratchSpace(scratch_idx);
    }
}

fn rewrite_max_quadratic(
    rel: &mut NoFieldMaxQuadraticGKRRelation,
    mapping: &BTreeMap<GKRAddress, usize>,
) {
    let mut rewritten_quadratic: Vec<(GKRAddress, Box<[(u32, GKRAddress)]>)> =
        Vec::with_capacity(rel.quadratic_terms.len());
    for (lhs, rhs_terms) in rel.quadratic_terms.iter() {
        let mut new_lhs = *lhs;
        rewrite_addr(&mut new_lhs, mapping);
        let mut new_rhs_terms: Vec<(u32, GKRAddress)> = Vec::with_capacity(rhs_terms.len());
        for (coeff, rhs) in rhs_terms.iter() {
            let mut new_rhs = *rhs;
            rewrite_addr(&mut new_rhs, mapping);
            new_rhs_terms.push((*coeff, new_rhs));
        }
        rewritten_quadratic.push((new_lhs, new_rhs_terms.into_boxed_slice()));
    }
    rel.quadratic_terms = rewritten_quadratic.into_boxed_slice();

    let mut rewritten_linear: Vec<(u32, GKRAddress)> = Vec::with_capacity(rel.linear_terms.len());
    for (coeff, addr) in rel.linear_terms.iter() {
        let mut new_addr = *addr;
        rewrite_addr(&mut new_addr, mapping);
        rewritten_linear.push((*coeff, new_addr));
    }
    rel.linear_terms = rewritten_linear.into_boxed_slice();
}

fn rewrite_relation_scratch_addresses(
    rel: &mut NoFieldGKRRelation,
    mapping: &BTreeMap<GKRAddress, usize>,
) {
    use NoFieldGKRRelation::*;
    match rel {
        MaxQuadratic { input, output } => {
            rewrite_max_quadratic(input, mapping);
            rewrite_addr(output, mapping);
        }
        EnforceSingleMaxQuadraticConstraint { input } => {
            rewrite_max_quadratic(input, mapping);
        }
        EnforceConstraintsMaxQuadratic { input } => {
            let mut rewritten_quadratic: Vec<((GKRAddress, GKRAddress), Box<[(u32, usize)]>)> =
                Vec::with_capacity(input.quadratic_terms.len());
            for ((a, b), coeffs) in input.quadratic_terms.iter() {
                let mut new_a = *a;
                let mut new_b = *b;
                rewrite_addr(&mut new_a, mapping);
                rewrite_addr(&mut new_b, mapping);
                rewritten_quadratic.push(((new_a, new_b), coeffs.clone()));
            }
            input.quadratic_terms = rewritten_quadratic.into_boxed_slice();
            let mut rewritten_linear: Vec<(GKRAddress, Box<[(u32, usize)]>)> =
                Vec::with_capacity(input.linear_terms.len());
            for (addr, coeffs) in input.linear_terms.iter() {
                let mut new_addr = *addr;
                rewrite_addr(&mut new_addr, mapping);
                rewritten_linear.push((new_addr, coeffs.clone()));
            }
            input.linear_terms = rewritten_linear.into_boxed_slice();
        }
        CopyInBaseField { input, output } => {
            rewrite_addr(input, mapping);
            rewrite_addr(output, mapping);
        }
        // `ScratchSpace` is base-field-only; rewriting `CopyInExtensionField`
        // inputs/outputs to `ScratchSpace` would mis-type the kernel
        // (forward writes the value as base, but the ExtCopy kernel reads it
        // as ext) and panic in `get_for_sumcheck_round_0`'s extension lookup.
        // cs/'s scratch-mapping rewrite (`delegation_circuit.rs:580-604`)
        // only touches lookup-style relations where the operand is base by
        // construction, so the GPU normalize pass mirrors that constraint
        // here: only base-side relations get the substitution.
        CopyInExtensionField { .. } => {}
        // Other relations either have their scratch references already
        // rewritten by cs/ (lookups) or are not expected to reference
        // scratch-backed values today. If a future relation does, add it
        // here alongside the constraint variants above.
        _ => {}
    }
}
