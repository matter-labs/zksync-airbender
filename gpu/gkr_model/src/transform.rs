use crate::upstream::{
    CompiledMaxQuadraticGKRRelation, GKRAddress, GKRCircuitArtifact, GKRRelation, LinearRelation,
    PrimeField, VectorLookupRelation,
};
use std::collections::BTreeMap;

/// Element type of `CompiledMaxQuadraticGKRRelation::quadratic_terms`.
type MaxQuadraticTerm<F> = (GKRAddress, Box<[(F, GKRAddress)]>);
/// Element type of `MaxQuadraticConstraintsGKRRelation::quadratic_terms`.
type ConstraintsQuadraticTerm<F> = ((GKRAddress, GKRAddress), Box<[(F, usize)]>);
/// Element type of `MaxQuadraticConstraintsGKRRelation::linear_terms`.
type ConstraintsLinearTerm<F> = (GKRAddress, Box<[(F, usize)]>);

pub fn normalize_compiled_circuit_for_gpu<F: PrimeField>(
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

/// Inverse of the scratch-storage rewrite, for protocol/claim identity only.
///
/// `normalize_compiled_circuit_for_gpu` rewrites scratch-backed `InnerLayer`
/// values to their `ScratchSpace` storage alias so the storage layout and the
/// forward / backward execution kernels can treat them uniformly with
/// witness/memory (the "reindex to a proper pointer" the GPU needs for
/// execution). That alias is *storage*, not identity: the GKR transcript commit
/// order, the proof `final_step_eval_addresses`, and the per-layer claim layout
/// are protocol-visible and MUST match the CPU verifier, which keeps the logical
/// `InnerLayer` identity everywhere in the layer graph (cs/'s
/// `family_circuit.rs` substitutes scratch only into lookup-relation *reads*,
/// never into producing gates, claims, or the transcript).
///
/// This maps a (possibly scratch-aliased) storage address back to that logical
/// `InnerLayer` identity via `scratch_space_mapping_rev`. It is a no-op for any
/// address that is not a scratch alias, so it is safe to apply uniformly at the
/// protocol/claim boundary; circuits without scratch-backed claimed values are
/// unaffected.
pub fn logical_protocol_address(
    addr: GKRAddress,
    scratch_space_mapping_rev: &BTreeMap<usize, GKRAddress>,
) -> GKRAddress {
    if let GKRAddress::ScratchSpace(scratch_idx) = addr {
        if let Some(&logical) = scratch_space_mapping_rev.get(&scratch_idx) {
            return logical;
        }
    }
    addr
}

fn rewrite_linear_relation<F: PrimeField>(
    rel: &mut LinearRelation<F>,
    mapping: &BTreeMap<GKRAddress, usize>,
) {
    let mut rewritten: Vec<(F, GKRAddress)> = Vec::with_capacity(rel.linear_terms.len());
    for (coeff, addr) in rel.linear_terms.iter() {
        let mut new_addr = *addr;
        rewrite_addr(&mut new_addr, mapping);
        rewritten.push((*coeff, new_addr));
    }
    rel.linear_terms = rewritten.into_boxed_slice();
}

fn rewrite_vector_lookup<F: PrimeField>(
    rel: &mut VectorLookupRelation<F>,
    mapping: &BTreeMap<GKRAddress, usize>,
) {
    for col in rel.columns.iter_mut() {
        rewrite_linear_relation(col, mapping);
    }
}

fn rewrite_max_quadratic<F: PrimeField>(
    rel: &mut CompiledMaxQuadraticGKRRelation<F>,
    mapping: &BTreeMap<GKRAddress, usize>,
) {
    let mut rewritten_quadratic: Vec<MaxQuadraticTerm<F>> =
        Vec::with_capacity(rel.quadratic_terms.len());
    for (lhs, rhs_terms) in rel.quadratic_terms.iter() {
        let mut new_lhs = *lhs;
        rewrite_addr(&mut new_lhs, mapping);
        let mut new_rhs_terms: Vec<(F, GKRAddress)> = Vec::with_capacity(rhs_terms.len());
        for (coeff, rhs) in rhs_terms.iter() {
            let mut new_rhs = *rhs;
            rewrite_addr(&mut new_rhs, mapping);
            new_rhs_terms.push((*coeff, new_rhs));
        }
        rewritten_quadratic.push((new_lhs, new_rhs_terms.into_boxed_slice()));
    }
    rel.quadratic_terms = rewritten_quadratic.into_boxed_slice();

    let mut rewritten_linear: Vec<(F, GKRAddress)> = Vec::with_capacity(rel.linear_terms.len());
    for (coeff, addr) in rel.linear_terms.iter() {
        let mut new_addr = *addr;
        rewrite_addr(&mut new_addr, mapping);
        rewritten_linear.push((*coeff, new_addr));
    }
    rel.linear_terms = rewritten_linear.into_boxed_slice();
}

fn rewrite_relation_scratch_addresses<F: PrimeField>(
    rel: &mut GKRRelation<F>,
    mapping: &BTreeMap<GKRAddress, usize>,
) {
    use GKRRelation::*;
    match rel {
        MaxQuadratic { input, output, .. } => {
            rewrite_max_quadratic(input, mapping);
            rewrite_addr(output, mapping);
        }
        EnforceSingleMaxQuadraticConstraint { input, .. } => {
            rewrite_max_quadratic(input, mapping);
        }
        EnforceConstraintsMaxQuadratic { input } => {
            let mut rewritten_quadratic: Vec<ConstraintsQuadraticTerm<F>> =
                Vec::with_capacity(input.quadratic_terms.len());
            for ((a, b), coeffs) in input.quadratic_terms.iter() {
                let mut new_a = *a;
                let mut new_b = *b;
                rewrite_addr(&mut new_a, mapping);
                rewrite_addr(&mut new_b, mapping);
                rewritten_quadratic.push(((new_a, new_b), coeffs.clone()));
            }
            input.quadratic_terms = rewritten_quadratic.into_boxed_slice();
            let mut rewritten_linear: Vec<ConstraintsLinearTerm<F>> =
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
        // Relation-local base inputs are not covered by cs's top-level lookup rewrite.
        LookupPairFromBaseInputs { input, .. } => {
            for single in input.iter_mut() {
                rewrite_linear_relation(&mut single.input, mapping);
            }
        }
        LookupPairFromVectorInputs { input, .. } => {
            for vec_rel in input.iter_mut() {
                rewrite_vector_lookup(vec_rel, mapping);
            }
        }
        LookupFromVectorInputWithSetup { input, .. } => {
            rewrite_vector_lookup(input, mapping);
        }
        LookupUnbalancedPairWithVectorInputs { remainder, .. } => {
            rewrite_vector_lookup(remainder, mapping);
        }
        LookupPairFromMaterializedBaseInputs { input, .. } => {
            for addr in input.iter_mut() {
                rewrite_addr(addr, mapping);
            }
        }
        // Only the base-field remainder may be scratch-mapped.
        LookupUnbalancedPairWithMaterializedBaseInputs { remainder, .. } => {
            rewrite_addr(remainder, mapping);
        }
        // ScratchSpace is base-field-only.
        CopyInExtensionField { .. } => {}
        _ => {}
    }
}
