use crate::upstream::{
    GKRAddress, GKRCircuitArtifact, NoFieldGKRRelation, NoFieldLinearRelation,
    NoFieldMaxQuadraticGKRRelation, NoFieldVectorLookupRelation, PrimeField,
};
use std::collections::BTreeMap;

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

fn rewrite_linear_relation(rel: &mut NoFieldLinearRelation, mapping: &BTreeMap<GKRAddress, usize>) {
    let mut rewritten: Vec<(u32, GKRAddress)> = Vec::with_capacity(rel.linear_terms.len());
    for (coeff, addr) in rel.linear_terms.iter() {
        let mut new_addr = *addr;
        rewrite_addr(&mut new_addr, mapping);
        rewritten.push((*coeff, new_addr));
    }
    rel.linear_terms = rewritten.into_boxed_slice();
}

fn rewrite_vector_lookup(
    rel: &mut NoFieldVectorLookupRelation,
    mapping: &BTreeMap<GKRAddress, usize>,
) {
    for col in rel.columns.iter_mut() {
        rewrite_linear_relation(col, mapping);
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
        // Lookup relations whose `input` / `remainder` fields carry inline
        // `NoFieldLinearRelation` or `NoFieldVectorLookupRelation` expressions
        // (not pre-materialized GKRAddresses). cs/'s scratch-mapping rewrite
        // only touches the top-level standalone lookup expression lists
        // (`range_check_16_lookups_compiled`, `timestamp_range_check_lookups_compiled`,
        // `generic_lookups_compiled`) in `family_circuit.rs`; it does NOT
        // rewrite linear terms embedded in these layer-gate relations. Without
        // this rewrite a scratch-backed address left unrewritten in a
        // `linear_terms` entry causes a missing-slot panic in
        // `register_flat_base_folding_for_layer`.
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
        // `1/(a+gamma) + 1/(b+gamma)` where `a, b` are base-field values that
        // may be materialized into scratch. cs/'s scratch-mapping rewrite only
        // touches range-check-16 / timestamp / generic lookup `input` linear
        // terms; it leaves the materialized addresses here unchanged. Without
        // this rewrite the writers are rewritten to `ScratchSpace` so the
        // layout drops the `InnerLayer` slots while the still-`InnerLayer`
        // reads panic in `register_flat_base_folding_for_layer`'s layout
        // lookup. `output` (extension results) is never scratch-mapped.
        LookupPairFromMaterializedBaseInputs { input, .. } => {
            for addr in input.iter_mut() {
                rewrite_addr(addr, mapping);
            }
        }
        // `a/b + 1/(c + gamma)` where `c` (the `remainder`) is a *base-field*
        // value that may be materialized into scratch. cs/'s scratch-mapping
        // rewrite only touches the range-check-16 / timestamp / generic
        // lookup `input` linear terms (`family_circuit.rs:1018-1042`); it
        // leaves this relation's `remainder` as its `InnerLayer` address. The
        // unified circuit is the first to exercise a scratch-backed `remainder`
        // here — without this rewrite, the writer (the `MaxQuadratic` that
        // produces `c`) is rewritten to `ScratchSpace` so the layout drops the
        // `InnerLayer` slot, while this still-`InnerLayer` read panics in
        // `register_flat_base_folding_for_layer`'s layout lookup. `input` (the
        // extension `a/b` pair) and `output` (extension results) are never
        // scratch-mapped (scratch is base-only), so only `remainder` is
        // rewritten — mirroring cs/'s base-read-only substitution.
        LookupUnbalancedPairWithMaterializedBaseInputs { remainder, .. } => {
            rewrite_addr(remainder, mapping);
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
