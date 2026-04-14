use cs::gkr_compiler::{GKRCircuitArtifact, GKRLayerDescription};
use field::PrimeField;

pub(crate) fn normalize_compiled_circuit_for_gpu<F: PrimeField>(
    compiled_circuit: GKRCircuitArtifact<F>,
) -> GKRCircuitArtifact<F> {
    // GPU execution now consumes cached layouts directly instead of rewriting
    // them into synthetic helper relations.
    compiled_circuit
}

pub(crate) fn normalize_layer_for_gpu(_layer: &mut GKRLayerDescription) {}
