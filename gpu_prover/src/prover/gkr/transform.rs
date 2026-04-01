use cs::gkr_compiler::{
    GKRCircuitArtifact, GKRLayerDescription, NoFieldGKRCacheRelation, NoFieldGKRRelation,
};
use field::PrimeField;

use cs::definitions::GKRAddress;

pub(crate) fn normalize_compiled_circuit_for_gpu<F: PrimeField>(
    mut compiled_circuit: GKRCircuitArtifact<F>,
) -> GKRCircuitArtifact<F> {
    for layer in compiled_circuit.layers.iter_mut() {
        normalize_layer_for_gpu(layer);
    }
    compiled_circuit
}

pub(crate) fn normalize_layer_for_gpu(layer: &mut GKRLayerDescription) {
    let cache_layer = layer
        .layer
        .checked_sub(1)
        .expect("GKR layers start at 1 and cache into the previous layer");
    let mut next_cached_offset = layer
        .cached_relations
        .keys()
        .filter_map(|address| match address {
            GKRAddress::Cached { layer, offset } if *layer == cache_layer => Some(*offset + 1),
            _ => None,
        })
        .max()
        .unwrap_or(0);

    normalize_gate_list_for_gpu(
        &mut layer.gates,
        cache_layer,
        &mut layer.cached_relations,
        &mut next_cached_offset,
    );
    normalize_gate_list_for_gpu(
        &mut layer.gates_with_external_connections,
        cache_layer,
        &mut layer.cached_relations,
        &mut next_cached_offset,
    );
}

fn normalize_gate_list_for_gpu(
    gates: &mut [cs::gkr_compiler::GateArtifacts],
    cache_layer: usize,
    cached_relations: &mut std::collections::BTreeMap<GKRAddress, NoFieldGKRCacheRelation>,
    next_cached_offset: &mut usize,
) {
    for gate in gates.iter_mut() {
        let relation = gate.enforced_relation.clone();
        if let NoFieldGKRRelation::MaterializedVectorLookupInput { input, output } = relation {
            let cached_input = find_or_insert_vectorized_lookup_cache(
                cache_layer,
                input,
                cached_relations,
                next_cached_offset,
            );
            gate.enforced_relation = NoFieldGKRRelation::Copy {
                input: cached_input,
                output,
            };
        }
    }
}

fn find_or_insert_vectorized_lookup_cache(
    cache_layer: usize,
    input: cs::definitions::gkr::NoFieldVectorLookupRelation,
    cached_relations: &mut std::collections::BTreeMap<GKRAddress, NoFieldGKRCacheRelation>,
    next_cached_offset: &mut usize,
) -> GKRAddress {
    if let Some(existing) = cached_relations
        .iter()
        .find_map(|(address, relation)| match relation {
            NoFieldGKRCacheRelation::VectorizedLookup(existing) if existing == &input => {
                Some(*address)
            }
            _ => None,
        })
    {
        return existing;
    }

    let address = GKRAddress::Cached {
        layer: cache_layer,
        offset: *next_cached_offset,
    };
    *next_cached_offset += 1;
    let previous =
        cached_relations.insert(address, NoFieldGKRCacheRelation::VectorizedLookup(input));
    assert!(
        previous.is_none(),
        "fresh cached relation address must be unique"
    );
    address
}
