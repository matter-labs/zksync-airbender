//! Circuit-layer evaluations in the group order consumed by the F1 encoder.
use crate::seed::{Circuit, Proof};
use field::{Field, Proth120};

/// One standard layer's at-point evals in group-offset order (gaps zero-filled), as the
/// calldata carries them.
pub(crate) fn circuit_layer_evals(
    circuit: &Circuit,
    proof: &Proof,
    config_idx: usize,
) -> Vec<Proth120> {
    use cs::definitions::GKRAddress;
    let num_mem = circuit.memory_layout.total_width;
    let num_wit = circuit.witness_layout.total_width;
    let siv = &proof.sumcheck_intermediate_values[&config_idx];
    let group_idx = |addr: &GKRAddress| -> Option<usize> {
        match addr {
            GKRAddress::InnerLayer { layer, offset } if *layer == config_idx && config_idx > 0 => {
                Some(*offset)
            }
            GKRAddress::BaseLayerMemory(o) if config_idx == 0 => Some(*o),
            GKRAddress::BaseLayerWitness(o) if config_idx == 0 => Some(num_mem + *o),
            GKRAddress::Setup(o) if config_idx == 0 => Some(num_mem + num_wit + *o),
            _ => None, // Cached / VirtualSetup: computed on heap, not in calldata
        }
    };
    let mut by_idx: std::collections::BTreeMap<usize, Proth120> = Default::default();
    for (addr, val) in siv.final_step_evaluations.iter() {
        if let Some(idx) = group_idx(addr) {
            by_idx.insert(idx, val[0]);
        }
    }
    for (addr, val) in siv.extra_evaluations_from_caching_relations.iter() {
        if let Some(idx) = group_idx(addr) {
            by_idx.insert(idx, *val);
        }
    }
    let n = by_idx.keys().max().map(|m| m + 1).unwrap_or(0);
    (0..n)
        .map(|i| by_idx.get(&i).copied().unwrap_or(Proth120::ZERO))
        .collect()
}
