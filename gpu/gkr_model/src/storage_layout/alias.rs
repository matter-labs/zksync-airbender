//! Union-find over `CopyInBaseField` / `CopyInExtensionField` gates: builds
//! the alias -> canonical redirect map consulted by
//! [`super::types::GpuGKRStorageLayout::lookup`], and validates that every
//! alias resolves to a canonical address with a real layout entry.

use std::collections::BTreeMap;

use crate::upstream::{GKRAddress, GKRCircuitArtifact, NoFieldGKRRelation, PrimeField};

use super::construct::address_storage_layer;
use super::types::GpuGKRStorageLayout;

impl GpuGKRStorageLayout {
    pub(super) fn assert_aliases_resolve(&self) {
        for (alias, canonical) in self.aliases.iter() {
            assert!(
                !self.aliases.contains_key(canonical),
                "alias chain not fully compressed: {alias:?} -> {canonical:?}",
            );
            let canonical_layer = address_storage_layer(*canonical);
            let layer_layout = self.layers.get(canonical_layer).unwrap_or_else(|| {
                panic!(
                    "alias {alias:?} resolves to canonical {canonical:?} at layer {canonical_layer}, out of range ({} layers)",
                    self.layers.len(),
                )
            });
            assert!(
                layer_layout.index.contains_key(canonical),
                "alias {alias:?} resolves to canonical {canonical:?} missing from layer {canonical_layer}'s index",
            );
        }
    }
}

pub(super) fn build_alias_redirects<F: PrimeField>(
    artifact: &GKRCircuitArtifact<F>,
) -> BTreeMap<GKRAddress, GKRAddress> {
    fn find(parent: &mut BTreeMap<GKRAddress, GKRAddress>, addr: GKRAddress) -> GKRAddress {
        let p = parent.get(&addr).copied().unwrap_or(addr);
        if p == addr {
            return addr;
        }
        let root = find(parent, p);
        parent.insert(addr, root);
        root
    }

    let mut parent: BTreeMap<GKRAddress, GKRAddress> = BTreeMap::new();
    for layer in artifact.layers.iter() {
        for gate in layer
            .gates
            .iter()
            .chain(layer.gates_with_external_connections.iter())
        {
            match &gate.enforced_relation {
                NoFieldGKRRelation::CopyInBaseField { input, output }
                | NoFieldGKRRelation::CopyInExtensionField { input, output } => {
                    let root = find(&mut parent, *input);
                    parent.insert(*output, root);
                }
                _ => {}
            }
        }
    }
    let alias_keys: Vec<_> = parent.keys().copied().collect();
    for addr in alias_keys {
        find(&mut parent, addr);
    }
    parent
        .into_iter()
        .filter(|(alias, canonical)| alias != canonical)
        .collect()
}
