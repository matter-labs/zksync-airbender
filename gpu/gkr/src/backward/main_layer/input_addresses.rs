use std::collections::BTreeSet;

use crate::programs::GkrPrograms;
use crate::upstream::GKRAddress;

impl GkrPrograms {
    pub(crate) fn main_layer_layout_addresses(
        &self,
    ) -> (Vec<Vec<GKRAddress>>, Vec<Vec<GKRAddress>>) {
        let circuit = self.runtime_circuit();
        assert_eq!(self.backward_layers.len(), circuit.layers.len());

        self.backward_layers
            .iter()
            .zip(&circuit.layers)
            .map(|(plan, layer)| {
                let inputs = plan
                    .inputs
                    .iter()
                    .copied()
                    .filter(|address| *address != GKRAddress::placeholder())
                    .map(|address| {
                        crate::transform::logical_protocol_address(
                            address,
                            &circuit.scratch_space_mapping_rev,
                        )
                    })
                    .collect::<BTreeSet<_>>();
                let extras = layer
                    .cached_relations
                    .values()
                    .flat_map(|relation| relation.dependencies())
                    .map(|address| {
                        crate::transform::logical_protocol_address(
                            address,
                            &circuit.scratch_space_mapping_rev,
                        )
                    })
                    .filter(|address| !inputs.contains(address))
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect();
                (inputs.into_iter().collect(), extras)
            })
            .unzip()
    }
}
