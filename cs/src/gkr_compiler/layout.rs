use crate::definitions::gkr::RamAuxComparisonSet;
use crate::gkr_compiler::graph::{CopyNode, GKRGraph};

use super::*;

#[derive(Clone, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct GKRAuxLayoutData {
    pub shuffle_ram_timestamp_comparison_aux_vars: Vec<RamAuxComparisonSet>,
}

#[serde_with::serde_as]
#[derive(Clone, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct GKRLayerDescription {
    pub layer: usize,
    // our point of convergence is batched sumchecks for lookup and grand product reduction,
    // but as we move to GKR stage where polynomial sizes are not changing, it'll reflect which random evaluation point to use
    // for the sumcheck like f(r) = \sum_x eq(r, x) a(x) b(x)
    pub gates_with_external_connections: Vec<GateArtifacts>,
    #[serde_as(as = "Vec<(_, _)>")]
    pub cached_relations: BTreeMap<GKRAddress, NoFieldGKRCacheRelation>,
    pub gates: Vec<GateArtifacts>,
    // pub additional_base_layer_openings: Vec<GKRAddress>,
}

#[derive(Clone, Debug)]
pub(crate) enum LookupOutput {
    Direct(NoFieldGKRRelation),
    Copied {
        num: NoFieldGKRRelation,
        den: NoFieldGKRRelation,
    },
}

impl GKRGraph {
    fn dump_base_layer_set(&self) -> BTreeSet<GKRAddress> {
        let mut result = BTreeSet::new();
        result.extend(self.base_layer_memory_rev.keys().copied());
        result.extend(self.base_layer_witness_rev.keys().copied());
        result.extend(self.setups.iter().copied());

        result
    }

    pub(crate) fn layout_layers(
        &mut self,
        mut grand_product_outputs: [(GKRAddress, NoFieldGKRRelation); 2],
        mut lookup_outputs: BTreeMap<LookupType, ([GKRAddress; 2], LookupOutput)>,
    ) -> (
        Vec<GKRLayerDescription>,
        BTreeMap<OutputType, Vec<GKRAddress>>,
    ) {
        assert!(self.enforced_relations.len() > 0);
        assert!(self.enforced_relations.get(&0).is_none());

        // We put all external outputs to the same layer

        let total_layers = self.enforced_relations.len();

        // stable iteration order
        let mut output_layers = BTreeMap::new();
        {
            for layer in (1..(1 + total_layers)).rev() {
                let relations = &self.enforced_relations[&layer];
                'outer: for rel in relations.iter() {
                    if rel == &grand_product_outputs[0].1 || rel == &grand_product_outputs[1].1 {
                        output_layers.insert(OutputType::PermutationProduct, layer);
                        continue 'outer;
                    }
                    for (k, (_, el)) in lookup_outputs.iter() {
                        let LookupOutput::Direct(el) = el else {
                            unreachable!()
                        };
                        if el == rel {
                            match k {
                                LookupType::RangeCheck16 => {
                                    output_layers.insert(OutputType::Lookup16Bits, layer);
                                }
                                LookupType::TimestampRangeCheck => {
                                    output_layers.insert(OutputType::LookupTimestamps, layer);
                                }
                                LookupType::Generic => {
                                    output_layers.insert(OutputType::GenericLookup, layer);
                                }
                            }
                            continue 'outer;
                        }
                    }
                }
            }

            let max_output_layer = output_layers.iter().map(|(k, v)| *v).max().unwrap();
            assert!(output_layers.len() <= 4);

            for (k, layer) in output_layers.into_iter() {
                if layer != max_output_layer {
                    match k {
                        OutputType::PermutationProduct => {
                            let current_output = &mut grand_product_outputs;
                            for next_layer in (layer + 1)..=max_output_layer {
                                // copy
                                *current_output =
                                    current_output.each_ref().map(|(addr, _relation)| {
                                        let copy_node = CopyNode::FromIntermediate(*addr);
                                        copy_node.add_at_layer(self, next_layer)
                                    });
                            }
                        }
                        a @ _ => {
                            let current_output = match a {
                                OutputType::Lookup16Bits => {
                                    lookup_outputs.get_mut(&LookupType::RangeCheck16).unwrap()
                                }
                                OutputType::LookupTimestamps => lookup_outputs
                                    .get_mut(&LookupType::TimestampRangeCheck)
                                    .unwrap(),
                                OutputType::GenericLookup => {
                                    lookup_outputs.get_mut(&LookupType::Generic).unwrap()
                                }
                                _ => {
                                    todo!()
                                }
                            };
                            for next_layer in (layer + 1)..=max_output_layer {
                                // copy
                                let [num, den] = &current_output.0;
                                let copy_node = CopyNode::FromIntermediate(*num);
                                let (new_num_addr, new_num_rel) =
                                    copy_node.add_at_layer(self, next_layer);

                                let copy_node = CopyNode::FromIntermediate(*den);
                                let (new_den_addr, new_den_rel) =
                                    copy_node.add_at_layer(self, next_layer);
                                *current_output = (
                                    [new_num_addr, new_den_addr],
                                    LookupOutput::Copied {
                                        num: new_num_rel,
                                        den: new_den_rel,
                                    },
                                );
                            }
                        }
                    }
                }
            }
        }

        // Capture the output map after addresses have been aligned to the max output layer
        let mut global_output_map = BTreeMap::new();
        global_output_map.insert(
            OutputType::PermutationProduct,
            grand_product_outputs
                .iter()
                .map(|(addr, _)| *addr)
                .collect(),
        );
        for (lookup_type, (addrs, _)) in lookup_outputs.iter() {
            let output_type = match lookup_type {
                LookupType::RangeCheck16 => OutputType::Lookup16Bits,
                LookupType::TimestampRangeCheck => OutputType::LookupTimestamps,
                LookupType::Generic => OutputType::GenericLookup,
            };
            global_output_map.insert(output_type, addrs.to_vec());
        }

        let mut result = vec![];

        // the only difficult topic is if a layer has any connection to the size-reducing part of GKR, otherwise we just take
        // all relations without splitting

        for layer in (1..(1 + total_layers)).rev() {
            let mut descr = GKRLayerDescription {
                layer,
                gates_with_external_connections: vec![],
                gates: vec![],
                cached_relations: BTreeMap::new(),
                // additional_base_layer_openings: vec![],
            };

            let layer_for_caches = layer - 1;
            let relations = &self.enforced_relations[&layer];
            let cache_relations_for_this_layer = self
                .cached_relations
                .get(&layer_for_caches)
                .cloned()
                .unwrap_or_default();

            let mut external_lookup_connections = BTreeSet::new();

            let mut base_layer_polys_to_open_for_caches = if layer == 1 {
                self.dump_base_layer_set()
            } else {
                BTreeSet::new()
            };

            'outer: for rel in relations.iter() {
                if rel == &grand_product_outputs[0].1 || rel == &grand_product_outputs[1].1 {
                    // we expect at least 4 grand product contributions for cycle,
                    // so no caching can happen here
                    assert!(rel.cached_addresses().is_empty());
                    let artifact = GateArtifacts {
                        output_layer: layer,
                        enforced_relation: rel.clone(),
                    };
                    descr.gates_with_external_connections.push(artifact);
                    continue 'outer;
                }
                for (k, (_, el)) in lookup_outputs.iter() {
                    match el {
                        LookupOutput::Direct(el) => {
                            if el == rel {
                                if layer > 1 {
                                    assert!(rel.cached_addresses().is_empty());
                                } else {
                                    for cached in rel.cached_addresses().into_iter() {
                                        let GKRAddress::Cached { layer: l, offset } = cached else {
                                            unreachable!();
                                        };
                                        assert_eq!(
                                            l + 1,
                                            layer,
                                            "relation {:?} is at layer {}, but references cache {:?}",
                                            rel,
                                            layer,
                                            cached
                                        );
                                        let relation =
                                            cache_relations_for_this_layer[offset].clone();
                                        descr.cached_relations.insert(cached, relation);
                                    }
                                    // for claim in rel.created_claims().into_iter() {
                                    //     base_layer_polys_to_open_for_caches.remove(&claim);
                                    // }
                                }

                                let artifact = GateArtifacts {
                                    output_layer: layer,
                                    enforced_relation: rel.clone(),
                                };
                                descr.gates_with_external_connections.push(artifact);
                                external_lookup_connections.insert(*k);
                                continue 'outer;
                            }
                        }
                        LookupOutput::Copied { num, den } => {
                            for el in [num, den] {
                                if el == rel {
                                    if layer > 1 {
                                        assert!(rel.cached_addresses().is_empty());
                                    } else {
                                        for cached in rel.cached_addresses().into_iter() {
                                            let GKRAddress::Cached { layer: l, offset } = cached
                                            else {
                                                unreachable!();
                                            };
                                            assert_eq!(
                                                l + 1,
                                                layer,
                                                "relation {:?} is at layer {}, but references cache {:?}",
                                                rel,
                                                layer,
                                                cached
                                            );
                                            let relation =
                                                cache_relations_for_this_layer[offset].clone();
                                            descr.cached_relations.insert(cached, relation);
                                        }
                                        // for claim in rel.created_claims().into_iter() {
                                        //     base_layer_polys_to_open_for_caches.remove(&claim);
                                        // }
                                    }

                                    let artifact = GateArtifacts {
                                        output_layer: layer,
                                        enforced_relation: rel.clone(),
                                    };
                                    descr.gates_with_external_connections.push(artifact);
                                    external_lookup_connections.insert(*k);
                                    continue 'outer;
                                }
                            }
                        }
                    }
                }

                // no external connection beyond this point
                let referenced_caches = rel.cached_addresses();
                for cached in referenced_caches.into_iter() {
                    let GKRAddress::Cached { layer: l, offset } = cached else {
                        unreachable!();
                    };
                    assert_eq!(
                        l + 1,
                        layer,
                        "relation {:?} is at layer {}, but references cache {:?}",
                        rel,
                        layer,
                        cached
                    );
                    let relation = cache_relations_for_this_layer[offset].clone();
                    descr.cached_relations.insert(cached, relation);
                }
                // if layer == 1 {
                //     for claim in rel.created_claims().into_iter() {
                //         base_layer_polys_to_open_for_caches.remove(&claim);
                //     }
                // }
                let artifact = GateArtifacts {
                    output_layer: layer,
                    enforced_relation: rel.clone(),
                };
                descr.gates.push(artifact);
            }

            for k in external_lookup_connections.into_iter() {
                lookup_outputs.remove(&k);
            }

            // if layer == 1 {
            //     descr
            //         .additional_base_layer_openings
            //         .extend(base_layer_polys_to_open_for_caches.into_iter());
            // }

            result.push(descr);
        }

        // enumerate naturally
        result.reverse();

        (result, global_output_map)
    }
}
