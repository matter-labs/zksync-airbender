use std::collections::{BTreeMap, BTreeSet};

use gpu_gkr_compiler::{CompiledLayer, ForwardDstLine, ForwardInstr, ForwardOperandLine};

use crate::gkr_address_audit::AddressClass;
use crate::storage_layout::{address_storage_layer, FieldType, GpuGKRStorageLayout};
use crate::upstream::{GKRAddress, ReadPlace};
use crate::GkrPrograms;

use super::vm::lower::read_place_to_gkr_address;
use super::GkrMemoryPolicy;

mod prune;
use prune::{keep_instruction, visit_operands};

pub(crate) struct RecomputePlan {
    pub aliases: BTreeMap<GKRAddress, GKRAddress>,
    pub fields: BTreeMap<GKRAddress, FieldType>,
    pub reads: Vec<BTreeSet<GKRAddress>>,
    pub writes: Vec<BTreeSet<GKRAddress>>,
    pub backward: Vec<BTreeSet<GKRAddress>>,
    pub retained: BTreeSet<GKRAddress>,
}

#[cfg(test)]
pub(crate) fn check_recompute_bindings(programs: &GkrPrograms) {
    for policy in GkrMemoryPolicy::candidates() {
        check_policy_bindings(programs, policy);
    }
}

#[cfg(test)]
fn check_policy_bindings(programs: &GkrPrograms, policy: GkrMemoryPolicy) {
    use super::vm::lower::{lower_desc, FwdVmInputs, ResolvedColumn};
    use crate::upstream::Field;
    use gpu_core::primitives::field::E4;

    let layout = GpuGKRStorageLayout::from_artifact_with_tower(programs.runtime_circuit(), 4);
    let plan = RecomputePlan::new(programs, &layout, policy);
    let dynamic: BTreeSet<_> = plan.writes.iter().flatten().copied().collect();
    let mut resolved = BTreeMap::new();
    let mut bank = 1usize;
    let mut allocate =
        |addresses: &BTreeSet<GKRAddress>,
         rows: usize,
         resolved: &mut BTreeMap<GKRAddress, ResolvedColumn>| {
            let mut groups = BTreeMap::<_, Vec<_>>::new();
            for &address in addresses {
                let (layer, class, field, _) = layout
                    .lookup(address_storage_layer(address), &address)
                    .unwrap();
                groups
                    .entry((layer, field, (!dynamic.contains(&address)).then_some(class)))
                    .or_default()
                    .push(address);
            }
            for ((_, field, _), addresses) in groups {
                let base = (bank << 40) as *mut u8;
                bank += 1;
                let stride_bytes =
                    u32::try_from(rows * if field == FieldType::Ext { 16 } else { 4 }).unwrap();
                for (column, address) in addresses.into_iter().enumerate() {
                    assert!(resolved
                        .insert(
                            address,
                            ResolvedColumn {
                                is_e4: field == FieldType::Ext,
                                matrix_base: base,
                                ptr: base.wrapping_add(column * stride_bytes as usize),
                                stride_bytes,
                            }
                        )
                        .is_none());
                }
            }
        };
    let raw = plan
        .fields
        .keys()
        .copied()
        .filter(|a| !dynamic.contains(a))
        .collect();
    allocate(&raw, layout.trace_len, &mut resolved);
    let header = FwdVmInputs {
        mapping_arena: [std::ptr::without_provenance(1); 3],
        decoder_mapping_col: Some(0),
        table: std::ptr::without_provenance(2),
        table_len: 16,
        count: layout.trace_len as u32,
        inits_and_teardowns_top_bits: &[0; 32],
    };
    let mut bind = |end: usize,
                    outputs: &BTreeSet<GKRAddress>,
                    replay: bool,
                    resolved: &mut BTreeMap<GKRAddress, ResolvedColumn>| {
        let resident = resolved.keys().copied().collect();
        let (layers, temporary) = if replay {
            plan.replay_layers(&programs.forward.layers[..end], &resident, outputs)
        } else {
            let temporary = plan.temporary(end, &resident, outputs);
            let destinations = outputs.union(&temporary).copied().collect();
            let layers = plan.filtered_layers(&programs.forward.layers[..end], &destinations);
            (layers, temporary)
        };
        allocate(outputs, layout.trace_len, resolved);
        allocate(&temporary, 256, resolved);
        lower_desc(
            &layers,
            &header,
            &|a| resolved.get(&plan.canonical(a)).copied(),
            &|_| E4::ONE,
        )
        .unwrap_or_else(|e| panic!("recomputation descriptor capacity/closure: {e:?}"));
        resolved.retain(|a, _| !temporary.contains(a));
    };
    bind(plan.writes.len(), &plan.retained, false, &mut resolved);
    let (_, extras) = programs.main_layer_layout_addresses();
    for i in (0..plan.backward.len()).rev() {
        assert!(plan.backward[i]
            .iter()
            .all(|&a| address_storage_layer(a) <= i));
        resolved.retain(|&a, _| address_storage_layer(a) <= i);
        let missing: BTreeSet<_> = plan.backward[i]
            .iter()
            .copied()
            .filter(|a| !resolved.contains_key(a))
            .collect();
        if !missing.is_empty() {
            let end = plan
                .writes
                .iter()
                .rposition(|w| !w.is_disjoint(&missing))
                .unwrap()
                + 1;
            bind(end, &missing, true, &mut resolved);
        }
        assert!(plan.backward[i].iter().all(|a| resolved.contains_key(a)));
        for source in &programs.main_continuation_window_layer(i).sources {
            let a = crate::programs::bound_window_address(source.raw_family, source.raw_column);
            if !matches!(a, GKRAddress::VirtualSetup(_)) {
                assert!(
                    resolved.contains_key(&plan.canonical(a)),
                    "publication reads a purged output: {a:?}"
                );
            }
        }
        if i > 0 {
            resolved.retain(|&a, _| address_storage_layer(a) < i);
        } else {
            resolved.retain(|a, _| !matches!(a, GKRAddress::Cached { layer: 0, .. }));
        }
        for &address in &extras[i] {
            assert!(
                resolved.contains_key(&plan.canonical(address)),
                "layer {i} extra evaluation reads released storage: {address:?}"
            );
        }
    }
}

impl RecomputePlan {
    pub fn new(
        programs: &GkrPrograms,
        layout: &GpuGKRStorageLayout,
        policy: GkrMemoryPolicy,
    ) -> Self {
        let artifact = programs.runtime_circuit();
        let (value_layers, cache_layers) = match policy {
            GkrMemoryPolicy::Materialize => (0, 0),
            GkrMemoryPolicy::Recompute {
                value_layers,
                cache_layers,
            } => {
                assert!(
                    value_layers != 0 || cache_layers != 0,
                    "recomputation must omit a nonempty prefix"
                );
                (value_layers, cache_layers)
            }
        };
        assert!(
            value_layers < artifact.layers.len(),
            "value omission must retain the final MAIN value layer"
        );
        assert!(
            cache_layers <= artifact.layers.len(),
            "cache omission exceeds the MAIN layer count"
        );
        let mut canonical = BTreeMap::new();
        for (layer, data) in layout.layers.iter().enumerate() {
            for (&address, &(class, field, column)) in &data.index {
                canonical
                    .entry((layer, class, field, column))
                    .or_insert(address);
            }
        }
        let key = |address| {
            let address = artifact
                .scratch_space_mapping
                .get(&address)
                .map_or(address, |&slot| GKRAddress::ScratchSpace(slot));
            layout
                .lookup(address_storage_layer(address), &address)
                .unwrap_or_else(|| panic!("recomputation address has no layout: {address:?}"))
        };
        let mut aliases = BTreeMap::new();
        let mut fields = BTreeMap::new();
        for address in layout
            .layers
            .iter()
            .flat_map(|l| l.index.keys())
            .chain(layout.aliases.keys())
            .chain(artifact.scratch_space_mapping.keys())
        {
            let k = key(*address);
            let target = canonical[&k];
            aliases.insert(*address, target);
            fields.insert(target, k.2);
        }
        let normalize = |address| {
            *aliases
                .get(&address)
                .unwrap_or_else(|| panic!("missing recomputation alias: {address:?}"))
        };
        let mut reads = Vec::new();
        let mut writes = Vec::new();
        for layer in &programs.forward.layers {
            let mut layer_reads = BTreeSet::new();
            let mut layer_writes = BTreeSet::new();
            for instruction in &layer.program.instrs {
                visit_operands(instruction, |operand, _| {
                    if let ForwardOperandLine::Source { window, column } = operand {
                        let place = layer
                            .source_windows
                            .resolve_read_place(*window, *column)
                            .expect("compiled forward source");
                        layer_reads.insert(normalize(read_place_to_gkr_address(&place)));
                    }
                });
                if let ForwardInstr::Mov {
                    dst: Some(ForwardDstLine::GlobalMaterialize { slot, col }),
                    ..
                } = instruction
                {
                    let place = layer
                        .backings
                        .slot_col_to_read_place(*slot, *col)
                        .expect("compiled forward destination");
                    layer_writes.insert(normalize(read_place_to_gkr_address(&place)));
                }
            }
            for special in layer.specials.iter() {
                if let gpu_gkr_compiler::ForwardSpecialStrategy::PeekDecoder { predicate } = special
                {
                    layer_reads.insert(normalize(read_place_to_gkr_address(predicate)));
                }
            }
            reads.push(layer_reads);
            writes.push(layer_writes);
        }
        let dynamic: BTreeSet<_> = writes.iter().flatten().copied().collect();
        let mut backward = Vec::new();
        for i in 0..artifact.layers.len() {
            let mut required = BTreeSet::new();
            for window in &programs.window_layer(i).window.windows {
                for column in &window.columns {
                    let address =
                        crate::programs::bound_window_address(window.family, column.column);
                    if !matches!(address, GKRAddress::VirtualSetup(_)) {
                        required.insert(normalize(address));
                    }
                }
            }
            for source in &programs.main_continuation_window_layer(i).sources {
                let address =
                    crate::programs::bound_window_address(source.raw_family, source.raw_column);
                if !matches!(address, GKRAddress::VirtualSetup(_)) {
                    required.insert(normalize(address));
                }
            }
            for relation in artifact.layers[i].cached_relations.values() {
                required.extend(relation.dependencies().into_iter().map(normalize));
            }
            backward.push(required);
        }
        let targets: BTreeSet<_> = dynamic
            .iter()
            .copied()
            .filter(|&address| {
                let (layer, class, _, _) = key(address);
                match class {
                    AddressClass::ThisLayerCachedWrite => layer < cache_layers,
                    AddressClass::ThisLayerInnerLayerWrite => layer > 0 && layer <= value_layers,
                    _ => false,
                }
            })
            .collect();
        let first_replay_layer = value_layers.max(cache_layers.saturating_sub(1));
        let mut needed_by_tail: BTreeSet<_> = backward
            .iter()
            .skip(first_replay_layer + 1)
            .flatten()
            .copied()
            .collect();
        needed_by_tail.extend(
            artifact
                .global_output_map
                .values()
                .flatten()
                .copied()
                .map(normalize),
        );
        let retained = dynamic
            .into_iter()
            .filter(|a| !targets.contains(a) || needed_by_tail.contains(a))
            .collect();
        Self {
            aliases,
            fields,
            reads,
            writes,
            backward,
            retained,
        }
    }

    pub fn canonical(&self, address: GKRAddress) -> GKRAddress {
        self.aliases[&address]
    }

    pub fn temporary(
        &self,
        end: usize,
        resident: &BTreeSet<GKRAddress>,
        outputs: &BTreeSet<GKRAddress>,
    ) -> BTreeSet<GKRAddress> {
        let read: BTreeSet<_> = self.reads[..end].iter().flatten().copied().collect();
        self.writes[..end]
            .iter()
            .flatten()
            .copied()
            .filter(|a| read.contains(a) && !resident.contains(a) && !outputs.contains(a))
            .collect()
    }

    pub fn filtered_layers(
        &self,
        layers: &[CompiledLayer],
        destinations: &BTreeSet<GKRAddress>,
    ) -> Vec<CompiledLayer> {
        layers
            .iter()
            .cloned()
            .map(|mut layer| {
                layer.program.instrs.retain(|instruction| {
                    let ForwardInstr::Mov {
                        dst: Some(ForwardDstLine::GlobalMaterialize { slot, col }),
                        ..
                    } = instruction
                    else {
                        return true;
                    };
                    let place: ReadPlace = layer
                        .backings
                        .slot_col_to_read_place(*slot, *col)
                        .expect("compiled forward destination");
                    destinations.contains(&self.canonical(read_place_to_gkr_address(&place)))
                });
                layer
            })
            .collect()
    }

    pub fn replay_layers(
        &self,
        layers: &[CompiledLayer],
        resident: &BTreeSet<GKRAddress>,
        outputs: &BTreeSet<GKRAddress>,
    ) -> (Vec<CompiledLayer>, BTreeSet<GKRAddress>) {
        let mut needed = outputs.clone();
        let mut temporary = BTreeSet::new();
        let mut pruned = layers.to_vec();
        for (layer, pruned) in layers.iter().zip(&mut pruned).rev() {
            // Descriptor lowering still binds special metadata even if its readers disappear.
            for special in layer.specials.iter() {
                if let gpu_gkr_compiler::ForwardSpecialStrategy::PeekDecoder { predicate } = special
                {
                    let address = self.canonical(read_place_to_gkr_address(predicate));
                    if !resident.contains(&address) {
                        needed.insert(address);
                    }
                }
            }
            let mut acc_live = false;
            let mut cells = BTreeSet::new();
            pruned.program.instrs = layer
                .program
                .instrs
                .iter()
                .rev()
                .filter(|instruction| {
                    let keep =
                        keep_instruction(instruction, &mut acc_live, &mut cells, |slot, col| {
                            let place = layer
                                .backings
                                .slot_col_to_read_place(slot, col)
                                .expect("compiled forward destination");
                            let address = self.canonical(read_place_to_gkr_address(&place));
                            if !needed.remove(&address) {
                                return false;
                            }
                            if !outputs.contains(&address) {
                                temporary.insert(address);
                            }
                            true
                        });
                    if keep {
                        visit_operands(instruction, |operand, _| {
                            if let ForwardOperandLine::Source { window, column } = operand {
                                let place = layer
                                    .source_windows
                                    .resolve_read_place(*window, *column)
                                    .expect("compiled forward source");
                                let address = self.canonical(read_place_to_gkr_address(&place));
                                if !resident.contains(&address) {
                                    needed.insert(address);
                                }
                            }
                        });
                    }
                    keep
                })
                .cloned()
                .collect();
            pruned.program.instrs.reverse();
        }
        assert!(
            needed.is_empty(),
            "replay columns have no resident value or retained producer: {needed:?}"
        );
        (pruned, temporary)
    }
}
