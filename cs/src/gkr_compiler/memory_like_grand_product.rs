use super::*;
use crate::cs::circuit_trait::{
    ConstantRegisterAccess, MemoryAccess, RegisterAccess, RegisterIndirectRamAccess,
    WordRepresentation,
};
use crate::definitions::Variable;
use crate::gkr_compiler::graph::CopyNode;

#[derive(Clone, Hash, Debug, PartialEq, Eq)]
pub enum GrandProductAccumulationStep {
    BasePair {
        lhs: MemoryPermutationExpression,
        rhs: MemoryPermutationExpression,
        is_write: bool,
    },
    AggregationPair {
        lhs: GKRAddress,
        rhs: GKRAddress,
        is_write: bool,
    },
    MaterializeBase {
        access: MemoryPermutationExpression,
        is_write: bool,
    },
}

impl GrandProductAccumulationStep {
    fn is_write(&self) -> bool {
        match self {
            Self::BasePair { is_write, .. }
            | Self::AggregationPair { is_write, .. }
            | Self::MaterializeBase { is_write, .. } => *is_write,
        }
    }
}

impl GKRGate for GrandProductAccumulationStep {
    type Output = GKRAddress;

    fn short_name(&self) -> String {
        let is_write = self.is_write();
        match self {
            Self::BasePair { .. } => {
                if is_write {
                    "Memory grand product base write accumulation node".to_string()
                } else {
                    "Memory grand product base read accumulation node".to_string()
                }
            }
            Self::AggregationPair { .. } => {
                if is_write {
                    "Memory grand product aggregation write accumulation node".to_string()
                } else {
                    "Memory grand product aggregation read accumulation node".to_string()
                }
            }
            Self::MaterializeBase { .. } => {
                if is_write {
                    "Materialize single write node".to_string()
                } else {
                    "Materialize single read node".to_string()
                }
            }
        }
    }

    #[track_caller]
    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation) {
        let output = graph.add_intermediate_variable_at_layer(output_layer);
        // create caches
        match self {
            Self::BasePair { lhs, rhs, .. } => {
                assert_ne!(lhs, rhs);
                let input = [lhs, rhs].map(|el| {
                    let expr = mem_permutation_expr_into_cached_expr(el, graph);
                    assert!(output_layer > 0);
                    let cache_layer = output_layer - 1;
                    graph.add_cached_relation(expr, cache_layer)
                });
                let relation = NoFieldGKRRelation::InitialGrandProductFromCaches { input, output };
                graph.add_enforced_relation(relation.clone(), output_layer);

                (output, relation)
            }
            Self::AggregationPair { lhs, rhs, .. } => {
                assert_ne!(lhs, rhs);
                let input = [*lhs, *rhs];
                let relation = NoFieldGKRRelation::TrivialProduct { input, output };
                println!(
                    "Adding memory grand product pairwise accumulation relation {:?}",
                    relation
                );
                graph.add_enforced_relation(relation.clone(), output_layer);

                (output, relation)
            }
            Self::MaterializeBase { access, .. } => {
                let expr = mem_permutation_expr_into_cached_expr(access, graph);
                assert!(output_layer > 0);
                let cache_layer = output_layer - 1;
                let cached = graph.add_cached_relation(expr, cache_layer);

                // and copy it
                let copy_node = CopyNode::FromBase(cached);
                copy_node.add_at_layer(graph, output_layer)
            }
        }
    }
}

#[derive(Clone, Copy, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct GrandProductAccumulationMaskingNode {
    pub lhs: GKRAddress,
    pub mask: GKRAddress,
    pub is_write: bool,
}

impl GKRGate for GrandProductAccumulationMaskingNode {
    type Output = GKRAddress;

    fn short_name(&self) -> String {
        if self.is_write {
            "Grand product write accumulation masking node".to_string()
        } else {
            "Grand product read accumulation masking node".to_string()
        }
    }

    fn add_at_layer(
        &self,
        graph: &mut impl GraphHolder,
        output_layer: usize,
    ) -> (Self::Output, NoFieldGKRRelation) {
        let output = graph.add_intermediate_variable_at_layer(output_layer);
        let relation = NoFieldGKRRelation::MaskIntoIdentityProduct {
            input: self.lhs,
            mask: self.mask,
            output,
        };
        graph.add_enforced_relation(relation.clone(), output_layer);

        (output, relation)
    }
}

pub(crate) fn layout_initial_grand_product_accumulation(
    graph: &mut impl GraphHolder,
    predicate: Variable,
    ram_augmented_sets: &[(MemoryAccess, ShuffleRamTimestampComparisonPartialData)],
    pc_permutation: Option<(
        ([Variable; 2], [Variable; NUM_TIMESTAMP_COLUMNS_FOR_RAM]),
        ([Variable; 2], [Variable; NUM_TIMESTAMP_COLUMNS_FOR_RAM]),
    )>, // (pc, ts)
    delegation_permutation: Option<(u16, [Variable; NUM_TIMESTAMP_COLUMNS_FOR_RAM])>, // virtual register index, timestamp
    mem_accesses_base_write_timestamp: [Variable; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
) -> ((Vec<GKRAddress>, Vec<GKRAddress>), GKRAddress) {
    const PLACEMENT_LAYER: usize = 1;

    println!(
        "Starting a grand product accumulation for in total of {} read/write pairs",
        ram_augmented_sets.len()
            + pc_permutation.is_some() as usize
            + delegation_permutation.is_some() as usize
    );

    let mut grand_product_read_accumulation_nodes = vec![];
    let mut grand_product_write_accumulation_nodes = vec![];

    let copied_predicate_for_grand_product_masking = graph.copy_base_layer_variable(predicate);

    for [a, b] in ram_augmented_sets.as_chunks::<2>().0.iter() {
        // we construct read and write sets separately
        let mut read_set = vec![];
        let mut write_set = vec![];
        for (query, aux) in [a, b] {
            let read_set_el = match query {
                MemoryAccess::RegisterOnly(RegisterAccess { reg_idx, .. }) => {
                    MemoryPermutationExpression {
                        address: AddressSpaceAddress::SingleLimb(*reg_idx),
                        address_space: AddressSpace::Constant(AddressSpaceType::Register),
                        timestamp: MemoryPermutationTimestamp::Normal(aux.read_timestamp),
                        value: query.read_value(),
                        timestamp_offset: 0,
                    }
                }
                MemoryAccess::RegisterOrRam(..) => {
                    todo!();
                }
                MemoryAccess::ConstantRegister(ConstantRegisterAccess { reg_idx, .. }) => {
                    MemoryPermutationExpression {
                        address: AddressSpaceAddress::ConstantU16Limb(*reg_idx),
                        address_space: AddressSpace::Constant(AddressSpaceType::Register),
                        timestamp: MemoryPermutationTimestamp::Normal(aux.read_timestamp),
                        value: query.read_value(),
                        timestamp_offset: 0,
                    }
                }
                MemoryAccess::RamIndirect(RegisterIndirectRamAccess {
                    variable_offset,
                    base_address,
                    constant_offset,
                    ..
                }) => MemoryPermutationExpression {
                    address: AddressSpaceAddress::U32SpaceSpecialIndirect {
                        low_base: base_address[0],
                        low_dynamic_offset: variable_offset.map(|(c, v, _)| (c as u16, v)),
                        offset: *constant_offset,
                        high: base_address[1],
                    },
                    address_space: AddressSpace::Constant(AddressSpaceType::RAM),
                    timestamp: MemoryPermutationTimestamp::Normal(aux.read_timestamp),
                    value: query.read_value(),
                    timestamp_offset: 0,
                },
            };
            read_set.push(read_set_el);

            let write_set_el = match query {
                MemoryAccess::RegisterOnly(RegisterAccess { reg_idx, .. }) => {
                    MemoryPermutationExpression {
                        address: AddressSpaceAddress::SingleLimb(*reg_idx),
                        address_space: AddressSpace::Constant(AddressSpaceType::Register),
                        timestamp: MemoryPermutationTimestamp::Normal(
                            mem_accesses_base_write_timestamp,
                        ),
                        value: query.write_value(),
                        timestamp_offset: query.local_timestamp_in_cycle(),
                    }
                }
                MemoryAccess::RegisterOrRam(..) => {
                    todo!();
                }
                MemoryAccess::ConstantRegister(ConstantRegisterAccess { reg_idx, .. }) => {
                    MemoryPermutationExpression {
                        address: AddressSpaceAddress::ConstantU16Limb(*reg_idx),
                        address_space: AddressSpace::Constant(AddressSpaceType::Register),
                        timestamp: MemoryPermutationTimestamp::Normal(
                            mem_accesses_base_write_timestamp,
                        ),
                        value: query.write_value(),
                        timestamp_offset: query.local_timestamp_in_cycle(),
                    }
                }
                MemoryAccess::RamIndirect(RegisterIndirectRamAccess {
                    variable_offset,
                    base_address,
                    constant_offset,
                    ..
                }) => MemoryPermutationExpression {
                    address: AddressSpaceAddress::U32SpaceSpecialIndirect {
                        low_base: base_address[0],
                        low_dynamic_offset: variable_offset.map(|(c, v, _)| (c as u16, v)),
                        offset: *constant_offset,
                        high: base_address[1],
                    },
                    address_space: AddressSpace::Constant(AddressSpaceType::RAM),
                    timestamp: MemoryPermutationTimestamp::Normal(
                        mem_accesses_base_write_timestamp,
                    ),
                    value: query.write_value(),
                    timestamp_offset: query.local_timestamp_in_cycle(),
                },
            };
            write_set.push(write_set_el);
        }

        let read_set_node = GrandProductAccumulationStep::BasePair {
            lhs: read_set[0].clone(),
            rhs: read_set[1].clone(),
            is_write: false,
        };
        let (read_set_node, _) = read_set_node.add_at_layer(graph, PLACEMENT_LAYER);
        grand_product_read_accumulation_nodes.push(read_set_node);

        let write_set_node = GrandProductAccumulationStep::BasePair {
            lhs: write_set[0].clone(),
            rhs: write_set[1].clone(),
            is_write: true,
        };
        let (write_set_node, _) = write_set_node.add_at_layer(graph, PLACEMENT_LAYER);
        grand_product_write_accumulation_nodes.push(write_set_node);
    }

    {
        let mut read_set = vec![];
        let mut write_set = vec![];

        if ram_augmented_sets.as_chunks::<2>().1.is_empty() == false {
            let last_el = ram_augmented_sets.as_chunks::<2>().1[0].clone();

            let (query, aux) = last_el;
            let read_set_el = match query {
                MemoryAccess::RegisterOnly(RegisterAccess { reg_idx, .. }) => {
                    MemoryPermutationExpression {
                        address: AddressSpaceAddress::SingleLimb(reg_idx),
                        address_space: AddressSpace::Constant(AddressSpaceType::Register),
                        timestamp: MemoryPermutationTimestamp::Normal(aux.read_timestamp),
                        value: query.read_value(),
                        timestamp_offset: 0,
                    }
                }
                MemoryAccess::RegisterOrRam(..) => {
                    todo!();
                }
                MemoryAccess::ConstantRegister(ConstantRegisterAccess { reg_idx, .. }) => {
                    MemoryPermutationExpression {
                        address: AddressSpaceAddress::ConstantU16Limb(reg_idx),
                        address_space: AddressSpace::Constant(AddressSpaceType::Register),
                        timestamp: MemoryPermutationTimestamp::Normal(aux.read_timestamp),
                        value: query.read_value(),
                        timestamp_offset: 0,
                    }
                }
                MemoryAccess::RamIndirect(RegisterIndirectRamAccess {
                    variable_offset,
                    base_address,
                    constant_offset,
                    ..
                }) => MemoryPermutationExpression {
                    address: AddressSpaceAddress::U32SpaceSpecialIndirect {
                        low_base: base_address[0],
                        low_dynamic_offset: variable_offset.map(|(c, v, _)| (c as u16, v)),
                        offset: constant_offset,
                        high: base_address[1],
                    },
                    address_space: AddressSpace::Constant(AddressSpaceType::RAM),
                    timestamp: MemoryPermutationTimestamp::Normal(aux.read_timestamp),
                    value: query.read_value(),
                    timestamp_offset: 0,
                },
            };
            read_set.push(read_set_el);

            let write_set_el = match query {
                MemoryAccess::RegisterOnly(RegisterAccess { reg_idx, .. }) => {
                    MemoryPermutationExpression {
                        address: AddressSpaceAddress::SingleLimb(reg_idx),
                        address_space: AddressSpace::Constant(AddressSpaceType::Register),
                        timestamp: MemoryPermutationTimestamp::Normal(
                            mem_accesses_base_write_timestamp,
                        ),
                        value: query.write_value(),
                        timestamp_offset: query.local_timestamp_in_cycle(),
                    }
                }
                MemoryAccess::RegisterOrRam(..) => {
                    todo!();
                }
                MemoryAccess::ConstantRegister(ConstantRegisterAccess { reg_idx, .. }) => {
                    MemoryPermutationExpression {
                        address: AddressSpaceAddress::ConstantU16Limb(reg_idx),
                        address_space: AddressSpace::Constant(AddressSpaceType::Register),
                        timestamp: MemoryPermutationTimestamp::Normal(
                            mem_accesses_base_write_timestamp,
                        ),
                        value: query.write_value(),
                        timestamp_offset: query.local_timestamp_in_cycle(),
                    }
                }
                MemoryAccess::RamIndirect(RegisterIndirectRamAccess {
                    variable_offset,
                    base_address,
                    constant_offset,
                    ..
                }) => MemoryPermutationExpression {
                    address: AddressSpaceAddress::U32SpaceSpecialIndirect {
                        low_base: base_address[0],
                        low_dynamic_offset: variable_offset.map(|(c, v, _)| (c as u16, v)),
                        offset: constant_offset,
                        high: base_address[1],
                    },
                    address_space: AddressSpace::Constant(AddressSpaceType::RAM),
                    timestamp: MemoryPermutationTimestamp::Normal(
                        mem_accesses_base_write_timestamp,
                    ),
                    value: query.write_value(),
                    timestamp_offset: query.local_timestamp_in_cycle(),
                },
            };
            write_set.push(write_set_el);
        }

        // and PC permutation or delegation permutation
        if let Some((
            (cycle_start_pc, cycle_start_timestamp),
            (cycle_end_pc, cycle_end_timestamp),
        )) = pc_permutation
        {
            assert!(delegation_permutation.is_none());
            let read_set_el = MemoryPermutationExpression {
                address: AddressSpaceAddress::Empty,
                address_space: AddressSpace::Constant(AddressSpaceType::PC),
                timestamp: MemoryPermutationTimestamp::Normal(cycle_start_timestamp),
                value: WordRepresentation::U16Limbs(cycle_start_pc),
                timestamp_offset: 0,
            };
            read_set.push(read_set_el);

            let write_set_el = MemoryPermutationExpression {
                address: AddressSpaceAddress::Empty,
                address_space: AddressSpace::Constant(AddressSpaceType::PC),
                timestamp: MemoryPermutationTimestamp::Normal(cycle_end_timestamp),
                value: WordRepresentation::U16Limbs(cycle_end_pc),
                timestamp_offset: 0,
            };
            write_set.push(write_set_el);
        }
        if let Some((reg_idx, delegation_ts)) = delegation_permutation {
            assert!(pc_permutation.is_none());
            let read_set_el = MemoryPermutationExpression {
                address: AddressSpaceAddress::ConstantU16Limb(reg_idx),
                address_space: AddressSpace::Constant(AddressSpaceType::Register),
                timestamp: MemoryPermutationTimestamp::Normal(delegation_ts),
                value: WordRepresentation::Zero,
                timestamp_offset: 0,
            };
            read_set.push(read_set_el);

            let write_set_el = MemoryPermutationExpression {
                address: AddressSpaceAddress::ConstantU16Limb(reg_idx),
                address_space: AddressSpace::Constant(AddressSpaceType::Register),
                timestamp: MemoryPermutationTimestamp::Zero, // delegation in the corresponding family uses read ts == 0, and some write TS,
                // so here we have to use non-zero read TS, and zero write TS to ensure a permutation
                value: WordRepresentation::Zero,
                timestamp_offset: 0,
            };
            write_set.push(write_set_el);
        }

        if read_set.len() == 1 {
            assert_eq!(write_set.len(), 1);
            // materialize it
            let read_set_node = GrandProductAccumulationStep::MaterializeBase {
                access: read_set[0].clone(),
                is_write: false,
            };
            let (read_set_node, _) = read_set_node.add_at_layer(graph, PLACEMENT_LAYER);
            grand_product_read_accumulation_nodes.push(read_set_node);

            let write_set_node = GrandProductAccumulationStep::MaterializeBase {
                access: write_set[0].clone(),
                is_write: true,
            };
            let (write_set_node, _) = write_set_node.add_at_layer(graph, PLACEMENT_LAYER);
            grand_product_write_accumulation_nodes.push(write_set_node);
        } else {
            assert_eq!(read_set.len(), 2);
            assert_eq!(write_set.len(), 2);

            let read_set_node = GrandProductAccumulationStep::BasePair {
                lhs: read_set[0].clone(),
                rhs: read_set[1].clone(),
                is_write: false,
            };
            let (read_set_node, _) = read_set_node.add_at_layer(graph, PLACEMENT_LAYER);
            grand_product_read_accumulation_nodes.push(read_set_node);

            let write_set_node = GrandProductAccumulationStep::BasePair {
                lhs: write_set[0].clone(),
                rhs: write_set[1].clone(),
                is_write: true,
            };
            let (write_set_node, _) = write_set_node.add_at_layer(graph, PLACEMENT_LAYER);
            grand_product_write_accumulation_nodes.push(write_set_node);
        }
    }

    (
        (
            grand_product_read_accumulation_nodes,
            grand_product_write_accumulation_nodes,
        ),
        copied_predicate_for_grand_product_masking,
    )
}

pub(crate) fn accumulate_memory_like_grand_product(
    graph: &mut impl GraphHolder,
    mut copied_predicate_for_grand_product_masking: GKRAddress,
    grand_product_read_accumulation_nodes: Vec<GKRAddress>,
    grand_product_write_accumulation_nodes: Vec<GKRAddress>,
) -> (
    (GKRAddress, NoFieldGKRRelation),
    (GKRAddress, NoFieldGKRRelation),
) {
    let mut output_layer = 2;

    println!(
        "Continuing grand product accumulation at layer {} for {} read/write contribution pairs",
        output_layer - 1,
        grand_product_read_accumulation_nodes.len()
    );

    let mut next_read_set = vec![];
    let mut next_write_set = vec![];

    copied_predicate_for_grand_product_masking =
        graph.copy_intermediate_layer_variable(copied_predicate_for_grand_product_masking);
    copied_predicate_for_grand_product_masking.assert_as_layer(output_layer);

    assert!(grand_product_read_accumulation_nodes.len() > 1);
    assert_eq!(
        grand_product_read_accumulation_nodes.len(),
        grand_product_write_accumulation_nodes.len()
    );

    for (is_write, source, dst) in [
        (
            false,
            &grand_product_read_accumulation_nodes,
            &mut next_read_set,
        ),
        (
            true,
            &grand_product_write_accumulation_nodes,
            &mut next_write_set,
        ),
    ] {
        for [a, b] in source.as_chunks::<2>().0.iter() {
            a.assert_as_dependency_for_layer(output_layer);
            b.assert_as_dependency_for_layer(output_layer);
            let el = GrandProductAccumulationStep::AggregationPair {
                lhs: *a,
                rhs: *b,
                is_write,
            };
            let (el, _) = el.add_at_layer(graph, output_layer);
            dst.push(el);
        }

        match source.as_chunks::<2>().1 {
            [] => {}
            [remainder] => {
                // copy to the next one
                remainder.assert_as_dependency_for_layer(output_layer);
                println!(
                    "Copying remaining contribution {:?} to the next layer",
                    &remainder
                );
                let copied_remainder = graph.copy_intermediate_layer_variable(*remainder);
                dst.push(copied_remainder);
            }
            _ => {
                unreachable!()
            }
        }
    }

    let mut current_read_set = next_read_set;
    let mut current_write_set = next_write_set;

    let mut next_read_set = vec![];
    let mut next_write_set = vec![];

    assert!(current_read_set.len() > 0);
    if current_read_set.len() > 1 || current_write_set.len() > 1 {
        loop {
            assert_eq!(current_read_set.len(), current_write_set.len());

            if current_read_set.len() == 1 {
                assert_eq!(current_write_set.len(), 1);
                break;
            }

            output_layer += 1;

            let initial_len = current_read_set.len();

            copied_predicate_for_grand_product_masking =
                graph.copy_intermediate_layer_variable(copied_predicate_for_grand_product_masking);
            copied_predicate_for_grand_product_masking.assert_as_layer(output_layer);

            println!(
                "Continuing grand product accumulation at layer {} for {} read/write contribution pairs",
                output_layer - 1,
                current_read_set.len(),
            );

            for (is_write, source, dst) in [
                (false, &current_read_set, &mut next_read_set),
                (true, &current_write_set, &mut next_write_set),
            ] {
                for [a, b] in source.as_chunks::<2>().0.iter() {
                    a.assert_as_dependency_for_layer(output_layer);
                    b.assert_as_dependency_for_layer(output_layer);
                    let el = GrandProductAccumulationStep::AggregationPair {
                        lhs: *a,
                        rhs: *b,
                        is_write,
                    };
                    let (el, _) = el.add_at_layer(graph, output_layer);
                    dst.push(el);
                }

                match source.as_chunks::<2>().1 {
                    [] => {}
                    [remainder] => {
                        // copy to the next one
                        remainder.assert_as_dependency_for_layer(output_layer);
                        println!(
                            "Copying remaining contribution {:?} to the next layer",
                            &remainder
                        );
                        let copied_remainder = graph.copy_intermediate_layer_variable(*remainder);
                        dst.push(copied_remainder);
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }

            current_read_set = next_read_set;
            current_write_set = next_write_set;

            next_read_set = vec![];
            next_write_set = vec![];

            if current_read_set.len() == initial_len {
                panic!(
                    "Placer is stuck at layer {}: read set = {:?}, write set = {:?}",
                    output_layer - 1,
                    &current_read_set,
                    &current_write_set
                );
            }
        }
    }

    assert_eq!(current_read_set.len(), 1);
    assert_eq!(current_write_set.len(), 1);

    let read_node = current_read_set.pop().unwrap();
    let write_node = current_write_set.pop().unwrap();

    output_layer += 1;
    copied_predicate_for_grand_product_masking.assert_as_dependency_for_layer(output_layer);
    read_node.assert_as_dependency_for_layer(output_layer);
    write_node.assert_as_dependency_for_layer(output_layer);

    println!(
        "Finishing grand product accumulation at layer {} for {:?} as final read contribution, {:?} as final write contribution, and {:?} as mask",
        output_layer - 1,
        read_node,
        write_node,
        copied_predicate_for_grand_product_masking,
    );

    let read_mask = GrandProductAccumulationMaskingNode {
        lhs: read_node,
        mask: copied_predicate_for_grand_product_masking,
        is_write: false,
    };
    let read_output = read_mask.add_at_layer(graph, output_layer);

    let write_mask = GrandProductAccumulationMaskingNode {
        lhs: write_node,
        mask: copied_predicate_for_grand_product_masking,
        is_write: true,
    };
    let write_output = write_mask.add_at_layer(graph, output_layer);

    (read_output, write_output)
}
