use crate::constraint::Constraint;
use crate::definitions::{GKRAddress, Variable, VirtualSetupPoly};
use crate::gkr_compiler::{GKRGate, LookupType, NoFieldGKRCacheRelation, NoFieldGKRRelation};
use field::PrimeField;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::{collections::BTreeMap, hash::Hash};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum CopyNode {
    FromBase(GKRAddress),
    FromIntermediate(GKRAddress),
}

impl GKRGate for CopyNode {
    type Output = GKRAddress;

    fn short_name(&self) -> String {
        match self {
            Self::FromBase(var) => {
                format!("Copy of {:?}", var)
            }
            Self::FromIntermediate(var) => {
                format!("Copy of {:?}", var)
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
        let input = match self {
            Self::FromBase(input) => *input,
            Self::FromIntermediate(input) => *input,
        };
        println!("Copying variable {:?} -> {:?}", input, output);
        let rel = NoFieldGKRRelation::Copy { input, output };
        graph.add_enforced_relation(rel.clone(), output_layer);

        (output, rel)
    }
}

pub struct GKRGraph {
    pub(crate) mapping: BTreeMap<GKRAddress, usize>,
    pub(crate) rev_mapping: BTreeMap<usize, GKRAddress>,
    pub(crate) base_layer_memory: BTreeMap<Variable, GKRAddress>,
    pub(crate) base_layer_memory_rev: BTreeMap<GKRAddress, Variable>,
    pub(crate) base_layer_witness: BTreeMap<Variable, GKRAddress>,
    pub(crate) base_layer_witness_rev: BTreeMap<GKRAddress, Variable>,
    pub(crate) setups: Vec<GKRAddress>,
    pub(crate) cached_relations: BTreeMap<usize, Vec<NoFieldGKRCacheRelation>>,
    pub(crate) enforced_relations: BTreeMap<usize, Vec<NoFieldGKRRelation>>,
    pub(crate) generic_lookup_setup_width: usize,
    pub(crate) copies: Vec<BTreeMap<GKRAddress, GKRAddress>>,
    pub(crate) intermediate_layers_offsets: BTreeMap<usize, usize>,
    pub(crate) intermediate_layers: BTreeMap<Variable, GKRAddress>,
    pub(crate) intermediate_layers_rev: BTreeMap<GKRAddress, Variable>,
}

impl GKRGraph {
    pub fn new(generic_lookup_setup_width: usize) -> Self {
        let mut new = Self {
            mapping: BTreeMap::new(),
            rev_mapping: BTreeMap::new(),
            base_layer_memory: BTreeMap::new(),
            base_layer_memory_rev: BTreeMap::new(),
            base_layer_witness: BTreeMap::new(),
            base_layer_witness_rev: BTreeMap::new(),
            setups: vec![],
            cached_relations: BTreeMap::new(),
            enforced_relations: BTreeMap::new(),
            generic_lookup_setup_width,
            copies: vec![],
            intermediate_layers_offsets: BTreeMap::new(),
            intermediate_layers: BTreeMap::new(),
            intermediate_layers_rev: BTreeMap::new(),
        };

        // add setups as already resolved
        for i in 0..generic_lookup_setup_width {
            let pos = GKRAddress::Setup(i);
            new.setups.push(pos);
        }

        new
    }

    // pub(crate) fn search_address(&self, pos: &GKRAddress) -> Option<usize> {
    //     for (idx, el) in self.all_nodes.iter().enumerate() {
    //         let other: &dyn GraphElement = el.as_ref();
    //         if pos.equals(other.as_dyn()) {
    //             return Some(idx);
    //         }
    //     }

    //     None
    // }

    // pub(crate) fn search(&self, node: &dyn GraphElement) -> Option<usize> {
    //     let this: &dyn GraphElement = node.as_dyn();
    //     for (idx, el) in self.all_nodes.iter().enumerate() {
    //         let other: &dyn GraphElement = el.as_ref().as_dyn();
    //         if this.equals(other) {
    //             return Some(idx);
    //         }
    //     }

    //     None
    // }

    fn search_cached_relation(
        &self,
        relation: &NoFieldGKRCacheRelation,
        output_layer: usize,
    ) -> Option<usize> {
        if let Some(cached) = self.cached_relations.get(&output_layer) {
            for (idx, el) in cached.iter().enumerate() {
                if relation == el {
                    return Some(idx);
                }
            }

            None
        } else {
            None
        }
    }

    #[track_caller]
    pub(crate) fn layout_memory_subtree_multiple_variables<const N: usize>(
        &mut self,
        variables: [Variable; N],
        all_variables_to_place: &mut BTreeSet<Variable>,
        layers_mapping: &HashMap<Variable, usize>,
    ) -> [GKRAddress; N] {
        let mut columns = [GKRAddress::placeholder(); N];
        for (i, variable) in variables.into_iter().enumerate() {
            assert_eq!(*layers_mapping.get(&variable).expect("is known"), 0);
            let offset = self.base_layer_memory.len();
            let place = GKRAddress::BaseLayerMemory(offset);
            columns[i] = place;
            self.base_layer_memory.insert(variable, place);
            self.base_layer_memory_rev.insert(place, variable);

            // self.add_base_layer_position_as_node(place);

            assert!(
                all_variables_to_place.remove(&variable),
                "variable {:?} was already placed",
                variable
            );
        }

        columns
    }

    #[track_caller]
    pub(crate) fn layout_witness_subtree_multiple_variables<const N: usize>(
        &mut self,
        variables: [Variable; N],
        all_variables_to_place: &mut BTreeSet<Variable>,
        layers_mapping: &HashMap<Variable, usize>,
    ) -> [GKRAddress; N] {
        let mut columns = [GKRAddress::placeholder(); N];
        for (i, variable) in variables.into_iter().enumerate() {
            assert_eq!(*layers_mapping.get(&variable).expect("is known"), 0);
            let offset = self.base_layer_witness.len();
            let place = GKRAddress::BaseLayerWitness(offset);
            columns[i] = place;
            self.base_layer_witness.insert(variable, place);
            self.base_layer_witness_rev.insert(place, variable);

            // self.add_base_layer_position_as_node(place);

            assert!(
                all_variables_to_place.remove(&variable),
                "variable {:?} was already placed",
                variable
            );
        }

        columns
    }

    #[track_caller]
    pub(crate) fn place_intermediate_variable_from_constraint_at_layer<F: PrimeField>(
        &mut self,
        intermediate_layer: usize,
        variable: Variable,
        all_variables_to_place: &mut BTreeSet<Variable>,
        layers_mapping: &HashMap<Variable, usize>,
        defining_constraint: Constraint<F>,
    ) -> GKRAddress {
        assert_eq!(
            *layers_mapping.get(&variable).expect("is known"),
            intermediate_layer
        );
        let offset = self
            .intermediate_layers_offsets
            .entry(intermediate_layer)
            .or_insert(0);
        let place = GKRAddress::InnerLayer {
            layer: intermediate_layer,
            offset: *offset,
        };
        *offset += 1;
        self.intermediate_layers.insert(variable, place);
        self.intermediate_layers_rev.insert(place, variable);
        assert!(
            all_variables_to_place.remove(&variable),
            "variable {:?} was already placed",
            variable
        );
        // add gate
        use crate::gkr_compiler::no_field_gkr_max_quadratic_from_constraint;
        let relation =
            no_field_gkr_max_quadratic_from_constraint(&*self, defining_constraint, place);
        self.add_enforced_relation(relation, intermediate_layer);

        place
    }

    #[track_caller]
    pub(crate) fn get_fixed_layout_pos(&self, variable: &Variable) -> Option<GKRAddress> {
        if let Some(pos) = self.base_layer_memory.get(variable) {
            return Some(*pos);
        }

        if let Some(pos) = self.base_layer_witness.get(variable) {
            return Some(*pos);
        }

        if let Some(pos) = self.intermediate_layers.get(variable) {
            return Some(*pos);
        }

        None
    }
}

impl GraphHolder for GKRGraph {
    #[track_caller]
    fn get_address_for_variable(&self, variable: Variable) -> GKRAddress {
        assert!(
            variable.is_placeholder() == false,
            "trying to place a placeholder variable"
        );
        let Some(pos) = self.get_fixed_layout_pos(&variable) else {
            panic!("Variable {:?} is not placed", variable);
        };

        pos
    }

    fn setup_addresses(&self, lookup_type: LookupType) -> Box<[GKRAddress]> {
        match lookup_type {
            LookupType::RangeCheck16 => {
                vec![GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits)]
                    .into_boxed_slice()
            }
            LookupType::TimestampRangeCheck => vec![GKRAddress::VirtualSetup(
                VirtualSetupPoly::RangeCheckTimestamp,
            )]
            .into_boxed_slice(),
            LookupType::Generic => self.setups.clone().into_boxed_slice(),
        }
    }

    #[track_caller]
    fn add_intermediate_variable_at_layer(&mut self, output_layer: usize) -> GKRAddress {
        let entry = self
            .intermediate_layers_offsets
            .entry(output_layer)
            .or_insert(0);
        let offset = *entry;
        *entry += 1;

        let intermediate = GKRAddress::InnerLayer {
            layer: output_layer,
            offset,
        };

        // println!(
        //     "Created intermediate layer variable {:?} for {:?}",
        //     intermediate,
        //     core::panic::Location::caller()
        // );

        intermediate
    }

    fn add_enforced_relation(&mut self, relation: NoFieldGKRRelation, output_layer: usize) {
        let entry = self
            .enforced_relations
            .entry(output_layer)
            .or_insert(vec![]);
        entry.push(relation);
    }

    #[track_caller]
    fn add_cached_relation(
        &mut self,
        relation: NoFieldGKRCacheRelation,
        output_layer: usize,
    ) -> GKRAddress {
        if let Some(idx) = self.search_cached_relation(&relation, output_layer) {
            GKRAddress::Cached {
                layer: output_layer,
                offset: idx,
            }
        } else {
            let entry = self.cached_relations.entry(output_layer).or_insert(vec![]);
            let offset = entry.len();
            entry.push(relation);

            let rel = GKRAddress::Cached {
                layer: output_layer,
                offset,
            };

            // println!(
            //     "Adding cache relation {:?} at {:?}",
            //     rel,
            //     core::panic::Location::caller()
            // );

            rel
        }
    }

    fn copy_base_layer_variable(&mut self, variable: Variable) -> GKRAddress {
        let pos = self.get_address_for_variable(variable);
        let node = CopyNode::FromBase(pos);
        let (out, _) = node.add_at_layer(self, 1);

        out
    }

    fn copy_intermediate_layer_variable(&mut self, pos: GKRAddress) -> GKRAddress {
        let GKRAddress::InnerLayer { layer, .. } = pos else {
            unreachable!()
        };
        let node = CopyNode::FromIntermediate(pos);
        let (out, _) = node.add_at_layer(self, layer + 1);

        out
    }
}

#[derive(
    Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, serde::Serialize, serde::Deserialize,
)]
pub struct NodeIndex(usize);

pub trait GraphHolder {
    // Get placement data for base layer
    fn get_address_for_variable(&self, variable: Variable) -> GKRAddress;
    // Some setup data
    fn setup_addresses(&self, lookup_type: LookupType) -> Box<[GKRAddress]>;

    // copy variables across layers
    fn copy_base_layer_variable(&mut self, variable: Variable) -> GKRAddress;
    fn copy_intermediate_layer_variable(&mut self, variable: GKRAddress) -> GKRAddress;

    // add cached relations
    fn add_cached_relation(
        &mut self,
        relation: NoFieldGKRCacheRelation,
        output_layer: usize,
    ) -> GKRAddress;

    // add enforced relations
    fn add_intermediate_variable_at_layer(&mut self, output_layer: usize) -> GKRAddress;
    fn add_enforced_relation(&mut self, relation: NoFieldGKRRelation, output_layer: usize);
}

// pub trait GraphElement: 'static + core::any::Any + core::fmt::Debug {
//     fn downcast_to_self(other: &dyn GraphElement) -> Option<&Self>
//     where
//         Self: Sized,
//     {
//         (other as &dyn core::any::Any).downcast_ref::<Self>()
//     }
//     fn as_dyn(&'_ self) -> &'_ (dyn GraphElement + 'static);
//     fn dyn_clone(&self) -> Box<dyn GraphElement>;
//     fn equals(&self, other: &dyn GraphElement) -> bool;
//     fn dependencies(&self, graph: &mut dyn GraphHolder) -> Vec<NodeIndex>;
//     fn short_name(&self) -> String;
//     fn evaluation_description(&self, graph: &mut dyn GraphHolder) -> NoFieldGKRRelation;
// }

// pub(crate) fn downcast_graph_element<T: Sized + 'static>(other: &dyn GraphElement) -> Option<&T> {
//     (other as &dyn core::any::Any).downcast_ref::<T>()
// }

// pub(crate) fn graph_element_equals_if_eq<T: GraphElement + PartialEq + Eq + 'static>(
//     a: &T,
//     other: &dyn GraphElement,
// ) -> bool {
//     let other_inner = other.as_dyn();
//     if let Some(other) = downcast_graph_element::<T>(other_inner) {
//         other == a
//     } else {
//         false
//     }
// }

// impl GraphElement for GKRAddress {
//     fn as_dyn(&'_ self) -> &'_ (dyn GraphElement + 'static) {
//         self
//     }
//     fn dyn_clone(&self) -> Box<dyn GraphElement> {
//         Box::new(*self)
//     }
//     fn equals(&self, other: &dyn GraphElement) -> bool {
//         graph_element_equals_if_eq(self, other)
//     }
//     fn dependencies(&self, _graph: &mut dyn GraphHolder) -> Vec<NodeIndex> {
//         // concrete address has no dependencies
//         vec![]
//     }
//     fn short_name(&self) -> String {
//         match self {
//             Self::BaseLayerMemory(idx) => {
//                 format!("M{}", idx)
//             }
//             Self::BaseLayerWitness(idx) => {
//                 format!("W{}", idx)
//             }
//             Self::Setup(idx) => {
//                 format!("S{}", idx)
//             }
//             Self::InnerLayer { layer, offset } => {
//                 format!("I{}[{}]", layer, offset)
//             }
//             Self::OptimizedOut(..) => {
//                 unreachable!()
//             }
//             Self::Cached(idx) => {
//                 format!("C{}", idx)
//             }
//         }
//     }
//     #[track_caller]
//     fn evaluation_description(&self, _graph: &mut dyn GraphHolder) -> NoFieldGKRRelation {
//         NoFieldGKRRelation::FormalBaseLayerInput
//     }
// }

#[track_caller]
fn find_variable(
    gkr_address: GKRAddress,
    base_layer_mapping: &BTreeMap<Variable, GKRAddress>,
) -> Option<Variable> {
    match gkr_address {
        GKRAddress::BaseLayerMemory(..) | GKRAddress::BaseLayerWitness(..) => {}
        _ => {
            return None;
        }
    }

    for (var, addr) in base_layer_mapping.iter() {
        if addr == &gkr_address {
            return Some(*var);
        }
    }

    None
}
