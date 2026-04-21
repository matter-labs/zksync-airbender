use std::fmt::Debug;

use super::*;

use crate::constraint::Constraint;
use crate::cs::circuit_trait::WordRepresentation;
use crate::definitions::gkr::AddressSpaceType;
use crate::definitions::gkr::*;
use crate::definitions::DecoderData;
use crate::definitions::DelegationCircuitState;
use crate::definitions::GKRAddress;
use crate::definitions::OpcodeFamilyCircuitState;
use crate::definitions::Variable;
use crate::definitions::REGISTER_SIZE;
use crate::gkr_compiler::graph::GKRGraph;
use crate::gkr_compiler::graph::GraphHolder;
use crate::gkr_compiler::lookup_nodes::LookupInputRelation;
use crate::types::Boolean;

pub fn add_compiler_defined_base_layer_variable(
    num_variables: &mut u64,
    all_variables_to_place: &mut BTreeSet<Variable>,
    layers_mapping: &mut HashMap<Variable, usize>,
) -> Variable {
    let var = Variable(*num_variables);
    *num_variables += 1;
    all_variables_to_place.insert(var);
    layers_mapping.insert(var, 0);

    var
}

pub fn get_input_layer_ensure_same(
    variables: &BTreeSet<Variable>,
    layers_mapping: &HashMap<Variable, usize>,
) -> usize {
    let mut layer = None;
    for el in variables.iter() {
        let el_layer = *layers_mapping.get(el).expect("must be known");
        if let Some(layer) = layer {
            assert_eq!(layer, el_layer);
        } else {
            layer = Some(el_layer)
        }
    }

    layer.expect("at least one input")
}

pub fn no_field_gkr_max_quadratic_from_constraint<F: PrimeField>(
    graph: &dyn GraphHolder,
    mut constraint: Constraint<F>,
    output: GKRAddress,
) -> NoFieldGKRRelation {
    constraint.normalize();
    let (quadratic_part, linear_part, constant) = constraint.clone().split_max_quadratic();

    if constraint.degree() == 1 && constraint.stable_variable_set().len() == 1 {
        // maybe copy is enough
        if quadratic_part.is_empty() && constant.is_zero() {
            assert_eq!(linear_part.len(), 1);
            let (c, var) = linear_part[0];
            if c.is_one() {
                // just copy
                let input = graph.get_address_for_variable(var);
                // in circuits all elements are in base field
                return NoFieldGKRRelation::CopyInBaseField { input, output };
            }
        }
    }

    let mut quadratic_sorted = BTreeMap::new();
    let mut linear_sorted = BTreeMap::new();

    for (coeff, a, b) in quadratic_part.iter() {
        let a = graph.get_address_for_variable(*a);
        let b = graph.get_address_for_variable(*b);
        let existing = quadratic_sorted
            .entry(a)
            .or_insert(BTreeMap::new())
            .insert(b, coeff.as_u32_reduced());
        assert!(existing.is_none());
    }
    for (coeff, a) in linear_part.into_iter() {
        let a = graph.get_address_for_variable(a);
        let exising = linear_sorted.insert(a, coeff.as_u32_reduced());
        assert!(exising.is_none());
    }

    let quadratic_terms = quadratic_sorted
        .into_iter()
        .map(|(k, v)| {
            (
                k,
                v.into_iter()
                    .map(|(k, v)| (v, k))
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
            )
        })
        .collect::<Vec<_>>()
        .into_boxed_slice();

    let linear_terms = linear_sorted
        .into_iter()
        .map(|(k, v)| (v, k))
        .collect::<Vec<_>>()
        .into_boxed_slice();

    let input = NoFieldMaxQuadraticGKRRelation {
        quadratic_terms,
        linear_terms,
        constant: constant.as_u32_reduced(),
    };
    NoFieldGKRRelation::MaxQuadratic { input, output }
}

// pub fn add_multiple_compiler_defined_variables<const N: usize>(
//     num_variables: &mut u64,
//     all_variables_to_place: &mut BTreeSet<Variable>,
// ) -> [Variable; N] {
//     let output = std::array::from_fn(|_| {
//         let var = Variable(*num_variables);
//         *num_variables += 1;
//         all_variables_to_place.insert(var);

//         var
//     });

//     output
// }

// #[track_caller]
// pub(crate) fn layout_witness_subtree_variable_at_column(
//     offset: usize,
//     variable: Variable,
//     all_variables_to_place: &mut BTreeSet<Variable>,
//     layout: &mut BTreeMap<Variable, GKRAddress>,
// ) -> GKRAddress {
//     assert!(
//         all_variables_to_place.remove(&variable),
//         "variable {:?} was already placed",
//         variable
//     );
//     let address = GKRAddress::BaseLayerWitness(offset);
//     let existing = layout.insert(variable, address);
//     assert!(existing.is_none());

//     address
// }

#[derive(Clone, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub struct MachineStateWithDecoderData {
    pub execute: usize,
    pub initial_pc: [usize; 2],
    pub initial_timestamp: [usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub final_pc: [usize; 2],
    pub final_timestamp: [usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub rs1_index: usize,
    // can be memory or witness, as there can be some selection there
    pub rs2_index: GKRAddress,
    pub rd_index: GKRAddress,
    pub imm: [GKRAddress; REGISTER_SIZE],
    pub funct3: Option<GKRAddress>,
    pub circuit_family_extra_mask: Vec<GKRAddress>,
}

pub(crate) fn layout_machine_state_for_preprocessed_bytecode<F: PrimeField>(
    graph: &mut GKRGraph,
    all_variables_to_place: &mut BTreeSet<Variable>,
    state: &OpcodeFamilyCircuitState<F>,
    family_bitmask: Vec<Variable>,
    layers_mapping: &HashMap<Variable, usize>,
) -> MachineStateWithDecoderData {
    let [execute] = graph.layout_memory_subtree_multiple_variables(
        [state.execute],
        all_variables_to_place,
        layers_mapping,
    );
    let GKRAddress::BaseLayerMemory(execute) = execute else {
        unreachable!()
    };
    let initial_pc = graph.layout_memory_subtree_multiple_variables(
        state.cycle_start_state.pc,
        all_variables_to_place,
        layers_mapping,
    );
    let initial_pc = initial_pc.map(|el| {
        let GKRAddress::BaseLayerMemory(el) = el else {
            unreachable!()
        };

        el
    });
    let initial_timestamp = graph.layout_memory_subtree_multiple_variables(
        state.cycle_start_state.timestamp,
        all_variables_to_place,
        layers_mapping,
    );
    let initial_timestamp = initial_timestamp.map(|el| {
        let GKRAddress::BaseLayerMemory(el) = el else {
            unreachable!()
        };

        el
    });

    let final_pc = graph.layout_memory_subtree_multiple_variables(
        state.cycle_end_state.pc,
        all_variables_to_place,
        layers_mapping,
    );
    let final_pc = final_pc.map(|el| {
        let GKRAddress::BaseLayerMemory(el) = el else {
            unreachable!()
        };

        el
    });
    let final_timestamp = graph.layout_memory_subtree_multiple_variables(
        state.cycle_end_state.timestamp,
        all_variables_to_place,
        layers_mapping,
    );
    let final_timestamp = final_timestamp.map(|el| {
        let GKRAddress::BaseLayerMemory(el) = el else {
            unreachable!()
        };

        el
    });

    // but the rest CAN be in witness, and form a special lookup table entry PC -> decoder data

    let DecoderData {
        rs1_index,
        rs2_index,
        rd_index,
        imm,
        funct3,
        funct7,
        circuit_family_extra_mask,
        ..
    } = state.decoder_data.clone();

    let rs1_index =
        if let Some(GKRAddress::BaseLayerMemory(offset)) = graph.get_fixed_layout_pos(&rs1_index) {
            offset
        } else {
            unreachable!();
        };

    let rs2_index =
        if let Some(GKRAddress::BaseLayerMemory(offset)) = graph.get_fixed_layout_pos(&rs2_index) {
            GKRAddress::BaseLayerMemory(offset)
        } else {
            let t = graph.layout_witness_subtree_multiple_variables(
                [rs2_index],
                all_variables_to_place,
                layers_mapping,
            );

            t[0]
        };

    let rd_index =
        if let Some(GKRAddress::BaseLayerMemory(offset)) = graph.get_fixed_layout_pos(&rd_index) {
            GKRAddress::BaseLayerMemory(offset)
        } else {
            let t = graph.layout_witness_subtree_multiple_variables(
                [rd_index],
                all_variables_to_place,
                layers_mapping,
            );

            t[0]
        };

    let imm = graph.layout_witness_subtree_multiple_variables(
        imm,
        all_variables_to_place,
        layers_mapping,
    );
    let funct3 = if let Some(funct3) = funct3 {
        let funct3 = graph.layout_witness_subtree_multiple_variables(
            [funct3],
            all_variables_to_place,
            layers_mapping,
        );
        Some(funct3[0])
    } else {
        None
    };

    assert!(funct7.is_none());
    assert!(circuit_family_extra_mask.is_placeholder());

    let mut bitmask = Vec::with_capacity(family_bitmask.len());
    for el in family_bitmask.into_iter() {
        let el = if let Some(GKRAddress::BaseLayerMemory(offset)) = graph.get_fixed_layout_pos(&el)
        {
            GKRAddress::BaseLayerMemory(offset)
        } else {
            let t = graph.layout_witness_subtree_multiple_variables(
                [el],
                all_variables_to_place,
                layers_mapping,
            );

            t[0]
        };
        bitmask.push(el);
    }

    MachineStateWithDecoderData {
        execute,
        initial_pc,
        initial_timestamp,
        final_pc,
        final_timestamp,
        rs1_index,
        rs2_index,
        rd_index,
        imm,
        funct3,
        circuit_family_extra_mask: bitmask,
    }
}

pub use crate::definitions::gkr::CompiledDelegationCircuitState;

pub(crate) fn layout_delegation_circuit_state(
    graph: &mut GKRGraph,
    all_variables_to_place: &mut BTreeSet<Variable>,
    state: &DelegationCircuitState,
    layers_mapping: &HashMap<Variable, usize>,
) -> CompiledDelegationCircuitState {
    let [execute] = graph.layout_memory_subtree_multiple_variables(
        [state.execute],
        all_variables_to_place,
        layers_mapping,
    );
    let GKRAddress::BaseLayerMemory(execute) = execute else {
        unreachable!()
    };
    let invocation_timestamp = graph.layout_memory_subtree_multiple_variables(
        state.invocation_timestamp,
        all_variables_to_place,
        layers_mapping,
    );
    let invocation_timestamp = invocation_timestamp.map(|el| {
        let GKRAddress::BaseLayerMemory(el) = el else {
            unreachable!()
        };

        el
    });

    CompiledDelegationCircuitState {
        execute,
        invocation_timestamp,
    }
}

pub trait DependentNode {
    fn add_dependencies_into(
        &self,
        graph: &mut dyn graph::GraphHolder,
        dst: &mut Vec<graph::NodeIndex>,
    );
}

#[derive(Clone, Copy, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum AddressSpaceIsRegisterOrRamRaw {
    IsRegister(Variable),
    IsRam(Variable),
}

#[derive(Clone, Copy, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[repr(u8)]
pub enum AddressSpace {
    Constant(AddressSpaceType),
    RegisterOrRam(AddressSpaceIsRegisterOrRamRaw),
}

#[derive(Clone, Copy, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum AddressSpaceAddress {
    Empty,
    ConstantU16Limb(u16),
    SingleLimb(Variable),
    U32Space([Variable; 2]),
    U32SpaceSpecialIndirect {
        low_base: Variable,
        low_dynamic_offset: Option<(u16, Variable)>,
        offset: u32,
        high: Variable,
    },
}

#[derive(Clone, Copy, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum MemoryPermutationTimestamp {
    Zero,
    Normal([Variable; NUM_TIMESTAMP_COLUMNS_FOR_RAM]),
}

#[derive(Clone, Copy, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct MemoryPermutationExpression {
    pub address_space: AddressSpace,
    pub address: AddressSpaceAddress,
    pub timestamp: MemoryPermutationTimestamp,
    pub value: WordRepresentation,
    pub timestamp_offset: u32,
}

pub fn add_compiler_defined_variable_from_constraint<F: PrimeField>(
    num_variables: &mut u64,
    all_variables_to_place: &mut BTreeSet<Variable>,
    variables_from_constraints: &mut HashMap<Variable, Constraint<F>>,
    constraint: Constraint<F>,
) -> Variable {
    let var = Variable(*num_variables);
    *num_variables += 1;
    all_variables_to_place.insert(var);
    variables_from_constraints.insert(var, constraint.clone());

    var
}

pub(crate) fn reg_boolean_into_address_space(
    is_register: Boolean,
    raw_column: usize,
) -> RegisterOrRamAddressSpace {
    match is_register {
        Boolean::Is(..) => {
            // if boolean is "true" then the address space must be "register" = 0
            assert_eq!(AddressSpaceType::Register as u8, 0);
            // and if raw column is `1` then it's interpreted directly
            RegisterOrRamAddressSpace::RegisterAddressSpace(raw_column)
        }
        Boolean::Not(..) => {
            // if boolean is "true" then the address space must be "register" = 0
            assert_eq!(AddressSpaceType::RAM as u8, 1);
            // and if raw column is `1` then it's interpreted directly later on into `0` value for contribution purposes
            RegisterOrRamAddressSpace::RamAddressSpace(raw_column)
        }
        Boolean::Constant(_) => {
            unreachable!()
        }
    }
}

pub(crate) fn mem_permutation_expr_into_gkr_relation(
    mem: &MemoryPermutationExpression,
    graph: &dyn GraphHolder,
) -> NoFieldSpecialMemoryContributionRelation {
    let address_space = match mem.address_space {
        AddressSpace::Constant(c) => CompiledAddressSpaceRelationStrict::Constant(c as u8 as u32),
        AddressSpace::RegisterOrRam(is_reg) => {
            assert_eq!(AddressSpaceType::Register as u8, 0);
            match is_reg {
                AddressSpaceIsRegisterOrRamRaw::IsRegister(v) => {
                    CompiledAddressSpaceRelationStrict::IsRegister(
                        // NOTE: if v == 1 we should have 0 (register address space),
                        graph.get_address_for_variable(v).as_memory(),
                    )
                }
                AddressSpaceIsRegisterOrRamRaw::IsRam(v) => {
                    CompiledAddressSpaceRelationStrict::IsRam(
                        // NOTE: if v == 1 we should have 1 (RAM address space),
                        graph.get_address_for_variable(v).as_memory(),
                    )
                }
            }
        }
    };
    let address = match mem.address {
        AddressSpaceAddress::Empty => CompiledAddressStrict::Constant(0),
        AddressSpaceAddress::ConstantU16Limb(u16_address) => {
            CompiledAddressStrict::ConstantU16(u16_address)
        }
        AddressSpaceAddress::SingleLimb(v) => {
            CompiledAddressStrict::U16Space(graph.get_address_for_variable(v).as_memory())
        }
        AddressSpaceAddress::U32Space(s) => CompiledAddressStrict::U32Space(
            s.map(|v| graph.get_address_for_variable(v).as_memory()),
        ),
        AddressSpaceAddress::U32SpaceSpecialIndirect {
            low_base,
            low_dynamic_offset,
            offset,
            high,
        } => {
            let low_base = graph.get_address_for_variable(low_base).as_memory();
            let low_dynamic_offset = low_dynamic_offset
                .map(|(coeff, el)| (coeff, graph.get_address_for_variable(el).as_memory()));
            let high = graph.get_address_for_variable(high).as_memory();
            CompiledAddressStrict::U32SpaceSpecialIndirect {
                low_base,
                low_dynamic_offset,
                low_offset: offset,
                high,
            }
        }
    };
    let value = match mem.value {
        WordRepresentation::Zero => RamWordRepresentation::Zero,
        WordRepresentation::U16Limbs(value) => RamWordRepresentation::U16Limbs(
            value.map(|el| graph.get_address_for_variable(el).as_memory()),
        ),
        WordRepresentation::U8Limbs(value) => RamWordRepresentation::U8Limbs(
            value.map(|el| graph.get_address_for_variable(el).as_memory()),
        ),
    };

    let timestamp = match mem.timestamp {
        MemoryPermutationTimestamp::Zero => CompiledMemoryTimestamp::Zero,
        MemoryPermutationTimestamp::Normal(ts) => CompiledMemoryTimestamp::Normal(
            ts.map(|el| graph.get_address_for_variable(el).as_memory()),
        ),
    };

    let rel = NoFieldSpecialMemoryContributionRelation {
        address_space,
        address,
        timestamp,
        value,
        timestamp_offset: mem.timestamp_offset,
    };

    rel
}

pub(crate) fn mem_permutation_expr_into_cached_expr(
    mem: &MemoryPermutationExpression,
    graph: &dyn GraphHolder,
) -> NoFieldGKRCacheRelation {
    NoFieldGKRCacheRelation::MemoryTuple(mem_permutation_expr_into_gkr_relation(mem, graph))
}

pub(crate) fn lookup_input_into_relation<F: PrimeField, const SINGLE_COLUMN: bool>(
    lookup: &LookupInputRelation<F>,
    lookup_set_index: usize,
    total_width: usize,
    graph: &dyn GraphHolder,
) -> NoFieldVectorLookupRelation {
    if SINGLE_COLUMN {
        assert_eq!(lookup.inputs.len(), 1);
        assert!(lookup.table_id.is_none());
    }
    let mut dst = vec![];
    for relation in lookup.inputs.iter() {
        let mut t = vec![];
        for (c, v) in relation.linear_terms.iter() {
            let v = graph.get_address_for_variable(*v);
            t.push((c.as_u32_reduced(), v));
        }
        let rel = NoFieldLinearRelation {
            linear_terms: t.into_boxed_slice(),
            constant: relation.constant_term.as_u32_reduced(),
        };
        dst.push(rel);
    }
    let padded_len = if lookup.table_id.is_some() {
        total_width - 1
    } else {
        total_width
    };
    assert!(dst.len() <= padded_len);

    for _ in dst.len()..padded_len {
        let rel = NoFieldLinearRelation {
            linear_terms: vec![].into_boxed_slice(),
            constant: 0,
        };
        dst.push(rel);
    }

    if let Some(table_id) = lookup.table_id.as_ref() {
        let mut t = vec![];
        for (c, v) in table_id.linear_terms.iter() {
            let v = graph.get_address_for_variable(*v);
            t.push((c.as_u32_reduced(), v));
        }
        let rel = NoFieldLinearRelation {
            linear_terms: t.into_boxed_slice(),
            constant: table_id.constant_term.as_u32_reduced(),
        };
        dst.push(rel);
    }

    NoFieldVectorLookupRelation {
        columns: dst.into_boxed_slice(),
        lookup_set_index,
    }
}

pub(crate) fn lookup_input_into_cached_expr<F: PrimeField, const SINGLE_COLUMN: bool>(
    lookup: &LookupInputRelation<F>,
    lookup_set_index: usize,
    total_width: usize,
    graph: &dyn GraphHolder,
) -> NoFieldGKRCacheRelation {
    NoFieldGKRCacheRelation::VectorizedLookup(lookup_input_into_relation::<F, SINGLE_COLUMN>(
        lookup,
        lookup_set_index,
        total_width,
        graph,
    ))
}

// pub(crate) fn vector_or_single_input<const SINGLE_COLUMN: bool>(
//     input: NoFieldVectorLookupRelation,
// ) -> LookupDenominator {
//     if SINGLE_COLUMN {
//         assert_eq!(input.columns.len(), 1);
//         let input = NoFieldSingleColumnLookupRelation {
//             input: input.columns[0].clone(),
//             lookup_set_index: input.lookup_set_index,
//         };
//         lookup_nodes::LookupDenominator::UseInput(input)
//     } else {
//         lookup_nodes::LookupDenominator::UseVectorInput(input)
//     }
// }

// pub(crate) fn vector_or_single_setup<const SINGLE_COLUMN: bool>(
//     graph: &dyn GraphHolder,
//     lookup_type: LookupType,
// ) -> LookupDenominator {
//     if SINGLE_COLUMN {
//         assert!(
//             lookup_type == LookupType::RangeCheck16
//                 || lookup_type == LookupType::TimestampRangeCheck
//         );
//         let setup = graph.setup_addresses(lookup_type);
//         assert_eq!(setup.len(), 1);
//         lookup_nodes::LookupDenominator::Setup(setup[0])
//     } else {
//         lookup_nodes::LookupDenominator::VectorSetup(
//             graph
//                 .setup_addresses(lookup_type)
//                 .to_vec()
//                 .into_boxed_slice(),
//         )
//     }
// }

// pub(crate) fn copy_single_base_input_or_materialize_vector<const SINGLE_COLUMN: bool>(
//     input: NoFieldVectorLookupRelation,
// ) -> LookupDenominator {
//     if SINGLE_COLUMN {
//         assert_eq!(input.columns.len(), 1);
//         if input.columns[0].constant == 0
//             && input.columns[0].linear_terms.len() == 1
//             && input.columns[0].linear_terms[0].0 == 1
//         {
//             lookup_nodes::LookupDenominator::UseInputViaCopy(input.columns[0].linear_terms[0].1)
//         } else {
//             let input = NoFieldSingleColumnLookupRelation {
//                 input: input.columns[0].clone(),
//                 lookup_set_index: input.lookup_set_index,
//             };
//             lookup_nodes::LookupDenominator::MaterializeBaseInput(input)
//         }
//     } else {
//         lookup_nodes::LookupDenominator::MaterializeVectorInput(input)
//     }
// }
