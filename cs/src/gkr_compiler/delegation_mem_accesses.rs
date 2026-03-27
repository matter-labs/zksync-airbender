use super::*;
use crate::constraint::{Constraint, Term};
use crate::cs::circuit::{
    IndirectAccessType, RangeCheckQuery, RegisterAccessType, RegisterAndIndirectAccesses,
};
use crate::cs::circuit_trait::{
    ConstantRegisterAccess, MemoryAccess, RegisterIndirectRamAccess, WordRepresentation,
};
use crate::definitions::gkr::{
    IndirectRamAccessAddress, RamAddress, RamQuery, RamReadQuery, RamWriteQuery,
};
use crate::definitions::LookupInput;
use crate::gkr_compiler::graph::GKRGraph;

const LOCAL_TIMESTAMP_FOR_INDIRECTS: u32 = 2;

pub(crate) fn compile_register_and_indirect_mem_accesses<F: PrimeField>(
    graph: &mut GKRGraph,
    num_variables: &mut u64,
    all_variables_to_place: &mut BTreeSet<Variable>,
    layers_mapping: &mut HashMap<Variable, usize>,
    boolean_vars: &mut Vec<Variable>,
    accesses: Vec<RegisterAndIndirectAccesses>,
    variable_names: &mut HashMap<Variable, String>,
    ram_access_sets: &mut Vec<RamQuery>,
    ram_augmented_sets: &mut Vec<(MemoryAccess, ShuffleRamTimestampComparisonPartialData)>,
    indirect_access_variable_offsets: &mut BTreeMap<usize, GKRAddress>,
    range_check_expressions: &mut Vec<RangeCheckQuery<F>>,
) {
    for (query_idx, memory_query) in accesses.clone().into_iter().enumerate() {
        let RegisterAndIndirectAccesses {
            register_index,
            register_access,
            indirects_alignment_log2,
            indirect_accesses,
        } = memory_query;
        let [read_timestamp_low, read_timestamp_high] = std::array::from_fn(|_| {
            add_compiler_defined_base_layer_variable(
                num_variables,
                all_variables_to_place,
                layers_mapping,
            )
        });
        variable_names.insert(
            read_timestamp_low,
            format!("ram or indirect query {}, register read_ts[0]", query_idx),
        );
        variable_names.insert(
            read_timestamp_high,
            format!("ram or indirect query {}, register read_ts[1]", query_idx),
        );
        let read_timestamp = graph.layout_memory_subtree_multiple_variables(
            [read_timestamp_low, read_timestamp_high],
            all_variables_to_place,
            layers_mapping,
        );
        let borrow_var = {
            // now that we have declared timestamps, we can produce comparison expressions for range checks
            let borrow_var = add_compiler_defined_base_layer_variable(
                num_variables,
                all_variables_to_place,
                layers_mapping,
            );
            boolean_vars.push(borrow_var);
            variable_names.insert(
                borrow_var,
                format!(
                    "indirect access query {}, register acccess interm ts borrow",
                    query_idx
                ),
            );

            borrow_var
        };

        let (register_read_value, register_write_value) = match register_access {
            RegisterAccessType::Read { read_value } => (read_value, read_value),
            RegisterAccessType::Write {
                read_value,
                write_value,
            } => (read_value, write_value),
        };
        let register_ram_query = MemoryAccess::ConstantRegister(ConstantRegisterAccess {
            reg_idx: register_index as u16,
            read_timestamp: [read_timestamp_low, read_timestamp_high],
            read_value: WordRepresentation::U16Limbs(register_read_value),
            write_value: WordRepresentation::U16Limbs(register_write_value),
            local_timestamp_in_cycle: LOCAL_TIMESTAMP_FOR_INDIRECTS,
        });
        let partial_data = ShuffleRamTimestampComparisonPartialData {
            intermediate_borrow: borrow_var,
            read_timestamp: [read_timestamp_low, read_timestamp_high],
            local_timestamp_in_cycle: LOCAL_TIMESTAMP_FOR_INDIRECTS as usize,
        };
        ram_augmented_sets.push((register_ram_query.clone(), partial_data));

        let read_timestamp = read_timestamp.map(|el| {
            let GKRAddress::BaseLayerMemory(el) = el else {
                unreachable!()
            };

            el
        });

        let register_read_value_vars = register_read_value;
        let (register_read_value, register_read_value_raw) = match register_ram_query.read_value() {
            WordRepresentation::U16Limbs(read_value) => {
                let read_value = graph.layout_memory_subtree_multiple_variables(
                    read_value,
                    all_variables_to_place,
                    layers_mapping,
                );
                let read_value = read_value.map(|el| {
                    let GKRAddress::BaseLayerMemory(el) = el else {
                        unreachable!()
                    };

                    el
                });

                (RamWordRepresentation::U16Limbs(read_value), read_value)
            }
            _ => {
                unreachable!()
            }
        };

        let register_address = RamAddress::ConstantRegister(register_index as u16);
        let query_columns = if register_ram_query.is_readonly() {
            assert_eq!(
                register_ram_query.read_value(),
                register_ram_query.write_value()
            );

            let query_columns = RamReadQuery {
                in_cycle_write_index: register_ram_query.local_timestamp_in_cycle(),
                address: register_address,
                read_timestamp,
                read_value: register_read_value,
            };

            RamQuery::Readonly(query_columns)
        } else {
            let write_value = match register_ram_query.write_value() {
                WordRepresentation::U16Limbs(write_value) => {
                    let write_value = graph.layout_memory_subtree_multiple_variables(
                        write_value,
                        all_variables_to_place,
                        layers_mapping,
                    );
                    let write_value = write_value.map(|el| {
                        let GKRAddress::BaseLayerMemory(el) = el else {
                            unreachable!()
                        };

                        el
                    });

                    RamWordRepresentation::U16Limbs(write_value)
                }
                _ => {
                    unreachable!()
                }
            };
            let query_columns = RamWriteQuery {
                in_cycle_write_index: register_ram_query.local_timestamp_in_cycle(),
                address: register_address,
                read_timestamp,
                read_value: register_read_value,
                write_value,
            };

            RamQuery::Write(query_columns)
        };

        ram_access_sets.push(query_columns);
        drop(register_ram_query);

        if indirects_alignment_log2 != 0 {
            assert!(indirects_alignment_log2 < 16);
            assert!(indirect_accesses.len() > 0);
            // permutation check will ensure that the value is 16 bits, so we just need to shift it right and
            // range check again
            let constraint = Constraint::empty()
                + Term::from((
                    F::from_u32_unchecked(1 << indirects_alignment_log2)
                        .inverse()
                        .unwrap(),
                    register_read_value_vars[0],
                ));
            range_check_expressions.push(RangeCheckQuery::new_for_input(
                LookupInput::from(constraint),
                16,
            ));
        }

        // and now complex part - indirects
        for (indirect_access_idx, indirect_access) in indirect_accesses.into_iter().enumerate() {
            assert!(indirect_access.consider_aligned());
            let constant_offset = indirect_access.offset_constant();
            let variable_offset = indirect_access.variable_dependent();
            // (offset, var, indirect_access_var_idx)

            let [read_timestamp_low, read_timestamp_high] = std::array::from_fn(|_| {
                add_compiler_defined_base_layer_variable(
                    num_variables,
                    all_variables_to_place,
                    layers_mapping,
                )
            });
            variable_names.insert(
                read_timestamp_low,
                format!(
                    "indirect query {}, indirect access {} read_ts[0]",
                    query_idx, indirect_access_idx
                ),
            );
            variable_names.insert(
                read_timestamp_high,
                format!(
                    "indirect query {}, indirect access {} read_ts[1]",
                    query_idx, indirect_access_idx
                ),
            );
            let read_timestamp = graph.layout_memory_subtree_multiple_variables(
                [read_timestamp_low, read_timestamp_high],
                all_variables_to_place,
                layers_mapping,
            );
            let borrow_var = {
                // now that we have declared timestamps, we can produce comparison expressions for range checks
                let borrow_var = add_compiler_defined_base_layer_variable(
                    num_variables,
                    all_variables_to_place,
                    layers_mapping,
                );
                boolean_vars.push(borrow_var);
                variable_names.insert(
                    borrow_var,
                    format!(
                        "indirect access query {}, indirect acccess {} interm ts borrow",
                        query_idx, indirect_access_idx
                    ),
                );

                borrow_var
            };

            // now place read value and write value if needed
            let indirect_read_value = indirect_access.read_value();
            let indirect_write_value = if let Some(write_value) = indirect_access.write_value() {
                write_value
            } else {
                indirect_read_value
            };
            let indirect_ram_query = MemoryAccess::RamIndirect(RegisterIndirectRamAccess {
                variable_offset: variable_offset,
                base_address: register_read_value_vars,
                constant_offset,
                read_timestamp: [read_timestamp_low, read_timestamp_high],
                read_value: WordRepresentation::U16Limbs(indirect_read_value),
                write_value: WordRepresentation::U16Limbs(indirect_write_value),
                local_timestamp_in_cycle: LOCAL_TIMESTAMP_FOR_INDIRECTS,
            });
            let partial_data = ShuffleRamTimestampComparisonPartialData {
                intermediate_borrow: borrow_var,
                read_timestamp: [read_timestamp_low, read_timestamp_high],
                local_timestamp_in_cycle: LOCAL_TIMESTAMP_FOR_INDIRECTS as usize,
            };
            ram_augmented_sets.push((indirect_ram_query.clone(), partial_data));

            let read_timestamp = read_timestamp.map(|el| {
                let GKRAddress::BaseLayerMemory(el) = el else {
                    unreachable!()
                };

                el
            });

            let indirect_read_value_vars = indirect_read_value;
            let indirect_read_value = {
                let read_value = graph.layout_memory_subtree_multiple_variables(
                    indirect_read_value,
                    all_variables_to_place,
                    layers_mapping,
                );
                let read_value = read_value.map(|el| {
                    let GKRAddress::BaseLayerMemory(el) = el else {
                        unreachable!()
                    };

                    el
                });

                RamWordRepresentation::U16Limbs(read_value)
            };

            let variable_offset_compiled = if let Some((offset, var, indirect_access_var_idx)) =
                variable_offset
            {
                assert!(offset < 1 << 16);
                let offset_place = if let Some(offset_place) = graph.get_fixed_layout_pos(&var) {
                    offset_place
                } else {
                    let [offset_place] = graph.layout_memory_subtree_multiple_variables(
                        [var],
                        all_variables_to_place,
                        layers_mapping,
                    );
                    offset_place
                };

                dbg!(query_idx);
                dbg!(indirect_access_idx);
                dbg!(indirect_access_var_idx);
                dbg!(offset);
                dbg!(&offset_place);

                let existing =
                    indirect_access_variable_offsets.insert(indirect_access_var_idx, offset_place);
                if let Some(existing) = existing {
                    assert_eq!(existing, offset_place);
                }
                // assert!(existing.is_none(), "duplicate variable for indirect access variable part index {}: inserting {:?}, but {:?} was present already", indirect_access_var_idx, offset_place, existing.unwrap());
                let GKRAddress::BaseLayerMemory(offset_place) = offset_place else {
                    unreachable!()
                };

                Some((offset as u16, offset_place))
            } else {
                None
            };

            let address = RamAddress::IndirectRam(IndirectRamAccessAddress {
                base_register_value: register_read_value_raw,
                base_register_index: register_index as u16,
                constant_offset: constant_offset as u16,
                variable_offset: variable_offset_compiled,
                indirect_access_idx_for_register: indirect_access_idx,
            });

            let query_columns = if indirect_ram_query.is_readonly() {
                assert_eq!(
                    indirect_ram_query.read_value(),
                    indirect_ram_query.write_value()
                );

                let query_columns = RamReadQuery {
                    in_cycle_write_index: indirect_ram_query.local_timestamp_in_cycle(),
                    address,
                    read_timestamp,
                    read_value: indirect_read_value,
                };

                RamQuery::Readonly(query_columns)
            } else {
                let indirect_write_value = match indirect_ram_query.write_value() {
                    WordRepresentation::U16Limbs(write_value) => {
                        let write_value = graph.layout_memory_subtree_multiple_variables(
                            write_value,
                            all_variables_to_place,
                            layers_mapping,
                        );
                        let write_value = write_value.map(|el| {
                            let GKRAddress::BaseLayerMemory(el) = el else {
                                unreachable!()
                            };

                            el
                        });

                        RamWordRepresentation::U16Limbs(write_value)
                    }
                    _ => {
                        unreachable!()
                    }
                };
                let query_columns = RamWriteQuery {
                    in_cycle_write_index: indirect_ram_query.local_timestamp_in_cycle(),
                    address,
                    read_timestamp,
                    read_value: indirect_read_value,
                    write_value: indirect_write_value,
                };

                RamQuery::Write(query_columns)
            };

            ram_access_sets.push(query_columns);
        }
    }
}
