use super::*;

use crate::constraint::Constraint;
use crate::constraint::Term;
use crate::cs::circuit::*;
use crate::cs::circuit_output::CircuitOutput;
use crate::cs::circuit_trait::*;
use crate::oracle::*;
use crate::witness_placer::cs_debug_evaluator::CSDebugWitnessEvaluator;
use crate::witness_placer::*;
use std::collections::BTreeMap;
// use crate::devices::optimization_context::OptCtxIndexers;
// use crate::devices::optimization_context::OptimizationContext;
// use crate::tables::LookupWrapper;
// use crate::tables::TableType;
use crate::tables::TableDriver;
use crate::types::*;
use field::PrimeField;
use std::collections::HashMap;
use std::collections::HashSet;
use std::vec;

#[cfg(feature = "debug_evaluate_witness")]
pub const RESOLVE_WITNESS: bool = true;

#[cfg(not(feature = "debug_evaluate_witness"))]
pub const RESOLVE_WITNESS: bool = false;

pub struct BasicAssembly<
    F: PrimeField,
    W: WitnessPlacer<F> = CSDebugWitnessEvaluator<F>,
    const ASSUME_MEMORY_VALUES_ASSIGNED: bool = true,
> {
    no_index_assigned: u64,
    constraint_storage: Vec<(Constraint<F>, bool)>,
    lookup_storage: Vec<LookupQuery<F>>,
    pub memory_queries: Vec<MemoryAccess>,
    boolean_variables: Vec<Variable>,
    rangechecked_expressions: Vec<RangeCheckQuery<F>>,
    placeholder_query: HashMap<(Placeholder, usize), Variable>,
    layers_mapping: HashMap<Variable, usize>,
    table_driver: TableDriver<F>,
    register_and_indirect_memory_accesses: Vec<RegisterAndIndirectAccesses>,
    register_and_indirect_memory_accesses_offset_variables_idxes: HashMap<Variable, usize>,
    executor_machine_state: Option<OpcodeFamilyCircuitState<F>>,
    delegation_circuit_state: Option<DelegationCircuitState>,

    pub witness_placer: Option<W>,
    witness_graph: WitnessResolutionGraph<F, W>,

    pub variable_names: HashMap<Variable, String>,
    variables_from_constraints: BTreeMap<Variable, Constraint<F>>,
    circuit_family_bitmask: Vec<Variable>,
    // logger: Vec<(&'static str, u64, OptCtxIndexers)>,
}

impl<F: PrimeField, W: WitnessPlacer<F>, const ASSUME_MEMORY_VALUES_ASSIGNED: bool> Circuit<F>
    for BasicAssembly<F, W, ASSUME_MEMORY_VALUES_ASSIGNED>
{
    const ASSUME_MEMORY_VALUES_ASSIGNED: bool = ASSUME_MEMORY_VALUES_ASSIGNED;
    type WitnessPlacer = W;

    fn new() -> Self {
        Self {
            no_index_assigned: 0,
            constraint_storage: vec![],
            lookup_storage: vec![],
            memory_queries: vec![],
            boolean_variables: vec![],
            rangechecked_expressions: vec![],
            placeholder_query: HashMap::new(),
            layers_mapping: HashMap::new(),
            table_driver: TableDriver::<F>::new(),

            register_and_indirect_memory_accesses: vec![],
            register_and_indirect_memory_accesses_offset_variables_idxes: HashMap::new(),
            witness_graph: WitnessResolutionGraph::new(),

            executor_machine_state: None,
            delegation_circuit_state: None,

            witness_placer: None,

            variable_names: HashMap::new(),
            variables_from_constraints: BTreeMap::new(),
            circuit_family_bitmask: vec![],
            // logger: vec![],
        }
    }

    #[track_caller]
    fn add_variable(&mut self) -> Variable {
        // if self.no_index_assigned == 11 {
        //     panic!("debug");
        // }
        let location = std::panic::Location::caller();
        let name = format!("Variable at {}::{}", location.file(), location.line());
        self.add_named_variable(&name)
    }

    fn add_named_variable(&mut self, name: &str) -> Variable {
        // if self.no_index_assigned == 11 {
        //     panic!("debug on named variable {}", name);
        // }
        let variable = Variable(self.no_index_assigned);
        self.no_index_assigned += 1;

        self.variable_names.insert(variable, name.to_string());
        self.layers_mapping.insert(variable, 0);

        variable
    }

    #[track_caller]
    fn add_intermediate_variable(&mut self, layer_idx: usize) -> Variable {
        let location = std::panic::Location::caller();
        let name = format!("Variable at {}::{}", location.file(), location.line());
        self.add_intermediate_named_variable(&name, layer_idx)
    }

    fn add_intermediate_named_variable(&mut self, name: &str, layer_idx: usize) -> Variable {
        let variable = Variable(self.no_index_assigned);
        self.no_index_assigned += 1;

        self.variable_names.insert(variable, name.to_string());
        self.layers_mapping.insert(variable, layer_idx);

        variable
    }

    fn set_name_for_variable(&mut self, var: Variable, name: &str) {
        self.variable_names.insert(var, name.to_string());
    }

    fn add_named_variable_from_constraint(
        &mut self,
        mut constraint: Constraint<F>,
        name: &str,
    ) -> Variable {
        assert!(constraint.is_empty() == false);
        assert!(constraint.terms.iter().all(|x| x.is_constant()) == false);
        constraint.normalize();
        let new_var = self.add_named_variable(name);
        // self.variables_from_constraints
        //     .insert(new_var, constraint.clone());

        use crate::cs::utils::collapse_max_quadratic_constraint_into;
        collapse_max_quadratic_constraint_into(self, constraint.clone(), new_var);

        constraint -= Term::from(new_var);
        self.add_constraint(constraint);

        new_var
    }

    fn add_intermediate_named_variable_from_constraint(
        &mut self,
        mut constraint: Constraint<F>,
        name: &str,
    ) -> Variable {
        assert!(constraint.is_empty() == false);
        assert!(constraint.terms.iter().all(|x| x.is_constant()) == false);
        constraint.normalize();
        let mut max_input_layer = isize::MIN;
        let mut all_vars = HashSet::new();
        constraint.dump_variables(&mut all_vars);
        for var in all_vars.into_iter() {
            let layer = *self
                .layers_mapping
                .get(&var)
                .expect("must have layer assigned") as isize;
            if max_input_layer != isize::MIN {
                if layer < max_input_layer {
                    println!(
                        "Variable {:?} will be copied from layer {} to {}",
                        var, layer, max_input_layer
                    );
                }
            }
            max_input_layer = core::cmp::max(max_input_layer, layer);
        }
        assert_ne!(max_input_layer, isize::MIN);
        let new_var = self.add_intermediate_named_variable(name, (max_input_layer as usize) + 1);
        self.variables_from_constraints
            .insert(new_var, constraint.clone());

        // NOTE: even though we did push variable into intermediate layer,
        // we still need to resolve it's witness because it may be a dependency for something else,
        // that can also involve lookups and multiplicity counting

        use crate::cs::utils::collapse_max_quadratic_constraint_into;
        collapse_max_quadratic_constraint_into(self, constraint.clone(), new_var);

        new_var
    }

    #[track_caller]
    fn add_variable_from_constraint_without_witness_evaluation(
        &mut self,
        mut constraint: Constraint<F>,
    ) -> Variable {
        assert!(constraint.is_empty() == false);
        assert!(constraint.terms.iter().all(|x| x.is_constant()) == false);
        constraint.normalize();
        let new_var = self.add_variable();
        // self.variables_from_constraints
        //     .insert(new_var, constraint.clone());

        constraint -= Term::from(new_var);
        self.add_constraint(constraint);

        new_var
    }

    #[track_caller]
    fn add_variable_from_constraint_allow_explicit_linear(
        &mut self,
        mut constraint: Constraint<F>,
    ) -> Variable {
        assert!(constraint.is_empty() == false);
        assert!(constraint.terms.iter().all(|x| x.is_constant()) == false);
        constraint.normalize();
        let new_var = self.add_variable();
        // self.variables_from_constraints
        //     .insert(new_var, constraint.clone());

        use crate::cs::utils::collapse_max_quadratic_constraint_into;
        collapse_max_quadratic_constraint_into(self, constraint.clone(), new_var);

        constraint -= Term::from(new_var);
        self.add_constraint_allow_explicit_linear(constraint);

        new_var
    }

    #[track_caller]
    fn add_variable_from_constraint_allow_explicit_linear_without_witness_evaluation(
        &mut self,
        mut constraint: Constraint<F>,
    ) -> Variable {
        assert!(constraint.is_empty() == false);
        assert!(constraint.terms.iter().all(|x| x.is_constant()) == false);
        constraint.normalize();
        let new_var = self.add_variable();
        // self.variables_from_constraints
        //     .insert(new_var, constraint.clone());

        constraint -= Term::from(new_var);
        self.add_constraint_allow_explicit_linear(constraint);

        new_var
    }

    #[track_caller]
    fn set_values(&mut self, node: impl WitnessResolutionDescription<F, W>) {
        if let Some(witness_placer) = self.witness_placer.as_mut() {
            witness_placer.record_resolver(node.clone_self());
        }
        self.witness_graph.append_inplace(node);
    }

    fn materialize_table<const TOTAL_WIDTH: usize>(&mut self, table_type: TableType) {
        self.table_driver
            .materialize_table::<TOTAL_WIDTH>(table_type);
        if let Some(witness_placer) = self.witness_placer.as_mut() {
            if std::any::TypeId::of::<W>() == std::any::TypeId::of::<CSDebugWitnessEvaluator<F>>() {
                unsafe {
                    let t = (witness_placer as *mut W)
                        .cast::<CSDebugWitnessEvaluator<F>>()
                        .as_mut_unchecked();
                    t.table_driver.materialize_table::<TOTAL_WIDTH>(table_type);
                }
            }
        }
    }

    // fn add_table_with_content(&mut self, table_type: TableType, table: LookupWrapper<F>) {
    //     self.table_driver
    //         .add_table_with_content(table_type, table.clone());
    //     if let Some(witness_placer) = self.witness_placer.as_mut() {
    //         if std::any::TypeId::of::<W>() == std::any::TypeId::of::<CSDebugWitnessEvaluator<F>>() {
    //             unsafe {
    //                 let t = (witness_placer as *mut W)
    //                     .cast::<CSDebugWitnessEvaluator<F>>()
    //                     .as_mut_unchecked();
    //                 t.table_driver.add_table_with_content(table_type, table);
    //             }
    //         }
    //     }
    // }

    #[track_caller]
    fn get_value(&self, var: Variable) -> Option<F> {
        if var.is_placeholder() {
            return None;
        }
        if let Some(witness_placer) = self.witness_placer.as_ref() {
            if std::any::TypeId::of::<W>() == std::any::TypeId::of::<CSDebugWitnessEvaluator<F>>() {
                unsafe {
                    let t = (witness_placer as *const W)
                        .cast::<CSDebugWitnessEvaluator<F>>()
                        .as_ref_unchecked();
                    t.get_value(var)
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    #[track_caller]
    fn add_constraint(&mut self, mut constraint: Constraint<F>) {
        assert!(constraint.degree() == 2, "use `add_constraint_allow_explicit_linear` if you need to make a variable arising from linear constraint");
        assert!(constraint.degree() <= 2);
        constraint.normalize();
        self.try_check_constraint(&constraint);
        self.constraint_storage.push((constraint, false));
    }

    #[track_caller]
    fn add_constraint_allow_explicit_linear(&mut self, mut constraint: Constraint<F>) {
        assert!(constraint.degree() == 1);
        constraint.normalize();
        self.try_check_constraint(&constraint);
        self.constraint_storage.push((constraint, false));
    }

    #[track_caller]
    fn add_constraint_allow_explicit_linear_prevent_optimizations(
        &mut self,
        mut constraint: Constraint<F>,
    ) {
        assert!(constraint.degree() == 1);
        constraint.normalize();
        self.try_check_constraint(&constraint);
        self.constraint_storage.push((constraint, true));
    }

    fn add_constraint_into_intermediate_variable(
        &mut self,
        constraint: Constraint<F>,
        intermediate_var: Variable,
    ) {
        todo!();
    }

    fn request_mem_access(
        &mut self,
        request: MemoryAccessRequest,
        name: &str,
        local_timestamp_in_cycle: u32,
    ) -> MemoryAccess {
        match request {
            MemoryAccessRequest::RegisterRead {
                reg_idx,
                read_value_placeholder,
                split_as_u8,
            } => {
                let read_timestamp = {
                    let vars = std::array::from_fn(|i| {
                        self.add_named_variable(&format!("{}[{}]", name, i))
                    });

                    println!(
                        "Created variables {:?} for mem access {} read timestamp",
                        vars, name
                    );

                    if Self::ASSUME_MEMORY_VALUES_ASSIGNED {
                        let value_fn = move |placer: &mut Self::WitnessPlacer| {
                            for el in vars.iter() {
                                placer.assume_assigned(*el);
                            }
                        };
                        self.set_values(value_fn);
                    } else {
                        let value_fn = move |placer: &mut Self::WitnessPlacer| {
                            let value =
                                placer.get_oracle_u32(Placeholder::ShuffleRamReadTimestamp(
                                    local_timestamp_in_cycle as usize,
                                ));

                            placer.assign_u32_from_u16_parts(vars, &value);
                        };
                        self.set_values(value_fn);
                    }

                    vars
                };

                // no range check is needed here, as our RAM is consistent by itself - our writes(!) are range-checked,
                // so any reads will have to be range-checked
                if split_as_u8 == false {
                    let read_value = Register::new_unchecked_from_placeholder_named(
                        self,
                        read_value_placeholder,
                        name,
                    );
                    let read_value = read_value.0.map(|el| el.get_variable());
                    println!(
                        "Created variables {:?} for mem access {} read value",
                        read_value, name
                    );
                    let read_value = WordRepresentation::U16Limbs(read_value);

                    let access = MemoryAccess::RegisterOnly(RegisterAccess {
                        reg_idx,
                        read_timestamp,
                        read_value: read_value.clone(),
                        write_value: read_value,
                        local_timestamp_in_cycle,
                    });

                    self.memory_queries.push(access.clone());

                    access
                } else {
                    let read_value: [Variable; 4] = std::array::from_fn(|i| {
                        self.add_named_variable(&format!("{}[{}]", name, i))
                    });
                    println!(
                        "Created variables {:?} for mem access {} read value",
                        read_value, name
                    );
                    if Self::ASSUME_MEMORY_VALUES_ASSIGNED {
                        let value_fn = move |placer: &mut Self::WitnessPlacer| {
                            for el in read_value.iter() {
                                placer.assume_assigned(*el);
                            }
                        };
                        self.set_values(value_fn);
                    } else {
                        let value_fn = move |placer: &mut Self::WitnessPlacer| {
                            let value = placer.get_oracle_u32(read_value_placeholder);
                            let low = value.truncate();
                            let high = value.shr(16).truncate();

                            placer.assign_u16_from_u8_parts([read_value[0], read_value[1]], &low);
                            placer.assign_u16_from_u8_parts([read_value[2], read_value[3]], &high);
                        };

                        self.set_values(value_fn);
                    }

                    let read_value = WordRepresentation::U8Limbs(read_value);
                    let access = MemoryAccess::RegisterOnly(RegisterAccess {
                        reg_idx,
                        read_timestamp,
                        read_value: read_value.clone(),
                        write_value: read_value,
                        local_timestamp_in_cycle,
                    });

                    self.memory_queries.push(access.clone());

                    access
                }
            }
            MemoryAccessRequest::RegisterReadWrite {
                reg_idx,
                read_value_placeholder,
                write_value_placeholder,
                split_read_as_u8,
                split_write_as_u8,
            } => {
                // allocate read value

                // no range check is needed here, as our RAM is consistent by itself - our writes(!) are range-checked,
                // so any reads will have to be range-checked
                match (split_read_as_u8, split_write_as_u8) {
                    (false, false) => {
                        let read_value = Register::new_unchecked_from_placeholder_named(
                            self,
                            read_value_placeholder,
                            name,
                        );
                        let read_value = read_value.0.map(|el| el.get_variable());
                        let read_value = WordRepresentation::U16Limbs(read_value);

                        let write_value = Register::new_unchecked_from_placeholder_named(
                            self,
                            write_value_placeholder,
                            name,
                        );
                        let write_value = write_value.0.map(|el| el.get_variable());
                        let write_value = WordRepresentation::U16Limbs(write_value);

                        let read_timestamp = {
                            let vars = std::array::from_fn(|i| {
                                self.add_named_variable(&format!("{}[{}]", name, i))
                            });

                            if Self::ASSUME_MEMORY_VALUES_ASSIGNED {
                                let value_fn = move |placer: &mut Self::WitnessPlacer| {
                                    for el in vars.iter() {
                                        placer.assume_assigned(*el);
                                    }
                                };
                                self.set_values(value_fn);
                            } else {
                                let value_fn = move |placer: &mut Self::WitnessPlacer| {
                                    let value = placer.get_oracle_u32(
                                        Placeholder::ShuffleRamReadTimestamp(
                                            local_timestamp_in_cycle as usize,
                                        ),
                                    );

                                    placer.assign_u32_from_u16_parts(vars, &value);
                                };
                                self.set_values(value_fn);
                            }

                            vars
                        };

                        let access = MemoryAccess::RegisterOnly(RegisterAccess {
                            reg_idx,
                            read_timestamp,
                            read_value,
                            write_value,
                            local_timestamp_in_cycle,
                        });

                        self.memory_queries.push(access.clone());

                        access
                    }
                    _ => {
                        todo!()
                    }
                }
            }
            _ => {
                todo!();
            }
        }
    }

    fn request_register_and_indirect_memory_accesses(
        &mut self,
        request: RegisterAccessRequest,
        name: &str,
        local_timestamp_in_cycle: u32,
    ) -> RegisterAndIndirectAccesses {
        assert!(request.register_index > 0);
        assert!(request.register_index < 32);

        let Some(_delegation_circuit_state) = self.delegation_circuit_state else {
            panic!("Delegation circuit state is not initialized");
        };

        // we always maintain sort
        if let Some(last) = self.register_and_indirect_memory_accesses.last() {
            assert!(
                last.register_index < request.register_index,
                "register accesses must be requested sorted"
            );
        } else {
            // nothing
        }

        let register_index = request.register_index as usize;

        if request.indirects_alignment_log2 < std::mem::align_of::<u32>().trailing_zeros() {
            assert!(request.indirect_accesses.is_empty());
        }

        let register_access = if request.register_write {
            let read_low = self.add_named_variable(&format!("{} read[0]", name));
            let read_high = self.add_named_variable(&format!("{} read[1]", name));

            self.require_invariant(
                read_low,
                Invariant::Substituted((
                    Placeholder::DelegationRegisterReadValue(register_index),
                    0,
                )),
            );
            self.require_invariant(
                read_high,
                Invariant::Substituted((
                    Placeholder::DelegationRegisterReadValue(register_index),
                    1,
                )),
            );

            let value_fn = move |placer: &mut Self::WitnessPlacer| {
                let value =
                    placer.get_oracle_u32(Placeholder::DelegationRegisterReadValue(register_index));
                placer.assign_u32_from_u16_parts([read_low, read_high], &value);
            };
            self.set_values(value_fn);

            let write_low = self.add_named_variable(&format!("{} write[0]", name));
            let write_high = self.add_named_variable(&format!("{} write[0]", name));

            RegisterAccessType::Write {
                read_value: [read_low, read_high],
                write_value: [write_low, write_high],
            }
        } else {
            let read_low = self.add_named_variable(&format!("{} read[0]", name));
            let read_high = self.add_named_variable(&format!("{} read[1]", name));

            self.require_invariant(
                read_low,
                Invariant::Substituted((
                    Placeholder::DelegationRegisterReadValue(register_index),
                    0,
                )),
            );
            self.require_invariant(
                read_high,
                Invariant::Substituted((
                    Placeholder::DelegationRegisterReadValue(register_index),
                    1,
                )),
            );

            let value_fn = move |placer: &mut Self::WitnessPlacer| {
                let value =
                    placer.get_oracle_u32(Placeholder::DelegationRegisterReadValue(register_index));
                placer.assign_u32_from_u16_parts([read_low, read_high], &value);
            };
            self.set_values(value_fn);

            RegisterAccessType::Read {
                read_value: [read_low, read_high],
            }
        };

        let mut indirect_accesses: Vec<IndirectAccessType> = vec![];

        for (indirect_access_idx, access_description) in
            request.indirect_accesses.into_iter().enumerate()
        {
            if let Some((c, _)) = access_description.variable_dependent {
                assert!(
                    c < 1 << 16,
                    "constant multiplier {} is too large and unsupported",
                    c
                );
                assert!(
                    access_description.assume_no_alignment_overflow,
                    "overflowing address generation with variable part is not yet supported"
                );
            }
            if access_description.variable_dependent.is_none() {
                if access_description.assume_no_alignment_overflow {
                    assert!(
                        access_description.offset_constant + (core::mem::size_of::<u32>() as u32)
                            <= (1 << request.indirects_alignment_log2)
                    );
                }
            }
            // make formal witness assignment to placeholder to drive witness resolution
            let variable_dependent = if let Some((off, var)) = access_description.variable_dependent
            {
                if self
                    .register_and_indirect_memory_accesses_offset_variables_idxes
                    .contains_key(&var)
                    == false
                {
                    let idx = self
                        .register_and_indirect_memory_accesses_offset_variables_idxes
                        .len();
                    self.register_and_indirect_memory_accesses_offset_variables_idxes
                        .insert(var, idx);
                    self.require_invariant(
                        var,
                        Invariant::Substituted((
                            Placeholder::DelegationIndirectAccessVariableOffset {
                                variable_index: idx,
                            },
                            0,
                        )),
                    );

                    // it was not used in other accesses, so it needs an oracle value
                    let value_fn = move |placer: &mut Self::WitnessPlacer| {
                        let value = placer.get_oracle_u16(
                            Placeholder::DelegationIndirectAccessVariableOffset {
                                variable_index: idx,
                            },
                        );
                        placer.assign_u16(var, &value);
                    };
                    self.set_values(value_fn);
                }

                Some((
                    off,
                    var,
                    self.register_and_indirect_memory_accesses_offset_variables_idxes
                        .get(&var)
                        .copied()
                        .unwrap(),
                ))
            } else {
                None
            };

            let access = if access_description.is_write_access {
                let read_low = self.add_named_variable(&format!(
                    "{} indirect access {} read[0]",
                    name, indirect_access_idx
                ));
                let read_high = self.add_named_variable(&format!(
                    "{} indirect access {} read[1]",
                    name, indirect_access_idx
                ));

                self.require_invariant(
                    read_low,
                    Invariant::Substituted((
                        Placeholder::DelegationIndirectReadValue {
                            register_index,
                            word_index: indirect_access_idx,
                        },
                        0,
                    )),
                );
                self.require_invariant(
                    read_high,
                    Invariant::Substituted((
                        Placeholder::DelegationIndirectReadValue {
                            register_index,
                            word_index: indirect_access_idx,
                        },
                        1,
                    )),
                );

                let value_fn = move |placer: &mut Self::WitnessPlacer| {
                    let value = placer.get_oracle_u32(Placeholder::DelegationIndirectReadValue {
                        register_index,
                        word_index: indirect_access_idx,
                    });
                    placer.assign_u32_from_u16_parts([read_low, read_high], &value);
                };
                self.set_values(value_fn);

                let write_low = self.add_named_variable(&format!(
                    "{} indirect access {} write[0]",
                    name, indirect_access_idx
                ));
                let write_high = self.add_named_variable(&format!(
                    "{} indirect access {} write[1]",
                    name, indirect_access_idx
                ));

                IndirectAccessType::Write {
                    read_value: [read_low, read_high],
                    write_value: [write_low, write_high],
                    variable_dependent: variable_dependent,
                    offset_constant: access_description.offset_constant,
                    assume_no_alignment_overflow: access_description.assume_no_alignment_overflow,
                }
            } else {
                let read_low = self.add_named_variable(&format!(
                    "{} indirect access {} read[0]",
                    name, indirect_access_idx
                ));
                let read_high = self.add_named_variable(&format!(
                    "{} indirect access {} read[1]",
                    name, indirect_access_idx
                ));

                self.require_invariant(
                    read_low,
                    Invariant::Substituted((
                        Placeholder::DelegationIndirectReadValue {
                            register_index,
                            word_index: indirect_access_idx,
                        },
                        0,
                    )),
                );
                self.require_invariant(
                    read_high,
                    Invariant::Substituted((
                        Placeholder::DelegationIndirectReadValue {
                            register_index,
                            word_index: indirect_access_idx,
                        },
                        1,
                    )),
                );

                let value_fn = move |placer: &mut Self::WitnessPlacer| {
                    let value = placer.get_oracle_u32(Placeholder::DelegationIndirectReadValue {
                        register_index,
                        word_index: indirect_access_idx,
                    });
                    placer.assign_u32_from_u16_parts([read_low, read_high], &value);
                };
                self.set_values(value_fn);

                IndirectAccessType::Read {
                    read_value: [read_low, read_high],
                    variable_dependent: variable_dependent,
                    offset_constant: access_description.offset_constant,
                    assume_no_alignment_overflow: access_description.assume_no_alignment_overflow,
                }
            };

            indirect_accesses.push(access);
        }

        let access = RegisterAndIndirectAccesses {
            register_index: request.register_index,
            indirects_alignment_log2: request.indirects_alignment_log2,
            register_access,
            indirect_accesses,
        };

        self.register_and_indirect_memory_accesses
            .push(access.clone());

        access
    }

    #[track_caller]
    fn enforce_lookup_tuple_for_fixed_table<const M: usize>(
        &mut self,
        inputs: &[LookupInput<F>; M],
        table_type: TableType,
        skip_generating_multiplicity_counting_function: bool,
    ) {
        assert!(M < MAX_TABLE_WIDTH);

        // NOTE: we will add formal witness eval function here to ensure that we can use it for "act of lookup"
        // if we want, and to count multiplicities

        let inputs_vars = inputs.clone();
        let value_fn = move |placer: &mut Self::WitnessPlacer| {
            let input_values: [_; M] = std::array::from_fn(|i| inputs_vars[i].evaluate(placer));
            let table_id =
                <Self::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(table_type as u16);
            placer.lookup_enforce::<M>(&input_values, &table_id);
        };
        if Self::WitnessPlacer::MERGE_LOOKUP_AND_MULTIPLICITY_COUNT
            && skip_generating_multiplicity_counting_function == false
        {
            self.set_values(value_fn);
        }

        let query = LookupQuery {
            row: inputs.to_vec(),
            table: LookupQueryTableType::Constant(table_type),
        };
        self.lookup_storage.push(query);
    }

    #[track_caller]
    fn enforce_lookup_tuple_for_variable_table<const M: usize>(
        &mut self,
        inputs: &[LookupInput<F>; M],
        table_type: Variable,
    ) {
        assert!(M < MAX_TABLE_WIDTH);

        // NOTE: we will add formal witness eval function here to ensure that we can use it for "act of lookup"
        // if we want, and to count multiplicities

        let inputs_vars = inputs.clone();
        let value_fn = move |placer: &mut Self::WitnessPlacer| {
            let input_values: [_; M] = std::array::from_fn(|i| inputs_vars[i].evaluate(placer));
            let table_id = placer.get_u16(table_type);
            placer.lookup_enforce::<M>(&input_values, &table_id);
        };
        if Self::WitnessPlacer::MERGE_LOOKUP_AND_MULTIPLICITY_COUNT {
            self.set_values(value_fn);
        }

        let query = LookupQuery {
            row: inputs.to_vec(),
            table: LookupQueryTableType::Variable(table_type),
        };
        self.lookup_storage.push(query);
    }

    #[track_caller]
    fn enforce_lookup_tuple<const M: usize>(
        &mut self,
        inputs: &[LookupInput<F>; M],
        table_type: LookupQueryTableType<F>,
    ) {
        assert!(M < MAX_TABLE_WIDTH);

        // NOTE: we will add formal witness eval function here to ensure that we can use it for "act of lookup"
        // if we want, and to count multiplicities

        let inputs_vars = inputs.clone();
        let table = table_type.clone();
        let value_fn = move |placer: &mut Self::WitnessPlacer| {
            let table_id = match &table {
                LookupQueryTableType::Constant(table_id) => {
                    <Self::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                        *table_id as u32 as u16,
                    )
                }
                LookupQueryTableType::Variable(var) => placer.get_u16(*var),
                LookupQueryTableType::Expression(input) => {
                    input.evaluate(placer).as_integer().truncate()
                }
            };
            let input_values: [_; M] = std::array::from_fn(|i| inputs_vars[i].evaluate(placer));
            placer.lookup_enforce::<M>(&input_values, &table_id);
        };
        if Self::WitnessPlacer::MERGE_LOOKUP_AND_MULTIPLICITY_COUNT {
            self.set_values(value_fn);
        }

        let query = LookupQuery {
            row: inputs.to_vec(),
            table: table_type,
        };
        self.lookup_storage.push(query);
    }

    #[track_caller]
    fn get_variables_from_lookup_constrained<const M: usize, const N: usize>(
        &mut self,
        inputs: &[LookupInput<F>; M],
        table_type: TableType,
    ) -> [Variable; N] {
        assert!(table_type != TableType::ZeroEntry && table_type != TableType::DynamicPlaceholder);
        let output_variables = std::array::from_fn(|_| self.add_variable());
        self.set_variables_from_lookup_constrained(
            inputs,
            &output_variables,
            LookupQueryTableType::Constant(table_type),
        );

        output_variables
    }

    #[track_caller]
    fn set_variables_from_lookup_constrained<const M: usize, const N: usize>(
        &mut self,
        lookup_inputs: &[LookupInput<F>; M],
        output_variables: &[Variable; N],
        table_type: LookupQueryTableType<F>,
    ) {
        assert!(lookup_inputs.len() > 0);

        let output_variables: [Variable; N] = output_variables.clone();
        let inputs = lookup_inputs.clone();
        let table = table_type.clone();

        let value_fn = move |placer: &mut Self::WitnessPlacer| {
            let table_id = match table {
                LookupQueryTableType::Constant(table_id) => {
                    <Self::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                        table_id as u32 as u16,
                    )
                }
                LookupQueryTableType::Variable(var) => placer.get_u16(var),
                LookupQueryTableType::Expression(..) => {
                    todo!()
                }
            };
            let input_values: [_; M] = std::array::from_fn(|i| inputs[i].evaluate(placer));
            let output_values = placer.lookup::<M, N>(&input_values, &table_id);
            for (var, value) in output_variables.iter().zip(output_values.iter()) {
                placer.assign_field(*var, value);
            }
        };
        self.set_values(value_fn);

        let mut inputs = lookup_inputs.to_vec();
        for el in output_variables.iter() {
            let as_input = LookupInput::Variable(*el);
            inputs.push(as_input);
        }

        let query = LookupQuery {
            row: inputs,
            table: table_type,
        };
        self.lookup_storage.push(query);
    }

    fn require_invariant(&mut self, variable: Variable, invariant: Invariant) {
        match invariant {
            Invariant::Boolean => self.boolean_variables.push(variable),
            Invariant::RangeChecked { width } => {
                assert!(
                    width == 8 || width == 16,
                    "only width 8 and 16 are supported"
                );
                let query = RangeCheckQuery::new(variable, width as usize);
                self.rangechecked_expressions.push(query)
            }
            Invariant::Substituted((placeholder, subindex)) => {
                self.placeholder_query
                    .insert((placeholder, subindex), variable);
            }
        }
    }

    fn allocate_machine_state(
        &mut self,
        need_funct3: bool,
        need_funct7: bool,
        family_bitmask_size: usize,
    ) -> (OpcodeFamilyCircuitState<F>, Vec<Variable>) {
        assert!(need_funct7 == false);

        // Variables will be allocated with all the corresponding guarantees,
        // and circuit should use them in constraints and make witness values if necessary

        // NOTE: We should make most of the variables below as substituted placeholders,
        // to formally recognize them as inputs for witness-evals

        // PC - by induction we start with 0, and then always adjust using range checks (and 0 mod 4),
        // so we can allocate from witness and allow permutation argument to take care of correct range
        let initial_pc: [Variable; 2] =
            std::array::from_fn(|i| self.add_named_variable(&format!("initial_pc[{}]", i)));
        initial_pc.iter().enumerate().for_each(|(i, el)| {
            self.require_invariant(*el, Invariant::Substituted((Placeholder::PcInit, i)))
        });

        // Same for timestamps - those are incremented with a proper range check in the execution circuits
        let initial_timestamp: [Variable; NUM_TIMESTAMP_COLUMNS_FOR_RAM] =
            std::array::from_fn(|i| self.add_named_variable(&format!("initial_ts[{}]", i)));
        initial_timestamp.iter().enumerate().for_each(|(i, el)| {
            self.require_invariant(
                *el,
                Invariant::Substituted((Placeholder::OpcodeFamilyCycleInitialTimestamp, i)),
            )
        });

        let cycle_start_state = MachineCycleStartOrEndState {
            pc: initial_pc,
            timestamp: initial_timestamp,
            _marker: std::marker::PhantomData,
        };

        // variables for decoder are not checked at all, and circuit will be responsible to properly constraint
        // them

        // NOTE: Ideally compiler should take care of this boolean check, but there is no nice place in quotient to put it,
        // so we will add constraints
        let execute = self.add_named_variable("Execute flag for cycle");
        self.require_invariant(
            execute,
            Invariant::Substituted((Placeholder::ExecuteOpcodeFamilyCycle, 0)),
        );
        use crate::constraint::Term;
        self.add_constraint((Term::from(execute) - Term::from(1u32)) * Term::from(execute));

        let mut decoder_data: DecoderData<F> = DecoderData {
            rs1_index: self.add_named_variable("rs1 index from decoder"),
            rs2_index: self.add_named_variable("rs2 index from decoder"),
            rd_index: self.add_named_variable("rd index from decoder"),
            imm: std::array::from_fn(|i| {
                self.add_named_variable(&format!("imm[{}] from decoder", i))
            }),
            funct3: if need_funct3 {
                Some(self.add_named_variable("funct3 from decoder"))
            } else {
                None
            },
            funct7: None,
            circuit_family_extra_mask: Variable::placeholder_variable(),
            circuit_family_mask_bits: Vec::new(),
            _marker: std::marker::PhantomData,
        };

        self.require_invariant(
            decoder_data.rs1_index,
            Invariant::Substituted((Placeholder::RS1Index, 0)),
        );
        self.require_invariant(
            decoder_data.rs2_index,
            Invariant::Substituted((Placeholder::RS2Index, 0)),
        );
        self.require_invariant(
            decoder_data.rd_index,
            Invariant::Substituted((Placeholder::RDIndex, 0)),
        );
        decoder_data.imm.iter().enumerate().for_each(|(i, el)| {
            self.require_invariant(*el, Invariant::Substituted((Placeholder::DecodedImm, i)))
        });
        if need_funct3 {
            self.require_invariant(
                decoder_data.funct3.unwrap(),
                Invariant::Substituted((Placeholder::DecodedFunct3, 0)),
            );
        }
        self.require_invariant(
            decoder_data.circuit_family_extra_mask,
            Invariant::Substituted((Placeholder::DecodedExecutorFamilyMask, 0)),
        );

        let mut circuit_family_bitmask = Vec::with_capacity(family_bitmask_size);
        for i in 0..family_bitmask_size {
            let bitmask_el = self.add_named_boolean_variable(&format!("family_bit[{}]", i));
            self.require_invariant(
                bitmask_el.get_variable().unwrap(),
                Invariant::Substituted((Placeholder::ExecutorFamilyMaskBit { bit: i }, 0)),
            );
            circuit_family_bitmask.push(bitmask_el.get_variable().unwrap());
        }

        decoder_data.circuit_family_mask_bits = circuit_family_bitmask.clone();

        let t = circuit_family_bitmask.clone();
        let value_fn = move |placer: &mut Self::WitnessPlacer| {
            for el in t.iter() {
                placer.assume_assigned(*el);
            }
        };
        self.set_values(value_fn);

        // we can also attach initial witness here - we need initial PC and decoder
        let t = decoder_data.clone();
        let value_fn = move |placer: &mut Self::WitnessPlacer| {
            let initial_pc_value = placer.get_oracle_u32(Placeholder::PcInit);
            placer.assign_u32_from_u16_parts(initial_pc, &initial_pc_value);

            placer.spec_decoder_relation(initial_pc, &t);
        };
        self.set_values(value_fn);

        // not make a final state - opcode family circuit is reponsible to create a PC,
        // and timestamps bump comes from compiler

        let final_pc: [Variable; 2] =
            std::array::from_fn(|i| self.add_named_variable(&format!("final_pc[{}]", i)));
        final_pc.iter().enumerate().for_each(|(i, el)| {
            self.require_invariant(*el, Invariant::Substituted((Placeholder::PcFin, i)))
        });

        let final_timestamp: [Variable; NUM_TIMESTAMP_COLUMNS_FOR_RAM] =
            std::array::from_fn(|i| self.add_named_variable(&format!("final_ts[{}]", i)));
        final_timestamp.iter().enumerate().for_each(|(i, el)| {
            self.require_invariant(
                *el,
                Invariant::Substituted((Placeholder::OpcodeFamilyCycleFinalTimestamp, i)),
            )
        });

        let cycle_end_state = MachineCycleStartOrEndState {
            pc: final_pc,
            timestamp: final_timestamp,
            _marker: std::marker::PhantomData,
        };

        // we also mark timestamps as formally assigned - those are resolved in prover
        let value_fn = move |placer: &mut Self::WitnessPlacer| {
            placer.assume_assigned(execute);

            placer.assume_assigned(cycle_start_state.timestamp[0]);
            placer.assume_assigned(cycle_start_state.timestamp[1]);

            placer.assume_assigned(cycle_end_state.timestamp[0]);
            placer.assume_assigned(cycle_end_state.timestamp[1]);
        };
        self.set_values(value_fn);

        let state = OpcodeFamilyCircuitState {
            execute,
            cycle_start_state,
            decoder_data,
            cycle_end_state,
        };

        self.executor_machine_state = Some(state.clone());
        self.circuit_family_bitmask = circuit_family_bitmask.clone();

        (state, circuit_family_bitmask)
    }

    fn allocate_delegation_state(
        &mut self,
        delegation_type: u16,
    ) -> (Variable, [Variable; NUM_TIMESTAMP_COLUMNS_FOR_RAM]) {
        assert!(self.delegation_circuit_state.is_none());
        let execute = self.add_named_variable("Execute flag for cycle");
        self.require_invariant(
            execute,
            Invariant::Substituted((Placeholder::ExecuteDelegation, 0)),
        );
        use crate::constraint::Term;
        self.add_constraint((Term::from(execute) - Term::from(1u32)) * Term::from(execute));

        let invocation_timestamp: [Variable; NUM_TIMESTAMP_COLUMNS_FOR_RAM] =
            std::array::from_fn(|i| {
                self.add_named_variable(&format!("delegation_invocation_ts[{}]", i))
            });
        invocation_timestamp.iter().enumerate().for_each(|(i, el)| {
            self.require_invariant(
                *el,
                Invariant::Substituted((Placeholder::DelegationWriteTimestamp, i)),
            )
        });

        let value_fn = move |placer: &mut Self::WitnessPlacer| {
            let execute_flag_value = placer.get_oracle_boolean(Placeholder::ExecuteDelegation);
            placer.assign_mask(execute, &execute_flag_value);
            placer.assume_assigned(invocation_timestamp[0]);
            placer.assume_assigned(invocation_timestamp[1]);
        };
        self.set_values(value_fn);

        self.delegation_circuit_state = Some(DelegationCircuitState {
            delegation_type,
            execute,
            invocation_timestamp,
        });

        (execute, invocation_timestamp)
    }

    // fn set_log(&mut self, opt_ctx: &OptimizationContext<F, Self>, name: &'static str) {
    //     if ENABLE_LOGGING {
    //         self.logger
    //             .push((name, self.no_index_assigned, opt_ctx.save_indexers()));
    //     }
    // }

    // fn view_log(&self, name: &'static str) {
    //     if ENABLE_LOGGING {
    //         // first the chronological order
    //         let mut logger = self.logger.clone();
    //         let total_vars = logger.last().unwrap().1;
    //         for i in (1..logger.len()).rev() {
    //             logger[i].1 -= logger[i - 1].1;
    //         }
    //         println!();
    //         println!("PERFORMANCE FOR {name} IN ORDER OF EXECUTION (# of vars)");
    //         for &(name, vars, indexers) in &logger {
    //             let OptCtxIndexers {
    //                 register_allocation_indexer,
    //                 add_sub_indexer,
    //                 u16_to_u8x2_decomposition_indexer,
    //                 u16_range_check_indexer,
    //                 mul_div_indexer,
    //                 lookup_indexer,
    //                 lookup_outputs_indexer,
    //                 zero_indexer,
    //             } = indexers;
    //             if name == "EXECUTOR" || name == "DECODER" || name == "OPT_CONTEXT" {
    //                 println!("{name:.<20}{vars:.>3}");
    //             } else {
    //                 println!("{name:.<20}{vars:.>3} ({add_sub_indexer} addsub, {u16_to_u8x2_decomposition_indexer} u16tou8, {u16_range_check_indexer} u16, {mul_div_indexer} muldiv, {zero_indexer} iszero, {lookup_indexer} lookup, {lookup_outputs_indexer} lookup output, {register_allocation_indexer} reg)");
    //             }
    //         }
    //         println!("TOTAL {total_vars:.>3}");

    //         // now the sorting / relative order
    //         println!();
    //         logger.sort_by_key(|tuple| tuple.1);
    //         let percentages = logger
    //             .iter()
    //             .map(|&(_, vars, _)| vars as f32 * 100. / total_vars as f32)
    //             .collect::<Vec<f32>>();
    //         assert!(percentages.iter().sum::<f32>() > 99.9);
    //         println!("RELATIVE PERFORMANCE FOR {name}");
    //         for (&(name, vars, _), &perc) in logger.iter().zip(&percentages) {
    //             let big = "#".repeat(perc as usize);
    //             let small = ".".repeat((perc * 10.) as usize % 10);
    //             let combined = big + &small;
    //             println!("{name:>20} {perc:4.1}% ({vars:2}) {combined:50}");
    //         }
    //         println!("");
    //     }
    // }

    fn finalize(mut self) -> (CircuitOutput<F>, Option<W>) {
        // Out default behavior is to enforce 8-bit range-checks in the same way as generic lookups.
        // Later on the compiler will place the variables, but we will add corresponding lookup queries

        let range_check_8_elements: Vec<_> = self
            .rangechecked_expressions
            .iter()
            .filter(|el| el.width == SMALL_RANGE_CHECK_TABLE_WIDTH)
            .cloned()
            .collect();
        let num_range_check_8 = range_check_8_elements.len();

        let mut range_check_8_iter = range_check_8_elements.into_iter();

        for _ in 0..(num_range_check_8.next_multiple_of(2) / 2) {
            let first_input = range_check_8_iter.next().unwrap();
            let LookupInput::Variable(first_input) = first_input.input else {
                unimplemented!()
            };
            if let Some(second_input) = range_check_8_iter.next() {
                let LookupInput::Variable(second_input) = second_input.input else {
                    unimplemented!()
                };
                // we make an input of [first, second, 0]

                let first_input = LookupInput::Variable(first_input);
                let second_input = LookupInput::Variable(second_input);
                self.enforce_lookup_tuple_for_fixed_table(
                    &[first_input, second_input, LookupInput::empty()],
                    TableType::RangeCheck8x8,
                    false,
                );
            } else {
                // we make an input of [first, 0, 0]
                let first_input = LookupInput::Variable(first_input);
                self.enforce_lookup_tuple_for_fixed_table(
                    &[first_input, LookupInput::empty(), LookupInput::empty()],
                    TableType::RangeCheck8x8,
                    false,
                );
            }
        }

        let BasicAssembly {
            no_index_assigned,
            constraint_storage,
            lookup_storage,
            boolean_variables,
            rangechecked_expressions,
            placeholder_query,
            table_driver,
            memory_queries,
            register_and_indirect_memory_accesses,
            executor_machine_state,
            delegation_circuit_state,
            variable_names,
            circuit_family_bitmask,
            variables_from_constraints,
            layers_mapping,
            ..
        } = self;

        let output = CircuitOutput {
            memory_queries,
            table_driver,
            num_of_variables: no_index_assigned as usize,
            constraints: constraint_storage,
            layers_mapping,
            lookups: lookup_storage,
            range_check_expressions: rangechecked_expressions,
            boolean_vars: boolean_variables,
            substitutions: placeholder_query,
            register_and_indirect_memory_accesses,
            executor_machine_state,
            delegation_circuit_state,
            variable_names,
            circuit_family_bitmask,
            variables_from_constraints,
        };

        (output, self.witness_placer)
    }

    fn is_satisfied(&mut self) -> bool {
        if let Some(witness_placer) = self.witness_placer.as_ref() {
            if std::any::TypeId::of::<W>() == std::any::TypeId::of::<CSDebugWitnessEvaluator<F>>() {
                unsafe {
                    let resolver = (witness_placer as *const W)
                        .cast::<CSDebugWitnessEvaluator<F>>()
                        .as_ref_unchecked();

                    // there could be cases when conditional branches were not taken,
                    // and our routines above just would not mark variable as resolved for that reason,
                    // so we can still assume that all unresolved are 0s below

                    for (constraint, _) in self.constraint_storage.iter() {
                        let (quad, linear, constant) = constraint.clone().split_max_quadratic();
                        let mut value = constant;
                        for (coeff, a, b) in quad.into_iter() {
                            let mut t = coeff;

                            // let a_value = resolver.get_value(a).unwrap_or(F::ZERO);
                            // t.mul_assign(&a_value);
                            // let b_value = resolver.get_value(b).unwrap_or(F::ZERO);
                            // t.mul_assign(&b_value);

                            let Some(a_value) = resolver.get_value(a) else {
                                panic!("Variable {:?} left unresolved", a);
                            };
                            t.mul_assign(&a_value);
                            let Some(b_value) = resolver.get_value(b) else {
                                panic!("Variable {:?} left unresolved", b);
                            };
                            t.mul_assign(&b_value);

                            value.add_assign(&t);
                        }
                        for (coeff, a) in linear.into_iter() {
                            let mut t = coeff;

                            // let a_value = resolver.get_value(a).unwrap_or(F::ZERO);
                            // t.mul_assign(&a_value);

                            let Some(a_value) = resolver.get_value(a) else {
                                panic!("Variable {:?} left unresolved", a);
                            };
                            t.mul_assign(&a_value);

                            value.add_assign(&t);
                        }

                        if value != F::ZERO {
                            println!(
                                "[{}:{}] unsatisfied at constraint {constraint:?} with value {value:?}",
                                file!(), line!()
                            );
                            return false;
                        }
                    }

                    return true;
                }
            }
        }

        true
    }
}

impl<F: PrimeField, W: WitnessPlacer<F>, const ASSUME_MEMORY_VALUES_ASSIGNED: bool>
    BasicAssembly<F, W, ASSUME_MEMORY_VALUES_ASSIGNED>
{
    #[track_caller]
    fn try_check_constraint(&self, constraint: &Constraint<F>) {
        if let Some(witness_placer) = self.witness_placer.as_ref() {
            if std::any::TypeId::of::<W>() == std::any::TypeId::of::<CSDebugWitnessEvaluator<F>>() {
                unsafe {
                    let resolver = (witness_placer as *const W)
                        .cast::<CSDebugWitnessEvaluator<F>>()
                        .as_ref_unchecked();

                    let (quad, linear, constant) = constraint.clone().split_max_quadratic();
                    let mut value = constant;
                    for (coeff, a, b) in quad.into_iter() {
                        let mut t = coeff;
                        let Some(a) = resolver.get_value(a) else {
                            println!("Variable {:?} is unresolved", a);
                            return;
                        };
                        let Some(b) = resolver.get_value(b) else {
                            println!("Variable {:?} is unresolved", b);
                            return;
                        };
                        t.mul_assign(&a);
                        t.mul_assign(&b);

                        value.add_assign(&t);
                    }
                    for (coeff, a) in linear.into_iter() {
                        let mut t = coeff;
                        let Some(a) = resolver.get_value(a) else {
                            println!("Variable {:?} is unresolved", a);
                            return;
                        };
                        t.mul_assign(&a);

                        value.add_assign(&t);
                    }

                    if value != F::ZERO {
                        panic!(
                            "unsatisfied at constraint {:?} with value {:?}",
                            constraint, value
                        );
                    }
                }
            }
        }
    }
}

impl<F: PrimeField> BasicAssembly<F, CSDebugWitnessEvaluator<F>, false> {
    pub fn new_with_oracle<O: Oracle<F> + 'static>(oracle: O) -> Self {
        let mut new = Self::new();
        new.witness_placer = Some(CSDebugWitnessEvaluator::new_with_oracle(oracle));

        new
    }

    pub fn new_with_oracle_and_preprocessed_decoder<O: Oracle<F> + 'static>(
        oracle: O,
        preprocessed_decoder_table: Vec<crate::gkr_circuits::ExecutorFamilyDecoderData>,
    ) -> Self {
        let mut new = Self::new();
        new.witness_placer = Some(
            CSDebugWitnessEvaluator::new_with_oracle_and_preprocessed_decoder(
                oracle,
                preprocessed_decoder_table,
            ),
        );

        new
    }
}
