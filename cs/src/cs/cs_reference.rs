use super::witness_placer::cs_debug_evaluator::CSDebugWitnessEvaluator;
use super::witness_placer::*;
use super::*;

use super::oracle::Oracle;
use crate::constraint::Constraint;
use crate::cs::circuit::*;
use crate::cs::placeholder::Placeholder;
use crate::devices::optimization_context::OptCtxIndexers;
use crate::devices::optimization_context::OptimizationContext;
use crate::tables::LookupWrapper;
use crate::tables::TableDriver;
use crate::tables::TableType;
use crate::types::*;
use field::PrimeField;
use std::collections::HashMap;
use std::vec;

#[cfg(feature = "debug_evaluate_witness")]
pub const RESOLVE_WITNESS: bool = true;

#[cfg(not(feature = "debug_evaluate_witness"))]
pub const RESOLVE_WITNESS: bool = false;

pub struct BasicAssembly<F: PrimeField, W: WitnessPlacer<F> = CSDebugWitnessEvaluator<F>> {
    no_index_assigned: u64,
    constraint_storage: Vec<(Constraint<F>, bool)>,
    lookup_storage: Vec<LookupQuery<F>>,
    pub shuffle_ram_queries: Vec<ShuffleRamMemQuery>,
    boolean_variables: Vec<Variable>,
    rangechecked_expressions: Vec<RangeCheckQuery<F>>,
    placeholder_query: HashMap<(Placeholder, usize), Variable>,
    linkage_queries: Vec<LinkedVariablesPair>,
    table_driver: TableDriver<F>,
    delegated_computation_requests: Vec<DelegatedComputationRequest>,
    degegated_request_to_process: Option<DelegatedProcessingData>,
    batched_memory_accesses: Vec<BatchedMemoryAccessType>,
    register_and_indirect_memory_accesses: Vec<RegisterAndIndirectAccesses>,

    pub witness_placer: Option<W>,
    witness_graph: WitnessResolutionGraph<F, W>,

    logger: Vec<(&'static str, u64, OptCtxIndexers)>,
}

impl<F: PrimeField, W: WitnessPlacer<F>> Circuit<F> for BasicAssembly<F, W> {
    type WitnessPlacer = W;

    fn new() -> Self {
        Self {
            no_index_assigned: 0,
            constraint_storage: vec![],
            lookup_storage: vec![],
            shuffle_ram_queries: vec![],
            boolean_variables: vec![],
            rangechecked_expressions: vec![],
            placeholder_query: HashMap::new(),
            linkage_queries: vec![],
            table_driver: TableDriver::<F>::new(),
            delegated_computation_requests: vec![],
            degegated_request_to_process: None,
            batched_memory_accesses: vec![],
            register_and_indirect_memory_accesses: vec![],
            witness_graph: WitnessResolutionGraph::new(),

            witness_placer: None,

            logger: vec![],
        }
    }

    #[track_caller]
    fn add_variable(&mut self) -> Variable {
        // if self.no_index_assigned == 203 {
        //     panic!("debug");
        // }
        let variable = Variable(self.no_index_assigned);
        self.no_index_assigned += 1;

        variable
    }

    fn add_constant_variable(&mut self, _fr: F) -> Variable {
        unimplemented!("unlikely needed for our circuits");
    }

    #[track_caller]
    fn set_values(&mut self, node: impl WitnessResolutionDescription<F, W>) {
        if let Some(witness_placer) = self.witness_placer.as_mut() {
            witness_placer.record_resolver(node.clone_self());
        }
        self.witness_graph.append_inplace(node);
    }

    fn materialize_table(&mut self, table_type: TableType) {
        self.table_driver.materialize_table(table_type);
        if let Some(witness_placer) = self.witness_placer.as_mut() {
            if std::any::TypeId::of::<W>() == std::any::TypeId::of::<CSDebugWitnessEvaluator<F>>() {
                unsafe {
                    let t = (witness_placer as *mut W)
                        .cast::<CSDebugWitnessEvaluator<F>>()
                        .as_mut_unchecked();
                    t.table_driver.materialize_table(table_type);
                }
            }
        }
    }

    fn add_table_with_content(&mut self, table_type: TableType, table: LookupWrapper<F>) {
        self.table_driver
            .add_table_with_content(table_type, table.clone());
        if let Some(witness_placer) = self.witness_placer.as_mut() {
            if std::any::TypeId::of::<W>() == std::any::TypeId::of::<CSDebugWitnessEvaluator<F>>() {
                unsafe {
                    let t = (witness_placer as *mut W)
                        .cast::<CSDebugWitnessEvaluator<F>>()
                        .as_mut_unchecked();
                    t.table_driver.add_table_with_content(table_type, table);
                }
            }
        }
    }

    #[track_caller]
    fn get_value(&self, var: Variable) -> Option<F> {
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

    fn add_shuffle_ram_query(&mut self, query: ShuffleRamMemQuery) {
        self.shuffle_ram_queries.push(query);
    }

    fn add_delegation_request(&mut self, request: DelegatedComputationRequest) {
        assert!(self.degegated_request_to_process.is_none());
        self.delegated_computation_requests.push(request);
    }

    fn process_delegation_request(&mut self) -> Boolean {
        assert!(self.degegated_request_to_process.is_none());
        assert!(self.delegated_computation_requests.is_empty());
        // NOTE: delegation requests processing variables are placed by the compiler, so we do not have
        // to manage their boolean properties or range checks
        let execute = self.add_variable();
        self.require_invariant(
            execute,
            Invariant::Substituted((Placeholder::ExecuteDelegation, 0)),
        );

        let memory_offset_high = self.add_variable();
        self.require_invariant(
            memory_offset_high,
            Invariant::Substituted((Placeholder::DegelationABIOffset, 0)),
        );

        // set witness
        let value_fn = move |placer: &mut Self::WitnessPlacer| {
            let execute_bool = placer.get_oracle_boolean(Placeholder::ExecuteDelegation);
            let abi_offset_high = placer.get_oracle_u16(Placeholder::DegelationABIOffset);
            placer.assign_mask(execute, &execute_bool);
            placer.assign_u16(memory_offset_high, &abi_offset_high);
        };
        self.set_values(value_fn);

        let request = DelegatedProcessingData {
            execute,
            memory_offset_high,
        };

        self.degegated_request_to_process = Some(request);

        Boolean::Is(execute)
    }

    fn create_batched_memory_accesses(
        &mut self,
        _is_writable: &[bool],
    ) -> Vec<BatchedMemoryAccessType> {
        unimplemented!("deprecated");

        // assert!(self.batched_memory_accesses.is_empty());
        // // we do not need range checks below in reads, otherwise it'll not be satisfiable as permutation
        // for (idx, el) in is_writable.iter().enumerate() {
        //     let request = if *el {
        //         let read_low = self
        //             .add_variable_from_placeholder(Placeholder::DelegationMemoryReadValue(idx), 0);
        //         let read_high = self
        //             .add_variable_from_placeholder(Placeholder::DelegationMemoryReadValue(idx), 1);

        //         let write_low = self.add_variable();
        //         let write_high = self.add_variable();

        //         BatchedMemoryAccessType::Write {
        //             read_value: [read_low, read_high],
        //             write_value: [write_low, write_high],
        //         }
        //     } else {
        //         let read_low = self
        //             .add_variable_from_placeholder(Placeholder::DelegationMemoryReadValue(idx), 0);
        //         let read_high = self
        //             .add_variable_from_placeholder(Placeholder::DelegationMemoryReadValue(idx), 1);

        //         BatchedMemoryAccessType::Read {
        //             read_value: [read_low, read_high],
        //         }
        //     };

        //     self.batched_memory_accesses.push(request);
        // }

        // self.batched_memory_accesses.clone()
    }

    fn create_register_and_indirect_memory_accesses(
        &mut self,
        request: RegisterAccessRequest,
    ) -> RegisterAndIndirectAccesses {
        assert!(request.register_index > 0);
        assert!(request.register_index < 32);
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
            let read_low = self.add_variable();
            let read_high = self.add_variable();

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

            let write_low = self.add_variable();
            let write_high = self.add_variable();

            RegisterAccessType::Write {
                read_value: [read_low, read_high],
                write_value: [write_low, write_high],
            }
        } else {
            let read_low = self.add_variable();
            let read_high = self.add_variable();

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

        let mut indirect_accesses = vec![];

        for (indirect_access_idx, is_write) in request.indirect_accesses.into_iter().enumerate() {
            let access = if is_write {
                let read_low = self.add_variable();
                let read_high = self.add_variable();

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

                let write_low = self.add_variable();
                let write_high = self.add_variable();

                IndirectAccessType::Write {
                    read_value: [read_low, read_high],
                    write_value: [write_low, write_high],
                }
            } else {
                let read_low = self.add_variable();
                let read_high = self.add_variable();

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
        assert_eq!(M, COMMON_TABLE_WIDTH);

        let row = std::array::from_fn(|idx| inputs[idx].clone());
        // NOTE: we will add formal witness eval function here to ensure that we can use it for "act of lookup"
        // if we want, and to count multiplicities

        let inputs_vars = inputs.clone();
        let value_fn = move |placer: &mut Self::WitnessPlacer| {
            let input_values: [_; M] = std::array::from_fn(|i| inputs_vars[i].evaluate(placer));
            let table_id = <Self::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                table_type.to_table_id() as u16,
            );
            placer.lookup_enforce::<M>(&input_values, &table_id);
        };
        if Self::WitnessPlacer::MERGE_LOOKUP_AND_MULTIPLICITY_COUNT
            && skip_generating_multiplicity_counting_function == false
        {
            self.set_values(value_fn);
        }

        let query = LookupQuery {
            row,
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
        assert_eq!(M, COMMON_TABLE_WIDTH);

        let row = std::array::from_fn(|idx| inputs[idx].clone());
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
            row,
            table: LookupQueryTableType::Variable(table_type),
        };
        self.lookup_storage.push(query);
    }

    #[track_caller]
    fn get_variables_from_lookup_constrained<const M: usize, const N: usize>(
        &mut self,
        inputs: &[LookupInput<F>; M],
        table_type: TableType,
    ) -> [Variable; N] {
        assert_eq!(M + N, COMMON_TABLE_WIDTH);
        assert!(table_type != TableType::ZeroEntry && table_type != TableType::DynamicPlaceholder);

        if M == COMMON_TABLE_WIDTH {
            assert_eq!(N, 0);
            // just add lookup, no witness evaluation here

            panic!("Please use `enforce_lookup_tuple_for_fixed_table` if no outputs are required");
        }

        assert!(M == 1 || M == 2);

        let output_variables: [Variable; N] = std::array::from_fn(|_| self.add_variable());

        let inputs_vars = inputs.clone();
        let value_fn = move |placer: &mut Self::WitnessPlacer| {
            let input_values: [_; M] = std::array::from_fn(|i| inputs_vars[i].evaluate(placer));
            let table_id = <Self::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                table_type.to_table_id() as u16,
            );
            let output_values = placer.lookup::<M, N>(&input_values, &table_id);
            for (var, value) in output_variables.iter().zip(output_values.iter()) {
                placer.assign_field(*var, value);
            }
        };
        self.set_values(value_fn);

        let input_len = M;
        let row = std::array::from_fn(|idx| {
            if idx < input_len {
                inputs[idx].clone()
            } else {
                LookupInput::Variable(output_variables[idx - input_len])
            }
        });
        let query = LookupQuery {
            row,
            table: LookupQueryTableType::Constant(table_type),
        };
        self.lookup_storage.push(query);

        output_variables
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

    fn link_variables(&mut self, initial_var: Variable, final_var: Variable) {
        self.linkage_queries.push(LinkedVariablesPair {
            initial_var,
            final_var,
        })
    }

    fn set_log(&mut self, opt_ctx: &OptimizationContext<F, Self>, name: &'static str) {
        if ENABLE_LOGGING {
            self.logger
                .push((name, self.no_index_assigned, opt_ctx.save_indexers()));
        }
    }

    fn view_log(&self, name: &'static str) {
        if ENABLE_LOGGING {
            // first the chronological order
            let mut logger = self.logger.clone();
            let total_vars = logger.last().unwrap().1;
            for i in (1..logger.len()).rev() {
                logger[i].1 -= logger[i - 1].1;
            }
            println!();
            println!("PERFORMANCE FOR {name} IN ORDER OF EXECUTION (# of vars)");
            for &(name, vars, indexers) in &logger {
                let OptCtxIndexers {
                    register_allocation_indexer,
                    add_sub_indexer,
                    u16_to_u8x2_decomposition_indexer,
                    u16_range_check_indexer,
                    mul_div_indexer,
                    lookup_indexer,
                    lookup_outputs_indexer,
                    zero_indexer,
                } = indexers;
                if name == "EXECUTOR" || name == "DECODER" || name == "OPT_CONTEXT" {
                    println!("{name:.<20}{vars:.>3}");
                } else {
                    println!("{name:.<20}{vars:.>3} ({add_sub_indexer} addsub, {u16_to_u8x2_decomposition_indexer} u16tou8, {u16_range_check_indexer} u16, {mul_div_indexer} muldiv, {zero_indexer} iszero, {lookup_indexer} lookup, {lookup_outputs_indexer} lookup output, {register_allocation_indexer} reg)");
                }
            }
            println!("TOTAL {total_vars:.>3}");

            // now the sorting / relative order
            println!();
            logger.sort_by_key(|tuple| tuple.1);
            let percentages = logger
                .iter()
                .map(|&(_, vars, _)| vars as f32 * 100. / total_vars as f32)
                .collect::<Vec<f32>>();
            assert!(percentages.iter().sum::<f32>() > 99.9);
            println!("RELATIVE PERFORMANCE FOR {name}");
            for (&(name, vars, _), &perc) in logger.iter().zip(&percentages) {
                let big = "#".repeat(perc as usize);
                let small = ".".repeat((perc * 10.) as usize % 10);
                let combined = big + &small;
                println!("{name:>20} {perc:4.1}% ({vars:2}) {combined:50}");
            }
            println!("");
        }
    }

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
                    TableType::RangeCheckSmall,
                    false,
                );
            } else {
                // we make an input of [first, 0, 0]
                let first_input = LookupInput::Variable(first_input);
                self.enforce_lookup_tuple_for_fixed_table(
                    &[first_input, LookupInput::empty(), LookupInput::empty()],
                    TableType::RangeCheckSmall,
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
            linkage_queries,
            table_driver,
            shuffle_ram_queries,
            delegated_computation_requests,
            degegated_request_to_process,
            batched_memory_accesses,
            register_and_indirect_memory_accesses,
            ..
        } = self;

        if delegated_computation_requests.len() > 0 {
            assert!(degegated_request_to_process.is_none());
        }

        if degegated_request_to_process.is_some() {
            assert_eq!(delegated_computation_requests.len(), 0);
        }

        assert!(delegated_computation_requests.len() <= 1);

        let output = CircuitOutput {
            state_input: Vec::new(),
            state_output: Vec::new(),
            shuffle_ram_queries,
            table_driver,
            num_of_variables: no_index_assigned as usize,
            constraints: constraint_storage,
            lookups: lookup_storage,
            linked_variables: linkage_queries,
            range_check_expressions: rangechecked_expressions,
            boolean_vars: boolean_variables,
            substitutions: placeholder_query,
            delegated_computation_requests,
            degegated_request_to_process,
            batched_memory_accesses,
            register_and_indirect_memory_accesses,
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

impl<F: PrimeField, W: WitnessPlacer<F>> BasicAssembly<F, W> {
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

impl<F: PrimeField> BasicAssembly<F, CSDebugWitnessEvaluator<F>> {
    pub fn new_with_oracle<O: Oracle<F> + 'static>(oracle: O) -> Self {
        let mut new = Self::new();
        new.witness_placer = Some(CSDebugWitnessEvaluator::new_with_oracle(oracle));

        new
    }
}
