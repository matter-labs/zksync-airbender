use super::*;

use crate::constraint::Constraint;
use crate::constraint::Term;
use crate::cs::circuit::LookupQueryTableType;
use crate::cs::circuit::RegisterAccessRequest;
use crate::cs::circuit::RegisterAndIndirectAccesses;
use crate::cs::circuit_output::CircuitOutput;
use crate::oracle::Placeholder;
use crate::structured_expr::Expr;
use crate::types::{Boolean, Num};
use crate::witness_placer::*;
use field::PrimeField;

#[non_exhaustive]
pub enum Invariant {
    Boolean,
    RangeChecked { width: u32 },
    Substituted((Placeholder, usize)),
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum MemoryAccessRequest {
    RegisterRead {
        reg_idx: Variable,
        read_value_placeholder: Placeholder,
        split_as_u8: bool,
    },
    RegisterReadWrite {
        reg_idx: Variable,
        read_value_placeholder: Placeholder,
        write_value_placeholder: Placeholder,
        split_read_as_u8: bool,
        split_write_as_u8: bool,
    },
    // Register or RAM accesses reallocate addresses
    RegisterOrRamRead {
        is_register: Boolean,
        address: [Variable; REGISTER_SIZE],
        read_value_placeholder: Placeholder,
        split_as_u8: bool,
    },
    RegisterOrRamReadWrite {
        is_register: Boolean,
        address: [Variable; REGISTER_SIZE],
        read_value_placeholder: Placeholder,
        write_value_placeholder: Placeholder,
        split_read_as_u8: bool,
        split_write_as_u8: bool,
    },
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum WordRepresentation {
    Zero,
    U16Limbs([Variable; REGISTER_SIZE]),
    U8Limbs([Variable; REGISTER_SIZE * 2]),
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ConstantRegisterAccess {
    pub reg_idx: u16,
    pub read_timestamp: [Variable; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub read_value: WordRepresentation,
    pub write_value: WordRepresentation,
    pub local_timestamp_in_cycle: u32,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct RegisterAccess {
    pub reg_idx: Variable,
    pub read_timestamp: [Variable; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub read_value: WordRepresentation,
    pub write_value: WordRepresentation,
    pub local_timestamp_in_cycle: u32,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct RegisterOrRamAccess {
    pub is_register: Boolean,
    pub address: [Variable; REGISTER_SIZE],
    pub read_timestamp: [Variable; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub read_value: WordRepresentation,
    pub write_value: WordRepresentation,
    pub local_timestamp_in_cycle: u32,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct RegisterIndirectRamAccess {
    pub variable_offset: Option<(u32, Variable, usize)>,
    pub base_address: [Variable; REGISTER_SIZE],
    pub constant_offset: u32,
    pub read_timestamp: [Variable; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub read_value: WordRepresentation,
    pub write_value: WordRepresentation,
    pub local_timestamp_in_cycle: u32,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum MemoryAccess {
    ConstantRegister(ConstantRegisterAccess),
    RegisterOnly(RegisterAccess),
    RegisterOrRam(RegisterOrRamAccess),
    RamIndirect(RegisterIndirectRamAccess),
}

impl MemoryAccess {
    pub fn local_timestamp_in_cycle(&self) -> u32 {
        match self {
            Self::ConstantRegister(inner) => inner.local_timestamp_in_cycle,
            Self::RegisterOnly(inner) => inner.local_timestamp_in_cycle,
            Self::RegisterOrRam(inner) => inner.local_timestamp_in_cycle,
            Self::RamIndirect(inner) => inner.local_timestamp_in_cycle,
        }
    }

    pub fn is_readonly(&self) -> bool {
        self.read_value() == self.write_value()
    }

    pub fn read_value(&self) -> WordRepresentation {
        match self {
            Self::ConstantRegister(inner) => inner.read_value.clone(),
            Self::RegisterOnly(inner) => inner.read_value.clone(),
            Self::RegisterOrRam(inner) => inner.read_value.clone(),
            Self::RamIndirect(inner) => inner.read_value.clone(),
        }
    }

    pub fn write_value(&self) -> WordRepresentation {
        match self {
            Self::ConstantRegister(inner) => inner.write_value.clone(),
            Self::RegisterOnly(inner) => inner.write_value.clone(),
            Self::RegisterOrRam(inner) => inner.write_value.clone(),
            Self::RamIndirect(inner) => inner.write_value.clone(),
        }
    }

    pub fn read_timestamp(&self) -> [Variable; NUM_TIMESTAMP_COLUMNS_FOR_RAM] {
        match self {
            Self::ConstantRegister(inner) => inner.read_timestamp,
            Self::RegisterOnly(inner) => inner.read_timestamp,
            Self::RegisterOrRam(inner) => inner.read_timestamp,
            Self::RamIndirect(inner) => inner.read_timestamp,
        }
    }
}

pub trait Circuit<F: PrimeField>: Sized {
    const ASSUME_MEMORY_VALUES_ASSIGNED: bool;

    type WitnessPlacer: WitnessPlacer<F>;

    fn new() -> Self;
    fn add_variable(&mut self) -> Variable;
    fn add_named_variable(&mut self, name: &str) -> Variable;
    fn set_name_for_variable(&mut self, var: Variable, name: &str);
    fn add_intermediate_variable(&mut self, layer_idx: usize) -> Variable;
    fn add_intermediate_named_variable(&mut self, name: &str, layer_idx: usize) -> Variable;
    fn set_values(&mut self, node: impl WitnessResolutionDescription<F, Self::WitnessPlacer>);
    fn get_value(&self, _var: Variable) -> Option<F> {
        None
    }
    fn add_constraint(&mut self, constraint: Constraint<F>);
    fn add_constraint_allow_explicit_linear(&mut self, constraint: Constraint<F>);
    fn add_constraint_allow_explicit_linear_prevent_optimizations(
        &mut self,
        constraint: Constraint<F>,
    );
    fn add_constraint_expr(&mut self, expr: Expr<F>);
    fn add_constraint_allow_explicit_linear_expr(&mut self, expr: Expr<F>);
    fn add_constraint_allow_explicit_linear_prevent_optimizations_expr(&mut self, expr: Expr<F>);
    fn define_variable_from_expr(&mut self, dst: Variable, expr: Expr<F>);
    fn add_constraint_into_intermediate_variable(
        &mut self,
        constraint: Constraint<F>,
        intermediate_var: Variable,
    );

    fn allocate_machine_state(
        &mut self,
        need_funct3: bool,
        need_funct7: bool,
        family_bitmask_size: usize,
    ) -> (OpcodeFamilyCircuitState<F>, Vec<Variable>);

    fn allocate_delegation_state(
        &mut self,
        delegation_type: u16,
    ) -> (Variable, [Variable; NUM_TIMESTAMP_COLUMNS_FOR_RAM]);

    fn request_mem_access(
        &mut self,
        request: MemoryAccessRequest,
        name: &str,
        local_timestamp_in_cycle: u32,
    ) -> MemoryAccess;

    fn request_register_and_indirect_memory_accesses(
        &mut self,
        request: RegisterAccessRequest,
        name: &str,
        local_timestamp_in_cycle: u32,
    ) -> RegisterAndIndirectAccesses;

    fn require_invariant(&mut self, variable: Variable, invariant: Invariant);
    fn require_invariant_from_lookup_input(&mut self, input: LookupInput<F>, invariant: Invariant);
    fn finalize(self) -> (CircuitOutput<F>, Option<Self::WitnessPlacer>);

    fn materialize_table<const TOTAL_WIDTH: usize>(&mut self, table_type: TableType);
    fn add_table_with_content(
        &mut self,
        table_type: TableType,
        table: crate::tables::LookupWrapper<F>,
    );

    #[track_caller]
    fn add_boolean_variable(&mut self) -> Boolean {
        let new_var = self.add_variable();
        self.require_invariant(new_var, Invariant::Boolean);
        Boolean::Is(new_var)
    }

    #[track_caller]
    fn add_named_boolean_variable(&mut self, name: &str) -> Boolean {
        let new_var = self.add_named_variable(name);
        self.require_invariant(new_var, Invariant::Boolean);
        Boolean::Is(new_var)
    }

    #[track_caller]
    fn add_variable_with_range_check(&mut self, width: u32) -> Num<F> {
        assert!(
            width as usize == SMALL_RANGE_CHECK_TABLE_WIDTH
                || width as usize == LARGE_RANGE_CHECK_TABLE_WIDTH
        );
        let new_var = self.add_variable();
        self.require_invariant(new_var, Invariant::RangeChecked { width });
        Num::Var(new_var)
    }

    #[track_caller]
    fn add_variable_from_constraint(&mut self, constraint: Constraint<F>) -> Variable {
        let name = format!("Variable at {}::{}", file!(), line!());
        self.add_named_variable_from_constraint(constraint, &name)
    }

    fn add_named_variable_from_constraint(
        &mut self,
        constraint: Constraint<F>,
        name: &str,
    ) -> Variable;
    fn add_variable_from_expr(&mut self, expr: Expr<F>) -> Variable;
    fn add_named_variable_from_expr(&mut self, expr: Expr<F>, name: &str) -> Variable;

    fn add_intermediate_named_variable_from_constraint(
        &mut self,
        constraint: Constraint<F>,
        name: &str,
    ) -> Variable;
    fn add_intermediate_named_variable_from_expr(&mut self, expr: Expr<F>, name: &str) -> Variable;

    #[track_caller]
    fn add_variable_from_constraint_without_witness_evaluation(
        &mut self,
        constraint: Constraint<F>,
    ) -> Variable;

    #[track_caller]
    fn add_variable_from_constraint_allow_explicit_linear(
        &mut self,
        constraint: Constraint<F>,
    ) -> Variable;

    #[track_caller]
    fn add_variable_from_constraint_allow_explicit_linear_without_witness_evaluation(
        &mut self,
        constraint: Constraint<F>,
    ) -> Variable;

    #[track_caller]
    fn choose(&mut self, flag: Boolean, if_true_val: Num<F>, if_false_val: Num<F>) -> Num<F> {
        if if_true_val == if_false_val {
            return if_true_val;
        }

        if let Boolean::Constant(flag) = flag {
            return if flag { if_true_val } else { if_false_val };
        }

        let new_var = self.add_variable();
        let flag_expr = Expr::<F>::from(flag);
        let expr = flag_expr.clone() * (Expr::from(if_true_val) - Expr::from(if_false_val))
            + Expr::from(if_false_val);

        let value_fn = move |placer: &mut Self::WitnessPlacer| {
            let mask = match flag {
                Boolean::Is(flag) => placer.get_boolean(flag),
                Boolean::Not(flag) => placer.get_boolean(flag).negate(),
                Boolean::Constant(_) => unreachable!(),
            };
            let if_true_value = match if_true_val {
                Num::Var(variable) => placer.get_field(variable),
                Num::Constant(value) => WitnessComputationalField::constant(value),
            };
            let if_false_value = match if_false_val {
                Num::Var(variable) => placer.get_field(variable),
                Num::Constant(value) => WitnessComputationalField::constant(value),
            };
            let selection_result =
                WitnessComputationalField::select(&mask, &if_true_value, &if_false_value);
            placer.assign_field(new_var, &selection_result);
        };
        self.set_values(value_fn);

        self.define_variable_from_expr(new_var, expr);
        Num::Var(new_var)
    }

    #[track_caller]
    fn choose_from_orthogonal_variants(
        &mut self,
        flags: &[Boolean],
        variants: &[Num<F>],
    ) -> Num<F> {
        todo!();

        // assert!(flags.len() > 0);
        // assert_eq!(flags.len(), variants.len());
        // return spec_choose_from_orthogonal_variants(self, flags, variants);
    }

    #[track_caller]
    fn choose_from_orthogonal_variants_for_linear_terms(
        &mut self,
        flags: &[Boolean],
        variants: &[Constraint<F>],
    ) -> Num<F> {
        todo!();

        // assert!(flags.len() > 0);
        // assert_eq!(flags.len(), variants.len());
        // return spec_choose_from_orthogonal_variants_for_linear_terms(self, flags, variants);
    }

    fn is_zero(&mut self, var: Num<F>) -> Boolean {
        self.equals_to(var, Num::Constant(F::ZERO))
    }

    // more generic version of is_zero_reg, only works with limbs
    fn is_zero_sum(&mut self, sum: Constraint<F>) -> Boolean {
        assert!(sum.degree() <= 1);
        let is_zero_flag = self.add_variable();
        let not_zero_flag = Constraint::from(1) - Term::from(is_zero_flag);
        let inv = self.add_variable();

        let sum_clone = sum.clone();
        let value_fn = move |placer: &mut Self::WitnessPlacer| {
            let mut sum_value =
                <Self::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(F::ZERO);
            for term in &sum_clone.terms {
                match term {
                    Term::Constant(c) => {
                        let c_value =
                            <Self::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(*c);
                        sum_value.add_assign(&c_value);
                    }
                    Term::Expression {
                        coeff,
                        inner,
                        degree,
                    } => {
                        assert!(*coeff == F::ONE && *degree == 1);
                        let inner_value = placer.get_field(inner[0]);
                        sum_value.add_assign(&inner_value);
                    }
                }
            }
            let inv_value = sum_value.inverse_or_zero();
            let zflag_value = sum_value.is_zero();
            placer.assign_field(inv, &inv_value);
            placer.assign_mask(is_zero_flag, &zflag_value);
        };
        self.set_values(value_fn);

        self.add_constraint(Constraint::from(inv) * sum.clone() - not_zero_flag.clone());
        self.add_constraint((Constraint::from(1) - not_zero_flag) * sum);
        Boolean::Is(is_zero_flag)
    }

    fn equals_to(&mut self, a: Num<F>, b: Num<F>) -> Boolean {
        match (a, b) {
            (Num::Var(a), Num::Var(b)) => {
                // (var - var2) * zero_flag = 0;
                // (var - var2) * var_inv = 1 - zero_flag;
                let var_inv = self.add_variable();
                let zero_flag = self.add_boolean_variable();
                let zero_flag_var = zero_flag.get_variable().unwrap();

                let value_fn = move |placer: &mut Self::WitnessPlacer| {
                    let mut a = placer.get_field(a);
                    let b = placer.get_field(b);
                    a.sub_assign(&b);
                    let is_zero = a.is_zero();
                    let inverse_witness = a.inverse_or_zero();
                    placer.assign_mask(zero_flag_var, &is_zero);
                    placer.assign_field(var_inv, &inverse_witness);
                };
                self.set_values(value_fn);
                self.add_constraint((Term::from(a) - Term::from(b)) * Term::from(zero_flag));
                self.add_constraint(
                    (Term::from(a) - Term::from(b)) * Term::from(var_inv) + Term::from(zero_flag)
                        - Term::from(1),
                );

                zero_flag
            }
            (Num::Var(a), Num::Constant(b)) => {
                // (var - cnst) * zero_flag = 0;
                // (var - cnst) * var_inv = 1 - zero_flag;
                let var_inv = self.add_variable();
                let zero_flag = self.add_boolean_variable();
                let zero_flag_var = zero_flag.get_variable().unwrap();

                let value_fn = move |placer: &mut Self::WitnessPlacer| {
                    let mut a = placer.get_field(a);
                    let b = WitnessComputationalField::constant(b);
                    a.sub_assign(&b);
                    let is_zero = a.is_zero();
                    let inverse_witness = a.inverse_or_zero();
                    placer.assign_mask(zero_flag_var, &is_zero);
                    placer.assign_field(var_inv, &inverse_witness);
                };
                self.set_values(value_fn);
                self.add_constraint((Term::from(a) - Term::from_field(b)) * Term::from(zero_flag));
                self.add_constraint(
                    (Term::from(a) - Term::from_field(b)) * Term::from(var_inv)
                        + Term::from(zero_flag)
                        - Term::from(1),
                );

                zero_flag
            }
            (Num::Constant(a), Num::Var(b)) => {
                // (var - cnst) * zero_flag = 0;
                // (var - cnst) * var_inv = 1 - zero_flag;
                let var_inv = self.add_variable();
                let zero_flag = self.add_boolean_variable();
                let zero_flag_var = zero_flag.get_variable().unwrap();

                let value_fn = move |placer: &mut Self::WitnessPlacer| {
                    let b = placer.get_field(b);
                    let mut a = <Self::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(a);
                    a.sub_assign(&b);
                    let is_zero = a.is_zero();
                    let inverse_witness = a.inverse_or_zero();
                    placer.assign_mask(zero_flag_var, &is_zero);
                    placer.assign_field(var_inv, &inverse_witness);
                };
                self.set_values(value_fn);
                self.add_constraint((Term::from_field(a) - Term::from(b)) * Term::from(zero_flag));
                self.add_constraint(
                    (Term::from_field(a) - Term::from(b)) * Term::from(var_inv)
                        + Term::from(zero_flag)
                        - Term::from(1),
                );

                zero_flag
            }
            (Num::Constant(a), Num::Constant(b)) => {
                let is_equal = a == b;
                Boolean::Constant(is_equal)
            }
        }
    }

    #[track_caller]
    fn peek_lookup_value_unconstrained<const M: usize, const N: usize>(
        &mut self,
        inputs: &[LookupInput<F>; M],
        table_type: TableType,
        exec_flag: Boolean,
    ) -> [Variable; N] {
        assert_eq!(M + N, COMMON_TABLE_WIDTH);
        assert!(M > 0);

        todo!();

        // // here we should do the same trick as with "add variable from constraint",
        // // so that we can have a universal witness generation function, but provide via constraints
        // // a description of the relation

        // let output_variables: [Variable; N] = std::array::from_fn(|_| self.add_variable());
        // let inputs = inputs.clone();
        // let exec_flag = exec_flag.get_variable().unwrap();

        // let inner_evaluator = move |placer: &mut Self::WitnessPlacer| {
        //     let mask = placer.get_boolean(exec_flag);
        //     if table_type == TableType::ZeroEntry {
        //         let zero = WitnessComputationalField::constant(F::ZERO);
        //         for var in output_variables.iter() {
        //             placer.conditionally_assign_field(*var, &mask, &zero);
        //         }
        //         return;
        //     }
        //     let input_values: [_; M] = std::array::from_fn(|i| inputs[i].evaluate(placer));
        //     let table_id = <Self::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
        //         table_type.to_table_id() as u16,
        //     );
        //     let output_values = placer.lookup::<M, N>(&input_values, &table_id);
        //     for (var, value) in output_variables.iter().zip(output_values.iter()) {
        //         placer.conditionally_assign_field(*var, &mask, value);
        //     }
        // };

        // let value_fn = move |placer: &mut Self::WitnessPlacer| {
        //     let mask = placer.get_boolean(exec_flag);
        //     witness_early_branch_if_possible(mask.clone(), placer, &inner_evaluator);
        // };

        // self.set_values(value_fn);

        // output_variables
    }

    #[track_caller]
    fn peek_lookup_value_unconstrained_ext<const M: usize, const N: usize>(
        &mut self,
        inputs: &[LookupInput<F>; M],
        outputs: &[Variable; N],
        table: Num<F>,
        exec_flag: Boolean,
    ) {
        assert!(inputs.len() > 0);

        let output_variables: [Variable; N] = outputs.clone();
        let inputs = inputs.clone();
        let exec_flag = exec_flag.get_variable().unwrap();

        let inner_evaluator = move |placer: &mut Self::WitnessPlacer| {
            let table_id = match table {
                Num::Constant(con) => <Self::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                    con.as_u32_reduced() as u16,
                ),
                Num::Var(var) => placer.get_u16(var),
            };
            let mask = placer.get_boolean(exec_flag);
            let input_values: [_; M] = std::array::from_fn(|i| inputs[i].evaluate(placer));
            let output_values = placer.maybe_lookup::<M, N>(&input_values, &table_id, &mask);
            for (var, value) in output_variables.iter().zip(output_values.iter()) {
                placer.conditionally_assign_field(*var, &mask, value);
            }
        };

        let value_fn = move |placer: &mut Self::WitnessPlacer| {
            let mask = placer.get_boolean(exec_flag);
            witness_early_branch_if_possible(mask.clone(), placer, &inner_evaluator);
        };

        self.set_values(value_fn);
    }

    fn enforce_lookup_tuple_for_fixed_table<const M: usize>(
        &mut self,
        inputs: &[LookupInput<F>; M],
        table_type: TableType,
        skip_generating_multiplicity_counting_function: bool,
    );

    fn enforce_lookup_tuple_for_variable_table<const M: usize>(
        &mut self,
        inputs: &[LookupInput<F>; M],
        table_type: Variable,
    );

    fn enforce_lookup_tuple<const M: usize>(
        &mut self,
        inputs: &[LookupInput<F>; M],
        table_type: LookupQueryTableType<F>,
    );

    #[track_caller]
    fn get_variables_from_lookup_constrained<const M: usize, const N: usize>(
        &mut self,
        inputs: &[LookupInput<F>; M],
        table_type: TableType,
    ) -> [Variable; N];

    #[track_caller]
    fn set_variables_from_lookup_constrained<const M: usize, const N: usize>(
        &mut self,
        inputs: &[LookupInput<F>; M],
        output_variables: &[Variable; N],
        table_type: LookupQueryTableType<F>,
    );

    // fn set_log(&mut self, opt_ctx: &OptimizationContext<F, Self>, name: &'static str);
    // fn view_log(&self, name: &'static str);
    fn is_satisfied(&mut self) -> bool;
}
