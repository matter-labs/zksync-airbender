use super::utils::*;
use crate::constraint::Constraint;
use crate::constraint::*;
use crate::cs::circuit::*;
use crate::cs::utils::{
    collapse_max_quadratic_constraint_into, mask_by_boolean_into_accumulator_constraint,
};
use crate::cs::witness_placer::cs_debug_evaluator::witness_early_branch_if_possible;
use crate::cs::witness_placer::WitnessTypeSet;
use crate::cs::witness_placer::{
    WitnessComputationCore, WitnessComputationalInteger, WitnessComputationalU16,
    WitnessComputationalU32, WitnessPlacer,
};
use crate::definitions::*;
use crate::one_row_compiler::LookupInput;
use crate::types::*;
use ::field::PrimeField;
use core::array::from_fn;

use super::risc_v_types::ExecutorOperation;

struct AddSubRelation<F: PrimeField> {
    exec_flag: Boolean,
    a: Register<F>,
    b: Register<F>,
    c: Register<F>,
}

// all range checks are of LIMB_WIDTH_SIZE
struct RangeCheckRelation<F: PrimeField> {
    exec_flag: Boolean,
    x: Num<F>,
}

// NOTE: we use Num for signs, as they can come as non-booleans in some conditional branches,
// so we do not cast them to Booleans to avoid witness generation assumptions
pub struct MulDivRelation<F: PrimeField> {
    pub(crate) exec_flag: Boolean,
    pub(crate) op_1: Register<F>,
    pub(crate) op_1_sign: Num<F>,
    pub(crate) op_2: Register<F>,
    pub(crate) op_2_sign: Num<F>,
    pub(crate) additive_term: Register<F>,
    pub(crate) additive_term_sign: Num<F>,
    pub(crate) mul_low: Register<F>,
    pub(crate) mul_high: Register<F>,
}

struct IsZeroRelation<F: PrimeField> {
    exec_flag: Boolean,
    reg: Register<F>,
}

#[derive(Clone, Debug)]
struct LookupRelation<F: PrimeField> {
    exec_flag: Boolean,
    row: [LookupInput<F>; COMMON_TABLE_WIDTH],
    table: Num<F>,
}

// Indexes and how it works:
// - one can usually look at relation as inputs <-> outputs
// - one usually has inputs and can preallocate outputs
// - then we can select over all inputs + branch taken combinations, and same for inputs, and enforce once
// - but as an alternative we can instead have a buffer of outputs, and avoid selecting of the outputs,
// but in the corresponding branch the "output" will be formally invalid witness, and we should just be careful
// to avoid unsatisfiable constraint if the branch is not taken
// Overall, it reduced a number of the variable in the circuit

#[derive(Clone, Copy, Debug)]
pub struct OptCtxIndexers {
    pub register_allocation_indexer: usize,
    pub add_sub_indexer: usize,
    pub u16_to_u8x2_decomposition_indexer: usize,
    pub u16_range_check_indexer: usize,
    pub mul_div_indexer: usize,
    pub lookup_indexer: usize,
    pub lookup_outputs_indexer: usize,
    pub zero_indexer: usize,
}

impl OptCtxIndexers {
    pub const fn uninitialized() -> Self {
        OptCtxIndexers {
            register_allocation_indexer: 0,
            add_sub_indexer: 0,
            u16_to_u8x2_decomposition_indexer: 0,
            u16_range_check_indexer: 0,
            mul_div_indexer: 0,
            lookup_indexer: 0,
            lookup_outputs_indexer: 0,
            zero_indexer: 0,
        }
    }

    pub fn reset(&mut self) {
        *self = Self::uninitialized();
    }
}

pub struct OptimizationContext<F: PrimeField, C: Circuit<F>> {
    pub indexers: OptCtxIndexers,
    add_sub_relations: Vec<(usize, AddSubRelation<F>)>,
    u16_to_u8x2_decomposition_relations: Vec<(usize, RangeCheckRelation<F>)>,
    u16_range_check_relations: Vec<(usize, RangeCheckRelation<F>)>,
    mul_div_relations: Vec<(usize, MulDivRelation<F>)>,
    lookup_relations: Vec<(usize, LookupRelation<F>)>,
    is_zero_relations: Vec<(usize, IsZeroRelation<F>)>,

    u16_to_u8x2_splits: Vec<(Num<F>, Num<F>)>,
    registers: Vec<Register<F>>,
    add_sub_ofs: Vec<Boolean>,
    is_zero_flags: Vec<Boolean>,
    lookup_outputs: Vec<Variable>,

    _marker: std::marker::PhantomData<(F, C)>,
}

impl<F: PrimeField, CS: Circuit<F>> OptimizationContext<F, CS> {
    #[inline(always)]
    pub fn save_indexers(&self) -> OptCtxIndexers {
        self.indexers
    }
    #[inline(always)]
    pub fn restore_indexers(&mut self, indexers: OptCtxIndexers) {
        self.indexers = indexers
    }

    pub fn new() -> Self {
        OptimizationContext {
            indexers: OptCtxIndexers::uninitialized(),
            add_sub_relations: vec![],
            u16_to_u8x2_decomposition_relations: vec![],
            u16_range_check_relations: vec![],
            mul_div_relations: vec![],
            lookup_relations: vec![],
            is_zero_relations: vec![],

            registers: vec![],
            u16_to_u8x2_splits: vec![],
            add_sub_ofs: vec![],
            is_zero_flags: vec![],
            lookup_outputs: vec![],

            _marker: std::marker::PhantomData,
        }
    }
    #[inline(always)]
    pub fn reset_indexers(&mut self) {
        self.indexers.reset()
    }

    #[track_caller]
    pub fn get_register_output(&mut self, cs: &mut CS) -> Register<F> {
        let register_to_use = if self.indexers.register_allocation_indexer < self.registers.len() {
            self.registers[self.indexers.register_allocation_indexer]
        } else {
            // unconditionally allocate and range check
            let reg = Register::new(cs);
            self.registers.push(reg);
            reg
        };

        self.indexers.register_allocation_indexer += 1;

        register_to_use
    }

    #[track_caller]
    pub fn append_add_relation(
        &mut self,
        a: Register<F>,
        b: Register<F>,
        exec_flag: Boolean,
        cs: &mut CS,
    ) -> (Register<F>, Boolean) {
        self.append_add_sub_relation(a, b, exec_flag, cs, false)
    }

    pub fn append_sub_relation(
        &mut self,
        a: Register<F>,
        b: Register<F>,
        flag: Boolean,
        cs: &mut CS,
    ) -> (Register<F>, Boolean) {
        self.append_add_sub_relation(a, b, flag, cs, true)
    }

    pub fn append_is_zero_relation(
        &mut self,
        reg: Register<F>,
        exec_flag: Boolean,
        cs: &mut CS,
    ) -> Boolean {
        let rel = IsZeroRelation { exec_flag, reg };
        self.is_zero_relations
            .push((self.indexers.zero_indexer, rel));
        assert!(self.indexers.zero_indexer <= self.is_zero_flags.len());

        let flag = if self.indexers.zero_indexer < self.is_zero_flags.len() {
            self.is_zero_flags[self.indexers.zero_indexer]
        } else {
            let flag = cs.add_boolean_variable();
            self.is_zero_flags.push(flag);
            flag
        };

        let reg_vars = reg.0.map(|el| el.get_variable());
        let result_var = flag.get_variable().unwrap();
        let exec_flag_var = exec_flag.get_variable().unwrap();
        // evaluate in place
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            use crate::cs::witness_placer::WitnessComputationalInteger;

            // No point of conditionally branching here

            let mask = placer.get_boolean(exec_flag_var);
            let reg_value = placer.get_u32_from_u16_parts(reg_vars);
            let is_zero = reg_value.is_zero();

            placer.conditionally_assign_mask(result_var, &mask, &is_zero);
        };

        cs.set_values(value_fn);

        self.indexers.zero_indexer += 1;
        flag
    }

    #[track_caller]
    pub fn append_mul_relation_unsigned(
        &mut self,
        a: Register<F>,
        b: Register<F>,
        exec_flag: Boolean,
        cs: &mut CS,
    ) -> (Register<F>, Register<F>) {
        let mul_low = self.get_register_output(cs);
        let mul_high = self.get_register_output(cs);

        let a_vars = [a.0[0].get_variable(), a.0[1].get_variable()];

        let b_vars = [b.0[0].get_variable(), b.0[1].get_variable()];

        let mul_low_vars = [mul_low.0[0].get_variable(), mul_low.0[1].get_variable()];

        let mul_high_vars = [mul_high.0[0].get_variable(), mul_high.0[1].get_variable()];

        let exec_flag_var = exec_flag.get_variable().unwrap();

        let evaluate_fn_inner = move |placer: &mut CS::WitnessPlacer| {
            let mask = placer.get_boolean(exec_flag_var);
            let a = placer.get_u32_from_u16_parts(a_vars);
            let b = placer.get_u32_from_u16_parts(b_vars);

            let (low, high) = a.split_widening_product(&b);

            placer.conditionally_assign_u32(mul_low_vars, &mask, &low);
            placer.conditionally_assign_u32(mul_high_vars, &mask, &high);
        };

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let mask = placer.get_boolean(exec_flag_var);
            witness_early_branch_if_possible(mask, placer, &evaluate_fn_inner);
        };

        cs.set_values(value_fn);

        let relation = MulDivRelation {
            exec_flag,
            op_1: a,
            op_1_sign: Num::Constant(F::ZERO),
            op_2: b,
            op_2_sign: Num::Constant(F::ZERO),
            additive_term: Register([Num::Constant(F::ZERO); 2]),
            additive_term_sign: Num::Constant(F::ZERO),
            mul_low,
            mul_high,
        };

        self.append_mul_relation_inner(relation);

        (mul_low, mul_high)
    }

    #[track_caller]
    pub fn append_mul_relation_ext(
        &mut self,
        a: RegisterWithSign<F>,
        b: RegisterWithSign<F>,
        exec_flag: Boolean,
        cs: &mut CS,
        exec_op: ExecutorOperation,
    ) -> (Register<F>, Register<F>) {
        let mul_low = self.get_register_output(cs);
        let mul_high = self.get_register_output(cs);

        let a_vars = [a.u16_limbs[0].get_variable(), a.u16_limbs[1].get_variable()];

        let b_vars = [b.u16_limbs[0].get_variable(), b.u16_limbs[1].get_variable()];

        let mul_low_vars = [mul_low.0[0].get_variable(), mul_low.0[1].get_variable()];

        let mul_high_vars = [mul_high.0[0].get_variable(), mul_high.0[1].get_variable()];

        let exec_flag_var = exec_flag.get_variable().unwrap();

        let evaluate_fn_inner = move |placer: &mut CS::WitnessPlacer| {
            use crate::cs::witness_placer::WitnessComputationalI32;

            let mask = placer.get_boolean(exec_flag_var);
            let a = placer.get_u32_from_u16_parts(a_vars);
            let b = placer.get_u32_from_u16_parts(b_vars);

            let (low, high) = match exec_op {
                ExecutorOperation::MUL | ExecutorOperation::MULHU => {
                    // unsigned is easy
                    a.split_widening_product(&b)
                }
                ExecutorOperation::MULH => {
                    let a = <CS::WitnessPlacer as WitnessTypeSet<F>>::I32::from_unsigned(a);
                    let b = <CS::WitnessPlacer as WitnessTypeSet<F>>::I32::from_unsigned(b);

                    a.widening_product_bits(&b)
                }
                ExecutorOperation::MULHSU => {
                    let a = <CS::WitnessPlacer as WitnessTypeSet<F>>::I32::from_unsigned(a);
                    a.mixed_widening_product_bits(&b)
                }
                _ => unreachable!(),
            };

            placer.conditionally_assign_u32(mul_low_vars, &mask, &low);
            placer.conditionally_assign_u32(mul_high_vars, &mask, &high);
        };

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let mask = placer.get_boolean(exec_flag_var);
            witness_early_branch_if_possible(mask, placer, &evaluate_fn_inner);
        };

        cs.set_values(value_fn);

        let op1_is_signed = match exec_op {
            ExecutorOperation::MULH | ExecutorOperation::MULHSU => true,
            ExecutorOperation::MUL | ExecutorOperation::MULHU => false,
            _ => unreachable!(),
        };
        let op2_is_signed = exec_op == ExecutorOperation::MULH;

        let op_1_sign = if op1_is_signed {
            Num::from_boolean_is(a.sign_bit)
        } else {
            Num::Constant(F::ZERO)
        };

        let op_2_sign = if op2_is_signed {
            Num::from_boolean_is(b.sign_bit)
        } else {
            Num::Constant(F::ZERO)
        };

        let relation = MulDivRelation {
            exec_flag,
            op_1: a.into_register(),
            op_1_sign: op_1_sign,
            op_2: b.into_register(),
            op_2_sign: op_2_sign,
            additive_term: Register([Num::Constant(F::ZERO); 2]),
            additive_term_sign: Num::Constant(F::ZERO),
            mul_low,
            mul_high,
        };

        self.append_mul_relation_inner(relation);

        (mul_low, mul_high)
    }

    #[track_caller]
    pub fn append_mul_relation_raw(
        &mut self,
        op_1: Register<F>,
        op_1_sign: Num<F>,
        op_2: Register<F>,
        op_2_sign: Num<F>,
        exec_flag: Boolean,
        cs: &mut CS,
    ) -> (Register<F>, Register<F>) {
        let mul_low = self.get_register_output(cs);
        let mul_high = self.get_register_output(cs);

        let op_1_vars = [op_1.0[0].get_variable(), op_1.0[1].get_variable()];

        let op_2_vars = [op_2.0[0].get_variable(), op_2.0[1].get_variable()];

        let mul_low_vars = [mul_low.0[0].get_variable(), mul_low.0[1].get_variable()];

        let mul_high_vars = [mul_high.0[0].get_variable(), mul_high.0[1].get_variable()];

        let op_1_sign_var = op_1_sign.get_variable();
        let op_2_sign_var = op_2_sign.get_variable();
        let exec_flag_var = exec_flag.get_variable().unwrap();

        let evaluate_fn_inner = move |placer: &mut CS::WitnessPlacer| {
            use crate::cs::witness_placer::WitnessComputationalI32;
            use crate::cs::witness_placer::WitnessComputationalInteger;
            use crate::cs::witness_placer::WitnessMask;

            let mask = placer.get_boolean(exec_flag_var);
            let a = placer.get_u32_from_u16_parts(op_1_vars);
            let b = placer.get_u32_from_u16_parts(op_2_vars);
            let a_is_signed = placer.get_boolean(op_1_sign_var);
            let b_is_signed = placer.get_boolean(op_2_sign_var);

            let a_is_unsigned = a_is_signed.negate();
            let b_is_unsigned = b_is_signed.negate();

            let a_signed = <CS::WitnessPlacer as WitnessTypeSet<F>>::I32::from_unsigned(a.clone());
            let b_signed = <CS::WitnessPlacer as WitnessTypeSet<F>>::I32::from_unsigned(b.clone());

            let mut result_low = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
            let mut result_high = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);

            // unsigned
            {
                let selector = a_is_unsigned.and(&b_is_unsigned);
                let (low, high) = a.split_widening_product(&b);
                result_low.assign_masked(&selector, &low);
                result_high.assign_masked(&selector, &high);
            }

            // signed
            {
                let selector = a_is_signed.and(&b_is_signed);
                let (low, high) = a_signed.widening_product_bits(&b_signed);
                result_low.assign_masked(&selector, &low);
                result_high.assign_masked(&selector, &high);
            }

            // signed by unsigned
            {
                let selector = a_is_signed.and(&b_is_unsigned);
                let (low, high) = a_signed.mixed_widening_product_bits(&b);
                result_low.assign_masked(&selector, &low);
                result_high.assign_masked(&selector, &high);
            }

            // unsigned by signed
            {
                let selector = a_is_unsigned.and(&b_is_signed);
                let (low, high) = b_signed.mixed_widening_product_bits(&a);
                result_low.assign_masked(&selector, &low);
                result_high.assign_masked(&selector, &high);
            }

            placer.conditionally_assign_u32(mul_low_vars, &mask, &result_low);
            placer.conditionally_assign_u32(mul_high_vars, &mask, &result_high);
        };

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let mask = placer.get_boolean(exec_flag_var);
            witness_early_branch_if_possible(mask, placer, &evaluate_fn_inner);
        };

        cs.set_values(value_fn);

        let relation = MulDivRelation {
            exec_flag,
            op_1: op_1,
            op_1_sign,
            op_2: op_2,
            op_2_sign,
            additive_term: Register([Num::Constant(F::ZERO); REGISTER_SIZE]),
            additive_term_sign: Num::Constant(F::ZERO),
            mul_low,
            mul_high,
        };

        self.append_mul_relation_inner(relation);

        (mul_low, mul_high)
    }

    #[track_caller]
    pub fn append_mul_relation_inner(&mut self, relation: MulDivRelation<F>) {
        self.mul_div_relations
            .push((self.indexers.mul_div_indexer, relation));
        self.indexers.mul_div_indexer += 1;
    }

    pub fn append_u16_to_le_u8_decomposition_relation(
        &mut self,
        x: Num<F>,
        exec_flag: Boolean,
        cs: &mut CS,
    ) -> [Num<F>; 2] {
        let rel = RangeCheckRelation { exec_flag, x };
        self.u16_to_u8x2_decomposition_relations
            .push((self.indexers.u16_to_u8x2_decomposition_indexer, rel));
        assert!(self.indexers.u16_to_u8x2_decomposition_indexer <= self.u16_to_u8x2_splits.len());

        let (low, high) =
            if self.indexers.u16_to_u8x2_decomposition_indexer < self.u16_to_u8x2_splits.len() {
                self.u16_to_u8x2_splits[self.indexers.u16_to_u8x2_decomposition_indexer]
            } else {
                let low = cs.add_variable_with_range_check(8);
                let high = cs.add_variable_with_range_check(8);
                self.u16_to_u8x2_splits.push((low, high));
                (low, high)
            };

        self.indexers.u16_to_u8x2_decomposition_indexer += 1;

        let in_var = x.get_variable();
        let outputs = [low.get_variable(), high.get_variable()];
        let exec_flag_var = exec_flag.get_variable().unwrap();

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            use crate::cs::witness_placer::WitnessComputationalInteger;
            use crate::cs::witness_placer::WitnessComputationalU16;

            let value = placer.get_u16(in_var);
            let low = value.truncate();
            let high = value.shr(8).truncate();
            let mask = placer.get_boolean(exec_flag_var);

            placer.conditionally_assign_u8(outputs[0], &mask, &low);
            placer.conditionally_assign_u8(outputs[1], &mask, &high);
        };

        cs.set_values(value_fn);

        [low, high]
    }

    #[track_caller]
    fn append_add_sub_relation(
        &mut self,
        a: Register<F>,
        b: Register<F>,
        exec_flag: Boolean,
        cs: &mut CS,
        is_sub: bool,
    ) -> (Register<F>, Boolean) {
        let res = self.get_register_output(cs);

        assert!(self.indexers.add_sub_indexer <= self.add_sub_ofs.len());
        let of_flag = if self.indexers.add_sub_indexer < self.add_sub_ofs.len() {
            self.add_sub_ofs[self.indexers.add_sub_indexer]
        } else {
            let of = cs.add_boolean_variable();
            self.add_sub_ofs.push(of);
            of
        };

        let relation = if is_sub {
            AddSubRelation {
                exec_flag,
                a: res,
                b,
                c: a,
            }
        } else {
            AddSubRelation {
                exec_flag,
                a,
                b,
                c: res,
            }
        };
        self.add_sub_relations
            .push((self.indexers.add_sub_indexer, relation));
        self.indexers.add_sub_indexer += 1;

        use crate::cs::utils::check_constants;
        let reg1_is_constant = check_constants(&a.0[0], &a.0[1]);
        let reg2_is_constant = check_constants(&b.0[0], &b.0[1]);

        let res_vars = res.0.map(|el| el.get_variable());
        let of_flag_var = of_flag.get_variable().unwrap();

        let exec_flag_var = exec_flag.get_variable().unwrap();

        match (reg1_is_constant, reg2_is_constant) {
            ((false, false), (false, false)) => {
                let a = a.0.map(|el| el.get_variable());
                let b = b.0.map(|el| el.get_variable());

                let value_fn = move |placer: &mut CS::WitnessPlacer| {
                    use crate::cs::witness_placer::WitnessComputationalInteger;

                    let a = placer.get_u32_from_u16_parts(a);
                    let b = placer.get_u32_from_u16_parts(b);
                    let mask = placer.get_boolean(exec_flag_var);

                    let (result, of) = if is_sub {
                        a.overflowing_sub(&b)
                    } else {
                        a.overflowing_add(&b)
                    };

                    placer.conditionally_assign_u32(res_vars, &mask, &result);
                    placer.conditionally_assign_mask(of_flag_var, &mask, &of);
                };

                cs.set_values(value_fn);
            }
            ((true, true), (false, false)) => {
                let a_low_constant = a.0[0].get_constant_value().as_u64_reduced() as u32;
                let a_high_constant = a.0[1].get_constant_value().as_u64_reduced() as u32;

                let a = (a_high_constant << 16) | a_low_constant;
                let b = b.0.map(|el| el.get_variable());

                let value_fn = move |placer: &mut CS::WitnessPlacer| {
                    use crate::cs::witness_placer::WitnessComputationalInteger;

                    let a = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(a);
                    let b = placer.get_u32_from_u16_parts(b);
                    let mask = placer.get_boolean(exec_flag_var);

                    let (result, of) = if is_sub {
                        a.overflowing_sub(&b)
                    } else {
                        a.overflowing_add(&b)
                    };

                    placer.conditionally_assign_u32(res_vars, &mask, &result);
                    placer.conditionally_assign_mask(of_flag_var, &mask, &of);
                };

                cs.set_values(value_fn);
            }
            ((false, false), (true, true)) => {
                let b_low_constant = b.0[0].get_constant_value().as_u64_reduced() as u32;
                let b_high_constant = b.0[1].get_constant_value().as_u64_reduced() as u32;

                let a = a.0.map(|el| el.get_variable());
                let b = (b_high_constant << 16) | b_low_constant;

                let value_fn = move |placer: &mut CS::WitnessPlacer| {
                    use crate::cs::witness_placer::WitnessComputationalInteger;

                    let a = placer.get_u32_from_u16_parts(a);
                    let b = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(b);
                    let mask = placer.get_boolean(exec_flag_var);

                    let (result, of) = if is_sub {
                        a.overflowing_sub(&b)
                    } else {
                        a.overflowing_add(&b)
                    };

                    placer.conditionally_assign_u32(res_vars, &mask, &result);
                    placer.conditionally_assign_mask(of_flag_var, &mask, &of);
                };

                cs.set_values(value_fn);
            }
            (
                (_reg1_low_is_constant, _reg1_high_is_constant),
                (_reg2_low_is_constant, _reg2_high_is_constant),
            ) => {
                unreachable!();
            }
        }

        (res, of_flag)
    }

    fn append_lookup_relation_inner<const M: usize, const N: usize>(
        &mut self,
        inputs: &[LookupInput<F>; M],
        expected_outputs: &[Variable; N],
        table: Num<F>,
        exec_flag: Boolean,
    ) {
        assert_eq!(M + N, COMMON_TABLE_WIDTH);

        let row: [LookupInput<F>; COMMON_TABLE_WIDTH] = std::array::from_fn(|i| {
            if i < inputs.len() {
                inputs[i].clone()
            } else {
                LookupInput::Variable(expected_outputs[i - inputs.len()])
            }
        });

        let rel = LookupRelation {
            exec_flag,
            row,
            table,
        };
        self.lookup_relations
            .push((self.indexers.lookup_indexer, rel));
        self.indexers.lookup_indexer += 1;
        self.indexers.lookup_outputs_indexer += N;
    }

    #[track_caller]
    pub fn append_lookup_relation<const M: usize, const N: usize>(
        &mut self,
        cs: &mut CS,
        vars: &[Variable; M],
        table: Num<F>,
        exec_flag: Boolean,
    ) -> [Variable; N] {
        // internally it'll perform witness resolution
        let inputs = vars.map(|el| LookupInput::Variable(el));
        let outputs = from_fn(|i| {
            if self.indexers.lookup_outputs_indexer + i < self.lookup_outputs.len() {
                self.lookup_outputs[self.indexers.lookup_outputs_indexer + i]
            } else {
                let x = cs.add_variable();
                self.lookup_outputs.push(x);
                x
            }
        });
        cs.peek_lookup_value_unconstrained_ext(&inputs, &outputs, table, exec_flag);
        self.append_lookup_relation_inner(&inputs, &outputs, table, exec_flag);

        outputs
    }

    #[track_caller]
    pub fn append_lookup_relation_from_linear_terms<const M: usize, const N: usize>(
        &mut self,
        cs: &mut CS,
        inputs: &[Constraint<F>; M],
        table: Num<F>,
        exec_flag: Boolean,
    ) -> [Variable; N] {
        for el in inputs.iter() {
            assert!(el.degree() <= 1);
        }
        // internally it'll perform witness resolution
        let inputs = inputs.clone().map(|el| LookupInput::from(el));
        let outputs = from_fn(|i| {
            if self.indexers.lookup_outputs_indexer + i < self.lookup_outputs.len() {
                self.lookup_outputs[self.indexers.lookup_outputs_indexer + i]
            } else {
                let x = cs.add_variable();
                self.lookup_outputs.push(x);
                x
            }
        });
        cs.peek_lookup_value_unconstrained_ext(&inputs, &outputs, table, exec_flag);
        self.append_lookup_relation_inner(&inputs, &outputs, table, exec_flag);

        outputs
    }

    pub fn enforce_all(&mut self, cs: &mut CS) {
        // we have 7 different types of relations to enforce

        // 1) enforcing add-sub relations
        let mut num_elements_processes = 0;
        let mut cur_index = 0;
        while num_elements_processes < self.add_sub_relations.len() {
            let (flags, a_s, b_s, c_s): (Vec<_>, Vec<_>, Vec<_>, Vec<_>) = {
                itertools::multiunzip(self.add_sub_relations.iter().filter_map(|e| {
                    if e.0 == cur_index {
                        Some((e.1.exec_flag, e.1.a, e.1.b, e.1.c))
                    } else {
                        None
                    }
                }))
            };
            num_elements_processes += flags.len();

            assert_eq!(flags.len(), a_s.len());
            assert_eq!(flags.len(), b_s.len());
            assert_eq!(flags.len(), c_s.len());

            let mut can_spec = true;
            {
                for el in a_s.iter().chain(b_s.iter()).chain(c_s.iter()) {
                    for i in 0..2 {
                        if let Num::Constant(..) = el.0[i] {
                            can_spec = false;
                        }
                    }
                }
            }

            // here is the trick: our all zeroes (for flags and similar) are satisfying witness for us,
            // so we can merge selection (potentially dummy one) and enforcement of the relation. The only inconvenience is
            // to set the value to the intermediate carry. Addition constraints are degree 1 over "what to add",
            // so with selection - we have degree 2

            if can_spec {
                enforce_add_sub_relation(cs, self.add_sub_ofs[cur_index], &a_s, &b_s, &c_s, &flags);
            } else {
                let mut a_constraint_low = Constraint::empty();
                let mut a_constraint_high = Constraint::empty();
                let mut b_constraint_low = Constraint::empty();
                let mut b_constraint_high = Constraint::empty();
                let mut c_constraint_low = Constraint::empty();
                let mut c_constraint_high = Constraint::empty();

                let carry_out = self.add_sub_ofs[cur_index];

                for (i, flag) in flags.iter().enumerate() {
                    a_constraint_low = mask_by_boolean_into_accumulator_constraint(
                        flag,
                        &a_s[i].0[0],
                        a_constraint_low,
                    );
                    a_constraint_high = mask_by_boolean_into_accumulator_constraint(
                        flag,
                        &a_s[i].0[1],
                        a_constraint_high,
                    );

                    b_constraint_low = mask_by_boolean_into_accumulator_constraint(
                        flag,
                        &b_s[i].0[0],
                        b_constraint_low,
                    );
                    b_constraint_high = mask_by_boolean_into_accumulator_constraint(
                        flag,
                        &b_s[i].0[1],
                        b_constraint_high,
                    );

                    c_constraint_low = mask_by_boolean_into_accumulator_constraint(
                        flag,
                        &c_s[i].0[0],
                        c_constraint_low,
                    );
                    c_constraint_high = mask_by_boolean_into_accumulator_constraint(
                        flag,
                        &c_s[i].0[1],
                        c_constraint_high,
                    );
                }

                let carry_intermediate = Boolean::new(cs);

                let constraint_low = a_constraint_low + b_constraint_low - c_constraint_low;

                let mut constraint_for_witness_eval = constraint_low.clone();
                constraint_for_witness_eval
                    .scale(F::from_u64_unchecked(1 << 16).inverse().unwrap());

                collapse_max_quadratic_constraint_into(
                    cs,
                    constraint_for_witness_eval,
                    carry_intermediate.get_variable().unwrap(),
                );

                let constraint_low = constraint_low
                    - Term::<F>::from((
                        F::from_u64_unchecked(1 << 16),
                        carry_intermediate.get_variable().unwrap(),
                    ));
                cs.add_constraint(constraint_low);

                let constraint_high = a_constraint_high + b_constraint_high - c_constraint_high
                    + Term::<F>::from(carry_intermediate.get_variable().unwrap())
                    - Term::<F>::from((
                        F::from_u64_unchecked(1 << 16),
                        carry_out.get_variable().unwrap(),
                    ));
                cs.add_constraint(constraint_high);
            }

            cur_index += 1;
        }
        assert_eq!(cur_index, self.add_sub_ofs.len());
        assert_eq!(num_elements_processes, self.add_sub_relations.len());
        #[cfg(feature = "debug_logs")]
        {
            println!("In total of {} add-sub relations at the end", cur_index);
        }

        // 2) enforcing range-check relations
        let mut num_elements_processes = 0;
        let mut cur_index = 0;
        while num_elements_processes < self.u16_to_u8x2_decomposition_relations.len() {
            let (flags, x_s): (Vec<_>, Vec<_>) = {
                itertools::multiunzip(self.u16_to_u8x2_decomposition_relations.iter().filter_map(
                    |e| {
                        if e.0 == cur_index {
                            Some((e.1.exec_flag, e.1.x))
                        } else {
                            None
                        }
                    },
                ))
            };
            num_elements_processes += flags.len();

            let x = cs.choose_from_orthogonal_variants(&flags, &x_s);
            let (low, high) = self.u16_to_u8x2_splits[cur_index];

            let in_var = x.get_variable();
            let outputs = [low.get_variable(), high.get_variable()];

            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                use crate::cs::witness_placer::WitnessComputationalInteger;
                use crate::cs::witness_placer::WitnessComputationalU16;

                let value = placer.get_u16(in_var);
                let low = value.truncate();
                let high = value.shr(8).truncate();

                placer.assign_u8(outputs[0], &low);
                placer.assign_u8(outputs[1], &high);
            };

            cs.set_values(value_fn);

            let constraint =
                Term::from(high) * Term::from(1 << 8) + Term::from(low) - Term::from(x);
            cs.add_constraint_allow_explicit_linear(constraint);

            cur_index += 1;
        }
        assert_eq!(cur_index, self.u16_to_u8x2_splits.len());
        assert_eq!(
            num_elements_processes,
            self.u16_to_u8x2_decomposition_relations.len()
        );
        #[cfg(feature = "debug_logs")]
        {
            println!(
                "In total of {} u16 -> 2xu8 decomposition relations at the end",
                cur_index
            );
        }

        // 3) enforcing u16 range-check relations
        let mut num_elements_processes = 0;
        let mut cur_index = 0;
        while num_elements_processes < self.u16_range_check_relations.len() {
            let (flags, x_s): (Vec<_>, Vec<_>) = {
                itertools::multiunzip(self.u16_range_check_relations.iter().filter_map(|e| {
                    if e.0 == cur_index {
                        Some((e.1.exec_flag, e.1.x))
                    } else {
                        None
                    }
                }))
            };
            num_elements_processes += flags.len();

            let x = cs.choose_from_orthogonal_variants(&flags, &x_s);
            cs.require_invariant(x.get_variable(), Invariant::RangeChecked { width: 16 });

            cur_index += 1;
        }
        assert_eq!(num_elements_processes, self.u16_range_check_relations.len());
        #[cfg(feature = "debug_logs")]
        {
            println!(
                "In total of {} u16 range check relations at the end",
                cur_index
            );
        }

        // 5) enforcing is zero relations
        let mut num_elements_processes = 0;
        let mut cur_index = 0;
        while num_elements_processes < self.is_zero_relations.len() {
            let (flags, regs): (Vec<_>, Vec<_>) = {
                itertools::multiunzip(self.is_zero_relations.iter().filter_map(|e| {
                    if e.0 == cur_index {
                        Some((e.1.exec_flag, e.1.reg))
                    } else {
                        None
                    }
                }))
            };
            num_elements_processes += flags.len();
            let reg = Register::choose_from_orthogonal_variants::<CS>(cs, &flags, &regs);
            let is_zero = self.is_zero_flags[cur_index].get_variable().unwrap();
            cs.is_zero_reg_explicit(reg, is_zero);

            cur_index += 1;
        }
        assert_eq!(cur_index, self.is_zero_flags.len());
        assert_eq!(num_elements_processes, self.is_zero_relations.len());
        #[cfg(feature = "debug_logs")]
        {
            println!("In total of {} `is zero` relations at the end", cur_index);
        }

        // 6) enforcing table relations
        let mut num_elements_processes = 0;
        let mut cur_index = 0;
        while num_elements_processes < self.lookup_relations.len() {
            let (flags, var_arrays, table_ids): (Vec<_>, Vec<_>, Vec<_>) = {
                itertools::multiunzip(self.lookup_relations.iter().filter_map(|e| {
                    if e.0 == cur_index {
                        Some((e.1.exec_flag, e.1.row.clone(), e.1.table))
                    } else {
                        None
                    }
                }))
            };
            num_elements_processes += flags.len();

            assert!(flags.len() > 0);

            // NOTE: here we must select such that in case if particular opcode doesn't use a table all available
            // lookups, then it would degrade to 0/0/0 case. So we select from orthogonal values, and in the worst
            // case we will indeed get 0s everywhere

            let vars: [Num<F>; COMMON_TABLE_WIDTH] = std::array::from_fn(|i| {
                let variants: Vec<Constraint<F>> = var_arrays
                    .iter()
                    .map(|els| match &els[i] {
                        LookupInput::Variable(var) => Constraint::<F>::from(*var),
                        LookupInput::Expression {
                            linear_terms,
                            constant_coeff,
                        } => {
                            let mut constraint = Constraint::<F>::from_field(*constant_coeff);
                            for (coeff, variable) in linear_terms.iter() {
                                constraint = constraint + Term::from((*coeff, *variable));
                            }

                            constraint
                        }
                    })
                    .collect();

                cs.choose_from_orthogonal_variants_for_linear_terms(&flags, &variants)
            });
            let table_id = cs.choose_from_orthogonal_variants(&flags, &table_ids);

            let inputs: [LookupInput<F>; COMMON_TABLE_WIDTH] =
                vars.map(|x| LookupInput::from(x.get_variable()));

            // we can add formal witness evaluation function here for cases when witness
            // evaluator can count everything on the fly

            let table_id_var = table_id.get_variable();
            cs.enforce_lookup_tuple_for_variable_table(&inputs, table_id_var);

            cur_index += 1;
        }
        assert_eq!(num_elements_processes, self.lookup_relations.len());

        #[cfg(feature = "debug_logs")]
        {
            println!(
                "In total of {} optimized lookup relations at the end",
                cur_index
            );
        }

        // 7) enforce mul-div relations

        // NOTE: when we will collect the elements below, we may have op1 sign to be "false",
        // but highest bit of op1 itself be 1 in case of signed multiplication. That doesn't change optimization
        let mut num_elements_processes = 0;
        let mut cur_index = 0;
        while num_elements_processes < self.mul_div_relations.len() {
            let (
                flags,
                op1_s,
                op1_signs,
                op2_s,
                op2_signs,
                additive_terms,
                add_term_signs,
                mul_low_s,
                mul_high_s,
            ): (
                Vec<_>,
                Vec<_>,
                Vec<_>,
                Vec<_>,
                Vec<_>,
                Vec<_>,
                Vec<_>,
                Vec<_>,
                Vec<_>,
            ) = {
                itertools::multiunzip(self.mul_div_relations.iter().filter_map(|e| {
                    if e.0 == cur_index {
                        Some((
                            e.1.exec_flag,
                            e.1.op_1,
                            e.1.op_1_sign,
                            e.1.op_2,
                            e.1.op_2_sign,
                            e.1.additive_term,
                            e.1.additive_term_sign,
                            e.1.mul_low,
                            e.1.mul_high,
                        ))
                    } else {
                        None
                    }
                }))
            };
            num_elements_processes += flags.len();

            let op1 = Register::choose_from_orthogonal_variants::<CS>(cs, &flags, &op1_s);
            let op1_sign = cs.choose_from_orthogonal_variants(&flags, &op1_signs);
            let op2 = Register::choose_from_orthogonal_variants::<CS>(cs, &flags, &op2_s);
            let op2_sign = cs.choose_from_orthogonal_variants(&flags, &op2_signs);
            let additive_term =
                Register::choose_from_orthogonal_variants::<CS>(cs, &flags, &additive_terms);
            let add_term_sign = cs.choose_from_orthogonal_variants(&flags, &add_term_signs);
            let mul_low = Register::choose_from_orthogonal_variants::<CS>(cs, &flags, &mul_low_s);
            let mul_high = Register::choose_from_orthogonal_variants::<CS>(cs, &flags, &mul_high_s);

            let op1_decomposition =
                RegisterDecomposition::parse_reg::<CS>(cs, op1).u8_decomposition;
            let op2_decomposition =
                RegisterDecomposition::parse_reg::<CS>(cs, op2).u8_decomposition;

            const NUM_BYTES: usize = 4;
            const NUM_BYTES_DOUBLED: usize = 8;

            // https://faculty-web.msoe.edu/johnsontimoj/Common/FILES/binary_multiplication.pdf
            // In 2’s complement you must sign extend to the product bit width
            let op1_sign_t = match op1_sign {
                Num::Var(op1_sign_var) => Term::from((F::from_u64_unchecked(0xff), op1_sign_var)),
                Num::Constant(op1_sign_constant) => {
                    if op1_sign_constant == F::ONE {
                        Term::from(0xff)
                    } else if op1_sign_constant == F::ZERO {
                        Term::from(0)
                    } else {
                        unreachable!()
                    }
                }
            };

            let op2_sign_t = match op2_sign {
                Num::Var(op2_sign_var) => Term::from((F::from_u64_unchecked(0xff), op2_sign_var)),
                Num::Constant(op2_sign_constant) => {
                    if op2_sign_constant == F::ONE {
                        Term::from(0xff)
                    } else if op2_sign_constant == F::ZERO {
                        Term::from(0)
                    } else {
                        unreachable!()
                    }
                }
            };

            let op1_t: [Term<F>; NUM_BYTES_DOUBLED] = std::array::from_fn(|idx: usize| {
                if idx < NUM_BYTES {
                    Term::from(op1_decomposition[idx])
                } else {
                    op1_sign_t
                }
            });
            let op2_t: [Term<F>; NUM_BYTES_DOUBLED] = std::array::from_fn(|idx: usize| {
                if idx < NUM_BYTES {
                    Term::from(op2_decomposition[idx])
                } else {
                    op2_sign_t
                }
            });

            let add_term_t = additive_term.get_terms();
            let mul_low_t = mul_low.get_terms();
            let mul_high_t = mul_high.get_terms();

            // low[0] + carry_out = a[0] * b[0] + a[1] * b[0] + a[0] * b[1] + rem[0]
            // carry_out is at most 16-bits long
            // low[1] + carry_out = a[1] * b[1] + a[0] * b[2] + a[2] * b[0] + a[3] * b[0] + a[2] * b[1] +
            // a[1] * b[2] + a[0] * b[3] + rem[1] + carry_in (and so on...)

            let byte_shift_t = Term::<F>::from(1 << 8);

            let sign_term = match add_term_sign {
                Num::Var(add_term_sign_var) => {
                    Term::from((F::from_u64_unchecked(0xffff), add_term_sign_var))
                }
                Num::Constant(op2_sign_constant) => {
                    if op2_sign_constant == F::ONE {
                        Term::from(0xffff)
                    } else if op2_sign_constant == F::ZERO {
                        Term::from(0)
                    } else {
                        unreachable!()
                    }
                }
            };

            // we manually unroll it to handle range checks with specific ranges

            // Important thing to consider here: we will encounter range checks for 9, 10 and 2x11 for signed case,
            // and 2x9 and 10 for unsigned. Let's consider a tradeoff:
            // - doing range checks with booleans and 8-bit chunks requires:
            //  - effectively 1 witness column for 8-bit chunk, and 2 stage-2 columns
            //  - 1 boolean by itself
            //  - total cost for signed is 4 * (1 + 2) + 1 + 2 + 2*3 = 21 columns everywhere
            //  - total cost for unsigned is 3 * (1 + 2) + 1*2 + 2 = 13 columns everywhere
            // - if we do explicit checks
            //  - 4 * (1 + 4) = 20 variables for signed case
            //  - 3 * (1 + 4) = 15 variables for unsigned case
            // So it's almost one for another, and we will stick with booleans

            // lowest 16 bits
            let carry = {
                // set values before constraint

                // max range here is (2^8 - 1) * (2^8 - 1) + 2 * 2^8 * (2^8 - 1) * (2^8 - 1) + (2^16 - 1) = 33423360 < 2^25
                // we expect lowest 16 bits to cancel completely, so we prove that it can be decomposed into 1 boolean and one 8-bit variable
                let bit = cs.add_boolean_variable();
                let byte = cs.add_variable();
                cs.require_invariant(byte, Invariant::RangeChecked { width: 8 });

                {
                    let byte_var = byte;
                    let bit_var = bit.get_variable().unwrap();

                    let op1_0 = op1_t[0].get_variable().unwrap();
                    let op1_1 = op1_t[1].get_variable().unwrap();
                    let op2_0 = op2_t[0].get_variable().unwrap();
                    let op2_1 = op2_t[1].get_variable().unwrap();
                    let add_term_t_low = add_term_t[0].get_variable().unwrap();
                    let mul_low_t_low = mul_low_t[0].get_variable().unwrap();
                    let value_fn = move |placer: &mut CS::WitnessPlacer| {
                        use crate::cs::witness_placer::WitnessComputationalU8;

                        let op1_0 = placer.get_u8(op1_0).widen().widen();
                        let op1_1 = placer.get_u8(op1_1).widen().widen();
                        let op2_0 = placer.get_u8(op2_0).widen().widen();
                        let op2_1 = placer.get_u8(op2_1).widen().widen();
                        let additive_term = placer.get_u16(add_term_t_low).widen();
                        let multiplicative_dest = placer.get_u16(mul_low_t_low).widen();

                        let mut value = op1_0.wrapping_product(&op2_0);
                        value.add_assign(&op1_0.wrapping_product(&op2_1).shl(8));
                        value.add_assign(&op1_1.wrapping_product(&op2_0).shl(8));

                        value.add_assign(&additive_term);
                        value.sub_assign(&multiplicative_dest);

                        value = value.shr(16);
                        let byte = value.truncate().truncate();
                        value = value.shr(8);
                        let bit = value.get_bit(0);

                        placer.assign_u8(byte_var, &byte);
                        placer.assign_mask(bit_var, &bit);
                    };

                    cs.set_values(value_fn);
                }

                let mut cnstr = Constraint::empty();
                cnstr = cnstr + op1_t[0] * op2_t[0];
                cnstr = cnstr + op1_t[0] * op2_t[1] * byte_shift_t;
                cnstr = cnstr + op1_t[1] * op2_t[0] * byte_shift_t;
                cnstr += add_term_t[0];
                cnstr -= mul_low_t[0];

                cnstr -= Term::from((F::from_u64_unchecked(1 << 16), byte));
                cnstr -= Term::from((F::from_u64_unchecked(1 << 24), bit.get_variable().unwrap()));

                cs.add_constraint(cnstr);

                [(byte, 0), (bit.get_variable().unwrap(), 8)]
            };

            // bits 16-32
            let carry = {
                assert_eq!(carry.len(), 2);

                // max range here is 3 * (2^8 - 1) * (2^8 - 1) + 4 * 2^8 * (2^8 - 1) * (2^8 - 1) + (2^16 - 1) + (2^9 - 1) = 66846721 < 2^26
                // we expect lowest 16 bits to cancel completely, so we prove that it can be decomposed
                let bit_0 = cs.add_boolean_variable();
                let bit_1 = cs.add_boolean_variable();
                let byte = cs.add_variable();
                cs.require_invariant(byte, Invariant::RangeChecked { width: 8 });

                // set values before constraint
                {
                    let byte_var = byte;
                    let bit_0_var = bit_0.get_variable().unwrap();
                    let bit_1_var = bit_1.get_variable().unwrap();

                    let op1_0 = op1_t[0].get_variable().unwrap();
                    let op1_1 = op1_t[1].get_variable().unwrap();
                    let op1_2 = op1_t[2].get_variable().unwrap();
                    let op1_3 = op1_t[3].get_variable().unwrap();
                    let op2_0 = op2_t[0].get_variable().unwrap();
                    let op2_1 = op2_t[1].get_variable().unwrap();
                    let op2_2 = op2_t[2].get_variable().unwrap();
                    let op2_3 = op2_t[3].get_variable().unwrap();
                    let add_term_t_high = add_term_t[1].get_variable().unwrap();
                    let mul_low_t_high = mul_low_t[1].get_variable().unwrap();

                    let value_fn = move |placer: &mut CS::WitnessPlacer| {
                        use crate::cs::witness_placer::*;

                        let op1_0 = placer.get_u8(op1_0).widen().widen();
                        let op1_1 = placer.get_u8(op1_1).widen().widen();
                        let op1_2 = placer.get_u8(op1_2).widen().widen();
                        let op1_3 = placer.get_u8(op1_3).widen().widen();
                        let op2_0 = placer.get_u8(op2_0).widen().widen();
                        let op2_1 = placer.get_u8(op2_1).widen().widen();
                        let op2_2 = placer.get_u8(op2_2).widen().widen();
                        let op2_3 = placer.get_u8(op2_3).widen().widen();

                        let additive_term = placer.get_u16(add_term_t_high).widen();
                        let multiplicative_dest = placer.get_u16(mul_low_t_high).widen();

                        let prev_carry_byte = placer.get_u8(carry[0].0).widen().widen();
                        let prev_carry_bit =
                            <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::from_mask(
                                placer.get_boolean(carry[1].0),
                            );

                        let mut value = prev_carry_byte;
                        value.add_assign(&prev_carry_bit.shl(8));

                        value.add_assign(&op1_0.wrapping_product(&op2_2));
                        value.add_assign(&op1_0.wrapping_product(&op2_3).shl(8));

                        value.add_assign(&op1_1.wrapping_product(&op2_1));
                        value.add_assign(&op1_1.wrapping_product(&op2_2).shl(8));

                        value.add_assign(&op1_2.wrapping_product(&op2_0));
                        value.add_assign(&op1_2.wrapping_product(&op2_1).shl(8));

                        value.add_assign(&op1_3.wrapping_product(&op2_0).shl(8));

                        value.add_assign(&additive_term);
                        value.sub_assign(&multiplicative_dest);

                        value = value.shr(16);
                        let byte = value.truncate().truncate();
                        value = value.shr(8);
                        let bit_0 = value.get_bit(0);
                        let bit_1 = value.get_bit(1);

                        placer.assign_u8(byte_var, &byte);
                        placer.assign_mask(bit_0_var, &bit_0);
                        placer.assign_mask(bit_1_var, &bit_1);
                    };

                    cs.set_values(value_fn);
                }

                let mut cnstr = Constraint::empty();
                cnstr += Term::from((F::from_u64_unchecked(1u64 << carry[0].1), carry[0].0));
                cnstr += Term::from((F::from_u64_unchecked(1u64 << carry[1].1), carry[1].0));

                cnstr = cnstr + op1_t[0] * op2_t[2];
                cnstr = cnstr + op1_t[0] * op2_t[3] * byte_shift_t;
                cnstr = cnstr + op1_t[1] * op2_t[1];
                cnstr = cnstr + op1_t[1] * op2_t[2] * byte_shift_t;
                cnstr = cnstr + op1_t[2] * op2_t[0];
                cnstr = cnstr + op1_t[2] * op2_t[1] * byte_shift_t;
                cnstr = cnstr + op1_t[3] * op2_t[0] * byte_shift_t;
                cnstr += add_term_t[1];
                cnstr -= mul_low_t[1];

                cnstr -= Term::from((F::from_u64_unchecked(1 << 16), byte));
                cnstr -= Term::from((
                    F::from_u64_unchecked(1 << 24),
                    bit_0.get_variable().unwrap(),
                ));
                cnstr -= Term::from((
                    F::from_u64_unchecked(1 << 25),
                    bit_1.get_variable().unwrap(),
                ));

                cs.add_constraint(cnstr);

                [
                    (byte, 0),
                    (bit_0.get_variable().unwrap(), 8),
                    (bit_1.get_variable().unwrap(), 9),
                ]
            };

            // for next terms we can have two options - if we support signed cases (so all signs are variable),
            // and if not - all are constants

            match (add_term_sign, op1_sign, op2_sign) {
                (
                    Num::Var(additive_term_sign_variable),
                    Num::Var(op1_sign_variable),
                    Num::Var(op2_sign_variable),
                ) => {
                    // bits 32-48
                    let carry = {
                        assert_eq!(carry.len(), 3);

                        // max range here is 6 * (2^8 - 1) * (2^8 - 1) + 5 * 2^8 * (2^8 - 1) * (2^8 - 1) + (2^16 - 1) + (2^10 - 1) = 83688708 < 2^27
                        // we expect lowest 16 bits to cancel completely, so we prove that it can be decomposed
                        let bit_0 = cs.add_boolean_variable();
                        let bit_1 = cs.add_boolean_variable();
                        let bit_2 = cs.add_boolean_variable();
                        let byte = cs.add_variable();
                        cs.require_invariant(byte, Invariant::RangeChecked { width: 8 });

                        // always try to set values before constraint, so we can have lazy checks
                        {
                            let byte_var = byte;
                            let bit_0_var = bit_0.get_variable().unwrap();
                            let bit_1_var = bit_1.get_variable().unwrap();
                            let bit_2_var = bit_2.get_variable().unwrap();

                            let op1_0 = op1_t[0].get_variable().unwrap();
                            let op1_1 = op1_t[1].get_variable().unwrap();
                            let op1_2 = op1_t[2].get_variable().unwrap();
                            let op1_3 = op1_t[3].get_variable().unwrap();
                            let op2_0 = op2_t[0].get_variable().unwrap();
                            let op2_1 = op2_t[1].get_variable().unwrap();
                            let op2_2 = op2_t[2].get_variable().unwrap();
                            let op2_3 = op2_t[3].get_variable().unwrap();
                            let mul_high_t_low = mul_high_t[0].get_variable().unwrap();

                            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                                use crate::cs::witness_placer::*;

                                let op1_0 = placer.get_u8(op1_0).widen().widen();
                                let op1_1 = placer.get_u8(op1_1).widen().widen();
                                let op1_2 = placer.get_u8(op1_2).widen().widen();
                                let op1_3 = placer.get_u8(op1_3).widen().widen();
                                let op2_0 = placer.get_u8(op2_0).widen().widen();
                                let op2_1 = placer.get_u8(op2_1).widen().widen();
                                let op2_2 = placer.get_u8(op2_2).widen().widen();
                                let op2_3 = placer.get_u8(op2_3).widen().widen();

                                let byte_sign_ext =
                                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0xff);
                                let word_sign_ext =
                                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0xffff);

                                let op1_sign =
                                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::from_mask(
                                        placer.get_boolean(op1_sign_variable),
                                    )
                                    .wrapping_product(&byte_sign_ext);
                                let op2_sign =
                                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::from_mask(
                                        placer.get_boolean(op2_sign_variable),
                                    )
                                    .wrapping_product(&byte_sign_ext);

                                let additive_term_sign =
                                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::from_mask(
                                        placer.get_boolean(additive_term_sign_variable),
                                    )
                                    .wrapping_product(&word_sign_ext);

                                let multiplicative_dest = placer.get_u16(mul_high_t_low).widen();

                                let prev_carry_byte = placer.get_u8(carry[0].0).widen().widen();
                                let prev_carry_bit_0 =
                                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::from_mask(
                                        placer.get_boolean(carry[1].0),
                                    );
                                let prev_carry_bit_1 =
                                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::from_mask(
                                        placer.get_boolean(carry[2].0),
                                    );

                                let mut value = prev_carry_byte;
                                value.add_assign(&prev_carry_bit_0.shl(8));
                                value.add_assign(&prev_carry_bit_1.shl(9));

                                // [0] * [4]
                                value.add_assign(&op1_0.wrapping_product(&op2_sign));
                                // [0] * [5]
                                value.add_assign(&op1_0.wrapping_product(&op2_sign).shl(8));

                                // [1] * [3]
                                value.add_assign(&op1_1.wrapping_product(&op2_3));
                                // [1] * [4]
                                value.add_assign(&op1_1.wrapping_product(&op2_sign).shl(8));

                                // [2] * [2]
                                value.add_assign(&op1_2.wrapping_product(&op2_2));
                                // [2] * [3]
                                value.add_assign(&op1_2.wrapping_product(&op2_3).shl(8));

                                // [3] * [1]
                                value.add_assign(&op1_3.wrapping_product(&op2_1));
                                // [3] * [2]
                                value.add_assign(&op1_3.wrapping_product(&op2_2).shl(8));

                                // [4] * [0]
                                value.add_assign(&op1_sign.wrapping_product(&op2_0));
                                // [4] * [1]
                                value.add_assign(&op1_sign.wrapping_product(&op2_1).shl(8));

                                // [5] * [0]
                                value.add_assign(&op1_sign.wrapping_product(&op2_0).shl(8));

                                value.add_assign(&additive_term_sign);
                                value.sub_assign(&multiplicative_dest);

                                value = value.shr(16);
                                let byte = value.truncate().truncate();
                                value = value.shr(8);
                                let bit_0 = value.get_bit(0);
                                let bit_1 = value.get_bit(1);
                                let bit_2 = value.get_bit(2);

                                placer.assign_u8(byte_var, &byte);
                                placer.assign_mask(bit_0_var, &bit_0);
                                placer.assign_mask(bit_1_var, &bit_1);
                                placer.assign_mask(bit_2_var, &bit_2);
                            };

                            cs.set_values(value_fn);
                        }

                        let mut cnstr = Constraint::empty();
                        cnstr +=
                            Term::from((F::from_u64_unchecked(1u64 << carry[0].1), carry[0].0));
                        cnstr +=
                            Term::from((F::from_u64_unchecked(1u64 << carry[1].1), carry[1].0));
                        cnstr +=
                            Term::from((F::from_u64_unchecked(1u64 << carry[2].1), carry[2].0));

                        cnstr = cnstr + op1_t[0] * op2_t[4];
                        cnstr = cnstr + op1_t[0] * op2_t[5] * byte_shift_t;
                        cnstr = cnstr + op1_t[1] * op2_t[3];
                        cnstr = cnstr + op1_t[1] * op2_t[4] * byte_shift_t;
                        cnstr = cnstr + op1_t[2] * op2_t[2];
                        cnstr = cnstr + op1_t[2] * op2_t[3] * byte_shift_t;
                        cnstr = cnstr + op1_t[3] * op2_t[1];
                        cnstr = cnstr + op1_t[3] * op2_t[2] * byte_shift_t;
                        cnstr = cnstr + op1_t[4] * op2_t[0];
                        cnstr = cnstr + op1_t[4] * op2_t[1] * byte_shift_t;
                        cnstr = cnstr + op1_t[5] * op2_t[0] * byte_shift_t;
                        cnstr += sign_term;
                        cnstr -= mul_high_t[0];

                        cnstr -= Term::from((F::from_u64_unchecked(1 << 16), byte));
                        cnstr -= Term::from((
                            F::from_u64_unchecked(1 << 24),
                            bit_0.get_variable().unwrap(),
                        ));
                        cnstr -= Term::from((
                            F::from_u64_unchecked(1 << 25),
                            bit_1.get_variable().unwrap(),
                        ));
                        cnstr -= Term::from((
                            F::from_u64_unchecked(1 << 26),
                            bit_2.get_variable().unwrap(),
                        ));

                        cs.add_constraint(cnstr);

                        [
                            (byte, 0),
                            (bit_0.get_variable().unwrap(), 8),
                            (bit_1.get_variable().unwrap(), 9),
                            (bit_2.get_variable().unwrap(), 10),
                        ]
                    };
                    // because effectively we multiply double-width (even though we make it truncating),
                    // we still need to "propagate" carry by range checking it and discarding
                    {
                        assert_eq!(carry.len(), 4);

                        // max range here is 7 * (2^8 - 1) * (2^8 - 1) + 8 * 2^8 * (2^8 - 1) * (2^8 - 1) + (2^16 - 1) + (2^11 - 1) = 133693957 < 2^27
                        // we expect lowest 16 bits to cancel completely, so we prove that it can be decomposed
                        let bit_0 = cs.add_boolean_variable();
                        let bit_1 = cs.add_boolean_variable();
                        let bit_2 = cs.add_boolean_variable();
                        let byte = cs.add_variable();
                        cs.require_invariant(byte, Invariant::RangeChecked { width: 8 });

                        {
                            let byte_var = byte;
                            let bit_0_var = bit_0.get_variable().unwrap();
                            let bit_1_var = bit_1.get_variable().unwrap();
                            let bit_2_var = bit_2.get_variable().unwrap();

                            let op1_0 = op1_t[0].get_variable().unwrap();
                            let op1_1 = op1_t[1].get_variable().unwrap();
                            let op1_2 = op1_t[2].get_variable().unwrap();
                            let op1_3 = op1_t[3].get_variable().unwrap();
                            let op2_0 = op2_t[0].get_variable().unwrap();
                            let op2_1 = op2_t[1].get_variable().unwrap();
                            let op2_2 = op2_t[2].get_variable().unwrap();
                            let op2_3 = op2_t[3].get_variable().unwrap();
                            let mul_high_t_high = mul_high_t[1].get_variable().unwrap();

                            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                                use crate::cs::witness_placer::*;

                                let op1_0 = placer.get_u8(op1_0).widen().widen();
                                let op1_1 = placer.get_u8(op1_1).widen().widen();
                                let op1_2 = placer.get_u8(op1_2).widen().widen();
                                let op1_3 = placer.get_u8(op1_3).widen().widen();
                                let op2_0 = placer.get_u8(op2_0).widen().widen();
                                let op2_1 = placer.get_u8(op2_1).widen().widen();
                                let op2_2 = placer.get_u8(op2_2).widen().widen();
                                let op2_3 = placer.get_u8(op2_3).widen().widen();

                                let byte_sign_ext =
                                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0xff);
                                let word_sign_ext =
                                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0xffff);

                                let op1_sign =
                                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::from_mask(
                                        placer.get_boolean(op1_sign_variable),
                                    )
                                    .wrapping_product(&byte_sign_ext);
                                let op2_sign =
                                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::from_mask(
                                        placer.get_boolean(op2_sign_variable),
                                    )
                                    .wrapping_product(&byte_sign_ext);

                                let additive_term_sign =
                                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::from_mask(
                                        placer.get_boolean(additive_term_sign_variable),
                                    )
                                    .wrapping_product(&word_sign_ext);

                                let multiplicative_dest = placer.get_u16(mul_high_t_high).widen();

                                let prev_carry_byte = placer.get_u8(carry[0].0).widen().widen();
                                let prev_carry_bit_0 =
                                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::from_mask(
                                        placer.get_boolean(carry[1].0),
                                    );
                                let prev_carry_bit_1 =
                                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::from_mask(
                                        placer.get_boolean(carry[2].0),
                                    );
                                let prev_carry_bit_2 =
                                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::from_mask(
                                        placer.get_boolean(carry[3].0),
                                    );

                                let mut value = prev_carry_byte;
                                value.add_assign(&prev_carry_bit_0.shl(8));
                                value.add_assign(&prev_carry_bit_1.shl(9));
                                value.add_assign(&prev_carry_bit_2.shl(10));

                                // [0] * [6]
                                value.add_assign(&op1_0.wrapping_product(&op2_sign));
                                // [0] * [7]
                                value.add_assign(&op1_0.wrapping_product(&op2_sign).shl(8));

                                // [1] * [5]
                                value.add_assign(&op1_1.wrapping_product(&op2_sign));
                                // [1] * [6]
                                value.add_assign(&op1_1.wrapping_product(&op2_sign).shl(8));

                                // [2] * [4]
                                value.add_assign(&op1_2.wrapping_product(&op2_sign));
                                // [2] * [5]
                                value.add_assign(&op1_2.wrapping_product(&op2_sign).shl(8));

                                // [3] * [3]
                                value.add_assign(&op1_3.wrapping_product(&op2_3));
                                // [3] * [4]
                                value.add_assign(&op1_3.wrapping_product(&op2_sign).shl(8));

                                // [4] * [2]
                                value.add_assign(&op1_sign.wrapping_product(&op2_2));
                                // [4] * [3]
                                value.add_assign(&op1_sign.wrapping_product(&op2_3).shl(8));

                                // [5] * [1]
                                value.add_assign(&op1_sign.wrapping_product(&op2_1));
                                // [5] * [2]
                                value.add_assign(&op1_sign.wrapping_product(&op2_2).shl(8));

                                // [6] * [0]
                                value.add_assign(&op1_sign.wrapping_product(&op2_0));
                                // [6] * [1]
                                value.add_assign(&op1_sign.wrapping_product(&op2_1).shl(8));

                                // [7] * [0]
                                value.add_assign(&op1_sign.wrapping_product(&op2_0).shl(8));

                                value.add_assign(&additive_term_sign);
                                value.sub_assign(&multiplicative_dest);

                                value = value.shr(16);
                                let byte = value.truncate().truncate();
                                value = value.shr(8);
                                let bit_0 = value.get_bit(0);
                                let bit_1 = value.get_bit(1);
                                let bit_2 = value.get_bit(2);

                                placer.assign_u8(byte_var, &byte);
                                placer.assign_mask(bit_0_var, &bit_0);
                                placer.assign_mask(bit_1_var, &bit_1);
                                placer.assign_mask(bit_2_var, &bit_2);
                            };

                            cs.set_values(value_fn);
                        }

                        let mut cnstr = Constraint::empty();
                        cnstr +=
                            Term::from((F::from_u64_unchecked(1u64 << carry[0].1), carry[0].0));
                        cnstr +=
                            Term::from((F::from_u64_unchecked(1u64 << carry[1].1), carry[1].0));
                        cnstr +=
                            Term::from((F::from_u64_unchecked(1u64 << carry[2].1), carry[2].0));
                        cnstr +=
                            Term::from((F::from_u64_unchecked(1u64 << carry[3].1), carry[3].0));

                        cnstr = cnstr + op1_t[0] * op2_t[6];
                        cnstr = cnstr + op1_t[0] * op2_t[7] * byte_shift_t;
                        cnstr = cnstr + op1_t[1] * op2_t[5];
                        cnstr = cnstr + op1_t[1] * op2_t[6] * byte_shift_t;
                        cnstr = cnstr + op1_t[2] * op2_t[4];
                        cnstr = cnstr + op1_t[2] * op2_t[5] * byte_shift_t;
                        cnstr = cnstr + op1_t[3] * op2_t[3];
                        cnstr = cnstr + op1_t[3] * op2_t[4] * byte_shift_t;
                        cnstr = cnstr + op1_t[4] * op2_t[2];
                        cnstr = cnstr + op1_t[4] * op2_t[3] * byte_shift_t;
                        cnstr = cnstr + op1_t[5] * op2_t[1];
                        cnstr = cnstr + op1_t[5] * op2_t[2] * byte_shift_t;
                        cnstr = cnstr + op1_t[6] * op2_t[0];
                        cnstr = cnstr + op1_t[6] * op2_t[1] * byte_shift_t;
                        cnstr = cnstr + op1_t[7] * op2_t[0] * byte_shift_t;
                        cnstr += sign_term;
                        cnstr -= mul_high_t[1];

                        cnstr -= Term::from((F::from_u64_unchecked(1 << 16), byte));
                        cnstr -= Term::from((
                            F::from_u64_unchecked(1 << 24),
                            bit_0.get_variable().unwrap(),
                        ));
                        cnstr -= Term::from((
                            F::from_u64_unchecked(1 << 25),
                            bit_1.get_variable().unwrap(),
                        ));
                        cnstr -= Term::from((
                            F::from_u64_unchecked(1 << 26),
                            bit_2.get_variable().unwrap(),
                        ));

                        cs.add_constraint(cnstr);
                    }
                }
                (Num::Constant(a), Num::Constant(b), Num::Constant(c))
                    if a == F::ZERO && b == F::ZERO && c == F::ZERO =>
                {
                    // we only support unsigned ops, so those terms are 0s
                    // bits 32-48
                    let carry = {
                        assert_eq!(carry.len(), 3);

                        // max range here is 3 * (2^8 - 1) * (2^8 - 1) + 2 * 2^8 * (2^8 - 1) * (2^8 - 1) + (2^10 - 1) = 33488898 < 2^25
                        // we expect lowest 16 bits to cancel completely, so we prove that it can be decomposed
                        let bit_0 = cs.add_boolean_variable();
                        let byte = cs.add_variable();
                        cs.require_invariant(byte, Invariant::RangeChecked { width: 8 });

                        {
                            let byte_var = byte;
                            let bit_0_var = bit_0.get_variable().unwrap();

                            let op1_0 = op1_t[0].get_variable().unwrap();
                            let op1_1 = op1_t[1].get_variable().unwrap();
                            let op1_2 = op1_t[2].get_variable().unwrap();
                            let op1_3 = op1_t[3].get_variable().unwrap();
                            let op2_0 = op2_t[0].get_variable().unwrap();
                            let op2_1 = op2_t[1].get_variable().unwrap();
                            let op2_2 = op2_t[2].get_variable().unwrap();
                            let op2_3 = op2_t[3].get_variable().unwrap();
                            let mul_high_t_low = mul_high_t[0].get_variable().unwrap();

                            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                                use crate::cs::witness_placer::*;

                                let _op1_0 = placer.get_u8(op1_0).widen().widen();
                                let op1_1 = placer.get_u8(op1_1).widen().widen();
                                let op1_2 = placer.get_u8(op1_2).widen().widen();
                                let op1_3 = placer.get_u8(op1_3).widen().widen();
                                let _op2_0 = placer.get_u8(op2_0).widen().widen();
                                let op2_1 = placer.get_u8(op2_1).widen().widen();
                                let op2_2 = placer.get_u8(op2_2).widen().widen();
                                let op2_3 = placer.get_u8(op2_3).widen().widen();

                                let multiplicative_dest = placer.get_u16(mul_high_t_low).widen();

                                let prev_carry_byte = placer.get_u8(carry[0].0).widen().widen();
                                let prev_carry_bit_0 =
                                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::from_mask(
                                        placer.get_boolean(carry[1].0),
                                    );
                                let prev_carry_bit_1 =
                                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::from_mask(
                                        placer.get_boolean(carry[2].0),
                                    );

                                let mut value = prev_carry_byte;
                                value.add_assign(&prev_carry_bit_0.shl(8));
                                value.add_assign(&prev_carry_bit_1.shl(9));

                                // [1] * [3]
                                value.add_assign(&op1_1.wrapping_product(&op2_3));

                                // [2] * [2]
                                value.add_assign(&op1_2.wrapping_product(&op2_2));
                                // [2] * [3]
                                value.add_assign(&op1_2.wrapping_product(&op2_3).shl(8));

                                // [3] * [1]
                                value.add_assign(&op1_3.wrapping_product(&op2_1));
                                // [3] * [2]
                                value.add_assign(&op1_3.wrapping_product(&op2_2).shl(8));

                                value.sub_assign(&multiplicative_dest);

                                value = value.shr(16);
                                let byte = value.truncate().truncate();
                                value = value.shr(8);
                                let bit_0 = value.get_bit(0);

                                placer.assign_u8(byte_var, &byte);
                                placer.assign_mask(bit_0_var, &bit_0);
                            };

                            cs.set_values(value_fn);
                        }

                        let mut cnstr = Constraint::empty();
                        cnstr +=
                            Term::from((F::from_u64_unchecked(1u64 << carry[0].1), carry[0].0));
                        cnstr +=
                            Term::from((F::from_u64_unchecked(1u64 << carry[1].1), carry[1].0));
                        cnstr +=
                            Term::from((F::from_u64_unchecked(1u64 << carry[2].1), carry[2].0));

                        cnstr = cnstr + op1_t[1] * op2_t[3];
                        cnstr = cnstr + op1_t[2] * op2_t[2];
                        cnstr = cnstr + op1_t[2] * op2_t[3] * byte_shift_t;
                        cnstr = cnstr + op1_t[3] * op2_t[1];
                        cnstr = cnstr + op1_t[3] * op2_t[2] * byte_shift_t;
                        cnstr -= mul_high_t[0];

                        cnstr -= Term::from((F::from_u64_unchecked(1 << 16), byte));
                        cnstr -= Term::from((
                            F::from_u64_unchecked(1 << 24),
                            bit_0.get_variable().unwrap(),
                        ));

                        cs.add_constraint(cnstr);

                        [(byte, 0), (bit_0.get_variable().unwrap(), 8)]
                    };
                    // and final bits just match into 0, we just need a constraint here and no decompositions
                    {
                        assert_eq!(carry.len(), 2);

                        let mut cnstr = Constraint::empty();
                        cnstr +=
                            Term::from((F::from_u64_unchecked(1u64 << carry[0].1), carry[0].0));
                        cnstr +=
                            Term::from((F::from_u64_unchecked(1u64 << carry[1].1), carry[1].0));

                        cnstr = cnstr + op1_t[3] * op2_t[3];
                        cnstr -= mul_high_t[1];

                        cs.add_constraint(cnstr);
                    }
                }
                a @ _ => {
                    panic!("Combination of signs {:?} is not supported", a);
                }
            }

            cur_index += 1;
        }

        assert_eq!(num_elements_processes, self.mul_div_relations.len());
        #[cfg(feature = "debug_logs")]
        {
            println!("In total of {} mul-div relations at the end", cur_index);
        }
    }
}
