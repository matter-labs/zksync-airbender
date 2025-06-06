use crate::constraint::Constraint;
use crate::constraint::Term;
use crate::cs::circuit::*;
use crate::cs::placeholder::Placeholder;
use crate::cs::witness_placer::WitnessComputationalInteger;
use crate::cs::witness_placer::WitnessComputationalU16;
use crate::cs::witness_placer::WitnessPlacer;
use crate::definitions::*;
use crate::devices::optimization_context::OptimizationContext;
use crate::one_row_compiler::LookupInput;
use crate::tables::TableType;
use field::PrimeField;

pub const LIMB_WIDTH: usize = 16;
pub const LIMB_MASK: u64 = (1 << LIMB_WIDTH) - 1;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Num<F: PrimeField> {
    Var(Variable),
    Constant(F),
}

impl TableType {
    pub fn to_num<F: PrimeField>(self) -> Num<F> {
        Num::Constant(F::from_u64_unchecked(self.to_table_id() as u64))
    }
}

impl<F: PrimeField> Num<F> {
    #[track_caller]
    pub fn get_variable(&self) -> Variable {
        match self {
            Num::Constant(..) => {
                panic!("this Num is not a variable")
            }
            Num::Var(v) => v.clone(),
        }
    }

    pub fn get_value<C: Circuit<F>>(&self, cs: &C) -> Option<F> {
        match *self {
            Self::Constant(c) => Some(c),
            Self::Var(var) => cs.get_value(var),
        }
    }

    pub fn get_constant_value(&self) -> F {
        match self {
            Num::Var(..) => panic!("this Num is not a constant"),
            Num::Constant(c) => *c,
        }
    }

    pub fn from_boolean_is(boolean: Boolean) -> Self {
        match boolean {
            Boolean::Is(_) => Num::Var(boolean.get_variable().unwrap()),
            Boolean::Constant(constant_value) => {
                if constant_value {
                    Num::Constant(F::ONE)
                } else {
                    Num::Constant(F::ZERO)
                }
            }
            _ => {
                panic!("Can not boolean NOT")
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Boolean {
    /// Existential view of the boolean variable
    Is(Variable),
    /// Negated view of the boolean variable
    Not(Variable),
    /// Constant (not an allocated variable)
    Constant(bool),
}

impl Boolean {
    pub const USE_SMART_AND_OR_BOUND: usize = 4;

    pub const fn uninitialized() -> Self {
        Boolean::Constant(false)
    }

    pub fn flag_for_marsking_witness_gen_function<F: PrimeField>(&self) -> F {
        match *self {
            Boolean::Is(_) => F::ZERO,
            Boolean::Not(_) => F::ONE,
            Boolean::Constant(_) => {
                panic!("flags for witness gen are not expected to come from constant booleans")
            }
        }
    }

    #[track_caller]
    pub fn get_variable(&self) -> Option<Variable> {
        match *self {
            Boolean::Is(v) => Some(v),
            Boolean::Not(_v) => unreachable!(),
            Boolean::Constant(_) => None,
        }
    }

    pub fn new<F: PrimeField, C: Circuit<F>>(circuit: &mut C) -> Self {
        circuit.add_boolean_variable()
    }

    pub fn get_value<F: PrimeField, C: Circuit<F>>(&self, cs: &C) -> Option<bool> {
        match *self {
            Self::Constant(c) => Some(c),
            Self::Is(var) => cs.get_value(var).map(|el| el.as_boolean()),
            Self::Not(var) => cs.get_value(var).map(|el| !el.as_boolean()),
        }
    }

    pub fn get_terms<F: PrimeField>(&self) -> Term<F> {
        match self {
            &Boolean::Is(var) => var.into(),
            &Boolean::Not(_var) => {
                unreachable!()
                // Term::from(1) - Term::from(var)
            }
            &Boolean::Constant(var) => {
                let var = var as u64;
                var.into()
            }
        }
    }

    #[track_caller]
    pub fn variable_and_negation_constant(&self) -> (Variable, bool) {
        match self {
            Boolean::Constant(_) => {
                panic!("Constant is not expected here");
            }
            Boolean::Is(var) => (*var, false),
            Boolean::Not(var) => (*var, true),
        }
    }

    pub fn split_into_bitmask<F: PrimeField, CS: Circuit<F>, const N: usize>(
        circuit: &mut CS,
        full_bitmask: Num<F>,
    ) -> [Boolean; N] {
        if N == 0 {
            return [Boolean::Constant(false); N];
        }

        assert!(N <= F::CHAR_BITS - 1);

        let type_bitmask: [Boolean; N] = std::array::from_fn(|_| Boolean::new(circuit));
        let type_bitmask_terms: [Term<F>; N] = type_bitmask.map(|x| x.into());
        let full_bitmask_as_int: Term<F> = full_bitmask.into();

        let input = full_bitmask.get_variable();
        let outputs = type_bitmask.map(|el| {
            let Boolean::Is(var) = el else { unreachable!() };

            var
        });

        //setting values
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            use crate::cs::witness_placer::*;
            let input_value = placer.get_field(input).as_integer();

            for idx in 0..N {
                let bit = input_value.get_bit(idx as u32);
                placer.assign_mask(outputs[idx], &bit);
            }
        };

        circuit.set_values(value_fn);

        let constraint = (0..N).fold(Constraint::empty(), |acc, x| {
            acc + Term::from(type_bitmask_terms[x]) * Term::from(1 << x)
        }) - full_bitmask_as_int;
        circuit.add_constraint_allow_explicit_linear(constraint);

        type_bitmask
    }

    pub fn split_into_bitmask_vec<F: PrimeField, C: Circuit<F>>(
        circuit: &mut C,
        full_bitmask: Num<F>,
        bit_size: usize,
    ) -> Vec<Boolean> {
        if bit_size == 0 {
            return vec![];
        }

        seq_macro::seq!(N in 0..32 {
            if bit_size == N {
                return Self::split_into_bitmask::<F, C, N>(circuit, full_bitmask).to_vec();
            }
        });

        panic!("unsupported number of bits: {}", bit_size);
    }

    pub fn toggle(&self) -> Self {
        match self {
            &Boolean::Constant(c) => Boolean::Constant(!c),
            &Boolean::Is(ref v) => Boolean::Not(v.clone()),
            &Boolean::Not(ref v) => Boolean::Is(v.clone()),
        }
    }

    pub fn and_constraint<F: PrimeField>(a: &Self, b: &Self) -> Constraint<F> {
        match (a, b) {
            // false AND x is always false
            (&Boolean::Constant(false), _) | (_, &Boolean::Constant(false)) => {
                Constraint::from(false)
            }
            // true AND x is always x
            (&Boolean::Constant(true), &x) | (&x, &Boolean::Constant(true)) => Constraint::from(x),
            // a AND (NOT b)
            (&Boolean::Is(is), &Boolean::Not(not)) | (&Boolean::Not(not), &Boolean::Is(is)) => {
                // This constrain for and_not: (a) * (1 - b) = (c), ensuring c is 1 iff
                // a is true and b is false, and otherwise c is 0.
                let constr = Term::from(is) * (Term::from(1) - Term::from(not));
                constr
            }
            // (NOT a) AND (NOT b) = a NOR b
            (&Boolean::Not(a), &Boolean::Not(b)) => {
                // This constrain for nor: (1 - a) * (1 - b) = (c), ensuring c is 1 iff
                // a and b are both false, and otherwise c is 0.

                // a*b - a - b  + 1 = c
                let constr =
                    Term::from(a) * Term::from(b) - Term::from(a) - Term::from(b) + (Term::from(1));
                constr
            }
            // a AND b
            (&Boolean::Is(a), &Boolean::Is(b)) => {
                // This constrain for and (a) * (b) = (c), ensuring c is 1 iff
                // a AND b are both 1.
                let constr = Term::from(a) * Term::from(b);
                constr
            }
        }
    }

    #[track_caller]
    pub fn and<F: PrimeField, C: Circuit<F>>(a: &Self, b: &Self, cs: &mut C) -> Self {
        match (a, b) {
            // false AND x is always false
            (&Boolean::Constant(false), _) | (_, &Boolean::Constant(false)) => {
                Boolean::Constant(false)
            }
            // true AND x is always x
            (&Boolean::Constant(true), x) | (x, &Boolean::Constant(true)) => x.clone(),
            // a AND (NOT b)
            (&Boolean::Is(is), &Boolean::Not(not)) | (&Boolean::Not(not), &Boolean::Is(is)) => {
                // This constrain for and_not: (a) * (1 - b) = (c), ensuring c is 1 iff
                // a is true and b is false, and otherwise c is 0.

                let var = Boolean::Is(cs.add_variable_from_constraint(
                    Term::from(is) * (Term::from(1) - Term::from(not)),
                ));

                var
            }
            // (NOT a) AND (NOT b) = (1 - a) * (1 - b)
            (&Boolean::Not(a), &Boolean::Not(b)) => {
                let var = Boolean::Is(cs.add_variable_from_constraint(
                    (Term::from(1) - Term::from(a)) * (Term::from(1) - Term::from(b)),
                ));

                var
            }
            // a AND b
            (&Boolean::Is(a), &Boolean::Is(b)) => {
                // This constrain for and (a) * (b) = (c), ensuring c is 1 iff
                // a AND b are both 1.
                let var =
                    Boolean::Is(cs.add_variable_from_constraint(Term::from(a) * Term::from(b)));

                var
            }
        }
    }

    pub fn or<F: PrimeField, C: Circuit<F>>(a: &Self, b: &Self, cs: &mut C) -> Self {
        match (a, b) {
            // true OR  x is always true
            (&Boolean::Constant(true), _) | (_, &Boolean::Constant(true)) => {
                Boolean::Constant(true)
            }
            // false OR x is always x
            (&Boolean::Constant(false), x) | (x, &Boolean::Constant(false)) => x.clone(),
            // a OR (NOT b) = NOT( a AND Not b)
            (&Boolean::Is(is), &Boolean::Not(not)) | (&Boolean::Not(not), &Boolean::Is(is)) => {
                // 1 - b + ab
                let var = Boolean::Is(cs.add_variable_from_constraint(
                    Term::from(1) - Term::from(not) + Term::from(is) * Term::from(not),
                ));

                var
            }
            // (NOT a) OR (NOT b) = a NOR b
            (&Boolean::Not(_), &Boolean::Not(_)) => {
                unreachable!();
            }
            // a OR b
            (&Boolean::Is(a), &Boolean::Is(b)) => {
                // 1 - b + ab
                // res = 1 - (1 - a)(1-b) = a + b - ab
                let var = Boolean::Is(cs.add_variable_from_constraint(
                    Constraint::from(a) + Term::from(b) - Term::from(a) * Term::from(b),
                ));

                var
            }
        }
    }

    #[track_caller]
    pub fn xor<F: PrimeField, C: Circuit<F>>(a: &Self, b: &Self, cs: &mut C) -> Self {
        match (a, b) {
            (&Boolean::Constant(false), x) | (x, &Boolean::Constant(false)) => x.clone(),
            (&Boolean::Constant(true), x) | (x, &Boolean::Constant(true)) => x.toggle(),
            // a XOR (NOT b) = NOT(a XOR b)
            (_is @ &Boolean::Is(_), _not @ &Boolean::Not(_))
            | (_not @ &Boolean::Not(_), _is @ &Boolean::Is(_)) => {
                unreachable!();

                //Boolean::xor(is, &not.toggle(), cs).toggle()
            }
            // a XOR b = (NOT a) XOR (NOT b)
            (&Boolean::Is(a), &Boolean::Is(b)) => {
                if a == b {
                    return Boolean::Constant(false);
                }
                // res = 1 - (1 - a)(1-b) = a + b - 2 * ab
                let var = Boolean::Is(cs.add_variable_from_constraint(
                    Constraint::from(a) + Term::from(b)
                        - Term::from(a) * Term::from(b) * Term::from(2),
                ));

                var
            }
            // a XOR b = (NOT a) XOR (NOT b)
            (&Boolean::Not(_a), &Boolean::Not(_b)) => {
                unreachable!();

                /*if a == b {
                    return Boolean::Constant(false);
                }
                // res = 1 - (1 - a)(1-b) = a + b - 2 * ab
                Boolean::Is(cs.add_variable_from_constraint(
                    Constraint::from(a) + Term::from(b)
                        - Term::from(a) * Term::from(b) * Term::from(2),
                ))*/
            }
        }
    }

    pub fn nor<F: PrimeField, C: Circuit<F>>(a: &Self, b: &Self, cs: &mut C) -> Self {
        match (a, b) {
            // true NOR x is always false
            (&Boolean::Constant(true), _) | (_, &Boolean::Constant(true)) => {
                Boolean::Constant(false)
            }
            (&Boolean::Constant(false), x) | (x, &Boolean::Constant(false)) => x.toggle(),
            // a NOR (NOT b) = b AND NOT a
            (&Boolean::Is(_is), &Boolean::Not(_not)) | (&Boolean::Not(_not), &Boolean::Is(_is)) => {
                unreachable!();
            }
            // (NOT a) NOR (NOT b) = a AND b
            (&Boolean::Not(_a), &Boolean::Not(_b)) => {
                unreachable!();
            }
            // a NOR b
            (&Boolean::Is(a), &Boolean::Is(b)) => {
                // res = (1 - a)(1 - b) = 1 - a - b + ab
                let var = Boolean::Is(cs.add_variable_from_constraint(
                    (Term::from(1) - Term::from(a)) * (Term::from(1) - Term::from(b)),
                ));

                var
            }
        }
    }

    pub fn multi_and<F: PrimeField, C: Circuit<F>>(arr: &[Self], cs: &mut C) -> Self {
        let mut meaningful_terms = Vec::with_capacity(arr.len());
        for el in arr.iter() {
            match el {
                Boolean::Constant(c) => {
                    if *c {
                        // constant true, fine
                    } else {
                        panic!("multi_and contains constant false");
                    }
                }
                a @ _ => {
                    meaningful_terms.push(*a);
                }
            }
        }

        assert!(meaningful_terms.len() > 0);
        if meaningful_terms.len() == 1 {
            return meaningful_terms[0];
        }
        let new_var = if meaningful_terms.len() <= Self::USE_SMART_AND_OR_BOUND {
            meaningful_terms
                .iter()
                .skip(1)
                .fold(meaningful_terms[0], |acc, x| Self::and::<F, C>(&acc, x, cs))
        } else {
            let mut cnstr = meaningful_terms
                .iter()
                .fold(Constraint::<F>::empty(), |acc, x| acc + x.get_terms());
            cnstr -= Term::from(meaningful_terms.len() as u64);
            let tmp = Num::Var(cs.add_variable_from_constraint_allow_explicit_linear(cnstr));
            // if sum of booleans is equal to number of them - than all of those were `true`

            cs.is_zero(tmp)
        };

        new_var
    }

    pub fn multi_or<F: PrimeField, C: Circuit<F>>(arr: &[Self], cs: &mut C) -> Self {
        let mut meaningful_terms = Vec::with_capacity(arr.len());
        for el in arr.iter() {
            match el {
                Boolean::Constant(c) => {
                    if *c {
                        return Boolean::Constant(true);
                    } else {
                        // nothing, do not add
                    }
                }
                a @ _ => {
                    meaningful_terms.push(*a);
                }
            }
        }

        assert!(meaningful_terms.len() > 0);
        if meaningful_terms.len() == 1 {
            return meaningful_terms[0];
        }

        let new_var = if meaningful_terms.len() <= Self::USE_SMART_AND_OR_BOUND {
            meaningful_terms
                .iter()
                .skip(1)
                .fold(meaningful_terms[0], |acc, x| Self::or::<F, C>(&acc, x, cs))
        } else {
            let cnstr = meaningful_terms
                .iter()
                .fold(Constraint::<F>::empty(), |acc, x| acc + Term::from(*x));
            let tmp = cs.add_variable_from_constraint(cnstr);
            let tmp = Num::Var(tmp);

            let sum_is_zero = cs.is_zero(tmp);
            sum_is_zero.toggle()
        };
        new_var
    }

    #[track_caller]
    pub fn choose_from_orthogonal_flags<F: PrimeField, C: Circuit<F>>(
        cs: &mut C,
        conds: &[Self],
        flags: &[Self],
    ) -> Self {
        assert_eq!(conds.len(), flags.len());
        let mut constraint = Constraint::<F>::empty();
        for (condition, flag) in conds.iter().zip(flags.iter()) {
            match *flag {
                Boolean::Constant(false) => {
                    // we can just ignore it
                    continue;
                }
                _ => {}
            }

            match *condition {
                Boolean::Constant(cond) => {
                    if cond {
                        panic!("Constant true in orthogonal flags");
                    } else {
                        // just ignore
                    }
                }
                cond @ _ => {
                    constraint = constraint + Boolean::and_constraint(&cond, flag);
                }
            };
        }

        if constraint.is_empty() {
            return Boolean::Constant(false);
        }
        let res = cs.add_variable_from_constraint(constraint);

        Boolean::Is(res)
    }

    #[track_caller]
    pub fn choose<F: PrimeField, CS: Circuit<F>>(
        cs: &mut CS,
        flag: &Self,
        if_true_val: &Self,
        if_false_val: &Self,
    ) -> Self {
        match (if_true_val, if_false_val) {
            (&Boolean::Constant(a), &Boolean::Constant(b)) => {
                if a == b {
                    return Boolean::Constant(a);
                }
                match flag {
                    &Boolean::Constant(flag) => {
                        let result_value = if flag { a } else { b };

                        Boolean::Constant(result_value)
                    }
                    &Boolean::Is(cond) => {
                        let new_var = cs.add_variable();

                        let value_fn = move |placer: &mut CS::WitnessPlacer| {
                            use crate::cs::witness_placer::*;
                            let a = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(a);
                            let b = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(b);
                            let mask = placer.get_boolean(cond);
                            let value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                                &mask, &a, &b,
                            );
                            placer.assign_mask(new_var, &value);
                        };
                        cs.set_values(value_fn);

                        // a * condition + b*(1-condition) = c ->
                        // (a - b) *condition - c + b = 0
                        let cnstr: Constraint<F> = {
                            Term::from(cond) * (Term::from(a as u64) - Term::from(b as u64))
                                + Term::from(b as u64)
                                - Term::from(new_var)
                        };
                        cs.add_constraint_allow_explicit_linear(cnstr);
                        Boolean::Is(new_var)
                    }

                    &Boolean::Not(_cond) => {
                        unreachable!();
                    }
                }
            }
            (&Boolean::Is(a), &Boolean::Is(b)) => {
                if a == b {
                    return if_true_val.clone();
                }

                match flag {
                    &Boolean::Constant(flag) => {
                        if flag {
                            *if_true_val
                        } else {
                            *if_false_val
                        }
                    }
                    &Boolean::Is(cond) => {
                        let new_var = cs.add_variable();

                        let value_fn = move |placer: &mut CS::WitnessPlacer| {
                            use crate::cs::witness_placer::*;
                            let a = placer.get_boolean(a);
                            let b = placer.get_boolean(b);
                            let mask = placer.get_boolean(cond);
                            let value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                                &mask, &a, &b,
                            );
                            placer.assign_mask(new_var, &value);
                        };

                        cs.set_values(value_fn);
                        // if_true_val = a, if_false_val = b
                        // new_var = flag * a + (1 - flag) * b = flag * (a - b) + b
                        let cnstr: Constraint<F> = {
                            Term::from(cond) * (Term::from(a) - Term::from(b)) + Term::from(b)
                                - Term::from(new_var)
                        };
                        cs.add_constraint(cnstr);
                        Boolean::Is(new_var)
                    }

                    &Boolean::Not(_cond) => {
                        unreachable!();
                    }
                }
            }
            (&Boolean::Not(_a), &Boolean::Not(_b)) => {
                unreachable!();
            }
            (&Boolean::Is(a), &Boolean::Constant(constant)) => {
                match flag {
                    &Boolean::Constant(flag) => {
                        if flag {
                            return Boolean::Is(a.clone());
                        } else {
                            return Boolean::Constant(constant);
                        }
                    }
                    &Boolean::Is(cond) => {
                        let new_var = cs.add_variable();

                        let value_fn = move |placer: &mut CS::WitnessPlacer| {
                            use crate::cs::witness_placer::*;
                            let a = placer.get_boolean(a);
                            let b =
                                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(constant);
                            let mask = placer.get_boolean(cond);
                            let value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                                &mask, &a, &b,
                            );
                            placer.assign_mask(new_var, &value);
                        };

                        cs.set_values(value_fn);

                        // new_var = flag * a + (1 - flag) * constant = flag * (if_true - constant) + constant
                        let cnstr: Constraint<F> = {
                            Term::from(cond)
                                * (Term::from(a)
                                    - Term::from_field(F::from_u64_unchecked(constant as u64)))
                                + Term::from_field(F::from_u64_unchecked(constant as u64))
                                - Term::from(new_var)
                        };
                        cs.add_constraint(cnstr);
                        Boolean::Is(new_var)
                    }

                    &Boolean::Not(_cond) => {
                        unreachable!();
                    }
                }
            }
            (&Boolean::Constant(constant), &Boolean::Is(b)) => {
                // Self::choose(cs, &flag.toggle(), if_false_val, if_true_val)
                match flag {
                    &Boolean::Constant(flag) => {
                        if flag {
                            return Boolean::Constant(constant);
                        } else {
                            return Boolean::Is(b.clone());
                        }
                    }
                    &Boolean::Is(cond) => {
                        let new_var = cs.add_variable();

                        let value_fn = move |placer: &mut CS::WitnessPlacer| {
                            use crate::cs::witness_placer::*;
                            let a =
                                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(constant);
                            let b = placer.get_boolean(b);
                            let mask = placer.get_boolean(cond);
                            let value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                                &mask, &a, &b,
                            );
                            placer.assign_mask(new_var, &value);
                        };

                        cs.set_values(value_fn);

                        // new_var = flag * constant + (1 - flag) * b = flag * (constant - b) + b
                        let cnstr: Constraint<F> = {
                            Term::from(cond)
                                * (Term::from_field(F::from_u64_unchecked(constant as u64))
                                    - Term::from(b))
                                + Term::from(b)
                                - Term::from(new_var)
                        };
                        cs.add_constraint(cnstr);
                        Boolean::Is(new_var)
                    }

                    &Boolean::Not(..) => {
                        unreachable!();
                    }
                }
            }
            (&Boolean::Not(_a), &Boolean::Constant(_constant)) => {
                unreachable!();
            }
            (&Boolean::Constant(..), &Boolean::Not(..)) => {
                unreachable!();
            }
            (&Boolean::Is(_a), &Boolean::Not(_b)) => {
                unreachable!();
            }
            (&Boolean::Not(..), &Boolean::Is(..)) => {
                unreachable!();
            }
        }
    }

    #[track_caller]
    pub fn choose_from_orthogonal_flag<F: PrimeField, CS: Circuit<F>>(
        cs: &mut CS,
        flag: &Self,
        if_true_val: &Self,
        if_false_val: &Self,
    ) -> Self {
        match (if_true_val, if_false_val) {
            (&Boolean::Constant(a), &Boolean::Constant(b)) => {
                if a == b {
                    return Boolean::Constant(a);
                }
                match flag {
                    &Boolean::Constant(flag) => {
                        let result_value = if flag { a } else { b };

                        Boolean::Constant(result_value)
                    }
                    &Boolean::Is(cond) => {
                        let new_var = cs.add_variable();

                        let value_fn = move |placer: &mut CS::WitnessPlacer| {
                            use crate::cs::witness_placer::*;
                            let a = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(a);
                            let b = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(b);
                            let mask = placer.get_boolean(cond);
                            let value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                                &mask, &a, &b,
                            );
                            placer.assign_mask(new_var, &value);
                        };

                        cs.set_values(value_fn);

                        // a * condition + b*(1-condition) = c ->
                        // (a - b) *condition - c + b = 0
                        let cnstr: Constraint<F> = {
                            Term::from(cond) * (Term::from(a as u64) - Term::from(b as u64))
                                + Term::from(b as u64)
                                - Term::from(new_var)
                        };
                        cs.add_constraint_allow_explicit_linear(cnstr);
                        Boolean::Is(new_var)
                    }

                    &Boolean::Not(_cond) => {
                        unreachable!();
                    }
                }
            }
            (&Boolean::Is(a), &Boolean::Is(b)) => {
                if a == b {
                    return if_true_val.clone();
                }

                match flag {
                    &Boolean::Constant(flag) => {
                        if flag {
                            *if_true_val
                        } else {
                            *if_false_val
                        }
                    }
                    &Boolean::Is(cond) => {
                        let new_var = cs.add_variable();

                        let value_fn = move |placer: &mut CS::WitnessPlacer| {
                            use crate::cs::witness_placer::*;
                            let a = placer.get_boolean(a);
                            let b = placer.get_boolean(b);
                            let mask = placer.get_boolean(cond);
                            let value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                                &mask, &a, &b,
                            );
                            placer.assign_mask(new_var, &value);
                        };

                        cs.set_values(value_fn);

                        // if_true_val = a, if_false_val = b
                        // new_var = flag * a + (1 - flag) * b = flag * (a - b) + b
                        let cnstr: Constraint<F> = {
                            Term::from(cond) * (Term::from(a) - Term::from(b)) + Term::from(b)
                                - Term::from(new_var)
                        };
                        cs.add_constraint(cnstr);
                        Boolean::Is(new_var)
                    }

                    &Boolean::Not(_cond) => {
                        unreachable!();
                    }
                }
            }
            (&Boolean::Not(_a), &Boolean::Not(_b)) => {
                unreachable!();
            }
            (&Boolean::Is(a), &Boolean::Constant(constant)) => {
                match flag {
                    &Boolean::Constant(flag) => {
                        if flag {
                            return Boolean::Is(a.clone());
                        } else {
                            return Boolean::Constant(constant);
                        }
                    }
                    &Boolean::Is(cond) => {
                        let new_var = cs.add_variable();

                        let value_fn = move |placer: &mut CS::WitnessPlacer| {
                            use crate::cs::witness_placer::*;
                            let a = placer.get_boolean(a);
                            let b =
                                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(constant);
                            let mask = placer.get_boolean(cond);
                            let value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                                &mask, &a, &b,
                            );
                            placer.assign_mask(new_var, &value);
                        };

                        cs.set_values(value_fn);

                        // new_var = flag * a + (1 - flag) * constant = flag * (if_true - constant) + constant
                        let cnstr: Constraint<F> = {
                            Term::from(cond)
                                * (Term::from(a)
                                    - Term::from_field(F::from_u64_unchecked(constant as u64)))
                                + Term::from_field(F::from_u64_unchecked(constant as u64))
                                - Term::from(new_var)
                        };
                        cs.add_constraint(cnstr);
                        Boolean::Is(new_var)
                    }

                    &Boolean::Not(_cond) => {
                        unreachable!();
                    }
                }
            }
            (&Boolean::Constant(constant), &Boolean::Is(b)) => {
                // Self::choose(cs, &flag.toggle(), if_false_val, if_true_val)
                match flag {
                    &Boolean::Constant(flag) => {
                        if flag {
                            return Boolean::Constant(constant);
                        } else {
                            return Boolean::Is(b.clone());
                        }
                    }
                    &Boolean::Is(cond) => {
                        let new_var = cs.add_variable();

                        let value_fn = move |placer: &mut CS::WitnessPlacer| {
                            use crate::cs::witness_placer::*;
                            let a =
                                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(constant);
                            let b = placer.get_boolean(b);
                            let mask = placer.get_boolean(cond);
                            let value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                                &mask, &a, &b,
                            );
                            placer.assign_mask(new_var, &value);
                        };

                        cs.set_values(value_fn);

                        // new_var = flag * constant + (1 - flag) * b = flag * (constant - b) + b
                        let cnstr: Constraint<F> = {
                            Term::from(cond)
                                * (Term::from_field(F::from_u64_unchecked(constant as u64))
                                    - Term::from(b))
                                + Term::from(b)
                                - Term::from(new_var)
                        };
                        cs.add_constraint(cnstr);
                        Boolean::Is(new_var)
                    }

                    &Boolean::Not(..) => {
                        unreachable!();
                    }
                }
            }
            (&Boolean::Not(_a), &Boolean::Constant(_constant)) => {
                unreachable!();
            }
            (&Boolean::Constant(..), &Boolean::Not(..)) => {
                unreachable!();
            }
            (&Boolean::Is(_a), &Boolean::Not(_b)) => {
                unreachable!();
            }
            (&Boolean::Not(..), &Boolean::Is(..)) => {
                unreachable!();
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Register<F: PrimeField>(pub [Num<F>; REGISTER_SIZE]);

impl<F: PrimeField> Register<F> {
    pub const fn uninitialized() -> Self {
        Self([Num::Constant(F::ZERO), Num::Constant(F::ZERO)])
    }

    #[track_caller]
    pub fn new<C: Circuit<F>>(circuit: &mut C) -> Self {
        let low = circuit.add_variable_with_range_check(LIMB_WIDTH as u32);
        let high = circuit.add_variable_with_range_check(LIMB_WIDTH as u32);

        Self([low, high])
    }

    pub fn new_unchecked<C: Circuit<F>>(circuit: &mut C) -> Self {
        let vars: [Num<F>; 2] = std::array::from_fn(|_| Num::Var(circuit.add_variable()));
        Self(vars)
    }

    pub fn new_unchecked_from_placeholder<CS: Circuit<F>>(
        cs: &mut CS,
        placeholder: Placeholder,
    ) -> Self {
        let new = Self::new_unchecked(cs);

        // set value
        let vars = new.0.map(|el| el.get_variable());
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let value = placer.get_oracle_u32(placeholder);

            placer.assign_u32_from_u16_parts(vars, &value);
        };

        cs.set_values(value_fn);

        new
    }

    #[track_caller]
    pub fn get_value_unsigned<C: Circuit<F>>(self, cs: &C) -> Option<u32> {
        let low = cs.get_value(self.0[0].get_variable())?.as_u64_reduced();
        let high = cs.get_value(self.0[1].get_variable())?.as_u64_reduced();

        assert!(low <= u16::MAX as u64);
        assert!(high <= u16::MAX as u64);

        Some(low as u32 | (high as u32) << 16)
    }

    pub fn get_value_signed<C: Circuit<F>>(self, cs: &C) -> Option<i32> {
        let unsigned = self.get_value_unsigned(cs)?;
        let signed = unsigned as i32;
        Some(signed)
    }

    pub fn new_from_constant(value: u32) -> Self {
        let vars: [Num<F>; 2] = std::array::from_fn(|idx: usize| {
            Num::Constant(F::from_u64_unchecked(((value >> idx * 16) & 0xffff) as u64))
        });
        Self(vars)
    }

    pub fn get_terms(&self) -> [Term<F>; REGISTER_SIZE] {
        self.0.map(|x| x.into())
    }

    #[track_caller]
    pub fn choose<C: Circuit<F>>(
        cs: &mut C,
        flag: &Boolean,
        if_true_variant: &Self,
        if_false_variant: &Self,
    ) -> Self {
        let low = cs.choose(*flag, if_true_variant.0[0], if_false_variant.0[0]);
        let high = cs.choose(*flag, if_true_variant.0[1], if_false_variant.0[1]);
        Register([low, high])
    }

    pub fn update_if_flag_is_set<C: Circuit<F>>(
        &mut self,
        cs: &mut C,
        flag: &Boolean,
        new_val: &Self,
    ) {
        *self = Register::choose(cs, flag, new_val, self);
    }

    #[track_caller]
    pub fn choose_from_orthogonal_variants<C: Circuit<F>>(
        cs: &mut C,
        flags: &[Boolean],
        variants: &[Self],
    ) -> Self {
        assert_eq!(flags.len(), variants.len());
        let low_parts: Vec<Num<F>> = variants.iter().map(|x| x.0[0]).collect();
        let high_parts: Vec<Num<F>> = variants.iter().map(|x| x.0[1]).collect();

        let low = cs.choose_from_orthogonal_variants(&flags, &low_parts);
        let high = cs.choose_from_orthogonal_variants(&flags, &high_parts);
        Register([low, high])
    }

    pub fn equals_to<C: Circuit<F>>(&self, cs: &mut C, cnst: u32) -> Boolean {
        let low_cnst = Num::Constant(F::from_u64_unchecked((cnst & 0xffff) as u64));
        let high_cnst = Num::Constant(F::from_u64_unchecked((cnst >> 16) as u64));

        let low_eq_flag = cs.equals_to(self.0[0], low_cnst);
        let high_eq_flag = cs.equals_to(self.0[1], high_cnst);
        Boolean::and::<F, C>(&low_eq_flag, &high_eq_flag, cs)
    }

    pub fn is_zero<C: Circuit<F>>(&self, cs: &mut C) -> Boolean {
        self.equals_to::<C>(cs, 0)
    }

    pub fn mask<C: Circuit<F>>(&self, cs: &mut C, flag: Boolean) -> Self {
        let low = cs.choose(flag, self.0[0], Num::Constant(F::ZERO));
        let high = cs.choose(flag, self.0[1], Num::Constant(F::ZERO));

        Register([low, high])
    }
}

#[deprecated]
#[derive(Clone, Debug, Copy)]
pub struct RegisterDecomposition<F: PrimeField> {
    pub u16_limbs: [Num<F>; 2],
    pub u8_decomposition: [Num<F>; 4],
}

impl<F: PrimeField> RegisterDecomposition<F> {
    pub fn into_register(&self) -> Register<F> {
        Register(self.u16_limbs)
    }

    pub unsafe fn split_unchecked<CS: Circuit<F>>(cs: &mut CS, reg: &Register<F>) -> Self {
        let chunks: [Num<F>; 4] = std::array::from_fn(|_: usize| Num::Var(cs.add_variable()));
        cs.add_constraint(
            Term::from(chunks[1]) * Term::from(1 << 8) + Term::from(chunks[0])
                - Term::from(reg.0[0]),
        );
        cs.add_constraint(
            Term::from(chunks[3]) * Term::from(1 << 8) + Term::from(chunks[2])
                - Term::from(reg.0[1]),
        );

        let outputs = chunks.map(|x| x.get_variable());
        let register_limbs = [reg.0[0].get_variable(), reg.0[1].get_variable()];
        //setting values for overflow flags
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let low_limb = placer.get_u16(register_limbs[0]);
            let high_limb = placer.get_u16(register_limbs[1]);

            let byte0 = low_limb.truncate();
            let byte1 = low_limb.shr(8).truncate();

            let byte2 = high_limb.truncate();
            let byte3 = high_limb.shr(8).truncate();

            placer.assign_u8(outputs[0], &byte0);
            placer.assign_u8(outputs[1], &byte1);
            placer.assign_u8(outputs[2], &byte2);
            placer.assign_u8(outputs[3], &byte3);
        };

        cs.set_values(value_fn);

        RegisterDecomposition {
            u16_limbs: [reg.0[0], reg.0[1]],
            u8_decomposition: chunks,
        }
    }

    pub const fn uninitialized() -> Self {
        RegisterDecomposition {
            u16_limbs: [Num::Constant(F::ZERO); 2],
            u8_decomposition: [Num::Constant(F::ZERO); 4],
        }
    }

    #[track_caller]
    pub fn split_reg_with_opt_ctx<CS: Circuit<F>>(
        circuit: &mut CS,
        reg: Register<F>,
        opt_ctx: &mut OptimizationContext<F, CS>,
        exec_flag: Boolean,
    ) -> Self {
        if exec_flag.get_value(&*circuit).unwrap_or(false) {
            if let Some(value) = reg.0[0].get_value(&*circuit) {
                assert!(value.as_u64_reduced() <= u16::MAX as u64);
            }

            if let Some(value) = reg.0[1].get_value(&*circuit) {
                assert!(value.as_u64_reduced() <= u16::MAX as u64);
            }
        }

        let u16_low_splitting =
            opt_ctx.append_u16_to_le_u8_decomposition_relation(reg.0[0], exec_flag, circuit);
        let u16_high_splitting =
            opt_ctx.append_u16_to_le_u8_decomposition_relation(reg.0[1], exec_flag, circuit);

        RegisterDecomposition {
            u16_limbs: [reg.0[0], reg.0[1]],
            u8_decomposition: [
                u16_low_splitting[0],
                u16_low_splitting[1],
                u16_high_splitting[0],
                u16_high_splitting[1],
            ],
        }
    }

    pub fn parse_reg<CS: Circuit<F>>(cs: &mut CS, reg: Register<F>) -> Self {
        let chunks: [Num<F>; 4] =
            std::array::from_fn(|_: usize| cs.add_variable_with_range_check(8));

        let outputs = chunks.map(|x| x.get_variable());
        let register_limbs = [reg.0[0].get_variable(), reg.0[1].get_variable()];
        //setting values for overflow flags
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let low_limb = placer.get_u16(register_limbs[0]);
            let high_limb = placer.get_u16(register_limbs[1]);

            let byte0 = low_limb.truncate();
            let byte1 = low_limb.shr(8).truncate();

            let byte2 = high_limb.truncate();
            let byte3 = high_limb.shr(8).truncate();

            placer.assign_u8(outputs[0], &byte0);
            placer.assign_u8(outputs[1], &byte1);
            placer.assign_u8(outputs[2], &byte2);
            placer.assign_u8(outputs[3], &byte3);
        };

        cs.set_values(value_fn);

        cs.add_constraint_allow_explicit_linear(
            Term::from(chunks[1]) * Term::from(1 << 8) + Term::from(chunks[0])
                - Term::from(reg.0[0]),
        );
        cs.add_constraint_allow_explicit_linear(
            Term::from(chunks[3]) * Term::from(1 << 8) + Term::from(chunks[2])
                - Term::from(reg.0[1]),
        );

        RegisterDecomposition {
            u16_limbs: [reg.0[0], reg.0[1]],
            u8_decomposition: chunks,
        }
    }
}

// To be used only for operands coming from decoder
#[derive(Clone, Debug, Copy)]
pub struct RegisterWithSign<F: PrimeField> {
    pub u16_limbs: [Num<F>; 2],
    pub sign_bit: Boolean,
}

impl<F: PrimeField> RegisterWithSign<F> {
    pub fn uninitialized() -> Self {
        Self {
            u16_limbs: [Num::Constant(F::ZERO); 2],
            sign_bit: Boolean::Constant(false),
        }
    }

    pub fn into_register(self) -> Register<F> {
        Register(self.u16_limbs)
    }
}

// To be used only for operands coming from decoder
#[derive(Clone, Debug)]
pub struct RegisterDecompositionWithSign<F: PrimeField> {
    pub u16_limbs: [Num<F>; 2],
    pub low_word_unconstrained_decomposition: (Variable, Constraint<F>),
    pub high_word_decomposition: (Constraint<F>, Variable),
    pub sign_bit: Boolean,
}

impl<F: PrimeField> RegisterDecompositionWithSign<F> {
    pub fn parse_reg<CS: Circuit<F>>(cs: &mut CS, reg: Register<F>) -> Self {
        let byte_0 = cs.add_variable();
        let low_word = reg.0[0].get_variable();
        //setting values for overflow flags
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let low_limb = placer.get_u16(low_word);

            let byte0_val = low_limb.truncate();

            placer.assign_u8(byte_0, &byte0_val);
        };
        cs.set_values(value_fn);

        let mut byte_1 = Term::from(reg.0[0]) - Term::from(byte_0);
        byte_1.scale(F::from_u64_unchecked(1 << 8).inverse().unwrap());

        // for high we get high byte and sign as one lookup, and low - as constraint
        let [sign, byte_3] = cs.get_variables_from_lookup_constrained(
            &[LookupInput::from(reg.0[1].get_variable())],
            TableType::U16GetSignAndHighByte,
        );
        let sign = Boolean::Is(sign);
        let byte_2 = Constraint::from(reg.0[1]) - (Term::from(byte_3) * Term::from(1 << 8));

        Self {
            u16_limbs: reg.0,
            low_word_unconstrained_decomposition: (byte_0, byte_1),
            high_word_decomposition: (byte_2, byte_3),
            sign_bit: sign,
        }
    }

    pub fn into_register(self) -> Register<F> {
        Register(self.u16_limbs)
    }

    pub fn get_value_unsigned<C: Circuit<F>>(self, cs: &C) -> Option<u32> {
        let low = cs
            .get_value(self.u16_limbs[0].get_variable())?
            .as_u64_reduced();
        let high = cs
            .get_value(self.u16_limbs[1].get_variable())?
            .as_u64_reduced();

        debug_assert!(low <= u16::MAX as u64);
        debug_assert!(high <= u16::MAX as u64);

        Some(low as u32 | (high as u32) << 16)
    }

    pub fn get_value_signed<C: Circuit<F>>(self, cs: &C) -> Option<i32> {
        let unsigned = self.clone().get_value_unsigned(cs)?;
        let sign = cs
            .get_value(self.sign_bit.get_variable().unwrap())?
            .as_boolean();
        let signed = unsigned as i32;
        if sign {
            assert!(
                signed < 0,
                "sign is claimed negative, while value = 0b{:032b}",
                unsigned
            );
        }
        Some(signed)
    }

    pub fn into_register_with_sign(self) -> RegisterWithSign<F> {
        RegisterWithSign {
            u16_limbs: self.u16_limbs,
            sign_bit: self.sign_bit,
        }
    }
}
