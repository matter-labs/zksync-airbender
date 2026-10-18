use super::circuit::{
    dispatch_sum, non_f2_dispatch_sum, pc_bump_gate,
    unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr_core,
    unified_register_all_tables, UnifiedCircuitProfile, UNIFIED_REDUCED_MACHINE_NUM_FLAGS,
};
use super::decoder::row_classes::unified_row_classes;
use super::decoder::{
    unified_decoder_mask_violation, UnifiedReducedMachineFamilyCircuitMask, UNIFIED_RD_IS_ZERO_BIT,
};
use super::jump_branch_slt::f2_rd_write_gates;
use crate::constraint::{Constraint, Term};
use crate::cs::circuit_impl::BasicAssembly;
use crate::cs::circuit_output::CircuitOutput;
use crate::cs::circuit_trait::*;
use crate::definitions::Variable;
use crate::structured_expr::{Expr, StructuredStatement};
use crate::types::Boolean;
use field::baby_bear::base::BabyBearField;
use field::{Field, PrimeField, Proth120};
use std::collections::{BTreeSet, HashMap};

const BASELINE_HELPERS: [&str; 5] = [
    "is_jal_or_jalr_writes_rd",
    "is_slt_writes_rd",
    "gate_fam2_rd_zero",
    "unified pc-bump gate",
    "unified family-dispatch one-hot",
];

/// The `Baseline` constraint system with its execute and flag variables.
struct BaselineSystem<F: PrimeField> {
    output: CircuitOutput<F>,
    execute: Variable,
    bits: [Variable; UNIFIED_REDUCED_MACHINE_NUM_FLAGS],
}

impl<F: PrimeField> BaselineSystem<F> {
    fn build<MopF: PrimeField>() -> Self {
        let mut cs = BasicAssembly::<F>::new();
        unified_register_all_tables(&mut cs);
        unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr_core::<F, MopF, _>(
            &mut cs,
            UnifiedCircuitProfile::Baseline,
        );
        let (output, _) = cs.finalize();
        let execute = output.executor_machine_state.as_ref().unwrap().execute;
        let bits = output.circuit_family_bitmask.clone().try_into().unwrap();
        Self {
            output,
            execute,
            bits,
        }
    }

    fn named(&self, name: &str) -> Variable {
        let matches: Vec<_> = self
            .output
            .variable_names
            .iter()
            .filter(|(_, n)| n.as_str() == name)
            .map(|(v, _)| *v)
            .collect();
        assert_eq!(matches.len(), 1, "variable {name}");
        matches[0]
    }

    /// The unique asserted constraint that defines `helper`: the helper appears in a
    /// degree-1 term with a nonzero coefficient, and every other term contains only
    /// execute and flag variables.
    fn definition_of(&self, helper: Variable) -> Constraint<F> {
        let inputs: BTreeSet<Variable> = self.bits.iter().copied().chain([self.execute]).collect();
        let candidates: Vec<_> = self
            .output
            .structured_statements
            .iter()
            .filter_map(|s| match s {
                StructuredStatement::AssertZero {
                    compiled_constraint,
                    ..
                } => Some(compiled_constraint),
                _ => None,
            })
            .filter(|c| {
                let mut linear_helper = false;
                for term in c.terms.iter() {
                    let Term::Expression {
                        coeff,
                        inner,
                        degree,
                    } = term
                    else {
                        continue;
                    };
                    let vars = &inner[..*degree];
                    if vars.contains(&helper) {
                        if *degree != 1 || coeff.is_zero() {
                            return false;
                        }
                        linear_helper = true;
                    } else if !vars.iter().all(|v| inputs.contains(v)) {
                        return false;
                    }
                }
                linear_helper
            })
            .collect();
        assert_eq!(candidates.len(), 1, "definition of {helper:?}");
        candidates[0].clone()
    }

    fn assignment(&self, execute: bool, mask: u32) -> HashMap<Variable, F> {
        let mut values: HashMap<_, _> = self
            .bits
            .iter()
            .enumerate()
            .map(|(i, v)| (*v, bool_to_field(mask >> i & 1 == 1)))
            .collect();
        values.insert(self.execute, bool_to_field(execute));
        values
    }

    fn mask(&self) -> UnifiedReducedMachineFamilyCircuitMask {
        UnifiedReducedMachineFamilyCircuitMask::from_full_mask(self.bits.map(Boolean::Is))
    }
}

/// A `Baseline` helper together with its defining constraint.
struct Helper<F: PrimeField> {
    var: Variable,
    definition: Constraint<F>,
}

impl<F: PrimeField> Helper<F> {
    fn new(system: &BaselineSystem<F>, name: &str) -> Self {
        let var = system.named(name);
        Self {
            var,
            definition: system.definition_of(var),
        }
    }

    /// The helper's value forced by its own definition under `values`.
    fn solve(&self, values: &HashMap<Variable, F>) -> F {
        let helper = self.var;
        let mut helper_coeff = F::ZERO;
        let mut rest = F::ZERO;
        for term in self.definition.terms.iter() {
            match term {
                Term::Constant(c) => {
                    rest.add_assign(c);
                }
                Term::Expression {
                    coeff,
                    inner,
                    degree,
                } if inner[..*degree] == [helper] => {
                    helper_coeff.add_assign(coeff);
                }
                Term::Expression {
                    coeff,
                    inner,
                    degree,
                } => {
                    let mut t = *coeff;
                    for v in &inner[..*degree] {
                        t.mul_assign(&values[v]);
                    }
                    rest.add_assign(&t);
                }
            }
        }
        let mut value = rest;
        value.negate();
        value.mul_assign(&helper_coeff.inverse().unwrap());
        value
    }
}

fn bool_to_field<F: PrimeField>(b: bool) -> F {
    if b {
        F::ONE
    } else {
        F::ZERO
    }
}

fn eval<F: PrimeField>(constraint: &Constraint<F>, values: &HashMap<Variable, F>) -> F {
    let mut result = F::ZERO;
    for term in constraint.terms.iter() {
        match term {
            Term::Constant(c) => {
                result.add_assign(c);
            }
            Term::Expression {
                coeff,
                inner,
                degree,
            } => {
                let mut t = *coeff;
                for v in &inner[..*degree] {
                    t.mul_assign(&values[v]);
                }
                result.add_assign(&t);
            }
        }
    }
    result
}

/// `[jal|jalr writes rd, slt writes rd, rd = x0, PC-bump gate, execute − Σ dispatch]` of the
/// `ColumnCuts` profile, as the circuit builds them.
fn column_cuts_gates<F: PrimeField>(system: &BaselineSystem<F>) -> [Constraint<F>; 5] {
    let mask = system.mask();
    let f2 = mask.jump_branch_slt();
    let [jj, slt, rd_zero] = f2_rd_write_gates(
        f2.perform_jal(),
        f2.perform_jalr(),
        f2.perform_slt(),
        f2.perform_branch(),
        f2.rd_is_zero(),
    );
    [
        jj,
        slt,
        rd_zero,
        pc_bump_gate(system.execute, &mask),
        Expr::var(system.execute) - dispatch_sum(&mask),
    ]
    .map(|e| e.to_max_quadratic_constraint())
}

fn padding_zeroed(execute: bool, mask: u32) -> bool {
    execute || mask == 0
}

fn gates_match_on_row_classes<F: PrimeField, MopF: PrimeField>() {
    let system = BaselineSystem::<F>::build::<MopF>();
    let helpers = BASELINE_HELPERS.map(|n| Helper::new(&system, n));
    let gates = column_cuts_gates(&system);
    let rows = unified_row_classes()
        .into_iter()
        .map(|mask| (true, mask))
        .chain([(false, 0)]);
    for (execute, mask) in rows {
        let values = system.assignment(execute, mask);
        let old = helpers.each_ref().map(|h| h.solve(&values));
        let new = gates.each_ref().map(|g| eval(g, &values));
        assert_eq!(old[..4], new[..4], "execute {execute} mask {mask:#b}");
        assert_eq!(new[4], F::ZERO, "tie on execute {execute} mask {mask:#b}");
        assert_eq!(old[4], bool_to_field(execute), "one-hot on mask {mask:#b}");
    }
}

/// On every decoder row class and on padding, each `ColumnCuts` gate equals the value its
/// `Baseline` helper is forced to by the helper's own definition, and the linear tie holds.
#[test]
fn column_cuts_gates_match_baseline_helpers_on_all_row_classes() {
    gates_match_on_row_classes::<BabyBearField, BabyBearField>();
    gates_match_on_row_classes::<Proth120, BabyBearField>();
}

/// Over all 2^20 Boolean (execute, mask) assignments, in both fields, the PC-bump gate minus
/// `non_f2_dispatch_sum` equals the tie residual `execute − dispatch_sum`: the two gates are
/// interchangeable on every assignment that satisfies the tie.
#[test]
fn pc_bump_gate_differs_from_non_f2_dispatch_sum_by_the_tie_residual() {
    fn check<F: PrimeField, MopF: PrimeField>() {
        let system = BaselineSystem::<F>::build::<MopF>();
        let mask = system.mask();
        let [gate, sum, tie] = [
            pc_bump_gate(system.execute, &mask),
            non_f2_dispatch_sum(&mask),
            Expr::var(system.execute) - dispatch_sum(&mask),
        ]
        .map(|e| e.to_max_quadratic_constraint());
        for execute in [false, true] {
            for mask in 0..1u32 << UNIFIED_REDUCED_MACHINE_NUM_FLAGS {
                let values = system.assignment(execute, mask);
                let mut difference = eval(&gate, &values);
                difference.sub_assign(&eval(&sum, &values));
                assert_eq!(difference, eval(&tie, &values), "{execute} {mask:#b}");
            }
        }
    }
    check::<BabyBearField, BabyBearField>();
    check::<Proth120, BabyBearField>();
}

/// Over all 2^20 Boolean (execute, mask) assignments: the tie with padding zeroing admits a
/// subset of what the `Baseline` one-hot admits, missing exactly the two `execute = 1`
/// assignments with no dispatch bit (neither a decoder row); on that subset the PC-bump
/// gate equals the `Baseline` helper; and the affine F2 gates equal their helpers
/// exactly on the masks the decoder-mask validator accepts.
#[test]
fn dispatch_tie_strengthens_one_hot_exhaustively() {
    let system = BaselineSystem::<BabyBearField>::build::<BabyBearField>();
    let helpers = BASELINE_HELPERS.map(|n| Helper::new(&system, n));
    let gates = column_cuts_gates(&system);
    let classes = unified_row_classes();
    let one = BabyBearField::ONE;
    let mut only_old = Vec::new();
    let mut affine_mismatch = BTreeSet::new();
    for execute in [false, true] {
        for mask in 0..1u32 << UNIFIED_REDUCED_MACHINE_NUM_FLAGS {
            let values = system.assignment(execute, mask);
            let padding = padding_zeroed(execute, mask);
            let one_hot = helpers[4].solve(&values);
            let in_old = padding && (one_hot.is_zero() || one_hot == one);
            let in_new = padding && eval(&gates[4], &values).is_zero();
            assert!(!in_new || in_old, "tie admits {execute} {mask:#b}");
            if in_old && !in_new {
                only_old.push((execute, mask));
            }
            if !in_new {
                continue;
            }
            assert_eq!(
                eval(&gates[3], &values),
                helpers[3].solve(&values),
                "PC-bump gate on {execute} {mask:#b}"
            );
            let affine_ok = (0..3).all(|i| eval(&gates[i], &values) == helpers[i].solve(&values));
            if !affine_ok {
                affine_mismatch.insert(mask);
            }
            if execute {
                assert_eq!(
                    affine_ok,
                    unified_decoder_mask_violation(mask).is_none(),
                    "affine gates on {mask:#b}"
                );
                assert_eq!(
                    classes.contains(&mask),
                    unified_decoder_mask_violation(mask).is_none()
                );
            }
        }
    }
    let rd_is_zero = 1u32 << UNIFIED_RD_IS_ZERO_BIT;
    assert_eq!(only_old, vec![(true, 0), (true, rd_is_zero)]);
    assert!(only_old.iter().all(|(_, m)| !classes.contains(m)));
    println!(
        "masks where the affine F2 gates differ from the Baseline helpers ({}): {:?}",
        affine_mismatch.len(),
        affine_mismatch
            .iter()
            .map(|m| format!("{m:#021b}"))
            .collect::<Vec<_>>()
    );
    assert_eq!(affine_mismatch.len(), 16);
}
