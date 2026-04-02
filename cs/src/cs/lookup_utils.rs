use crate::constraint::Constraint;
use crate::cs::circuit_trait::Circuit;
use crate::types::Boolean;
use crate::witness_placer::*;
use field::PrimeField;

use super::*;

#[track_caller]
pub(crate) fn peek_lookup_values_unconstrained_into_variables<
    F: PrimeField,
    CS: Circuit<F>,
    const M: usize,
    const N: usize,
>(
    cs: &mut CS,
    inputs: &[LookupInput<F>; M],
    outputs: &[Variable; N],
    table: LookupInput<F>,
    exec_flag: Boolean,
) {
    assert!(inputs.len() > 0);

    let output_variables: [Variable; N] = outputs.clone();
    let inputs = inputs.clone();
    let exec_flag = exec_flag.get_variable().unwrap();

    let inner_evaluator = move |placer: &mut CS::WitnessPlacer| {
        let table_id = table.evaluate(placer).as_integer().truncate();
        let mask = placer.get_boolean(exec_flag);
        let input_values: [_; M] = std::array::from_fn(|i| inputs[i].evaluate(placer));
        let output_values = placer.maybe_lookup::<M, N>(&input_values, &table_id, &mask);
        for (var, value) in output_variables.iter().zip(output_values.iter()) {
            placer.conditionally_assign_field(*var, &mask, value);
        }
    };

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let mask = placer.get_boolean(exec_flag);
        witness_early_branch_if_possible(mask.clone(), placer, &inner_evaluator);
    };

    cs.set_values(value_fn);
}

#[track_caller]
pub(crate) fn peek_lookup_values_unconstrained_into_variables_from_constraints<
    F: PrimeField,
    CS: Circuit<F>,
    const M: usize,
    const N: usize,
>(
    cs: &mut CS,
    inputs: &[Constraint<F>; M],
    output_variables: &[Variable; N],
    table_type: Constraint<F>,
) {
    assert!(inputs.len() > 0);

    let inputs = inputs.clone();
    let output_variables = output_variables.clone();

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let inputs = inputs
            .each_ref()
            .map(|con| con.evaluate_with_placer(placer));
        let table_id = table_type
            .evaluate_with_placer(placer)
            .as_integer()
            .truncate();
        let output_values: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field; N] =
            placer.peek_lookup(&inputs, &table_id);
        for (&variable, value) in output_variables.iter().zip(&output_values) {
            placer.assign_field(variable, value);
        }
    };
    cs.set_values(value_fn);
}
