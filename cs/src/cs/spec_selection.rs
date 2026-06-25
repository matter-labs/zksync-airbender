use std::collections::BTreeSet;

#[cfg(not(feature = "picus"))]
use super::circuit::Circuit;
#[cfg(feature = "picus")]
use super::circuit::{
    picus_expr_from_boolean_circuit, picus_expr_from_constraint, picus_expr_from_num_circuit,
    Circuit, PicusExpr, PicusStructuredConstraint,
};
use crate::constraint::*;
use crate::cs::utils::mask_by_boolean_into_accumulator_constraint;
use crate::cs::utils::mask_linear_term_by_boolean_into_accumulator_constraint;
use crate::cs::witness_placer::WitnessComputationalField;
use crate::cs::witness_placer::WitnessPlacer;
use crate::cs::witness_placer::WitnessTypeSet;
use crate::one_row_compiler::Variable;
use crate::types::*;
use ::field::PrimeField;

#[track_caller]
pub(crate) fn spec_choose_from_orthogonal_variants<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    flags: &[Boolean],
    variants: &[Num<F>],
) -> Num<F> {
    assert_eq!(flags.len(), variants.len());

    if flags.iter().all(|el| matches!(el, Boolean::Is(..))) {
        return spec_choose_from_orthogonal_variants_no_nots(cs, flags, variants);
    }

    // we enumerate all booleans to properly resolve
    let mut boolean_vars = BTreeSet::new();
    for flag in flags.iter() {
        match flag {
            Boolean::Is(var) => {
                boolean_vars.insert(*var);
            }
            Boolean::Not(var) => {
                boolean_vars.insert(*var);
            }
            Boolean::Constant(..) => {
                panic!("constant flags do not make sense for selection functions")
            }
        }
    }

    // now we can make a constraint
    let mut constraint = Constraint::<F>::empty();
    #[cfg(feature = "picus")]
    let mut parallel_constraint = PicusExpr::Constant(F::ZERO);
    for (flag, variant) in flags.iter().zip(variants.iter()) {
        constraint = mask_by_boolean_into_accumulator_constraint(flag, variant, constraint);
        #[cfg(feature = "picus")]
        {
            parallel_constraint = parallel_constraint
                + picus_expr_from_boolean_circuit(*flag) * picus_expr_from_num_circuit(*variant);
        }
    }

    spec_choose_from_orthogonal_variants_for_constraint_inner(
        cs,
        boolean_vars,
        constraint,
        #[cfg(feature = "picus")]
        parallel_constraint,
    )
}

#[track_caller]
pub(crate) fn spec_choose_from_orthogonal_variants_for_linear_terms<
    F: PrimeField,
    CS: Circuit<F>,
>(
    cs: &mut CS,
    flags: &[Boolean],
    variants: &[Constraint<F>],
) -> Num<F> {
    assert_eq!(flags.len(), variants.len());

    // we enumerate all booleans to properly resolve
    let mut boolean_vars = BTreeSet::new();
    for flag in flags.iter() {
        match flag {
            Boolean::Is(var) => {
                boolean_vars.insert(*var);
            }
            Boolean::Not(var) => {
                boolean_vars.insert(*var);
            }
            Boolean::Constant(..) => {
                panic!("constant flags do not make sense for selection functions")
            }
        }
    }

    // now we can make a constraint
    let mut constraint = Constraint::<F>::empty();
    #[cfg(feature = "picus")]
    let mut parallel_constraint = PicusExpr::Constant(F::ZERO);
    for (flag, variant) in flags.iter().zip(variants.iter()) {
        constraint =
            mask_linear_term_by_boolean_into_accumulator_constraint(flag, variant, constraint);
        #[cfg(feature = "picus")]
        {
            parallel_constraint = parallel_constraint
                + picus_expr_from_boolean_circuit(*flag) * picus_expr_from_constraint(variant);
        }
    }

    spec_choose_from_orthogonal_variants_for_constraint_inner(
        cs,
        boolean_vars,
        constraint,
        #[cfg(feature = "picus")]
        parallel_constraint,
    )
}

fn spec_choose_from_orthogonal_variants_for_constraint_inner<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    booleans: BTreeSet<Variable>,
    mut constraint: Constraint<F>,
    #[cfg(feature = "picus")] mut parallel_constraint: PicusExpr<F>,
) -> Num<F> {
    let (quadratic, linear, constant_term) = constraint.clone().split_max_quadratic();

    let mut parsed_quadratic = vec![];
    let mut parsed_linear = vec![];
    for (c, a, b) in quadratic.into_iter() {
        if booleans.contains(&a) {
            assert!(booleans.contains(&b) == false);
            parsed_quadratic.push((a, (c, b)));
        } else {
            assert!(booleans.contains(&b));
            parsed_quadratic.push((b, (c, a)));
        }
    }
    for (c, a) in linear.into_iter() {
        assert!(booleans.contains(&a));
        parsed_linear.push((a, c));
    }

    let result = cs.add_variable();
    constraint -= Term::from(result);
    #[cfg(feature = "picus")]
    {
        parallel_constraint = parallel_constraint - PicusExpr::Variable(result);
    }

    // Filter constants equal to 1
    let mut quadratic_trivial = vec![];
    let mut quadratic_nontrivial = vec![];
    for (flag, (c, a)) in parsed_quadratic.into_iter() {
        assert!(c != F::ZERO);
        if c == F::ONE {
            quadratic_trivial.push((flag, a));
        } else {
            quadratic_nontrivial.push((flag, (c, a)));
        }
    }

    let mut linear_trivial = vec![];
    let mut linear_nontrivial = vec![];
    for (flag, c) in parsed_linear.into_iter() {
        assert!(c != F::ZERO);
        if c == F::ONE {
            linear_trivial.push(flag);
        } else {
            linear_nontrivial.push((flag, c));
        }
    }

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        use crate::cs::witness_placer::WitnessMask;

        let mut value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(constant_term);

        for (mask, term) in quadratic_trivial.iter() {
            let mask = placer.get_boolean(*mask);
            let term = placer.get_field(*term);
            value.add_assign_masked(&mask, &term);
        }

        for (mask, (constant, term)) in quadratic_nontrivial.iter() {
            let mask = placer.get_boolean(*mask);
            let constant = <CS::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(*constant);
            let term = placer.get_field(*term);
            value.add_assign_product_masked(&mask, &constant, &term);
        }

        if linear_trivial.len() > 0 {
            let mut mask_for_one_constant =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
            for mask in linear_trivial.iter() {
                let mask = placer.get_boolean(*mask);
                mask_for_one_constant = mask_for_one_constant.or(&mask);
            }
            let one = <CS::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(F::ONE);
            value.add_assign_masked(&mask_for_one_constant, &one);
        }

        for (mask, constant) in linear_nontrivial.iter() {
            let mask = placer.get_boolean(*mask);
            let constant = <CS::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(*constant);
            value.add_assign_masked(&mask, &constant);
        }

        placer.assign_field(result, &value);
    };

    cs.set_values(value_fn);

    assert!(constraint.degree() > 0);
    if constraint.degree() == 2 {
        cs.add_constraint(constraint);
    } else {
        cs.add_constraint_allow_explicit_linear(constraint);
    }
    #[cfg(feature = "picus")]
    cs.add_picus_parallel_constraint(PicusStructuredConstraint::Eq {
        lhs: parallel_constraint,
        rhs: PicusExpr::Constant(F::ZERO),
    });

    Num::Var(result)
}

#[track_caller]
fn spec_choose_from_orthogonal_variants_no_nots<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    flags: &[Boolean],
    variants: &[Num<F>],
) -> Num<F> {
    assert_eq!(flags.len(), variants.len());

    let mut boolean_vars = BTreeSet::new();

    let mut parsed_quadratic = vec![];
    let mut parsed_linear = vec![];

    // now we can make a constraint
    let mut constraint = Constraint::empty();
    #[cfg(feature = "picus")]
    let mut parallel_constraint = PicusExpr::Constant(F::ZERO);
    for (flag, variant) in flags.iter().zip(variants.iter()) {
        let Boolean::Is(flag) = *flag else {
            unreachable!()
        };

        let is_unique = boolean_vars.insert(flag);
        assert!(is_unique, "use of the same flag in orthogonal combination");

        match variant {
            Num::Var(variant) => {
                constraint = constraint + Term::from(flag) * Term::from(*variant);
                parsed_quadratic.push((flag, *variant));
                #[cfg(feature = "picus")]
                {
                    parallel_constraint = parallel_constraint
                        + picus_expr_from_boolean_circuit(Boolean::Is(flag))
                            * PicusExpr::Variable(*variant);
                }
            }
            Num::Constant(constant) => {
                constraint += Term::from((*constant, flag));
                parsed_linear.push((flag, *constant));
                #[cfg(feature = "picus")]
                {
                    parallel_constraint = parallel_constraint
                        + picus_expr_from_boolean_circuit(Boolean::Is(flag))
                            * PicusExpr::Constant(*constant);
                }
            }
        }
    }

    let result = cs.add_variable();
    constraint -= Term::from(result);
    #[cfg(feature = "picus")]
    {
        parallel_constraint = parallel_constraint - PicusExpr::Variable(result);
    }

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let mut value = <CS::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(F::ZERO);

        for (mask, term) in parsed_quadratic.iter() {
            let mask = placer.get_boolean(*mask);
            let term = placer.get_field(*term);
            value.add_assign_masked(&mask, &term);
        }

        for (mask, constant) in parsed_linear.iter() {
            let mask = placer.get_boolean(*mask);
            let constant = <CS::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(*constant);
            value.add_assign_masked(&mask, &constant);
        }

        placer.assign_field(result, &value);
    };

    cs.set_values(value_fn);

    assert!(constraint.degree() > 0);
    if constraint.degree() == 2 {
        cs.add_constraint(constraint);
    } else {
        cs.add_constraint_allow_explicit_linear(constraint);
    }
    #[cfg(feature = "picus")]
    cs.add_picus_parallel_constraint(PicusStructuredConstraint::Eq {
        lhs: parallel_constraint,
        rhs: PicusExpr::Constant(F::ZERO),
    });

    Num::Var(result)
}

// #[track_caller]
// fn spec_choose_from_orthogonal_variants_no_nots_value_fn<F: PrimeField>(
//     num_quadtratic_terms: usize,
//     num_linear_terms: usize,
// ) -> fn(WitnessGenSource<'_, F>, WitnessGenDest<'_, F>, &[F], &TableDriver<F>, TableType) {
//     // TODO: use fixed combinations

//     // Below we use only limited list to avoid too much monomorphization burden. If necessary it should be extended

//     super_seq_macro::seq!(N in [0, 1, 2, 3, 4] {
//         if num_quadtratic_terms == N {
//             super_seq_macro::seq!(M in [0, 1, 2, 3, 4, 5, 6] {
//                 if num_linear_terms == M {
//                     // return false_fn_~N::collapse_max_quadratic_constraint_into_fixed_witness_eval_fn_~M::<F, false, N, M>;
//                     return choose_from_orthogonal_variants_no_nots_value_fn::<F, N, M>;
//                 }
//             });

//             panic!("unsupported number of linear terms: {} for {} quadratic terms", num_linear_terms, num_quadtratic_terms);
//         }
//     });

//     panic!(
//         "unsupported number of quadratic terms: {}",
//         num_quadtratic_terms
//     );
// }

// #[track_caller]
// #[inline(always)]
// fn choose_from_orthogonal_variants_no_nots_value_fn<
//     F: PrimeField,
//     const NUM_QUADRATIC: usize,
//     const NUM_LINEAR: usize,
// >(
//     input: WitnessGenSource<'_, F>,
//     mut output: WitnessGenDest<'_, F>,
//     constants: &[F],
//     _table_driver: &TableDriver<F>,
//     _table_type: TableType,
// ) {
//     unsafe {
//         for j in 0..NUM_QUADRATIC {
//             let a = input[2 * j].as_boolean();
//             if a {
//                 output[0] = input[2 * j + 1];
//                 return;
//             }
//         }
//         for j in 0..NUM_LINEAR {
//             let a = input[NUM_QUADRATIC * 2 + j].as_boolean();
//             if a {
//                 output[0] = *constants.get_unchecked(j);
//                 return;
//             }
//         }
//         output[0] = F::ZERO;
//     }
// }

// #[track_caller]
// fn spec_choose_from_orthogonal_variants_for_constraint_value_fn<F: PrimeField>(
//     num_quadtratic_terms: usize,
//     num_linear_terms: usize,
// ) -> fn(WitnessGenSource<'_, F>, WitnessGenDest<'_, F>, &[F], &TableDriver<F>, TableType) {
//     seq_macro::seq!(N in 0..32 {
//         if num_quadtratic_terms == N {
//             super_seq_macro::seq!(M in 0..32-N {
//                 if num_linear_terms == M {
//                     // return false_fn_~N::collapse_max_quadratic_constraint_into_fixed_witness_eval_fn_~M::<F, false, N, M>;
//                     return choose_from_orthogonal_variants_for_constraint_value_fn::<F, N, M>;
//                 }
//             });

//             panic!("unsupported number of linear terms: {} for {} quadratic terms", num_linear_terms, num_quadtratic_terms);
//         }
//     });

//     panic!(
//         "unsupported number of quadratic terms: {}",
//         num_quadtratic_terms
//     );
// }

// #[track_caller]
// #[inline(always)]
// fn choose_from_orthogonal_variants_for_constraint_value_fn<
//     F: PrimeField,
//     const NUM_QUADRATIC: usize,
//     const NUM_LINEAR: usize,
// >(
//     input: WitnessGenSource<'_, F>,
//     mut output: WitnessGenDest<'_, F>,
//     constants: &[F],
//     _table_driver: &TableDriver<F>,
//     _table_type: TableType,
// ) {
//     // the problem here is that even though we use booleans, there are no guarantees on uniqueness
//     // of products, so we have to accumulate. We also expect constants in front of quadratic terms
//     unsafe {
//         let mut result = *constants.get_unchecked(0);
//         for j in 0..NUM_QUADRATIC {
//             let a = input[2 * j].as_boolean();
//             if a {
//                 // there are quite a few cases of trivial constants, so faster to branch
//                 if constants.get_unchecked(1 + j).is_one() {
//                     result.add_assign(&input[2 * j + 1]);
//                 } else {
//                     result.add_assign_product(&input[2 * j + 1], constants.get_unchecked(1 + j));
//                 }
//             }
//         }
//         for j in 0..NUM_LINEAR {
//             let a = input[NUM_QUADRATIC * 2 + j].as_boolean();
//             if a {
//                 result.add_assign(constants.get_unchecked(1 + NUM_QUADRATIC + j));
//             }
//         }

//         output[0] = result;
//     }
// }

// seq_macro::seq!(N in 0..32 {
//     mod false_fn_~N {
//         use super::*;

//         seq_macro::seq!(M in 0..32 {
//             #[inline(always)]
//             pub(crate) fn collapse_max_quadratic_constraint_into_fixed_witness_eval_fn_~M<
//                 F: PrimeField,
//                 const HAS_CONSTANT_TERM: bool,
//                 const NUM_QUADRATIC: usize,
//                 const NUM_LINEAR: usize
//             >(
//                 input: WitnessGenSource<'_, F>,
//                 output: WitnessGenDest<'_, F>,
//                 constants: &[F],
//                 table_driver: &TableDriver<F>,
//                 table_type: TableType
//             ) {

//                 collapse_max_quadratic_constraint_into_fixed_witness_eval_fn::<F, false, N, M>(input, output, constants, table_driver, table_type)
//             }
//         });
//     }
// });

// seq_macro::seq!(N in 0..32 {
//     mod true_fn_~N {
//         use super::*;

//         seq_macro::seq!(M in 0..32 {
//             #[inline(always)]
//             pub(crate) fn collapse_max_quadratic_constraint_into_fixed_witness_eval_fn_~M<
//                 F: PrimeField,
//                 const HAS_CONSTANT_TERM: bool,
//                 const NUM_QUADRATIC: usize,
//                 const NUM_LINEAR: usize
//             >(
//                 input: WitnessGenSource<'_, F>,
//                 output: WitnessGenDest<'_, F>,
//                 constants: &[F],
//                 table_driver: &TableDriver<F>,
//                 table_type: TableType
//             ) {
//                 collapse_max_quadratic_constraint_into_fixed_witness_eval_fn::<F, true, N, M>(input, output, constants, table_driver, table_type)
//             }
//         });
//     }
// });
