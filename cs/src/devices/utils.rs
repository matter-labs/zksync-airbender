use crate::constraint::*;
use crate::cs::circuit::Circuit;
#[cfg(feature = "picus")]
use crate::cs::circuit::{PicusExpr, PicusStructuredConstraint};
use crate::types::*;
use field::PrimeField;

#[cfg(feature = "picus")]
#[inline(always)]
fn picus_from_num<F: PrimeField>(num: Num<F>) -> PicusExpr<F> {
    match num {
        Num::Constant(c) => PicusExpr::Constant(c),
        Num::Var(v) => PicusExpr::Variable(v),
    }
}

pub(crate) fn enforce_add_sub_relation<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    carry_out: Boolean,
    a_s: &[Register<F>],
    b_s: &[Register<F>],
    c_s: &[Register<F>],
    flags: &[Boolean],
) {
    assert_eq!(a_s.len(), b_s.len());
    assert_eq!(a_s.len(), c_s.len());
    assert_eq!(a_s.len(), flags.len());

    let mut constraint_low = Constraint::empty();
    let mut constraint_high = Constraint::empty();
    #[cfg(feature = "picus")]
    let mut parallel_low = PicusExpr::Constant(F::ZERO);
    #[cfg(feature = "picus")]
    let mut parallel_high = PicusExpr::Constant(F::ZERO);

    let mut dependencies = vec![];

    for (((a, b), c), flag) in a_s.iter().zip(b_s.iter()).zip(c_s.iter()).zip(flags.iter()) {
        let Boolean::Is(flag) = *flag else { todo!() };
        #[cfg(feature = "picus")]
        println!("FLAG: {flag:?}");
        let a_low = a.0[0];
        let a_high = a.0[1];
        let b_low = b.0[0];
        let b_high = b.0[1];
        let c_low = c.0[0];
        let c_high = c.0[1];

        #[cfg(feature = "picus")]
        let flag_expr = picus_from_num(Num::Var(flag));
        constraint_low = constraint_low + (Term::from(flag) * Term::from(a_low));
        #[cfg(feature = "picus")]
        {
            parallel_low = parallel_low + flag_expr.clone() * picus_from_num(a_low);
        }
        constraint_low = constraint_low + (Term::from(flag) * Term::from(b_low));
        #[cfg(feature = "picus")]
        {
            parallel_low = parallel_low + flag_expr.clone() * picus_from_num(b_low);
        }
        constraint_low = constraint_low - (Term::from(flag) * Term::from(c_low));
        #[cfg(feature = "picus")]
        {
            parallel_low = parallel_low - flag_expr.clone() * picus_from_num(c_low);
        }

        constraint_high = constraint_high + (Term::from(flag) * Term::from(a_high));
        #[cfg(feature = "picus")]
        {
            parallel_high = parallel_high + flag_expr.clone() * picus_from_num(a_high);
        }
        constraint_high = constraint_high + (Term::from(flag) * Term::from(b_high));
        #[cfg(feature = "picus")]
        {
            parallel_high = parallel_high + flag_expr.clone() * picus_from_num(b_high);
        }
        constraint_high = constraint_high - (Term::from(flag) * Term::from(c_high));
        #[cfg(feature = "picus")]
        {
            parallel_high = parallel_high - flag_expr * picus_from_num(c_high);
        }

        dependencies.push((flag, a_low, b_low, c_low)); // we only need that for carry low
    }

    let carry_intermediate = Boolean::new(cs);
    let carry_intermediate_var = carry_intermediate.get_variable().unwrap();

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        use crate::cs::witness_placer::*;

        let mut carry = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);

        for (flag, a, b, c) in dependencies.iter() {
            let mask = placer.get_boolean(*flag);
            let mut result = match a {
                Num::Constant(a) => <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(
                    a.as_u64_reduced() as u32,
                ),
                Num::Var(a) => placer.get_u16(*a).widen(),
            };
            let b = match b {
                Num::Constant(b) => <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(
                    b.as_u64_reduced() as u32,
                ),
                Num::Var(b) => placer.get_u16(*b).widen(),
            };
            let c = match c {
                Num::Constant(c) => <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(
                    c.as_u64_reduced() as u32,
                ),
                Num::Var(c) => placer.get_u16(*c).widen(),
            };
            result.add_assign(&b);
            result.sub_assign(&c);
            let carry_candidate = result.get_bit(16);
            carry.assign_masked(&mask, &carry_candidate);
        }

        placer.assign_mask(carry_intermediate_var, &carry);
    };
    cs.set_values(value_fn);

    let constraint_low = constraint_low
        - Term::<F>::from((
            F::from_u64_unchecked(1 << 16),
            carry_intermediate.get_variable().unwrap(),
        ));
    #[cfg(feature = "picus")]
    let parallel_low = parallel_low
        - PicusExpr::Constant(F::from_u64_unchecked(1 << 16))
            * PicusExpr::Variable(carry_intermediate.get_variable().unwrap());
    cs.add_constraint(constraint_low);
    #[cfg(feature = "picus")]
    cs.add_picus_parallel_constraint(PicusStructuredConstraint::Eq {
        lhs: parallel_low,
        rhs: PicusExpr::Constant(F::ZERO),
    });

    let constraint_high = constraint_high
        + Term::<F>::from(carry_intermediate.get_variable().unwrap())
        - Term::<F>::from((
            F::from_u64_unchecked(1 << 16),
            carry_out.get_variable().unwrap(),
        ));
    #[cfg(feature = "picus")]
    let parallel_high = parallel_high
        + PicusExpr::Variable(carry_intermediate.get_variable().unwrap())
        - PicusExpr::Constant(F::from_u64_unchecked(1 << 16))
            * PicusExpr::Variable(carry_out.get_variable().unwrap());
    cs.add_constraint(constraint_high);
    #[cfg(feature = "picus")]
    cs.add_picus_parallel_constraint(PicusStructuredConstraint::Eq {
        lhs: parallel_high,
        rhs: PicusExpr::Constant(F::ZERO),
    });
}
