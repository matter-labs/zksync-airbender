use crate::constraint::*;
use crate::cs::circuit::Circuit;
use crate::types::*;
use field::PrimeField;

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

    let mut dependencies = vec![];

    for (((a, b), c), flag) in a_s.iter().zip(b_s.iter()).zip(c_s.iter()).zip(flags.iter()) {
        let Boolean::Is(flag) = *flag else { todo!() };
        let Num::Var(a_low) = a.0[0] else { todo!() };
        let Num::Var(a_high) = a.0[1] else { todo!() };
        let Num::Var(b_low) = b.0[0] else { todo!() };
        let Num::Var(b_high) = b.0[1] else { todo!() };
        let Num::Var(c_low) = c.0[0] else { todo!() };
        let Num::Var(c_high) = c.0[1] else { todo!() };
        constraint_low = constraint_low + (Term::from(flag) * Term::from(a_low));
        constraint_low = constraint_low + (Term::from(flag) * Term::from(b_low));
        constraint_low = constraint_low - (Term::from(flag) * Term::from(c_low));

        constraint_high = constraint_high + (Term::from(flag) * Term::from(a_high));
        constraint_high = constraint_high + (Term::from(flag) * Term::from(b_high));
        constraint_high = constraint_high - (Term::from(flag) * Term::from(c_high));

        dependencies.push((flag, a_low, b_low, c_low)); // we only need that for carry low
    }

    let carry_intermediate = Boolean::new(cs);
    let carry_intermediate_var = carry_intermediate.get_variable().unwrap();

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        use crate::cs::witness_placer::*;

        let mut carry = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);

        for (flag, a, b, c) in dependencies.iter() {
            let mask = placer.get_boolean(*flag);
            let mut result = placer.get_u16(*a).widen();
            let b = placer.get_u16(*b).widen();
            let c = placer.get_u16(*c).widen();
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
    cs.add_constraint(constraint_low);

    let constraint_high = constraint_high
        + Term::<F>::from(carry_intermediate.get_variable().unwrap())
        - Term::<F>::from((
            F::from_u64_unchecked(1 << 16),
            carry_out.get_variable().unwrap(),
        ));
    cs.add_constraint(constraint_high);
}
