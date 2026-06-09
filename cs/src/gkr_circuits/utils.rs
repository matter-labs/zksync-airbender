use super::*;
use crate::cs::circuit_trait::Circuit;
use crate::cs::circuit_trait::Invariant;
use crate::structured_expr::Expr;
use crate::types::LIMB_WIDTH;
use crate::witness_placer::*;
use field::PrimeField;

pub fn calculate_pc_next_no_overflows_with_range_checks<F: PrimeField, CS: Circuit<F>>(
    circuit: &mut CS,
    pc: [Variable; REGISTER_SIZE],
    pc_next: [Variable; REGISTER_SIZE],
) {
    // Input invariant: PC % 4 == 0, preserved as:
    // - initial PC is valid % 4
    // - jumps and branches check for alignments

    let [pc_next_low, pc_next_high] = pc_next;

    // range check of both output limbs ensures that there is no overflow/wrap around
    circuit.require_invariant(
        pc_next_low,
        Invariant::RangeChecked {
            width: LIMB_WIDTH as u32,
        },
    );
    circuit.require_invariant(
        pc_next_high,
        Invariant::RangeChecked {
            width: LIMB_WIDTH as u32,
        },
    );

    let carry = (Expr::<F>::var(pc[0]) + Expr::from(common_constants::PC_STEP as u32)
        - Expr::var(pc_next_low))
        * F::from_u32_unchecked(1 << 16).inverse().unwrap();

    // ensure boolean
    circuit.add_constraint_expr(carry.clone() * (carry.clone() - Expr::one()));

    let pc_high = carry + Expr::var(pc[1]) - Expr::var(pc_next_high);

    // NOTE: we should try to set values before setting constraint as much as possible
    // setting values for overflow flags

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let pc_inc_step = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(
            common_constants::PC_STEP as u32,
        );
        let pc = placer.get_u32_from_u16_parts(pc);
        let (pc_next_value, _of) = pc.overflowing_add(&pc_inc_step);
        placer.assign_u32_from_u16_parts(pc_next, &pc_next_value);
    };
    circuit.set_values(value_fn);

    circuit.add_constraint_allow_explicit_linear_prevent_optimizations_expr(pc_high);
}

pub(crate) fn montgomery_product<F: PrimeField, W: WitnessTypeSet<F>>(
    a: &W::Field,
    b: &W::Field,
) -> W::Field {
    let mut product = a.clone();
    product.mul_assign(b);
    product.mul_assign(&W::Field::constant(F::from_reduced_raw_repr(1)));
    product
}

pub(crate) fn montgomery_product_expr<F: PrimeField>(a: Expr<F>, b: Expr<F>) -> Expr<F> {
    a * b * Expr::<F>::constant(F::from_reduced_raw_repr(1))
}

pub(crate) fn update_intermediate_carry_value<
    F: PrimeField,
    W: WitnessPlacer<F>,
    const IS_SUB: bool,
>(
    intermediate_carry: &mut <W as WitnessTypeSet<F>>::Mask,
    flag: &<W as WitnessTypeSet<F>>::Mask,
    a: &<W as WitnessTypeSet<F>>::U16,
    b: &<W as WitnessTypeSet<F>>::U16,
    imm_for_b: Option<&<W as WitnessTypeSet<F>>::U16>,
) {
    if IS_SUB {
        let (tmp, of0) = a.overflowing_sub(b);
        if let Some(imm_for_b) = imm_for_b {
            let (_, of1) = tmp.overflowing_sub(imm_for_b);
            let of = of0.or(&of1);
            *intermediate_carry =
                <W as WitnessTypeSet<F>>::Mask::select(flag, &of, &*intermediate_carry);
        } else {
            *intermediate_carry =
                <W as WitnessTypeSet<F>>::Mask::select(flag, &of0, &*intermediate_carry);
        }
    } else {
        let (tmp, of0) = a.overflowing_add(b);
        if let Some(imm_for_b) = imm_for_b {
            let (_, of1) = tmp.overflowing_add(imm_for_b);
            let of = of0.or(&of1);
            *intermediate_carry =
                <W as WitnessTypeSet<F>>::Mask::select(flag, &of, &*intermediate_carry);
        } else {
            *intermediate_carry =
                <W as WitnessTypeSet<F>>::Mask::select(flag, &of0, &*intermediate_carry);
        }
    }
}
