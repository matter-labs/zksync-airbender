//! MUL / MULHU family of the unified extended machine (no division).
//!
//! `rd = low(rs1 * rs2)` for MUL and `high(rs1 * rs2)` for MULHU, enforced as the schoolbook
//! product over bytes (16-bit limb products would not fit the 31-bit BabyBear field). The
//! family commits NO columns of its own beyond its two flags: the operand bytes, the other
//! half of the product and the three 16-bit-chunk carries all live in the shared scratch pool.
//!
//! * rs1's two committed bytes (`byte 0`, `byte 2`; bytes 1 and 3 are the linear complements
//!   `(limb - byte) / 256`) reuse Family 3's rs1 split slots (the RC-16 shared register,
//!   written conditionally on mul rows as u16 like Family 3 does).
//! * rs2's bytes are Family 3's rs2 split slots, which Family 3's witness writes
//!   UNCONDITIONALLY on every row; this family only reads them and proves them with its own
//!   lookups.
//! * each byte pair `(rs1_byte_i, rs2_byte_i)` is pinned by one `RangeCheck8x8` lookup, the
//!   carries (each < 2^10) by two `RangeCheck10x10` lookups; all gated by `is_mul + is_mulhu`
//!   so they fold into the pooled slots.
//! * the product relation is checked one intermediate layer up: every operand is copied there
//!   masked by the family gate, so the four chunk equations read `0 = 0` on other rows while
//!   the pool slots hold other families' values.
use super::*;
use crate::cs::circuit_trait::*;
use crate::gkr_circuits::unified_reduced_machine::circuit::LookupRequest;
use crate::structured_expr::Expr;
use crate::types::*;
use crate::witness_placer::*;
use field::PrimeField;

#[allow(clippy::too_many_arguments)]
pub(super) fn apply_extended_mul_inner<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    is_mul: Boolean,
    is_mulhu: Boolean,
    rs1_limbs: [Variable; REGISTER_SIZE],
    rs2_limbs: [Variable; REGISTER_SIZE],
    rd_write_limbs: [Variable; REGISTER_SIZE],
    // bytes 0 and 2 of rs1: written here on mul rows (shared register slots, RC-16)
    rs1_byte_slots: [Variable; 2],
    // bytes 0 and 2 of rs2: Family 3's unconditional split, read only
    rs2_byte_slots: [Variable; 2],
    // the other half of the 64-bit product (u16 limbs, RC-16 pool-wide)
    other_half_slots: [Variable; 2],
    // chunk carries c0, c1, c2 (each < 2^10, pinned by the gated lookups below)
    carry_slots: [Variable; 3],
) -> Vec<LookupRequest<F>> {
    for slot in other_half_slots {
        cs.require_invariant(slot, Invariant::RangeChecked { width: 16 });
    }

    // ---- witness ----------------------------------------------------------------------
    {
        let is_mul_var = is_mul.expect_variable();
        let is_mulhu_var = is_mulhu.expect_variable();
        let assume_assigned = CS::ASSUME_MEMORY_VALUES_ASSIGNED;
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            type U32<CS, F> = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32;
            let is_mul = placer.get_boolean(is_mul_var);
            let is_mulhu = placer.get_boolean(is_mulhu_var);
            let is_fam = is_mul.or(&is_mulhu);

            let rs1 = placer.get_u32_from_u16_parts(rs1_limbs);
            let rs2 = placer.get_u32_from_u16_parts(rs2_limbs);
            let (low, high) = rs1.split_widening_product(&rs2);
            let rd = U32::<CS, F>::select(&is_mulhu, &high, &low);
            let other = U32::<CS, F>::select(&is_mulhu, &low, &high);

            let rs1_bytes: [_; 4] =
                core::array::from_fn(|i| rs1.shr(8 * i as u32).truncate().truncate());
            let rs2_bytes: [_; 4] =
                core::array::from_fn(|i| rs2.shr(8 * i as u32).truncate().truncate());

            // chunk carries of the byte schoolbook, as in the standalone mul/div circuit
            let mut carries = [
                U32::<CS, F>::constant(0),
                U32::<CS, F>::constant(0),
                U32::<CS, F>::constant(0),
            ];
            let targets = [low.truncate().widen(), low.shr(16), high.truncate().widen()];
            for i in 0..3 {
                let mut acc = U32::<CS, F>::constant(0);
                for j in 0..4 {
                    for k in 0..4 {
                        let term = rs1_bytes[j].widening_product(&rs2_bytes[k]).widen();
                        if j + k == 2 * i {
                            acc.add_assign(&term);
                        } else if j + k == 2 * i + 1 {
                            acc.add_assign(&term.shl(8));
                        }
                    }
                }
                if i > 0 {
                    let prev = carries[i - 1].clone();
                    acc.add_assign(&prev);
                }
                acc.sub_assign(&targets[i]);
                carries[i] = acc.shr(16);
            }

            placer.conditionally_assign_u16(rs1_byte_slots[0], &is_fam, &rs1_bytes[0].widen());
            placer.conditionally_assign_u16(rs1_byte_slots[1], &is_fam, &rs1_bytes[2].widen());
            placer.conditionally_assign_u32(other_half_slots, &is_fam, &other);
            for i in 0..3 {
                placer.conditionally_assign_u16(carry_slots[i], &is_fam, &carries[i].truncate());
            }
            if !assume_assigned {
                placer.conditionally_assign_u32(rd_write_limbs, &is_fam, &rd);
            }
        };
        cs.set_values(value_fn);
    }

    // ---- lookups: bytes and carries, gated so they pool ----------------------------------
    let fam = || Expr::<F>::from(is_mul) + Expr::from(is_mulhu);
    let inv_256 = F::from_u32_with_reduction(1 << 8).inverse().unwrap();
    let bytes = |limbs: [Variable; 2], slots: [Variable; 2]| -> [Expr<F>; 4] {
        [
            Expr::from(slots[0]),
            (Expr::from(limbs[0]) - Expr::from(slots[0])) * inv_256,
            Expr::from(slots[1]),
            (Expr::from(limbs[1]) - Expr::from(slots[1])) * inv_256,
        ]
    };
    let rs1_bytes = bytes(rs1_limbs, rs1_byte_slots);
    let rs2_bytes = bytes(rs2_limbs, rs2_byte_slots);

    let mut requests = Vec::with_capacity(6);
    for i in 0..4 {
        requests.push(LookupRequest::new(
            fam() * Expr::from(TableType::RangeCheck8x8),
            vec![fam() * rs1_bytes[i].clone(), fam() * rs2_bytes[i].clone()],
        ));
    }
    // c0 < 2^9, c1 < 2^10, c2 < 2^9 for honest witnesses; the field equations below do not
    // wrap for any carry below 2^10 (chunk sums stay below 2^27 ≪ p), so 10 bits suffice.
    requests.push(LookupRequest::new(
        fam() * Expr::from(TableType::RangeCheck10x10),
        vec![
            fam() * Expr::from(carry_slots[0]),
            fam() * Expr::from(carry_slots[1]),
        ],
    ));
    requests.push(LookupRequest::new(
        fam() * Expr::from(TableType::RangeCheck10x10),
        vec![fam() * Expr::from(carry_slots[2])],
    ));

    // ---- product relation one layer up, with every operand masked by the gate -----------
    let q: [Variable; 4] = core::array::from_fn(|j| {
        cs.add_intermediate_named_variable_from_expr(
            fam() * rs1_bytes[j].clone(),
            &format!("mul: rs1 byte {j} (L2)"),
        )
    });
    let d: [Variable; 4] = core::array::from_fn(|k| {
        cs.add_intermediate_named_variable_from_expr(
            fam() * rs2_bytes[k].clone(),
            &format!("mul: rs2 byte {k} (L2)"),
        )
    });
    // (low, high) = (rd, other) for MUL and (other, rd) for MULHU
    let low: [Variable; 2] = core::array::from_fn(|i| {
        cs.add_intermediate_named_variable_from_expr(
            Expr::from(rd_write_limbs[i]).mask(is_mul)
                + Expr::from(other_half_slots[i]).mask(is_mulhu),
            &format!("mul: product low limb {i} (L2)"),
        )
    });
    let high: [Variable; 2] = core::array::from_fn(|i| {
        cs.add_intermediate_named_variable_from_expr(
            Expr::from(rd_write_limbs[i]).mask(is_mulhu)
                + Expr::from(other_half_slots[i]).mask(is_mul),
            &format!("mul: product high limb {i} (L2)"),
        )
    });
    let carries: [Variable; 3] = core::array::from_fn(|i| {
        cs.add_intermediate_named_variable_from_expr(
            fam() * Expr::from(carry_slots[i]),
            &format!("mul: carry {i} (L2)"),
        )
    });

    let shift8 = F::from_u32_with_reduction(1 << 8);
    let shift16 = F::from_u32_with_reduction(1 << 16);
    let targets = [low[0], low[1], high[0], high[1]];
    for i in 0..4 {
        let mut expr = Expr::<F>::zero();
        for j in 0..4 {
            for k in 0..4 {
                if j + k == 2 * i {
                    expr = expr + Expr::from(q[j]) * Expr::from(d[k]);
                } else if j + k == 2 * i + 1 {
                    expr = expr + Expr::from(q[j]) * Expr::from(d[k]) * shift8;
                }
            }
        }
        if i > 0 {
            expr = expr + Expr::from(carries[i - 1]);
        }
        if i < 3 {
            expr = expr - Expr::from(carries[i]) * shift16;
        }
        expr = expr - Expr::from(targets[i]);
        cs.add_constraint_expr(expr);
    }

    requests
}
