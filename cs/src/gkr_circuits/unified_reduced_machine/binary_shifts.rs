use super::circuit::{LookupRequest, F3_SCRATCH_VARS};
use super::*;
use crate::constraint::{Constraint, Term};
use crate::cs::circuit_trait::*;
use crate::cs::lookup_utils::peek_lookup_values_unconstrained_into_variables;
use crate::gkr_circuits::binary_shifts_family::ShiftBinaryFamilyCircuitMask;
use crate::structured_expr::Expr;
use crate::witness_placer::*;
use field::PrimeField;

/// Family 3 (binary ops / shifts) constraints for the unified circuit. Mirrors the
/// standalone inner; rd-write constraints are gated on `is_binary_op + is_shift` so
/// non-Family-3 cycles don't pin rd_write_limbs.
///
/// Xor-rotate (`ZimopIXorRot`) rides the ordinary binary-op path: the decoder gives it
/// funct3 = XorRotate{r} table id (plain binops get the Wide{Xor,Or,And} ids), every
/// binop lookup returns 4 contribution bytes, and the output word is reconstructed
/// cyclically — identity byte placement for the rot-0 wide tables. Xor-rotate's second
/// operand (rd's old value) arrives through the rs2 read port — `preprocess_bytecode`
/// aliases rs2 := rd — with imm = 0, so its rows are operand-identical to register
/// binop rows.
pub fn apply_unified_binary_shifts_inner<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    decoder: ShiftBinaryFamilyCircuitMask,
    rs1_limbs: [Variable; 2],
    rs2_limbs: [Variable; 2],
    rd_write_limbs: [Variable; 2],
    scratch_space: [Variable; F3_SCRATCH_VARS],
) -> Vec<LookupRequest<F>> {
    // NOTE: by preprocessing if we have rd == 0 in any of the opcodes below, then
    // we have rs1 = x0, rs2 = x0 and imm = 0, and it's preprocessed into plain addition,
    // so we do NOT need to mask rd value

    // strategies:
    // - for binary ops we have funct3 that encodes table type (Wide{Xor,Or,And} for plain
    // binops, XorRotate{r} for xor-rotate), and the only thing we need to deal with is the
    // immediate. Instead of preprocessing it as u32, we only sign-extend it into u16, and encode it as 2 lowest bytes.
    // Then we use one lookup to get sign-extension of the higher byte (either 0 or 0xff), and use unchecked addition
    // of the immediate with rs2 value. Every binop table returns 4 contribution bytes
    // (T = LE bytes of `rotate_right((a ^ b) at byte 0, r)`; rot-0 shape for plain binops),
    // and the output word is reconstructed cyclically: out_byte[k] = Σ_i chunk[i][(k-i) mod 4]
    // — which degenerates to identity byte placement for the rot-0 wide tables.
    // - for shifts we take lowest 2 bytes of rs2 and feed it into table to truncate shift amount and ensure correct byte
    // decomposition. Then we use 2 tables: each takes as an input 8-bit chunk of the word, shift amount (5 bits), and funct3, and output
    // contributions to every other output word 8-bit chunk. One table is for the highest byte (for SRA), and another one for all other bytes

    // scratch space
    // - for binary ops we need 17: one for sign-extension of the immediate, and 4x4 for the
    //   contribution bytes (aliasing the shift outputs — the two paths are mutually exclusive)
    // - for shift we need 17: 4x4 for output contributions, and one for truncated shift amount

    const _: () = assert!(F3_SCRATCH_VARS == 21);
    let binary_ops_imm_sign_ext = scratch_space[0];
    let truncated_shift_amount = scratch_space[0];
    let shift_outputs: [Variable; 16] = core::array::from_fn(|i| scratch_space[i + 1]);
    let shift_output_chunks = shift_outputs.as_chunks::<4>().0;

    let inv_256 = F::from_u32_with_reduction(1 << 8).inverse().unwrap();
    let rs1_b0 = scratch_space[17];
    let rs1_b2 = scratch_space[18];
    let rs2_b0 = scratch_space[19];
    let rs2_b2 = scratch_space[20];
    let hi_byte = |lo_limb: Variable, lo_byte: Variable| -> Expr<F> {
        (Expr::from(lo_limb) - Expr::from(lo_byte)) * inv_256
    };
    // [byte0(committed), byte1(linear), byte2(committed), byte3(linear)] per operand.
    let rs1_bytes: [Expr<F>; 4] = [
        Expr::from(rs1_b0),
        hi_byte(rs1_limbs[0], rs1_b0),
        Expr::from(rs1_b2),
        hi_byte(rs1_limbs[1], rs1_b2),
    ];
    let rs2_bytes: [Expr<F>; 4] = [
        Expr::from(rs2_b0),
        hi_byte(rs2_limbs[0], rs2_b0),
        Expr::from(rs2_b2),
        hi_byte(rs2_limbs[1], rs2_b2),
    ];
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let rs1_lo = placer.get_u16(rs1_limbs[0]);
            let rs1_hi = placer.get_u16(rs1_limbs[1]);
            let rs2_lo = placer.get_u16(rs2_limbs[0]);
            let rs2_hi = placer.get_u16(rs2_limbs[1]);
            placer.assign_u8(rs1_b0, &rs1_lo.truncate());
            placer.assign_u8(rs1_b2, &rs1_hi.truncate());
            placer.assign_u8(rs2_b0, &rs2_lo.truncate());
            placer.assign_u8(rs2_b2, &rs2_hi.truncate());
        };
        cs.set_values(value_fn);
    }

    let is_binary_op = decoder.perform_binary_op();
    let is_shift = decoder.perform_shift();

    let shift_amount_constraint: Expr<F> =
        Expr::from(truncated_shift_amount) + Expr::from(inputs.decoder_data.imm[0]);

    // Here we only assign witness

    // first binary ops
    {
        peek_lookup_values_unconstrained_into_variables(
            cs,
            &[LookupInput::from(inputs.decoder_data.imm[1])],
            &[binary_ops_imm_sign_ext],
            LookupInput::from(
                F::from_u32(TableType::GetSignExtensionByte as u32).expect("must fit"),
            ),
            is_binary_op,
        );

        // Per byte-pair, the funct3-selected table (Wide{Xor,Or,And} or XorRotate{r}) returns
        // 4 contribution bytes into the shared shift_output_chunks scratch (binop and shift are
        // mutually exclusive). Xor-rot rows have imm = 0 (decoder), so `b + imm` and the imm
        // sign-extension above both see zeros there.
        for i in 0..4 {
            let a = rs1_bytes[i].clone();
            let b = rs2_bytes[i].clone();
            let imm = if i >= 2 {
                binary_ops_imm_sign_ext
            } else {
                inputs.decoder_data.imm[i]
            };
            let outs = shift_output_chunks[i];

            peek_lookup_values_unconstrained_into_variables(
                cs,
                &[LookupInput::from(a), LookupInput::from(b + Expr::from(imm))],
                &outs,
                LookupInput::from(inputs.decoder_data.funct3.expect("is present")),
                is_binary_op,
            );
        }
    }

    // then shifts
    {
        peek_lookup_values_unconstrained_into_variables(
            cs,
            &[
                LookupInput::from(rs2_bytes[0].clone()),
                LookupInput::from(rs2_bytes[1].clone()),
            ],
            &[truncated_shift_amount],
            LookupInput::from(
                F::from_u32(TableType::TruncateShiftAmountAndRangeCheck8 as u32).expect("must fit"),
            ),
            is_shift,
        );
        for i in 0..4 {
            let a = rs1_bytes[i].clone();
            let outs = shift_output_chunks[i];
            let table_id = TableType::ShiftImplementationOverBytes;
            let byte_index = i;

            peek_lookup_values_unconstrained_into_variables(
                cs,
                &[
                    LookupInput::from(F::from_u32_unchecked(byte_index as u32)),
                    LookupInput::from(a),
                    LookupInput::from(shift_amount_constraint.clone()),
                    LookupInput::from(inputs.decoder_data.funct3.expect("is present")),
                ],
                &outs,
                LookupInput::from(F::from_u32(table_id as u32).expect("must fit")),
                is_shift,
            );
        }
    }

    // and to enforce lookups we will perform selections (via constraints that push to the next layer),
    // where they will be used as lookups. Most of selections are quadratic anyway.

    let combined_request = {
        // Each term is one `flag * operand` product (flag = is_binary_op/is_shift), kept factored.
        let input_0 = Expr::from(is_binary_op) * Expr::from(inputs.decoder_data.imm[1])
            + Expr::from(is_shift) * rs2_bytes[0].clone();
        let input_1 = Expr::from(is_binary_op) * Expr::from(binary_ops_imm_sign_ext)
            + Expr::from(is_shift) * rs2_bytes[1].clone();
        let input_2 = Expr::from(is_shift) * Expr::from(truncated_shift_amount);

        let table_id = Expr::from(is_shift)
            * F::from_u32(TableType::TruncateShiftAmountAndRangeCheck8 as u32).expect("must fit")
            + Expr::from(is_binary_op)
                * F::from_u32(TableType::GetSignExtensionByte as u32).expect("must fit");

        LookupRequest::new(table_id, vec![input_0, input_1, input_2])
    };

    // per-byte main lookups (4): binary-op output bytes / shift output chunks
    let mut per_byte_requests: Vec<LookupRequest<F>> = Vec::with_capacity(4);
    for i in 0..4 {
        // Each lookup column is a sum of factored `flag * operand` products (`Expr` has no
        // `AddAssign`, so accumulate with `= <prev> + <term>`).
        let mut constraints: [Expr<F>; 8] = std::array::from_fn(|_| Expr::zero());

        let byte_index = i;

        // rs1 byte for the binary op, or byte index for shift
        constraints[0] = constraints[0].clone()
            + Expr::from(is_binary_op) * rs1_bytes[i].clone()
            + Expr::from(is_shift) * Expr::from(byte_index as u32);

        let binary_op_imm = if i >= 2 {
            binary_ops_imm_sign_ext
        } else {
            inputs.decoder_data.imm[i]
        };

        // rs2 byte or imm extension for binary op, or rs1 byte for shift
        constraints[1] = constraints[1].clone()
            + Expr::from(is_binary_op) * rs2_bytes[i].clone()
            + Expr::from(is_binary_op) * Expr::from(binary_op_imm)
            + Expr::from(is_shift) * rs1_bytes[i].clone();

        // shift amount for shift (binop tables are (a, b, o0..o3) — inputs at cols 0,1,
        // contribution bytes at cols 2..6)
        constraints[2] =
            constraints[2].clone() + shift_amount_constraint.clone() * Expr::from(is_shift);

        // only shift is used for inputs below. funct3 here
        constraints[3] = constraints[3].clone()
            + Expr::from(is_shift) * Expr::from(inputs.decoder_data.funct3.expect("is present"));

        let shift_outputs = shift_output_chunks[i];

        for j in 0..4 {
            // and outputs of shifts here
            constraints[4 + j] =
                constraints[4 + j].clone() + Expr::from(is_shift) * Expr::from(shift_outputs[j]);
        }

        // binop (incl. xor-rotate): the funct3-selected table — Wide{Xor,Or,And} or
        // XorRotate{r} — is (a, b, o0, o1, o2, o3): 4 contribution bytes at cols 2..6
        // (reusing the shift_output_chunks scratch; the paths are mutually exclusive).
        for j in 0..4 {
            constraints[2 + j] = constraints[2 + j].clone()
                + Expr::from(is_binary_op) * Expr::from(shift_outputs[j]);
        }

        let table_id = Expr::from(is_shift)
            * F::from_u32(TableType::ShiftImplementationOverBytes as u32).expect("must fit")
            + Expr::from(is_binary_op)
                * Expr::from(inputs.decoder_data.funct3.expect("must be present"));

        per_byte_requests.push(LookupRequest::new(table_id, constraints.to_vec()));
    }

    // Self-generating witness (no-ASSUME contract, see jump_branch_slt.rs):
    // derive the rd-write limbs from the byte-level contribution chunks, mirroring
    // the constraints below exactly — shift: sum of the four chunk contributions;
    // binary op (incl. xor-rotate): cyclic reconstruction out_byte[k] = Σ_i
    // chunk[i][(k - i) mod 4], degenerating to identity byte placement for the rot-0
    // Wide{Xor,Or,And} tables. Computed in field space (honest per-lane sums stay
    // < 2^16). Gated on Family 3 (is_binary_op + is_shift).
    if !CS::ASSUME_MEMORY_VALUES_ASSIGNED {
        let is_binary_var = is_binary_op.expect_variable();
        let is_shift_var = is_shift.expect_variable();
        let chunks: [[Variable; 4]; 4] = core::array::from_fn(|i| shift_output_chunks[i]);
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            type Fld<CS, F> = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field;
            let c256 = Fld::<CS, F>::constant(F::from_u32_with_reduction(1 << 8));
            let byte_pair = |placer: &mut CS::WitnessPlacer, b0: Variable, b1: Variable| {
                let mut v = placer.get_field(b1);
                v.mul_assign(&c256);
                v.add_assign(&placer.get_field(b0));
                v
            };

            let is_binary_m = placer.get_boolean(is_binary_var);
            let is_shift_m = placer.get_boolean(is_shift_var);
            let any_f3 = is_binary_m.or(&is_shift_m);

            let mut low = Fld::<CS, F>::constant(F::ZERO);
            let mut high = Fld::<CS, F>::constant(F::ZERO);

            let mut shift_low = Fld::<CS, F>::constant(F::ZERO);
            let mut shift_high = Fld::<CS, F>::constant(F::ZERO);
            let mut binop_low = Fld::<CS, F>::constant(F::ZERO);
            let mut binop_high = Fld::<CS, F>::constant(F::ZERO);
            for i in 0..4 {
                let v = byte_pair(placer, chunks[i][0], chunks[i][1]);
                shift_low.add_assign(&v);
                let v = byte_pair(placer, chunks[i][2], chunks[i][3]);
                shift_high.add_assign(&v);
                // binary op (incl. xor-rotate): out_byte[k] = Σ_i chunk[i][(k - i) mod 4]
                let v = byte_pair(placer, chunks[i][(4 - i) % 4], chunks[i][(1 + 4 - i) % 4]);
                binop_low.add_assign(&v);
                let v = byte_pair(
                    placer,
                    chunks[i][(2 + 4 - i) % 4],
                    chunks[i][(3 + 4 - i) % 4],
                );
                binop_high.add_assign(&v);
            }
            low.add_assign_masked(&is_shift_m, &shift_low);
            high.add_assign_masked(&is_shift_m, &shift_high);
            low.add_assign_masked(&is_binary_m, &binop_low);
            high.add_assign_masked(&is_binary_m, &binop_high);

            placer.conditionally_assign_field(rd_write_limbs[0], &any_f3, &low);
            placer.conditionally_assign_field(rd_write_limbs[1], &any_f3, &high);
        };
        cs.set_values(value_fn);
    }

    // rd-write constraint, gated on Family 3 firing so non-Family-3 cycles in the
    // unified circuit aren't forced to rd_write = 0. is_binary_op + is_shift is
    // the family-firing indicator (mutually exclusive ⇒ sum is 0 or 1).
    let mut low_constraint: Expr<F> = Expr::zero();
    for i in 0..4 {
        let shift_outputs = shift_output_chunks[i];
        low_constraint = low_constraint
            + Expr::from(is_shift)
                * (Expr::constant(F::from_u32_with_reduction(1 << 8))
                    * Expr::var(shift_outputs[1])
                    + Expr::var(shift_outputs[0]));
        // binop (incl. xor-rotate): cyclic reconstruction out_byte[k] = Σ_i chunk[i][(k-i) mod 4]
        // — identity byte placement for the rot-0 Wide{Xor,Or,And} tables.
        // low limb = out_byte[0] + out_byte[1]<<8.
        let b0 = shift_outputs[(4 - i) % 4]; // (0 - i) mod 4
        let b1 = shift_outputs[(1 + 4 - i) % 4]; // (1 - i) mod 4
        low_constraint = low_constraint
            + Expr::from(is_binary_op)
                * (Expr::constant(F::from_u32_with_reduction(1 << 8)) * Expr::var(b1)
                    + Expr::var(b0));
    }
    low_constraint = low_constraint
        - (Expr::from(is_binary_op) + Expr::from(is_shift)) * Expr::var(rd_write_limbs[0]);
    cs.add_constraint_expr(low_constraint);

    let mut high_constraint: Expr<F> = Expr::zero();
    for i in 0..4 {
        let shift_outputs = shift_output_chunks[i];
        high_constraint = high_constraint
            + Expr::from(is_shift)
                * (Expr::constant(F::from_u32_with_reduction(1 << 8))
                    * Expr::var(shift_outputs[3])
                    + Expr::var(shift_outputs[2]));
        // binop (incl. xor-rotate) high limb = out_byte[2] + out_byte[3]<<8.
        let b2 = shift_outputs[(2 + 4 - i) % 4]; // (2 - i) mod 4
        let b3 = shift_outputs[(3 + 4 - i) % 4]; // (3 - i) mod 4
        high_constraint = high_constraint
            + Expr::from(is_binary_op)
                * (Expr::constant(F::from_u32_with_reduction(1 << 8)) * Expr::var(b3)
                    + Expr::var(b2));
    }
    high_constraint = high_constraint
        - (Expr::from(is_binary_op) + Expr::from(is_shift)) * Expr::var(rd_write_limbs[1]);
    cs.add_constraint_expr(high_constraint);

    let mut lookups = vec![combined_request];
    lookups.extend(per_byte_requests);
    lookups
}
