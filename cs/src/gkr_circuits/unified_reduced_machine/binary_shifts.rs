use super::circuit::{LookupRequest, F3_SCRATCH_VARS};
use super::*;
use crate::constraint::{Constraint, Term};
use crate::cs::circuit_trait::*;
use crate::cs::lookup_utils::peek_lookup_values_unconstrained_into_variables;
use crate::gkr_circuits::binary_shifts_family::ShiftBinaryFamilyCircuitMask;
use crate::types::Boolean;
use crate::witness_placer::*;
use field::PrimeField;

/// Family 3 (binary ops / shifts) constraints for the unified circuit. Mirrors the
/// standalone inner; rd-write constraints are gated on `is_binary_op + is_shift`
/// so non-Family-3 cycles don't pin rd_write_limbs.
pub fn apply_unified_binary_shifts_inner<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    decoder: ShiftBinaryFamilyCircuitMask,
    xor_rot: Boolean,
    rs1_limbs: [Variable; 2],
    rs2_limbs: [Variable; 2],
    rd_write_limbs: [Variable; 2],
    rd_read_limbs: [Variable; 2],
    scratch_space: [Variable; F3_SCRATCH_VARS],
) -> Vec<LookupRequest<F>> {
    // NOTE: by preprocessing if we have rd == 0 in any of the opcodes below, then
    // we have rs1 = x0, rs2 = x0 and imm = 0, and it's preprocessed into plain addition,
    // so we do NOT need to mask rd value

    // strategies:
    // - for binary ops we have funct3 that encodes table type, and the only thing we need to deal with is
    // immediate. Instead of preprocessing it as u32, we only sign-extend it into u16, and encode it as 2 lowest bytes.
    // Then we use one lookup to get sign-extension of the higher byte (either 0 or 0xff), and use unchecked addition
    // of the immediate with rs2 value
    // - for shifts we take lowest 2 bytes of rs2 and feed it into table to truncate shift amount and ensure correct byte
    // decomposition. Then we use 2 tables: each takes as an input 8-bit chunk of the word, shift amount (5 bits), and funct3, and output
    // contributions to every other output word 8-bit chunk. One table is for the highest byte (for SRA), and another one for all other bytes

    // scratch space
    // - for binary ops we need just 5: one for sign-extension of the immediate, and 4 for outputs
    // - for shift we need 17: 4x4 for output contributions, and one for truncated shift amount

    const _: () = assert!(F3_SCRATCH_VARS == 23);
    let [binary_ops_imm_sign_ext, binop_output_0, binop_output_1, binop_output_2, binop_output_3, ..] =
        scratch_space;
    let binary_ops_outputs = [
        binop_output_0,
        binop_output_1,
        binop_output_2,
        binop_output_3,
    ];

    let truncated_shift_amount = scratch_space[0];
    let shift_outputs: [Variable; 16] = core::array::from_fn(|i| scratch_space[i + 1]);
    let shift_output_chunks = shift_outputs.as_chunks::<4>().0;

    let inv_256 = F::from_u32_with_reduction(1 << 8).inverse().unwrap();
    let rs1_b0 = scratch_space[17];
    let rs1_b2 = scratch_space[18];
    let rs2_b0 = scratch_space[19];
    let rs2_b2 = scratch_space[20];
    // xor-rotate (unified-only) reads rd_old (rd_read_limbs) as the 2nd XOR operand; split its
    // low bytes the same way as rs1/rs2. These slots are unused by binary-op / shift rows.
    let rd_old_b0 = scratch_space[21];
    let rd_old_b2 = scratch_space[22];
    let hi_byte = |lo_limb: Variable, lo_byte: Variable| -> Constraint<F> {
        let mut c = Constraint::from(lo_limb);
        c -= Constraint::from(lo_byte);
        c.scale(inv_256);
        c
    };
    // [byte0(committed), byte1(linear), byte2(committed), byte3(linear)] per operand.
    let rs1_bytes: [Constraint<F>; 4] = [
        Constraint::from(rs1_b0),
        hi_byte(rs1_limbs[0], rs1_b0),
        Constraint::from(rs1_b2),
        hi_byte(rs1_limbs[1], rs1_b2),
    ];
    let rs2_bytes: [Constraint<F>; 4] = [
        Constraint::from(rs2_b0),
        hi_byte(rs2_limbs[0], rs2_b0),
        Constraint::from(rs2_b2),
        hi_byte(rs2_limbs[1], rs2_b2),
    ];
    let rd_old_bytes: [Constraint<F>; 4] = [
        Constraint::from(rd_old_b0),
        hi_byte(rd_read_limbs[0], rd_old_b0),
        Constraint::from(rd_old_b2),
        hi_byte(rd_read_limbs[1], rd_old_b2),
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
            // rd_old low bytes (xor-rotate 2nd operand).
            let rd_old_lo = placer.get_u16(rd_read_limbs[0]);
            let rd_old_hi = placer.get_u16(rd_read_limbs[1]);
            placer.assign_u8(rd_old_b0, &rd_old_lo.truncate());
            placer.assign_u8(rd_old_b2, &rd_old_hi.truncate());
        };
        cs.set_values(value_fn);
    }

    let is_binary_op = decoder.perform_binary_op();
    let is_shift = decoder.perform_shift();
    let is_xor_rot = xor_rot;

    {
        // At most one Family-3 sub-opcode fires per row (binary-op / shift / xor-rotate).
        let f3_sum: Constraint<F> =
            Term::from(is_binary_op) + Term::from(is_shift) + Term::from(is_xor_rot);
        cs.add_constraint(f3_sum.clone() * (f3_sum - Term::from(1u32)));
    }

    let shift_amount_constraint =
        Constraint::from(truncated_shift_amount) + Term::from(inputs.decoder_data.imm[0]);

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

        for i in 0..4 {
            let a = rs1_bytes[i].clone();
            let b = rs2_bytes[i].clone();
            let imm = if i >= 2 {
                binary_ops_imm_sign_ext
            } else {
                inputs.decoder_data.imm[i]
            };
            let out = binary_ops_outputs[i];

            peek_lookup_values_unconstrained_into_variables(
                cs,
                &[LookupInput::from(a), LookupInput::from(b + Term::from(imm))],
                &[out],
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

    // then xor-rotate (unified-only): per byte, look up the funct3-selected XorRotate{r} table on
    // (rs1_byte, rd_old_byte) -> the 4 contribution bytes T_i = rotate_right((rs1^rd_old) byte at
    // byte 0, r). Reuses the shift_output_chunks scratch (shift and xor-rot are mutually exclusive).
    {
        for i in 0..4 {
            let a = rs1_bytes[i].clone();
            let b = rd_old_bytes[i].clone();
            let outs = shift_output_chunks[i];
            peek_lookup_values_unconstrained_into_variables(
                cs,
                &[LookupInput::from(a), LookupInput::from(b)],
                &outs,
                LookupInput::from(inputs.decoder_data.funct3.expect("is present")),
                is_xor_rot,
            );
        }
    }

    // and to enforce lookups we will perform selections (via constraints that push to the next layer),
    // where they will be used as lookups. Most of selections are quadratic anyway.

    let combined_request = {
        let mut input_0 = Constraint::empty();
        input_0 += Term::from(is_binary_op) * Term::from(inputs.decoder_data.imm[1]);
        input_0 += Term::from(is_shift) * rs2_bytes[0].clone();

        let mut input_1 = Constraint::empty();
        input_1 += Term::from(is_binary_op) * Term::from(binary_ops_imm_sign_ext);
        input_1 += Term::from(is_shift) * rs2_bytes[1].clone();

        let mut input_2 = Constraint::empty();
        input_2 += Term::from(is_shift) * Term::from(truncated_shift_amount);

        let mut table_id = Constraint::empty();
        table_id += Term::from(is_shift)
            * Term::from_field(
                F::from_u32(TableType::TruncateShiftAmountAndRangeCheck8 as u32).expect("must fit"),
            );
        table_id += Term::from(is_binary_op)
            * Term::from_field(
                F::from_u32(TableType::GetSignExtensionByte as u32).expect("must fit"),
            );

        LookupRequest::new(table_id, vec![input_0, input_1, input_2])
    };

    // per-byte main lookups (4): binary-op output bytes / shift output chunks
    let mut per_byte_requests: Vec<LookupRequest<F>> = Vec::with_capacity(4);
    for i in 0..4 {
        let mut constraints: [Constraint<F>; 8] = std::array::from_fn(|_| Constraint::empty());

        let byte_index = i;

        // rs1 byte for the binary op, or byte index for shift
        constraints[0] += Term::from(is_binary_op) * rs1_bytes[i].clone();
        constraints[0] += Term::from(is_shift) * Term::from(byte_index as u32);

        let binary_op_imm = if i >= 2 {
            binary_ops_imm_sign_ext
        } else {
            inputs.decoder_data.imm[i]
        };

        // rs2 byte or imm extension for binary op, or rs1 byte for shift
        constraints[1] += Term::from(is_binary_op) * rs2_bytes[i].clone();
        constraints[1] += Term::from(is_binary_op) * Term::from(binary_op_imm);
        constraints[1] += Term::from(is_shift) * rs1_bytes[i].clone();

        // output for the binary op, or shift amount for shift
        constraints[2] += Term::from(is_binary_op) * Term::from(binary_ops_outputs[i]);
        constraints[2] += shift_amount_constraint.clone() * Term::from(is_shift);

        // only shift is used for inputs below. funct3 here
        constraints[3] +=
            Term::from(is_shift) * Term::from(inputs.decoder_data.funct3.expect("is present"));

        let shift_outputs = shift_output_chunks[i];

        for j in 0..4 {
            // and outputs of shifts here
            constraints[4 + j] += Term::from(is_shift) * Term::from(shift_outputs[j]);
        }

        // xor-rotate: the XorRotate{r} table is (a, b, o0, o1, o2, o3) — inputs at cols 0,1,
        // the 4 contribution bytes at cols 2..6 (reusing the shift_output_chunks scratch).
        constraints[0] += Term::from(is_xor_rot) * rs1_bytes[i].clone();
        constraints[1] += Term::from(is_xor_rot) * rd_old_bytes[i].clone();
        for j in 0..4 {
            constraints[2 + j] += Term::from(is_xor_rot) * Term::from(shift_outputs[j]);
        }

        let mut table_id = Constraint::empty();
        table_id += Term::from(is_shift)
            * Term::from_field(
                F::from_u32(TableType::ShiftImplementationOverBytes as u32).expect("must fit"),
            );
        table_id += Term::from(is_binary_op)
            * Term::from(inputs.decoder_data.funct3.expect("must be present"));
        // xor-rotate dispatches by funct3 = the per-rotation XorRotate{r} table id.
        table_id += Term::from(is_xor_rot)
            * Term::from(inputs.decoder_data.funct3.expect("must be present"));

        per_byte_requests.push(LookupRequest::new(table_id, constraints.to_vec()));
    }

    // rd-write constraint, gated on Family 3 firing so non-Family-3 cycles in the
    // unified circuit aren't forced to rd_write = 0. is_binary_op + is_shift is
    // the family-firing indicator (mutually exclusive ⇒ sum is 0 or 1).
    let mut low_constraint = Constraint::empty();
    low_constraint += Term::from(is_binary_op)
        * (Term::from(1 << 8) * Term::from(binary_ops_outputs[1])
            + Term::from(binary_ops_outputs[0]));
    for i in 0..4 {
        let shift_outputs = shift_output_chunks[i];
        low_constraint += Term::from(is_shift)
            * (Term::from(1 << 8) * Term::from(shift_outputs[1]) + Term::from(shift_outputs[0]));
        // xor-rotate: cyclic reconstruction out_byte[k] = Σ_i chunk[i][(k - i) mod 4].
        // low limb = out_byte[0] + out_byte[1]<<8.
        let b0 = shift_outputs[(4 - i) % 4]; // (0 - i) mod 4
        let b1 = shift_outputs[(1 + 4 - i) % 4]; // (1 - i) mod 4
        low_constraint +=
            Term::from(is_xor_rot) * (Term::from(1 << 8) * Term::from(b1) + Term::from(b0));
    }
    low_constraint -=
        (Constraint::from(is_binary_op) + Term::from(is_shift) + Term::from(is_xor_rot))
            * Term::from(rd_write_limbs[0]);
    cs.add_constraint(low_constraint);

    let mut high_constraint = Constraint::empty();
    high_constraint += Term::from(is_binary_op)
        * (Term::from(1 << 8) * Term::from(binary_ops_outputs[3])
            + Term::from(binary_ops_outputs[2]));
    for i in 0..4 {
        let shift_outputs = shift_output_chunks[i];
        high_constraint += Term::from(is_shift)
            * (Term::from(1 << 8) * Term::from(shift_outputs[3]) + Term::from(shift_outputs[2]));
        // xor-rotate high limb = out_byte[2] + out_byte[3]<<8.
        let b2 = shift_outputs[(2 + 4 - i) % 4]; // (2 - i) mod 4
        let b3 = shift_outputs[(3 + 4 - i) % 4]; // (3 - i) mod 4
        high_constraint +=
            Term::from(is_xor_rot) * (Term::from(1 << 8) * Term::from(b3) + Term::from(b2));
    }
    high_constraint -=
        (Constraint::from(is_binary_op) + Term::from(is_shift) + Term::from(is_xor_rot))
            * Term::from(rd_write_limbs[1]);
    cs.add_constraint(high_constraint);

    let mut lookups = vec![combined_request];
    lookups.extend(per_byte_requests);
    lookups
}
