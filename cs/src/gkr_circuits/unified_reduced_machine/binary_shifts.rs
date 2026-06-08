use super::circuit::{LookupRequest, F3_SCRATCH_VARS};
use super::*;
use crate::constraint::{Constraint, Term};
use crate::cs::circuit_trait::*;
use crate::cs::lookup_utils::peek_lookup_values_unconstrained_into_variables;
use crate::gkr_circuits::binary_shifts_family::ShiftBinaryFamilyCircuitMask;
use crate::types::*;
use field::PrimeField;

/// Family 3 (binary ops / shifts) constraints for the unified circuit. Mirrors the
/// standalone inner; rd-write constraints are gated on `is_binary_op + is_shift`
/// so non-Family-3 cycles don't pin rd_write_limbs.
pub fn apply_unified_binary_shifts_inner<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    decoder: ShiftBinaryFamilyCircuitMask,
    rs1_limbs: [Variable; 4],
    rs2_limbs: [Variable; 4],
    rd_write_limbs: [Variable; 2],
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

    let [binary_ops_imm_sign_ext, binop_output_0, binop_output_1, binop_output_2, binop_output_3, ..] =
        scratch_space;
    let binary_ops_outputs = [
        binop_output_0,
        binop_output_1,
        binop_output_2,
        binop_output_3,
    ];

    let truncated_shift_amount = scratch_space[0];
    let shift_outputs: [Variable; 16] = scratch_space[1..].try_into().unwrap();
    let shift_output_chunks = shift_outputs.as_chunks::<4>().0;

    let is_binary_op = decoder.perform_binary_op();
    let is_shift = decoder.perform_shift();

    {
        let f3_sum: Constraint<F> = Term::from(is_binary_op) + Term::from(is_shift);
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
            let a = rs1_limbs[i];
            let b = rs2_limbs[i];
            let imm = if i >= 2 {
                binary_ops_imm_sign_ext
            } else {
                inputs.decoder_data.imm[i]
            };
            let out = binary_ops_outputs[i];

            peek_lookup_values_unconstrained_into_variables(
                cs,
                &[
                    LookupInput::from(a),
                    LookupInput::from(Constraint::from(b) + Term::from(imm)),
                ],
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
                LookupInput::from(rs2_limbs[0]),
                LookupInput::from(rs2_limbs[1]),
            ],
            &[truncated_shift_amount],
            LookupInput::from(
                F::from_u32(TableType::TruncateShiftAmountAndRangeCheck8 as u32).expect("must fit"),
            ),
            is_shift,
        );
        for i in 0..4 {
            let a = rs1_limbs[i];
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
        let mut input_0 = Constraint::empty();
        input_0 += Term::from(is_binary_op) * Term::from(inputs.decoder_data.imm[1]);
        input_0 += Term::from(is_shift) * Term::from(rs2_limbs[0]);

        let mut input_1 = Constraint::empty();
        input_1 += Term::from(is_binary_op) * Term::from(binary_ops_imm_sign_ext);
        input_1 += Term::from(is_shift) * Term::from(rs2_limbs[1]);

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

        LookupRequest {
            table_id,
            inputs: vec![input_0, input_1, input_2],
        }
    };

    // per-byte main lookups (4): binary-op output bytes / shift output chunks
    let mut per_byte_requests: Vec<LookupRequest<F>> = Vec::with_capacity(4);
    for i in 0..4 {
        let mut constraints: [Constraint<F>; 8] = std::array::from_fn(|_| Constraint::empty());

        let byte_index = i;

        // rs1 byte for the binary op, or byte index for shift
        constraints[0] += Term::from(is_binary_op) * Term::from(rs1_limbs[i]);
        constraints[0] += Term::from(is_shift) * Term::from(byte_index as u32);

        let binary_op_imm = if i >= 2 {
            binary_ops_imm_sign_ext
        } else {
            inputs.decoder_data.imm[i]
        };

        // rs2 byte or imm extension for binary op, or rs1 byte for shift
        constraints[1] += Term::from(is_binary_op) * Term::from(rs2_limbs[i]);
        constraints[1] += Term::from(is_binary_op) * Term::from(binary_op_imm);
        constraints[1] += Term::from(is_shift) * Term::from(rs1_limbs[i]);

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

        let mut table_id = Constraint::empty();
        table_id += Term::from(is_shift)
            * Term::from_field(
                F::from_u32(TableType::ShiftImplementationOverBytes as u32).expect("must fit"),
            );
        table_id += Term::from(is_binary_op)
            * Term::from(inputs.decoder_data.funct3.expect("must be present"));

        per_byte_requests.push(LookupRequest {
            table_id,
            inputs: constraints.to_vec(),
        });
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
    }
    low_constraint -=
        (Constraint::from(is_binary_op) + Term::from(is_shift)) * Term::from(rd_write_limbs[0]);
    cs.add_constraint(low_constraint);

    let mut high_constraint = Constraint::empty();
    high_constraint += Term::from(is_binary_op)
        * (Term::from(1 << 8) * Term::from(binary_ops_outputs[3])
            + Term::from(binary_ops_outputs[2]));
    for i in 0..4 {
        let shift_outputs = shift_output_chunks[i];
        high_constraint += Term::from(is_shift)
            * (Term::from(1 << 8) * Term::from(shift_outputs[3]) + Term::from(shift_outputs[2]));
    }
    high_constraint -=
        (Constraint::from(is_binary_op) + Term::from(is_shift)) * Term::from(rd_write_limbs[1]);
    cs.add_constraint(high_constraint);

    let mut lookups = vec![combined_request];
    lookups.extend(per_byte_requests);
    lookups
}
