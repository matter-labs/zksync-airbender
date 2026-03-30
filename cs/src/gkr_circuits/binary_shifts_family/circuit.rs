use super::*;
use crate::constraint::Constraint;
use crate::constraint::Term;
use crate::cs::circuit_trait::*;
use crate::cs::lookup_utils::peek_lookup_values_unconstrained_into_variables;
use crate::oracle::Placeholder;
use crate::tables::TableDriver;
use crate::types::*;
use field::PrimeField;

const TABLES_TOTAL_WIDTH: usize = 8;

// NOTE: this circuit should specify non-dummy CSR table in proving/setup. while compilation in tests
// takes case of properly computing offsets by using dummy table

pub fn shift_binop_tables() -> Vec<TableType> {
    vec![
        TableType::ZeroEntry, // we need it, as we use conditional lookup enforcements
        TableType::TruncateShiftAmountAndRangeCheck8,
        TableType::GetSignExtensionByte,
        TableType::ShiftImplementationOverBytes,
        TableType::Xor,
        TableType::And,
        TableType::Or,
    ]
}

pub fn shift_binop_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    for el in shift_binop_tables() {
        cs.materialize_table::<TABLES_TOTAL_WIDTH>(el);
    }
}

pub fn shift_binop_table_driver_fn<F: PrimeField>(table_driver: &mut TableDriver<F>) {
    for el in shift_binop_tables() {
        table_driver.materialize_table::<TABLES_TOTAL_WIDTH>(el);
    }
}

fn apply_shift_binop_inner<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    decoder: ShiftBinaryFamilyCircuitMask,
) {
    // NOTE: by preprocessing if we have rd == 0 in any of the opcodes below, then
    // we have rs1 = x0, rs2 = x0 and imm = 0, and it's preprocessed into plain addition,
    // so we do NOT need to mask rd value

    if let Some(circuit_family_extra_mask) =
        cs.get_value(inputs.decoder_data.circuit_family_extra_mask)
    {
        println!(
            "circuit_family_extra_mask = 0b{:08b}",
            circuit_family_extra_mask.as_u32_reduced()
        );
    }

    // read inputs and prepare outputs
    let rs1_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterRead {
            reg_idx: inputs.decoder_data.rs1_index,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(0),
            split_as_u8: true,
        },
        "rs1",
        0,
    );

    let rs2_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterRead {
            reg_idx: inputs.decoder_data.rs2_index,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(1),
            split_as_u8: true,
        },
        "rs2",
        1,
    );

    let rd_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterReadWrite {
            reg_idx: inputs.decoder_data.rd_index,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(2),
            write_value_placeholder: Placeholder::ShuffleRamWriteValue(2),
            split_read_as_u8: false,
            split_write_as_u8: false,
        },
        "rd",
        2,
    );

    let MemoryAccess::RegisterOnly(rs1_access) = rs1_access else {
        unreachable!()
    };
    let MemoryAccess::RegisterOnly(rs2_access) = rs2_access else {
        unreachable!()
    };
    let MemoryAccess::RegisterOnly(rd_access) = rd_access else {
        unreachable!()
    };

    let WordRepresentation::U8Limbs(rs1_limbs) = rs1_access.read_value else {
        unreachable!()
    };
    let WordRepresentation::U8Limbs(rs2_limbs) = rs2_access.read_value else {
        unreachable!()
    };
    let WordRepresentation::U16Limbs(rd_write_limbs) = rd_access.write_value else {
        unreachable!()
    };

    // if let Some(rs1_reg) = Register(rs1_limbs.map(|el| Num::Var(el))).get_value_unsigned(cs) {
    //     println!("RS1 value = 0x{:08x}", rs1_reg);
    // }

    // if let Some(rs2_reg) = Register(rs2_limbs.map(|el| Num::Var(el))).get_value_unsigned(cs) {
    //     println!("RS2 value = 0x{:08x}", rs2_reg);
    // }

    // if let Some(imm) =
    //     Register::<F>(inputs.decoder_data.imm.map(|el| Num::Var(el))).get_value_unsigned(cs)
    // {
    //     println!("IMM value = 0x{:08x}", imm);
    // }

    // strategies:
    // - for binary ops we have funct3 that encodes table type, and the only thing we need to deal with is
    // immediate. Instead of preprocessing it as u32, we only sign-extend it into u16, and encode it as 2 lowest bytes.
    // Then we use one lookup to get sign-extension of the higher byte (either 0 or 0xff), and use unchecked addition
    // of the immediate with rs2 value
    // - for shifts we take lowest 2 bytes of rs2 and feed it into table to truncate shift amount and ensure correct byte
    // decomposition. Then we use 2 tables: each takes as an input 8-bit chunk of the word, shift amount (5 bits), and funct3, and output
    // contrubutions to every other output word 8-bit chunk. One table is for the highest byte (for SRA), and another one for all other bytes

    // scratch space
    // - for binary ops we need just 5: one for sign-extension of the immediate, and 4 for outputs
    // - for shift we need 17: 4x4 for output contributions, and one for truncated shift amount

    let scratch_space: [Variable; 17] =
        std::array::from_fn(|i| cs.add_named_variable(&format!("scratch space {}", i)));

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

    // constraint for shift amount or immediate sign extension
    {
        let mut input_0 = Constraint::empty();
        input_0 += Term::from(is_binary_op) * Term::from(inputs.decoder_data.imm[1]);
        input_0 += Term::from(is_shift) * Term::from(rs2_limbs[0]);
        let input_0 = cs.add_intermediate_named_variable_from_constraint(
            input_0,
            "input 0 for binary sign ext/trucate shift",
        );

        let mut input_1 = Constraint::empty();
        input_1 += Term::from(is_binary_op) * Term::from(binary_ops_imm_sign_ext);
        input_1 += Term::from(is_shift) * Term::from(rs2_limbs[1]);
        let input_1 = cs.add_intermediate_named_variable_from_constraint(
            input_1,
            "input 1 for binary sign ext/trucate shift",
        );

        let mut input_2 = Constraint::empty();
        input_2 += Term::from(is_shift) * Term::from(truncated_shift_amount);
        let input_2 = cs.add_intermediate_named_variable_from_constraint(
            input_2,
            "input 2 for binary sign ext/trucate shift",
        );

        let mut table_id = Constraint::empty();
        table_id += Term::from(is_shift)
            * Term::from_field(
                F::from_u32(TableType::TruncateShiftAmountAndRangeCheck8 as u32).expect("must fit"),
            );
        table_id += Term::from(is_binary_op)
            * Term::from_field(
                F::from_u32(TableType::GetSignExtensionByte as u32).expect("must fit"),
            );
        let table_id = cs.add_intermediate_named_variable_from_constraint(
            table_id,
            "table ID for binary sign ext/trucate shift",
        );

        cs.enforce_lookup_tuple_for_variable_table(
            &[
                LookupInput::from(input_0),
                LookupInput::from(input_1),
                LookupInput::from(input_2),
            ],
            table_id,
        );
    }
    // and value-related lookups
    {
        for i in 0..4 {
            let mut constraints: [Constraint<F>; TABLES_TOTAL_WIDTH] =
                std::array::from_fn(|_| Constraint::empty());

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

            let input_vars: [Variable; TABLES_TOTAL_WIDTH] = constraints
                .into_iter()
                .enumerate()
                .map(|(idx, el)| {
                    cs.add_intermediate_named_variable_from_constraint(
                        el,
                        &format!("lookup input {} for main part of ops for byte {}", idx, i),
                    )
                })
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();

            let lookup_inputs = input_vars.map(|el| LookupInput::from(el));

            let table_id = {
                let shift_table_id = TableType::ShiftImplementationOverBytes;
                let mut table_id = Constraint::empty();
                table_id += Term::from(is_shift)
                    * Term::from_field(F::from_u32(shift_table_id as u32).expect("must fit"));
                table_id += Term::from(is_binary_op)
                    * Term::from(inputs.decoder_data.funct3.expect("must be present"));
                let table_id = cs.add_intermediate_named_variable_from_constraint(
                    table_id,
                    "table ID for binary/shift main ops",
                );

                table_id
            };

            cs.enforce_lookup_tuple_for_variable_table(&lookup_inputs, table_id);
        }
    }

    // select and write to RD - easiest part

    let mut low_constraint = Constraint::empty();
    low_constraint += Term::from(is_binary_op)
        * (Term::from(1 << 8) * Term::from(binary_ops_outputs[1])
            + Term::from(binary_ops_outputs[0]));
    for i in 0..4 {
        let shift_outputs = shift_output_chunks[i];
        low_constraint += Term::from(is_shift)
            * (Term::from(1 << 8) * Term::from(shift_outputs[1]) + Term::from(shift_outputs[0]));
    }
    low_constraint -= Term::from(rd_write_limbs[0]);
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
    high_constraint -= Term::from(rd_write_limbs[1]);
    cs.add_constraint(high_constraint);

    if let Some(rd_reg) = Register(rd_write_limbs.map(|el| Num::Var(el))).get_value_unsigned(cs) {
        println!("RD value = 0x{:08x}", rd_reg);
    }

    // bump PC
    use crate::gkr_circuits::utils::calculate_pc_next_no_overflows_with_range_checks;
    calculate_pc_next_no_overflows_with_range_checks(
        cs,
        inputs.cycle_start_state.pc,
        inputs.cycle_end_state.pc,
    );
}

pub fn shift_binop_circuit_with_preprocessed_bytecode_for_gkr<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
) {
    let (input, bitmask) = cs.allocate_machine_state(true, false, SHIFT_BINARY_FAMILY_NUM_FLAGS);
    let bitmask: [_; SHIFT_BINARY_FAMILY_NUM_FLAGS] = bitmask.try_into().unwrap();
    let bitmask = bitmask.map(|el| Boolean::Is(el));
    let decoder = ShiftBinaryFamilyCircuitMask::from_mask(bitmask);
    apply_shift_binop_inner(cs, input, decoder);
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use crate::gkr_compiler::compile_unrolled_circuit_state_transition_into_gkr;
    use crate::gkr_compiler::dump_ssa_witness_eval_form;
    use crate::utils::serialize_to_file;

    #[test]
    fn compile_shift_binop_into_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let gkr_compiled = compile_unrolled_circuit_state_transition_into_gkr::<BabyBearField>(
            &|cs| shift_binop_table_addition_fn(cs),
            &|cs| shift_binop_circuit_with_preprocessed_bytecode_for_gkr(cs),
            common_constants::ROM_WORD_SIZE,
            24,
        );

        serialize_to_file(
            &gkr_compiled,
            "compiled_circuits/shift_binop_preprocessed_layout_gkr.json",
        );
    }

    #[test]
    fn compile_shift_binop_gkr_witness_graph() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let ssa_forms = dump_ssa_witness_eval_form::<BabyBearField>(
            &|cs| shift_binop_table_addition_fn(cs),
            &|cs| shift_binop_circuit_with_preprocessed_bytecode_for_gkr(cs),
        );
        serialize_to_file(
            &ssa_forms,
            "compiled_circuits/shift_binop_preprocessed_ssa_gkr.json",
        );
    }
}
