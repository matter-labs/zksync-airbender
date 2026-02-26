//! Encodings of lookup tables into LLZK.

use crate::builder::OpsBuilder;
use crate::codegen::StructVars;
use crate::constraints::EmitLlzkInConstrain as _;
use crate::field::FieldInfo;
use crate::keccak_tables::keccak_permutation_indices_outputs;
use anyhow::Result;
use llzk::dialect::bool;
use llzk::dialect::felt;
use melior::ir::Value;
use prover::common_constants;
use prover::cs::cs::circuit::DisjunctiveLookup;
use prover::cs::cs::circuit::LookupQuery;
use prover::cs::cs::circuit::LookupQueryTableType;
use prover::cs::definitions::Variable;
use prover::cs::tables::TableType;
use prover::cs::types::Num;

/// Add constraints that the LookupQuery represents based on the parsed table type.
/// If `conditional` is specified, then all generated constraints will be implications
/// based on `conditional`.
pub fn add_lookup_constraints_for_table<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    table: TableType,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    match table {
        TableType::RangeCheckSmall => add_range_check_small_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::U16GetSignAndHighByte => add_u16_get_sign_and_high_byte_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::U16SplitAsBytes => add_u16_split_as_bytes_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::RangeCheck9x9 => add_range_check_two_tuple_lookup_constraints::<F, 9>(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::RangeCheck10x10 => add_range_check_two_tuple_lookup_constraints::<F, 10>(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::RangeCheck11 => add_range_check_single_entry_lookup_constraints::<F, 11>(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::RangeCheck12 => add_range_check_single_entry_lookup_constraints::<F, 12>(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::RangeCheck13 => add_range_check_single_entry_lookup_constraints::<F, 13>(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::ConditionalJmpBranchSlt => add_conditional_jmp_branch_slt_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::JumpCleanupOffset => {
            add_jump_cleanup_lookup_constraints(builder, vars, query, row_multiplier, conditional)
        }
        TableType::MemoryGetOffsetAndMaskWithTrap => {
            add_memory_get_offset_and_mask_with_trap_lookup_constraints(
                builder,
                vars,
                query,
                row_multiplier,
                conditional,
            )
        }
        TableType::RomAddressSpaceSeparator => add_rom_address_space_separator_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::RomRead => {
            add_rom_read_lookup_constraints(builder, vars, query, row_multiplier, conditional)
        }
        TableType::SpecialCSRProperties => add_special_csr_properties_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::MemoryOffsetGetBits => add_memory_offset_get_bits_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::MemoryLoadHalfwordOrByte => add_memory_load_halfword_or_byte_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::ExtendLoadedValue => add_extend_loaded_value_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::StoreByteSourceContribution => {
            add_store_byte_source_contribution_lookup_constraints(
                builder,
                vars,
                query,
                row_multiplier,
                conditional,
            )
        }
        TableType::StoreByteExistingContribution => {
            add_store_byte_existing_contribution_lookup_constraints(
                builder,
                vars,
                query,
                row_multiplier,
                conditional,
            )
        }
        TableType::MemStoreClearOriginalRamValueLimb => {
            add_mem_store_clear_original_ram_value_limb_lookup_constraints(
                builder,
                vars,
                query,
                row_multiplier,
                conditional,
            )
        }
        TableType::MemStoreClearWrittenValueLimb => {
            add_mem_store_clear_written_value_limb_lookup_constraints(
                builder,
                vars,
                query,
                row_multiplier,
                conditional,
            )
        }
        TableType::AlignedRomRead => add_aligned_rom_read_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::TruncateShiftAmount => add_truncate_shift_amount_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::Xor => add_bitwise_byte_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
            8,
            felt::bit_xor,
        ),
        TableType::Xor3 => add_bitwise_byte_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
            3,
            felt::bit_xor,
        ),
        TableType::Xor4 => add_bitwise_byte_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
            4,
            felt::bit_xor,
        ),
        TableType::Xor7 => add_bitwise_byte_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
            7,
            felt::bit_xor,
        ),
        TableType::Xor9 => add_bitwise_byte_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
            9,
            felt::bit_xor,
        ),
        TableType::Xor12 => add_bitwise_byte_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
            12,
            felt::bit_xor,
        ),
        TableType::Or => add_bitwise_byte_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
            8,
            felt::bit_or,
        ),
        TableType::And => add_bitwise_byte_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
            8,
            felt::bit_and,
        ),
        TableType::RangeCheck16WithZeroPads => {
            add_range_check_16_with_zero_pads_lookup_constraints(
                builder,
                vars,
                query,
                row_multiplier,
                conditional,
            )
        }
        TableType::QuickDecodeDecompositionCheck4x4x4 => {
            add_quick_decode_decomposition_lookup_constraints::<F, 4, 4, 4>(
                builder,
                vars,
                query,
                row_multiplier,
                conditional,
            )
        }
        TableType::QuickDecodeDecompositionCheck7x3x6 => {
            add_quick_decode_decomposition_lookup_constraints::<F, 7, 3, 6>(
                builder,
                vars,
                query,
                row_multiplier,
                conditional,
            )
        }
        TableType::OpTypeBitmask => add_op_type_bitmask_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::ShiftImplementation => add_shift_implementation_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::SRASignFiller => add_sra_sign_filler_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::ConditionalOpAllConditionsResolver => {
            add_conditional_op_all_conditions_lookup_constraints(
                builder,
                vars,
                query,
                row_multiplier,
                conditional,
            )
        }
        TableType::SllWith16BitInputLow => add_logical_shift_16_bit_lookup_constraints::<
            F,
            false,
            false,
        >(
            builder, vars, query, row_multiplier, conditional
        ),
        TableType::SllWith16BitInputHigh => add_logical_shift_16_bit_lookup_constraints::<
            F,
            true,
            false,
        >(
            builder, vars, query, row_multiplier, conditional
        ),
        TableType::SrlWith16BitInputLow => add_logical_shift_16_bit_lookup_constraints::<
            F,
            false,
            true,
        >(
            builder, vars, query, row_multiplier, conditional
        ),
        TableType::SrlWith16BitInputHigh => add_logical_shift_16_bit_lookup_constraints::<
            F,
            true,
            true,
        >(
            builder, vars, query, row_multiplier, conditional
        ),
        TableType::Sra16BitInputSignFill => add_sra_16_bit_input_sign_fill_lookup_constraints(
            builder,
            vars,
            query,
            row_multiplier,
            conditional,
        ),
        TableType::KeccakPermutationIndices12
        | TableType::KeccakPermutationIndices34
        | TableType::KeccakPermutationIndices56 => {
            add_keccak_permutation_indices_lookup_constraints(
                builder,
                vars,
                query,
                table,
                row_multiplier,
                conditional,
            )
        }
        _ => panic!("unsupported lookup table in LLZK lookup lowering: {table:#?}"),
    }
}

/// Returns true when row-multiplication by an activation flag is safe for the table.
///
/// Safety criterion here is that the multiplied inactive row still corresponds to a
/// valid table behavior for the summarization strategy.
fn table_supports_zero_row_multiply_in(table: TableType) -> bool {
    matches!(
        table,
        TableType::RangeCheckSmall
            | TableType::U16GetSignAndHighByte
            | TableType::U16SplitAsBytes
            | TableType::RangeCheck9x9
            | TableType::RangeCheck10x10
            | TableType::RangeCheck11
            | TableType::RangeCheck12
            | TableType::RangeCheck13
            | TableType::MemoryOffsetGetBits
            | TableType::ExtendLoadedValue
            | TableType::StoreByteSourceContribution
            | TableType::StoreByteExistingContribution
            | TableType::MemoryLoadHalfwordOrByte
            | TableType::MemStoreClearOriginalRamValueLimb
            | TableType::Xor
            | TableType::Xor3
            | TableType::Xor4
            | TableType::Xor7
            | TableType::Xor9
            | TableType::Xor12
            | TableType::Or
            | TableType::And
            | TableType::RangeCheck16WithZeroPads
            | TableType::ShiftImplementation
            | TableType::SRASignFiller
            | TableType::ConditionalOpAllConditionsResolver
            | TableType::SllWith16BitInputLow
            | TableType::SllWith16BitInputHigh
            | TableType::SrlWith16BitInputLow
            | TableType::SrlWith16BitInputHigh
            | TableType::Sra16BitInputSignFill
            | TableType::QuickDecodeDecompositionCheck4x4x4
            | TableType::QuickDecodeDecompositionCheck7x3x6
            | TableType::TruncateShiftAmount
    )
}

/// Combine an outer felt-valued condition with an `i1` table-selection predicate.
fn combine_case_condition<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    conditional: Option<Value<'ctx, 'sco>>,
    predicate: Value<'ctx, 'sco>,
) -> Result<Option<Value<'ctx, 'sco>>> {
    let predicate = builder.append_bool_to_field(predicate)?;
    match conditional {
        Some(conditional) => Ok(Some(
            builder.append_product_here(&[conditional, predicate])?,
        )),
        None => Ok(Some(predicate)),
    }
}

/// Lower variable table ids for the currently supported byte-wise binary-op family.
///
/// `shift_binary_csr` emits `LookupQueryTableType::Variable(funct3)` for the XOR/OR/AND byte
/// tables. The source circuit already constrains the decoder's `funct3`, so we can preserve
/// the same logic by predicating all three table lookup results with a `table_id == <constant>`
/// condition.
pub fn add_dynamic_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    table_id_variable: Variable,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let table_id = vars.get_constrain_val(builder, &table_id_variable)?;
    let location = builder.current_location();
    let candidates = [TableType::Xor, TableType::Or, TableType::And];
    let matches = candidates
        .iter()
        .map(|table| builder.append_field_eq_constant(table_id, u64::from(table.to_table_id())))
        .collect::<Result<Vec<_>>>()?;

    for is_match in &matches {
        builder.append_conditional_boolean_constraint(
            conditional,
            builder.append_bool_to_field(*is_match)?,
        )?;
    }

    let match_sum = builder.append_sum(
        location,
        &matches
            .iter()
            .map(|is_match| builder.append_bool_to_field(*is_match))
            .collect::<Result<Vec<_>>>()?,
    )?;
    builder.append_conditional_constrain_eq(
        location,
        conditional,
        match_sum,
        builder.get_felt_constant_from_start(1)?,
    )?;

    for (table, is_match) in candidates.into_iter().zip(matches.into_iter()) {
        add_lookup_constraints_for_table(
            builder,
            vars,
            query,
            table,
            row_multiplier,
            combine_case_condition(builder, conditional, is_match)?,
        )?;
    }

    Ok(())
}

/// Adds translated constraints for disjunctive lookup metadata emitted by optimization context.
///
/// For each disjunctive relation this function:
/// - adds postconditions that flags are boolean and satisfy `sum(flags) <= 1`,
/// - dispatches each case through the same table translator,
/// - either multiplies row expressions by flag for safe tables or guards case constraints under
///   `(flag = 1) => ...`.
pub fn add_disjunctive_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    relation: &DisjunctiveLookup<F>,
) -> Result<()> {
    let flags = relation
        .cases
        .iter()
        .map(|case| case.flag.emit_constrain(builder, vars))
        .collect::<Result<Vec<Value<'ctx, 'sco>>>>()?;

    for flag in &flags {
        builder.append_boolean_constraint(*flag)?;
    }
    let flag_sum = builder.append_sum_here(&flags)?;
    // flag_sum <= 1, meaning flag_sum must be boolean
    builder.append_boolean_constraint(flag_sum)?;

    for case in &relation.cases {
        let table_id = match case.table {
            Num::Var(_variable) => {
                panic!("variable table ids in disjunctive lookup queries are not yet supported")
            }
            Num::Constant(table_id) => table_id,
        };

        let table = TableType::get_table_from_id(table_id.as_u64_reduced() as u32);
        let query = LookupQuery {
            row: case.row.clone(),
            table: LookupQueryTableType::Constant(table),
        };
        let flag_expr = case.flag.emit_constrain(builder, vars)?;

        if table_supports_zero_row_multiply_in(table) {
            add_lookup_constraints_for_table(builder, vars, &query, table, Some(flag_expr), None)?;
        } else {
            // The lookup constraints in these tables are conditional on the flag_expr.
            add_lookup_constraints_for_table(builder, vars, &query, table, None, Some(flag_expr))?;
        }
    }
    Ok(())
}

/// Multiplies the value by the row_multiplier if one is provided, otherwise
/// yield the original value.
fn apply_row_multiplier<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    val: Value<'ctx, 'sco>,
) -> Result<Value<'ctx, 'sco>> {
    match row_multiplier {
        Some(coeff) => {
            let op = felt::mul(builder.current_location(), coeff, val)?;
            builder.append_op_with_result(op)
        }
        None => Ok(val),
    }
}

/// Lower the canonical width-3 lookup row `(row[0], row[1], row[2])` into felt values and apply
/// the optional row multiplier to each element.
fn constrain_lookup_row3<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
) -> Result<(Value<'ctx, 'sco>, Value<'ctx, 'sco>, Value<'ctx, 'sco>)> {
    Ok((
        apply_row_multiplier::<F>(
            builder,
            row_multiplier,
            query.row[0].emit_constrain(builder, vars)?,
        )?,
        apply_row_multiplier::<F>(
            builder,
            row_multiplier,
            query.row[1].emit_constrain(builder, vars)?,
        )?,
        apply_row_multiplier::<F>(
            builder,
            row_multiplier,
            query.row[2].emit_constrain(builder, vars)?,
        )?,
    ))
}

/// Translation for `RangeCheckSmall`.
///
/// This table is the width-3 two-tuple form of the 8-bit range check table, so the row shape is
/// `(a, b, 0)`.
fn add_range_check_small_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (a, b, zero_pad) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    let zero = builder.get_constant_from_start(builder.felt_type(), 0)?;

    builder.append_conditional_range_constraint(conditional, a, 8)?;
    builder.append_conditional_range_constraint(conditional, b, 8)?;
    builder.append_conditional_constrain_eq_here(conditional, zero_pad, zero)
}

/// Translation for the width-3 two-tuple range-check tables `(a, b, 0)`.
fn add_range_check_two_tuple_lookup_constraints<'ctx, 'sco, F: FieldInfo, const WIDTH: usize>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (a, b, zero_pad) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    let zero = builder.get_constant_from_start(builder.felt_type(), 0)?;

    builder.append_conditional_range_constraint(conditional, a, WIDTH)?;
    builder.append_conditional_range_constraint(conditional, b, WIDTH)?;
    builder.append_conditional_constrain_eq_here(conditional, zero_pad, zero)
}

/// Translation for the width-3 single-entry range-check tables `(value, 0, 0)`.
fn add_range_check_single_entry_lookup_constraints<'ctx, 'sco, F: FieldInfo, const WIDTH: usize>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (value, zero_0, zero_1) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    let zero = builder.get_constant_from_start(builder.felt_type(), 0)?;

    builder.append_conditional_range_constraint(conditional, value, WIDTH)?;
    builder.append_conditional_constrain_eq_here(conditional, zero_0, zero)?;
    builder.append_conditional_constrain_eq_here(conditional, zero_1, zero)
}

/// Translation for the `KeccakPermutationIndices{12,34,56}` tables.
///
/// These tables are total width-3 lookups of the form `(control_with_exe, out_i, out_j)`, where
/// the two outputs are deterministic small constants derived from the 12-bit control key.
fn add_keccak_permutation_indices_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    table: TableType,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (control_with_exe, out_0, out_1) =
        constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    builder.append_conditional_range_constraint(conditional, control_with_exe, 12)?;

    let (expected_0, expected_1) =
        append_keccak_permutation_indices_expected_outputs(builder, control_with_exe, table)?;
    let location = builder.current_location();
    builder.append_conditional_constrain_eq(location, conditional, out_0, expected_0)?;
    builder.append_conditional_constrain_eq(location, conditional, out_1, expected_1)
}

fn append_keccak_permutation_indices_expected_outputs<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    control_with_exe: Value<'ctx, 'sco>,
    table: TableType,
) -> Result<(Value<'ctx, 'sco>, Value<'ctx, 'sco>)> {
    let (first_0, second_0) = keccak_permutation_indices_outputs(table, 0);
    let mut selected_first = builder.get_felt_constant_from_start(first_0)?;
    let mut selected_second = builder.get_felt_constant_from_start(second_0)?;

    for control in 1..(1u64 << 12) {
        let (candidate_first, candidate_second) =
            keccak_permutation_indices_outputs(table, control);
        let is_selected = builder.append_field_eq_constant(control_with_exe, control)?;
        selected_first = builder.append_select_value(
            is_selected,
            builder.get_felt_constant_from_start(candidate_first)?,
            selected_first,
        )?;
        selected_second = builder.append_select_value(
            is_selected,
            builder.get_felt_constant_from_start(candidate_second)?,
            selected_second,
        )?;
    }

    Ok((selected_first, selected_second))
}

/// Translation for `U16GetSignAndHighByte`.
///
/// The table row is `(value, sign_bit, high_byte)`, with `sign_bit` equal to the top bit of the
/// input and `high_byte` equal to bits `[15:8]`.
fn add_u16_get_sign_and_high_byte_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (value, sign, high_byte) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;

    let low_byte = builder.new_nondet_felt()?;
    let high_byte_low_bits = builder.new_nondet_felt()?;
    let location = builder.current_location();
    let byte_scale = builder.get_constant_from_start(builder.felt_type(), 1 << 8)?;
    let sign_scale = builder.get_constant_from_start(builder.felt_type(), 1 << 7)?;

    builder.append_conditional_range_constraint(conditional, value, 16)?;
    builder.append_conditional_boolean_constraint(conditional, sign)?;
    builder.append_conditional_range_constraint(conditional, high_byte, 8)?;
    builder.append_conditional_range_constraint(conditional, low_byte, 8)?;
    builder.append_conditional_range_constraint(conditional, high_byte_low_bits, 7)?;

    let reconstructed = builder.append_op_with_result(felt::add(
        location,
        low_byte,
        builder.append_op_with_result(felt::mul(location, byte_scale, high_byte)?)?,
    )?)?;
    builder.append_conditional_constrain_eq(location, conditional, value, reconstructed)?;

    let expected_high_byte = builder.append_op_with_result(felt::add(
        location,
        high_byte_low_bits,
        builder.append_op_with_result(felt::mul(location, sign_scale, sign)?)?,
    )?)?;
    builder.append_conditional_constrain_eq(location, conditional, high_byte, expected_high_byte)
}

/// Translation for `U16SplitAsBytes`.
///
/// The table row is `(value, low_byte, high_byte)`, with `value = low_byte + 256 * high_byte`.
fn add_u16_split_as_bytes_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (value, low_byte, high_byte) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    let location = builder.current_location();
    let byte_scale = builder.get_constant_from_start(builder.felt_type(), 1 << 8)?;

    builder.append_conditional_range_constraint(conditional, value, 16)?;
    builder.append_conditional_range_constraint(conditional, low_byte, 8)?;
    builder.append_conditional_range_constraint(conditional, high_byte, 8)?;

    let reconstructed = builder.append_op_with_result(felt::add(
        location,
        low_byte,
        builder.append_op_with_result(felt::mul(location, byte_scale, high_byte)?)?,
    )?)?;
    builder.append_conditional_constrain_eq(location, conditional, value, reconstructed)
}

/// Translation for `MemoryOffsetGetBits`.
///
/// The row is `(input, lowest_bit, second_lowest_bit)`.
fn add_memory_offset_get_bits_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (input, lowest, second) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    let location = builder.current_location();

    builder.append_conditional_range_constraint(conditional, input, 16)?;
    builder.append_conditional_boolean_constraint(conditional, lowest)?;
    builder.append_conditional_boolean_constraint(conditional, second)?;
    builder.append_conditional_constrain_eq(
        location,
        conditional,
        lowest,
        builder.append_lowest_bits_felt(input, 1)?,
    )?;
    builder.append_conditional_constrain_eq(
        location,
        conditional,
        second,
        builder.append_shifted_low_bits(input, 1, 1)?,
    )
}

/// Translation for `JumpCleanupOffset` lookup.
///
/// Table generation: [`prover::cs::tables::jump_opcode_related::create_jump_cleanup_offset_table`]
///
/// Table intent: decompose a low PC limb into aligned and bit components used
/// when cleaning up jump targets.
///
/// Extraction strategy: keep the arithmetic decomposition (`a = cleaned + 2*bit_1 + bit_0`)
/// and alignment relation (`cleaned = 4*k`) with appropriate bit/range guards.
fn add_jump_cleanup_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (a, bit_1, cleaned) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;

    let bit_0 = builder.new_nondet_felt()?;
    let k = builder.new_nondet_felt()?;

    builder.append_conditional_range_constraint(conditional, a, 16)?;
    builder.append_conditional_range_constraint(conditional, cleaned, 16)?;
    builder.append_conditional_boolean_constraint(conditional, bit_0)?;
    builder.append_conditional_boolean_constraint(conditional, bit_1)?;
    builder.append_conditional_range_constraint(conditional, k, 14)?;

    // a = cleaned + 2*bit_1 + bit_0
    //      2*bit_1
    let bit_1_mul = builder.append_op_with_result(felt::mul(
        builder.current_location(),
        builder.get_constant_from_start(builder.felt_type(), 2)?,
        bit_1,
    )?)?;
    //      2*bit_1 + bit_0
    let twit =
        builder.append_op_with_result(felt::add(builder.current_location(), bit_1_mul, bit_0)?)?;
    //      cleaned + 2*bit_1 + bit_0
    let a_computed =
        builder.append_op_with_result(felt::add(builder.current_location(), cleaned, twit)?)?;
    builder.append_conditional_constrain_eq(
        builder.current_location(),
        conditional,
        a,
        a_computed,
    )?;

    // cleaned = 4*k
    builder.append_conditional_constrain_eq(
        builder.current_location(),
        conditional,
        cleaned,
        builder.append_op_with_result(felt::mul(
            builder.current_location(),
            builder.get_constant_from_start(builder.felt_type(), 4)?,
            k,
        )?)?,
    )
}

/// Translation for `ConditionalJmpBranchSlt` lookup.
///
/// Table generation:
/// [`prover::cs::tables::branch_opcode_related::create_conditional_jmp_branch_slt_family_resolution_table`]
///
/// Table intent: resolve branch/SLT condition flags from packed condition inputs.
///
/// Extraction strategy: preserve the full logical/arithmetic encoding because the
/// table captures control-sensitive semantics that are not represented by a simple
/// determinism summary.
fn add_conditional_jmp_branch_slt_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (a, f3, flag) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;

    let uf = builder.new_nondet_felt()?;
    let out_is_zero = builder.new_nondet_felt()?;
    let sign1 = builder.new_nondet_felt()?;
    let sign2 = builder.new_nondet_felt()?;

    builder.append_conditional_range_constraint(conditional, a, 4)?; // a < 16
    builder.append_conditional_range_constraint(conditional, f3, 3)?; // f3 < 8
    builder.append_conditional_boolean_constraint(conditional, uf)?;
    builder.append_conditional_boolean_constraint(conditional, out_is_zero)?;
    builder.append_conditional_boolean_constraint(conditional, sign1)?;
    builder.append_conditional_boolean_constraint(conditional, sign2)?;
    builder.append_conditional_boolean_constraint(conditional, flag)?;

    // a = uf + 2*out_is_zero + 4*sign1 + 8*sign2
    builder.append_conditional_constrain_eq(
        builder.current_location(),
        conditional,
        a,
        builder.append_sum(
            builder.current_location(),
            &[
                uf,
                builder.append_const_scaling_here(2, out_is_zero)?,
                builder.append_const_scaling_here(4, sign1)?,
                builder.append_const_scaling_here(8, sign2)?,
            ],
        )?,
    )?;

    // signs_different = sign1 + sign2 - (2 * sign1 * sign2)
    let signs_different = builder.append_sum(
        builder.current_location(),
        &[
            sign1,
            sign2,
            builder.append_op_with_result(felt::neg(
                builder.current_location(),
                builder.append_product(
                    builder.current_location(),
                    &[builder.get_felt_constant_from_start(2)?, sign1, sign2],
                )?,
            )?)?,
        ],
    )?;
    let unsigned_lt = uf;
    // signed_lt = (sign1 * signs_different) + unsigned_lt * (1 - signs_different);
    let signed_lt = builder.append_op_with_result(felt::add(
        builder.current_location(),
        builder.append_product_here(&[sign1, signs_different])?,
        builder.append_product(
            builder.current_location(),
            &[
                unsigned_lt,
                builder.append_op_with_result(felt::sub(
                    builder.current_location(),
                    builder.get_felt_constant_from_start(1)?,
                    signs_different,
                )?)?,
            ],
        )?,
    )?)?;
    let eq = out_is_zero;

    // one-hot for funct3
    let f3_one_hot = builder.append_one_hot_here(8)?;
    let f3_reconstructed = builder.append_one_hot_reconstruction_here(&f3_one_hot)?;
    builder.append_conditional_constrain_eq(
        builder.current_location(),
        conditional,
        f3,
        f3_reconstructed,
    )?;

    // expected_flag =
    //       f3_one_hot[0] * eq
    //     + f3_one_hot[1] * (1 - eq)
    //     + f3_one_hot[2] * signed_lt
    //     + f3_one_hot[3] * unsigned_lt
    //     + f3_one_hot[4] * signed_lt
    //     + f3_one_hot[5] * (1 - signed_lt)
    //     + f3_one_hot[6] * unsigned_lt
    //     + f3_one_hot[7] * (1 - unsigned_lt);

    let one_minus = |v| -> Result<Value<'ctx, 'sco>> {
        builder.append_op_with_result(felt::sub(
            builder.current_location(),
            builder.get_felt_constant_from_start(1)?,
            v,
        )?)
    };

    let expected_flag = builder.append_sum(
        builder.current_location(),
        &[
            builder.append_product_here(&[f3_one_hot[0], eq])?,
            builder.append_product_here(&[f3_one_hot[1], one_minus(eq)?])?,
            builder.append_product_here(&[f3_one_hot[2], signed_lt])?,
            builder.append_product_here(&[f3_one_hot[3], unsigned_lt])?,
            builder.append_product_here(&[f3_one_hot[4], signed_lt])?,
            builder.append_product(
                builder.current_location(),
                &[f3_one_hot[5], one_minus(signed_lt)?],
            )?,
            builder.append_product_here(&[f3_one_hot[6], unsigned_lt])?,
            builder.append_product(
                builder.current_location(),
                &[f3_one_hot[7], one_minus(unsigned_lt)?],
            )?,
        ],
    )?;
    // flag === expected_flag
    builder.append_conditional_constrain_eq(
        builder.current_location(),
        conditional,
        flag,
        expected_flag,
    )?;
    Ok(())
}

/// Translation for `MemoryGetOffsetAndMaskWithTrap` lookup.
///
/// Table intent: map packed memory access metadata to offset and trap/mask bits.
///
/// TODO:
/// Extraction strategy: use a compact summary with input/output range bounds and a
/// determinism axiom `det(input) => (det(offset) && det(bitmask))`.
fn add_memory_get_offset_and_mask_with_trap_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (input, offset, bitmask) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;

    builder.append_conditional_range_constraint(conditional, input, 21)?;
    builder.append_conditional_range_constraint(conditional, offset, 4)?;
    builder.append_conditional_range_constraint(conditional, bitmask, 8)?;

    // TODO: No way to encode this in LLZK
    // det(input) => (det(offset) && det(bitmask))
    // let det_input = PicusConstraint::new_det(input);
    // let det_offset = PicusConstraint::new_det(offset);
    // let det_bitmask = PicusConstraint::new_det(bitmask);
    // module.constraints.push(PicusConstraint::Implies(
    // Box::new(det_input),
    // Box::new(PicusConstraint::And(
    // Box::new(det_offset),
    // Box::new(det_bitmask),
    // )),
    // ));
    Ok(())
}

/// Translation for the byte-wise `Xor`/`Or`/`And` lookup tables.
fn add_bitwise_byte_lookup_constraints<'ctx, 'sco, F: FieldInfo, FN>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
    width: usize,
    op: FN,
) -> Result<()>
where
    FN: Copy
        + Fn(
            melior::ir::Location<'ctx>,
            Value<'ctx, 'sco>,
            Value<'ctx, 'sco>,
        ) -> Result<melior::ir::Operation<'ctx>, llzk::error::Error>,
{
    let (lhs, rhs, out) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    let location = builder.current_location();

    builder.append_conditional_range_constraint(conditional, lhs, width)?;
    builder.append_conditional_range_constraint(conditional, rhs, width)?;
    builder.append_conditional_range_constraint(conditional, out, width)?;
    let expected = builder.append_op_with_result(op(location, lhs, rhs)?)?;
    builder.append_conditional_constrain_eq(location, conditional, out, expected)
}

/// Translation for `RomAddressSpaceSeparator` lookup.
///
/// Table intent: split a high address limb into `(is_ram_range, rom_chunk)`.
///
/// Extraction strategy: keep explicit decomposition constraints linking
/// `address_high`, `rom_chunk`, and `is_ram_range`.
fn add_rom_address_space_separator_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (address_high, is_ram_range, rom_chunk) =
        constrain_lookup_row3(builder, vars, query, row_multiplier)?;

    let rom_bound = 1u64 << common_constants::ROM_SECOND_WORD_BITS;

    let q_tail = builder.new_nondet_felt()?;
    let q = builder.new_nondet_felt()?;

    builder.append_conditional_range_constraint(conditional, address_high, 16)?;
    builder.append_conditional_boolean_constraint(conditional, is_ram_range)?;
    builder.append_conditional_range_constraint(
        conditional,
        rom_chunk,
        common_constants::ROM_SECOND_WORD_BITS,
    )?;
    builder.append_conditional_range_constraint(
        conditional,
        q_tail,
        16 - common_constants::ROM_SECOND_WORD_BITS,
    )?;
    builder.append_conditional_range_constraint(
        conditional,
        q_tail,
        16 - common_constants::ROM_SECOND_WORD_BITS,
    )?;

    let location = builder.current_location();
    // Address decomposition by ROM chunk size.
    // address_high = rom_chunk + (rom_bound * q)
    builder.append_conditional_constrain_eq(
        location,
        conditional,
        address_high,
        builder.append_sum(
            location,
            &[
                rom_chunk,
                builder.append_product(
                    location,
                    &[builder.get_felt_constant_from_start(rom_bound)?, q],
                )?,
            ],
        )?,
    )?;
    // Link is_ram_range to q != 0 by construction:
    // q = is_ram_range * (q_tail + 1).
    builder.append_conditional_constrain_eq(
        location,
        conditional,
        q,
        builder.append_product(
            location,
            &[
                is_ram_range,
                builder.append_sum(
                    location,
                    &[builder.get_felt_constant_from_start(1)?, q_tail],
                )?,
            ],
        )?,
    )?;
    Ok(())
}

/// Translation for `RomRead`.
///
/// The exact ROM contents stay external to the emitted circuit family, but the table still
/// enforces that the address is in-bounds and word-aligned and that the returned limbs are 16-bit
/// values.
fn add_rom_read_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (byte_address, low, high) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    let word_index = builder.new_nondet_felt()?;
    let location = builder.current_location();

    builder.append_conditional_range_constraint(
        conditional,
        byte_address,
        16 + common_constants::ROM_SECOND_WORD_BITS,
    )?;
    builder.append_conditional_range_constraint(
        conditional,
        word_index,
        16 + common_constants::ROM_SECOND_WORD_BITS - 2,
    )?;
    builder.append_conditional_range_constraint(conditional, low, 16)?;
    builder.append_conditional_range_constraint(conditional, high, 16)?;

    let aligned_address = builder.append_product(
        location,
        &[builder.get_felt_constant_from_start(4)?, word_index],
    )?;
    builder.append_conditional_constrain_eq(location, conditional, byte_address, aligned_address)
}

/// Translation for `RangeCheck16WithZeroPads`.
fn add_range_check_16_with_zero_pads_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (value, zero_0, zero_1) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    let zero = builder.get_felt_constant_from_start(0)?;
    let location = builder.current_location();

    builder.append_conditional_range_constraint(conditional, value, 16)?;
    builder.append_conditional_constrain_eq(location, conditional, zero_0, zero)?;
    builder.append_conditional_constrain_eq(location, conditional, zero_1, zero)
}

/// Translation for `SpecialCSRProperties`.
///
/// The supported/delegating CSR indices are recovered from the circuit's table driver.
fn add_special_csr_properties_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let metadata = vars.special_csr_properties().ok_or_else(|| {
        anyhow::anyhow!("missing SpecialCSRProperties metadata for LLZK lookup lowering")
    })?;

    let (csr_index, is_supported, is_for_delegation) =
        constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    let location = builder.current_location();

    builder.append_conditional_range_constraint(conditional, csr_index, 12)?;
    builder.append_conditional_boolean_constraint(conditional, is_supported)?;
    builder.append_conditional_boolean_constraint(conditional, is_for_delegation)?;

    let (expected_is_supported, expected_is_for_delegation) =
        builder.append_special_csr_properties_outputs(csr_index, metadata)?;

    builder.append_conditional_constrain_eq(
        location,
        conditional,
        is_for_delegation,
        expected_is_for_delegation,
    )?;
    builder.append_conditional_constrain_eq(
        location,
        conditional,
        is_supported,
        expected_is_supported,
    )
}

/// Translation for `MemoryLoadHalfwordOrByte` lookup.
///
/// Table intent: compute the `(low, high)` loaded value limbs for subword loads.
///
/// TODO:
/// Extraction strategy: summarize with range bounds and determinism
/// `det(input) => (det(out_low) && det(out_high))`.
fn add_memory_load_halfword_or_byte_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (input, out_low, out_high) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;

    builder.append_conditional_range_constraint(conditional, input, 16 + 2 + 3)?;
    builder.append_conditional_range_constraint(conditional, out_low, 16)?;
    builder.append_conditional_range_constraint(conditional, out_high, 16)?;

    // TODO: Port to LLZK
    // let det_input = PicusConstraint::new_det(input);
    // let det_out_low = PicusConstraint::new_det(out_low);
    // let det_out_high = PicusConstraint::new_det(out_high);
    // module.constraints.push(PicusConstraint::Implies(
    //     Box::new(det_input),
    //     Box::new(PicusConstraint::And(
    //         Box::new(det_out_low),
    //         Box::new(det_out_high),
    //     )),
    // ));
    Ok(())
}

/// Lower the width-only quick-decoder decomposition tables.
///
/// These tables do not model an interesting functional relation; they only certify that each
/// tuple entry fits within a fixed bit width. A const-generic helper keeps the `4x4x4` and
/// `7x3x6` cases aligned while still making the call sites explicit about the expected widths.
fn add_quick_decode_decomposition_lookup_constraints<
    'ctx,
    'sco,
    F: FieldInfo,
    const A: usize,
    const B: usize,
    const C: usize,
>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let [a, b, c] = lookup_inputs(builder, vars, query, row_multiplier)?;
    builder.append_conditional_range_constraint(conditional, a, A)?;
    builder.append_conditional_range_constraint(conditional, b, B)?;
    builder.append_conditional_range_constraint(conditional, c, C)?;
    Ok(())
}

/// `OpTypeBitmask` is summarized the same way as in `picus_translation`: range bounds only.
///
/// The exact table relation is very large. The logical backend keeps the decoder bitmask table
/// conservative and relies on the surrounding boolean decompositions for the fine-grained logic.
fn add_op_type_bitmask_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let [packed_opcode, first_chunk, second_chunk] =
        lookup_inputs(builder, vars, query, row_multiplier)?;
    builder.append_conditional_range_constraint(conditional, packed_opcode, 17)?;
    builder.append_conditional_range_constraint(conditional, first_chunk, 30)?;
    builder.append_conditional_range_constraint(conditional, second_chunk, 30)?;
    Ok(())
}

fn lookup_inputs<'ctx, 'sco, F: FieldInfo, const N: usize>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
) -> Result<[Value<'ctx, 'sco>; N]> {
    query
        .row
        .iter()
        .map(|input| {
            apply_row_multiplier(
                builder,
                row_multiplier,
                input.emit_constrain(builder, vars)?,
            )
        })
        .collect::<Result<Vec<_>>>()?
        .try_into()
        .map_err(|actual: Vec<_>| {
            anyhow::anyhow!("expected {N} lookup inputs, found {}", actual.len())
        })
}

/// Translation for `ExtendLoadedValue`.
fn add_extend_loaded_value_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (input, out_low, out_high) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    let location = builder.current_location();
    let (expected_low, expected_high) = builder.append_extend_loaded_value_outputs(input)?;

    builder.append_conditional_range_constraint(conditional, input, 20)?;
    builder.append_conditional_range_constraint(conditional, out_low, 16)?;
    builder.append_conditional_range_constraint(conditional, out_high, 16)?;
    builder.append_conditional_constrain_eq(location, conditional, out_low, expected_low)?;
    builder.append_conditional_constrain_eq(location, conditional, out_high, expected_high)
}

/// Translation for `StoreByteSourceContribution`.
fn add_store_byte_source_contribution_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (byte, bit_0, out) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    let location = builder.current_location();

    builder.append_conditional_range_constraint(conditional, byte, 8)?;
    builder.append_conditional_boolean_constraint(conditional, bit_0)?;
    builder.append_conditional_range_constraint(conditional, out, 16)?;
    builder.append_conditional_constrain_eq(
        location,
        conditional,
        out,
        builder.append_store_byte_source_contribution_output(byte, bit_0)?,
    )
}

/// Translation for `StoreByteExistingContribution`.
fn add_store_byte_existing_contribution_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (word, bit_0, out) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    let location = builder.current_location();

    builder.append_conditional_range_constraint(conditional, word, 16)?;
    builder.append_conditional_boolean_constraint(conditional, bit_0)?;
    builder.append_conditional_range_constraint(conditional, out, 16)?;
    builder.append_conditional_constrain_eq(
        location,
        conditional,
        out,
        builder.append_store_byte_existing_contribution_output(word, bit_0)?,
    )
}

/// Translation for `MemStoreClearOriginalRamValueLimb` lookup.
///
/// Table intent: clear the relevant bytes in the original RAM limb before merge.
///
/// TODO:
/// Extraction strategy: summarize with range bounds and determinism
/// `det(input) => (det(cleaned) && det(unused))`.
fn add_mem_store_clear_original_ram_value_limb_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (input, cleaned, unused) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;

    builder.append_conditional_range_constraint(conditional, input, 16 + 2 + 3)?;
    builder.append_conditional_range_constraint(conditional, cleaned, 16)?;
    builder.append_conditional_range_constraint(conditional, unused, 16)?;

    // det(input) => (det(cleaned) && det(unused))
    // let det_input = PicusConstraint::new_det(input);
    // let det_cleaned = PicusConstraint::new_det(cleaned);
    // let det_unused = PicusConstraint::new_det(unused);
    // module.constraints.push(PicusConstraint::Implies(
    //     Box::new(det_input),
    //     Box::new(PicusConstraint::And(
    //         Box::new(det_cleaned),
    //         Box::new(det_unused),
    //     )),
    // ));
    Ok(())
}

/// Translation for `MemStoreClearWrittenValueLimb` lookup.
///
/// Table intent: normalize/position the written value limb before merging into RAM.
///
/// TODO:
/// Extraction strategy: summarize with range bounds and determinism
/// `det(input) => (det(cleaned) && det(unused))`.
fn add_mem_store_clear_written_value_limb_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (input, cleaned, unused) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;

    builder.append_conditional_range_constraint(conditional, input, 16 + 2 + 3)?;
    builder.append_conditional_range_constraint(conditional, cleaned, 16)?;
    builder.append_conditional_range_constraint(conditional, unused, 16)?;

    // det(input) => (det(cleaned) && det(unused))
    // let det_input = PicusConstraint::new_det(input);
    // let det_cleaned = PicusConstraint::new_det(cleaned);
    // let det_unused = PicusConstraint::new_det(unused);
    // module.constraints.push(PicusConstraint::Implies(
    //     Box::new(det_input),
    //     Box::new(PicusConstraint::And(
    //         Box::new(det_cleaned),
    //         Box::new(det_unused),
    //     )),
    // ));
    Ok(())
}

/// Translation for `AlignedRomRead` lookup.
///
/// Table intent: map ROM word index to low/high 16-bit instruction limbs.
///
/// TODO:
/// Extraction strategy: bound index/output ranges and enforce determinism
/// `det(word_index) => (det(low) && det(high))`.
fn add_aligned_rom_read_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (word_index, low, high) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;

    // Aligned ROM table is keyed by word index in [0, 2^(16 + ROM_SECOND_WORD_BITS - 2)).
    builder.append_conditional_range_constraint(
        conditional,
        word_index,
        16 + common_constants::ROM_SECOND_WORD_BITS - 2,
    )?;
    builder.append_conditional_range_constraint(conditional, low, 16)?;
    builder.append_conditional_range_constraint(conditional, high, 16)?;

    // det(word_index) => (det(low) && det(high))
    // let det_word_index = PicusConstraint::new_det(word_index);
    // let det_low = PicusConstraint::new_det(low);
    // let det_high = PicusConstraint::new_det(high);
    // module.constraints.push(PicusConstraint::Implies(
    //     Box::new(det_word_index),
    //     Box::new(PicusConstraint::And(Box::new(det_low), Box::new(det_high))),
    // ));

    // NOTE: exact (word_index -> low/high) value linkage still requires
    // embedding the concrete ROM table contents.
    Ok(())
}

/// Translation for `TruncateShiftAmount`.
///
/// The table row is `(input, truncated_shift, 0)`, where `truncated_shift = input & 0b1_1111`.
fn add_truncate_shift_amount_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (input, truncated, zero_pad) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    let quotient = builder.new_nondet_felt()?;
    let location = builder.current_location();

    builder.append_conditional_range_constraint(conditional, input, 16)?;
    builder.append_conditional_range_constraint(conditional, truncated, 5)?;
    builder.append_conditional_range_constraint(conditional, quotient, 11)?;
    builder.append_conditional_constrain_eq(
        location,
        conditional,
        zero_pad,
        builder.get_felt_constant_from_start(0)?,
    )?;

    let reconstructed = builder.append_sum(
        location,
        &[
            truncated,
            builder.append_product(
                location,
                &[builder.get_felt_constant_from_start(1 << 5)?, quotient],
            )?,
        ],
    )?;
    builder.append_conditional_constrain_eq(location, conditional, input, reconstructed)
}

/// Translation for `ShiftImplementation`.
fn add_shift_implementation_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (input, in_place, overflow) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    let location = builder.current_location();
    let (expected_in_place, expected_overflow) =
        builder.append_shift_implementation_outputs(input)?;

    builder.append_conditional_range_constraint(conditional, input, 22)?;
    builder.append_conditional_range_constraint(conditional, in_place, 16)?;
    builder.append_conditional_range_constraint(conditional, overflow, 16)?;
    builder.append_conditional_constrain_eq(location, conditional, in_place, expected_in_place)?;
    builder.append_conditional_constrain_eq(location, conditional, overflow, expected_overflow)
}

/// Translation for `SRASignFiller`.
fn add_sra_sign_filler_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (input, low, high) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    let location = builder.current_location();
    let (expected_low, expected_high) = builder.append_sra_sign_filler_outputs(input)?;

    builder.append_conditional_range_constraint(conditional, input, 7)?;
    builder.append_conditional_range_constraint(conditional, low, 16)?;
    builder.append_conditional_range_constraint(conditional, high, 16)?;
    builder.append_conditional_constrain_eq(location, conditional, low, expected_low)?;
    builder.append_conditional_constrain_eq(location, conditional, high, expected_high)
}

/// Translation for `ConditionalOpAllConditionsResolver`.
fn add_conditional_op_all_conditions_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (input, should_branch, should_store) =
        constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    let location = builder.current_location();
    let (expected_branch, expected_store) =
        builder.append_conditional_op_all_conditions_outputs(input)?;

    builder.append_conditional_range_constraint(conditional, input, 7)?;
    builder.append_conditional_boolean_constraint(conditional, should_branch)?;
    builder.append_conditional_boolean_constraint(conditional, should_store)?;
    builder.append_conditional_constrain_eq(
        location,
        conditional,
        should_branch,
        expected_branch,
    )?;
    builder.append_conditional_constrain_eq(location, conditional, should_store, expected_store)
}

/// Translation for the generic 16-bit logical shift tables.
fn add_logical_shift_16_bit_lookup_constraints<
    'ctx,
    'sco,
    F: FieldInfo,
    const INPUT_IS_HIGH: bool,
    const IS_RIGHT_SHIFT: bool,
>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (input, low, high) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    let location = builder.current_location();
    let (expected_low, expected_high) =
        builder.append_logical_shift_16_bit_outputs::<INPUT_IS_HIGH, IS_RIGHT_SHIFT>(input)?;

    builder.append_conditional_range_constraint(conditional, input, 21)?;
    builder.append_conditional_range_constraint(conditional, low, 16)?;
    builder.append_conditional_range_constraint(conditional, high, 16)?;
    builder.append_conditional_constrain_eq(location, conditional, low, expected_low)?;
    builder.append_conditional_constrain_eq(location, conditional, high, expected_high)
}

/// Translation for `Sra16BitInputSignFill`.
fn add_sra_16_bit_input_sign_fill_lookup_constraints<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    query: &LookupQuery<F>,
    row_multiplier: Option<Value<'ctx, 'sco>>,
    conditional: Option<Value<'ctx, 'sco>>,
) -> Result<()> {
    let (input, low, high) = constrain_lookup_row3(builder, vars, query, row_multiplier)?;
    let location = builder.current_location();
    let (expected_low, expected_high) = builder.append_sra_16_bit_input_sign_fill_outputs(input)?;

    builder.append_conditional_range_constraint(conditional, input, 21)?;
    builder.append_conditional_range_constraint(conditional, low, 16)?;
    builder.append_conditional_range_constraint(conditional, high, 16)?;
    builder.append_conditional_constrain_eq(location, conditional, low, expected_low)?;
    builder.append_conditional_constrain_eq(location, conditional, high, expected_high)
}

#[cfg(test)]
mod tests {
    use prover::cs::cs::circuit::DisjunctiveLookupCase;
    use prover::cs::cs::circuit::LookupQueryTableType;
    use prover::cs::definitions::Variable;
    use prover::cs::one_row_compiler::LookupInput;
    use prover::cs::types::Boolean;
    use prover::field::Mersenne31Field;

    use super::*;
    use crate::codegen::SpecialCsrPropertiesMetadata;
    use crate::test_helpers::assert_full_ir_eq;
    use crate::test_helpers::emit_test_constrain_ir;
    use crate::test_helpers::emit_test_constrain_ir_with_special_csr_properties;
    use crate::test_helpers::maybe_dump_test_ir;

    /// Create a [`LookupQuery`] for the given `row` in the given `table`.
    fn direct_lookup_query(table: TableType, row: [Variable; 3]) -> LookupQuery<Mersenne31Field> {
        LookupQuery {
            row: row.map(LookupInput::from),
            table: LookupQueryTableType::Constant(table),
        }
    }

    /// Create a [`LookupQuery`] with a variable table id for the given `row`.
    fn dynamic_lookup_query(
        table_id: Variable,
        row: [Variable; 3],
    ) -> LookupQuery<Mersenne31Field> {
        LookupQuery {
            row: row.map(LookupInput::from),
            table: LookupQueryTableType::Variable(table_id),
        }
    }

    /// Generate an exact-fixture test for a direct constant-table lookup.
    ///
    /// Each generated test uses the standard three-column synthetic row and checks the emitted
    /// `@constrain` IR against the provided fixture.
    macro_rules! direct_lookup_fixture_test {
        ($test_name:ident, $table:ident, $fixture:literal) => {
            #[test]
            fn $test_name() {
                let row = [Variable(7), Variable(8), Variable(9)];
                let table = TableType::$table;
                let query = direct_lookup_query(table, row);
                let ir = emit_test_constrain_ir("lookup_test", &row, &[], |ops, vars| {
                    add_lookup_constraints_for_table(ops, vars, &query, table, None, None)
                });
                maybe_dump_test_ir(stringify!($test_name), &ir);
                assert_full_ir_eq(&ir, include_str!($fixture));
            }
        };
    }

    /// Generate an exact-fixture test for a one-case disjunctive lookup relation.
    ///
    /// Each generated test uses one boolean guard plus a three-column row and verifies the full
    /// guarded lookup encoding against the provided fixture.
    macro_rules! disjunctive_lookup_fixture_test {
        ($test_name:ident, $table:ident, $fixture:literal) => {
            #[test]
            fn $test_name() {
                let flag = Variable(7);
                let row = [Variable(8), Variable(9), Variable(10)];
                let relation = DisjunctiveLookup {
                    relation_index: 0,
                    cases: vec![DisjunctiveLookupCase {
                        flag: Boolean::Is(flag),
                        row: row.map(LookupInput::from),
                        table: TableType::$table.to_num(),
                        guard: None,
                    }],
                };
                let ir = emit_test_constrain_ir(
                    "lookup_test",
                    &[flag, row[0], row[1], row[2]],
                    &[],
                    |ops, vars| add_disjunctive_lookup_constraints(ops, vars, &relation),
                );
                maybe_dump_test_ir(stringify!($test_name), &ir);
                assert_full_ir_eq(&ir, include_str!($fixture));
            }
        };
    }

    /// Generate an exact-fixture test for the dynamic bitwise-table dispatch path.
    ///
    /// The table id is exposed as an explicit felt input so the test exercises the same
    /// `LookupQueryTableType::Variable(...)` lowering that `shift_binary_csr` uses.
    macro_rules! dynamic_lookup_fixture_test {
        ($test_name:ident, $fixture:literal) => {
            #[test]
            fn $test_name() {
                let table_id = Variable(7);
                let row = [Variable(8), Variable(9), Variable(10)];
                let query = dynamic_lookup_query(table_id, row);
                let ir = emit_test_constrain_ir(
                    "lookup_test",
                    &[table_id, row[0], row[1], row[2]],
                    &[],
                    |ops, vars| query.emit_constrain(ops, vars),
                );
                maybe_dump_test_ir(stringify!($test_name), &ir);
                assert_full_ir_eq(&ir, include_str!($fixture));
            }
        };
    }

    dynamic_lookup_fixture_test!(
        dynamic_lookup_dispatches_bitwise_tables,
        "../testdata/lookups/dynamic_lookup_dispatches_bitwise_tables.mlir"
    );
    direct_lookup_fixture_test!(
        extend_loaded_value_lookup_emits_extension_logic,
        ExtendLoadedValue,
        "../testdata/lookups/extend_loaded_value_lookup_emits_extension_logic.mlir"
    );
    direct_lookup_fixture_test!(
        store_byte_source_contribution_lookup_shifts_selected_byte,
        StoreByteSourceContribution,
        "../testdata/lookups/store_byte_source_contribution_lookup_shifts_selected_byte.mlir"
    );
    direct_lookup_fixture_test!(
        store_byte_existing_contribution_lookup_masks_selected_half,
        StoreByteExistingContribution,
        "../testdata/lookups/store_byte_existing_contribution_lookup_masks_selected_half.mlir"
    );
    direct_lookup_fixture_test!(
        truncate_shift_amount_lookup_reconstructs_input,
        TruncateShiftAmount,
        "../testdata/lookups/truncate_shift_amount_lookup_reconstructs_input.mlir"
    );
    direct_lookup_fixture_test!(
        shift_implementation_lookup_splits_shifted_result,
        ShiftImplementation,
        "../testdata/lookups/shift_implementation_lookup_splits_shifted_result.mlir"
    );
    direct_lookup_fixture_test!(
        sra_sign_filler_lookup_emits_sign_mask,
        SRASignFiller,
        "../testdata/lookups/sra_sign_filler_lookup_emits_sign_mask.mlir"
    );
    direct_lookup_fixture_test!(
        conditional_op_all_conditions_lookup_resolves_branch_and_store,
        ConditionalOpAllConditionsResolver,
        "../testdata/lookups/conditional_op_all_conditions_lookup_resolves_branch_and_store.mlir"
    );
    direct_lookup_fixture_test!(
        logical_shift_low_lookup_emits_shifted_limbs,
        SllWith16BitInputLow,
        "../testdata/lookups/logical_shift_low_lookup_emits_shifted_limbs.mlir"
    );
    direct_lookup_fixture_test!(
        sra_16_bit_input_sign_fill_lookup_emits_sign_mask,
        Sra16BitInputSignFill,
        "../testdata/lookups/sra_16_bit_input_sign_fill_lookup_emits_sign_mask.mlir"
    );
    direct_lookup_fixture_test!(
        jump_cleanup_lookup_emits_alignment_constraints,
        JumpCleanupOffset,
        "../testdata/lookups/jump_cleanup_lookup_emits_alignment_constraints.mlir"
    );
    direct_lookup_fixture_test!(
        conditional_jump_lookup_emits_one_hot_logic,
        ConditionalJmpBranchSlt,
        "../testdata/lookups/conditional_jump_lookup_emits_one_hot_logic.mlir"
    );
    direct_lookup_fixture_test!(
        memory_get_offset_and_mask_lookup_is_range_only,
        MemoryGetOffsetAndMaskWithTrap,
        "../testdata/lookups/memory_get_offset_and_mask_lookup_is_range_only.mlir"
    );
    direct_lookup_fixture_test!(
        rom_address_space_separator_lookup_emits_rom_bound_relation,
        RomAddressSpaceSeparator,
        "../testdata/lookups/rom_address_space_separator_lookup_emits_rom_bound_relation.mlir"
    );
    direct_lookup_fixture_test!(
        memory_load_halfword_or_byte_lookup_is_range_only,
        MemoryLoadHalfwordOrByte,
        "../testdata/lookups/memory_load_halfword_or_byte_lookup_is_range_only.mlir"
    );
    direct_lookup_fixture_test!(
        mem_store_clear_original_lookup_is_range_only,
        MemStoreClearOriginalRamValueLimb,
        "../testdata/lookups/mem_store_clear_original_lookup_is_range_only.mlir"
    );
    direct_lookup_fixture_test!(
        mem_store_clear_written_lookup_is_range_only,
        MemStoreClearWrittenValueLimb,
        "../testdata/lookups/mem_store_clear_written_lookup_is_range_only.mlir"
    );
    direct_lookup_fixture_test!(
        aligned_rom_read_lookup_is_range_only,
        AlignedRomRead,
        "../testdata/lookups/aligned_rom_read_lookup_is_range_only.mlir"
    );

    disjunctive_lookup_fixture_test!(
        disjunctive_lookup_uses_row_multiplier_for_safe_tables,
        MemoryLoadHalfwordOrByte,
        "../testdata/lookups/disjunctive_lookup_uses_row_multiplier_for_safe_tables.mlir"
    );
    disjunctive_lookup_fixture_test!(
        disjunctive_lookup_uses_conditional_constraints_for_unsafe_tables,
        JumpCleanupOffset,
        "../testdata/lookups/disjunctive_lookup_uses_conditional_constraints_for_unsafe_tables.mlir"
    );

    #[test]
    fn special_csr_properties_lookup_uses_metadata() {
        let row = [Variable(7), Variable(8), Variable(9)];
        let table = TableType::SpecialCSRProperties;
        let query = direct_lookup_query(table, row);
        let metadata = Some(SpecialCsrPropertiesMetadata {
            supported_only_indices: vec![5, 7],
            delegation_indices: vec![9],
        });
        let ir = emit_test_constrain_ir_with_special_csr_properties(
            "lookup_test",
            &row,
            &[],
            metadata,
            |ops, vars| add_lookup_constraints_for_table(ops, vars, &query, table, None, None),
        );
        maybe_dump_test_ir("special_csr_properties_lookup_uses_metadata", &ir);
        assert_full_ir_eq(
            &ir,
            include_str!("../testdata/lookups/special_csr_properties_lookup_uses_metadata.mlir"),
        );
    }
}
