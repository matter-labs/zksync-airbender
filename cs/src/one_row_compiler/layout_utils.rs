use super::*;
use crate::cs::placeholder::Placeholder;
use crate::one_row_compiler::compile_layout::*;
use std::collections::HashMap;

#[inline(always)]
pub fn read_value<T: Sized + Copy>(place: ColumnAddress, witness_row: &[T], memory_row: &[T]) -> T {
    unsafe {
        match place {
            ColumnAddress::WitnessSubtree(offset) => {
                debug_assert!(
                    offset < witness_row.len(),
                    "witness row contains {} elements, but index is {}",
                    witness_row.len(),
                    offset
                );
                witness_row.as_ptr().add(offset).read()
            }
            ColumnAddress::MemorySubtree(offset) => {
                debug_assert!(
                    offset < memory_row.len(),
                    "memory row contains {} elements, but index is {}",
                    memory_row.len(),
                    offset
                );
                memory_row.as_ptr().add(offset).read()
            }
            _ => unreachable!("can only read from witness or memory tree here"),
        }
    }
}

#[inline(always)]
pub fn read_value_ext<T: Sized + Copy>(
    place: ColumnAddress,
    witness_row: &[T],
    memory_row: &[T],
    scratch_space: &[T],
) -> T {
    unsafe {
        match place {
            ColumnAddress::WitnessSubtree(offset) => {
                debug_assert!(
                    offset < witness_row.len(),
                    "witness row contains {} elements, but index is {}",
                    witness_row.len(),
                    offset
                );
                witness_row.as_ptr().add(offset).read()
            }
            ColumnAddress::MemorySubtree(offset) => {
                debug_assert!(
                    offset < memory_row.len(),
                    "memory row contains {} elements, but index is {}",
                    memory_row.len(),
                    offset
                );
                memory_row.as_ptr().add(offset).read()
            }
            ColumnAddress::OptimizedOut(offset) => {
                debug_assert!(
                    offset < scratch_space.len(),
                    "optimized variables scratch space contains {} elements, but index is {}",
                    scratch_space.len(),
                    offset
                );
                scratch_space.as_ptr().add(offset).read()
            }
            _ => unreachable!("can only read from witness or memory tree here, or scratch space"),
        }
    }
}

#[inline(always)]
pub fn read_value_with_setup_access<T: Sized + Copy>(
    place: ColumnAddress,
    witness_row: &[T],
    memory_row: &[T],
    setup_row: &[T],
) -> T {
    unsafe {
        match place {
            ColumnAddress::WitnessSubtree(offset) => {
                debug_assert!(
                    offset < witness_row.len(),
                    "witness row contains {} elements, but index is {}",
                    witness_row.len(),
                    offset
                );
                witness_row.as_ptr().add(offset).read()
            }
            ColumnAddress::MemorySubtree(offset) => {
                debug_assert!(
                    offset < memory_row.len(),
                    "memory row contains {} elements, but index is {}",
                    memory_row.len(),
                    offset
                );
                memory_row.as_ptr().add(offset).read()
            }
            ColumnAddress::SetupSubtree(offset) => {
                debug_assert!(
                    offset < setup_row.len(),
                    "setup row contains {} elements, but index is {}",
                    setup_row.len(),
                    offset
                );
                setup_row.as_ptr().add(offset).read()
            }
            _ => unreachable!("can only read from witness, memory or setup tree here"),
        }
    }
}

#[inline(always)]
pub fn write_value<T: Sized + Copy>(
    place: ColumnAddress,
    value: T,
    witness_row: &mut [T],
    memory_row: &mut [T],
) {
    unsafe {
        match place {
            ColumnAddress::WitnessSubtree(offset) => {
                debug_assert!(
                    offset < witness_row.len(),
                    "witness row contains {} elements, but index is {}",
                    witness_row.len(),
                    offset
                );
                *witness_row.get_unchecked_mut(offset) = value;
            }
            ColumnAddress::MemorySubtree(offset) => {
                debug_assert!(
                    offset < memory_row.len(),
                    "memory row contains {} elements, but index is {}",
                    memory_row.len(),
                    offset
                );
                *memory_row.get_unchecked_mut(offset) = value;
            }
            _ => unreachable!("can only write into witness or memory tree here"),
        }
    }
}

#[inline(always)]
pub fn write_value_ext<T: Sized + Copy>(
    place: ColumnAddress,
    value: T,
    witness_row: &mut [T],
    memory_row: &mut [T],
    scratch_space: &mut [T],
) {
    unsafe {
        match place {
            ColumnAddress::WitnessSubtree(offset) => {
                debug_assert!(
                    offset < witness_row.len(),
                    "witness row contains {} elements, but index is {}",
                    witness_row.len(),
                    offset
                );
                *witness_row.get_unchecked_mut(offset) = value;
            }
            ColumnAddress::MemorySubtree(offset) => {
                debug_assert!(
                    offset < memory_row.len(),
                    "memory row contains {} elements, but index is {}",
                    memory_row.len(),
                    offset
                );
                *memory_row.get_unchecked_mut(offset) = value;
            }
            ColumnAddress::OptimizedOut(offset) => {
                debug_assert!(
                    offset < scratch_space.len(),
                    "optimized out scratch space contains {} elements, but index is {}",
                    scratch_space.len(),
                    offset
                );
                *scratch_space.get_unchecked_mut(offset) = value;
            }
            _ => unreachable!("can only write into witness or memory tree here, or scratch space"),
        }
    }
}

pub(crate) fn layout_decoder_state_into_memory<F: PrimeField>(
    memory_tree_offset: &mut usize,
    all_variables_to_place: &mut BTreeSet<Variable>,
    layout: &mut BTreeMap<Variable, ColumnAddress>,
    state: &DecoderCircuitMachineState<F>,
) -> (
    MachineStatePermutationVariables,
    IntermediateStatePermutationVariables,
) {
    // in decoder PC/Timestamp are shared
    let pc = layout_memory_subtree_multiple_variables(
        memory_tree_offset,
        state.cycle_start_state.pc,
        all_variables_to_place,
        layout,
    );
    let timestamp = layout_memory_subtree_multiple_variables(
        memory_tree_offset,
        state.cycle_start_state.timestamp,
        all_variables_to_place,
        layout,
    );

    let machine_state = MachineStatePermutationVariables { pc, timestamp };

    // we will need to layout the decoder output, and circuit family would be decoder's output

    let DecoderData {
        rs1_index,
        rs2_index,
        rd_index,
        rd_is_zero,
        imm,
        funct3,
        funct7,
        circuit_family_extra_mask,
        ..
    } = state.decoder_data.decoder_data.clone();

    let rs1_index = layout_memory_subtree_variable(
        memory_tree_offset,
        rs1_index,
        all_variables_to_place,
        layout,
    );
    let rs2_index = layout_memory_subtree_variable(
        memory_tree_offset,
        rs2_index,
        all_variables_to_place,
        layout,
    );
    let rd_index = layout_memory_subtree_variable(
        memory_tree_offset,
        rd_index,
        all_variables_to_place,
        layout,
    );
    let rd_is_zero = layout_memory_subtree_variable(
        memory_tree_offset,
        rd_is_zero,
        all_variables_to_place,
        layout,
    );
    let imm = layout_memory_subtree_multiple_variables(
        memory_tree_offset,
        imm,
        all_variables_to_place,
        layout,
    );
    let funct3 =
        layout_memory_subtree_variable(memory_tree_offset, funct3, all_variables_to_place, layout);
    let funct7 = funct7.expect("must be present in case of not preprocessed decoder");
    let funct7 =
        layout_memory_subtree_variable(memory_tree_offset, funct7, all_variables_to_place, layout);
    let circuit_family_extra_mask = layout_memory_subtree_variable(
        memory_tree_offset,
        circuit_family_extra_mask,
        all_variables_to_place,
        layout,
    );
    let circuit_family = layout_memory_subtree_variable(
        memory_tree_offset,
        state.decoder_data.circuit_family,
        all_variables_to_place,
        layout,
    );

    let intermediate_state = IntermediateStatePermutationVariables {
        execute: ColumnSet::empty(),
        pc,
        timestamp,
        rs1_index,
        rs2_index: ColumnAddress::MemorySubtree(rs2_index.start()),
        rd_index: ColumnAddress::MemorySubtree(rd_index.start()),
        decoder_witness_is_in_memory: true,
        rd_is_zero,
        imm,
        funct3,
        funct7,
        circuit_family,
        circuit_family_extra_mask: ColumnAddress::MemorySubtree(circuit_family_extra_mask.start()),
    };

    (machine_state, intermediate_state)
}

pub(crate) fn layout_executor_state_into_memory<F: PrimeField>(
    memory_tree_offset: &mut usize,
    all_variables_to_place: &mut BTreeSet<Variable>,
    layout: &mut BTreeMap<Variable, ColumnAddress>,
    state: &OpcodeFamilyCircuitState<F>,
) -> (
    MachineStatePermutationVariables,
    IntermediateStatePermutationVariables,
) {
    let execute = layout_memory_subtree_variable(
        memory_tree_offset,
        state.execute,
        all_variables_to_place,
        layout,
    );

    // in decoder PC/Timestamp are NOT shared
    let pc = layout_memory_subtree_multiple_variables(
        memory_tree_offset,
        state.cycle_start_state.pc,
        all_variables_to_place,
        layout,
    );
    let timestamp = layout_memory_subtree_multiple_variables(
        memory_tree_offset,
        state.cycle_start_state.timestamp,
        all_variables_to_place,
        layout,
    );

    let machine_state = MachineStatePermutationVariables { pc, timestamp };

    // we will need to layout the decoder output, and circuit family would be decoder's output

    let DecoderData {
        rs1_index,
        rs2_index,
        rd_index,
        rd_is_zero,
        imm,
        funct3,
        funct7,
        circuit_family_extra_mask,
        ..
    } = state.decoder_data.clone();

    // reallocate for final set
    let pc = layout_memory_subtree_multiple_variables(
        memory_tree_offset,
        state.cycle_end_state.pc,
        all_variables_to_place,
        layout,
    );
    let timestamp = layout_memory_subtree_multiple_variables(
        memory_tree_offset,
        state.cycle_end_state.timestamp,
        all_variables_to_place,
        layout,
    );
    let rs1_index = layout_memory_subtree_variable(
        memory_tree_offset,
        rs1_index,
        all_variables_to_place,
        layout,
    );
    let rs2_index = layout_memory_subtree_variable(
        memory_tree_offset,
        rs2_index,
        all_variables_to_place,
        layout,
    );
    let rd_index = layout_memory_subtree_variable(
        memory_tree_offset,
        rd_index,
        all_variables_to_place,
        layout,
    );
    let rd_is_zero = layout_memory_subtree_variable(
        memory_tree_offset,
        rd_is_zero,
        all_variables_to_place,
        layout,
    );
    let imm = layout_memory_subtree_multiple_variables(
        memory_tree_offset,
        imm,
        all_variables_to_place,
        layout,
    );
    let funct3 =
        layout_memory_subtree_variable(memory_tree_offset, funct3, all_variables_to_place, layout);
    let funct7 = funct7.expect("must be present in case of not preprocessed decoder");
    let funct7 =
        layout_memory_subtree_variable(memory_tree_offset, funct7, all_variables_to_place, layout);
    let circuit_family_extra_mask = layout_memory_subtree_variable(
        memory_tree_offset,
        circuit_family_extra_mask,
        all_variables_to_place,
        layout,
    );
    // This variable is a constant
    let circuit_family = ColumnSet::empty();

    let intermediate_state = IntermediateStatePermutationVariables {
        execute,
        pc,
        timestamp,
        rs1_index,
        rs2_index: ColumnAddress::MemorySubtree(rs2_index.start()),
        rd_index: ColumnAddress::MemorySubtree(rd_index.start()),
        decoder_witness_is_in_memory: true,
        rd_is_zero,
        imm,
        funct3,
        funct7,
        circuit_family,
        circuit_family_extra_mask: ColumnAddress::MemorySubtree(circuit_family_extra_mask.start()),
    };

    (machine_state, intermediate_state)
}

// NOTE: some variables (even though they can be in witness) would be already placed into memory,
// so we will conditionally place
pub(crate) fn layout_executor_state_for_preprocessed_bytecode<F: PrimeField>(
    memory_tree_offset: &mut usize,
    witness_tree_offset: &mut usize,
    all_variables_to_place: &mut BTreeSet<Variable>,
    layout: &mut BTreeMap<Variable, ColumnAddress>,
    state: &OpcodeFamilyCircuitState<F>,
) -> (
    MachineStatePermutationVariables,
    IntermediateStatePermutationVariables,
) {
    let execute = layout_memory_subtree_variable(
        memory_tree_offset,
        state.execute,
        all_variables_to_place,
        layout,
    );

    // in decoder PC/Timestamp for the current state - always in memory as they are part of permutation
    let pc = layout_memory_subtree_multiple_variables(
        memory_tree_offset,
        state.cycle_start_state.pc,
        all_variables_to_place,
        layout,
    );
    let timestamp = layout_memory_subtree_multiple_variables(
        memory_tree_offset,
        state.cycle_start_state.timestamp,
        all_variables_to_place,
        layout,
    );

    // but the rest CAN be in witness, and form a special lookup table entry PC -> decoder data

    let DecoderData {
        rs1_index,
        rs2_index,
        rd_index,
        rd_is_zero,
        imm,
        funct3,
        funct7,
        circuit_family_extra_mask,
        ..
    } = state.decoder_data.clone();

    let rs1_index =
        if let Some(ColumnAddress::MemorySubtree(offset)) = layout.get(&rs1_index).copied() {
            ColumnSet::new(offset, 1)
        } else {
            unreachable!();
            // layout_witness_subtree_variable(
            //     witness_tree_offset,
            //     rs1_index,
            //     all_variables_to_place,
            //     layout,
            // )
        };

    let rs2_index =
        if let Some(ColumnAddress::MemorySubtree(offset)) = layout.get(&rs2_index).copied() {
            ColumnAddress::MemorySubtree(offset)
        } else {
            let t = layout_witness_subtree_variable(
                witness_tree_offset,
                rs2_index,
                all_variables_to_place,
                layout,
            );

            ColumnAddress::WitnessSubtree(t.start())
        };

    let rd_index =
        if let Some(ColumnAddress::MemorySubtree(offset)) = layout.get(&rd_index).copied() {
            ColumnAddress::MemorySubtree(offset)
        } else {
            let t = layout_witness_subtree_variable(
                witness_tree_offset,
                rd_index,
                all_variables_to_place,
                layout,
            );

            ColumnAddress::WitnessSubtree(t.start())
        };
    let rd_is_zero = layout_witness_subtree_variable(
        witness_tree_offset,
        rd_is_zero,
        all_variables_to_place,
        layout,
    );
    let imm = layout_witness_subtree_multiple_variables(
        witness_tree_offset,
        imm,
        all_variables_to_place,
        layout,
    );
    let funct3 = layout_witness_subtree_variable(
        witness_tree_offset,
        funct3,
        all_variables_to_place,
        layout,
    );

    let funct7 = if let Some(funct7) = funct7 {
        layout_witness_subtree_variable(witness_tree_offset, funct7, all_variables_to_place, layout)
    } else {
        ColumnSet::empty()
    };
    let circuit_family_extra_mask = if let Some(ColumnAddress::MemorySubtree(offset)) =
        layout.get(&circuit_family_extra_mask).copied()
    {
        ColumnAddress::MemorySubtree(offset)
    } else {
        let t = layout_witness_subtree_variable(
            witness_tree_offset,
            circuit_family_extra_mask,
            all_variables_to_place,
            layout,
        );

        ColumnAddress::WitnessSubtree(t.start())
    };

    // there is no family - a table in every particular family only contains entries from the binary
    // that are responsible for the corresponding PC
    let circuit_family = ColumnSet::empty();

    let intermediate_state = IntermediateStatePermutationVariables {
        execute,
        pc,
        timestamp,
        rs1_index,
        rs2_index,
        rd_index,
        decoder_witness_is_in_memory: false,
        rd_is_zero,
        imm,
        funct3,
        funct7,
        circuit_family,
        circuit_family_extra_mask,
    };

    // reallocate for final set
    let next_pc = layout_memory_subtree_multiple_variables(
        memory_tree_offset,
        state.cycle_end_state.pc,
        all_variables_to_place,
        layout,
    );
    let next_timestamp = layout_memory_subtree_multiple_variables(
        memory_tree_offset,
        state.cycle_end_state.timestamp,
        all_variables_to_place,
        layout,
    );

    let next_machine_state = MachineStatePermutationVariables {
        pc: next_pc,
        timestamp: next_timestamp,
    };

    (next_machine_state, intermediate_state)
}

pub(crate) fn allocate_range_check_expressions<F: PrimeField>(
    trace_len: usize,
    compiled_extra_range_check_16_expressions: Vec<LookupExpression<F>>,
    range_check_expressions: &[RangeCheckQuery<F>],
    witness_tree_offset: &mut usize,
    all_variables_to_place: &mut BTreeSet<Variable>,
    layout: &mut BTreeMap<Variable, ColumnAddress>,
    extra_preexisting_range_checks_16: usize,
) -> (ColumnSet<1>, ColumnSet<1>, Vec<LookupExpression<F>>) {
    assert!(trace_len.is_power_of_two());

    for range_check in range_check_expressions.iter() {
        let RangeCheckQuery { input, width } = range_check;
        let LookupInput::Variable(..) = input else {
            unimplemented!()
        };
        assert!(*width == LARGE_RANGE_CHECK_TABLE_WIDTH || *width == SMALL_RANGE_CHECK_TABLE_WIDTH);
    }

    // We will place 8-bit range check variables, and then 16-bit ones

    let range_check_8_iter = range_check_expressions
        .iter()
        .filter(|el| el.width == SMALL_RANGE_CHECK_TABLE_WIDTH);
    let range_check_16_iter = range_check_expressions
        .iter()
        .filter(|el| el.width == LARGE_RANGE_CHECK_TABLE_WIDTH);

    let num_range_check_8 = range_check_8_iter.clone().count();
    let num_range_check_16 = range_check_16_iter.clone().count();

    let range_check_8_columns: ColumnSet<1> =
        ColumnSet::layout_at(witness_tree_offset, num_range_check_8);
    let range_check_8_columns_it = range_check_8_columns.iter();

    for (input, mut layout_part) in range_check_8_iter.zip(range_check_8_columns_it) {
        let LookupInput::Variable(input) = input.input else {
            unimplemented!()
        };
        let offset = layout_part.next().unwrap();
        let _place = layout_witness_subtree_variable_at_column(
            offset,
            input,
            all_variables_to_place,
            layout,
        );
    }

    // range checks 16 deserve their own treatment and own table, and for lookups over explicit variables
    // we just layout those continously in the row. We will also declare formal lookup expressions over them,
    // as below we will declare less-trivial range-check 16 expressions

    let mut range_check_16_lookup_expressions = vec![];

    // well, some variables could be already placed
    let mut num_columns_needed = 0;
    let mut offset = *witness_tree_offset;

    for range_check in range_check_16_iter {
        let RangeCheckQuery { input, .. } = range_check;
        let LookupInput::Variable(variable) = input else {
            unimplemented!()
        };
        let place = if let Some(place) = layout.get(variable).copied() {
            place
        } else {
            let place = layout_witness_subtree_variable_at_column(
                offset,
                *variable,
                all_variables_to_place,
                layout,
            );

            offset += 1;
            num_columns_needed += 1;

            place
        };

        let lookup_expr = LookupExpression::Variable(place);
        range_check_16_lookup_expressions.push(lookup_expr)
    }

    assert!(num_columns_needed <= num_range_check_16);

    let range_check_16_columns: ColumnSet<1> =
        ColumnSet::layout_at(witness_tree_offset, num_columns_needed);

    assert_eq!(*witness_tree_offset, offset);

    range_check_16_lookup_expressions.extend(compiled_extra_range_check_16_expressions);

    #[cfg(feature = "debug_logs")]
    {
        dbg!(range_check_16_lookup_expressions.len());
    }

    let total_lookups_for_range_checks_16 = ((range_check_16_lookup_expressions.len()
        + extra_preexisting_range_checks_16) as u64)
        * trace_len as u64;
    assert!(total_lookups_for_range_checks_16 < F::CHARACTERISTICS, "total number of range-check-16 lookups in circuit is {} that is larger that field characteristics {}", total_lookups_for_range_checks_16, F::CHARACTERISTICS);

    (
        range_check_8_columns,
        range_check_16_columns,
        range_check_16_lookup_expressions,
    )
}

pub(crate) fn allocate_width_3_lookups<F: PrimeField>(
    trace_len: usize,
    lookups: Vec<LookupQuery<F>>,
    witness_tree_offset: &mut usize,
    all_variables_to_place: &mut BTreeSet<Variable>,
    layout: &mut BTreeMap<Variable, ColumnAddress>,
) -> Vec<LookupSetDescription<F, 3>> {
    assert!(trace_len.is_power_of_two());

    let mut width_3_lookups = vec![];

    for lookup_query in lookups {
        let LookupQuery { row, table } = lookup_query;
        assert_eq!(row.len(), 3);

        let mut input_columns = Vec::with_capacity(3);
        for el in row.into_iter() {
            match el {
                LookupInput::Variable(single_var) => {
                    let place = if let Some(place) = layout.get(&single_var) {
                        // it's already placed
                        *place
                    } else {
                        let column = layout_witness_subtree_variable(
                            witness_tree_offset,
                            single_var,
                            all_variables_to_place,
                            layout,
                        );
                        let place = ColumnAddress::WitnessSubtree(column.start);

                        place
                    };

                    let lookup_expr = LookupExpression::Variable(place);
                    input_columns.push(lookup_expr);
                }
                LookupInput::Expression {
                    linear_terms,
                    constant_coeff,
                } => {
                    // place all of them
                    let mut compiled_linear_terms = vec![];
                    for (coeff, var) in linear_terms.iter() {
                        let place = if let Some(place) = layout.get(var) {
                            // it's already placed
                            *place
                        } else {
                            let column = layout_witness_subtree_variable(
                                witness_tree_offset,
                                *var,
                                all_variables_to_place,
                                layout,
                            );
                            let place = ColumnAddress::WitnessSubtree(column.start);

                            place
                        };
                        compiled_linear_terms.push((*coeff, place));
                    }
                    let compiled_constraint = CompiledDegree1Constraint {
                        linear_terms: compiled_linear_terms.into_boxed_slice(),
                        constant_term: constant_coeff,
                    };
                    let lookup_expr = LookupExpression::Expression(compiled_constraint);
                    input_columns.push(lookup_expr);
                }
            }
        }

        let table_index = match table {
            LookupQueryTableType::Constant(constant) => TableIndex::Constant(constant),
            LookupQueryTableType::Variable(variable) => {
                let column = layout_witness_subtree_variable(
                    witness_tree_offset,
                    variable,
                    all_variables_to_place,
                    layout,
                );
                let place = ColumnAddress::WitnessSubtree(column.start);
                TableIndex::Variable(place)
            }
        };

        let lookup = LookupSetDescription {
            input_columns: input_columns.try_into().unwrap(),
            table_index,
        };
        width_3_lookups.push(lookup);
    }

    let total_generic_lookups = width_3_lookups.len() as u64 * trace_len as u64;
    assert!(total_generic_lookups < F::CHARACTERISTICS, "total number of generic lookups in circuit is {} that is larger that field characteristics {}", total_generic_lookups, F::CHARACTERISTICS);

    width_3_lookups
}

pub(crate) fn compile_timestamp_range_check_expressions<
    F: PrimeField,
    const USE_CIRCUIT_SEQ: bool,
>(
    trace_len: usize,
    timestamp_range_check_expressions_to_compile: Vec<LookupInput<F>>,
    shuffle_ram_timestamp_range_check_partial_sets: Vec<ShuffleRamTimestampComparisonPartialData>,
    layout: &BTreeMap<Variable, ColumnAddress>,
    setup_layout: &SetupLayout,
    cycle_timestamp: Option<ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>>,
) -> (usize, std::vec::Vec<LookupExpression<F>>) {
    let mut compiled_timestamp_comparion_expressions = vec![];

    // we already have enough information to compile range check expressions that are left from memory accesses layout
    for input in timestamp_range_check_expressions_to_compile.into_iter() {
        let (linear_terms, constant_coeff) = match input {
            LookupInput::Expression {
                linear_terms,
                constant_coeff,
            } => (linear_terms, constant_coeff),
            LookupInput::Variable(var) => (vec![(F::ONE, var)], F::ZERO),
        };
        // place all of them
        let mut compiled_linear_terms = vec![];
        for (coeff, var) in linear_terms.iter() {
            let place = layout
                .get(var)
                .copied()
                .expect("all variables must be already placed");
            compiled_linear_terms.push((*coeff, place));
        }
        let compiled_constraint = CompiledDegree1Constraint {
            linear_terms: compiled_linear_terms.into_boxed_slice(),
            constant_term: constant_coeff,
        };
        let lookup_expr = LookupExpression::Expression(compiled_constraint);
        compiled_timestamp_comparion_expressions.push(lookup_expr);
    }

    // timestamps deserve separate range checks for shuffle RAM in the main circuit,
    // as those also take contribution from circuit index in the sequence

    // NOTE: these expressions are separate, as we will have to add to them a circuit sequence constant
    // that comes during the proving only

    let offset_for_special_shuffle_ram_timestamps_range_check_expressions =
        compiled_timestamp_comparion_expressions.len();

    for data in shuffle_ram_timestamp_range_check_partial_sets.into_iter() {
        let ShuffleRamTimestampComparisonPartialData {
            intermediate_borrow,
            read_timestamp,
            local_timestamp_in_cycle,
        } = data;
        let [read_low, read_high] = read_timestamp;
        // we know all the places, but will have to manually compile it into degree-1 constraint

        // low part
        {
            let mut compiled_linear_terms = vec![];
            let borrow_place = *layout.get(&intermediate_borrow).unwrap();
            compiled_linear_terms.push((
                F::from_u64_unchecked(1 << TIMESTAMP_COLUMNS_NUM_BITS),
                borrow_place,
            ));
            let read_low_place = *layout.get(&read_low).unwrap();
            compiled_linear_terms.push((F::ONE, read_low_place));

            // have to manually create write low place
            let write_low_place = if let Some(cycle_timestamp) = cycle_timestamp {
                assert!(USE_CIRCUIT_SEQ == false);
                ColumnAddress::MemorySubtree(cycle_timestamp.start())
            } else {
                assert!(USE_CIRCUIT_SEQ);
                ColumnAddress::SetupSubtree(setup_layout.timestamp_setup_columns.start())
            };
            compiled_linear_terms.push((F::MINUS_ONE, write_low_place));

            // and we also have a constant of `- in cycle local write`
            let mut constant_coeff = F::from_u64_unchecked(local_timestamp_in_cycle as u64);
            constant_coeff.negate();

            let compiled_constraint = CompiledDegree1Constraint {
                linear_terms: compiled_linear_terms.into_boxed_slice(),
                constant_term: constant_coeff,
            };
            let lookup_expr = LookupExpression::Expression(compiled_constraint);
            compiled_timestamp_comparion_expressions.push(lookup_expr);
        }
        // and almost the same for high part
        {
            let mut compiled_linear_terms = vec![];
            let read_high_place = *layout.get(&read_high).unwrap();
            compiled_linear_terms.push((F::ONE, read_high_place));

            let write_high_place = if let Some(cycle_timestamp) = cycle_timestamp {
                assert!(USE_CIRCUIT_SEQ == false);
                ColumnAddress::MemorySubtree(cycle_timestamp.start() + 1)
            } else {
                assert!(USE_CIRCUIT_SEQ);
                ColumnAddress::SetupSubtree(setup_layout.timestamp_setup_columns.start() + 1)
            };
            compiled_linear_terms.push((F::MINUS_ONE, write_high_place));

            // subtract borrow
            let borrow_place = *layout.get(&intermediate_borrow).unwrap();
            compiled_linear_terms.push((F::MINUS_ONE, borrow_place));

            let constant_coeff = F::from_u64_unchecked(1 << TIMESTAMP_COLUMNS_NUM_BITS);
            let compiled_constraint = CompiledDegree1Constraint {
                linear_terms: compiled_linear_terms.into_boxed_slice(),
                constant_term: constant_coeff,
            };
            let lookup_expr = LookupExpression::Expression(compiled_constraint);
            compiled_timestamp_comparion_expressions.push(lookup_expr);
        }
    }

    let offset_for_special_shuffle_ram_timestamps_range_check_expressions = if USE_CIRCUIT_SEQ {
        offset_for_special_shuffle_ram_timestamps_range_check_expressions
    } else {
        compiled_timestamp_comparion_expressions.len()
    };

    let total_timestamp_range_check_lookups =
        compiled_timestamp_comparion_expressions.len() as u64 * trace_len as u64;
    assert!(total_timestamp_range_check_lookups < F::CHARACTERISTICS, "total number of timestamp range check lookups in circuit is {} that is larger that field characteristics {}", total_timestamp_range_check_lookups, F::CHARACTERISTICS);

    (
        offset_for_special_shuffle_ram_timestamps_range_check_expressions,
        compiled_timestamp_comparion_expressions,
    )
}

pub(crate) fn optimize_out_linear_constraints<F: PrimeField>(
    state_input: &[Variable],
    state_output: &[Variable],
    substitutions: &HashMap<(Placeholder, usize), Variable>,
    mut constraints: Vec<(Constraint<F>, bool)>,
    all_variables_to_place: &mut BTreeSet<Variable>,
) -> (Vec<Variable>, Vec<(Constraint<F>, bool)>) {
    let initial_len = all_variables_to_place.len();
    let mut optimized_out_variables = vec![];
    let mut tried_variables = BTreeSet::new();
    'outer: loop {
        // we will try to remove every variable in there
        let mut to_remove: Option<(Variable, Vec<usize>, Vec<usize>)> = None;
        'inner: for variable in all_variables_to_place.iter() {
            if optimized_out_variables.contains(variable) {
                continue;
            }

            if tried_variables.contains(variable) {
                continue;
            }

            // we need
            // - some "defining" constraint where variable comes as the first degree
            // - potentially other constraints that contant such variable
            let mut defining_constraints = vec![];

            for (constraint_id, (constraint, prevent_optimizations)) in
                constraints.iter().enumerate()
            {
                if *prevent_optimizations {
                    continue;
                }
                if constraint.degree() > 1 {
                    continue;
                }
                if constraint.degree_for_var(variable) == 0 {
                    continue;
                }
                defining_constraints.push((constraint_id, constraint));
            }

            // check if variable is not a placeholder
            for (_, v) in substitutions.iter() {
                if v == variable {
                    continue 'inner;
                }
            }

            // it also can not be state input or output
            if state_input.contains(&variable) {
                continue;
            }

            if state_output.contains(&variable) {
                continue;
            }

            if defining_constraints.len() > 0 {
                let mut occurances = vec![];

                for (constraint_id, (constraint, _)) in constraints.iter().enumerate() {
                    if constraint.contains_var(variable) && constraint.degree_for_var(variable) < 2
                    {
                        occurances.push((constraint_id, constraint));
                    }
                }

                if occurances.len() > 1 {
                    // defining constraint will be here too
                    to_remove = Some((
                        *variable,
                        defining_constraints.iter().map(|el| el.0).collect(),
                        occurances.iter().map(|el| el.0).collect(),
                    ));
                    break;
                }
            }
        }

        if to_remove.is_none() {
            break 'outer;
        }

        let Some((variable_to_optimize_out, defining_constraints, occurances)) = to_remove else {
            panic!();
        };

        let mut optimized_out_params = None;

        for defining_constraint_idx in defining_constraints.into_iter() {
            // for now there is no heuristics to prefer one defining constraint over another,
            // but let's try all

            let defining_constraint = constraints[defining_constraint_idx].0.clone();
            // now we should rewrite it to factor out linear term
            let mut expression = defining_constraint.express_variable(variable_to_optimize_out);
            expression.normalize();

            #[cfg(feature = "debug_logs")]
            {
                println!("===============================================");
                println!(
                    "Will try to optimize out the variable {:?} using constraint {:?}",
                    variable_to_optimize_out, &defining_constraint
                );
                println!(
                    "Expression for variable {:?} is degree {} = {:?}",
                    variable_to_optimize_out,
                    expression.degree(),
                    &expression
                );
            }

            let mut can_be_optimized_out = true;
            let mut replacement_constraints = vec![];
            // now we should walk over other constraints and rewrite them
            for occurance_constraint_idx in occurances.iter().copied() {
                if occurance_constraint_idx == defining_constraint_idx {
                    continue;
                }

                let existing_constraint = constraints[occurance_constraint_idx].0.clone();
                let rewritten_constraint = existing_constraint
                    .clone()
                    .substitute_variable(variable_to_optimize_out, expression.clone());
                #[cfg(feature = "debug_logs")]
                {
                    println!("-----------------------------------------------");
                    println!(
                        "Will try to rewrite {:?} as {:?}",
                        &existing_constraint, &rewritten_constraint
                    );
                }

                if rewritten_constraint.degree() > 2 {
                    #[cfg(feature = "debug_logs")]
                    {
                        println!(
                            "Resultring constraint {:?} is of degree {}",
                            &rewritten_constraint,
                            rewritten_constraint.degree()
                        );
                    }
                    can_be_optimized_out = false;
                    break;
                } else {
                    replacement_constraints.push((occurance_constraint_idx, rewritten_constraint));
                }
            }

            #[cfg(feature = "debug_logs")]
            {
                println!("-----------------------------------------------");
            }
            if can_be_optimized_out {
                // we do not check whether one potential substitution or another will be the best,
                // so we will just use the latest one that will work
                optimized_out_params = Some((defining_constraint_idx, replacement_constraints));
            } else {
                tried_variables.insert(variable_to_optimize_out);
            }
        }

        if let Some((defining_constraint_idx, replacement_constraints)) = optimized_out_params {
            #[cfg(feature = "debug_logs")]
            {
                println!(
                    "Succesfully removed variable {:?}",
                    variable_to_optimize_out
                );
            }
            let existed = all_variables_to_place.remove(&variable_to_optimize_out);
            assert!(existed);
            optimized_out_variables.push(variable_to_optimize_out);
            // now we should carefully remove all the constraints
            let mut removal_set = BTreeMap::new();
            removal_set.insert(defining_constraint_idx, None);
            for (k, v) in replacement_constraints.into_iter() {
                removal_set.insert(k, Some(v));
            }

            let mut new_constraints = vec![];
            for (idx, constraint) in std::mem::replace(&mut constraints, vec![])
                .into_iter()
                .enumerate()
            {
                if let Some(replacement) = removal_set.get(&idx) {
                    let mut constraint = constraint;
                    if let Some(replacement) = replacement {
                        constraint.0 = replacement.clone();
                        new_constraints.push(constraint);
                    } else {
                        // just remove
                    }
                } else {
                    new_constraints.push(constraint);
                }
            }

            constraints = new_constraints;
        } else {
            #[cfg(feature = "debug_logs")]
            {
                println!("Can not remove variable {:?}", variable_to_optimize_out);
            }
        }
        #[cfg(feature = "debug_logs")]
        {
            println!("===============================================");
        }
    }

    #[cfg(feature = "debug_logs")]
    {
        println!(
            "{} variables were optimized out via linear constraint substitution",
            optimized_out_variables.len()
        );
    }

    assert_eq!(
        initial_len,
        optimized_out_variables.len() + all_variables_to_place.len()
    );

    (optimized_out_variables, constraints)
}

pub(crate) fn layout_scratch_space<F: PrimeField>(
    compiled_quadratic_terms: &mut Vec<CompiledDegree2Constraint<F>>,
    compiled_linear_terms: &mut Vec<CompiledDegree1Constraint<F>>,
    optimized_out_variables: Vec<Variable>,
    constraints: Vec<(Constraint<F>, bool)>,
    witness_tree_offset: &mut usize,
    all_variables_to_place: BTreeSet<Variable>,
    layout: &mut BTreeMap<Variable, ColumnAddress>,
) -> ColumnSet<1> {
    // those can be placed into scratch space right now
    let mut optimized_out_offset = 0;
    for var in optimized_out_variables.into_iter() {
        layout.insert(var, ColumnAddress::OptimizedOut(optimized_out_offset));
        optimized_out_offset += 1;
    }

    let mut scratch_space_columns_start = *witness_tree_offset;
    let scratch_space_columns_range = ColumnSet::layout_at(
        &mut scratch_space_columns_start,
        all_variables_to_place.len(),
    );

    // and then we will just place all other variable
    for variable in all_variables_to_place.into_iter() {
        layout.insert(
            variable,
            ColumnAddress::WitnessSubtree(*witness_tree_offset),
        );
        *witness_tree_offset += 1;
    }

    assert_eq!(
        scratch_space_columns_range.full_range().end,
        *witness_tree_offset
    );

    for (constraint, _) in constraints.into_iter() {
        assert!(constraint
            .terms
            .is_sorted_by(|a, b| a.degree() >= b.degree()));

        match constraint.degree() {
            2 => {
                let mut quadratic_terms = vec![];
                let mut linear_terms = vec![];
                let mut constant_term = F::ZERO;
                for term in constraint.terms.into_iter() {
                    match term.degree() {
                        2 => {
                            let coeff = term.get_coef();
                            let [a, b] = term.as_slice() else { panic!() };
                            assert!(*a <= *b);
                            let a = layout.get(a).copied().unwrap();
                            let b = layout.get(b).copied().unwrap();
                            quadratic_terms.push((coeff, a, b));
                        }
                        1 => {
                            let coeff = term.get_coef();
                            let [a] = term.as_slice() else { panic!() };
                            let a = layout.get(a).copied().unwrap();
                            linear_terms.push((coeff, a));
                        }
                        0 => {
                            constant_term.add_assign(&term.get_coef());
                        }
                        _ => {
                            unreachable!()
                        }
                    }
                }

                let compiled_term = CompiledDegree2Constraint {
                    quadratic_terms: quadratic_terms.into_boxed_slice(),
                    linear_terms: linear_terms.into_boxed_slice(),
                    constant_term,
                };

                compiled_quadratic_terms.push(compiled_term);
            }
            1 => {
                let mut linear_terms = vec![];
                let mut constant_term = F::ZERO;
                for term in constraint.terms.into_iter() {
                    match term.degree() {
                        1 => {
                            let coeff = term.get_coef();
                            let [a] = term.as_slice() else { panic!() };
                            let a = layout.get(a).copied().unwrap();
                            linear_terms.push((coeff, a));
                        }
                        0 => {
                            constant_term.add_assign(&term.get_coef());
                        }
                        _ => {
                            unreachable!()
                        }
                    }
                }

                let compiled_term = CompiledDegree1Constraint {
                    linear_terms: linear_terms.into_boxed_slice(),
                    constant_term,
                };

                compiled_linear_terms.push(compiled_term);
            }
            _ => {
                unreachable!()
            }
        }
    }

    #[cfg(feature = "debug_logs")]
    {
        dbg!(compiled_quadratic_terms.len());
        dbg!(compiled_linear_terms.len());
    }

    scratch_space_columns_range
}
