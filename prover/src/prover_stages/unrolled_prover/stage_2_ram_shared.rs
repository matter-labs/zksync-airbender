use super::*;
use crate::prover_stages::stage2_utils::stage_2_shuffle_ram_assemble_address_contribution;
use ::field::Mersenne31Field;

#[inline(always)]
pub(crate) unsafe fn stage_2_shuffle_ram_add_timestamp_contributions_in_executor_circuit(
    memory_trace_row: &[Mersenne31Field],
    read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    cycle_timestamp_columns: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
    access_idx: usize,
    numerator: &mut Mersenne31Quartic,
    denom: &mut Mersenne31Quartic,
) {
    // Numerator is write set, denom is read set

    let read_timestamp_low = *memory_trace_row.get_unchecked(read_timestamp.start());
    let mut read_timestamp_contibution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
    read_timestamp_contibution.mul_assign_by_base(&read_timestamp_low);

    let read_timestamp_high = *memory_trace_row.get_unchecked(read_timestamp.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
    t.mul_assign_by_base(&read_timestamp_high);
    read_timestamp_contibution.add_assign(&t);

    let mut write_timestamp_low = *memory_trace_row.get_unchecked(cycle_timestamp_columns.start());
    write_timestamp_low.add_assign(&Mersenne31Field::from_u64_unchecked(access_idx as u64));
    let mut write_timestamp_contibution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
    write_timestamp_contibution.mul_assign_by_base(&write_timestamp_low);

    let write_timestamp_high = *memory_trace_row.get_unchecked(cycle_timestamp_columns.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
    t.mul_assign_by_base(&write_timestamp_high);
    write_timestamp_contibution.add_assign(&t);

    numerator.add_assign(&write_timestamp_contibution);
    denom.add_assign(&read_timestamp_contibution);
}

#[inline(always)]
pub(crate) unsafe fn stage_2_shuffle_ram_assemble_read_contribution_in_executor_circuit(
    memory_trace_row: &[Mersenne31Field],
    address_contribution: &Mersenne31Quartic,
    columns: &ShuffleRamQueryReadColumns,
    cycle_timestamp_columns: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
    access_idx: usize,
    numerator_acc_value: &mut Mersenne31Quartic,
    denom_acc_value: &mut Mersenne31Quartic,
) {
    // Numerator is write set, denom is read set
    debug_assert_eq!(columns.read_value.width(), 2);

    let value_low = *memory_trace_row.get_unchecked(columns.read_value.start());
    let mut value_contibution = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
    value_contibution.mul_assign_by_base(&value_low);

    let value_high = *memory_trace_row.get_unchecked(columns.read_value.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
    t.mul_assign_by_base(&value_high);
    value_contibution.add_assign(&t);

    let mut numerator = memory_argument_challenges.memory_argument_gamma;
    numerator.add_assign(&address_contribution);
    numerator.add_assign(&value_contibution);

    let mut denom = numerator;

    stage_2_shuffle_ram_add_timestamp_contributions_in_executor_circuit(
        memory_trace_row,
        columns.read_timestamp,
        cycle_timestamp_columns,
        memory_argument_challenges,
        access_idx,
        &mut numerator,
        &mut denom,
    );

    numerator_acc_value.mul_assign(&numerator);
    denom_acc_value.mul_assign(&denom);
}

#[inline(always)]
pub(crate) unsafe fn stage_2_shuffle_ram_assemble_write_contribution_in_executor_circuit(
    memory_trace_row: &[Mersenne31Field],
    address_contribution: &Mersenne31Quartic,
    columns: &ShuffleRamQueryWriteColumns,
    cycle_timestamp_columns: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
    access_idx: usize,
    numerator_acc_value: &mut Mersenne31Quartic,
    denom_acc_value: &mut Mersenne31Quartic,
) {
    // Numerator is write set, denom is read set
    debug_assert_eq!(columns.read_value.width(), 2);

    let read_value_low = *memory_trace_row.get_unchecked(columns.read_value.start());
    let mut read_value_contibution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
    read_value_contibution.mul_assign_by_base(&read_value_low);

    let read_value_high = *memory_trace_row.get_unchecked(columns.read_value.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
    t.mul_assign_by_base(&read_value_high);
    read_value_contibution.add_assign(&t);

    debug_assert_eq!(columns.write_value.width(), 2);

    let write_value_low = *memory_trace_row.get_unchecked(columns.write_value.start());
    let mut write_value_contibution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
    write_value_contibution.mul_assign_by_base(&write_value_low);

    let write_value_high = *memory_trace_row.get_unchecked(columns.write_value.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
    t.mul_assign_by_base(&write_value_high);
    write_value_contibution.add_assign(&t);

    let mut numerator = memory_argument_challenges.memory_argument_gamma;
    numerator.add_assign(&address_contribution);

    let mut denom = numerator;

    numerator.add_assign(&write_value_contibution);
    denom.add_assign(&read_value_contibution);

    stage_2_shuffle_ram_add_timestamp_contributions_in_executor_circuit(
        memory_trace_row,
        columns.read_timestamp,
        cycle_timestamp_columns,
        memory_argument_challenges,
        access_idx,
        &mut numerator,
        &mut denom,
    );

    numerator_acc_value.mul_assign(&numerator);
    denom_acc_value.mul_assign(&denom);
}

pub(crate) unsafe fn stage2_process_ram_access_assuming_no_decoder(
    memory_trace_row: &[Mersenne31Field],
    stage_2_trace: &mut [Mersenne31Field],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    numerator_acc_value: &mut Mersenne31Quartic,
    denom_acc_value: &mut Mersenne31Quartic,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
    batch_inverses_input: &mut Vec<Mersenne31Quartic>,
) {
    // now we can continue to accumulate
    let cycle_timestamp_columns = compiled_circuit
        .memory_layout
        .intermediate_state_layout
        .unwrap()
        .timestamp;
    let dst_columns = compiled_circuit
        .stage_2_layout
        .intermediate_polys_for_memory_argument;
    assert_eq!(
        dst_columns.num_elements(),
        compiled_circuit.memory_layout.shuffle_ram_access_sets.len()
    );

    for (access_idx, memory_access_columns) in compiled_circuit
        .memory_layout
        .shuffle_ram_access_sets
        .iter()
        .enumerate()
    {
        match memory_access_columns {
            ShuffleRamQueryColumns::Readonly(columns) => {
                let address_contribution = stage_2_shuffle_ram_assemble_address_contribution(
                    memory_trace_row,
                    memory_access_columns,
                    &memory_argument_challenges,
                );

                debug_assert_eq!(columns.read_value.width(), 2);

                stage_2_shuffle_ram_assemble_read_contribution_in_executor_circuit(
                    memory_trace_row,
                    &address_contribution,
                    &columns,
                    cycle_timestamp_columns,
                    &memory_argument_challenges,
                    access_idx,
                    numerator_acc_value,
                    denom_acc_value,
                );

                // NOTE: here we write a chain of accumulator values, and not numerators themselves
                let dst = stage_2_trace
                    .as_mut_ptr()
                    .add(dst_columns.get_range(access_idx).start)
                    .cast::<Mersenne31Quartic>();
                debug_assert!(dst.is_aligned());
                dst.write(*numerator_acc_value);

                // and keep denominators for batch inverse
                batch_inverses_input.push(*denom_acc_value);
            }
            ShuffleRamQueryColumns::Write(columns) => {
                let address_contribution = stage_2_shuffle_ram_assemble_address_contribution(
                    memory_trace_row,
                    memory_access_columns,
                    &memory_argument_challenges,
                );

                stage_2_shuffle_ram_assemble_write_contribution_in_executor_circuit(
                    memory_trace_row,
                    &address_contribution,
                    &columns,
                    cycle_timestamp_columns,
                    &memory_argument_challenges,
                    access_idx,
                    numerator_acc_value,
                    denom_acc_value,
                );

                // NOTE: here we write a chain of accumulator values, and not numerators themselves
                let dst = stage_2_trace
                    .as_mut_ptr()
                    .add(dst_columns.get_range(access_idx).start)
                    .cast::<Mersenne31Quartic>();
                debug_assert!(dst.is_aligned());
                dst.write(*numerator_acc_value);

                // and keep denominators for batch inverse
                batch_inverses_input.push(*denom_acc_value);
            }
        }
    }
}

pub(crate) unsafe fn stage2_process_machine_state_permutation_assuming_no_decoder(
    memory_trace_row: &[Mersenne31Field],
    stage_2_trace: &mut [Mersenne31Field],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    numerator_acc_value: &mut Mersenne31Quartic,
    denom_acc_value: &mut Mersenne31Quartic,
    challenges: &ExternalMachineStateArgumentChallenges,
    batch_inverses_input: &mut Vec<Mersenne31Quartic>,
) {
    // sequence of keys is pc_low || pc_high || timestamp low || timestamp_high

    // we assemble P(x) = write set / read set

    let initial_machine_state = compiled_circuit
        .memory_layout
        .intermediate_state_layout
        .unwrap();
    let final_machine_state = compiled_circuit.memory_layout.machine_state_layout.unwrap();

    let dst_column_sets = compiled_circuit
        .stage_2_layout
        .intermediate_polys_for_state_permutation;
    assert_eq!(dst_column_sets.num_elements(), 1);

    // first write - final state
    let c0 = *memory_trace_row.get_unchecked(final_machine_state.pc.start());
    let c1 = *memory_trace_row.get_unchecked(final_machine_state.pc.start() + 1);
    let c2 = *memory_trace_row.get_unchecked(final_machine_state.timestamp.start());
    let c3 = *memory_trace_row.get_unchecked(final_machine_state.timestamp.start() + 1);

    let numerator = compute_aggregated_key_value(
        c0,
        [c1, c2, c3],
        challenges.linearization_challenges,
        challenges.additive_term,
    );
    numerator_acc_value.mul_assign(&numerator);

    // then read
    let c0 = *memory_trace_row.get_unchecked(initial_machine_state.pc.start());
    let c1 = *memory_trace_row.get_unchecked(initial_machine_state.pc.start() + 1);
    let c2 = *memory_trace_row.get_unchecked(initial_machine_state.timestamp.start());
    let c3 = *memory_trace_row.get_unchecked(initial_machine_state.timestamp.start() + 1);

    let denom = compute_aggregated_key_value(
        c0,
        [c1, c2, c3],
        challenges.linearization_challenges,
        challenges.additive_term,
    );
    denom_acc_value.mul_assign(&denom);

    // NOTE: here we write a chain of accumulator values, and not numerators themselves
    let dst_ptr = stage_2_trace
        .as_mut_ptr()
        .add(dst_column_sets.start())
        .cast::<Mersenne31Quartic>();
    debug_assert!(dst_ptr.is_aligned());
    dst_ptr.write(*numerator_acc_value);

    // and keep denominators for batch inverse
    batch_inverses_input.push(*denom_acc_value);
}
