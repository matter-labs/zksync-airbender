use super::*;

#[inline(always)]
pub(crate) unsafe fn stage_2_shuffle_ram_assemble_address_contribution(
    memory_trace_row: &[Mersenne31Field],
    memory_access_columns: &ShuffleRamQueryColumns,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
) -> Mersenne31Quartic {
    // Numerator is write set, denom is read set
    match memory_access_columns.get_address() {
        ShuffleRamAddress::RegisterOnly(RegisterOnlyAccessAddress { register_index }) => {
            let address_low = *memory_trace_row.get_unchecked(register_index.start());
            let mut address_contribution = memory_argument_challenges
                .memory_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            address_contribution.mul_assign_by_base(&address_low);

            // considered is register always
            address_contribution.add_assign_base(&Mersenne31Field::ONE);

            address_contribution
        }
        ShuffleRamAddress::RegisterOrRam(RegisterOrRamAccessAddress {
            is_register,
            address,
        }) => {
            debug_assert_eq!(address.width(), 2);

            let address_low = *memory_trace_row.get_unchecked(address.start());
            let mut address_contribution = memory_argument_challenges
                .memory_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            address_contribution.mul_assign_by_base(&address_low);

            let address_high = *memory_trace_row.get_unchecked(address.start() + 1);
            let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
            t.mul_assign_by_base(&address_high);
            address_contribution.add_assign(&t);

            debug_assert_eq!(is_register.width(), 1);
            let is_reg = *memory_trace_row.get_unchecked(is_register.start());
            address_contribution.add_assign_base(&is_reg);

            address_contribution
        }
    }
}

#[inline(always)]
pub(crate) unsafe fn stage_2_shuffle_ram_assemble_read_contribution(
    memory_trace_row: &[Mersenne31Field],
    setup_row: &[Mersenne31Field],
    address_contribution: &Mersenne31Quartic,
    columns: &ShuffleRamQueryReadColumns,
    timestamp_setup_columns: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM_IN_SETUP>,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
    access_idx: usize,
    memory_timestamp_high_from_circuit_idx: Mersenne31Field,
    numerator_acc_value: &mut Mersenne31Quartic,
    denom_acc_value: &mut Mersenne31Quartic,
) {
    // Numerator is write set, denom is read set
    debug_assert_eq!(columns.read_value.width(), 2);

    let value_low = *memory_trace_row.get_unchecked(columns.read_value.start());
    let mut value_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
    value_contribution.mul_assign_by_base(&value_low);

    let value_high = *memory_trace_row.get_unchecked(columns.read_value.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
    t.mul_assign_by_base(&value_high);
    value_contribution.add_assign(&t);

    let mut numerator = memory_argument_challenges.memory_argument_gamma;
    numerator.add_assign(&address_contribution);
    numerator.add_assign(&value_contribution);

    let mut denom = numerator;

    stage_2_shuffle_ram_add_timestamp_contributions(
        memory_trace_row,
        setup_row,
        columns.read_timestamp,
        timestamp_setup_columns,
        memory_argument_challenges,
        access_idx,
        memory_timestamp_high_from_circuit_idx,
        &mut numerator,
        &mut denom,
    );

    numerator_acc_value.mul_assign(&numerator);
    denom_acc_value.mul_assign(&denom);
}

#[inline(always)]
pub(crate) unsafe fn stage_2_shuffle_ram_assemble_write_contribution(
    memory_trace_row: &[Mersenne31Field],
    setup_row: &[Mersenne31Field],
    address_contribution: &Mersenne31Quartic,
    columns: &ShuffleRamQueryWriteColumns,
    timestamp_setup_columns: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM_IN_SETUP>,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
    access_idx: usize,
    circuit_idx: Mersenne31Field,
    numerator_acc_value: &mut Mersenne31Quartic,
    denom_acc_value: &mut Mersenne31Quartic,
) {
    // Numerator is write set, denom is read set
    debug_assert_eq!(columns.read_value.width(), 2);

    let read_value_low = *memory_trace_row.get_unchecked(columns.read_value.start());
    let mut read_value_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
    read_value_contribution.mul_assign_by_base(&read_value_low);

    let read_value_high = *memory_trace_row.get_unchecked(columns.read_value.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
    t.mul_assign_by_base(&read_value_high);
    read_value_contribution.add_assign(&t);

    debug_assert_eq!(columns.write_value.width(), 2);

    let write_value_low = *memory_trace_row.get_unchecked(columns.write_value.start());
    let mut write_value_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
    write_value_contribution.mul_assign_by_base(&write_value_low);

    let write_value_high = *memory_trace_row.get_unchecked(columns.write_value.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
    t.mul_assign_by_base(&write_value_high);
    write_value_contribution.add_assign(&t);

    let mut numerator = memory_argument_challenges.memory_argument_gamma;
    numerator.add_assign(&address_contribution);

    let mut denom = numerator;

    numerator.add_assign(&write_value_contribution);
    denom.add_assign(&read_value_contribution);

    stage_2_shuffle_ram_add_timestamp_contributions(
        memory_trace_row,
        setup_row,
        columns.read_timestamp,
        timestamp_setup_columns,
        memory_argument_challenges,
        access_idx,
        circuit_idx,
        &mut numerator,
        &mut denom,
    );

    numerator_acc_value.mul_assign(&numerator);
    denom_acc_value.mul_assign(&denom);
}

#[inline(always)]
pub(crate) unsafe fn stage_2_shuffle_ram_add_timestamp_contributions(
    memory_trace_row: &[Mersenne31Field],
    setup_row: &[Mersenne31Field],
    read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    timestamp_setup_columns: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM_IN_SETUP>,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
    access_idx: usize,
    memory_timestamp_high_from_circuit_idx: Mersenne31Field,
    numerator: &mut Mersenne31Quartic,
    denom: &mut Mersenne31Quartic,
) {
    // Numerator is write set, denom is read set
    debug_assert_eq!(read_timestamp.width(), 2);

    let read_timestamp_low = *memory_trace_row.get_unchecked(read_timestamp.start());
    let mut read_timestamp_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
    read_timestamp_contribution.mul_assign_by_base(&read_timestamp_low);

    let read_timestamp_high = *memory_trace_row.get_unchecked(read_timestamp.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
    t.mul_assign_by_base(&read_timestamp_high);
    read_timestamp_contribution.add_assign(&t);

    let mut write_timestamp_low = *setup_row.get_unchecked(timestamp_setup_columns.start());
    write_timestamp_low.add_assign(&Mersenne31Field::from_u64_unchecked(access_idx as u64));
    let mut write_timestamp_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
    write_timestamp_contribution.mul_assign_by_base(&write_timestamp_low);

    let mut write_timestamp_high = *setup_row.get_unchecked(timestamp_setup_columns.start() + 1);
    write_timestamp_high.add_assign(&memory_timestamp_high_from_circuit_idx);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
    t.mul_assign_by_base(&write_timestamp_high);
    write_timestamp_contribution.add_assign(&t);

    numerator.add_assign(&write_timestamp_contribution);
    denom.add_assign(&read_timestamp_contribution);
}

#[inline(always)]
pub(crate) unsafe fn stage_2_batched_ram_assemble_address_contribution(
    memory_trace_row: &[Mersenne31Field],
    mem_offset_high: ColumnSet<1>,
    offset: usize,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
) -> Mersenne31Quartic {
    // Numerator is write set, denom is read set
    let address_low = Mersenne31Field(offset as u32);
    let mut address_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
    address_contribution.mul_assign_by_base(&address_low);

    let address_high = *memory_trace_row.get_unchecked(mem_offset_high.start());
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
    t.mul_assign_by_base(&address_high);
    address_contribution.add_assign(&t);

    // thiere is no "is register" contribution

    address_contribution
}

#[inline(always)]
pub(crate) unsafe fn _stage_2_ram_assemble_timestamp_contribution(
    memory_trace_row: &[Mersenne31Field],
    read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    write_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
    numerator: &mut Mersenne31Quartic,
    denom: &mut Mersenne31Quartic,
) {
    // Numerator is write set, denom is read set
    debug_assert_eq!(read_timestamp.width(), 2);

    let read_timestamp_low = *memory_trace_row.get_unchecked(read_timestamp.start());
    let mut read_timestamp_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
    read_timestamp_contribution.mul_assign_by_base(&read_timestamp_low);

    let read_timestamp_high = *memory_trace_row.get_unchecked(read_timestamp.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
    t.mul_assign_by_base(&read_timestamp_high);
    read_timestamp_contribution.add_assign(&t);

    let write_timestamp_low = *memory_trace_row.get_unchecked(write_timestamp.start());
    let mut write_timestamp_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
    write_timestamp_contribution.mul_assign_by_base(&write_timestamp_low);

    let write_timestamp_high = *memory_trace_row.get_unchecked(write_timestamp.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
    t.mul_assign_by_base(&write_timestamp_high);
    write_timestamp_contribution.add_assign(&t);

    numerator.add_assign(&write_timestamp_contribution);
    denom.add_assign(&read_timestamp_contribution);
}

#[inline(always)]
pub(crate) unsafe fn stage_2_delegation_ram_assemble_timestamp_contribution(
    memory_trace_row: &[Mersenne31Field],
    read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    write_timestamp_contribution: &Mersenne31Quartic,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
    numerator: &mut Mersenne31Quartic,
    denom: &mut Mersenne31Quartic,
) {
    // Numerator is write set, denom is read set
    debug_assert_eq!(read_timestamp.width(), 2);

    let read_timestamp_low = *memory_trace_row.get_unchecked(read_timestamp.start());
    let mut read_timestamp_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
    read_timestamp_contribution.mul_assign_by_base(&read_timestamp_low);

    let read_timestamp_high = *memory_trace_row.get_unchecked(read_timestamp.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
    t.mul_assign_by_base(&read_timestamp_high);
    read_timestamp_contribution.add_assign(&t);

    numerator.add_assign(write_timestamp_contribution);
    denom.add_assign(&read_timestamp_contribution);
}

#[inline(always)]
pub(crate) unsafe fn stage_2_batched_ram_assemble_read_contribution(
    memory_trace_row: &[Mersenne31Field],
    read_value: ColumnSet<REGISTER_SIZE>,
    read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    write_timestamp_contribution: &Mersenne31Quartic,
    mem_offset_high: ColumnSet<1>,
    offset: usize,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
    numerator_acc_value: &mut Mersenne31Quartic,
    denom_acc_value: &mut Mersenne31Quartic,
) {
    // Numerator is write set, denom is read set
    let address_contribution = stage_2_batched_ram_assemble_address_contribution(
        memory_trace_row,
        mem_offset_high,
        offset,
        memory_argument_challenges,
    );

    debug_assert_eq!(read_value.width(), 2);

    let value_low = *memory_trace_row.get_unchecked(read_value.start());
    let mut value_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
    value_contribution.mul_assign_by_base(&value_low);

    let value_high = *memory_trace_row.get_unchecked(read_value.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
    t.mul_assign_by_base(&value_high);
    value_contribution.add_assign(&t);

    let mut numerator = memory_argument_challenges.memory_argument_gamma;
    numerator.add_assign(&address_contribution);
    numerator.add_assign(&value_contribution);

    let mut denom = numerator;

    stage_2_delegation_ram_assemble_timestamp_contribution(
        memory_trace_row,
        read_timestamp,
        write_timestamp_contribution,
        memory_argument_challenges,
        &mut numerator,
        &mut denom,
    );

    numerator_acc_value.mul_assign(&numerator);
    denom_acc_value.mul_assign(&denom);
}

#[inline(always)]
pub(crate) unsafe fn stage_2_batched_ram_assemble_write_contribution(
    memory_trace_row: &[Mersenne31Field],
    read_value: ColumnSet<REGISTER_SIZE>,
    write_value: ColumnSet<REGISTER_SIZE>,
    read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    write_timestamp_contribution: &Mersenne31Quartic,
    mem_offset_high: ColumnSet<1>,
    offset: usize,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
    numerator_acc_value: &mut Mersenne31Quartic,
    denom_acc_value: &mut Mersenne31Quartic,
) {
    // Numerator is write set, denom is read set
    let address_contribution = stage_2_batched_ram_assemble_address_contribution(
        memory_trace_row,
        mem_offset_high,
        offset,
        memory_argument_challenges,
    );

    debug_assert_eq!(read_value.width(), 2);

    let read_value_low = *memory_trace_row.get_unchecked(read_value.start());
    let mut read_value_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
    read_value_contribution.mul_assign_by_base(&read_value_low);

    let read_value_high = *memory_trace_row.get_unchecked(read_value.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
    t.mul_assign_by_base(&read_value_high);
    read_value_contribution.add_assign(&t);

    debug_assert_eq!(write_value.width(), 2);

    let write_value_low = *memory_trace_row.get_unchecked(write_value.start());
    let mut write_value_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
    write_value_contribution.mul_assign_by_base(&write_value_low);

    let write_value_high = *memory_trace_row.get_unchecked(write_value.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
    t.mul_assign_by_base(&write_value_high);
    write_value_contribution.add_assign(&t);

    let mut numerator = memory_argument_challenges.memory_argument_gamma;
    numerator.add_assign(&address_contribution);

    let mut denom = numerator;

    numerator.add_assign(&write_value_contribution);
    denom.add_assign(&read_value_contribution);

    stage_2_delegation_ram_assemble_timestamp_contribution(
        memory_trace_row,
        read_timestamp,
        write_timestamp_contribution,
        memory_argument_challenges,
        &mut numerator,
        &mut denom,
    );

    numerator_acc_value.mul_assign(&numerator);
    denom_acc_value.mul_assign(&denom);
}

#[inline(always)]
pub(crate) unsafe fn stage_2_register_access_assemble_address_contribution(
    register_index: u32,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
) -> Mersenne31Quartic {
    debug_assert!(register_index > 0);
    debug_assert!(register_index < 32);

    // Numerator is write set, denom is read set
    let address_low = Mersenne31Field(register_index);
    let mut address_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
    address_contribution.mul_assign_by_base(&address_low);

    // "is register"
    address_contribution.add_assign_base(&Mersenne31Field::ONE);

    address_contribution
}

#[inline(always)]
pub(crate) unsafe fn stage_2_indirect_access_assemble_address_contribution(
    base_value: (u16, u16),
    offset: u16,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
) -> Mersenne31Quartic {
    let (base_low, base_high) = base_value;
    let (address_low, of) = base_low.overflowing_add(offset);
    let (address_high, of) = base_high.overflowing_add(of as u16);
    assert!(of == false);

    // Numerator is write set, denom is read set
    let address_low = Mersenne31Field(address_low as u32);
    let mut address_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
    address_contribution.mul_assign_by_base(&address_low);

    let address_high = Mersenne31Field(address_high as u32);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
    t.mul_assign_by_base(&address_high);
    address_contribution.add_assign(&t);

    // thiere is no "is register" contribution

    address_contribution
}

#[inline(always)]
pub(crate) unsafe fn stage_2_register_access_assemble_read_contribution(
    memory_trace_row: &[Mersenne31Field],
    read_value: ColumnSet<REGISTER_SIZE>,
    read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    write_timestamp_contribution: &Mersenne31Quartic,
    register_index: u32,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
    numerator_acc_value: &mut Mersenne31Quartic,
    denom_acc_value: &mut Mersenne31Quartic,
) -> (u16, u16) {
    // Numerator is write set, denom is read set
    let address_contribution = stage_2_register_access_assemble_address_contribution(
        register_index,
        memory_argument_challenges,
    );

    debug_assert_eq!(read_value.width(), 2);

    let value_low = *memory_trace_row.get_unchecked(read_value.start());
    let mut value_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
    value_contribution.mul_assign_by_base(&value_low);

    let value_high = *memory_trace_row.get_unchecked(read_value.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
    t.mul_assign_by_base(&value_high);
    value_contribution.add_assign(&t);

    let mut numerator = memory_argument_challenges.memory_argument_gamma;
    numerator.add_assign(&address_contribution);
    numerator.add_assign(&value_contribution);

    let mut denom = numerator;

    stage_2_delegation_ram_assemble_timestamp_contribution(
        memory_trace_row,
        read_timestamp,
        write_timestamp_contribution,
        memory_argument_challenges,
        &mut numerator,
        &mut denom,
    );

    numerator_acc_value.mul_assign(&numerator);
    denom_acc_value.mul_assign(&denom);

    (
        value_low.to_reduced_u32() as u16,
        value_high.to_reduced_u32() as u16,
    )
}

#[inline(always)]
pub(crate) unsafe fn stage_2_register_access_assemble_write_contribution(
    memory_trace_row: &[Mersenne31Field],
    read_value: ColumnSet<REGISTER_SIZE>,
    write_value: ColumnSet<REGISTER_SIZE>,
    read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    write_timestamp_contribution: &Mersenne31Quartic,
    register_index: u32,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
    numerator_acc_value: &mut Mersenne31Quartic,
    denom_acc_value: &mut Mersenne31Quartic,
) -> (u16, u16) {
    // Numerator is write set, denom is read set
    let address_contribution = stage_2_register_access_assemble_address_contribution(
        register_index,
        memory_argument_challenges,
    );

    debug_assert_eq!(read_value.width(), 2);

    let read_value_low = *memory_trace_row.get_unchecked(read_value.start());
    let mut read_value_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
    read_value_contribution.mul_assign_by_base(&read_value_low);

    let read_value_high = *memory_trace_row.get_unchecked(read_value.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
    t.mul_assign_by_base(&read_value_high);
    read_value_contribution.add_assign(&t);

    debug_assert_eq!(write_value.width(), 2);

    let write_value_low = *memory_trace_row.get_unchecked(write_value.start());
    let mut write_value_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
    write_value_contribution.mul_assign_by_base(&write_value_low);

    let write_value_high = *memory_trace_row.get_unchecked(write_value.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
    t.mul_assign_by_base(&write_value_high);
    write_value_contribution.add_assign(&t);

    let mut numerator = memory_argument_challenges.memory_argument_gamma;
    numerator.add_assign(&address_contribution);

    let mut denom = numerator;

    numerator.add_assign(&write_value_contribution);
    denom.add_assign(&read_value_contribution);

    stage_2_delegation_ram_assemble_timestamp_contribution(
        memory_trace_row,
        read_timestamp,
        write_timestamp_contribution,
        memory_argument_challenges,
        &mut numerator,
        &mut denom,
    );

    numerator_acc_value.mul_assign(&numerator);
    denom_acc_value.mul_assign(&denom);

    (
        read_value_low.to_reduced_u32() as u16,
        read_value_high.to_reduced_u32() as u16,
    )
}

#[inline(always)]
pub(crate) unsafe fn stage_2_indirect_access_assemble_read_contribution(
    memory_trace_row: &[Mersenne31Field],
    read_value: ColumnSet<REGISTER_SIZE>,
    read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    write_timestamp_contribution: &Mersenne31Quartic,
    base_value: (u16, u16),
    offset: u16,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
    numerator_acc_value: &mut Mersenne31Quartic,
    denom_acc_value: &mut Mersenne31Quartic,
) {
    // Numerator is write set, denom is read set
    let address_contribution = stage_2_indirect_access_assemble_address_contribution(
        base_value,
        offset,
        &memory_argument_challenges,
    );

    debug_assert_eq!(read_value.width(), 2);

    let value_low = *memory_trace_row.get_unchecked(read_value.start());
    let mut value_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
    value_contribution.mul_assign_by_base(&value_low);

    let value_high = *memory_trace_row.get_unchecked(read_value.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
    t.mul_assign_by_base(&value_high);
    value_contribution.add_assign(&t);

    let mut numerator = memory_argument_challenges.memory_argument_gamma;
    numerator.add_assign(&address_contribution);
    numerator.add_assign(&value_contribution);

    let mut denom = numerator;

    stage_2_delegation_ram_assemble_timestamp_contribution(
        memory_trace_row,
        read_timestamp,
        write_timestamp_contribution,
        memory_argument_challenges,
        &mut numerator,
        &mut denom,
    );

    numerator_acc_value.mul_assign(&numerator);
    denom_acc_value.mul_assign(&denom);
}

#[inline(always)]
pub(crate) unsafe fn stage_2_indirect_access_assemble_write_contribution(
    memory_trace_row: &[Mersenne31Field],
    read_value: ColumnSet<REGISTER_SIZE>,
    write_value: ColumnSet<REGISTER_SIZE>,
    read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    write_timestamp_contribution: &Mersenne31Quartic,
    base_value: (u16, u16),
    offset: u16,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
    numerator_acc_value: &mut Mersenne31Quartic,
    denom_acc_value: &mut Mersenne31Quartic,
) {
    // Numerator is write set, denom is read set
    let address_contribution = stage_2_indirect_access_assemble_address_contribution(
        base_value,
        offset,
        &memory_argument_challenges,
    );

    debug_assert_eq!(read_value.width(), 2);

    let read_value_low = *memory_trace_row.get_unchecked(read_value.start());
    let mut read_value_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
    read_value_contribution.mul_assign_by_base(&read_value_low);

    let read_value_high = *memory_trace_row.get_unchecked(read_value.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
    t.mul_assign_by_base(&read_value_high);
    read_value_contribution.add_assign(&t);

    debug_assert_eq!(write_value.width(), 2);

    let write_value_low = *memory_trace_row.get_unchecked(write_value.start());
    let mut write_value_contribution = memory_argument_challenges
        .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
    write_value_contribution.mul_assign_by_base(&write_value_low);

    let write_value_high = *memory_trace_row.get_unchecked(write_value.start() + 1);
    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
    t.mul_assign_by_base(&write_value_high);
    write_value_contribution.add_assign(&t);

    let mut numerator = memory_argument_challenges.memory_argument_gamma;
    numerator.add_assign(&address_contribution);

    let mut denom = numerator;

    numerator.add_assign(&write_value_contribution);
    denom.add_assign(&read_value_contribution);

    stage_2_delegation_ram_assemble_timestamp_contribution(
        memory_trace_row,
        read_timestamp,
        write_timestamp_contribution,
        memory_argument_challenges,
        &mut numerator,
        &mut denom,
    );

    numerator_acc_value.mul_assign(&numerator);
    denom_acc_value.mul_assign(&denom);
}

pub(crate) unsafe fn stage2_process_ram_access(
    memory_trace_row: &[Mersenne31Field],
    setup_row: &[Mersenne31Field],
    stage_2_trace: &mut [Mersenne31Field],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    numerator_acc_value: &mut Mersenne31Quartic,
    denom_acc_value: &mut Mersenne31Quartic,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
    batch_inverses_input: &mut Vec<Mersenne31Quartic>,
    memory_timestamp_high_from_circuit_idx: Mersenne31Field,
) {
    // now we can continue to accumulate
    let dst_columns = compiled_circuit
        .stage_2_layout
        .intermediate_polys_for_memory_argument;
    assert_eq!(
        dst_columns.num_elements(),
        compiled_circuit.memory_layout.shuffle_ram_access_sets.len()
    );

    // now we can continue to accumulate
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

                stage_2_shuffle_ram_assemble_read_contribution(
                    memory_trace_row,
                    setup_row,
                    &address_contribution,
                    &columns,
                    compiled_circuit.setup_layout.timestamp_setup_columns,
                    &memory_argument_challenges,
                    access_idx,
                    memory_timestamp_high_from_circuit_idx,
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

                stage_2_shuffle_ram_assemble_write_contribution(
                    memory_trace_row,
                    setup_row,
                    &address_contribution,
                    &columns,
                    compiled_circuit.setup_layout.timestamp_setup_columns,
                    &memory_argument_challenges,
                    access_idx,
                    memory_timestamp_high_from_circuit_idx,
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
