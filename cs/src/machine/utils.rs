use one_row_compiler::LookupInput;

use super::*;
use crate::devices::diffs::PC_INC_STEP;
use crate::machine::ops::*;
use crate::tables::*;

pub fn assert_no_unimp<F: PrimeField, C: Circuit<F>>(_cs: &mut C, _next_opcode: Register<F>) {
    todo!();

    // let term_low = Term::from(next_opcode.0[0]) - Term::<F>::from(UNIMP_OPCODE_LOW as u64);
    // let term_high = Term::from(next_opcode.0[1]) - Term::<F>::from(UNIMP_OPCODE_HIGH as u64);
    // // we never want them to simultaneously be 0, so we can make a variable and assert it's not zero
    // let inversion_witness_0 = cs.add_variable();
    // let t0 = cs.add_variable_from_constraint(
    //     Constraint::from(1) - term_low * Term::from(inversion_witness_0),
    // );
    // let inversion_witness_1 = cs.add_variable();
    // let t1 = cs.add_variable_from_constraint(
    //     Constraint::from(1) - term_high * Term::from(inversion_witness_1),
    // );
    // cs.add_constraint(Term::from(t0) * Term::from(t1));

    // let value_fn = |input: WitnessGenSource<'_, F>,
    //                 mut output: WitnessGenDest<'_, F>,
    //                 constants: &[F],
    //                 table_driver: &TableDriver<F>,
    //                 table_type: TableType| {
    //     debug_assert!(constants.is_empty());
    //     let mut opcode_low: F = input[0];
    //     opcode_low.sub_assign(&F::from_u64_unchecked(UNIMP_OPCODE_LOW as u64));
    //     let mut opcode_high: F = input[1];
    //     opcode_high.sub_assign(&F::from_u64_unchecked(UNIMP_OPCODE_HIGH as u64));
    //     let inv0 = opcode_low.inverse().unwrap_or(F::ZERO);
    //     let inv1 = opcode_high.inverse().unwrap_or(F::ZERO);
    //     output[0] = inv0;
    //     output[1] = inv1;
    // };
    // cs.set_values(
    //     &[
    //         next_opcode.0[0].get_variable(),
    //         next_opcode.0[1].get_variable(),
    //     ],
    //     &[inversion_witness_0, inversion_witness_1],
    //     &[],
    //     TableType::ZeroEntry,
    //     value_fn,
    // );
}

pub fn calculate_pc_next_no_overflows<F: PrimeField, CS: Circuit<F>>(
    circuit: &mut CS,
    pc: Register<F>,
) -> Register<F> {
    // Input invariant: PC % 4 == 0, preserved as:
    // - initial PC is valid % 4
    // - jumps and branches check for alignments

    // strategy:
    // - allocate lower part of addition result and ensure that it is 16 bits
    // - do not allocate carry and make sure that (pc_low + 4 - result) >> 16 is boolean
    // - compute new high as pc_high + ((pc_low + 4 - result) >> 16)
    // - make sure that new high is not equal to 2^16

    let pc_next_low = circuit.add_variable();
    circuit.require_invariant(
        pc_next_low,
        Invariant::RangeChecked {
            width: LIMB_WIDTH as u32,
        },
    );

    let pc_t = pc.get_terms();
    let mut carry_constraint = Constraint::empty();
    carry_constraint += pc_t[0].clone();
    carry_constraint += Term::from(PC_INC_STEP);
    carry_constraint -= Term::from(pc_next_low);
    carry_constraint.scale(F::from_u64_unchecked(1 << 16).inverse().unwrap());

    // ensure boolean
    let mut t = carry_constraint.clone();
    t -= Term::from(1u64);
    circuit.add_constraint(carry_constraint.clone() * t);

    let mut pc_high_constraint = carry_constraint;
    pc_high_constraint += pc_t[1].clone();
    // we will evaluate witness below all at once
    let pc_next_high = circuit
        .add_variable_from_constraint_allow_explicit_linear_without_witness_evaluation(
            pc_high_constraint,
        );
    // ensure that it is not equal to 2^16
    let inversion_witness = circuit.add_variable();
    circuit.add_constraint(
        (Term::from(inversion_witness) * (Term::from(pc_next_high) - Term::from(1u64 << 16)))
            - Term::from(1u64),
    );

    let pc_next = Register([Num::Var(pc_next_low), Num::Var(pc_next_high)]);

    // NOTE: we should try to set values before setting constraint as much as possible
    // setting values for overflow flags

    let pc_vars = [pc.0[0].get_variable(), pc.0[1].get_variable()];
    let pc_next_vars = [pc_next.0[0].get_variable(), pc_next.0[1].get_variable()];

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        use crate::cs::witness_placer::*;

        let pc_inc_step =
            <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(PC_INC_STEP as u32);
        let pc = placer.get_u32_from_u16_parts(pc_vars);
        let (pc_next, _of) = pc.overflowing_add(&pc_inc_step);
        placer.assign_u32_from_u16_parts(pc_next_vars, &pc_next);

        let pc_high = pc_next.shr(16);
        let mut pc_high = <CS::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer(pc_high);
        let shift = <CS::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(
            F::from_u64_unchecked(1u64 << 16),
        );
        pc_high.sub_assign(&shift);
        let inversion_witness_value = pc_high.inverse();
        placer.assign_field(inversion_witness, &inversion_witness_value);
    };

    circuit.set_values(value_fn);

    pc_next
}

pub fn bump_pc_no_range_checks_explicit<F: PrimeField, CS: Circuit<F>>(
    circuit: &mut CS,
    pc: Register<F>,
    pc_next: Register<F>,
) {
    // Input invariant: PC % 4 == 0, preserved as:
    // - initial PC is valid % 4
    // - jumps and branches check for alignemnts

    // check if PC_LOW + 4 is exactly 2^16, and then select

    let carry_var = {
        let pc_low_var = pc.0[0].get_variable();
        let pc_next_low_var = pc_next.0[0].get_variable();

        // (var - var2) * zero_flag = 0;
        // (var - var2) * var_inv = 1 - zero_flag;
        let var_inv = circuit.add_variable();
        let low_eq_flag = circuit.add_boolean_variable();
        let low_eq_flag_var = low_eq_flag.get_variable().unwrap();

        circuit.add_constraint(
            (Term::from(pc_low_var) + Term::from(PC_INC_STEP) - Term::from(1 << 16))
                * Term::from(low_eq_flag),
        );
        circuit.add_constraint(
            (Term::from(pc_low_var) + Term::from(PC_INC_STEP) - Term::from(1 << 16))
                * Term::from(var_inv)
                + Term::from(low_eq_flag)
                - Term::from(1),
        );

        // then select - just make a constraint - if equal then 0, otherwise - result of addition
        circuit.add_constraint(
            (Term::from(1) - Term::from(low_eq_flag))
                * (Term::from(pc_low_var) + Term::from(PC_INC_STEP))
                - Term::from(pc_next_low_var),
        );

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            use crate::cs::witness_placer::*;

            let pc_low = placer.get_u16(pc_low_var);
            let step = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(PC_INC_STEP as u16);
            let (maybe_next_pc_low, of) = pc_low.overflowing_add(&step);
            // if we have overflow, then it's equal indeed
            placer.assign_mask(low_eq_flag_var, &of);

            // actually assign a value for next PC
            let zero = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0);
            let selected_pc_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                &of,
                &zero,
                &maybe_next_pc_low,
            );
            placer.assign_u16(pc_next_low_var, &selected_pc_value);

            let mut tmp =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer(pc_low.widen());
            tmp.add_assign(&<CS::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(
                F::from_u64_unchecked(PC_INC_STEP),
            ));
            tmp.sub_assign(&<CS::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(
                F::from_u64_unchecked(1 << 16),
            ));
            let tmp = tmp.inverse_or_zero();
            placer.assign_field(var_inv, &tmp);
        };
        circuit.set_values(value_fn);

        low_eq_flag_var
    };

    // now effectively the same, but with variable instead of constant step
    let pc_high_var = pc.0[1].get_variable();
    let pc_next_high_var = pc_next.0[1].get_variable();

    {
        // (var - var2) * zero_flag = 0;
        // (var - var2) * var_inv = 1 - zero_flag;
        let var_inv = circuit.add_variable();
        let eq_flag = circuit.add_boolean_variable();
        let eq_flag_var = eq_flag.get_variable().unwrap();

        circuit.add_constraint(
            (Term::from(pc_high_var) + Term::from(carry_var) - Term::from(1 << 16))
                * Term::from(eq_flag),
        );
        circuit.add_constraint(
            (Term::from(pc_high_var) + Term::from(carry_var) - Term::from(1 << 16))
                * Term::from(var_inv)
                + Term::from(eq_flag)
                - Term::from(1),
        );

        // then select - just make a constraint
        circuit.add_constraint(
            (Term::from(1) - Term::from(eq_flag))
                * (Term::from(pc_high_var) + Term::from(carry_var))
                - Term::from(pc_next_high_var),
        );

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            use crate::cs::witness_placer::*;

            let pc_high = placer.get_u16(pc_high_var);
            let step = placer.get_u16(carry_var);
            let (maybe_next_pc_high, of) = pc_high.overflowing_add(&step);
            // if we have overflow, then it's equal indeed
            placer.assign_mask(eq_flag_var, &of);

            // actually assign a value for next PC
            let zero = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0);
            let selected_pc_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                &of,
                &zero,
                &maybe_next_pc_high,
            );
            placer.assign_u16(pc_next_high_var, &selected_pc_value);

            let mut tmp =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer(pc_high.widen());
            tmp.add_assign(
                &<CS::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer(step.widen()),
            );
            tmp.sub_assign(&<CS::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(
                F::from_u64_unchecked(1 << 16),
            ));
            let tmp = tmp.inverse_or_zero();
            placer.assign_field(var_inv, &tmp);
        };
        circuit.set_values(value_fn);
    }
}

#[allow(deprecated)]
pub fn read_from_shuffle_ram_or_bytecode_with_ctx<F: PrimeField, C: Circuit<F>>(
    cs: &mut C,
    local_timestamp_in_cycle: usize,
    address_aligned_low: Constraint<F>,
    address_aligned_high: Num<F>,
    opt_ctx: &mut OptimizationContext<F, C>,
    exec_flag: Boolean,
) -> (RegisterDecomposition<F>, ShuffleRamMemQuery, Variable) {
    let (mem_value, query, is_ram_range) =
        read_from_shuffle_ram_or_bytecode_no_decomposition_with_ctx(
            cs,
            local_timestamp_in_cycle,
            address_aligned_low,
            address_aligned_high,
            opt_ctx,
            exec_flag,
        );

    let res = RegisterDecomposition::split_reg_with_opt_ctx(cs, mem_value, opt_ctx, exec_flag);

    (res, query, is_ram_range)
}

pub(crate) fn read_from_shuffle_ram_or_bytecode_no_decomposition_with_ctx<
    F: PrimeField,
    C: Circuit<F>,
>(
    cs: &mut C,
    local_timestamp_in_cycle: usize,
    address_aligned_low: Constraint<F>,
    address_aligned_high: Num<F>,
    optimization_context: &mut OptimizationContext<F, C>,
    exec_flag: Boolean,
) -> (Register<F>, ShuffleRamMemQuery, Variable) {
    // NOTE: all lookup actions here are conditional, so we should not accume that boolean is so,
    // and should not use special operations like Boolean::and where witness generation is specialized.

    // This is ok even for masking into x0 read/write for query as we are globally predicated by memory operations flags,
    // so if it's not a memory operation it'll be overwritten during merge of memory queries

    let [is_ram_range, address_high_bits_for_rom] = optimization_context.append_lookup_relation(
        cs,
        &[address_aligned_high.get_variable()],
        TableType::RomAddressSpaceSeparator.to_num(),
        exec_flag,
    );
    // this one is also aligned
    let rom_address = address_aligned_low.clone()
        + Term::from((F::from_u64_unchecked(1 << 16), address_high_bits_for_rom));

    let [rom_value_low, rom_value_high] = optimization_context
        .append_lookup_relation_from_linear_terms(
            cs,
            &[rom_address],
            TableType::RomRead.to_num(),
            exec_flag,
        );

    // no range check is needed here, as our RAM is consistent by itself - our writes(!) are range-checked,
    // so any reads will have to be range-checked
    let ram_result = Register::new_unchecked_from_placeholder(cs, Placeholder::MemSlot);
    // If it is not RAM query, we should mask is as x0 register access,
    // with a corresponding value

    let ram_result_masked_low = cs.add_variable_from_constraint(
        Term::from(is_ram_range) * Term::from(ram_result.0[0].get_variable()),
    );
    let ram_result_masked_high = cs.add_variable_from_constraint(
        Term::from(is_ram_range) * Term::from(ram_result.0[1].get_variable()),
    );

    let ram_address_masked_low =
        cs.add_variable_from_constraint(address_aligned_low * Term::from(is_ram_range));
    let ram_address_masked_high = cs.add_variable_from_constraint(
        Term::from(is_ram_range) * Term::from(address_aligned_high.get_variable()),
    );

    // TODO: it is linear, so we can postpone making a variable towards merging

    let is_register = cs.add_variable_from_constraint_allow_explicit_linear(
        Term::from(1) - Term::from(is_ram_range),
    );

    let query_type = ShuffleRamQueryType::RegisterOrRam {
        is_register: Boolean::Is(is_register),
        address: [ram_address_masked_low, ram_address_masked_high],
    };

    let query = ShuffleRamMemQuery {
        query_type,
        local_timestamp_in_cycle,
        read_value: [ram_result_masked_low, ram_result_masked_high],
        write_value: [ram_result_masked_low, ram_result_masked_high],
    };

    // and here we have to quasy-choose between value from ROM and RAM queries, and in the path we take
    // we also know that value is range-checked, otherwise it is not important
    let result_low = cs.add_variable_from_constraint(
        Term::from(is_ram_range) * Term::from(ram_result_masked_low)
            + (Term::from(1) - Term::from(is_ram_range)) * Term::from(rom_value_low),
    );
    let result_high = cs.add_variable_from_constraint(
        Term::from(is_ram_range) * Term::from(ram_result_masked_high)
            + (Term::from(1) - Term::from(is_ram_range)) * Term::from(rom_value_high),
    );

    let result = Register([Num::Var(result_low), Num::Var(result_high)]);

    (result, query, is_ram_range)
}

pub(crate) fn read_opcode_from_rom<
    F: PrimeField,
    C: Circuit<F>,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    cs: &mut C,
    pc: Register<F>,
) -> Register<F> {
    // we implement read via lookup, and we need to ensure that
    // PC is in range, but checking that high half of PC only has lower bits
    assert!(16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS <= F::CHAR_BITS - 1);

    let [is_ram_range, rom_address_low] = cs.get_variables_from_lookup_constrained(
        &[LookupInput::from(pc.0[1].get_variable())],
        TableType::RomAddressSpaceSeparator,
    );
    // assert that we only read opcodes from ROM, so "is RAM" is always false here
    cs.add_constraint_allow_explicit_linear(Constraint::<F>::from(is_ram_range));
    let rom_address_constraint = Term::from(pc.0[0].get_variable())
        + Term::from((F::from_u64_unchecked(1 << 16), rom_address_low));

    let [low, high] = cs.get_variables_from_lookup_constrained(
        &[LookupInput::from(rom_address_constraint)],
        TableType::RomRead,
    );

    let result = Register([Num::Var(low), Num::Var(high)]);

    result
}

#[allow(dead_code)]
pub(crate) fn get_register_op_as_shuffle_ram<F: PrimeField, C: Circuit<F>>(
    cs: &mut C,
    reg_encoding: Num<F>,
    bytecode_is_in_rom_only: bool,
    is_first: bool,
) -> (Register<F>, ShuffleRamMemQuery) {
    // NOTE: since we use a value from read set, it means we do not need range check
    let (mut local_timestamp_in_cycle, placeholder) = if is_first {
        (0, Placeholder::FirstRegMem)
    } else {
        (1, Placeholder::SecondRegMem)
    };
    if bytecode_is_in_rom_only == false {
        local_timestamp_in_cycle += 1;
    }
    // no range check is needed here, as our RAM is consistent by itself - our writes(!) are range-checked,
    // so any reads will have to be range-checked
    let value = Register::new_unchecked_from_placeholder::<C>(cs, placeholder);

    // registers live in their separate address space
    let query = form_mem_op_for_register_only(local_timestamp_in_cycle, reg_encoding, value, value);

    (value, query)
}

#[allow(dead_code)]
pub(crate) fn get_rs1_as_shuffle_ram<F: PrimeField, C: Circuit<F>>(
    cs: &mut C,
    reg_encoding: Num<F>,
    bytecode_is_in_rom_only: bool,
) -> (Register<F>, ShuffleRamMemQuery) {
    // NOTE: since we use a value from read set, it means we do not need range check
    let (mut local_timestamp_in_cycle, placeholder) = (0, Placeholder::FirstRegMem);
    if bytecode_is_in_rom_only == false {
        local_timestamp_in_cycle += 1;
    }

    // no range check is needed here, as our RAM is consistent by itself - our writes(!) are range-checked,
    // so any reads will have to be range-checked
    let value = Register::new_unchecked_from_placeholder::<C>(cs, placeholder);

    // registers live in their separate address space
    let query = form_mem_op_for_register_only(local_timestamp_in_cycle, reg_encoding, value, value);

    (value, query)
}

pub(crate) fn get_rs2_as_shuffle_ram<F: PrimeField, C: Circuit<F>>(
    cs: &mut C,
    reg_encoding: Num<F>,
    bytecode_is_in_rom_only: bool,
) -> (Register<F>, ShuffleRamMemQuery) {
    // NOTE: since we use a value from read set, it means we do not need range check
    let (mut local_timestamp_in_cycle, placeholder) =
        (RS2_LOAD_LOCAL_TIMESTAMP, Placeholder::SecondRegMem);
    if bytecode_is_in_rom_only == false {
        local_timestamp_in_cycle += 1;
    }

    // no range check is needed here, as our RAM is consistent by itself - our writes(!) are range-checked,
    // so any reads will have to be range-checked
    let value = Register::new_unchecked_from_placeholder::<C>(cs, placeholder);

    // registers live in their separate address space
    let query = form_mem_op_for_register_only(local_timestamp_in_cycle, reg_encoding, value, value);

    (value, query)
}

pub(crate) fn set_rd_with_mask_as_shuffle_ram<F: PrimeField, C: Circuit<F>>(
    cs: &mut C,
    reg_encoding: Num<F>,
    write_value: Register<F>,
    reg_is_x0: Boolean,
    bytecode_is_in_rom_only: bool,
) -> ShuffleRamMemQuery {
    let local_timestamp_in_cycle = if bytecode_is_in_rom_only {
        RD_STORE_LOCAL_TIMESTAMP
    } else {
        RD_STORE_LOCAL_TIMESTAMP + 1
    };
    let read_value =
        Register::new_unchecked_from_placeholder(cs, Placeholder::WriteRdReadSetWitness);
    let masked_write_value = write_value.mask(cs, reg_is_x0.toggle());
    let query = form_mem_op_for_register_only(
        local_timestamp_in_cycle,
        reg_encoding,
        read_value,
        masked_write_value,
    );

    query
}

pub(crate) fn set_rd_without_mask_as_shuffle_ram<F: PrimeField, C: Circuit<F>>(
    cs: &mut C,
    reg_encoding: Num<F>,
    write_value: Register<F>,
    bytecode_is_in_rom_only: bool,
) -> ShuffleRamMemQuery {
    let local_timestamp_in_cycle = if bytecode_is_in_rom_only {
        RD_STORE_LOCAL_TIMESTAMP
    } else {
        RD_STORE_LOCAL_TIMESTAMP + 1
    };
    let read_value =
        Register::new_unchecked_from_placeholder(cs, Placeholder::WriteRdReadSetWitness);
    let query = form_mem_op_for_register_only(
        local_timestamp_in_cycle,
        reg_encoding,
        read_value,
        write_value,
    );
    query
}

#[allow(dead_code)]
pub(crate) struct RS2ShuffleRamQueryCandidate<F: PrimeField> {
    pub(crate) rs2: Constraint<F>,
    pub(crate) local_timestamp_in_cycle: usize,
    pub(crate) read_value: [Variable; REGISTER_SIZE],
}

#[allow(dead_code)]
pub(crate) fn prepare_rs2_op_as_shuffle_ram<F: PrimeField, C: Circuit<F>>(
    cs: &mut C,
    rs2_constraint: Constraint<F>,
    bytecode_is_in_rom_only: bool,
) -> (Register<F>, RS2ShuffleRamQueryCandidate<F>) {
    // NOTE: since we use a value from read set, it means we do not need range check
    let (mut local_timestamp_in_cycle, placeholder) = (1, Placeholder::SecondRegMem);
    if bytecode_is_in_rom_only == false {
        local_timestamp_in_cycle += 1;
    }

    // no range check is needed here, as our RAM is consistent by itself - our writes(!) are range-checked,
    // so any reads will have to be range-checked
    let value = Register::new_unchecked_from_placeholder::<C>(cs, placeholder);

    // here we should manually form temporary holder
    let query = RS2ShuffleRamQueryCandidate {
        rs2: rs2_constraint,
        local_timestamp_in_cycle,
        read_value: value.0.map(|el| el.get_variable()),
    };

    (value, query)
}

#[allow(dead_code)]
pub(crate) fn update_register_op_as_shuffle_ram<F: PrimeField, C: Circuit<F>>(
    cs: &mut C,
    local_timestamp_in_cycle: usize,
    reg_encoding: Num<F>,
    reg_value: Register<F>,
    execute_register_update: Boolean,
    memory_store_query_to_merge: ShuffleRamMemQuery,
    execute_memory_store: Boolean,
) -> ShuffleRamMemQuery {
    assert_eq!(
        local_timestamp_in_cycle,
        memory_store_query_to_merge.local_timestamp_in_cycle
    );

    // if we will not update register and do not execute memory store, then
    // we still want to model it as reading x0 (and writing back hardcoded 0)

    let reg_is_zero = cs.is_zero(reg_encoding);
    // we ALWAYS write to register (with maybe modified value), unless we write to RAM

    // But if we do NOT need to execute register update, OR if dst register is x0, then we must mask a value
    let mask_value_to_zero = Boolean::or(&execute_register_update.toggle(), &reg_is_zero, cs);
    // if we write to x0, then we will write 0
    let reg_write_value = reg_value.mask(cs, mask_value_to_zero.toggle());

    // no range check is needed here, as our RAM is consistent by itself - our writes(!) are range-checked,
    // so any reads will have to be range-checked
    let reg_read_value =
        Register::new_unchecked_from_placeholder(cs, Placeholder::WriteRdReadSetWitness);

    // registers live in their separate address space, so we just choose here, and default to 0
    // - no register update, no store -> address 0
    // - register update, no store -> reg index in low
    // - store, no register update -> RAM address

    let ShuffleRamQueryType::RegisterOrRam {
        is_register: _,
        address: ram_query_address,
    } = memory_store_query_to_merge.query_type
    else {
        panic!("we expect query to merge to be RAM")
    };

    let addr_low = cs.add_variable_from_constraint(
        (Term::from(reg_encoding) * Term::from(execute_register_update)) // register
        + (Term::from(ram_query_address[0]) * Term::from(execute_memory_store)), // RAM
    );
    let addr_high = cs.add_variable_from_constraint(
        Term::from(ram_query_address[1]) * Term::from(execute_memory_store),
    );

    let is_register = Boolean::choose(
        cs,
        &execute_memory_store,
        &Boolean::Constant(false),
        &Boolean::Constant(true),
    );
    let query_type = ShuffleRamQueryType::RegisterOrRam {
        is_register,
        address: [addr_low, addr_high],
    };

    let mut query = memory_store_query_to_merge;
    query.query_type = query_type;
    query.read_value = std::array::from_fn(|i| {
        cs.choose(
            execute_memory_store,
            Num::Var(query.read_value[i]),
            reg_read_value.0[i],
        )
        .get_variable()
    });
    query.write_value = std::array::from_fn(|i| {
        cs.choose(
            execute_memory_store,
            Num::Var(query.write_value[i]),
            reg_write_value.0[i],
        )
        .get_variable()
    });

    query
}

pub fn form_mem_op_for_register_only<F: PrimeField>(
    local_timestamp_in_cycle: usize,
    reg_idx: Num<F>,
    read_value: Register<F>,
    write_value: Register<F>,
) -> ShuffleRamMemQuery {
    ShuffleRamMemQuery {
        query_type: ShuffleRamQueryType::RegisterOnly {
            register_index: reg_idx.get_variable(),
        },
        local_timestamp_in_cycle,
        read_value: read_value.0.map(|el| el.get_variable()),
        write_value: write_value.0.map(|el| el.get_variable()),
    }
}

pub fn get_sign_bit_from_orthogonal_terms<F: PrimeField, CS: Circuit<F>, const N: usize>(
    cs: &mut CS,
    orthoflags: [Boolean; N],
    orthoxs: [Variable; N],
) -> Boolean {
    let underflow = cs.add_boolean_variable();
    let out = cs.add_variable_with_range_check(16);

    let value_vars = orthoflags
        .iter()
        .zip(orthoxs.iter())
        .map(|(&b, &x)| (b, x))
        .collect::<Vec<(Boolean, Variable)>>();
    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        use crate::cs::witness_placer::*;
        let mut input_v = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0);
        for (b, x) in &value_vars {
            let b_v = placer.get_boolean(b.get_variable().unwrap());
            let x_v = placer.get_u16(*x);
            input_v.assign_masked(&b_v, &x_v);
        }
        let highest_v = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(1 << 15);
        let (out_v, underflow_v) = input_v.overflowing_sub(&highest_v);
        placer.assign_mask(underflow.get_variable().unwrap(), &underflow_v);
        placer.assign_u16(out.get_variable(), &out_v);
    };
    cs.set_values(value_fn);

    let mut input = Constraint::empty();
    for (&b, &x) in orthoflags.iter().zip(orthoxs.iter()) {
        input = input + Term::from(b) * Term::from(x);
    }
    cs.add_constraint(
        (input - Term::from(1 << 15))
            - (Constraint::from(out) - Term::from(1 << 16) * Term::from(underflow)),
    );
    underflow.toggle()
}

pub fn get_sign_bit_masked<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    x: Variable,
    mask: Boolean,
) -> Boolean {
    let not_underflow = cs.add_boolean_variable();
    let underflow = not_underflow.toggle();
    let out = cs.add_variable_with_range_check(16);

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        use crate::cs::witness_placer::*;
        let x_v = placer.get_u16(x);
        let mask_v = match mask {
            Boolean::Is(var) => placer.get_boolean(var),
            Boolean::Not(var) => placer.get_boolean(var).negate(),
            Boolean::Constant(c) => {
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(c)
            }
        };
        let (out_v_masked, underflow_v_masked) = {
            let highest_v = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(1 << 15);
            let (out_v, underflow_v) = x_v.overflowing_sub(&highest_v);
            let out_v_masked =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::select(&mask_v, &out_v, &x_v);
            let underflow_v_masked = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                &mask_v,
                &underflow_v,
                &mask_v.negate(),
            );
            (out_v_masked, underflow_v_masked)
        };
        let not_underflow_v_masked = underflow_v_masked.negate();
        placer.assign_mask(
            not_underflow.get_variable().unwrap(),
            &not_underflow_v_masked,
        );
        placer.assign_u16(out.get_variable(), &out_v_masked);
    };
    cs.set_values(value_fn);

    cs.add_constraint_allow_explicit_linear(
        (Constraint::from(x)
            - Term::from(1 << 15) * Constraint::from(mask)
            - Term::from(1 << 16) * Constraint::from(mask.toggle()))
            - (Constraint::from(out) - Term::from(1 << 16) * Constraint::from(underflow)),
    );
    underflow.toggle()
}

pub fn get_reg_add_and_overflow<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    a: Register<F>,
    b: Register<F>,
) -> (Register<F>, Boolean) {
    let c = Register::new(cs);
    // We do not need to make intermediate carry at all, so we can just re-express it
    // as constraint, and require booleanity
    let of = Boolean::new(cs);

    let [a_low, a_high] = a.0.map(|x| x.get_variable());
    let [b_low, b_high] = b.0.map(|x| x.get_variable());
    let [c_low, c_high] = c.0.map(|x| x.get_variable());
    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        use crate::cs::witness_placer::*;
        let a_value = placer.get_u32_from_u16_parts([a_low, a_high]);
        let b_value = placer.get_u32_from_u16_parts([b_low, b_high]);

        let (c_value, of_value) = a_value.overflowing_add(&b_value);
        placer.assign_u32_from_u16_parts([c_low, c_high], &c_value);
        placer.assign_mask(of.get_variable().unwrap(), &of_value);
    };
    cs.set_values(value_fn);

    let mut carry_constraint = Constraint::from(a_low) + Term::from(b_low) - Term::from(c_low);
    carry_constraint.scale(F::from_u64_unchecked(1 << 16).inverse().unwrap());

    let bool_constraint = carry_constraint.clone() * (carry_constraint.clone() - Term::from(1));
    cs.add_constraint(bool_constraint);

    cs.add_constraint_allow_explicit_linear(
        carry_constraint + Term::from(a_high) + Term::from(b_high)
            - (Constraint::from(c_high) + Term::from(1 << 16) * Term::from(of)),
    );
    (c, of)
}

pub fn get_reg_sub_and_underflow<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    a: Register<F>,
    b: Register<F>,
) -> (Register<F>, Boolean) {
    let c = Register::new(cs);
    // We do not need to make intermediate carry at all, so we can just re-express it
    // as constraint, and require booleanity
    let uf = Boolean::new(cs);

    let [a_low, a_high] = a.0.map(|x| x.get_variable());
    let [b_low, b_high] = b.0.map(|x| x.get_variable());
    let [c_low, c_high] = c.0.map(|x| x.get_variable());
    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        use crate::cs::witness_placer::*;
        let a_value = placer.get_u32_from_u16_parts([a_low, a_high]);
        let b_value = placer.get_u32_from_u16_parts([b_low, b_high]);

        let (c_value, uf_value) = a_value.overflowing_sub(&b_value);
        placer.assign_u32_from_u16_parts([c_low, c_high], &c_value);
        placer.assign_mask(uf.get_variable().unwrap(), &uf_value);
    };
    cs.set_values(value_fn);

    // a - b == c - 2^16 uf --> 2^16 uf == c - a + b
    let mut carry_constraint = Constraint::from(c_low) - Term::from(a_low) + Term::from(b_low);
    carry_constraint.scale(F::from_u64_unchecked(1 << 16).inverse().unwrap());

    let bool_constraint = carry_constraint.clone() * (carry_constraint.clone() - Term::from(1));
    cs.add_constraint(bool_constraint);

    cs.add_constraint_allow_explicit_linear(
        Constraint::from(a_high)
            - Term::from(b_high)
            - carry_constraint
            - (Constraint::from(c_high) - Term::from(1 << 16) * Term::from(uf)),
    );
    (c, uf)
}

pub fn choose_reg_add_sub_and_overflow<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    is_add: Boolean,
    a: Register<F>,
    b: Register<F>,
) -> (Register<F>, Boolean) {
    let c = Register::new(cs);
    let of_low = Boolean::new(cs);
    let of_high = Boolean::new(cs);

    let [a_low, a_high] = a.0.map(|x| x.get_variable());
    let [b_low, b_high] = b.0.map(|x| x.get_variable());
    let [c_low, c_high] = c.0.map(|x| x.get_variable());
    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        use crate::cs::witness_placer::*;
        let is_add_value = match is_add {
            Boolean::Is(var) => placer.get_boolean(var),
            Boolean::Not(var) => placer.get_boolean(var).negate(),
            Boolean::Constant(c) => {
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(c)
            }
        };
        let a_low_value = placer.get_u16(a_low);
        let b_low_value = placer.get_u16(b_low);
        let (c_low_value, of_low_value) = {
            let (cadd_low_value, ofadd_low_value) = a_low_value.overflowing_add(&b_low_value);
            let (csub_low_value, ofsub_low_value) = a_low_value.overflowing_sub(&b_low_value);
            let c_low_value = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                &is_add_value,
                &cadd_low_value,
                &csub_low_value,
            );
            let of_low_value =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                    &is_add_value,
                    &ofadd_low_value,
                    &ofsub_low_value,
                ); // bit ridiculous
            (c_low_value, of_low_value)
        };
        let a_high_value = placer.get_u16(a_high);
        let b_high_value = placer.get_u16(b_high);
        let (c_high_value, of_high_value) = {
            let (cadd_high_value, ofadd_high_value) =
                a_high_value.overflowing_add_with_carry(&b_high_value, &of_low_value);
            let (csub_high_value, ofsub_high_value) =
                a_high_value.overflowing_sub_with_borrow(&b_high_value, &of_low_value);
            let c_high_value =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                    &is_add_value,
                    &cadd_high_value,
                    &csub_high_value,
                );
            let of_high_value =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                    &is_add_value,
                    &ofadd_high_value,
                    &ofsub_high_value,
                ); // bit ridiculous
            (c_high_value, of_high_value)
        };
        placer.assign_u16(c_low, &c_low_value);
        placer.assign_u16(c_high, &c_high_value);
        placer.assign_mask(of_low.get_variable().unwrap(), &of_low_value);
        placer.assign_mask(of_high.get_variable().unwrap(), &of_high_value);
    };
    cs.set_values(value_fn);

    let is_sub = is_add.toggle();
    cs.add_constraint(
        Constraint::from(is_add) * Term::from(a_low)
            + Constraint::from(is_sub) * Term::from(c_low)
            + Term::from(b_low)
            - (Constraint::from(is_add) * Term::from(c_low)
                + Constraint::from(is_sub) * Term::from(a_low)
                + Term::from(1 << 16) * Term::from(of_low)),
    );
    cs.add_constraint(
        Constraint::from(is_add) * Term::from(a_high)
            + Constraint::from(is_sub) * Term::from(c_high)
            + Term::from(b_high)
            + Term::from(of_low)
            - (Constraint::from(is_add) * Term::from(c_high)
                + Constraint::from(is_sub) * Term::from(a_high)
                + Term::from(1 << 16) * Term::from(of_high)),
    );
    (c, of_high)
}
