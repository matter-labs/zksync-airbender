use super::decoder::ReducedMachineDecoder;
use super::*;
use crate::machine::machine_configurations::BasicDecodingResultWithSigns;

pub fn reduced_machine_tables() -> Vec<TableType> {
    use crate::machine::machine_configurations::minimal_no_exceptions_with_delegation::MinimalMachineNoExceptionHandlingWithDelegation;
    use crate::machine::Machine;
    use field::Mersenne31Field;

    // these get dynamically allocated by instance of the circuit depending on the machine configuration
    //      TableType::RomAddressSpaceSeparator,
    //      TableType::RomRead,

    let mut result = vec![TableType::ZeroEntry, TableType::U16GetSignAndHighByte];

    result.extend(
        <MinimalMachineNoExceptionHandlingWithDelegation as Machine<Mersenne31Field>>::define_used_tables()
    );

    result
}

const ASSUME_TRUSTED_CODE: bool = true;
const OUTPUT_EXACT_EXCEPTIONS: bool = false;
const PERFORM_DELEGATION: bool = true;

pub fn reduced_machine_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    for el in reduced_machine_tables() {
        cs.materialize_table(el);
    }
}

pub fn reduced_machine_table_driver_fn<F: PrimeField>(table_driver: &mut TableDriver<F>) {
    for el in reduced_machine_tables() {
        table_driver.materialize_table(el);
    }
}

pub fn create_reduced_machine_special_tables<
    F: PrimeField,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    bytecode: &[u32],
    delegation_csrs: &[u32],
) -> [(TableType, LookupWrapper<F>); 3] {
    use crate::machine::machine_configurations::create_csr_table_for_delegation;
    use crate::machine::machine_configurations::create_table_for_rom_image;
    use crate::tables::create_rom_separator_table;

    // machine.define_additional_tables();

    let id = TableType::RomAddressSpaceSeparator.to_table_id();
    let rom_separator_table = LookupWrapper::Dimensional3(create_rom_separator_table::<
        F,
        ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
    >(id));

    let id = TableType::RomRead.to_table_id();
    let bytecode_words_table = LookupWrapper::Dimensional3(create_table_for_rom_image::<
        F,
        ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
    >(bytecode, id));

    let id = TableType::SpecialCSRProperties.to_table_id();
    let csr_table =
        LookupWrapper::Dimensional3(create_csr_table_for_delegation(true, delegation_csrs, id));

    [
        (TableType::RomAddressSpaceSeparator, rom_separator_table),
        (TableType::RomRead, bytecode_words_table),
        (TableType::SpecialCSRProperties, csr_table),
    ]
}

pub fn reduced_machine_circuit_with_preprocessed_bytecode<
    F: PrimeField,
    CS: Circuit<F>,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    cs: &mut CS,
) {
    let input = cs.allocate_execution_circuit_state::<true>();
    apply_reduced_machine_circuit::<_, _, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(cs, input);
}

fn apply_reduced_machine_circuit<
    F: PrimeField,
    CS: Circuit<F>,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
) {
    let (decoder_bits, decoder_output, memory_queries, start_pc) =
        get_initial_data_for_execution(cs, inputs);

    let flags_source = decoder_bits.get_flag_source();

    use crate::machine::machine_configurations::minimal_state::MinimalStateRegistersInMemory;
    let initial_state = MinimalStateRegistersInMemory { pc: start_pc };

    let mut opt_ctx = OptimizationContext::<F, CS>::new();
    cs.set_log(&opt_ctx, "DECODER");

    let mut application_results = Vec::<CommonDiffs<F>>::with_capacity(32);

    let application_result = AddOp::apply::<_, ASSUME_TRUSTED_CODE, OUTPUT_EXACT_EXCEPTIONS>(
        cs,
        &initial_state,
        &decoder_output,
        &flags_source,
        &mut opt_ctx,
    );
    application_results.push(application_result);
    cs.set_log(&opt_ctx, "ADD");

    let application_result = SubOp::apply::<_, ASSUME_TRUSTED_CODE, OUTPUT_EXACT_EXCEPTIONS>(
        cs,
        &initial_state,
        &decoder_output,
        &flags_source,
        &mut opt_ctx,
    );
    application_results.push(application_result);
    cs.set_log(&opt_ctx, "SUB");

    let application_result = LuiOp::apply::<_, ASSUME_TRUSTED_CODE, OUTPUT_EXACT_EXCEPTIONS>(
        cs,
        &initial_state,
        &decoder_output,
        &flags_source,
        &mut opt_ctx,
    );
    application_results.push(application_result);
    cs.set_log(&opt_ctx, "LUI");

    let application_result = AuiPc::apply::<_, ASSUME_TRUSTED_CODE, OUTPUT_EXACT_EXCEPTIONS>(
        cs,
        &initial_state,
        &decoder_output,
        &flags_source,
        &mut opt_ctx,
    );
    application_results.push(application_result);
    cs.set_log(&opt_ctx, "AUIPC");

    let application_result = BinaryOp::apply::<_, ASSUME_TRUSTED_CODE, OUTPUT_EXACT_EXCEPTIONS>(
        cs,
        &initial_state,
        &decoder_output,
        &flags_source,
        &mut opt_ctx,
    );
    application_results.push(application_result);
    cs.set_log(&opt_ctx, "BINARY");

    let application_result =
        ConditionalOp::<true>::apply::<_, ASSUME_TRUSTED_CODE, OUTPUT_EXACT_EXCEPTIONS>(
            cs,
            &initial_state,
            &decoder_output,
            &flags_source,
            &mut opt_ctx,
        );
    application_results.push(application_result);
    cs.set_log(&opt_ctx, "CONDITIONAL");

    let application_result =
        ShiftOp::<true, false>::apply::<_, ASSUME_TRUSTED_CODE, OUTPUT_EXACT_EXCEPTIONS>(
            cs,
            &initial_state,
            &decoder_output,
            &flags_source,
            &mut opt_ctx,
        );
    application_results.push(application_result);
    cs.set_log(&opt_ctx, "SHIFT_SRA_ROT");

    let application_result = JumpOp::apply::<_, ASSUME_TRUSTED_CODE, OUTPUT_EXACT_EXCEPTIONS>(
        cs,
        &initial_state,
        &decoder_output,
        &flags_source,
        &mut opt_ctx,
    );
    application_results.push(application_result);
    cs.set_log(&opt_ctx, "JUMP");

    let application_result = MopOp::apply::<_, ASSUME_TRUSTED_CODE, OUTPUT_EXACT_EXCEPTIONS>(
        cs,
        &initial_state,
        &decoder_output,
        &flags_source,
        &mut opt_ctx,
    );
    application_results.push(application_result);
    cs.set_log(&opt_ctx, "MOP");

    let [rs1_query, mut rs2_or_mem_load_query, mut rd_or_mem_store_query] = memory_queries;

    let application_result = LoadOp::<false, false>::spec_apply::<
        _,
        _,
        _,
        _,
        _,
        _,
        ASSUME_TRUSTED_CODE,
        OUTPUT_EXACT_EXCEPTIONS,
    >(
        cs,
        &initial_state,
        &decoder_output,
        &flags_source,
        &mut rs2_or_mem_load_query,
        &mut opt_ctx,
    );
    application_results.push(application_result);
    cs.set_log(&opt_ctx, "LOAD");

    let application_result = StoreOp::<false>::spec_apply::<
        _,
        _,
        _,
        _,
        _,
        _,
        ASSUME_TRUSTED_CODE,
        OUTPUT_EXACT_EXCEPTIONS,
    >(
        cs,
        &initial_state,
        &decoder_output,
        &flags_source,
        &mut rd_or_mem_store_query,
        &mut opt_ctx,
    );
    application_results.push(application_result);
    cs.set_log(&opt_ctx, "STORE");

    if PERFORM_DELEGATION == false {
        // CSR operation must be hand implemented for most of the machines, even though we can declare support of it in the opcode
        let application_result = apply_non_determinism_csr_only_assuming_no_unimp::<
            _,
            _,
            _,
            _,
            _,
            _,
            false,
            false,
            false,
            ASSUME_TRUSTED_CODE,
            OUTPUT_EXACT_EXCEPTIONS,
        >(
            cs,
            &initial_state,
            &decoder_output,
            &flags_source,
            &mut opt_ctx,
        );
        application_results.push(application_result);
    } else {
        let application_result = apply_csr_with_delegation::<
            _,
            _,
            _,
            _,
            _,
            _,
            false,
            false,
            false,
            ASSUME_TRUSTED_CODE,
            OUTPUT_EXACT_EXCEPTIONS,
        >(
            cs,
            &initial_state,
            &decoder_output,
            &flags_source,
            &mut opt_ctx,
        );
        application_results.push(application_result);
    };
    cs.set_log(&opt_ctx, "CSR");

    // finish with optimizer, as we do not have any "branching" below
    opt_ctx.enforce_all(cs);
    // drop(opt_ctx);

    final_state_check(
        cs,
        inputs,
        decoder_bits,
        rs1_query,
        rs2_or_mem_load_query,
        rd_or_mem_store_query,
        application_results,
        decoder_output.pc_next,
        &opt_ctx,
    );
}

fn get_initial_data_for_execution<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
) -> (
    ReducedMachineCircuitMask,
    BasicDecodingResultWithSigns<F>,
    [ShuffleRamMemQuery; 3],
    Register<F>,
) {
    let decoder_bits = <ReducedMachineDecoder as OpcodeFamilyDecoder>::BitmaskCircuitParser::parse(
        cs,
        inputs.decoder_data.circuit_family_extra_mask,
    );

    let use_rs2_flag = decoder_bits.get_use_rs2_flag();

    // just to reuse existing code
    let start_pc = Register(inputs.cycle_start_state.pc.map(|el| Num::Var(el)));

    let mut memory_queries = vec![];

    let rs1_value = {
        // RS1 is always register
        // NOTE: since we use a value from read set, it means we do not need range check
        let (local_timestamp_in_cycle, placeholder) = (
            RS1_LOAD_LOCAL_TIMESTAMP,
            Placeholder::ShuffleRamReadValue(0),
        );

        // no range check is needed here, as our RAM is consistent by itself - our writes(!) are range-checked,
        // so any reads will have to be range-checked
        let value = Register::new_unchecked_from_placeholder(cs, placeholder);

        // registers live in their separate address space
        let query = form_mem_op_for_register_only(
            local_timestamp_in_cycle,
            Num::Var(inputs.decoder_data.rs1_index),
            value,
            value,
        );
        memory_queries.push(query);

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

        value
    };

    // RS2 is merged with mem LOAD, and it's always placed into memory columns, so we can just allocate is_register as non-determinate placeholder,
    // and then modify
    let rs2_value_if_register = {
        // NOTE: since we use a value from read set, it means we do not need range check
        let (local_timestamp_in_cycle, placeholder) = (
            RS2_LOAD_LOCAL_TIMESTAMP,
            Placeholder::ShuffleRamReadValue(1),
        );

        // no range check is needed here, as our RAM is consistent by itself - our writes(!) are range-checked,
        // so any reads will have to be range-checked
        let value = Register::new_unchecked_from_placeholder(cs, placeholder);
        let read_address =
            Register::new_unchecked_from_placeholder(cs, Placeholder::ShuffleRamAddress(1));

        let query = ShuffleRamMemQuery {
            query_type: ShuffleRamQueryType::RegisterOrRam {
                is_register: Boolean::Constant(true),
                // is_register: decoder_bits.get_rs2_query_is_register_flag(),
                address: read_address.0.map(|el| el.get_variable()),
            },
            local_timestamp_in_cycle,
            read_value: value.0.map(|el| el.get_variable()),
            write_value: value.0.map(|el| el.get_variable()),
        };
        memory_queries.push(query);

        value
    };

    // and we can right away prepare RD/STORE query
    {
        let local_timestamp_in_cycle = RD_STORE_LOCAL_TIMESTAMP;
        // no range check is needed here, as our RAM is consistent by itself - our writes(!) are range-checked,
        // so any reads will have to be range-checked
        let read_value =
            Register::new_unchecked_from_placeholder(cs, Placeholder::ShuffleRamReadValue(2));
        // Also unchecked, as it would be constrained in STORE opcode, or at the end of the cycle
        let write_value =
            Register::new_unchecked_from_placeholder(cs, Placeholder::ShuffleRamWriteValue(2));

        let read_address =
            Register::new_unchecked_from_placeholder(cs, Placeholder::ShuffleRamAddress(2));

        let query = ShuffleRamMemQuery {
            query_type: ShuffleRamQueryType::RegisterOrRam {
                is_register: Boolean::Constant(true),
                // is_register: decoder_bits.get_rd_query_is_register_flag(),
                address: read_address.0.map(|el| el.get_variable()),
            },
            local_timestamp_in_cycle,
            read_value: read_value.0.map(|el| el.get_variable()),
            write_value: write_value.0.map(|el| el.get_variable()),
        };
        memory_queries.push(query);
    }

    let src1 = rs1_value;

    let imm = Register(inputs.decoder_data.imm.map(|el| Num::Var(el)));
    let src2 = Register::choose(cs, &use_rs2_flag, &rs2_value_if_register, &imm);

    // now with PC considered range-checked we can compute next PC without overflows
    let default_pc_next = Register::new_unchecked(cs);
    bump_pc_no_range_checks_explicit(cs, start_pc, default_pc_next);

    let src1 = RegisterDecompositionWithSign::parse_reg(cs, src1);
    let src2 = RegisterDecompositionWithSign::parse_reg(cs, src2);

    let rs2_index: Constraint<F> = inputs.decoder_data.rs2_index.into();

    let decoder_output = BasicDecodingResultWithSigns {
        pc_next: default_pc_next,
        src1,
        src2,
        rs2_index,
        imm,
        funct3: Num::Var(inputs.decoder_data.funct3),
        funct12: inputs.decoder_data.imm[0].into(), // We use imm as funct12 for RType
    };

    (
        decoder_bits,
        decoder_output,
        memory_queries.try_into().unwrap(),
        start_pc,
    )
}

fn final_state_check<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    decoder_bits: ReducedMachineCircuitMask,
    rs1_query: ShuffleRamMemQuery,
    rs2_or_mem_load_query: ShuffleRamMemQuery,
    rd_or_mem_store_query: ShuffleRamMemQuery,
    application_results: Vec<CommonDiffs<F>>,
    default_next_pc: Register<F>,
    opt_ctx: &OptimizationContext<F, CS>,
) {
    // now it's time to merge state
    if application_results.iter().all(|el| el.trapped.is_none()) {
        // there are no traps in opcodes support,
        // we can just apply state updates

        {
            let ShuffleRamQueryType::RegisterOrRam { is_register, .. } =
                rd_or_mem_store_query.query_type
            else {
                unreachable!()
            };
            let Boolean::Is(..) = is_register else {
                panic!("Memory opcode must resolve RS2/LOAD query `is_register` flag");
            };
        }

        // we do not care about predicating state updates below, because if trap happens it's already unsatisfiable circuit

        let new_reg_val = CommonDiffs::select_final_rd_value(cs, &application_results);

        // if we will not update register and do not execute memory store, then
        // we still want to model it as reading x0 (and writing back hardcoded 0)

        let rd = inputs.decoder_data.rd_index;
        let reg_is_zero = inputs.decoder_data.rd_is_zero;
        // we ALWAYS write to register (with maybe modified value), unless we write to RAM, except for B-format opcodes (
        // that are modeled as write 0 to x0)

        // Mask to get 0s if we write into x0
        let reg_write_value_low = cs.add_variable_from_constraint(
            (Term::from(1) - Term::from(reg_is_zero)) * Term::from(new_reg_val.0[0]),
        );
        let reg_write_value_high = cs.add_variable_from_constraint(
            (Term::from(1) - Term::from(reg_is_zero)) * Term::from(new_reg_val.0[1]),
        );

        // now constraint that if we do update register, then address is correct
        let ShuffleRamQueryType::RegisterOrRam {
            is_register,
            address,
        } = rd_or_mem_store_query.query_type
        else {
            unreachable!()
        };
        let Boolean::Is(..) = is_register else {
            panic!("Memory opcode must resolve RD/STORE query `is_register` flag");
        };

        let update_rd_flag = decoder_bits.get_update_rd_flag();
        let b_instruction_flag = decoder_bits.get_b_instruction_flag();

        // if we write to RD - we should make a constraint over the address, that it comes from opcode
        cs.add_constraint((Term::from(rd) - Term::from(address[0])) * Term::from(update_rd_flag));
        cs.add_constraint((Term::from(address[1])) * Term::from(update_rd_flag));
        // x0 for BRANCH instructions as it's not even encoded in the opcode
        cs.add_constraint((Term::from(address[0])) * Term::from(b_instruction_flag));
        cs.add_constraint((Term::from(address[1])) * Term::from(b_instruction_flag));

        // and constraint value
        cs.add_constraint(
            (Term::from(reg_write_value_low) - Term::from(rd_or_mem_store_query.write_value[0]))
                * Term::from(update_rd_flag),
        );
        cs.add_constraint(
            (Term::from(reg_write_value_high) - Term::from(rd_or_mem_store_query.write_value[1]))
                * Term::from(update_rd_flag),
        );
        // 0 for BRANCH instructions
        cs.add_constraint(
            (Term::from(rd_or_mem_store_query.write_value[0])) * Term::from(b_instruction_flag),
        );
        cs.add_constraint(
            (Term::from(rd_or_mem_store_query.write_value[1])) * Term::from(b_instruction_flag),
        );

        // push all memory queries
        cs.add_shuffle_ram_query(rs1_query);
        cs.add_shuffle_ram_query(rs2_or_mem_load_query);
        cs.add_shuffle_ram_query(rd_or_mem_store_query);

        let _ = CommonDiffs::select_final_pc_value(
            cs,
            &application_results,
            default_next_pc,
            Some(inputs.cycle_end_state.pc),
        );

        // // enforce that next PC is the one that is a result of selection
        // CommonDiffs::select_final_pc_into(
        //     cs,
        //     &application_results,
        //     default_next_pc,
        //     inputs.cycle_end_state.pc,
        // );

        cs.set_log(&opt_ctx, "EXECUTOR");
    } else {
        todo!()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::utils::serialize_to_file;

    const SECOND_WORD_BITS: usize = 4;
    const DUMMY_BYTECODE: &[u32] = &[UNIMP_OPCODE];

    #[test]
    fn compile_reduced_machine_circuit() {
        use ::field::Mersenne31Field;

        let compiled = compile_unified_circuit_state_transition::<Mersenne31Field>(
            &|cs| {
                reduced_machine_table_addition_fn(cs);

                let extra_tables = create_reduced_machine_special_tables::<_, SECOND_WORD_BITS>(
                    DUMMY_BYTECODE,
                    &[
                        common_constants::NON_DETERMINISM_CSR,
                        BLAKE2S_DELEGATION_CSR_REGISTER,
                    ],
                );
                for (table_type, table) in extra_tables {
                    cs.add_table_with_content(table_type, table);
                }
            },
            &|cs| reduced_machine_circuit_with_preprocessed_bytecode::<_, _, SECOND_WORD_BITS>(cs),
            1 << (16 + SECOND_WORD_BITS),
            23,
        );

        serialize_to_file(&compiled, "reduced_machine_preprocessed_layout.json");
    }

    #[test]
    fn compile_reduced_machine_witness_graph() {
        use ::field::Mersenne31Field;

        let ssa_forms = dump_ssa_witness_eval_form_for_unrolled_circuit::<Mersenne31Field>(
            &|cs| {
                reduced_machine_table_addition_fn(cs);

                let extra_tables = create_reduced_machine_special_tables::<_, SECOND_WORD_BITS>(
                    DUMMY_BYTECODE,
                    &[
                        common_constants::NON_DETERMINISM_CSR,
                        BLAKE2S_DELEGATION_CSR_REGISTER,
                    ],
                );
                for (table_type, table) in extra_tables {
                    cs.add_table_with_content(table_type, table);
                }
            },
            &|cs| reduced_machine_circuit_with_preprocessed_bytecode::<_, _, SECOND_WORD_BITS>(cs),
        );
        serialize_to_file(&ssa_forms, "reduced_machine_preprocessed_ssa.json");
    }
}
