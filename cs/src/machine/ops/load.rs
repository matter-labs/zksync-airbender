use super::*;

pub const LOAD_COMMON_OP_KEY: DecoderMajorInstructionFamilyKey =
    DecoderMajorInstructionFamilyKey("LW/LH/LHU/LB/LBU");
pub const LOAD_WORD_OP_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("LW");
pub const LOAD_HALF_WORD_OP_KEY: DecoderInstructionVariantsKey =
    DecoderInstructionVariantsKey("LH/LHU");
pub const SIGN_EXTEND_ON_LOAD_OP_KEY: DecoderInstructionVariantsKey =
    DecoderInstructionVariantsKey("LB/LW");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LoadOp<const SUPPORT_SIGNED: bool, const SUPPORT_LESS_THAN_WORD: bool>;

impl<const SUPPORT_SIGNED: bool, const SUPPORT_LESS_THAN_WORD: bool> DecodableMachineOp
    for LoadOp<SUPPORT_SIGNED, SUPPORT_LESS_THAN_WORD>
{
    fn define_decoder_subspace(
        &self,
        opcode: u8,
        func3: u8,
        func7: u8,
    ) -> Result<
        (
            InstructionType,
            DecoderMajorInstructionFamilyKey,
            &'static [DecoderInstructionVariantsKey],
        ),
        (),
    > {
        let params = match (opcode, func3, func7) {
            (OPERATION_LOAD, 0b000, _) if SUPPORT_SIGNED & SUPPORT_LESS_THAN_WORD => {
                // LB
                (
                    InstructionType::IType,
                    LOAD_COMMON_OP_KEY,
                    &[SIGN_EXTEND_ON_LOAD_OP_KEY][..],
                )
            }
            (OPERATION_LOAD, 0b001, _) if SUPPORT_SIGNED & SUPPORT_LESS_THAN_WORD => {
                // LH
                (
                    InstructionType::IType,
                    LOAD_COMMON_OP_KEY,
                    &[LOAD_HALF_WORD_OP_KEY, SIGN_EXTEND_ON_LOAD_OP_KEY][..],
                )
            }
            (OPERATION_LOAD, 0b010, _) => {
                // LW
                if SUPPORT_LESS_THAN_WORD {
                    (
                        InstructionType::IType,
                        LOAD_COMMON_OP_KEY,
                        &[LOAD_WORD_OP_KEY][..],
                    )
                } else {
                    (InstructionType::IType, LOAD_COMMON_OP_KEY, &[][..])
                }
            }
            (OPERATION_LOAD, 0b100, _) if SUPPORT_LESS_THAN_WORD => {
                // LBU
                (InstructionType::IType, LOAD_COMMON_OP_KEY, &[][..])
            }
            (OPERATION_LOAD, 0b101, _) if SUPPORT_LESS_THAN_WORD => {
                // LHU
                (
                    InstructionType::IType,
                    LOAD_COMMON_OP_KEY,
                    &[LOAD_HALF_WORD_OP_KEY][..],
                )
            }
            _ => return Err(()),
        };

        Ok(params)
    }
}

// it's just a special function to apply, but we add the case for tables

impl<
        F: PrimeField,
        ST: BaseMachineState<F>,
        RS: RegisterValueSource<F>,
        DE: DecoderOutputSource<F, RS>,
        BS: IndexableBooleanSet,
        const SUPPORT_SIGNED: bool,
        const SUPPORT_LESS_THAN_WORD: bool,
    > MachineOp<F, ST, RS, DE, BS> for LoadOp<SUPPORT_SIGNED, SUPPORT_LESS_THAN_WORD>
{
    fn define_used_tables() -> Vec<TableType> {
        if SUPPORT_SIGNED {
            vec![TableType::MemoryOffsetGetBits, TableType::ExtendLoadedValue]
        } else {
            vec![TableType::MemoryOffsetGetBits]
        }
    }

    fn apply<
        CS: Circuit<F>,
        const ASSUME_TRUSTED_CODE: bool,
        const OUTPUT_EXACT_EXCEPTIONS: bool,
    >(
        _cs: &mut CS,
        _machine_state: &ST,
        _inputs: &DE,
        _boolean_set: &BS,
        _opt_ctx: &mut OptimizationContext<F, CS>,
    ) -> CommonDiffs<F> {
        panic!("use special function for this opcode")
    }
}

impl<const SUPPORT_SIGNED: bool, const SUPPORT_LESS_THAN_WORD: bool>
    LoadOp<SUPPORT_SIGNED, SUPPORT_LESS_THAN_WORD>
{
    pub fn spec_apply<
        F: PrimeField,
        CS: Circuit<F>,
        ST: BaseMachineState<F>,
        RS: RegisterValueSource<F>,
        DE: DecoderOutputSource<F, RS>,
        BS: IndexableBooleanSet,
        const ASSUME_TRUSTED_CODE: bool,
        const OUTPUT_EXACT_EXCEPTIONS: bool,
    >(
        cs: &mut CS,
        _machine_state: &ST,
        inputs: &DE,
        boolean_set: &BS,
        rs2_or_mem_load_query: &mut ShuffleRamMemQuery,
        opt_ctx: &mut OptimizationContext<F, CS>,
    ) -> CommonDiffs<F> {
        opt_ctx.reset_indexers();

        assert!(ST::opcodes_are_in_rom());

        let execute_family = boolean_set.get_major_flag(LOAD_COMMON_OP_KEY);
        let src1 = inputs.get_rs1_or_equivalent();
        let funct3 = inputs.funct3();

        if execute_family.get_value(cs).unwrap_or(false) {
            println!("LOAD");
            println!("Address = {:?}", src1.get_register().get_value_unsigned(cs));
        }

        if SUPPORT_LESS_THAN_WORD == true {
            // this is common for FAMILY of memory instructions

            if SUPPORT_SIGNED == false {
                todo!();
            }

            let full_word_access_flag =
                boolean_set.get_minor_flag(LOAD_COMMON_OP_KEY, LOAD_WORD_OP_KEY);
            let half_word_access_flag =
                boolean_set.get_minor_flag(LOAD_COMMON_OP_KEY, LOAD_HALF_WORD_OP_KEY);
            let exec_word = Boolean::and(&execute_family, &full_word_access_flag, cs);
            let exec_half_word = Boolean::and(&execute_family, &half_word_access_flag, cs);

            let src1 = src1.get_register();
            let imm = inputs.get_imm();

            let (unaligned_address, _of_flag) =
                opt_ctx.append_add_relation(src1, imm, execute_family, cs);

            // we will need an aligned address in any case
            let [bit_0, bit_1] = opt_ctx.append_lookup_relation(
                cs,
                &[unaligned_address.0[0].get_variable()],
                TableType::MemoryOffsetGetBits.to_num(),
                execute_family,
            );
            let aligned_address_low_constraint = {
                Constraint::from(unaligned_address.0[0].get_variable())
                    - (Term::from(bit_1) * Term::from(2))
                    - Term::from(bit_0)
            };

            // check alignment in case of subword accesses
            if ASSUME_TRUSTED_CODE {
                // unprovable if we do not have proper alignment
                cs.add_constraint((Term::from(bit_0) + Term::from(bit_1)) * exec_word.get_terms());

                cs.add_constraint(Term::from(bit_0) * exec_half_word.get_terms());
            } else {
                todo!();
            }

            // NOTE: we do NOT cast presumable bits to booleans, as it's under conditional assignment of lookup

            // NOTE: all lookup actions here are conditional, so we should not assume that boolean is so,
            // and should not use special operations like Boolean::and where witness generation is specialized.

            // This is ok even for masking into x0 read/write for query as we are globally predicated by memory operations flags,
            // so if it's not a memory operation it'll be overwritten during merge of memory queries

            let [is_ram_range, address_high_bits_for_rom] = opt_ctx.append_lookup_relation(
                cs,
                &[unaligned_address.0[1].get_variable()],
                TableType::RomAddressSpaceSeparator.to_num(),
                execute_family,
            );

            // now we can make everything conditional, but on other predicates. These are either 0,
            // or true booleans if we actually execute this family
            let is_rom_read = cs.add_variable_from_constraint(
                Term::from(execute_family.get_variable().unwrap())
                    * (Term::from(1u64) - Term::from(is_ram_range)),
            );
            let is_ram_read = cs.add_variable_from_constraint(
                Term::from(execute_family.get_variable().unwrap()) * Term::from(is_ram_range),
            );

            let indexers = opt_ctx.save_indexers();
            let [rom_value_low, rom_value_high] = {
                // ROM
                let rom_address = aligned_address_low_constraint.clone()
                    + Term::from((F::from_u64_unchecked(1 << 16), address_high_bits_for_rom));

                let [rom_value_low, rom_value_high] = opt_ctx
                    .append_lookup_relation_from_linear_terms(
                        cs,
                        &[rom_address],
                        TableType::RomRead.to_num(),
                        Boolean::Is(is_rom_read),
                    );

                // now we can select a word in case of sub-word reads
                let subword_to_use = cs.add_variable_from_constraint(
                    Term::from(bit_1) * Term::from(rom_value_high)
                        + (Term::from(1u64) - Term::from(bit_1)) * Term::from(rom_value_low),
                );

                // zero/signextend if needed - we will just use funct3 for it
                let input = Constraint::from(subword_to_use)
                    + (Term::from(1 << 16) * Term::from(bit_0))
                    + (Term::from(1 << 17) * Term::from(funct3));
                let [subword_case_rom_value_low, subword_case_rom_value_high] = opt_ctx
                    .append_lookup_relation_from_linear_terms(
                        cs,
                        &[input],
                        TableType::ExtendLoadedValue.to_num(),
                        Boolean::Is(is_rom_read),
                    );

                // constraint that we model it as read 0 from 0 address
                let ShuffleRamQueryType::RegisterOrRam {
                    is_register: _,
                    address,
                } = rs2_or_mem_load_query.query_type
                else {
                    unreachable!()
                };
                cs.add_constraint(Term::from(address[0]) * Term::from(is_rom_read));
                cs.add_constraint(Term::from(address[1]) * Term::from(is_rom_read));

                cs.add_constraint(
                    Term::from(rs2_or_mem_load_query.read_value[0]) * Term::from(is_rom_read),
                );
                cs.add_constraint(
                    Term::from(rs2_or_mem_load_query.read_value[1]) * Term::from(is_rom_read),
                );

                // select in case of ROM
                let selected_rom_low = cs.add_variable_from_constraint(
                    Term::from(full_word_access_flag) * Term::from(rom_value_low)
                        + (Term::from(1) - Term::from(full_word_access_flag))
                            * Term::from(subword_case_rom_value_low),
                );
                let selected_rom_high = cs.add_variable_from_constraint(
                    Term::from(full_word_access_flag) * Term::from(rom_value_high)
                        + (Term::from(1) - Term::from(full_word_access_flag))
                            * Term::from(subword_case_rom_value_high),
                );

                [selected_rom_low, selected_rom_high]
            };

            // RAM read is not different
            opt_ctx.restore_indexers(indexers);
            let [ram_value_low, ram_value_high] = {
                let [ram_value_low, ram_value_high] = rs2_or_mem_load_query.read_value;
                // constraint that read address that we use is a valid one
                let ShuffleRamQueryType::RegisterOrRam {
                    is_register: _,
                    address,
                } = rs2_or_mem_load_query.query_type
                else {
                    unreachable!()
                };
                cs.add_constraint(
                    (aligned_address_low_constraint.clone() - Term::from(address[0]))
                        * Term::from(is_ram_read),
                );
                cs.add_constraint(
                    (Term::from(unaligned_address.0[1]) - Term::from(address[1]))
                        * Term::from(is_ram_read),
                );

                // now we can select a word in case of sub-word reads
                let subword_to_use = cs.add_variable_from_constraint(
                    Term::from(bit_1) * Term::from(ram_value_high)
                        + (Term::from(1u64) - Term::from(bit_1)) * Term::from(ram_value_low),
                );

                // zero/signextend if needed - we will just use funct3 for it
                let input = Constraint::from(subword_to_use)
                    + (Term::from(1 << 16) * Term::from(bit_0))
                    + (Term::from(1 << 17) * Term::from(funct3));
                let [subword_case_ram_value_low, subword_case_ram_value_high] = opt_ctx
                    .append_lookup_relation_from_linear_terms(
                        cs,
                        &[input],
                        TableType::ExtendLoadedValue.to_num(),
                        Boolean::Is(is_ram_read),
                    );

                // select in case of RAM
                let selected_ram_low = cs.add_variable_from_constraint(
                    Term::from(full_word_access_flag) * Term::from(ram_value_low)
                        + (Term::from(1) - Term::from(full_word_access_flag))
                            * Term::from(subword_case_ram_value_low),
                );
                let selected_ram_high = cs.add_variable_from_constraint(
                    Term::from(full_word_access_flag) * Term::from(ram_value_high)
                        + (Term::from(1) - Term::from(full_word_access_flag))
                            * Term::from(subword_case_ram_value_high),
                );

                [selected_ram_low, selected_ram_high]
            };

            // NOTE: here we also assert that if we do NOT execute LOAD, we indeed perform access into register, and use rs2 index as address
            let ShuffleRamQueryType::RegisterOrRam {
                is_register,
                address,
            } = &mut rs2_or_mem_load_query.query_type
            else {
                unreachable!()
            };
            // TODO: fix compiler to handle it
            let t = cs.add_variable_from_constraint_allow_explicit_linear(
                Term::from(1u64) - Term::from(execute_family),
            );
            *is_register = Boolean::Is(t);

            // and if we do not perform memory read, then addresses are constrained to be RS2 index read access formally
            let rs2_index = inputs.get_rs2_index();
            cs.add_constraint(
                (rs2_index - Term::from(address[0]))
                    * (Term::from(1u64) - Term::from(execute_family)),
            );
            cs.add_constraint(
                Term::from(address[1]) * (Term::from(1u64) - Term::from(execute_family)),
            );

            if ASSUME_TRUSTED_CODE {
                CommonDiffs {
                    exec_flag: execute_family,
                    trapped: None,
                    trap_reason: None,
                    rd_value: vec![
                        (
                            [
                                Constraint::from(rom_value_low),
                                Constraint::from(rom_value_high),
                            ],
                            Boolean::Is(is_rom_read),
                        ),
                        (
                            [
                                Constraint::from(ram_value_low),
                                Constraint::from(ram_value_high),
                            ],
                            Boolean::Is(is_ram_read),
                        ),
                    ],
                    new_pc_value: NextPcValue::Default,
                }
            } else {
                // we trap if misaligned access that can happen in untrusted code

                todo!();
            }
        } else {
            // support only LW, and so we assume code is trusted
            assert!(ASSUME_TRUSTED_CODE);

            let src1 = src1.get_register();
            let imm = inputs.get_imm();

            let (unaligned_address, _of_flag) =
                opt_ctx.append_add_relation(src1, imm, execute_family, cs);

            let [is_ram_range, address_high_bits_for_rom] = opt_ctx.append_lookup_relation(
                cs,
                &[unaligned_address.0[1].get_variable()],
                TableType::RomAddressSpaceSeparator.to_num(),
                execute_family,
            );

            // This will also trap unaligned access
            let rom_address = Term::from(unaligned_address.0[0])
                + Term::from((F::from_u64_unchecked(1 << 16), address_high_bits_for_rom));

            let [rom_value_low, rom_value_high] = opt_ctx.append_lookup_relation_from_linear_terms(
                cs,
                &[rom_address],
                TableType::RomRead.to_num(),
                execute_family,
            );

            // now we can make everything conditional, but on other predicates. These are either 0,
            // or true booleans if we actually execute this family
            let is_rom_read = cs.add_variable_from_constraint(
                Term::from(execute_family.get_variable().unwrap())
                    * (Term::from(1u64) - Term::from(is_ram_range)),
            );
            let is_ram_read = cs.add_variable_from_constraint(
                Term::from(execute_family.get_variable().unwrap()) * Term::from(is_ram_range),
            );

            {
                // ROM

                // constraint that we model it as read 0 from 0 address
                let ShuffleRamQueryType::RegisterOrRam {
                    is_register: _,
                    address,
                } = rs2_or_mem_load_query.query_type
                else {
                    unreachable!()
                };
                cs.add_constraint(Term::from(address[0]) * Term::from(is_rom_read));
                cs.add_constraint(Term::from(address[1]) * Term::from(is_rom_read));

                cs.add_constraint(
                    Term::from(rs2_or_mem_load_query.read_value[0]) * Term::from(is_rom_read),
                );
                cs.add_constraint(
                    Term::from(rs2_or_mem_load_query.read_value[1]) * Term::from(is_rom_read),
                );
            };

            let [ram_value_low, ram_value_high] = rs2_or_mem_load_query.read_value;
            {
                // constraint that read address that we use is a valid one
                let ShuffleRamQueryType::RegisterOrRam {
                    is_register: _,
                    address,
                } = rs2_or_mem_load_query.query_type
                else {
                    unreachable!()
                };
                cs.add_constraint(
                    (Term::from(unaligned_address.0[0]) - Term::from(address[0]))
                        * Term::from(is_ram_read),
                );
                cs.add_constraint(
                    (Term::from(unaligned_address.0[1]) - Term::from(address[1]))
                        * Term::from(is_ram_read),
                );
            };

            // NOTE: here we also assert that if we do NOT execute LOAD, we indeed perform access into register, and use rs2 index as address
            let ShuffleRamQueryType::RegisterOrRam {
                is_register,
                address,
            } = &mut rs2_or_mem_load_query.query_type
            else {
                unreachable!()
            };
            // TODO: fix compiler to handle it
            // TODO: fix compiler to handle it
            let t = cs.add_variable_from_constraint_allow_explicit_linear(
                Term::from(1u64) - Term::from(execute_family),
            );
            *is_register = Boolean::Is(t);

            // and if we do not perform memory read, then addresses are constrained to be RS2 index read access formally
            let rs2_index = inputs.get_rs2_index();
            cs.add_constraint(
                (rs2_index - Term::from(address[0]))
                    * (Term::from(1u64) - Term::from(execute_family)),
            );
            cs.add_constraint(
                Term::from(address[1]) * (Term::from(1u64) - Term::from(execute_family)),
            );

            CommonDiffs {
                exec_flag: execute_family,
                trapped: None,
                trap_reason: None,
                rd_value: vec![
                    (
                        [
                            Constraint::from(rom_value_low),
                            Constraint::from(rom_value_high),
                        ],
                        Boolean::Is(is_rom_read),
                    ),
                    (
                        [
                            Constraint::from(ram_value_low),
                            Constraint::from(ram_value_high),
                        ],
                        Boolean::Is(is_ram_read),
                    ),
                ],
                new_pc_value: NextPcValue::Default,
            }
        }
    }
}
