use super::*;

pub const MEMORY_COMMON_OP_KEY: DecoderMajorInstructionFamilyKey =
    DecoderMajorInstructionFamilyKey("LW/SW/LH/LHU/SH/LB/LBU/SB");
pub const MEMORY_WRITE_COMMON_OP_KEY: DecoderInstructionVariantsKey =
    DecoderInstructionVariantsKey("SW/SH/SB");
pub const ACCESS_BYTE_OP_KEY: DecoderInstructionVariantsKey =
    DecoderInstructionVariantsKey("LB/LBU/SB");
pub const ACCESS_HALF_WORD_OP_KEY: DecoderInstructionVariantsKey =
    DecoderInstructionVariantsKey("LH/LHU/SH");
pub const ACCESS_WORD_OP_KEY: DecoderInstructionVariantsKey =
    DecoderInstructionVariantsKey("LW/SW");
pub const SIGN_EXTEND_ON_LOAD_OP_KEY: DecoderInstructionVariantsKey =
    DecoderInstructionVariantsKey("LB/LW");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemoryOp<const SUPPORT_SIGNED: bool, const SUPPORT_LESS_THAN_WORD: bool>;

impl<const SUPPORT_SIGNED: bool, const SUPPORT_LESS_THAN_WORD: bool> DecodableMachineOp
    for MemoryOp<SUPPORT_SIGNED, SUPPORT_LESS_THAN_WORD>
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
                    MEMORY_COMMON_OP_KEY,
                    &[ACCESS_BYTE_OP_KEY, SIGN_EXTEND_ON_LOAD_OP_KEY][..],
                )
            }
            (OPERATION_LOAD, 0b001, _) if SUPPORT_SIGNED & SUPPORT_LESS_THAN_WORD => {
                // LH
                (
                    InstructionType::IType,
                    MEMORY_COMMON_OP_KEY,
                    &[ACCESS_HALF_WORD_OP_KEY, SIGN_EXTEND_ON_LOAD_OP_KEY][..],
                )
            }
            (OPERATION_LOAD, 0b010, _) => {
                // LW
                if SUPPORT_LESS_THAN_WORD {
                    (
                        InstructionType::IType,
                        MEMORY_COMMON_OP_KEY,
                        &[ACCESS_WORD_OP_KEY][..],
                    )
                } else {
                    (InstructionType::IType, MEMORY_COMMON_OP_KEY, &[][..])
                }
            }
            (OPERATION_LOAD, 0b100, _) if SUPPORT_LESS_THAN_WORD => {
                // LBU
                (
                    InstructionType::IType,
                    MEMORY_COMMON_OP_KEY,
                    &[ACCESS_BYTE_OP_KEY][..],
                )
            }
            (OPERATION_LOAD, 0b101, _) if SUPPORT_LESS_THAN_WORD => {
                // LHU
                (
                    InstructionType::IType,
                    MEMORY_COMMON_OP_KEY,
                    &[ACCESS_HALF_WORD_OP_KEY][..],
                )
            }
            (OPERATION_STORE, 0b000, _) if SUPPORT_LESS_THAN_WORD => {
                // SB
                (
                    InstructionType::SType,
                    MEMORY_COMMON_OP_KEY,
                    &[ACCESS_BYTE_OP_KEY, MEMORY_WRITE_COMMON_OP_KEY][..],
                )
            }
            (OPERATION_STORE, 0b001, _) if SUPPORT_LESS_THAN_WORD => {
                // SH
                (
                    InstructionType::SType,
                    MEMORY_COMMON_OP_KEY,
                    &[ACCESS_HALF_WORD_OP_KEY, MEMORY_WRITE_COMMON_OP_KEY][..],
                )
            }
            (OPERATION_STORE, 0b010, _) => {
                // SW
                if SUPPORT_LESS_THAN_WORD {
                    (
                        InstructionType::SType,
                        MEMORY_COMMON_OP_KEY,
                        &[ACCESS_WORD_OP_KEY, MEMORY_WRITE_COMMON_OP_KEY][..],
                    )
                } else {
                    (
                        InstructionType::SType,
                        MEMORY_COMMON_OP_KEY,
                        &[MEMORY_WRITE_COMMON_OP_KEY][..],
                    )
                }
            }
            _ => return Err(()),
        };

        Ok(params)
    }
}

impl<
        F: PrimeField,
        ST: BaseMachineState<F>,
        RS: RegisterValueSource<F>,
        DE: DecoderOutputSource<F, RS>,
        BS: IndexableBooleanSet,
        const SUPPORT_SIGNED: bool,
        const SUPPORT_LESS_THAN_WORD: bool,
    > MachineOp<F, ST, RS, DE, BS> for MemoryOp<SUPPORT_SIGNED, SUPPORT_LESS_THAN_WORD>
{
    fn define_used_tables() -> Vec<TableType> {
        if SUPPORT_SIGNED {
            vec![
                TableType::MemoryOffsetGetBits,
                TableType::ExtendLoadedValue,
                TableType::StoreByteSourceContribution,
                TableType::StoreByteExistingContribution,
            ]
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
        panic!("use `apply_with_mem_access` for this opcode")
    }

    fn apply_with_mem_access<
        CS: Circuit<F>,
        const ASSUME_TRUSTED_CODE: bool,
        const OUTPUT_EXACT_EXCEPTIONS: bool,
    >(
        cs: &mut CS,
        _machine_state: &ST,
        inputs: &DE,
        boolean_set: &BS,
        rs2_or_mem_load_query: &mut ShuffleRamMemQuery,
        rd_or_mem_store_query: &mut ShuffleRamMemQuery,
        opt_ctx: &mut OptimizationContext<F, CS>,
    ) -> CommonDiffs<F> {
        opt_ctx.reset_indexers();

        assert!(ST::opcodes_are_in_rom());

        let execute_family = boolean_set.get_major_flag(MEMORY_COMMON_OP_KEY);
        let should_read_mem = Boolean::and(
            &execute_family,
            &boolean_set
                .get_minor_flag(MEMORY_COMMON_OP_KEY, MEMORY_WRITE_COMMON_OP_KEY)
                .toggle(),
            cs,
        );
        let should_write_mem = Boolean::and(
            &execute_family,
            &boolean_set.get_minor_flag(MEMORY_COMMON_OP_KEY, MEMORY_WRITE_COMMON_OP_KEY),
            cs,
        );

        let src1 = inputs.get_rs1_or_equivalent();
        let src2 = inputs.get_rs2_or_equivalent();
        let funct3 = inputs.funct3();

        if execute_family.get_value(cs).unwrap_or(false) {
            println!("MEMORY");
            println!("Address = {:?}", src1.get_register().get_value_unsigned(cs));
        }

        if SUPPORT_LESS_THAN_WORD == true {
            // this is common for FAMILY of memory instructions

            if SUPPORT_SIGNED == false {
                todo!();
            }

            let full_word_access_flag =
                boolean_set.get_minor_flag(MEMORY_COMMON_OP_KEY, ACCESS_WORD_OP_KEY);
            let half_word_access_flag =
                boolean_set.get_minor_flag(MEMORY_COMMON_OP_KEY, ACCESS_HALF_WORD_OP_KEY);
            let exec_word = Boolean::and(&execute_family, &full_word_access_flag, cs);
            let exec_half_word = Boolean::and(&execute_family, &half_word_access_flag, cs);
            let write_word = Boolean::and(
                &exec_word,
                &boolean_set.get_minor_flag(MEMORY_COMMON_OP_KEY, MEMORY_WRITE_COMMON_OP_KEY),
                cs,
            );

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

            // we can not write into ROM
            if ASSUME_TRUSTED_CODE {
                // NOTE: `should_write_mem` always conditioned over execution of the opcode itself
                cs.add_constraint(
                    should_write_mem.get_terms() * (Term::from(1) - Term::from(is_ram_range)),
                );
            } else {
                // we should trap maybe
                todo!()
            }

            // now we can make everything conditional, but on other predicates. These are either 0,
            // or true booleans if we actually execute this family
            let is_rom_read = cs.add_variable_from_constraint(
                Term::from(should_read_mem.get_variable().unwrap())
                    * (Term::from(1u64) - Term::from(is_ram_range)),
            );
            let is_ram_read = cs.add_variable_from_constraint(
                Term::from(should_read_mem.get_variable().unwrap()) * Term::from(is_ram_range),
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
            *is_register = should_read_mem;
            // and if we do not perform memory read, then addresses are constrainted to be RS2 index read access formally
            let rs2_index = inputs.get_rs2_index();
            cs.add_constraint(
                (rs2_index - Term::from(address[0]))
                    * (Term::from(1u64) - Term::from(should_read_mem)),
            );
            cs.add_constraint(
                Term::from(address[1]) * (Term::from(1u64) - Term::from(should_read_mem)),
            );

            // only write remains
            opt_ctx.restore_indexers(indexers);
            {
                let base_value = rd_or_mem_store_query.read_value;
                // NOTE: here it's yes unconstrainted byte, but if we take this branch - it becomes constrainted
                let src_half_word = src2
                    .get_register_with_decomposition_and_sign()
                    .unwrap()
                    .u16_limbs[0]
                    .get_variable();
                let subword_to_use_for_update = cs.add_variable_from_constraint(
                    Term::from(bit_1) * Term::from(base_value[1])
                        + (Term::from(1u64) - Term::from(bit_1)) * Term::from(base_value[0]),
                );
                // we will use 2 lookups to get contribution of byte into subword,
                // and constibution of subword into result

                let [update_contribution] = opt_ctx.append_lookup_relation(
                    cs,
                    &[src_half_word, bit_0],
                    TableType::StoreByteSourceContribution.to_num(),
                    should_write_mem,
                );

                let [to_keep_contribution] = opt_ctx.append_lookup_relation(
                    cs,
                    &[subword_to_use_for_update, bit_0],
                    TableType::StoreByteExistingContribution.to_num(),
                    should_write_mem,
                );

                // constraint that write address that we use is a valid one
                let ShuffleRamQueryType::RegisterOrRam {
                    is_register: _,
                    address,
                } = rd_or_mem_store_query.query_type
                else {
                    unreachable!()
                };
                cs.add_constraint(
                    (aligned_address_low_constraint.clone() - Term::from(address[0]))
                        * Term::from(should_write_mem),
                );
                cs.add_constraint(
                    (Term::from(unaligned_address.0[1]) - Term::from(address[1]))
                        * Term::from(should_write_mem),
                );

                // constraint written values

                // if we store full word, then it's just src2
                let word_to_store = src2.get_register();
                cs.add_constraint(
                    (Term::from(word_to_store.0[0])
                        - Term::from(rd_or_mem_store_query.write_value[0]))
                        * Term::from(write_word),
                );
                cs.add_constraint(
                    (Term::from(word_to_store.0[1])
                        - Term::from(rd_or_mem_store_query.write_value[1]))
                        * Term::from(write_word),
                );

                // otherwise we have to properly shuffle and constraint
                // half-word case and full-word case are not too different anyway

                let selected_subword = cs.add_variable_from_constraint(
                    Term::from(half_word_access_flag) * Term::from(src_half_word)
                        + (Term::from(update_contribution) + Term::from(to_keep_contribution))
                            * (Term::from(1) - Term::from(half_word_access_flag)),
                );
                // now route it based on the bit_1, and then constraint in case if we do any form of subword write (byte or half-word)
                let selected_low = cs.add_variable_from_constraint(
                    Term::from(bit_1) * Term::from(base_value[0])
                        + (Term::from(1) - Term::from(bit_1)) * Term::from(selected_subword),
                );
                let selected_high = cs.add_variable_from_constraint(
                    Term::from(bit_1) * Term::from(selected_subword)
                        + (Term::from(1) - Term::from(bit_1)) * Term::from(base_value[1]),
                );
                cs.add_constraint(
                    (Term::from(selected_low) - Term::from(rd_or_mem_store_query.write_value[0]))
                        * (Term::from(should_write_mem) - Term::from(write_word)),
                );
                cs.add_constraint(
                    (Term::from(selected_high) - Term::from(rd_or_mem_store_query.write_value[1]))
                        * (Term::from(should_write_mem) - Term::from(write_word)),
                );
            }
            let ShuffleRamQueryType::RegisterOrRam { is_register, .. } =
                &mut rd_or_mem_store_query.query_type
            else {
                unreachable!()
            };
            let t = cs.add_variable_from_constraint_allow_explicit_linear(
                Term::from(1u64) - Term::from(should_write_mem),
            );
            *is_register = Boolean::Is(t);
            // here we do not need to constraint address if case if we did NOT perform write,
            // as we anyway expect a writeback to be performed

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
            // support only SW/LW, and so we assume code is trusted
            assert!(ASSUME_TRUSTED_CODE);

            todo!();

            // // this is common for FAMILY of memory instructions

            // let src1 = src1.get_register();
            // let imm = inputs.get_imm();

            // let (unaligned_address, _of_flag) =
            //     opt_ctx.append_add_relation(src1, imm, execute_family, cs);

            // let [bit_0, bit_1] = opt_ctx.append_lookup_relation(
            //     cs,
            //     &[unaligned_address.0[0].get_variable()],
            //     TableType::MemoryOffsetGetBits.to_num(),
            //     execute_family,
            // );
            // let aligned_address_low_constraint = {
            //     Constraint::from(unaligned_address.0[0].get_variable())
            //         - (Term::from(bit_1) * Term::from(2))
            //         - Term::from(bit_0)
            // };

            // // NOTE: in a form that we use the "share" lookup we can not use Boolean::or here (that uses custom witness generation)
            // // that assumes that some values are booleans. Instead we evaluate it as generic constraint

            // // 1 - b + ab
            // // res = 1 - (1 - a)(1-b) = a + b - ab
            // let is_unaligned = cs.add_variable_from_constraint(
            //     Constraint::from(bit_0) + Term::from(bit_1) - Term::from(bit_0) * Term::from(bit_1),
            // );

            // // unprovable if unaligned
            // cs.add_constraint(Term::from(is_unaligned) * execute_family.get_terms());

            // // NOTE: whether it's read or write, we will always read from src1 + imm
            // let (source, mem_load_query, address_is_in_ram_range) =
            //     read_from_shuffle_ram_or_bytecode_no_decomposition_with_ctx(
            //         cs,
            //         mem_load_timestamp,
            //         aligned_address_low_constraint,
            //         unaligned_address.0[1],
            //         opt_ctx,
            //         execute_family,
            //     );

            // // NOTE: `should_write_mem` always conditioned over execution of the opcode itself
            // cs.add_constraint(
            //     should_write_mem.get_terms()
            //         * (Term::from(1) - Term::from(address_is_in_ram_range)),
            // );

            // // if we will do STORE, then it'll be the value
            // let val_to_store = src2.get_register();

            // let returned_value = [
            //     Constraint::<F>::from(source.0[0].get_variable()),
            //     Constraint::<F>::from(source.0[1].get_variable()),
            // ];

            // let value_to_store = Register([val_to_store.0[0], val_to_store.0[1]]);

            // // we add read query if we LOAD
            // memory_queries.push(mem_load_query);

            // let execute_read = execute_family;
            // let execute_write = should_write_mem;

            // // and we form join query if we STORE
            // let mut mem_store_query = mem_load_query;
            // mem_store_query.local_timestamp_in_cycle = mem_store_timestamp;
            // mem_store_query.write_value = std::array::from_fn(|i| {
            //     cs.choose(
            //         execute_write,
            //         value_to_store.0[i],
            //         Num::Var(mem_store_query.read_value[i]),
            //     )
            //     .get_variable()
            // });

            // memory_queries.push(mem_store_query);

            // if execute_family.get_value(cs).unwrap_or(false) {
            //     println!("MEMORY");
            //     dbg!(execute_read.get_value(cs));
            //     dbg!(should_write_mem.get_value(cs));
            //     dbg!(execute_write.get_value(cs));
            //     dbg!(src1.get_value_unsigned(cs));
            //     dbg!(src2.get_register().get_value_unsigned(cs));
            //     // dbg!(rd.get_value_unsigned(cs));
            // }

            // CommonDiffs {
            //     exec_flag: execute_family,
            //     trapped: None,
            //     trap_reason: None,
            //     rd_value: Some(returned_value),
            //     new_pc_value: NextPcValue::Default,
            // }
        }
    }
}
