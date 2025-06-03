use super::*;

pub const STORE_COMMON_OP_KEY: DecoderMajorInstructionFamilyKey =
    DecoderMajorInstructionFamilyKey("SW/SH/SB");
pub const STORE_WORD_OP_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("SW");
pub const STORE_HALF_WORD_OP_KEY: DecoderInstructionVariantsKey =
    DecoderInstructionVariantsKey("SH");
// pub const STORE_BYTE_OP_KEY: DecoderInstructionVariantsKey = DecoderInstructionVariantsKey("SB");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StoreOp<const SUPPORT_LESS_THAN_WORD: bool>;

impl<const SUPPORT_LESS_THAN_WORD: bool> DecodableMachineOp for StoreOp<SUPPORT_LESS_THAN_WORD> {
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
            (OPERATION_STORE, 0b000, _) if SUPPORT_LESS_THAN_WORD => {
                // SB
                (InstructionType::SType, STORE_COMMON_OP_KEY, &[][..])
            }
            (OPERATION_STORE, 0b001, _) if SUPPORT_LESS_THAN_WORD => {
                // SH
                (
                    InstructionType::SType,
                    STORE_COMMON_OP_KEY,
                    &[STORE_HALF_WORD_OP_KEY][..],
                )
            }
            (OPERATION_STORE, 0b010, _) => {
                // SW
                if SUPPORT_LESS_THAN_WORD {
                    (
                        InstructionType::SType,
                        STORE_COMMON_OP_KEY,
                        &[STORE_WORD_OP_KEY][..],
                    )
                } else {
                    (InstructionType::SType, STORE_COMMON_OP_KEY, &[][..])
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
        const SUPPORT_LESS_THAN_WORD: bool,
    > MachineOp<F, ST, RS, DE, BS> for StoreOp<SUPPORT_LESS_THAN_WORD>
{
    fn define_used_tables() -> Vec<TableType> {
        if SUPPORT_LESS_THAN_WORD {
            vec![
                TableType::MemoryOffsetGetBits,
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
        panic!("use special function for this opcode")
    }
}
impl<const SUPPORT_LESS_THAN_WORD: bool> StoreOp<SUPPORT_LESS_THAN_WORD> {
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
        rd_or_mem_store_query: &mut ShuffleRamMemQuery,
        opt_ctx: &mut OptimizationContext<F, CS>,
    ) -> CommonDiffs<F> {
        opt_ctx.reset_indexers();

        assert!(ST::opcodes_are_in_rom());

        let execute_family = boolean_set.get_major_flag(STORE_COMMON_OP_KEY);

        let src1 = inputs.get_rs1_or_equivalent();
        let src2 = inputs.get_rs2_or_equivalent();

        if execute_family.get_value(cs).unwrap_or(false) {
            println!("STORE");
            println!("Address = {:?}", src1.get_register().get_value_unsigned(cs));
        }

        if SUPPORT_LESS_THAN_WORD == true {
            // this is common for FAMILY of memory instructions

            let full_word_access_flag =
                boolean_set.get_minor_flag(STORE_COMMON_OP_KEY, STORE_WORD_OP_KEY);
            let half_word_access_flag =
                boolean_set.get_minor_flag(STORE_COMMON_OP_KEY, STORE_HALF_WORD_OP_KEY);
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

            let [is_ram_range, _address_high_bits_for_rom] = opt_ctx.append_lookup_relation(
                cs,
                &[unaligned_address.0[1].get_variable()],
                TableType::RomAddressSpaceSeparator.to_num(),
                execute_family,
            );

            // we can not write into ROM
            if ASSUME_TRUSTED_CODE {
                // NOTE: `should_write_mem` always conditioned over execution of the opcode itself
                cs.add_constraint(
                    execute_family.get_terms() * (Term::from(1) - Term::from(is_ram_range)),
                );
            } else {
                // we should trap maybe
                todo!()
            }

            let base_value = rd_or_mem_store_query.read_value;
            // NOTE: here it's yes unconstrained byte, but if we take this branch - it becomes constrained
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
                execute_family,
            );
            let [to_keep_contribution] = opt_ctx.append_lookup_relation(
                cs,
                &[subword_to_use_for_update, bit_0],
                TableType::StoreByteExistingContribution.to_num(),
                execute_family,
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
                    * Term::from(execute_family),
            );
            cs.add_constraint(
                (Term::from(unaligned_address.0[1]) - Term::from(address[1]))
                    * Term::from(execute_family),
            );

            // constraint written values

            // if we store full word, then it's just src2
            let word_to_store = src2.get_register();
            cs.add_constraint(
                (Term::from(word_to_store.0[0]) - Term::from(rd_or_mem_store_query.write_value[0]))
                    * Term::from(exec_word),
            );
            cs.add_constraint(
                (Term::from(word_to_store.0[1]) - Term::from(rd_or_mem_store_query.write_value[1]))
                    * Term::from(exec_word),
            );

            // otherwise we have to properly shuffle and constraint
            // half-word case and byte case are not too different anyway

            // NOTE: it would select `update + keep` for full word too, but it'll not be used below
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
                    * (Term::from(execute_family) - Term::from(exec_word)),
            );
            cs.add_constraint(
                (Term::from(selected_high) - Term::from(rd_or_mem_store_query.write_value[1]))
                    * (Term::from(execute_family) - Term::from(exec_word)),
            );

            let ShuffleRamQueryType::RegisterOrRam { is_register, .. } =
                &mut rd_or_mem_store_query.query_type
            else {
                unreachable!()
            };
            let t = cs.add_variable_from_constraint_allow_explicit_linear(
                Term::from(1u64) - Term::from(execute_family),
            );
            *is_register = Boolean::Is(t);
            // here we do not need to constraint address if case if we did NOT perform write,
            // as we anyway expect a writeback to be performed

            if ASSUME_TRUSTED_CODE {
                CommonDiffs {
                    exec_flag: execute_family,
                    trapped: None,
                    trap_reason: None,
                    rd_value: vec![],
                    new_pc_value: NextPcValue::Default,
                }
            } else {
                // we trap if misaligned access that can happen in untrusted code

                todo!();
            }
        } else {
            // support only SW/LW, and so we assume code is trusted
            assert!(ASSUME_TRUSTED_CODE);

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

            // check alignment in case of subword accesses
            if ASSUME_TRUSTED_CODE {
                // unprovable if we do not have proper alignment
                cs.add_constraint(
                    (Term::from(bit_0) + Term::from(bit_1)) * execute_family.get_terms(),
                );
            } else {
                todo!();
            }

            // NOTE: we do NOT cast presumable bits to booleans, as it's under conditional assignment of lookup

            // NOTE: all lookup actions here are conditional, so we should not assume that boolean is so,
            // and should not use special operations like Boolean::and where witness generation is specialized.

            // This is ok even for masking into x0 read/write for query as we are globally predicated by memory operations flags,
            // so if it's not a memory operation it'll be overwritten during merge of memory queries

            let [is_ram_range, _address_high_bits_for_rom] = opt_ctx.append_lookup_relation(
                cs,
                &[unaligned_address.0[1].get_variable()],
                TableType::RomAddressSpaceSeparator.to_num(),
                execute_family,
            );

            // we can not write into ROM
            if ASSUME_TRUSTED_CODE {
                // NOTE: `should_write_mem` always conditioned over execution of the opcode itself
                cs.add_constraint(
                    execute_family.get_terms() * (Term::from(1) - Term::from(is_ram_range)),
                );
            } else {
                // we should trap maybe
                todo!()
            }

            // constraint that write address that we use is a valid one
            let ShuffleRamQueryType::RegisterOrRam {
                is_register: _,
                address,
            } = rd_or_mem_store_query.query_type
            else {
                unreachable!()
            };
            cs.add_constraint(
                (Term::from(unaligned_address.0[0]) - Term::from(address[0]))
                    * Term::from(execute_family),
            );
            cs.add_constraint(
                (Term::from(unaligned_address.0[1]) - Term::from(address[1]))
                    * Term::from(execute_family),
            );

            // constraint written values

            // if we store full word, then it's just src2
            let word_to_store = src2.get_register();
            cs.add_constraint(
                (Term::from(word_to_store.0[0]) - Term::from(rd_or_mem_store_query.write_value[0]))
                    * Term::from(execute_family),
            );
            cs.add_constraint(
                (Term::from(word_to_store.0[1]) - Term::from(rd_or_mem_store_query.write_value[1]))
                    * Term::from(execute_family),
            );

            let ShuffleRamQueryType::RegisterOrRam { is_register, .. } =
                &mut rd_or_mem_store_query.query_type
            else {
                unreachable!()
            };
            let t = cs.add_variable_from_constraint_allow_explicit_linear(
                Term::from(1u64) - Term::from(execute_family),
            );
            *is_register = Boolean::Is(t);
            // here we do not need to constraint address if case if we did NOT perform write,
            // as we anyway expect a writeback to be performed

            CommonDiffs {
                exec_flag: execute_family,
                trapped: None,
                trap_reason: None,
                rd_value: vec![],
                new_pc_value: NextPcValue::Default,
            }
        }
    }
}
