use super::*;
use crate::machine::{
    decoder::decode_optimized_must_handle_csr::OptimizedDecoderOutput,
    ops::{RD_STORE_LOCAL_TIMESTAMP, RS1_LOAD_LOCAL_TIMESTAMP, RS2_LOAD_LOCAL_TIMESTAMP},
};

pub(crate) fn optimized_decode_and_read_reg_operands<
    F: PrimeField,
    CS: Circuit<F>,
    const ASSUME_TRUSTED_CODE: bool,
    const PERFORM_DELEGATION: bool,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    cs: &mut CS,
    pc: Register<F>,
    opcodes_are_in_rom: bool,
    decode_table_splitting: [usize; 2],
) -> (
    Vec<ShuffleRamMemQuery>,
    RS2ShuffleRamQueryCandidate<F>,
    Register<F>,
    Register<F>,
    Constraint<F>,
    OptimizedDecoderOutput<F>,
    Vec<Boolean>,
) {
    let next_opcode = read_opcode_from_rom::<F, CS, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(cs, pc);

    // there is one small thing here - if we use CSR processing that doesn't have matching over CSR index,
    // then we must handle UNIMP instruction here that is csrrw x0, cycle, x0
    // Also ROM is padded with UNIMP

    if ASSUME_TRUSTED_CODE {
        if PERFORM_DELEGATION {
            // there will be mtaching over CSR index in the corresponding path, and we do not support "cycle" csr, so we will fail

            // Do nothing
        } else {
            assert_no_unimp(cs, next_opcode);
        }
    } else {
        unimplemented!()
    }

    if let Some(opcode) = next_opcode.get_value_unsigned(cs) {
        println!("Opcode = 0x{:08x}", opcode);
    }

    use crate::machine::decoder::decode_optimized_must_handle_csr::*;
    use crate::machine::decoder::DecoderInput;

    let decoder_input = DecoderInput {
        instruction: next_opcode,
    };
    let (invalid_opcode, raw_decoder_output, opcode_format_bits, other_bits) =
        OptimizedDecoder::decode::<F, CS>(&decoder_input, cs, decode_table_splitting);

    if ASSUME_TRUSTED_CODE {
        // if opcode is invalid - it's unsatisfiable
        cs.add_constraint_allow_explicit_linear_prevent_optimizations(Constraint::<F>::from(
            invalid_opcode,
        ));
    } else {
        unimplemented!()
    }

    let mut memory_queries = vec![];

    let (src1_reg, rs1_mem_query) =
        get_rs1_as_shuffle_ram(cs, raw_decoder_output.rs1, opcodes_are_in_rom);
    // even though not all the opcodes read first register, we still consider it unconditional
    memory_queries.push(rs1_mem_query);

    // for src2 we will drag some data along

    let (src2_reg, rs2_mem_query) =
        prepare_rs2_op_as_shuffle_ram(cs, raw_decoder_output.rs2.clone(), opcodes_are_in_rom);
    // we will merge rs2 with mem LOAD opcode queries below

    let (src1, src2, update_rd) = OptimizedDecoder::select_src1_and_src2_values(
        cs,
        &opcode_format_bits,
        src1_reg,
        raw_decoder_output.imm,
        src2_reg,
    );

    (
        memory_queries,
        rs2_mem_query,
        src1,
        src2,
        update_rd,
        raw_decoder_output,
        other_bits,
    )
}

pub(crate) fn optimized_decode_and_preallocate_mem_queries_for_bytecode_in_rom<
    F: PrimeField,
    CS: Circuit<F>,
    const ASSUME_TRUSTED_CODE: bool,
    const PERFORM_DELEGATION: bool,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    cs: &mut CS,
    pc: Register<F>,
    decode_table_splitting: [usize; 2],
    boolean_keys: DecoderOutputExtraKeysHolder,
) -> (
    [ShuffleRamMemQuery; 3],
    Register<F>,
    Register<F>,
    OptimizedDecoderOutput<F>,
    BasicFlagsSource,
    [Boolean; NUM_INSTRUCTION_TYPES_IN_DECODE_BITS],
) {
    let next_opcode = read_opcode_from_rom::<F, CS, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(cs, pc);

    // there is one small thing here - if we use CSR processing that doesn't have matching over CSR index,
    // then we must handle UNIMP instruction here that is csrrw x0, cycle, x0
    // Also ROM is padded with UNIMP

    if ASSUME_TRUSTED_CODE {
        if PERFORM_DELEGATION {
            // there will be mtaching over CSR index in the corresponding path, and we do not support "cycle" csr, so we will fail

            // Do nothing
        } else {
            assert_no_unimp(cs, next_opcode);
        }
    } else {
        unimplemented!()
    }

    if let Some(opcode) = next_opcode.get_value_unsigned(cs) {
        println!("Opcode = 0x{:08x}", opcode);
    }

    use crate::machine::decoder::decode_optimized_must_handle_csr::*;
    use crate::machine::decoder::DecoderInput;

    let decoder_input = DecoderInput {
        instruction: next_opcode,
    };
    let (invalid_opcode, raw_decoder_output, opcode_format_bits, other_bits) =
        OptimizedDecoder::decode::<F, CS>(&decoder_input, cs, decode_table_splitting);

    if ASSUME_TRUSTED_CODE {
        // if opcode is invalid - it's unsatisfiable
        cs.add_constraint_allow_explicit_linear_prevent_optimizations(Constraint::<F>::from(
            invalid_opcode,
        ));
    } else {
        unimplemented!()
    }

    let flags_source = BasicFlagsSource::new(boolean_keys, other_bits);

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
            raw_decoder_output.rs1.clone(),
            value,
            value,
        );
        memory_queries.push(query);

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
                address: read_address.0.map(|el| el.get_variable()),
            },
            local_timestamp_in_cycle,
            read_value: read_value.0.map(|el| el.get_variable()),
            write_value: write_value.0.map(|el| el.get_variable()),
        };
        memory_queries.push(query);
    }

    let [r_insn, i_insn, s_insn, b_insn, _u_insn, _j_insn] = opcode_format_bits;

    let src1 = rs1_value;

    let src2 = Register::choose_from_orthogonal_variants(
        cs,
        &[r_insn, i_insn, s_insn, b_insn],
        &[
            rs2_value_if_register,
            raw_decoder_output.imm,
            rs2_value_if_register,
            rs2_value_if_register,
        ],
    );

    (
        memory_queries.try_into().unwrap(),
        src1,
        src2,
        raw_decoder_output,
        flags_source,
        opcode_format_bits,
    )
}
