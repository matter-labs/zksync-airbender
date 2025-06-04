use super::*;
use crate::machine::machine_configurations::state_transition_parts::*;

pub(crate) fn optimized_reduced_isa_state_transition<
    F: PrimeField,
    CS: Circuit<F>,
    const ASSUME_TRUSTED_CODE: bool,
    const OUTPUT_EXACT_EXCEPTIONS: bool,
    const PERFORM_DELEGATION: bool,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    cs: &mut CS,
    decode_table_splitting: [usize; 2],
    boolean_keys: DecoderOutputExtraKeysHolder,
) -> (
    MinimalStateRegistersInMemory<F>,
    MinimalStateRegistersInMemory<F>,
) {
    let initial_state = MinimalStateRegistersInMemory::<F>::initialize(cs);

    // now apply decoding and all the opcodes.
    // Note that we use custom decoder here

    let pc = *initial_state.get_pc();

    // In the decoder function below PC will be used as:
    // - take high part and split, so it's range checked
    // - then low part will be joined with high part and opcode lookup will happen
    // So, we need to range check low part only
    cs.require_invariant(
        pc.0[0].get_variable(),
        Invariant::RangeChecked {
            width: LIMB_WIDTH as u32,
        },
    );

    // TODO: because PCs are part of the state and are linked from the previous row, then by recursion they are range checked,
    // and we may consider to remove this extra range check completely

    // TODO: Reading opcode from ROM here checks that PC % 4 == 0, so we can skip checks for PC % 4 == 0 in jump and branch instructions
    let (memory_queries, src1, src2, raw_decoder_output, flags_source, opcode_types_bits) =
        optimized_decode_and_preallocate_mem_queries_for_bytecode_in_rom::<
            F,
            CS,
            ASSUME_TRUSTED_CODE,
            PERFORM_DELEGATION,
            ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
        >(cs, pc, decode_table_splitting, boolean_keys);

    // now with PC considered range-checked we can compute next PC without overflows
    let next_pc = calculate_pc_next_no_overflows(cs, pc);

    let mut opt_ctx = OptimizationContext::<F, CS>::new();

    let src1 = RegisterDecompositionWithSign::parse_reg(cs, src1);
    let src2 = RegisterDecompositionWithSign::parse_reg(cs, src2);

    let decoder_output = BasicDecodingResultWithSigns {
        pc_next: next_pc,
        src1,
        src2,
        rs2_index: raw_decoder_output.rs2.clone(),
        imm: raw_decoder_output.imm,
        funct3: raw_decoder_output.funct3,
        funct12: raw_decoder_output.funct12,
    };
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

    // now it's time to merge state

    assert!(OUTPUT_EXACT_EXCEPTIONS == false);

    let final_state = writeback_no_exception_with_opcodes_in_rom::<
        F,
        CS,
        ASSUME_TRUSTED_CODE,
        PERFORM_DELEGATION,
    >(
        cs,
        opcode_types_bits,
        raw_decoder_output.rd,
        rs1_query,
        rs2_or_mem_load_query,
        rd_or_mem_store_query,
        application_results,
        next_pc,
        &opt_ctx,
    );

    (initial_state, final_state)
}
