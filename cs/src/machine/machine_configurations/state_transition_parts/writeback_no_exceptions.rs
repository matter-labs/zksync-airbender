use super::*;
use crate::machine::machine_configurations::minimal_state::MinimalStateRegistersInMemory;

pub(crate) fn writeback_no_exception_with_opcodes_in_rom<
    F: PrimeField,
    CS: Circuit<F>,
    const ASSUME_TRUSTED_CODE: bool,
    const PERFORM_DELEGATION: bool,
>(
    cs: &mut CS,
    opcode_format_bits: [Boolean; NUM_INSTRUCTION_TYPES_IN_DECODE_BITS],
    rd_constraint: Constraint<F>,
    rs1_query: ShuffleRamMemQuery,
    rs2_or_mem_load_query: ShuffleRamMemQuery,
    rd_or_mem_store_query: ShuffleRamMemQuery,
    application_results: Vec<CommonDiffs<F>>,
    default_next_pc: Register<F>,
    opt_ctx: &OptimizationContext<F, CS>,
) -> MinimalStateRegistersInMemory<F> {
    if ASSUME_TRUSTED_CODE {
        // we can NOT have exceptions coming from the reachable code itself

        // NOTE: if we have the code that is "sound", then any broken invariant will either be:
        // - caught in the opcode, so circuit is unsatisfiable
        // - logical "panic" from the code will finish the program, that will be either UNIMP, or just
        // panic handler that will logically finish the program
        if application_results.iter().all(|el| el.trapped.is_none()) {
            // there are no traps in opcodes support,
            // we can just apply state updates

            // we do not care about predicating state updates below, because if trap happens it's already unsatisfiable circuit

            let new_reg_val = CommonDiffs::select_final_rd_value(cs, &application_results);

            // if we will not update register and do not execute memory store, then
            // we still want to model it as reading x0 (and writing back hardcoded 0)

            let [r_insn, i_insn, _s_insn, b_insn, u_insn, j_insn] = opcode_format_bits;

            // opcode formats are orthogonal flags, so a boolean to update RD is just a linear combination
            let update_rd = Constraint::from(r_insn.get_variable().unwrap())
                + Constraint::from(i_insn.get_variable().unwrap())
                + Constraint::from(j_insn.get_variable().unwrap())
                + Constraint::from(u_insn.get_variable().unwrap());

            let rd = cs.add_variable_from_constraint_allow_explicit_linear(rd_constraint.clone());
            let reg_is_zero = cs.is_zero(Num::Var(rd));
            // we ALWAYS write to register (with maybe modified value), unless we write to RAM, except for B-format opcodes (
            // that are modeled as write 0 to x0)

            // Mask to get 0s if we write into x0
            let reg_write_value_low = cs.add_variable_from_constraint(
                (Term::from(1) - Term::from(reg_is_zero.get_variable().unwrap()))
                    * Term::from(new_reg_val.0[0]),
            );
            let reg_write_value_high = cs.add_variable_from_constraint(
                (Term::from(1) - Term::from(reg_is_zero.get_variable().unwrap()))
                    * Term::from(new_reg_val.0[1]),
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
            // if we write to RD - we should make a constraint over the address, that it comes from opcode
            cs.add_constraint((rd_constraint.clone() - Term::from(address[0])) * update_rd.clone());
            cs.add_constraint((Term::from(address[1])) * update_rd.clone());
            // x0 for BRANCH instructions as it's not even encoded in the opcode
            cs.add_constraint((Term::from(address[0])) * Term::from(b_insn));
            cs.add_constraint((Term::from(address[1])) * Term::from(b_insn));

            // and constraint value
            cs.add_constraint(
                (Term::from(reg_write_value_low)
                    - Term::from(rd_or_mem_store_query.write_value[0]))
                    * update_rd.clone(),
            );
            cs.add_constraint(
                (Term::from(reg_write_value_high)
                    - Term::from(rd_or_mem_store_query.write_value[1]))
                    * update_rd.clone(),
            );
            // 0 for BRANCH instructions
            cs.add_constraint(
                (Term::from(rd_or_mem_store_query.write_value[0])) * Term::from(b_insn),
            );
            cs.add_constraint(
                (Term::from(rd_or_mem_store_query.write_value[1])) * Term::from(b_insn),
            );

            // push all memory queries
            cs.add_shuffle_ram_query(rs1_query);
            cs.add_shuffle_ram_query(rs2_or_mem_load_query);
            cs.add_shuffle_ram_query(rd_or_mem_store_query);

            let new_pc =
                CommonDiffs::select_final_pc_value(cs, &application_results, default_next_pc);

            let final_state = MinimalStateRegistersInMemory { pc: new_pc };

            cs.set_log(&opt_ctx, "EXECUTOR");
            cs.view_log(if PERFORM_DELEGATION {
                "ISA_WITH_DELEGATION"
            } else {
                "ISA_WITHOUT_DELEGATION"
            });

            final_state
        } else {
            todo!()
        }
    } else {
        unreachable!()
    }
}
