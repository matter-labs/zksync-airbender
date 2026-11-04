use super::*;

pub(crate) unsafe fn evaluate_memory_init_teardown_ordering(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    witness_trace_view_row: &[Mersenne31Field],
    memory_trace_view_row: &[Mersenne31Field],
    memory_trace_view_next_row: &[Mersenne31Field],
    _tau_in_domain: &Mersenne31Complex,
    tau_in_domain_by_half: &Mersenne31Complex,
    absolute_row_idx: usize,
    is_last_two_rows: bool,
    quotient_term: &mut Mersenne31Quartic,
    every_row_except_last_two_challenges_ptr: &mut *const Mersenne31Quartic,
) {
    const SHIFT_16: Mersenne31Field = Mersenne31Field(1u32 << 16);

    for (lazy_init_address_aux_vars, shuffle_ram_inits_and_teardowns) in
        compiled_circuit.lazy_init_address_aux_vars.iter().zip(
            compiled_circuit
                .memory_layout
                .shuffle_ram_inits_and_teardowns
                .iter(),
        )
    {
        let lazy_init_address_start = shuffle_ram_inits_and_teardowns
            .lazy_init_addresses_columns
            .start();
        let lazy_init_address_low = lazy_init_address_start;
        let lazy_init_address_high = lazy_init_address_start + 1;

        let ShuffleRamAuxComparisonSet {
            aux_low_high: [address_aux_low, address_aux_high],
            intermediate_borrow,
            final_borrow,
        } = *lazy_init_address_aux_vars;
        // first we do low: this - next with borrow
        let this_low = *memory_trace_view_row.get_unchecked(lazy_init_address_low);
        let next_low = *memory_trace_view_next_row.get_unchecked(lazy_init_address_low);
        let aux_low = read_value(
            address_aux_low,
            witness_trace_view_row,
            memory_trace_view_row,
        );
        let intermediate_borrow_value = read_value(
            intermediate_borrow,
            witness_trace_view_row,
            memory_trace_view_row,
        );
        let final_borrow_value =
            read_value(final_borrow, witness_trace_view_row, memory_trace_view_row);

        let mut term_contribution = SHIFT_16;
        term_contribution.mul_assign(&intermediate_borrow_value);
        term_contribution.add_assign(&this_low);
        term_contribution.sub_assign(&next_low);
        term_contribution.sub_assign(&aux_low);
        if DEBUG_QUOTIENT {
            if is_last_two_rows == false {
                assert_eq!(
                    term_contribution,
                    Mersenne31Field::ZERO,
                    "unsatisfied at lazy init address sorting low at row idx {}",
                    absolute_row_idx
                );
            }
        }
        let mut term_contribution_ext2 = *tau_in_domain_by_half;
        term_contribution_ext2.mul_assign_by_base(&term_contribution);
        add_quotient_term_contribution_in_ext2(
            every_row_except_last_two_challenges_ptr,
            term_contribution_ext2,
            quotient_term,
        );

        // then we do high: this - next with borrow
        let this_high = *memory_trace_view_row.get_unchecked(lazy_init_address_high);
        let next_high = *memory_trace_view_next_row.get_unchecked(lazy_init_address_high);
        let aux_high = read_value(
            address_aux_high,
            witness_trace_view_row,
            memory_trace_view_row,
        );

        let mut term_contribution = SHIFT_16;
        term_contribution.mul_assign(&final_borrow_value);
        term_contribution.add_assign(&this_high);
        term_contribution.sub_assign(&intermediate_borrow_value);
        term_contribution.sub_assign(&next_high);
        term_contribution.sub_assign(&aux_high);
        if DEBUG_QUOTIENT {
            if is_last_two_rows == false {
                assert_eq!(
                    term_contribution,
                    Mersenne31Field::ZERO,
                    "unsatisfied at lazy init address sorting highat row idx {}",
                    absolute_row_idx
                );
            }
        }

        let mut term_contribution_ext2 = *tau_in_domain_by_half;
        term_contribution_ext2.mul_assign_by_base(&term_contribution);
        add_quotient_term_contribution_in_ext2(
            every_row_except_last_two_challenges_ptr,
            term_contribution_ext2,
            quotient_term,
        );
    }
}
