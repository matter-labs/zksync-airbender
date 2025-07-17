use super::*;

#[inline]
pub(crate) unsafe fn evaluate_lookup_arguments_consistency(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    _witness_trace_view_row: &[Mersenne31Field],
    _memory_trace_view_row: &[Mersenne31Field],
    _setup_trace_view_row: &[Mersenne31Field],
    stage_2_trace_view_row: &[Mersenne31Field],
    _tau_in_domain: &Mersenne31Complex,
    tau_in_domain_by_half: &Mersenne31Complex,
    _absolute_row_idx: usize,
    is_last_row: bool,
    quotient_term: &mut Mersenne31Quartic,
    last_row_and_at_zero_challenges_ptr: &mut *const Mersenne31Quartic,
) {
    // range check 16
    if compiled_circuit
        .witness_layout
        .multiplicities_columns_for_range_check_16
        .num_elements()
        > 0
    {
        let multiplicity_aux = stage_2_trace_view_row
            .as_ptr()
            .add(
                compiled_circuit
                    .stage_2_layout
                    .intermediate_poly_for_range_check_16_multiplicity
                    .start(),
            )
            .cast::<Mersenne31Quartic>()
            .read();
        let mut term_contribution = multiplicity_aux;

        for i in 0..compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_range_check_16
            .num_pairs
        {
            let el = stage_2_trace_view_row
                .as_ptr()
                .add(
                    compiled_circuit
                        .stage_2_layout
                        .intermediate_polys_for_range_check_16
                        .ext_4_field_oracles
                        .get_range(i)
                        .start,
                )
                .cast::<Mersenne31Quartic>()
                .read();
            term_contribution.sub_assign(&el);
        }
        // add lazy init value
        if compiled_circuit
            .memory_layout
            .shuffle_ram_inits_and_teardowns
            .is_empty()
            == false
        {
            let lazy_init_address_range_check_16 = compiled_circuit
                .stage_2_layout
                .lazy_init_address_range_check_16
                .unwrap();
            assert_eq!(
                compiled_circuit
                    .memory_layout
                    .shuffle_ram_inits_and_teardowns
                    .len(),
                lazy_init_address_range_check_16.num_pairs
            );
            for i in 0..lazy_init_address_range_check_16.num_pairs {
                let el = stage_2_trace_view_row
                    .as_ptr()
                    .add(
                        lazy_init_address_range_check_16
                            .ext_4_field_oracles
                            .get_range(i)
                            .start,
                    )
                    .cast::<Mersenne31Quartic>()
                    .read();
                term_contribution.sub_assign(&el);
            }
        }
        if let Some(_remainder) = compiled_circuit.stage_2_layout.remainder_for_range_check_16 {
            todo!();
        }
        if DEBUG_QUOTIENT {
            if is_last_row {
                assert_eq!(
                    term_contribution,
                    Mersenne31Quartic::ZERO,
                    "unsatisfied at lookups aux polys difference for range check 16 at last row"
                );
            }
        }
        // linear
        term_contribution.mul_assign_by_base(tau_in_domain_by_half);
        add_quotient_term_contribution_in_ext4(
            last_row_and_at_zero_challenges_ptr,
            term_contribution,
            quotient_term,
        );
    }

    // timestamp range check
    if compiled_circuit
        .witness_layout
        .multiplicities_columns_for_timestamp_range_check
        .num_elements()
        > 0
    {
        let multiplicity_aux = stage_2_trace_view_row
            .as_ptr()
            .add(
                compiled_circuit
                    .stage_2_layout
                    .intermediate_poly_for_timestamp_range_check_multiplicity
                    .start(),
            )
            .cast::<Mersenne31Quartic>()
            .read();
        let mut term_contribution = multiplicity_aux;

        for i in 0..compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_timestamp_range_checks
            .num_pairs
        {
            let el = stage_2_trace_view_row
                .as_ptr()
                .add(
                    compiled_circuit
                        .stage_2_layout
                        .intermediate_polys_for_timestamp_range_checks
                        .ext_4_field_oracles
                        .get_range(i)
                        .start,
                )
                .cast::<Mersenne31Quartic>()
                .read();
            term_contribution.sub_assign(&el);
        }
        if DEBUG_QUOTIENT {
            if is_last_row {
                assert_eq!(term_contribution, Mersenne31Quartic::ZERO, "unsatisfied at lookups aux polys difference for timestamp range check at last row");
            }
        }
        // linear
        term_contribution.mul_assign_by_base(tau_in_domain_by_half);
        add_quotient_term_contribution_in_ext4(
            last_row_and_at_zero_challenges_ptr,
            term_contribution,
            quotient_term,
        );
    }

    // decoder state lookup
    if compiled_circuit
        .stage_2_layout
        .intermediate_poly_for_decoder_accesses
        .num_elements()
        > 0
    {
        let multiplicity_aux = stage_2_trace_view_row
            .as_ptr()
            .add(
                compiled_circuit
                    .stage_2_layout
                    .intermediate_polys_for_decoder_multiplicities
                    .start(),
            )
            .cast::<Mersenne31Quartic>()
            .read();
        let mut term_contribution = multiplicity_aux;

        let el = stage_2_trace_view_row
            .as_ptr()
            .add(
                compiled_circuit
                    .stage_2_layout
                    .intermediate_poly_for_decoder_accesses
                    .start(),
            )
            .cast::<Mersenne31Quartic>()
            .read();
        term_contribution.sub_assign(&el);
        if DEBUG_QUOTIENT {
            if is_last_row {
                assert_eq!(
                    term_contribution,
                    Mersenne31Quartic::ZERO,
                    "unsatisfied at lookups aux polys difference for decoder table at last row"
                );
            }
        }
        // linear
        term_contribution.mul_assign_by_base(tau_in_domain_by_half);
        add_quotient_term_contribution_in_ext4(
            last_row_and_at_zero_challenges_ptr,
            term_contribution,
            quotient_term,
        );
    }

    // generic lookup
    if compiled_circuit
        .witness_layout
        .multiplicities_columns_for_generic_lookup
        .num_elements()
        > 0
    {
        assert!(
            compiled_circuit
                .stage_2_layout
                .intermediate_polys_for_generic_lookup
                .num_elements()
                > 0
        );
        let mut term_contribution = Mersenne31Quartic::ZERO;
        for i in 0..compiled_circuit
            .witness_layout
            .multiplicities_columns_for_generic_lookup
            .num_elements()
        {
            let ptr = stage_2_trace_view_row
                .as_ptr()
                .add(
                    compiled_circuit
                        .stage_2_layout
                        .intermediate_polys_for_generic_multiplicities
                        .get_range(i)
                        .start,
                )
                .cast::<Mersenne31Quartic>();
            assert!(ptr.is_aligned());
            let multiplicity_aux = ptr.read();
            term_contribution.add_assign(&multiplicity_aux);
        }

        for i in 0..compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_generic_lookup
            .num_elements()
        {
            let ptr = stage_2_trace_view_row
                .as_ptr()
                .add(
                    compiled_circuit
                        .stage_2_layout
                        .intermediate_polys_for_generic_lookup
                        .get_range(i)
                        .start,
                )
                .cast::<Mersenne31Quartic>();
            assert!(ptr.is_aligned());
            let el = ptr.read();
            term_contribution.sub_assign(&el);
        }
        if DEBUG_QUOTIENT {
            if is_last_row {
                assert_eq!(
                    term_contribution,
                    Mersenne31Quartic::ZERO,
                    "unsatisfied at lookups aux polys difference for generic lookup at last row"
                );
            }
        }
        // linear
        term_contribution.mul_assign_by_base(tau_in_domain_by_half);
        add_quotient_term_contribution_in_ext4(
            last_row_and_at_zero_challenges_ptr,
            term_contribution,
            quotient_term,
        );
    }
}
