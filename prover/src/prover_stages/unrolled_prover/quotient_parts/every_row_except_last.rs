use super::*;

#[inline]
pub(crate) unsafe fn evaluate_generic_constraints(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    witness_trace_view_row: &[Mersenne31Field],
    memory_trace_view_row: &[Mersenne31Field],
    setup_trace_view_row: &[Mersenne31Field],
    tau_in_domain: &Mersenne31Complex,
    tau_in_domain_by_half: &Mersenne31Complex,
    quadratic_terms_challenges: &[Mersenne31Quartic],
    linear_terms_challenges: &[Mersenne31Quartic],
    absolute_row_idx: usize,
    is_last_row: bool,
) -> Mersenne31Quartic {
    let mut quotient_quadratic_accumulator = Mersenne31Quartic::ZERO;
    let mut quotient_linear_accumulator = Mersenne31Quartic::ZERO;
    let mut quotient_constant_accumulator = Mersenne31Quartic::ZERO;

    //  Quadratic terms
    let bound = compiled_circuit.degree_2_constraints.len();
    let num_boolean_constraints = compiled_circuit
        .witness_layout
        .boolean_vars_columns_range
        .num_elements();

    // special case for boolean constraints
    let start = compiled_circuit
        .witness_layout
        .boolean_vars_columns_range
        .start();
    for i in 0..num_boolean_constraints {
        // a^2 - a
        let challenge = *quadratic_terms_challenges.get_unchecked(i);
        let value = *witness_trace_view_row.get_unchecked(start + i);
        let mut t = value;
        t.square();

        let mut quadratic = challenge;
        quadratic.mul_assign_by_base(&t);
        quotient_quadratic_accumulator.add_assign(&quadratic);

        let mut linear = challenge;
        linear.mul_assign_by_base(&value);
        quotient_linear_accumulator.sub_assign(&linear);

        if DEBUG_QUOTIENT {
            assert!(compiled_circuit
                .degree_2_constraints
                .get_unchecked(i)
                .is_boolean_constraint());

            let mut term_contribution = value;
            term_contribution.square();
            term_contribution.sub_assign(&value);

            if is_last_row == false {
                assert!(value == Mersenne31Field::ZERO || value == Mersenne31Field::ONE);
                assert_eq!(
                    term_contribution,
                    Mersenne31Field::ZERO,
                    "unsatisfied at row {} boolean constraint {}: {:?}",
                    absolute_row_idx,
                    i,
                    compiled_circuit.degree_2_constraints.get_unchecked(i),
                );
            }
        }
    }
    for i in num_boolean_constraints..bound {
        let challenge = *quadratic_terms_challenges.get_unchecked(i);
        let term = compiled_circuit.degree_2_constraints.get_unchecked(i);
        term.evaluate_at_row_with_accumulation(
            &*witness_trace_view_row,
            &*memory_trace_view_row,
            &challenge,
            &mut quotient_quadratic_accumulator,
            &mut quotient_linear_accumulator,
            &mut quotient_constant_accumulator,
        );

        if DEBUG_QUOTIENT {
            let term_contribution =
                term.evaluate_at_row_on_main_domain(witness_trace_view_row, memory_trace_view_row);
            if is_last_row == false {
                assert_eq!(
                    term_contribution,
                    Mersenne31Field::ZERO,
                    "unsatisfied at row {} at degree-2 constraint {}: {:?}",
                    absolute_row_idx,
                    i,
                    compiled_circuit.degree_2_constraints.get_unchecked(i),
                );
            }
        }
    }

    quotient_quadratic_accumulator.mul_assign_by_base(tau_in_domain);

    // Linear terms
    let bound = compiled_circuit.degree_1_constraints.len();
    for i in 0..bound {
        let challenge = *linear_terms_challenges.get_unchecked(i);
        let term = compiled_circuit.degree_1_constraints.get_unchecked(i);
        term.evaluate_at_row_with_accumulation(
            &*witness_trace_view_row,
            &*memory_trace_view_row,
            &challenge,
            &mut quotient_linear_accumulator,
            &mut quotient_constant_accumulator,
        );

        if DEBUG_QUOTIENT {
            let term_contribution = term.evaluate_at_row_on_main_domain_ext(
                witness_trace_view_row,
                memory_trace_view_row,
                setup_trace_view_row,
            );

            if is_last_row == false {
                assert_eq!(
                    term_contribution,
                    Mersenne31Field::ZERO,
                    "unsatisfied at row {} degree-1 constraint {}: {:?}",
                    absolute_row_idx,
                    i,
                    compiled_circuit.degree_1_constraints.get_unchecked(i),
                );
            }
        }
    }
    quotient_linear_accumulator.mul_assign_by_base(tau_in_domain_by_half);

    let mut quotient_term = quotient_constant_accumulator;
    quotient_term.add_assign(&quotient_quadratic_accumulator);
    quotient_term.add_assign(&quotient_linear_accumulator);

    if DEBUG_QUOTIENT {
        if is_last_row == false {
            assert_eq!(
                quotient_term,
                Mersenne31Quartic::ZERO,
                "unsatisfied over user constraints at row {}",
                absolute_row_idx
            );
        }
    }

    quotient_term
}

#[inline]
pub(crate) unsafe fn evaluate_delegation_processing_conventions(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    _witness_trace_view_row: &[Mersenne31Field],
    memory_trace_view_row: &[Mersenne31Field],
    _setup_trace_view_row: &[Mersenne31Field],
    _tau_in_domain: &Mersenne31Complex,
    tau_in_domain_by_half: &Mersenne31Complex,
    absolute_row_idx: usize,
    is_last_row: bool,
    quotient_term: &mut Mersenne31Quartic,
    other_challenges_ptr: &mut *const Mersenne31Quartic,
    delegation_processor_layout: &DelegationProcessingLayout,
) {
    let predicate =
        *memory_trace_view_row.get_unchecked(delegation_processor_layout.multiplicity.start());
    let mut t = *tau_in_domain_by_half;
    t.mul_assign_by_base(&predicate);
    let mut t_minus_one = t;
    t_minus_one.sub_assign_base(&Mersenne31Field::ONE);

    // predicate is 0/1
    let mut term_contribution = t;
    term_contribution.mul_assign(&t_minus_one);
    if DEBUG_QUOTIENT {
        if is_last_row == false {
            assert_eq!(
                term_contribution,
                Mersenne31Complex::ZERO,
                "unsatisfied for delegation convention: predicate is 0/1 at row {}",
                absolute_row_idx
            );
        }
    }
    add_quotient_term_contribution_in_ext2(other_challenges_ptr, term_contribution, quotient_term);

    // now the rest of the values have to be 0s
    // we want a constraint of (predicate - 1) * value == 0

    let mut t_minus_one_adjusted = t_minus_one;
    t_minus_one_adjusted.mul_assign(&tau_in_domain_by_half);

    // - mem abi offset == 0
    let mut term_contribution = t_minus_one_adjusted;
    term_contribution.mul_assign_by_base(
        memory_trace_view_row
            .get_unchecked(delegation_processor_layout.abi_mem_offset_high.start()),
    );
    if DEBUG_QUOTIENT {
        if is_last_row == false {
            assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: mem offset high is 0 if predicate is 0 at row {}", absolute_row_idx);
        }
    }
    add_quotient_term_contribution_in_ext2(other_challenges_ptr, term_contribution, quotient_term);

    // - write timestamp == 0
    let mut term_contribution = t_minus_one_adjusted;
    term_contribution.mul_assign_by_base(
        memory_trace_view_row.get_unchecked(delegation_processor_layout.write_timestamp.start()),
    );
    if DEBUG_QUOTIENT {
        if is_last_row == false {
            assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: write timestamp low is 0 if predicate is 0 at row {}", absolute_row_idx);
        }
    }
    add_quotient_term_contribution_in_ext2(other_challenges_ptr, term_contribution, quotient_term);

    let mut term_contribution = t_minus_one_adjusted;
    term_contribution.mul_assign_by_base(
        memory_trace_view_row
            .get_unchecked(delegation_processor_layout.write_timestamp.start() + 1),
    );
    if DEBUG_QUOTIENT {
        if is_last_row == false {
            assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: write timestamp high is 0 if predicate is 0 at row {}", absolute_row_idx);
        }
    }
    add_quotient_term_contribution_in_ext2(other_challenges_ptr, term_contribution, quotient_term);

    // for every value we check that read timestamp == 0
    // for every read value we check that value == 0
    // for every written value value we check that value == 0

    let bound = compiled_circuit.memory_layout.batched_ram_accesses.len();
    for access_idx in 0..bound {
        let access = *compiled_circuit
            .memory_layout
            .batched_ram_accesses
            .get_unchecked(access_idx);
        match access {
            BatchedRamAccessColumns::ReadAccess {
                read_timestamp,
                read_value,
            } => {
                for set in [read_timestamp, read_value].into_iter() {
                    // low and high
                    let mut term_contribution = t_minus_one_adjusted;
                    term_contribution
                        .mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start()));
                    if DEBUG_QUOTIENT {
                        if is_last_row == false {
                            assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value low is 0 if predicate is 0 at row {}", absolute_row_idx);
                        }
                    }
                    add_quotient_term_contribution_in_ext2(
                        other_challenges_ptr,
                        term_contribution,
                        quotient_term,
                    );

                    let mut term_contribution = t_minus_one_adjusted;
                    term_contribution
                        .mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start() + 1));
                    if DEBUG_QUOTIENT {
                        if is_last_row == false {
                            assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value high is 0 if predicate is 0 at row {}", absolute_row_idx);
                        }
                    }
                    add_quotient_term_contribution_in_ext2(
                        other_challenges_ptr,
                        term_contribution,
                        quotient_term,
                    );
                }
            }
            BatchedRamAccessColumns::WriteAccess {
                read_timestamp,
                read_value,
                write_value,
            } => {
                for set in [read_timestamp, read_value, write_value].into_iter() {
                    // low and high
                    let mut term_contribution = t_minus_one_adjusted;
                    term_contribution
                        .mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start()));
                    if DEBUG_QUOTIENT {
                        if is_last_row == false {
                            assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value/write value low is 0 if predicate is 0 at row {}", absolute_row_idx);
                        }
                    }
                    add_quotient_term_contribution_in_ext2(
                        other_challenges_ptr,
                        term_contribution,
                        quotient_term,
                    );

                    let mut term_contribution = t_minus_one_adjusted;
                    term_contribution
                        .mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start() + 1));
                    if DEBUG_QUOTIENT {
                        if is_last_row == false {
                            assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value/write value high is 0 if predicate is 0 at row {}", absolute_row_idx);
                        }
                    }
                    add_quotient_term_contribution_in_ext2(
                        other_challenges_ptr,
                        term_contribution,
                        quotient_term,
                    );
                }
            }
        }
    }

    // for every register and indirect access
    let bound = compiled_circuit
        .memory_layout
        .register_and_indirect_accesses
        .len();
    for access_idx in 0..bound {
        let access = compiled_circuit
            .memory_layout
            .register_and_indirect_accesses
            .get_unchecked(access_idx);
        match access.register_access {
            RegisterAccessColumns::ReadAccess {
                read_timestamp,
                read_value,
                ..
            } => {
                for set in [read_timestamp, read_value].into_iter() {
                    // low and high
                    let mut term_contribution = t_minus_one_adjusted;
                    term_contribution
                        .mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start()));
                    if DEBUG_QUOTIENT {
                        if is_last_row == false {
                            assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value low is 0 if predicate is 0 at row {} for access to register {}", absolute_row_idx, access.register_access.get_register_index());
                        }
                    }
                    add_quotient_term_contribution_in_ext2(
                        other_challenges_ptr,
                        term_contribution,
                        quotient_term,
                    );

                    let mut term_contribution = t_minus_one_adjusted;
                    term_contribution
                        .mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start() + 1));
                    if DEBUG_QUOTIENT {
                        if is_last_row == false {
                            assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value high is 0 if predicate is 0 at row {} for access to register {}", absolute_row_idx, access.register_access.get_register_index());
                        }
                    }
                    add_quotient_term_contribution_in_ext2(
                        other_challenges_ptr,
                        term_contribution,
                        quotient_term,
                    );
                }
            }
            RegisterAccessColumns::WriteAccess {
                read_timestamp,
                read_value,
                write_value,
                ..
            } => {
                for set in [read_timestamp, read_value, write_value].into_iter() {
                    // low and high
                    let mut term_contribution = t_minus_one_adjusted;
                    term_contribution
                        .mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start()));
                    if DEBUG_QUOTIENT {
                        if is_last_row == false {
                            assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value/write value low is 0 if predicate is 0 at row {} for access to register {}", absolute_row_idx, access.register_access.get_register_index());
                        }
                    }
                    add_quotient_term_contribution_in_ext2(
                        other_challenges_ptr,
                        term_contribution,
                        quotient_term,
                    );

                    let mut term_contribution = t_minus_one_adjusted;
                    term_contribution
                        .mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start() + 1));
                    if DEBUG_QUOTIENT {
                        if is_last_row == false {
                            assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value/write value high is 0 if predicate is 0 at row {} for access to register {}", absolute_row_idx, access.register_access.get_register_index());
                        }
                    }
                    add_quotient_term_contribution_in_ext2(
                        other_challenges_ptr,
                        term_contribution,
                        quotient_term,
                    );
                }
            }
        }

        let subbound = access.indirect_accesses.len();
        for indirect_access_idx in 0..subbound {
            let indirect_access = access.indirect_accesses.get_unchecked(indirect_access_idx);
            match indirect_access {
                IndirectAccessColumns::ReadAccess {
                    read_timestamp,
                    read_value,
                    address_derivation_carry_bit,
                    ..
                } => {
                    for set in [read_timestamp, read_value].into_iter() {
                        // low and high
                        let mut term_contribution = t_minus_one_adjusted;
                        term_contribution
                            .mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start()));
                        if DEBUG_QUOTIENT {
                            if is_last_row == false {
                                assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value low is 0 if predicate is 0 at row {} for access to register {} indirect access with offset {}", absolute_row_idx, access.register_access.get_register_index(), indirect_access.get_offset());
                            }
                        }
                        add_quotient_term_contribution_in_ext2(
                            other_challenges_ptr,
                            term_contribution,
                            quotient_term,
                        );

                        let mut term_contribution = t_minus_one_adjusted;
                        term_contribution.mul_assign_by_base(
                            memory_trace_view_row.get_unchecked(set.start() + 1),
                        );
                        if DEBUG_QUOTIENT {
                            if is_last_row == false {
                                assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value high is 0 if predicate is 0 at row {} for access to register {} indirect access with offset {}", absolute_row_idx, access.register_access.get_register_index(), indirect_access.get_offset());
                            }
                        }
                        add_quotient_term_contribution_in_ext2(
                            other_challenges_ptr,
                            term_contribution,
                            quotient_term,
                        );
                    }

                    // We only derive with non-trivial addition if it's not-first access
                    if indirect_access_idx > 0 {
                        let carry_bit = *memory_trace_view_row
                            .get_unchecked(address_derivation_carry_bit.start());
                        let mut term_contribution = *tau_in_domain_by_half;
                        term_contribution.mul_assign_by_base(&carry_bit);
                        term_contribution.sub_assign_base(&Mersenne31Field::ONE);
                        term_contribution.mul_assign_by_base(&carry_bit);
                        term_contribution.mul_assign(&tau_in_domain_by_half);
                        if DEBUG_QUOTIENT {
                            if is_last_row == false {
                                assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: carry bit is not boolean at row {} for access to register {} indirect access with offset {}", absolute_row_idx, access.register_access.get_register_index(), indirect_access.get_offset());
                            }
                        }
                        add_quotient_term_contribution_in_ext2(
                            other_challenges_ptr,
                            term_contribution,
                            quotient_term,
                        );
                    } else {
                        debug_assert_eq!(address_derivation_carry_bit.num_elements(), 0);
                    }
                }
                IndirectAccessColumns::WriteAccess {
                    read_timestamp,
                    read_value,
                    write_value,
                    address_derivation_carry_bit,
                    ..
                } => {
                    for set in [read_timestamp, read_value, write_value].into_iter() {
                        // low and high
                        let mut term_contribution = t_minus_one_adjusted;
                        term_contribution
                            .mul_assign_by_base(memory_trace_view_row.get_unchecked(set.start()));
                        if DEBUG_QUOTIENT {
                            if is_last_row == false {
                                assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value/write value low is 0 if predicate is 0 at row {} for access to register {} indirect access with offset {}", absolute_row_idx, access.register_access.get_register_index(), indirect_access.get_offset());
                            }
                        }
                        add_quotient_term_contribution_in_ext2(
                            other_challenges_ptr,
                            term_contribution,
                            quotient_term,
                        );

                        let mut term_contribution = t_minus_one_adjusted;
                        term_contribution.mul_assign_by_base(
                            memory_trace_view_row.get_unchecked(set.start() + 1),
                        );
                        if DEBUG_QUOTIENT {
                            if is_last_row == false {
                                assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value/write value high is 0 if predicate is 0 at row {} for access to register {} indirect access with offset {}", absolute_row_idx, access.register_access.get_register_index(), indirect_access.get_offset());
                            }
                        }
                        add_quotient_term_contribution_in_ext2(
                            other_challenges_ptr,
                            term_contribution,
                            quotient_term,
                        );
                    }

                    // We only derive with non-trivial addition if it's not-first access
                    if indirect_access_idx > 0 {
                        let carry_bit = *memory_trace_view_row
                            .get_unchecked(address_derivation_carry_bit.start());
                        let mut term_contribution = *tau_in_domain_by_half;
                        term_contribution.mul_assign_by_base(&carry_bit);
                        term_contribution.sub_assign_base(&Mersenne31Field::ONE);
                        term_contribution.mul_assign_by_base(&carry_bit);
                        term_contribution.mul_assign(&tau_in_domain_by_half);
                        if DEBUG_QUOTIENT {
                            if is_last_row == false {
                                assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: carry bit is not boolean at row {} for access to register {} indirect access with offset {}", absolute_row_idx, access.register_access.get_register_index(), indirect_access.get_offset());
                            }
                        }
                        add_quotient_term_contribution_in_ext2(
                            other_challenges_ptr,
                            term_contribution,
                            quotient_term,
                        );
                    } else {
                        debug_assert_eq!(address_derivation_carry_bit.num_elements(), 0);
                    }
                }
            }
        }
    }
}

#[inline]
pub(crate) unsafe fn evaluate_range_check_16_over_variables(
    _compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    witness_trace_view_row: &[Mersenne31Field],
    memory_trace_view_row: &[Mersenne31Field],
    _setup_trace_view_row: &[Mersenne31Field],
    stage_2_trace_view_row: &[Mersenne31Field],
    _tau_in_domain: &Mersenne31Complex,
    tau_in_domain_by_half: &Mersenne31Complex,
    _absolute_row_idx: usize,
    is_last_row: bool,
    quotient_term: &mut Mersenne31Quartic,
    other_challenges_ptr: &mut *const Mersenne31Quartic,
    lookup_argument_gamma: &Mersenne31Quartic,
    lookup_argument_two_gamma: &Mersenne31Quartic,
    range_check_16_width_1_lookups_access_ref: &[LookupWidth1SourceDestInformation],
) {
    // trivial case where range check is just over 1 variable
    for (i, lookup_set) in range_check_16_width_1_lookups_access_ref.iter().enumerate() {
        let c_offset = lookup_set.base_field_quadratic_oracle_col;
        let c = *stage_2_trace_view_row.get_unchecked(c_offset);
        let a = lookup_set.a_col;
        let b = lookup_set.b_col;
        let a_place = ColumnAddress::WitnessSubtree(a);
        let b_place = ColumnAddress::WitnessSubtree(b);
        let a = read_value(a_place, witness_trace_view_row, memory_trace_view_row);
        let b = read_value(b_place, witness_trace_view_row, memory_trace_view_row);

        if DEBUG_QUOTIENT {
            if is_last_row == false {
                assert!(
                    a.to_reduced_u32() < 1u32 << 16,
                    "unsatisfied at range check 16: value is {}",
                    a,
                );

                assert!(
                    b.to_reduced_u32() < 1u32 << 16,
                    "unsatisfied at range check 16: value is {}",
                    b,
                );
            }
        }

        let mut a_mul_by_b = a;
        a_mul_by_b.mul_assign(&b);

        let mut term_contribution = *tau_in_domain_by_half;
        term_contribution.mul_assign_by_base(&a_mul_by_b);
        term_contribution.sub_assign_base(&c);
        term_contribution.mul_assign(&tau_in_domain_by_half);
        if DEBUG_QUOTIENT {
            if is_last_row == false {
                assert_eq!(
                    term_contribution,
                    Mersenne31Complex::ZERO,
                    "unsatisfied at range check lookup base field oracle {}",
                    i
                );
            }
        }
        add_quotient_term_contribution_in_ext2(
            other_challenges_ptr,
            term_contribution,
            quotient_term,
        );

        // now accumulator * denom - numerator == 0
        let acc = lookup_set.ext4_field_inverses_columns_start;
        let acc_ptr = stage_2_trace_view_row
            .as_ptr()
            .add(acc)
            .cast::<Mersenne31Quartic>();
        debug_assert!(acc_ptr.is_aligned());

        let mut acc_value = acc_ptr.read();
        acc_value.mul_assign_by_base(tau_in_domain_by_half);

        let mut t = a;
        t.add_assign(&b);
        let mut a_plus_b_contribution = *tau_in_domain_by_half;
        a_plus_b_contribution.mul_assign_by_base(&t);

        let mut c_contribution = *tau_in_domain_by_half;
        c_contribution.mul_assign_by_base(&c);

        let mut denom = *lookup_argument_gamma;
        denom.add_assign_base(&a_plus_b_contribution);
        denom.mul_assign(lookup_argument_gamma);
        denom.add_assign_base(&c_contribution);
        // C(x) + gamma * (a(x) + b(x)) + gamma^2

        // a(x) + b(x) + 2 * gamma
        let mut numerator = *lookup_argument_two_gamma;
        numerator.add_assign_base(&a_plus_b_contribution);

        // Acc(x) * (C(x) + gamma * (a(x) + b(x)) + gamma^2) - (a(x) + b(x) + 2 * gamma)
        let mut term_contribution = denom;
        term_contribution.mul_assign(&acc_value);
        term_contribution.sub_assign(&numerator);
        if DEBUG_QUOTIENT {
            if is_last_row == false {
                assert_eq!(
                    term_contribution,
                    Mersenne31Quartic::ZERO,
                    "unsatisfied at range check lookup ext field oracle {}",
                    i
                );
            }
        }
        add_quotient_term_contribution_in_ext4(
            other_challenges_ptr,
            term_contribution,
            quotient_term,
        );
    }
}

#[inline]
pub(crate) unsafe fn evaluate_range_check_16_over_expressions(
    _compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    witness_trace_view_row: &[Mersenne31Field],
    memory_trace_view_row: &[Mersenne31Field],
    setup_trace_view_row: &[Mersenne31Field],
    stage_2_trace_view_row: &[Mersenne31Field],
    _tau_in_domain: &Mersenne31Complex,
    tau_in_domain_by_half: &Mersenne31Complex,
    _absolute_row_idx: usize,
    is_last_row: bool,
    quotient_term: &mut Mersenne31Quartic,
    other_challenges_ptr: &mut *const Mersenne31Quartic,
    lookup_argument_gamma: &Mersenne31Quartic,
    lookup_argument_two_gamma: &Mersenne31Quartic,
    range_check_16_width_1_lookups_access_via_expressions_ref: &[LookupWidth1SourceDestInformationForExpressions<Mersenne31Field>],
) {
    for (i, lookup_set) in range_check_16_width_1_lookups_access_via_expressions_ref
        .iter()
        .enumerate()
    {
        let c_offset = lookup_set.base_field_quadratic_oracle_col;
        let c = *stage_2_trace_view_row.get_unchecked(c_offset);
        let LookupExpression::Expression(a) = &lookup_set.a_expr else {
            unreachable!()
        };
        let LookupExpression::Expression(b) = &lookup_set.b_expr else {
            unreachable!()
        };
        let a = a.evaluate_at_row_ext(
            witness_trace_view_row,
            memory_trace_view_row,
            setup_trace_view_row,
            &tau_in_domain_by_half,
        );
        let b = b.evaluate_at_row_ext(
            witness_trace_view_row,
            memory_trace_view_row,
            setup_trace_view_row,
            &tau_in_domain_by_half,
        );

        if DEBUG_QUOTIENT {
            if is_last_row == false {
                assert!(
                    a.c0.to_reduced_u32() < 1u32 << 16,
                    "unsatisfied at range check 16: value is {}",
                    a,
                );

                assert!(
                    b.c0.to_reduced_u32() < 1u32 << 16,
                    "unsatisfied at range check 16: value is {}",
                    b,
                );
            }
        }

        let mut a_mul_by_b = a;
        a_mul_by_b.mul_assign(&b);

        let mut c_ext = *tau_in_domain_by_half;
        c_ext.mul_assign_by_base(&c);

        let mut term_contribution = a_mul_by_b;
        term_contribution.sub_assign_base(&c_ext);
        if DEBUG_QUOTIENT {
            if is_last_row == false {
                assert_eq!(
                    term_contribution,
                    Mersenne31Complex::ZERO,
                    "unsatisfied at range check lookup base field oracle {}",
                    i
                );
            }
        }
        add_quotient_term_contribution_in_ext2(
            other_challenges_ptr,
            term_contribution,
            quotient_term,
        );

        // now accumulator * denom - numerator == 0
        let acc = lookup_set.ext4_field_inverses_columns_start;
        let acc_ptr = stage_2_trace_view_row
            .as_ptr()
            .add(acc)
            .cast::<Mersenne31Quartic>();
        debug_assert!(acc_ptr.is_aligned());

        let mut acc_value = acc_ptr.read();
        acc_value.mul_assign_by_base(tau_in_domain_by_half);

        let mut a_plus_b_contribution = a;
        a_plus_b_contribution.add_assign(&b);

        let mut denom = *lookup_argument_gamma;
        denom.add_assign_base(&a_plus_b_contribution);
        denom.mul_assign(lookup_argument_gamma);
        denom.add_assign_base(&c_ext);
        // C(x) + gamma * (a(x) + b(x)) + gamma^2

        // a(x) + b(x) + 2 * gamma
        let mut numerator = *lookup_argument_two_gamma;
        numerator.add_assign_base(&a_plus_b_contribution);

        // Acc(x) * (C(x) + gamma * (a(x) + b(x)) + gamma^2) - (a(x) + b(x) + 2 * gamma)
        let mut term_contribution = denom;
        term_contribution.mul_assign(&acc_value);
        term_contribution.sub_assign(&numerator);
        if DEBUG_QUOTIENT {
            if is_last_row == false {
                assert_eq!(
                    term_contribution,
                    Mersenne31Quartic::ZERO,
                    "unsatisfied at range check lookup ext field oracle {}",
                    i
                );
            }
        }
        add_quotient_term_contribution_in_ext4(
            other_challenges_ptr,
            term_contribution,
            quotient_term,
        );
    }
}

#[inline]
pub(crate) unsafe fn evaluate_timestamp_range_check_expressions(
    _compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    witness_trace_view_row: &[Mersenne31Field],
    memory_trace_view_row: &[Mersenne31Field],
    setup_trace_view_row: &[Mersenne31Field],
    stage_2_trace_view_row: &[Mersenne31Field],
    _tau_in_domain: &Mersenne31Complex,
    tau_in_domain_by_half: &Mersenne31Complex,
    _absolute_row_idx: usize,
    is_last_row: bool,
    quotient_term: &mut Mersenne31Quartic,
    other_challenges_ptr: &mut *const Mersenne31Quartic,
    lookup_argument_gamma: &Mersenne31Quartic,
    lookup_argument_two_gamma: &Mersenne31Quartic,
    timestamp_range_check_width_1_lookups_access_via_expressions_ref: &[LookupWidth1SourceDestInformationForExpressions<Mersenne31Field>],
    timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram_ref: &[LookupWidth1SourceDestInformationForExpressions<Mersenne31Field>],
    memory_timestamp_high_from_circuit_idx: &Mersenne31Field,
) {
    let bound = timestamp_range_check_width_1_lookups_access_via_expressions_ref.len()
        + timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram_ref.len();
    let offset = timestamp_range_check_width_1_lookups_access_via_expressions_ref.len();
    // second part is where we have expressions as part of the range check, but do not need extra contribution from the timestamp
    // and the last part, where we also account for the circuit sequence in the write timestamp
    for i in 0..bound {
        let lookup_set = if i < offset {
            timestamp_range_check_width_1_lookups_access_via_expressions_ref.get_unchecked(i)
        } else {
            timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram_ref
                .get_unchecked(i - offset)
        };
        let c_offset = lookup_set.base_field_quadratic_oracle_col;
        let c = *stage_2_trace_view_row.get_unchecked(c_offset);
        let LookupExpression::Expression(a) = &lookup_set.a_expr else {
            unreachable!()
        };
        let LookupExpression::Expression(b) = &lookup_set.b_expr else {
            unreachable!()
        };
        let a = a.evaluate_at_row_ext(
            witness_trace_view_row,
            memory_trace_view_row,
            setup_trace_view_row,
            &tau_in_domain_by_half,
        );
        let mut b = b.evaluate_at_row_ext(
            witness_trace_view_row,
            memory_trace_view_row,
            setup_trace_view_row,
            &tau_in_domain_by_half,
        );
        if i >= offset {
            // width_1_lookups_access_via_expressions_for_shuffle_ram_ref need to account for extra contribution for timestamp high
            b.sub_assign_base(memory_timestamp_high_from_circuit_idx); // literal constant
        }

        if DEBUG_QUOTIENT {
            if is_last_row == false {
                assert!(
                    a.c0.to_reduced_u32() < 1u32 << TIMESTAMP_COLUMNS_NUM_BITS,
                    "unsatisfied at timestamp range check: value is {}",
                    a,
                );

                assert!(
                    b.c0.to_reduced_u32() < 1u32 << TIMESTAMP_COLUMNS_NUM_BITS,
                    "unsatisfied at timestamp range check: value is {}",
                    b,
                );
            }
        }

        let mut a_mul_by_b = a;
        a_mul_by_b.mul_assign(&b);

        let mut c_ext = *tau_in_domain_by_half;
        c_ext.mul_assign_by_base(&c);

        let mut term_contribution = a_mul_by_b;
        term_contribution.sub_assign_base(&c_ext);
        if DEBUG_QUOTIENT {
            if is_last_row == false {
                assert_eq!(
                    term_contribution,
                    Mersenne31Complex::ZERO,
                    "unsatisfied at range check lookup base field oracle {}",
                    i
                );
            }
        }
        add_quotient_term_contribution_in_ext2(
            other_challenges_ptr,
            term_contribution,
            quotient_term,
        );

        // now accumulator * denom - numerator == 0
        let acc = lookup_set.ext4_field_inverses_columns_start;
        let acc_ptr = stage_2_trace_view_row
            .as_ptr()
            .add(acc)
            .cast::<Mersenne31Quartic>();
        debug_assert!(acc_ptr.is_aligned());

        let mut acc_value = acc_ptr.read();
        acc_value.mul_assign_by_base(tau_in_domain_by_half);

        let mut a_plus_b_contribution = a;
        a_plus_b_contribution.add_assign(&b);

        let mut denom = *lookup_argument_gamma;
        denom.add_assign_base(&a_plus_b_contribution);
        denom.mul_assign(lookup_argument_gamma);
        denom.add_assign_base(&c_ext);
        // C(x) + gamma * (a(x) + b(x)) + gamma^2

        // a(x) + b(x) + 2 * gamma
        let mut numerator = *lookup_argument_two_gamma;
        numerator.add_assign_base(&a_plus_b_contribution);

        // Acc(x) * (C(x) + gamma * (a(x) + b(x)) + gamma^2) - (a(x) + b(x) + 2 * gamma)
        let mut term_contribution = denom;
        term_contribution.mul_assign(&acc_value);
        term_contribution.sub_assign(&numerator);
        if DEBUG_QUOTIENT {
            if is_last_row == false {
                assert_eq!(
                    term_contribution,
                    Mersenne31Quartic::ZERO,
                    "unsatisfied at range check lookup ext field oracle {}",
                    i
                );
            }
        }
        add_quotient_term_contribution_in_ext4(
            other_challenges_ptr,
            term_contribution,
            quotient_term,
        );
    }
}

#[inline]
pub(crate) unsafe fn evaluate_decoder_table_access(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    witness_trace_view_row: &[Mersenne31Field],
    memory_trace_view_row: &[Mersenne31Field],
    _setup_trace_view_row: &[Mersenne31Field],
    stage_2_trace_view_row: &[Mersenne31Field],
    _tau_in_domain: &Mersenne31Complex,
    tau_in_domain_by_half: &Mersenne31Complex,
    absolute_row_idx: usize,
    is_last_row: bool,
    quotient_term: &mut Mersenne31Quartic,
    other_challenges_ptr: &mut *const Mersenne31Quartic,
    decoder_table_linearization_challenges: &[Mersenne31Quartic;
        EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_LINEARIZATION_CHALLENGES],
    decoder_table_gamma: &Mersenne31Quartic,
) {
    // it's not too different from just the lookup, except instead of 1/(witness + gamma) we use execute/(witness + gamma)
    let intermediate_state_layout = compiled_circuit
        .memory_layout
        .intermediate_state_layout
        .as_ref()
        .unwrap();
    let IntermediateStatePermutationVariables {
        execute,
        pc,
        timestamp: _,
        rs1_index,
        rs2_index,
        rd_index,
        decoder_witness_is_in_memory,
        rd_is_zero,
        imm,
        funct3,
        funct7,
        circuit_family,
        circuit_family_extra_mask,
    } = *intermediate_state_layout;

    debug_assert!(funct7.num_elements() == 0);
    debug_assert!(circuit_family.num_elements() == 0);

    // read all the inputs

    let execute = *memory_trace_view_row.get_unchecked(execute.start());
    let pc: [Mersenne31Field; 2] = memory_trace_view_row
        .as_ptr()
        .add(pc.start())
        .cast::<[Mersenne31Field; 2]>()
        .read();

    let rs1_index = *memory_trace_view_row.get_unchecked(rs1_index.start());
    let rs2_index = read_value(rs2_index, witness_trace_view_row, memory_trace_view_row);
    let rd_index = read_value(rd_index, witness_trace_view_row, memory_trace_view_row);
    // there are rare cases when bitmask width is just 1 bit, and so we can just fit it into memory instead
    let circuit_family_extra_mask = read_value(
        circuit_family_extra_mask,
        witness_trace_view_row,
        memory_trace_view_row,
    );

    let (rd_is_zero, imm, funct3) = if decoder_witness_is_in_memory == false {
        let rd_is_zero = *witness_trace_view_row.get_unchecked(rd_is_zero.start());
        let imm: [Mersenne31Field; 2] = witness_trace_view_row
            .as_ptr()
            .add(imm.start())
            .cast::<[Mersenne31Field; 2]>()
            .read();
        let funct3 = *witness_trace_view_row.get_unchecked(funct3.start());

        (rd_is_zero, imm, funct3)
    } else {
        unreachable!()
    };

    let key_values_to_aggregate = [
        pc[1],
        rs1_index,
        rs2_index,
        rd_index,
        rd_is_zero,
        imm[0],
        imm[1],
        funct3,
        circuit_family_extra_mask,
    ];

    // acc * denom - execute == 0

    let denom = quotient_compute_aggregated_key_value(
        pc[0],
        key_values_to_aggregate,
        *decoder_table_linearization_challenges,
        *decoder_table_gamma,
        *tau_in_domain_by_half,
    );

    let acc_ptr = stage_2_trace_view_row
        .as_ptr()
        .add(
            compiled_circuit
                .stage_2_layout
                .intermediate_poly_for_decoder_accesses
                .start(),
        )
        .cast::<Mersenne31Quartic>();
    debug_assert!(acc_ptr.is_aligned());

    let acc_value = acc_ptr.read();

    let mut term_contribution = denom;
    term_contribution.mul_assign(&acc_value);
    term_contribution.sub_assign_base(&execute);
    term_contribution.mul_assign_by_base(tau_in_domain_by_half);

    if DEBUG_QUOTIENT {
        if is_last_row == false {
            assert_eq!(
                term_contribution,
                Mersenne31Quartic::ZERO,
                "unsatisfied at decoder table intermediate poly access at row {}",
                absolute_row_idx,
            );
        }
    }
    add_quotient_term_contribution_in_ext4(other_challenges_ptr, term_contribution, quotient_term);
}

#[inline]
pub(crate) unsafe fn evaluate_width_3_lookups(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    witness_trace_view_row: &[Mersenne31Field],
    memory_trace_view_row: &[Mersenne31Field],
    _setup_trace_view_row: &[Mersenne31Field],
    stage_2_trace_view_row: &[Mersenne31Field],
    _tau_in_domain: &Mersenne31Complex,
    tau_in_domain_by_half: &Mersenne31Complex,
    absolute_row_idx: usize,
    is_last_row: bool,
    quotient_term: &mut Mersenne31Quartic,
    other_challenges_ptr: &mut *const Mersenne31Quartic,
    lookup_argument_linearization_challenges: &[Mersenne31Quartic;
         NUM_LOOKUP_ARGUMENT_KEY_PARTS - 1],
    lookup_argument_linearization_challenges_without_table_id: &[Mersenne31Quartic;
         NUM_LOOKUP_ARGUMENT_KEY_PARTS
             - 2],
    lookup_argument_gamma: &Mersenne31Quartic,
) {
    for (i, lookup_set) in compiled_circuit
        .witness_layout
        .width_3_lookups
        .iter()
        .enumerate()
    {
        let mut table_id_contribution =
            lookup_argument_linearization_challenges[NUM_LOOKUP_ARGUMENT_KEY_PARTS - 2];
        match lookup_set.table_index {
            TableIndex::Constant(table_type) => {
                let table_id = Mersenne31Field(table_type.to_table_id());
                table_id_contribution.mul_assign_by_base(&table_id);
            }
            TableIndex::Variable(place) => {
                let mut t = *tau_in_domain_by_half;
                let table_id = read_value(place, &*witness_trace_view_row, &*memory_trace_view_row);
                t.mul_assign_by_base(&table_id);
                table_id_contribution.mul_assign_by_base(&t);
            }
        }

        let acc = compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_generic_lookup
            .get_range(i)
            .start;
        let acc_ptr = stage_2_trace_view_row
            .as_ptr()
            .add(acc)
            .cast::<Mersenne31Quartic>();
        assert!(acc_ptr.is_aligned());
        let mut acc_value = acc_ptr.read();
        acc_value.mul_assign_by_base(tau_in_domain_by_half);

        let input_values = std::array::from_fn(|i| {
            match &lookup_set.input_columns[i] {
                LookupExpression::Variable(place) => {
                    let mut t = *tau_in_domain_by_half;
                    t.mul_assign_by_base(&read_value(
                        *place,
                        &*witness_trace_view_row,
                        &*memory_trace_view_row,
                    ));

                    t
                }
                LookupExpression::Expression(constraint) => {
                    // as we allow constant to be non-zero, we have to evaluate as on non-main domain in general
                    // instead of once amortizing multiplication by tau in domain by half
                    constraint.evaluate_at_row(
                        &*witness_trace_view_row,
                        &*memory_trace_view_row,
                        &tau_in_domain_by_half,
                    )
                }
            }
        });

        let [input0, input1, input2] = input_values;
        let mut denom = quotient_compute_aggregated_key_value_in_ext2(
            input0,
            [input1, input2],
            *lookup_argument_linearization_challenges_without_table_id,
            *lookup_argument_gamma,
        );

        denom.add_assign(&table_id_contribution);

        let mut term_contribution = denom;
        term_contribution.mul_assign(&acc_value);
        term_contribution.sub_assign_base(&Mersenne31Field::ONE);

        if DEBUG_QUOTIENT {
            if is_last_row == false {
                let input = input_values.map(|el| {
                    assert!(el.c1.is_zero());
                    el.c0
                });

                let table_id = match lookup_set.table_index {
                    TableIndex::Constant(table_type) => table_type.to_table_id(),
                    TableIndex::Variable(place) => {
                        let table_id =
                            read_value(place, &*witness_trace_view_row, &*memory_trace_view_row);
                        assert!(
                            table_id.to_reduced_u32() as usize <= TABLE_TYPES_UPPER_BOUNDS,
                            "table ID is the integer between 0 and {}, but got {}",
                            TABLE_TYPES_UPPER_BOUNDS,
                            table_id
                        );

                        table_id.to_reduced_u32()
                    }
                };

                assert_eq!(
                    term_contribution,
                    Mersenne31Quartic::ZERO,
                    "unsatisfied at width 3 lookup set {} with table type {:?} at row {} with tuple {:?} and ID = {}",
                    i,
                    lookup_set.table_index,
                    absolute_row_idx,
                    input,
                    table_id,
                );
            }
        }
        add_quotient_term_contribution_in_ext4(
            other_challenges_ptr,
            term_contribution,
            quotient_term,
        );
    }
}

#[inline]
pub(crate) unsafe fn evaluate_width_1_range_check_multiplicity(
    _compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    witness_trace_view_row: &[Mersenne31Field],
    _memory_trace_view_row: &[Mersenne31Field],
    setup_trace_view_row: &[Mersenne31Field],
    stage_2_trace_view_row: &[Mersenne31Field],
    _tau_in_domain: &Mersenne31Complex,
    tau_in_domain_by_half: &Mersenne31Complex,
    absolute_row_idx: usize,
    is_last_row: bool,
    quotient_term: &mut Mersenne31Quartic,
    other_challenges_ptr: &mut *const Mersenne31Quartic,
    lookup_argument_gamma: &Mersenne31Quartic,
    intermediate_poly_offset: usize,
    range_check_multiplicities_src: usize,
    range_check_setup_column: usize,
) {
    let acc_ptr = stage_2_trace_view_row
        .as_ptr()
        .add(intermediate_poly_offset)
        .cast::<Mersenne31Quartic>();
    debug_assert!(acc_ptr.is_aligned());
    let acc_value = acc_ptr.read();

    let m = *witness_trace_view_row.get_unchecked(range_check_multiplicities_src);

    let mut t = *tau_in_domain_by_half;
    t.mul_assign_by_base(setup_trace_view_row.get_unchecked(range_check_setup_column));

    let mut denom = *lookup_argument_gamma;
    denom.add_assign_base(&t);

    // extra power to scale accumulator and multiplicity
    let mut term_contribution = denom;
    term_contribution.mul_assign(&acc_value);
    term_contribution.sub_assign_base(&m);
    term_contribution.mul_assign_by_base(tau_in_domain_by_half);

    if DEBUG_QUOTIENT {
        if is_last_row == false {
            assert_eq!(
                term_contribution,
                Mersenne31Quartic::ZERO,
                "unsatisfied at range check multiplicities column at row {}",
                absolute_row_idx,
            );
        }
    }
    add_quotient_term_contribution_in_ext4(other_challenges_ptr, term_contribution, quotient_term);
}

#[inline]
pub(crate) unsafe fn evaluate_decoder_lookup_multiplicity(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    witness_trace_view_row: &[Mersenne31Field],
    _memory_trace_view_row: &[Mersenne31Field],
    setup_trace_view_row: &[Mersenne31Field],
    stage_2_trace_view_row: &[Mersenne31Field],
    _tau_in_domain: &Mersenne31Complex,
    tau_in_domain_by_half: &Mersenne31Complex,
    _absolute_row_idx: usize,
    is_last_row: bool,
    quotient_term: &mut Mersenne31Quartic,
    other_challenges_ptr: &mut *const Mersenne31Quartic,
    decoder_table_linearization_challenges: &[Mersenne31Quartic;
        EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_LINEARIZATION_CHALLENGES],
    decoder_table_gamma: &Mersenne31Quartic,
) {
    let acc = compiled_circuit
        .stage_2_layout
        .intermediate_polys_for_decoder_multiplicities
        .start();
    let acc_ptr = stage_2_trace_view_row
        .as_ptr()
        .add(acc)
        .cast::<Mersenne31Quartic>();
    debug_assert!(acc_ptr.is_aligned());
    let acc_value = acc_ptr.read();

    let m = *witness_trace_view_row.get_unchecked(
        compiled_circuit
            .witness_layout
            .multiplicities_columns_for_decoder_in_executor_families
            .start(),
    );

    let src = setup_trace_view_row.as_ptr().add(
        compiled_circuit
            .setup_layout
            .preprocessed_decoder_setup_columns
            .start(),
    );
    let src0 = src.read();
    let rest = src
        .add(1)
        .cast::<[Mersenne31Field; EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_LINEARIZATION_CHALLENGES]>()
        .read();

    let denom = quotient_compute_aggregated_key_value(
        src0,
        rest,
        *decoder_table_linearization_challenges,
        *decoder_table_gamma,
        *tau_in_domain_by_half,
    );

    // extra power to scale accumulator and multiplicity
    let mut term_contribution = denom;
    term_contribution.mul_assign(&acc_value);
    term_contribution.sub_assign_base(&m);
    term_contribution.mul_assign_by_base(tau_in_domain_by_half);
    if DEBUG_QUOTIENT {
        if is_last_row == false {
            assert_eq!(
                term_contribution,
                Mersenne31Quartic::ZERO,
                "unsatisfied at decoder lookup multiplicities column",
            );
        }
    }
    add_quotient_term_contribution_in_ext4(other_challenges_ptr, term_contribution, quotient_term);
}

#[inline]
pub(crate) unsafe fn evaluate_width_3_lookups_multiplicity(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    witness_trace_view_row: &[Mersenne31Field],
    _memory_trace_view_row: &[Mersenne31Field],
    setup_trace_view_row: &[Mersenne31Field],
    stage_2_trace_view_row: &[Mersenne31Field],
    _tau_in_domain: &Mersenne31Complex,
    tau_in_domain_by_half: &Mersenne31Complex,
    _absolute_row_idx: usize,
    is_last_row: bool,
    quotient_term: &mut Mersenne31Quartic,
    other_challenges_ptr: &mut *const Mersenne31Quartic,
    lookup_argument_linearization_challenges: &[Mersenne31Quartic;
         NUM_LOOKUP_ARGUMENT_KEY_PARTS - 1],
    lookup_argument_gamma: &Mersenne31Quartic,
) {
    let generic_lookup_multiplicities_src_start = compiled_circuit
        .witness_layout
        .multiplicities_columns_for_generic_lookup
        .start();
    let generic_lookup_setup_columns_start = compiled_circuit
        .setup_layout
        .generic_lookup_setup_columns
        .start();

    for i in 0..compiled_circuit
        .witness_layout
        .multiplicities_columns_for_generic_lookup
        .num_elements()
    {
        let acc = compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_generic_multiplicities
            .get_range(i)
            .start;
        let acc_ptr = stage_2_trace_view_row
            .as_ptr()
            .add(acc)
            .cast::<Mersenne31Quartic>();
        debug_assert!(acc_ptr.is_aligned());
        let acc_value = acc_ptr.read();

        let m = *witness_trace_view_row.get_unchecked(generic_lookup_multiplicities_src_start + i);

        let start = generic_lookup_setup_columns_start + i * (COMMON_TABLE_WIDTH + 1);
        let [src0, src1, src2, src3] = setup_trace_view_row
            .as_ptr()
            .add(start)
            .cast::<[Mersenne31Field; COMMON_TABLE_WIDTH + 1]>()
            .read();

        let denom = quotient_compute_aggregated_key_value(
            src0,
            [src1, src2, src3],
            *lookup_argument_linearization_challenges,
            *lookup_argument_gamma,
            *tau_in_domain_by_half,
        );

        // extra power to scale accumulator and multiplicity
        let mut term_contribution = denom;
        term_contribution.mul_assign(&acc_value);
        term_contribution.sub_assign_base(&m);
        term_contribution.mul_assign_by_base(tau_in_domain_by_half);
        if DEBUG_QUOTIENT {
            if is_last_row == false {
                assert_eq!(
                    term_contribution,
                    Mersenne31Quartic::ZERO,
                    "unsatisfied at generic lookup multiplicities column",
                );
            }
        }
        add_quotient_term_contribution_in_ext4(
            other_challenges_ptr,
            term_contribution,
            quotient_term,
        );
    }
}

#[inline]
pub(crate) unsafe fn evaluate_memory_queries_accumulation(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    _witness_trace_view_row: &[Mersenne31Field],
    memory_trace_view_row: &[Mersenne31Field],
    _setup_trace_view_row: &[Mersenne31Field],
    stage_2_trace_view_row: &[Mersenne31Field],
    _tau_in_domain: &Mersenne31Complex,
    tau_in_domain_by_half: &Mersenne31Complex,
    absolute_row_idx: usize,
    is_last_row: bool,
    quotient_term: &mut Mersenne31Quartic,
    other_challenges_ptr: &mut *const Mersenne31Quartic,
    memory_argument_challenges: &ExternalMemoryArgumentChallenges,
    tau_in_domain_by_half_inv: &Mersenne31Complex,
    memory_argument_src: &mut *const Mersenne31Quartic,
    extra_write_timestamp_high: &Mersenne31Quartic,
    write_timestamp_low: Mersenne31Field,
    write_timestamp_high: Mersenne31Field,
) {
    for (access_idx, memory_access_columns) in compiled_circuit
        .memory_layout
        .shuffle_ram_access_sets
        .iter()
        .enumerate()
    {
        let read_value_columns = memory_access_columns.get_read_value_columns();
        let read_timestamp_columns = memory_access_columns.get_read_timestamp_columns();

        let address_contibution = match memory_access_columns.get_address() {
            ShuffleRamAddress::RegisterOnly(RegisterOnlyAccessAddress { register_index }) => {
                let address_low = *memory_trace_view_row.get_unchecked(register_index.start());
                let mut address_contibution = memory_argument_challenges
                    .memory_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                address_contibution.mul_assign_by_base(&address_low);

                // considered is register always
                // to we need to add literal 1, so we cancel multiplication by tau^H/2 below
                address_contibution.add_assign_base(tau_in_domain_by_half_inv);

                address_contibution
            }

            ShuffleRamAddress::RegisterOrRam(RegisterOrRamAccessAddress {
                is_register,
                address,
            }) => {
                debug_assert_eq!(address.width(), 2);

                let address_low = *memory_trace_view_row.get_unchecked(address.start());
                let mut address_contibution = memory_argument_challenges
                    .memory_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                address_contibution.mul_assign_by_base(&address_low);

                let address_high = *memory_trace_view_row.get_unchecked(address.start() + 1);
                let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                t.mul_assign_by_base(&address_high);
                address_contibution.add_assign(&t);

                debug_assert_eq!(is_register.width(), 1);
                let is_reg = *memory_trace_view_row.get_unchecked(is_register.start());
                address_contibution.add_assign_base(&is_reg);

                address_contibution
            }
        };

        debug_assert_eq!(read_value_columns.width(), 2);

        let read_value_low = *memory_trace_view_row.get_unchecked(read_value_columns.start());
        let mut read_value_contibution = memory_argument_challenges
            .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        read_value_contibution.mul_assign_by_base(&read_value_low);

        let read_value_high = *memory_trace_view_row.get_unchecked(read_value_columns.start() + 1);
        let mut t = memory_argument_challenges.memory_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        t.mul_assign_by_base(&read_value_high);
        read_value_contibution.add_assign(&t);

        debug_assert_eq!(read_timestamp_columns.width(), 2);

        let read_timestamp_low =
            *memory_trace_view_row.get_unchecked(read_timestamp_columns.start());
        let mut read_timestamp_contibution = memory_argument_challenges
            .memory_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        read_timestamp_contibution.mul_assign_by_base(&read_timestamp_low);

        let read_timestamp_high =
            *memory_trace_view_row.get_unchecked(read_timestamp_columns.start() + 1);
        let mut t = memory_argument_challenges.memory_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        t.mul_assign_by_base(&read_timestamp_high);
        read_timestamp_contibution.add_assign(&t);

        // timestamp high is STATIC from the index of access, and setup value
        debug_assert_eq!(
            compiled_circuit
                .setup_layout
                .timestamp_setup_columns
                .width(),
            2
        );

        // NOTE on write timestamp: it has literal constants in contribution, so we add it AFTER
        // scaling by tau^H/2
        let mut write_timestamp_contibution = memory_argument_challenges
            .memory_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        write_timestamp_contibution.mul_assign_by_base(&write_timestamp_low);

        let mut t = memory_argument_challenges.memory_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        t.mul_assign_by_base(&write_timestamp_high);
        write_timestamp_contibution.add_assign(&t);

        let mut extra_write_timestamp_low = memory_argument_challenges
            .memory_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        extra_write_timestamp_low
            .mul_assign_by_base(&Mersenne31Field::from_u64_unchecked(access_idx as u64));

        let previous = memory_argument_src.read();
        let this = stage_2_trace_view_row
            .as_ptr()
            .add(
                compiled_circuit
                    .stage_2_layout
                    .intermediate_polys_for_memory_argument
                    .get_range(access_idx)
                    .start,
            )
            .cast::<Mersenne31Quartic>();
        assert!(this.is_aligned());
        *memory_argument_src = this;

        match memory_access_columns {
            ShuffleRamQueryColumns::Readonly(_) => {
                let mut numerator = address_contibution;
                numerator.add_assign(&read_value_contibution);

                let mut denom = numerator;

                // read and write set only differ in timestamp contribution
                numerator.add_assign(&write_timestamp_contibution);
                denom.add_assign(&read_timestamp_contibution);

                // scale all previous terms that are linear in witness
                numerator.mul_assign_by_base(tau_in_domain_by_half);
                denom.mul_assign_by_base(tau_in_domain_by_half);

                // add missing contribution from literal constants
                numerator.add_assign(&extra_write_timestamp_low);
                numerator.add_assign(extra_write_timestamp_high);

                numerator.add_assign(&memory_argument_challenges.memory_argument_gamma);
                denom.add_assign(&memory_argument_challenges.memory_argument_gamma);

                // this * demon - previous * numerator
                let accumulator = memory_argument_src.read();

                let mut term_contribution = accumulator;
                term_contribution.mul_assign(&denom);
                let mut t = previous;
                t.mul_assign(&numerator);
                term_contribution.sub_assign(&t);
                // only accumulators are not restored, but we are linear over them
                // or just this * denom - numerator
                term_contribution.mul_assign_by_base(tau_in_domain_by_half);

                if DEBUG_QUOTIENT {
                    if is_last_row == false {
                        assert_eq!(
                            term_contribution,
                            Mersenne31Quartic::ZERO,
                            "unsatisfied at shuffle RAM memory accumulation for access idx {} at readonly access at row {}",
                            access_idx,
                            absolute_row_idx,
                        );
                    }
                }
                add_quotient_term_contribution_in_ext4(
                    other_challenges_ptr,
                    term_contribution,
                    quotient_term,
                );
            }
            ShuffleRamQueryColumns::Write(columns) => {
                debug_assert_eq!(columns.write_value.width(), 2);

                let write_value_low =
                    *memory_trace_view_row.get_unchecked(columns.write_value.start());
                let mut write_value_contibution = memory_argument_challenges
                    .memory_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                write_value_contibution.mul_assign_by_base(&write_value_low);

                let write_value_high =
                    *memory_trace_view_row.get_unchecked(columns.write_value.start() + 1);
                let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                t.mul_assign_by_base(&write_value_high);
                write_value_contibution.add_assign(&t);

                let mut numerator = address_contibution;
                let mut denom = numerator;

                // read and write set differ in timestamp and value
                numerator.add_assign(&write_value_contibution);
                denom.add_assign(&read_value_contibution);

                numerator.add_assign(&write_timestamp_contibution);
                denom.add_assign(&read_timestamp_contibution);

                // scale all previous terms that are linear in witness
                numerator.mul_assign_by_base(tau_in_domain_by_half);
                denom.mul_assign_by_base(tau_in_domain_by_half);

                // add missing contribution from literal constants
                numerator.add_assign(&extra_write_timestamp_low);
                numerator.add_assign(extra_write_timestamp_high);

                numerator.add_assign(&memory_argument_challenges.memory_argument_gamma);
                denom.add_assign(&memory_argument_challenges.memory_argument_gamma);

                // this * demon - previous * numerator,
                let accumulator = memory_argument_src.read();

                let mut term_contribution = accumulator;
                term_contribution.mul_assign(&denom);
                let mut t = previous;
                t.mul_assign(&numerator);
                term_contribution.sub_assign(&t);
                // only accumulators are not restored, but we are linear over them
                term_contribution.mul_assign_by_base(tau_in_domain_by_half);

                if DEBUG_QUOTIENT {
                    if is_last_row == false {
                        assert_eq!(
                            term_contribution,
                            Mersenne31Quartic::ZERO,
                            "unsatisfied at shuffle RAM memory accumulation for access idx {} at write access at row {}",
                            access_idx,
                            absolute_row_idx
                        );
                    }
                }
                add_quotient_term_contribution_in_ext4(
                    other_challenges_ptr,
                    term_contribution,
                    quotient_term,
                );
            }
        }
    }
}

pub(crate) unsafe fn evaluate_machine_state_permutation_assuming_no_decoder(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    _witness_trace_view_row: &[Mersenne31Field],
    memory_trace_view_row: &[Mersenne31Field],
    _setup_trace_view_row: &[Mersenne31Field],
    stage_2_trace_view_row: &[Mersenne31Field],
    _tau_in_domain: &Mersenne31Complex,
    tau_in_domain_by_half: &Mersenne31Complex,
    absolute_row_idx: usize,
    is_last_row: bool,
    quotient_term: &mut Mersenne31Quartic,
    other_challenges_ptr: &mut *const Mersenne31Quartic,
    challenges: &ExternalMachineStateArgumentChallenges,
    permutation_argument_src: &mut *const Mersenne31Quartic,
) {
    // sequence of keys is pc_low || pc_high || timestamp low || timestamp_high

    // we assemble P(x) = write set / read set

    let initial_machine_state = compiled_circuit
        .memory_layout
        .intermediate_state_layout
        .unwrap();
    let final_machine_state = compiled_circuit.memory_layout.machine_state_layout.unwrap();

    let dst_column_sets = compiled_circuit
        .stage_2_layout
        .intermediate_polys_for_state_permutation;
    assert_eq!(dst_column_sets.num_elements(), 1);

    // first write - final state
    let c0 = *memory_trace_view_row.get_unchecked(final_machine_state.pc.start());
    let c1 = *memory_trace_view_row.get_unchecked(final_machine_state.pc.start() + 1);
    let c2 = *memory_trace_view_row.get_unchecked(final_machine_state.timestamp.start());
    let c3 = *memory_trace_view_row.get_unchecked(final_machine_state.timestamp.start() + 1);

    let numerator = quotient_compute_aggregated_key_value(
        c0,
        [c1, c2, c3],
        challenges.linearization_challenges,
        challenges.additive_term,
        *tau_in_domain_by_half,
    );

    // then read
    let c0 = *memory_trace_view_row.get_unchecked(initial_machine_state.pc.start());
    let c1 = *memory_trace_view_row.get_unchecked(initial_machine_state.pc.start() + 1);
    let c2 = *memory_trace_view_row.get_unchecked(initial_machine_state.timestamp.start());
    let c3 = *memory_trace_view_row.get_unchecked(initial_machine_state.timestamp.start() + 1);

    let denom = quotient_compute_aggregated_key_value(
        c0,
        [c1, c2, c3],
        challenges.linearization_challenges,
        challenges.additive_term,
        *tau_in_domain_by_half,
    );

    let previous = permutation_argument_src.read();
    let next_acc_ptr = stage_2_trace_view_row
        .as_ptr()
        .add(dst_column_sets.start())
        .cast::<Mersenne31Quartic>();
    debug_assert!(next_acc_ptr.is_aligned());
    let accumulator = next_acc_ptr.read();
    *permutation_argument_src = next_acc_ptr;

    // this * demon - previous * numerator,
    let mut term_contribution = accumulator;
    term_contribution.mul_assign(&denom);
    let mut t = previous;
    t.mul_assign(&numerator);
    term_contribution.sub_assign(&t);
    // only accumulators are not restored, but we are linear over them
    term_contribution.mul_assign_by_base(tau_in_domain_by_half);

    if DEBUG_QUOTIENT {
        if is_last_row == false {
            assert_eq!(
                term_contribution,
                Mersenne31Quartic::ZERO,
                "unsatisfied at state permutation in case of no decoder circuit at row {}",
                absolute_row_idx,
            );
        }
    }

    add_quotient_term_contribution_in_ext4(other_challenges_ptr, term_contribution, quotient_term);
}

pub(crate) unsafe fn evaluate_permutation_masking(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    _witness_trace_view_row: &[Mersenne31Field],
    memory_trace_view_row: &[Mersenne31Field],
    _setup_trace_view_row: &[Mersenne31Field],
    stage_2_trace_view_row: &[Mersenne31Field],
    _tau_in_domain: &Mersenne31Complex,
    tau_in_domain_by_half: &Mersenne31Complex,
    absolute_row_idx: usize,
    is_last_row: bool,
    quotient_term: &mut Mersenne31Quartic,
    other_challenges_ptr: &mut *const Mersenne31Quartic,
    permutation_argument_src: &mut *const Mersenne31Quartic,
) {
    // sequence of keys is pc_low || pc_high || timestamp low || timestamp_high

    // we assemble P(x) = write set / read set

    let initial_machine_state = compiled_circuit
        .memory_layout
        .intermediate_state_layout
        .unwrap();

    assert_eq!(
        compiled_circuit
            .stage_2_layout
            .intermediate_polys_for_permutation_masking
            .num_elements(),
        1
    );

    let execute = *memory_trace_view_row.get_unchecked(initial_machine_state.execute.start());

    let previous = permutation_argument_src.read();
    let next_acc_ptr = stage_2_trace_view_row
        .as_ptr()
        .add(
            compiled_circuit
                .stage_2_layout
                .intermediate_polys_for_permutation_masking
                .start(),
        )
        .cast::<Mersenne31Quartic>();
    debug_assert!(next_acc_ptr.is_aligned());
    let accumulator = next_acc_ptr.read();
    *permutation_argument_src = next_acc_ptr;

    let mut execute_ext = *tau_in_domain_by_half;
    execute_ext.mul_assign_by_base(&execute);

    // this = execute * previous + (1 - execute) * 1

    // this - execute * previous + execute - 1;
    let mut term_contribution = accumulator;
    let mut t = previous;
    t.mul_assign_by_base(&execute_ext);
    term_contribution.sub_assign(&t);
    term_contribution.add_assign_base(&execute);
    // restore before subtracting literal constant
    term_contribution.mul_assign_by_base(tau_in_domain_by_half);
    term_contribution.sub_assign_base(&Mersenne31Field::ONE);

    if DEBUG_QUOTIENT {
        if is_last_row == false {
            if term_contribution.is_zero() == false {
                dbg!(accumulator);
                dbg!(previous);
                dbg!(execute);
            }
            assert_eq!(
                term_contribution,
                Mersenne31Quartic::ZERO,
                "unsatisfied at permutation masking at row {}",
                absolute_row_idx
            );
        }
    }

    add_quotient_term_contribution_in_ext4(other_challenges_ptr, term_contribution, quotient_term);
}
