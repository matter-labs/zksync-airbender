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
    // We require that on unused rows in delegation circuits prover
    // can only substitute 0s for:
    // - delegation data itself - so write timestamp is 0
    // - all memory reads values/read timestamps - so that they do not contribute to RAM permutaiton (cancel immediatelly with writes)
    // - all memory writes created by circuits are masked/default 0s - same, so that they do not contribute to RAM permutaiton (cancel immediatelly with reads)
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

    assert!(
        compiled_circuit
            .memory_layout
            .batched_ram_accesses
            .is_empty(),
        "deprecated"
    );

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
                                assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value low is 0 if predicate is 0 at row {} for access to register {} indirect access with offset {}", absolute_row_idx, access.register_access.get_register_index(), indirect_access.offset_constant());
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
                                assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value high is 0 if predicate is 0 at row {} for access to register {} indirect access with offset {}", absolute_row_idx, access.register_access.get_register_index(), indirect_access.offset_constant());
                            }
                        }
                        add_quotient_term_contribution_in_ext2(
                            other_challenges_ptr,
                            term_contribution,
                            quotient_term,
                        );
                    }

                    // We only derive with non-trivial addition if it's not-first access
                    if address_derivation_carry_bit.num_elements() > 0 {
                        let carry_bit = *memory_trace_view_row
                            .get_unchecked(address_derivation_carry_bit.start());
                        let mut term_contribution = *tau_in_domain_by_half;
                        term_contribution.mul_assign_by_base(&carry_bit);
                        term_contribution.sub_assign_base(&Mersenne31Field::ONE);
                        term_contribution.mul_assign_by_base(&carry_bit);
                        term_contribution.mul_assign(&tau_in_domain_by_half);
                        if DEBUG_QUOTIENT {
                            if is_last_row == false {
                                assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: carry bit is not boolean at row {} for access to register {} indirect access with offset {}", absolute_row_idx, access.register_access.get_register_index(), indirect_access.offset_constant());
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
                                assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value/write value low is 0 if predicate is 0 at row {} for access to register {} indirect access with offset {}", absolute_row_idx, access.register_access.get_register_index(), indirect_access.offset_constant());
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
                                assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: read timestamp/read value/write value high is 0 if predicate is 0 at row {} for access to register {} indirect access with offset {}", absolute_row_idx, access.register_access.get_register_index(), indirect_access.offset_constant());
                            }
                        }
                        add_quotient_term_contribution_in_ext2(
                            other_challenges_ptr,
                            term_contribution,
                            quotient_term,
                        );
                    }

                    // We only derive with non-trivial addition if it's not-first access
                    if address_derivation_carry_bit.num_elements() > 0 {
                        let carry_bit = *memory_trace_view_row
                            .get_unchecked(address_derivation_carry_bit.start());
                        let mut term_contribution = *tau_in_domain_by_half;
                        term_contribution.mul_assign_by_base(&carry_bit);
                        term_contribution.sub_assign_base(&Mersenne31Field::ONE);
                        term_contribution.mul_assign_by_base(&carry_bit);
                        term_contribution.mul_assign(&tau_in_domain_by_half);
                        if DEBUG_QUOTIENT {
                            if is_last_row == false {
                                assert_eq!(term_contribution, Mersenne31Complex::ZERO, "unsatisfied for delegation convention: carry bit is not boolean at row {} for access to register {} indirect access with offset {}", absolute_row_idx, access.register_access.get_register_index(), indirect_access.offset_constant());
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
    _memory_trace_view_row: &[Mersenne31Field],
    _setup_trace_view_row: &[Mersenne31Field],
    stage_2_trace_view_row: &[Mersenne31Field],
    _tau_in_domain: &Mersenne31Complex,
    tau_in_domain_by_half: &Mersenne31Complex,
    absolute_row_idx: usize,
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
        let a = *witness_trace_view_row.get_unchecked(a);
        let b = *witness_trace_view_row.get_unchecked(b);

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
                if term_contribution.is_zero() == false {
                    dbg!(lookup_set);
                    dbg!(a);
                    dbg!(b);
                    dbg!(c);
                }
                assert_eq!(
                    term_contribution,
                    Mersenne31Complex::ZERO,
                    "unsatisfied at range check 16 lookup base field oracle {} at row {}",
                    i,
                    absolute_row_idx,
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
                    "unsatisfied at range check 16 lookup ext field oracle {} at row {}",
                    i,
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
                    "unsatisfied at range check 16 lookup base field oracle {}",
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
                    "unsatisfied at range check 16 lookup ext field oracle {}",
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

pub(crate) unsafe fn evaluate_delegation_requests(
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
    delegation_request_layout: &DelegationRequestLayout,
    delegation_challenges: &ExternalDelegationArgumentChallenges,
    timestamp_low: Mersenne31Field,
    timestamp_high: Mersenne31Field,
    delegation_requests_timestamp_extra_contribution: &Mersenne31Quartic,
) {
    let acc = compiled_circuit
        .stage_2_layout
        .delegation_processing_aux_poly
        .unwrap()
        .start();
    let acc_ptr = stage_2_trace_view_row
        .as_ptr()
        .add(acc)
        .cast::<Mersenne31Quartic>();
    debug_assert!(acc_ptr.is_aligned());
    let acc_value = acc_ptr.read();

    let m = *memory_trace_view_row.get_unchecked(delegation_request_layout.multiplicity.start());

    // we will add contribution from literal offset afterwards
    let mut denom = quotient_compute_aggregated_key_value(
        *memory_trace_view_row.get_unchecked(delegation_request_layout.delegation_type.start()),
        [
            *memory_trace_view_row
                .get_unchecked(delegation_request_layout.abi_mem_offset_high.start()),
            timestamp_low,
            timestamp_high,
        ],
        delegation_challenges.delegation_argument_linearization_challenges,
        delegation_challenges.delegation_argument_gamma,
        *tau_in_domain_by_half,
    );
    denom.add_assign(delegation_requests_timestamp_extra_contribution);

    // extra power to scale accumulator and multiplicity
    let mut term_contribution = denom;
    term_contribution.mul_assign(&acc_value);
    term_contribution.sub_assign_base(&m);
    term_contribution.mul_assign_by_base(tau_in_domain_by_half);
    if DEBUG_QUOTIENT {
        if is_last_row == false {
            assert!(
                m == Mersenne31Field::ZERO || m == Mersenne31Field::ONE,
                "multiplicity must be 0 or 1, but got {}",
                m
            );
            assert_eq!(
                term_contribution,
                Mersenne31Quartic::ZERO,
                "unsatisfied at delegation argument aux column at row {}",
                absolute_row_idx,
            );
        }
    }
    add_quotient_term_contribution_in_ext4(other_challenges_ptr, term_contribution, quotient_term);
}

pub(crate) unsafe fn evaluate_memory_init_teardown_range_checks(
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
    lookup_argument_gamma: &Mersenne31Quartic,
    lookup_argument_two_gamma: &Mersenne31Quartic,
) {
    let lazy_init_address_range_check_16 = compiled_circuit
        .stage_2_layout
        .lazy_init_address_range_check_16
        .unwrap_unchecked();
    for i in 0..lazy_init_address_range_check_16.num_pairs {
        let shuffle_ram_inits_and_teardowns = compiled_circuit
            .memory_layout
            .shuffle_ram_inits_and_teardowns
            .get_unchecked(i);
        let c = lazy_init_address_range_check_16
            .base_field_oracles
            .get_range(i)
            .start;
        let c = *stage_2_trace_view_row.get_unchecked(c);
        let a = shuffle_ram_inits_and_teardowns
            .lazy_init_addresses_columns
            .start();
        let b = a + 1;
        let a = *memory_trace_view_row.get_unchecked(a);
        let b = *memory_trace_view_row.get_unchecked(b);

        if DEBUG_QUOTIENT {
            if is_last_row == false {
                assert!(
                    a.to_reduced_u32() < 1u32 << 16,
                    "unsatisfied at range check 16 for lazy init addresses: value is {}",
                    a,
                );

                assert!(
                    b.to_reduced_u32() < 1u32 << 16,
                    "unsatisfied at range check 16 for lazy init addresses: value is {}",
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
                    "unsatisfied at range check 16 lookup base field oracle for lazy init addresses at row {} set {}",
                    absolute_row_idx, i
                );
            }
        }
        add_quotient_term_contribution_in_ext2(
            other_challenges_ptr,
            term_contribution,
            quotient_term,
        );

        let acc = lazy_init_address_range_check_16
            .ext_4_field_oracles
            .get_range(i)
            .start;
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
                    "unsatisfied at range check 16 lookup ext field oracle for lazy init addresses at row {} set {}",
                    absolute_row_idx, i
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

pub(crate) unsafe fn evaluate_memory_init_teardown_padding(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    witness_trace_view_row: &[Mersenne31Field],
    memory_trace_view_row: &[Mersenne31Field],
    _setup_trace_view_row: &[Mersenne31Field],
    _stage_2_trace_view_row: &[Mersenne31Field],
    _tau_in_domain: &Mersenne31Complex,
    tau_in_domain_by_half: &Mersenne31Complex,
    absolute_row_idx: usize,
    is_last_row: bool,
    quotient_term: &mut Mersenne31Quartic,
    other_challenges_ptr: &mut *const Mersenne31Quartic,
) {
    // NOTE: very special trick here - this constraint makes sense on every row except last two, but it's quadratic,
    // and unless we actually make it on every row except last only(!) we can not get a quotient of degree 1. The good thing
    // is that a constraint about final borrow in the lazy init sorting is on every row except last two, so we can just place
    // an artificial borrow value for our needs

    for (lazy_init_address_aux_vars, shuffle_ram_inits_and_teardowns) in
        compiled_circuit.lazy_init_address_aux_vars.iter().zip(
            compiled_circuit
                .memory_layout
                .shuffle_ram_inits_and_teardowns
                .iter(),
        )
    {
        let ShuffleRamAuxComparisonSet { final_borrow, .. } = *lazy_init_address_aux_vars;

        // then if we do NOT have borrow-high, then we require that init address, teardown final value and timestamps are all zeroes

        let final_borrow_value =
            read_value(final_borrow, witness_trace_view_row, memory_trace_view_row);

        let lazy_init_address_start = shuffle_ram_inits_and_teardowns
            .lazy_init_addresses_columns
            .start();
        let lazy_init_address_low = lazy_init_address_start;
        let lazy_init_address_high = lazy_init_address_start + 1;

        let lazy_init_address_low = memory_trace_view_row[lazy_init_address_low];
        let lazy_init_address_high = memory_trace_view_row[lazy_init_address_high];

        let teardown_value_start = shuffle_ram_inits_and_teardowns
            .lazy_teardown_values_columns
            .start();
        let teardown_value_low = teardown_value_start;
        let teardown_value_high = teardown_value_start + 1;

        let teardown_value_low = memory_trace_view_row[teardown_value_low];
        let teardown_value_high = memory_trace_view_row[teardown_value_high];

        let teardown_timestamp_start = shuffle_ram_inits_and_teardowns
            .lazy_teardown_timestamps_columns
            .start();
        let teardown_timestamp_low = teardown_timestamp_start;
        let teardown_timestamp_high = teardown_timestamp_start + 1;

        let teardown_timestamp_low = memory_trace_view_row[teardown_timestamp_low];
        let teardown_timestamp_high = memory_trace_view_row[teardown_timestamp_high];

        // if borrow is 1 (strict comparison), then values can be any,
        // otherwise address, value and timestamp are 0
        let mut final_borrow_minus_one = *tau_in_domain_by_half;
        final_borrow_minus_one.mul_assign_by_base(&final_borrow_value);
        final_borrow_minus_one.sub_assign_base(&Mersenne31Field::ONE);

        // pre-multiply by another tau^H/2
        let mut final_borrow_minus_one_term = final_borrow_minus_one;
        final_borrow_minus_one_term.mul_assign(&tau_in_domain_by_half);

        for value in [
            lazy_init_address_low,
            lazy_init_address_high,
            teardown_value_low,
            teardown_value_high,
            teardown_timestamp_low,
            teardown_timestamp_high,
        ]
        .into_iter()
        {
            let mut term_contribution_ext2 = final_borrow_minus_one_term;
            term_contribution_ext2.mul_assign_by_base(&value);

            if DEBUG_QUOTIENT {
                if is_last_row == false {
                    assert_eq!(
                        term_contribution_ext2,
                        Mersenne31Complex::ZERO,
                        "unsatisfied at lazy init padding constraint at row {}",
                        absolute_row_idx
                    );
                    if final_borrow_value.is_zero() {
                        assert_eq!(
                            value,
                            Mersenne31Field::ZERO,
                            "unsatisfied at lazy init padding constraint at row {}",
                            absolute_row_idx
                        );
                    } else {
                        assert_eq!(final_borrow_value, Mersenne31Field::ONE);
                    }
                }
            }

            add_quotient_term_contribution_in_ext2(
                other_challenges_ptr,
                term_contribution_ext2,
                quotient_term,
            );
        }
    }
}

pub(crate) unsafe fn evaluate_memory_init_teardown_accumulation(
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
    permutation_argument_src: &mut *const Mersenne31Quartic,
) {
    for (access_idx, shuffle_ram_inits_and_teardowns) in compiled_circuit
        .memory_layout
        .shuffle_ram_inits_and_teardowns
        .iter()
        .enumerate()
    {
        let mut numerator = Mersenne31Quartic::ZERO;
        let address_low = *memory_trace_view_row.get_unchecked(
            shuffle_ram_inits_and_teardowns
                .lazy_init_addresses_columns
                .start(),
        );
        let mut t = memory_argument_challenges.memory_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        t.mul_assign_by_base(&address_low);
        numerator.add_assign(&t);

        let address_high = *memory_trace_view_row.get_unchecked(
            shuffle_ram_inits_and_teardowns
                .lazy_init_addresses_columns
                .start()
                + 1,
        );
        let mut t = memory_argument_challenges.memory_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
        t.mul_assign_by_base(&address_high);
        numerator.add_assign(&t);

        // lazy init and teardown sets have same addresses
        let mut denom = numerator;

        let value_low = *memory_trace_view_row.get_unchecked(
            shuffle_ram_inits_and_teardowns
                .lazy_teardown_values_columns
                .start(),
        );
        let mut t = memory_argument_challenges.memory_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        t.mul_assign_by_base(&value_low);
        denom.add_assign(&t);

        let value_high = *memory_trace_view_row.get_unchecked(
            shuffle_ram_inits_and_teardowns
                .lazy_teardown_values_columns
                .start()
                + 1,
        );
        let mut t = memory_argument_challenges.memory_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        t.mul_assign_by_base(&value_high);
        denom.add_assign(&t);

        let timestamp_low = *memory_trace_view_row.get_unchecked(
            shuffle_ram_inits_and_teardowns
                .lazy_teardown_timestamps_columns
                .start(),
        );
        let mut t = memory_argument_challenges.memory_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        t.mul_assign_by_base(&timestamp_low);
        denom.add_assign(&t);

        let timestamp_high = *memory_trace_view_row.get_unchecked(
            shuffle_ram_inits_and_teardowns
                .lazy_teardown_timestamps_columns
                .start()
                + 1,
        );
        let mut t = memory_argument_challenges.memory_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        t.mul_assign_by_base(&timestamp_high);
        denom.add_assign(&t);

        numerator.mul_assign_by_base(tau_in_domain_by_half);
        denom.mul_assign_by_base(tau_in_domain_by_half);

        numerator.add_assign(&memory_argument_challenges.memory_argument_gamma);
        denom.add_assign(&memory_argument_challenges.memory_argument_gamma);

        // this * demon - previous * numerator,
        let previous = permutation_argument_src.read();
        let next_acc_ptr = stage_2_trace_view_row
            .as_ptr()
            .add(
                compiled_circuit
                    .stage_2_layout
                    .intermediate_polys_for_memory_init_teardown
                    .get_range(access_idx)
                    .start,
            )
            .cast::<Mersenne31Quartic>();
        debug_assert!(next_acc_ptr.is_aligned());
        let accumulator = next_acc_ptr.read();
        *permutation_argument_src = next_acc_ptr;

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
                    "unsatisfied at memory accumulation for lazy init/teardown at row {}",
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
}

pub(crate) unsafe fn evaluate_register_and_indirect_memory_accesses(
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
    permutation_argument_src: &mut *const Mersenne31Quartic,
    delegation_write_timestamp_contribution: &Mersenne31Quartic,
    tau_in_domain_by_half_inv: &Mersenne31Complex,
) {
    const SHIFT_16: Mersenne31Field = Mersenne31Field(1u32 << 16);

    // we only process RAM permutation itself here, and extra constraints related to convention of
    // read timestamps/values and write timestamps/values is enforced above

    // commong contribution here will come from the fact that we access register, but it's a literal constant and will be added last

    let mut memory_columns_it = compiled_circuit
        .stage_2_layout
        .intermediate_polys_for_memory_argument
        .iter();

    for (access_idx, register_access_columns) in compiled_circuit
        .memory_layout
        .register_and_indirect_accesses
        .iter()
        .enumerate()
    {
        let read_value_columns = register_access_columns
            .register_access
            .get_read_value_columns();
        let read_timestamp_columns = register_access_columns
            .register_access
            .get_read_timestamp_columns();
        let register_index = register_access_columns.register_access.get_register_index();
        debug_assert!(register_index > 0);
        debug_assert!(register_index < 32);

        // address contribution is literal constant
        let mem_offset_low = Mersenne31Field(register_index);
        let mut address_contribution = memory_argument_challenges
            .memory_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        address_contribution.mul_assign_by_base(&mem_offset_low);
        // also a fact that it's a register. There is no challenge here
        address_contribution.add_assign_base(&Mersenne31Field::ONE);

        debug_assert_eq!(read_value_columns.width(), 2);

        let register_read_value_low =
            *memory_trace_view_row.get_unchecked(read_value_columns.start());
        let mut read_value_contribution = memory_argument_challenges
            .memory_argument_linearization_challenges[MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        read_value_contribution.mul_assign_by_base(&register_read_value_low);

        let register_read_value_high =
            *memory_trace_view_row.get_unchecked(read_value_columns.start() + 1);
        let mut t = memory_argument_challenges.memory_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        t.mul_assign_by_base(&register_read_value_high);
        read_value_contribution.add_assign(&t);

        debug_assert_eq!(read_timestamp_columns.width(), 2);

        let read_timestamp_low =
            *memory_trace_view_row.get_unchecked(read_timestamp_columns.start());
        let mut read_timestamp_contribution = memory_argument_challenges
            .memory_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        read_timestamp_contribution.mul_assign_by_base(&read_timestamp_low);

        let read_timestamp_high =
            *memory_trace_view_row.get_unchecked(read_timestamp_columns.start() + 1);
        let mut t = memory_argument_challenges.memory_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        t.mul_assign_by_base(&read_timestamp_high);
        read_timestamp_contribution.add_assign(&t);

        match register_access_columns.register_access {
            RegisterAccessColumns::ReadAccess { .. } => {
                let mut numerator = read_value_contribution;

                let mut denom = numerator;

                numerator.add_assign(&delegation_write_timestamp_contribution);
                denom.add_assign(&read_timestamp_contribution);

                numerator.mul_assign_by_base(tau_in_domain_by_half);
                numerator.add_assign(&memory_argument_challenges.memory_argument_gamma);
                // literal constant
                numerator.add_assign(&address_contribution);

                denom.mul_assign_by_base(tau_in_domain_by_half);
                denom.add_assign(&memory_argument_challenges.memory_argument_gamma);
                // literal constant
                denom.add_assign(&address_contribution);

                // this * demon - previous * numerator
                // or just this * denom - numerator
                let previous = permutation_argument_src.read();
                let next_acc_ptr = stage_2_trace_view_row
                    .as_ptr()
                    .add(memory_columns_it.next().unwrap().start)
                    .cast::<Mersenne31Quartic>();
                debug_assert!(next_acc_ptr.is_aligned());
                let accumulator = next_acc_ptr.read();
                *permutation_argument_src = next_acc_ptr;

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
                            "unsatisfied at register RAM memory accumulation for access idx {} at readonly access:\nprevious accumulated value = {}, numerator = {}, denominator = {}, new expected accumulator = {}. Previous * numerator = {}",
                            access_idx,
                            previous,
                            numerator,
                            denom,
                            accumulator,
                            t,
                        );
                    }
                }
                add_quotient_term_contribution_in_ext4(
                    other_challenges_ptr,
                    term_contribution,
                    quotient_term,
                );
            }
            RegisterAccessColumns::WriteAccess { write_value, .. } => {
                let write_value_low = *memory_trace_view_row.get_unchecked(write_value.start());
                let mut write_value_contribution = memory_argument_challenges
                    .memory_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                write_value_contribution.mul_assign_by_base(&write_value_low);

                let write_value_high =
                    *memory_trace_view_row.get_unchecked(write_value.start() + 1);
                let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                t.mul_assign_by_base(&write_value_high);
                write_value_contribution.add_assign(&t);

                let mut numerator = write_value_contribution;
                let mut denom = read_value_contribution;

                numerator.add_assign(&delegation_write_timestamp_contribution);
                denom.add_assign(&read_timestamp_contribution);

                numerator.mul_assign_by_base(tau_in_domain_by_half);
                numerator.add_assign(&memory_argument_challenges.memory_argument_gamma);
                // literal constant
                numerator.add_assign(&address_contribution);

                denom.mul_assign_by_base(tau_in_domain_by_half);
                denom.add_assign(&memory_argument_challenges.memory_argument_gamma);
                // literal constant
                denom.add_assign(&address_contribution);

                // this * demon - previous * numerator
                // or just this * denom - numerator
                let previous = permutation_argument_src.read();
                let next_acc_ptr = stage_2_trace_view_row
                    .as_ptr()
                    .add(memory_columns_it.next().unwrap().start)
                    .cast::<Mersenne31Quartic>();
                debug_assert!(next_acc_ptr.is_aligned());
                let accumulator = next_acc_ptr.read();
                *permutation_argument_src = next_acc_ptr;

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
                            "unsatisfied at register RAM memory accumulation for access idx {} at write access:\nprevious accumulated value = {}, numerator = {}, denominator = {}, new expected accumulator = {}. previous * numerator = {}",
                            access_idx,
                            previous,
                            numerator,
                            denom,
                            accumulator,
                            t,
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

        // and now if we have indirects - must process those
        for (indirect_access_idx, indirect_access_columns) in
            register_access_columns.indirect_accesses.iter().enumerate()
        {
            let read_value_columns = indirect_access_columns.get_read_value_columns();
            let read_timestamp_columns = indirect_access_columns.get_read_timestamp_columns();
            let carry_bit_column =
                indirect_access_columns.get_address_derivation_carry_bit_column();
            let offset_constant = indirect_access_columns.offset_constant();
            assert!(
                offset_constant < 1 << 16,
                "constant offset {} is too large and not supported",
                offset_constant
            );
            // address contribution is literal constant common, but a little convoluated

            // let will multiply offset by inverse of tau in domain by half to make our live simpler below
            let mut offset_adjusted = *tau_in_domain_by_half_inv;
            offset_adjusted.mul_assign_by_base(&Mersenne31Field(offset_constant));

            if let Some((c, v, _)) = indirect_access_columns.variable_dependent() {
                let mut t: Mersenne31Field = *memory_trace_view_row.get_unchecked(v.start());
                t.mul_assign(&Mersenne31Field(c));
                offset_adjusted.add_assign_base(&t);
            }

            let address_contribution = if carry_bit_column.num_elements() == 0 {
                let mem_offset_low = register_read_value_low;
                let mut mem_offset_low = Mersenne31Complex::from_base(mem_offset_low);
                mem_offset_low.add_assign_base(&offset_adjusted);

                let mut address_contribution = memory_argument_challenges
                    .memory_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                address_contribution.mul_assign_by_base(&mem_offset_low);

                let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                t.mul_assign_by_base(&register_read_value_high);
                address_contribution.add_assign(&t);

                address_contribution
            } else {
                assert!(indirect_access_columns.variable_dependent().is_none());

                // we compute an absolute address as read value + offset, so low part is register_low + offset - 2^16 * carry_bit
                let carry_bit = *memory_trace_view_row.get_unchecked(carry_bit_column.start());
                let mut carry_bit_shifted = SHIFT_16;
                carry_bit_shifted.mul_assign(&carry_bit);

                let mut mem_offset_low = register_read_value_low;
                mem_offset_low.sub_assign(&carry_bit_shifted);
                let mut mem_offset_low = Mersenne31Complex::from_base(mem_offset_low);
                mem_offset_low.add_assign(&offset_adjusted);

                let mut address_contribution = memory_argument_challenges
                    .memory_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                address_contribution.mul_assign_by_base(&mem_offset_low);

                let mut mem_offset_high = register_read_value_high;
                mem_offset_high.add_assign(&carry_bit);

                let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                t.mul_assign_by_base(&mem_offset_high);
                address_contribution.add_assign(&t);

                address_contribution
            };

            // we access RAM and not registers
            debug_assert_eq!(read_value_columns.width(), 2);

            let read_value_low = *memory_trace_view_row.get_unchecked(read_value_columns.start());
            let mut read_value_contribution = memory_argument_challenges
                .memory_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
            read_value_contribution.mul_assign_by_base(&read_value_low);

            let read_value_high =
                *memory_trace_view_row.get_unchecked(read_value_columns.start() + 1);
            let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
            t.mul_assign_by_base(&read_value_high);
            read_value_contribution.add_assign(&t);

            debug_assert_eq!(read_timestamp_columns.width(), 2);

            let read_timestamp_low =
                *memory_trace_view_row.get_unchecked(read_timestamp_columns.start());
            let mut read_timestamp_contribution = memory_argument_challenges
                .memory_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
            read_timestamp_contribution.mul_assign_by_base(&read_timestamp_low);

            let read_timestamp_high =
                *memory_trace_view_row.get_unchecked(read_timestamp_columns.start() + 1);
            let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
            t.mul_assign_by_base(&read_timestamp_high);
            read_timestamp_contribution.add_assign(&t);

            let mut numerator = address_contribution;

            match indirect_access_columns {
                IndirectAccessColumns::ReadAccess { .. } => {
                    numerator.add_assign(&read_value_contribution);

                    let mut denom = numerator;

                    numerator.add_assign(&delegation_write_timestamp_contribution);
                    denom.add_assign(&read_timestamp_contribution);

                    numerator.mul_assign_by_base(tau_in_domain_by_half);
                    numerator.add_assign(&memory_argument_challenges.memory_argument_gamma);

                    denom.mul_assign_by_base(tau_in_domain_by_half);
                    denom.add_assign(&memory_argument_challenges.memory_argument_gamma);

                    // this * demon - previous * numerator
                    let previous = permutation_argument_src.read();
                    let next_acc_ptr = stage_2_trace_view_row
                        .as_ptr()
                        .add(memory_columns_it.next().unwrap().start)
                        .cast::<Mersenne31Quartic>();
                    debug_assert!(next_acc_ptr.is_aligned());
                    let accumulator = next_acc_ptr.read();
                    *permutation_argument_src = next_acc_ptr;

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
                                "row {}: unsatisfied at indirect RAM memory accumulation for register access idx {} indirect access {} at readonly access:\nprevious accumulated value = {}, numerator = {}, denominator = {}, new expected accumulator = {}. Previous * numerator = {}",
                                absolute_row_idx,
                                access_idx,
                                indirect_access_idx,
                                previous,
                                numerator,
                                denom,
                                accumulator,
                                t,
                            );
                        }
                    }
                    add_quotient_term_contribution_in_ext4(
                        other_challenges_ptr,
                        term_contribution,
                        quotient_term,
                    );
                }
                IndirectAccessColumns::WriteAccess { write_value, .. } => {
                    let write_value_low = *memory_trace_view_row.get_unchecked(write_value.start());
                    let mut write_value_contribution = memory_argument_challenges
                        .memory_argument_linearization_challenges
                        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                    write_value_contribution.mul_assign_by_base(&write_value_low);

                    let write_value_high =
                        *memory_trace_view_row.get_unchecked(write_value.start() + 1);
                    let mut t = memory_argument_challenges.memory_argument_linearization_challenges
                        [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                    t.mul_assign_by_base(&write_value_high);
                    write_value_contribution.add_assign(&t);

                    let mut denom = numerator;

                    numerator.add_assign(&write_value_contribution);
                    denom.add_assign(&read_value_contribution);

                    numerator.add_assign(&delegation_write_timestamp_contribution);
                    denom.add_assign(&read_timestamp_contribution);

                    numerator.mul_assign_by_base(tau_in_domain_by_half);
                    numerator.add_assign(&memory_argument_challenges.memory_argument_gamma);

                    denom.mul_assign_by_base(tau_in_domain_by_half);
                    denom.add_assign(&memory_argument_challenges.memory_argument_gamma);

                    // this * demon - previous * numerator
                    let previous = permutation_argument_src.read();
                    let next_acc_ptr = stage_2_trace_view_row
                        .as_ptr()
                        .add(memory_columns_it.next().unwrap().start)
                        .cast::<Mersenne31Quartic>();
                    debug_assert!(next_acc_ptr.is_aligned());
                    let accumulator = next_acc_ptr.read();
                    *permutation_argument_src = next_acc_ptr;

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
                                "row {}: unsatisfied at indirect RAM memory accumulation for access idx {} indirect access {} at write access:\nprevious accumulated value = {}, numerator = {}, denominator = {}, new expected accumulator = {}. previous * numerator = {}",
                                absolute_row_idx,
                                access_idx,
                                indirect_access_idx,
                                previous,
                                numerator,
                                denom,
                                accumulator,
                                t,
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
}
