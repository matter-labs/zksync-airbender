use verifier_common::field_ops;
#[allow(unused_braces, unused_mut, unused_variables)]
unsafe fn evaluate_every_row_except_last(
    random_point: Mersenne31Quartic,
    witness: &[Mersenne31Quartic],
    memory: &[Mersenne31Quartic],
    setup: &[Mersenne31Quartic],
    stage_2: &[Mersenne31Quartic],
    witness_next_row: &[Mersenne31Quartic],
    memory_next_row: &[Mersenne31Quartic],
    stage_2_next_row: &[Mersenne31Quartic],
    quotient_alpha: Mersenne31Quartic,
    quotient_beta: Mersenne31Quartic,
    divisors: &[Mersenne31Quartic; 6usize],
    lookup_argument_linearization_challenges: &[Mersenne31Quartic;
         NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES],
    lookup_argument_gamma: Mersenne31Quartic,
    lookup_argument_two_gamma: Mersenne31Quartic,
    memory_argument_linearization_challenges: &[Mersenne31Quartic;
         NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES],
    memory_argument_gamma: Mersenne31Quartic,
    delegation_argument_linearization_challenges : & [Mersenne31Quartic ; NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES],
    delegation_argument_gamma: Mersenne31Quartic,
    decoder_lookup_argument_linearization_challenges : & [Mersenne31Quartic ; EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_LINEARIZATION_CHALLENGES],
    decoder_lookup_argument_gamma: Mersenne31Quartic,
    state_permutation_argument_linearization_challenges : & [Mersenne31Quartic ; NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES],
    state_permutation_argument_gamma: Mersenne31Quartic,
    public_inputs: &[Mersenne31Field; 0usize],
    aux_proof_values: &ProofAuxValues,
    aux_boundary_values: &[AuxArgumentsBoundaryValues; 0usize],
    memory_timestamp_high_from_sequence_idx: Mersenne31Field,
    delegation_type: Mersenne31Field,
    delegation_argument_interpolant_linear_coeff: Mersenne31Quartic,
) -> Mersenne31Quartic {
    let every_row_except_last_contribution = {
        let mut accumulated_contribution = {
            let individual_term = {
                let value = *(witness.get_unchecked(29usize));
                let mut t = value;
                field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                field_ops::mul_assign(&mut t, &value);
                t
            };
            individual_term
        };
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(30usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(31usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(32usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(33usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(34usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(35usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(36usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(37usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(38usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(39usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(40usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(41usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(42usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(43usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(44usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(45usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(46usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(47usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(48usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(49usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(50usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(51usize));
                    let mut t = value;
                    field_ops::sub_assign_base(&mut t, &Mersenne31Field::ONE);
                    field_ops::mul_assign(&mut t, &value);
                    t
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(memory.get_unchecked(17usize));
                        let b = *(memory.get_unchecked(17usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(17usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(33usize));
                        let b = *(witness.get_unchecked(34usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147483645u32));
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(33usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(34usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(52usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(54usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(24usize));
                        let b = *(witness.get_unchecked(54usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(53usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    field_ops::add_assign_base(
                        &mut individual_term,
                        &Mersenne31Field(2147483646u32),
                    );
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(53usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(24usize));
                        let b = *(witness.get_unchecked(53usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(52usize));
                        let b = *(witness.get_unchecked(53usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(52usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(55usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(25usize));
                        let b = *(witness.get_unchecked(57usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(26usize));
                        let b = *(witness.get_unchecked(57usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(56usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    field_ops::add_assign_base(
                        &mut individual_term,
                        &Mersenne31Field(2147483646u32),
                    );
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(25usize));
                        let b = *(witness.get_unchecked(56usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(26usize));
                        let b = *(witness.get_unchecked(56usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(33usize));
                        let b = *(witness.get_unchecked(56usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(33usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(58usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(29usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(memory.get_unchecked(2usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(9usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(10usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(256u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(2usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(24usize));
                        let b = *(witness.get_unchecked(29usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(memory.get_unchecked(3usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(11usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(256u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(3usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(33usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(55usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(33usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(59usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(25usize));
                        let b = *(witness.get_unchecked(29usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(60usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(26usize));
                        let b = *(witness.get_unchecked(29usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(61usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(58usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(62usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(29usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(memory.get_unchecked(2usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(23usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(63usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(24usize));
                        let b = *(witness.get_unchecked(29usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(memory.get_unchecked(3usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(24usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(64usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(25usize));
                        let b = *(witness.get_unchecked(29usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(33usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418112u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(25usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(65usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(26usize));
                        let b = *(witness.get_unchecked(29usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(33usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418112u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(26usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(66usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(13usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(14usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(256u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(10usize));
                        let b = *(witness.get_unchecked(13usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(256u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418111u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(35usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2130706431u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(60usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(63usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(15usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(16usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(256u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(10usize));
                        let b = *(witness.get_unchecked(14usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(10usize));
                        let b = *(witness.get_unchecked(15usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(256u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(13usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(14usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(256u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(13usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(256u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(17usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418111u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(35usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(256u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(36usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2130706431u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(37usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2113929215u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(61usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(64usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(34usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65535u32));
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(10usize));
                        let b = *(witness.get_unchecked(16usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(10usize));
                        let b = *(witness.get_unchecked(34usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65280u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(15usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(16usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(256u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(14usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(15usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(256u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(13usize));
                        let b = *(witness.get_unchecked(59usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65535u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        let b = *(witness.get_unchecked(59usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65280u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(18usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(19usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418111u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(36usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(256u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(37usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(512u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(38usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2130706431u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(39usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2113929215u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(40usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2080374783u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(62usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65535u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(65usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(34usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65535u32));
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(10usize));
                        let b = *(witness.get_unchecked(34usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65535u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(34usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65535u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(16usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(34usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65280u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(13usize));
                        let b = *(witness.get_unchecked(59usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65535u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        let b = *(witness.get_unchecked(59usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65535u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(15usize));
                        let b = *(witness.get_unchecked(59usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65535u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(16usize));
                        let b = *(witness.get_unchecked(59usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65280u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(19usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(20usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418111u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(38usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(256u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(39usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(512u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(40usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(1024u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(41usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2130706431u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(42usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2113929215u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(43usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2080374783u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(62usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65535u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(66usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(30usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(25usize));
                        let b = *(witness.get_unchecked(30usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(25usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(67usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(24usize));
                        let b = *(witness.get_unchecked(30usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(26usize));
                        let b = *(witness.get_unchecked(30usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(26usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(68usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(70usize));
                        let b = *(memory.get_unchecked(7usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(70usize));
                        let b = *(memory.get_unchecked(8usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(69usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    field_ops::add_assign_base(
                        &mut individual_term,
                        &Mersenne31Field(2147483646u32),
                    );
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(69usize));
                        let b = *(memory.get_unchecked(7usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(69usize));
                        let b = *(memory.get_unchecked(8usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(69usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(71usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(71usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(71usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418112u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(24usize));
                        let b = *(witness.get_unchecked(71usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(71usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418112u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(34usize));
                        let b = *(witness.get_unchecked(58usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147483645u32));
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(34usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(58usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(72usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(25usize));
                        let b = *(witness.get_unchecked(72usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2u32));
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(27usize));
                        let b = *(witness.get_unchecked(72usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147483645u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(25usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(27usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(44usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418111u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(7usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(26usize));
                        let b = *(witness.get_unchecked(72usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2u32));
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(28usize));
                        let b = *(witness.get_unchecked(72usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147483645u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(26usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(28usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(44usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(45usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418111u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(8usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(45usize));
                        let b = *(witness.get_unchecked(72usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147483645u32));
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(45usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(72usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(73usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(27usize));
                        let b = *(witness.get_unchecked(75usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(28usize));
                        let b = *(witness.get_unchecked(75usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(74usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    field_ops::add_assign_base(
                        &mut individual_term,
                        &Mersenne31Field(2147483646u32),
                    );
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(27usize));
                        let b = *(witness.get_unchecked(74usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(28usize));
                        let b = *(witness.get_unchecked(74usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(73usize));
                        let b = *(witness.get_unchecked(74usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(73usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(74usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(76usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    field_ops::add_assign_base(&mut individual_term, &Mersenne31Field(1u32));
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(58usize));
                        let b = *(witness.get_unchecked(73usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(58usize));
                        let b = *(witness.get_unchecked(76usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(73usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(77usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(77usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(71usize));
                        let b = *(witness.get_unchecked(77usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(29usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(71usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(0usize));
                        let b = *(witness.get_unchecked(67usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(67usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(15usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(0usize));
                        let b = *(witness.get_unchecked(68usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(68usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(16usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(46usize));
                        let b = *(memory.get_unchecked(18usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(46usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418115u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(78usize));
                        let b = *(memory.get_unchecked(18usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(46usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(78usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418115u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    field_ops::add_assign_base(
                        &mut individual_term,
                        &Mersenne31Field(2147483646u32),
                    );
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(46usize));
                        let b = *(memory.get_unchecked(18usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(46usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147483643u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(18usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(22usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    field_ops::add_assign_base(&mut individual_term, &Mersenne31Field(4u32));
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(46usize));
                        let b = *(witness.get_unchecked(47usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(47usize));
                        let b = *(memory.get_unchecked(19usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(47usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418111u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(46usize));
                        let b = *(witness.get_unchecked(79usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(79usize));
                        let b = *(memory.get_unchecked(19usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(47usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(79usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418111u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    field_ops::add_assign_base(
                        &mut individual_term,
                        &Mersenne31Field(2147483646u32),
                    );
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(46usize));
                        let b = *(witness.get_unchecked(47usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(47usize));
                        let b = *(memory.get_unchecked(19usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(46usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(19usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(23usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(4usize));
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(29usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(30usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(4u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(32usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(8u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(21usize));
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(32768u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(33usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418111u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(3usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(22usize));
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(32usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(32768u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(34usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418111u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(8usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let a = *(witness.get_unchecked(13usize));
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(256u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(7usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let a = *(witness.get_unchecked(15usize));
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(16usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(256u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(8usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(51usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(20usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(24usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    field_ops::add_assign_base(
                        &mut individual_term,
                        &Mersenne31Field(2147483643u32),
                    );
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(51usize));
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(21usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(25usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            let a = {
                let value = *(witness.get_unchecked(21usize));
                value
            };
            let b = {
                let value = *(witness.get_unchecked(22usize));
                value
            };
            let c = *(stage_2.get_unchecked(0usize));
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let mut individual_term = a;
                        field_ops::mul_assign(&mut individual_term, &b);
                        field_ops::sub_assign(&mut individual_term, &c);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let acc_value = *(stage_2.get_unchecked(8usize));
                        let mut denom = lookup_argument_gamma;
                        field_ops::add_assign(&mut denom, &a);
                        field_ops::add_assign(&mut denom, &b);
                        field_ops::mul_assign(&mut denom, &lookup_argument_gamma);
                        field_ops::add_assign(&mut denom, &c);
                        field_ops::mul_assign(&mut denom, &acc_value);
                        let mut numerator = lookup_argument_two_gamma;
                        field_ops::add_assign(&mut numerator, &a);
                        field_ops::add_assign(&mut numerator, &b);
                        let mut individual_term = denom;
                        field_ops::sub_assign(&mut individual_term, &numerator);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        {
            let a = {
                let value = *(witness.get_unchecked(23usize));
                value
            };
            let b = {
                let value = *(witness.get_unchecked(24usize));
                value
            };
            let c = *(stage_2.get_unchecked(1usize));
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let mut individual_term = a;
                        field_ops::mul_assign(&mut individual_term, &b);
                        field_ops::sub_assign(&mut individual_term, &c);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let acc_value = *(stage_2.get_unchecked(9usize));
                        let mut denom = lookup_argument_gamma;
                        field_ops::add_assign(&mut denom, &a);
                        field_ops::add_assign(&mut denom, &b);
                        field_ops::mul_assign(&mut denom, &lookup_argument_gamma);
                        field_ops::add_assign(&mut denom, &c);
                        field_ops::mul_assign(&mut denom, &acc_value);
                        let mut numerator = lookup_argument_two_gamma;
                        field_ops::add_assign(&mut numerator, &a);
                        field_ops::add_assign(&mut numerator, &b);
                        let mut individual_term = denom;
                        field_ops::sub_assign(&mut individual_term, &numerator);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        {
            let a = {
                let value = *(witness.get_unchecked(25usize));
                value
            };
            let b = {
                let value = *(witness.get_unchecked(26usize));
                value
            };
            let c = *(stage_2.get_unchecked(2usize));
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let mut individual_term = a;
                        field_ops::mul_assign(&mut individual_term, &b);
                        field_ops::sub_assign(&mut individual_term, &c);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let acc_value = *(stage_2.get_unchecked(10usize));
                        let mut denom = lookup_argument_gamma;
                        field_ops::add_assign(&mut denom, &a);
                        field_ops::add_assign(&mut denom, &b);
                        field_ops::mul_assign(&mut denom, &lookup_argument_gamma);
                        field_ops::add_assign(&mut denom, &c);
                        field_ops::mul_assign(&mut denom, &acc_value);
                        let mut numerator = lookup_argument_two_gamma;
                        field_ops::add_assign(&mut numerator, &a);
                        field_ops::add_assign(&mut numerator, &b);
                        let mut individual_term = denom;
                        field_ops::sub_assign(&mut individual_term, &numerator);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        {
            let a = {
                let value = *(witness.get_unchecked(27usize));
                value
            };
            let b = {
                let value = *(witness.get_unchecked(28usize));
                value
            };
            let c = *(stage_2.get_unchecked(3usize));
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let mut individual_term = a;
                        field_ops::mul_assign(&mut individual_term, &b);
                        field_ops::sub_assign(&mut individual_term, &c);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let acc_value = *(stage_2.get_unchecked(11usize));
                        let mut denom = lookup_argument_gamma;
                        field_ops::add_assign(&mut denom, &a);
                        field_ops::add_assign(&mut denom, &b);
                        field_ops::mul_assign(&mut denom, &lookup_argument_gamma);
                        field_ops::add_assign(&mut denom, &c);
                        field_ops::mul_assign(&mut denom, &acc_value);
                        let mut numerator = lookup_argument_two_gamma;
                        field_ops::add_assign(&mut numerator, &a);
                        field_ops::add_assign(&mut numerator, &b);
                        let mut individual_term = denom;
                        field_ops::sub_assign(&mut individual_term, &numerator);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        {
            let a = {
                let individual_term = {
                    let mut individual_term = {
                        let a = *(memory.get_unchecked(24usize));
                        a
                    };
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let a = *(memory.get_unchecked(25usize));
                        a
                    };
                    individual_term
                };
                individual_term
            };
            let c = *(stage_2.get_unchecked(4usize));
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let mut individual_term = a;
                        field_ops::mul_assign(&mut individual_term, &b);
                        field_ops::sub_assign(&mut individual_term, &c);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let acc_value = *(stage_2.get_unchecked(12usize));
                        let mut denom = lookup_argument_gamma;
                        field_ops::add_assign(&mut denom, &a);
                        field_ops::add_assign(&mut denom, &b);
                        field_ops::mul_assign(&mut denom, &lookup_argument_gamma);
                        field_ops::add_assign(&mut denom, &c);
                        field_ops::mul_assign(&mut denom, &acc_value);
                        let mut numerator = lookup_argument_two_gamma;
                        field_ops::add_assign(&mut numerator, &a);
                        field_ops::add_assign(&mut numerator, &b);
                        let mut individual_term = denom;
                        field_ops::sub_assign(&mut individual_term, &numerator);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        {
            let a = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(48usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(0usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(20usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let a = *(memory.get_unchecked(1usize));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(21usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(48usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    field_ops::add_assign_base(&mut individual_term, &Mersenne31Field(524288u32));
                    individual_term
                };
                individual_term
            };
            let c = *(stage_2.get_unchecked(5usize));
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let mut individual_term = a;
                        field_ops::mul_assign(&mut individual_term, &b);
                        field_ops::sub_assign(&mut individual_term, &c);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let acc_value = *(stage_2.get_unchecked(13usize));
                        let mut denom = lookup_argument_gamma;
                        field_ops::add_assign(&mut denom, &a);
                        field_ops::add_assign(&mut denom, &b);
                        field_ops::mul_assign(&mut denom, &lookup_argument_gamma);
                        field_ops::add_assign(&mut denom, &c);
                        field_ops::mul_assign(&mut denom, &acc_value);
                        let mut numerator = lookup_argument_two_gamma;
                        field_ops::add_assign(&mut numerator, &a);
                        field_ops::add_assign(&mut numerator, &b);
                        let mut individual_term = denom;
                        field_ops::sub_assign(&mut individual_term, &numerator);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        {
            let a = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(49usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(5usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(20usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    field_ops::add_assign_base(
                        &mut individual_term,
                        &Mersenne31Field(2147483646u32),
                    );
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let a = *(memory.get_unchecked(6usize));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(21usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(49usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    field_ops::add_assign_base(&mut individual_term, &Mersenne31Field(524288u32));
                    individual_term
                };
                individual_term
            };
            let c = *(stage_2.get_unchecked(6usize));
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let mut individual_term = a;
                        field_ops::mul_assign(&mut individual_term, &b);
                        field_ops::sub_assign(&mut individual_term, &c);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let acc_value = *(stage_2.get_unchecked(14usize));
                        let mut denom = lookup_argument_gamma;
                        field_ops::add_assign(&mut denom, &a);
                        field_ops::add_assign(&mut denom, &b);
                        field_ops::mul_assign(&mut denom, &lookup_argument_gamma);
                        field_ops::add_assign(&mut denom, &c);
                        field_ops::mul_assign(&mut denom, &acc_value);
                        let mut numerator = lookup_argument_two_gamma;
                        field_ops::add_assign(&mut numerator, &a);
                        field_ops::add_assign(&mut numerator, &b);
                        let mut individual_term = denom;
                        field_ops::sub_assign(&mut individual_term, &numerator);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        {
            let a = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(50usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(10usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(memory.get_unchecked(20usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    field_ops::add_assign_base(
                        &mut individual_term,
                        &Mersenne31Field(2147483645u32),
                    );
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let a = *(memory.get_unchecked(11usize));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(21usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(50usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    field_ops::add_assign_base(&mut individual_term, &Mersenne31Field(524288u32));
                    individual_term
                };
                individual_term
            };
            let c = *(stage_2.get_unchecked(7usize));
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let mut individual_term = a;
                        field_ops::mul_assign(&mut individual_term, &b);
                        field_ops::sub_assign(&mut individual_term, &c);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let acc_value = *(stage_2.get_unchecked(15usize));
                        let mut denom = lookup_argument_gamma;
                        field_ops::add_assign(&mut denom, &a);
                        field_ops::add_assign(&mut denom, &b);
                        field_ops::mul_assign(&mut denom, &lookup_argument_gamma);
                        field_ops::add_assign(&mut denom, &c);
                        field_ops::mul_assign(&mut denom, &acc_value);
                        let mut numerator = lookup_argument_two_gamma;
                        field_ops::add_assign(&mut numerator, &a);
                        field_ops::add_assign(&mut numerator, &b);
                        let mut individual_term = denom;
                        field_ops::sub_assign(&mut individual_term, &numerator);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let m = *(memory.get_unchecked(17usize));
                    let mut denom = decoder_lookup_argument_gamma;
                    field_ops::add_assign(&mut denom, &*(memory.get_unchecked(18usize)));
                    let mut t = decoder_lookup_argument_linearization_challenges[0usize];
                    field_ops::mul_assign(&mut t, &*(memory.get_unchecked(19usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[1usize];
                    field_ops::mul_assign(&mut t, &*(memory.get_unchecked(4usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[2usize];
                    field_ops::mul_assign(&mut t, &*(memory.get_unchecked(9usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[3usize];
                    field_ops::mul_assign(&mut t, &*(memory.get_unchecked(14usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[4usize];
                    field_ops::mul_assign(&mut t, &*(witness.get_unchecked(0usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[5usize];
                    field_ops::mul_assign(&mut t, &*(witness.get_unchecked(1usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[6usize];
                    field_ops::mul_assign(&mut t, &*(witness.get_unchecked(2usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[7usize];
                    field_ops::mul_assign(&mut t, &*(witness.get_unchecked(3usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[8usize];
                    field_ops::mul_assign(&mut t, &*(witness.get_unchecked(4usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut individual_term = denom;
                    field_ops::mul_assign(&mut individual_term, &*(stage_2.get_unchecked(22usize)));
                    field_ops::sub_assign(&mut individual_term, &m);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let src0 = {
                        let value = *(witness.get_unchecked(9usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(10usize));
                        value
                    };
                    let src2 = {
                        let individual_term = Mersenne31Field(0u32);
                        individual_term
                    };
                    let mut denom = lookup_argument_linearization_challenges[2];
                    let table_id = Mersenne31Field(8u32);
                    field_ops::mul_assign_by_base(&mut denom, &table_id);
                    let mut t = lookup_argument_linearization_challenges[1];
                    field_ops::mul_assign_by_base(&mut t, &src2);
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = lookup_argument_linearization_challenges[0];
                    field_ops::mul_assign_by_base(&mut t, &src1);
                    field_ops::add_assign(&mut denom, &t);
                    field_ops::add_assign(&mut denom, &src0);
                    field_ops::add_assign(&mut denom, &lookup_argument_gamma);
                    let mut individual_term = denom;
                    field_ops::mul_assign(&mut individual_term, &*(stage_2.get_unchecked(16usize)));
                    field_ops::sub_assign_base(&mut individual_term, &Mersenne31Field::ONE);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let src0 = {
                        let value = *(witness.get_unchecked(11usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(12usize));
                        value
                    };
                    let src2 = {
                        let individual_term = Mersenne31Field(0u32);
                        individual_term
                    };
                    let mut denom = lookup_argument_linearization_challenges[2];
                    let table_id = Mersenne31Field(8u32);
                    field_ops::mul_assign_by_base(&mut denom, &table_id);
                    let mut t = lookup_argument_linearization_challenges[1];
                    field_ops::mul_assign_by_base(&mut t, &src2);
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = lookup_argument_linearization_challenges[0];
                    field_ops::mul_assign_by_base(&mut t, &src1);
                    field_ops::add_assign(&mut denom, &t);
                    field_ops::add_assign(&mut denom, &src0);
                    field_ops::add_assign(&mut denom, &lookup_argument_gamma);
                    let mut individual_term = denom;
                    field_ops::mul_assign(&mut individual_term, &*(stage_2.get_unchecked(17usize)));
                    field_ops::sub_assign_base(&mut individual_term, &Mersenne31Field::ONE);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let src0 = {
                        let value = *(witness.get_unchecked(13usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(14usize));
                        value
                    };
                    let src2 = {
                        let individual_term = Mersenne31Field(0u32);
                        individual_term
                    };
                    let mut denom = lookup_argument_linearization_challenges[2];
                    let table_id = Mersenne31Field(8u32);
                    field_ops::mul_assign_by_base(&mut denom, &table_id);
                    let mut t = lookup_argument_linearization_challenges[1];
                    field_ops::mul_assign_by_base(&mut t, &src2);
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = lookup_argument_linearization_challenges[0];
                    field_ops::mul_assign_by_base(&mut t, &src1);
                    field_ops::add_assign(&mut denom, &t);
                    field_ops::add_assign(&mut denom, &src0);
                    field_ops::add_assign(&mut denom, &lookup_argument_gamma);
                    let mut individual_term = denom;
                    field_ops::mul_assign(&mut individual_term, &*(stage_2.get_unchecked(18usize)));
                    field_ops::sub_assign_base(&mut individual_term, &Mersenne31Field::ONE);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let src0 = {
                        let value = *(witness.get_unchecked(15usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(16usize));
                        value
                    };
                    let src2 = {
                        let individual_term = Mersenne31Field(0u32);
                        individual_term
                    };
                    let mut denom = lookup_argument_linearization_challenges[2];
                    let table_id = Mersenne31Field(8u32);
                    field_ops::mul_assign_by_base(&mut denom, &table_id);
                    let mut t = lookup_argument_linearization_challenges[1];
                    field_ops::mul_assign_by_base(&mut t, &src2);
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = lookup_argument_linearization_challenges[0];
                    field_ops::mul_assign_by_base(&mut t, &src1);
                    field_ops::add_assign(&mut denom, &t);
                    field_ops::add_assign(&mut denom, &src0);
                    field_ops::add_assign(&mut denom, &lookup_argument_gamma);
                    let mut individual_term = denom;
                    field_ops::mul_assign(&mut individual_term, &*(stage_2.get_unchecked(19usize)));
                    field_ops::sub_assign_base(&mut individual_term, &Mersenne31Field::ONE);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let src0 = {
                        let value = *(witness.get_unchecked(17usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(18usize));
                        value
                    };
                    let src2 = {
                        let individual_term = Mersenne31Field(0u32);
                        individual_term
                    };
                    let mut denom = lookup_argument_linearization_challenges[2];
                    let table_id = Mersenne31Field(8u32);
                    field_ops::mul_assign_by_base(&mut denom, &table_id);
                    let mut t = lookup_argument_linearization_challenges[1];
                    field_ops::mul_assign_by_base(&mut t, &src2);
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = lookup_argument_linearization_challenges[0];
                    field_ops::mul_assign_by_base(&mut t, &src1);
                    field_ops::add_assign(&mut denom, &t);
                    field_ops::add_assign(&mut denom, &src0);
                    field_ops::add_assign(&mut denom, &lookup_argument_gamma);
                    let mut individual_term = denom;
                    field_ops::mul_assign(&mut individual_term, &*(stage_2.get_unchecked(20usize)));
                    field_ops::sub_assign_base(&mut individual_term, &Mersenne31Field::ONE);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let src0 = {
                        let value = *(witness.get_unchecked(19usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(20usize));
                        value
                    };
                    let src2 = {
                        let individual_term = Mersenne31Field(0u32);
                        individual_term
                    };
                    let mut denom = lookup_argument_linearization_challenges[2];
                    let table_id = Mersenne31Field(8u32);
                    field_ops::mul_assign_by_base(&mut denom, &table_id);
                    let mut t = lookup_argument_linearization_challenges[1];
                    field_ops::mul_assign_by_base(&mut t, &src2);
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = lookup_argument_linearization_challenges[0];
                    field_ops::mul_assign_by_base(&mut t, &src1);
                    field_ops::add_assign(&mut denom, &t);
                    field_ops::add_assign(&mut denom, &src0);
                    field_ops::add_assign(&mut denom, &lookup_argument_gamma);
                    let mut individual_term = denom;
                    field_ops::mul_assign(&mut individual_term, &*(stage_2.get_unchecked(21usize)));
                    field_ops::sub_assign_base(&mut individual_term, &Mersenne31Field::ONE);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let m = *(witness.get_unchecked(5usize));
                    let t = *(setup.get_unchecked(0usize));
                    let mut denom = lookup_argument_gamma;
                    field_ops::add_assign(&mut denom, &t);
                    let mut individual_term = denom;
                    field_ops::mul_assign(&mut individual_term, &*(stage_2.get_unchecked(23usize)));
                    field_ops::sub_assign(&mut individual_term, &m);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let m = *(witness.get_unchecked(6usize));
                    let t = *(setup.get_unchecked(1usize));
                    let mut denom = lookup_argument_gamma;
                    field_ops::add_assign(&mut denom, &t);
                    let mut individual_term = denom;
                    field_ops::mul_assign(&mut individual_term, &*(stage_2.get_unchecked(24usize)));
                    field_ops::sub_assign(&mut individual_term, &m);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let m = *(witness.get_unchecked(7usize));
                    let mut denom = decoder_lookup_argument_gamma;
                    field_ops::add_assign(&mut denom, &*(setup.get_unchecked(6usize)));
                    let mut t = decoder_lookup_argument_linearization_challenges[0usize];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(7usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[1usize];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(8usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[2usize];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(9usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[3usize];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(10usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[4usize];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(11usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[5usize];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(12usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[6usize];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(13usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[7usize];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(14usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[8usize];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(15usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut individual_term = denom;
                    field_ops::mul_assign(&mut individual_term, &*(stage_2.get_unchecked(26usize)));
                    field_ops::sub_assign(&mut individual_term, &m);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let m = *(witness.get_unchecked(8usize));
                    let mut denom = lookup_argument_linearization_challenges[2];
                    let table_id = *(setup.get_unchecked(5usize));
                    field_ops::mul_assign(&mut denom, &table_id);
                    let mut t = lookup_argument_linearization_challenges[1];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(4usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = lookup_argument_linearization_challenges[0];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(3usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let t = *(setup.get_unchecked(2usize));
                    field_ops::add_assign(&mut denom, &t);
                    field_ops::add_assign(&mut denom, &lookup_argument_gamma);
                    let mut individual_term = denom;
                    field_ops::mul_assign(&mut individual_term, &*(stage_2.get_unchecked(25usize)));
                    field_ops::sub_assign(&mut individual_term, &m);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let address_contribution = {
                        let address_low = *(memory.get_unchecked(4usize));
                        let mut address_contribution =
                            memory_argument_linearization_challenges[0usize];
                        field_ops::mul_assign(&mut address_contribution, &address_low);
                        field_ops::add_assign_base(
                            &mut address_contribution,
                            &Mersenne31Field::ONE,
                        );
                        address_contribution
                    };
                    let value_low = *(memory.get_unchecked(2usize));
                    let mut value_contribution = memory_argument_linearization_challenges[4usize];
                    field_ops::mul_assign(&mut value_contribution, &value_low);
                    let value_high = *(memory.get_unchecked(3usize));
                    let mut t = memory_argument_linearization_challenges[5usize];
                    field_ops::mul_assign(&mut t, &value_high);
                    field_ops::add_assign(&mut value_contribution, &t);
                    let mut numerator = memory_argument_gamma;
                    field_ops::add_assign(&mut numerator, &address_contribution);
                    field_ops::add_assign(&mut numerator, &value_contribution);
                    let mut denom = numerator;
                    let read_timestamp_low = *(memory.get_unchecked(0usize));
                    let mut read_timestamp_contribution =
                        memory_argument_linearization_challenges[2usize];
                    field_ops::mul_assign(&mut read_timestamp_contribution, &read_timestamp_low);
                    let read_timestamp_high = *(memory.get_unchecked(1usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    field_ops::mul_assign(&mut t, &read_timestamp_high);
                    field_ops::add_assign(&mut read_timestamp_contribution, &t);
                    let mut write_timestamp_low = *(memory.get_unchecked(20usize));
                    field_ops::add_assign_base(&mut write_timestamp_low, &Mersenne31Field(0u32));
                    let mut write_timestamp_contribution =
                        memory_argument_linearization_challenges[2usize];
                    field_ops::mul_assign(&mut write_timestamp_contribution, &write_timestamp_low);
                    let mut write_timestamp_high = *(memory.get_unchecked(21usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    field_ops::mul_assign(&mut t, &write_timestamp_high);
                    field_ops::add_assign(&mut write_timestamp_contribution, &t);
                    field_ops::add_assign(&mut numerator, &write_timestamp_contribution);
                    field_ops::add_assign(&mut denom, &read_timestamp_contribution);
                    let accumulator = *(stage_2.get_unchecked(27usize));
                    let mut individual_term = accumulator;
                    field_ops::mul_assign(&mut individual_term, &denom);
                    field_ops::sub_assign(&mut individual_term, &numerator);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let address_contribution = {
                        let address_low = *(memory.get_unchecked(9usize));
                        let mut address_contribution =
                            memory_argument_linearization_challenges[0usize];
                        field_ops::mul_assign(&mut address_contribution, &address_low);
                        field_ops::add_assign_base(
                            &mut address_contribution,
                            &Mersenne31Field::ONE,
                        );
                        address_contribution
                    };
                    let value_low = *(memory.get_unchecked(7usize));
                    let mut value_contribution = memory_argument_linearization_challenges[4usize];
                    field_ops::mul_assign(&mut value_contribution, &value_low);
                    let value_high = *(memory.get_unchecked(8usize));
                    let mut t = memory_argument_linearization_challenges[5usize];
                    field_ops::mul_assign(&mut t, &value_high);
                    field_ops::add_assign(&mut value_contribution, &t);
                    let mut numerator = memory_argument_gamma;
                    field_ops::add_assign(&mut numerator, &address_contribution);
                    field_ops::add_assign(&mut numerator, &value_contribution);
                    let mut denom = numerator;
                    let read_timestamp_low = *(memory.get_unchecked(5usize));
                    let mut read_timestamp_contribution =
                        memory_argument_linearization_challenges[2usize];
                    field_ops::mul_assign(&mut read_timestamp_contribution, &read_timestamp_low);
                    let read_timestamp_high = *(memory.get_unchecked(6usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    field_ops::mul_assign(&mut t, &read_timestamp_high);
                    field_ops::add_assign(&mut read_timestamp_contribution, &t);
                    let mut write_timestamp_low = *(memory.get_unchecked(20usize));
                    field_ops::add_assign_base(&mut write_timestamp_low, &Mersenne31Field(1u32));
                    let mut write_timestamp_contribution =
                        memory_argument_linearization_challenges[2usize];
                    field_ops::mul_assign(&mut write_timestamp_contribution, &write_timestamp_low);
                    let mut write_timestamp_high = *(memory.get_unchecked(21usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    field_ops::mul_assign(&mut t, &write_timestamp_high);
                    field_ops::add_assign(&mut write_timestamp_contribution, &t);
                    field_ops::add_assign(&mut numerator, &write_timestamp_contribution);
                    field_ops::add_assign(&mut denom, &read_timestamp_contribution);
                    let accumulator = *(stage_2.get_unchecked(28usize));
                    let previous = *(stage_2.get_unchecked(27usize));
                    let mut individual_term = accumulator;
                    field_ops::mul_assign(&mut individual_term, &denom);
                    let mut t = previous;
                    field_ops::mul_assign(&mut t, &numerator);
                    field_ops::sub_assign(&mut individual_term, &t);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let address_contribution = {
                        let address_low = *(memory.get_unchecked(14usize));
                        let mut address_contribution =
                            memory_argument_linearization_challenges[0usize];
                        field_ops::mul_assign(&mut address_contribution, &address_low);
                        field_ops::add_assign_base(
                            &mut address_contribution,
                            &Mersenne31Field::ONE,
                        );
                        address_contribution
                    };
                    let mut numerator = memory_argument_gamma;
                    field_ops::add_assign(&mut numerator, &address_contribution);
                    let mut denom = numerator;
                    let read_value_low = *(memory.get_unchecked(12usize));
                    let mut read_value_contribution =
                        memory_argument_linearization_challenges[4usize];
                    field_ops::mul_assign(&mut read_value_contribution, &read_value_low);
                    let read_value_high = *(memory.get_unchecked(13usize));
                    let mut t = memory_argument_linearization_challenges[5usize];
                    field_ops::mul_assign(&mut t, &read_value_high);
                    field_ops::add_assign(&mut read_value_contribution, &t);
                    let write_value_low = *(memory.get_unchecked(15usize));
                    let mut write_value_contribution =
                        memory_argument_linearization_challenges[4usize];
                    field_ops::mul_assign(&mut write_value_contribution, &write_value_low);
                    let write_value_high = *(memory.get_unchecked(16usize));
                    let mut t = memory_argument_linearization_challenges[5usize];
                    field_ops::mul_assign(&mut t, &write_value_high);
                    field_ops::add_assign(&mut write_value_contribution, &t);
                    field_ops::add_assign(&mut numerator, &write_value_contribution);
                    field_ops::add_assign(&mut denom, &read_value_contribution);
                    let read_timestamp_low = *(memory.get_unchecked(10usize));
                    let mut read_timestamp_contribution =
                        memory_argument_linearization_challenges[2usize];
                    field_ops::mul_assign(&mut read_timestamp_contribution, &read_timestamp_low);
                    let read_timestamp_high = *(memory.get_unchecked(11usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    field_ops::mul_assign(&mut t, &read_timestamp_high);
                    field_ops::add_assign(&mut read_timestamp_contribution, &t);
                    let mut write_timestamp_low = *(memory.get_unchecked(20usize));
                    field_ops::add_assign_base(&mut write_timestamp_low, &Mersenne31Field(2u32));
                    let mut write_timestamp_contribution =
                        memory_argument_linearization_challenges[2usize];
                    field_ops::mul_assign(&mut write_timestamp_contribution, &write_timestamp_low);
                    let mut write_timestamp_high = *(memory.get_unchecked(21usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    field_ops::mul_assign(&mut t, &write_timestamp_high);
                    field_ops::add_assign(&mut write_timestamp_contribution, &t);
                    field_ops::add_assign(&mut numerator, &write_timestamp_contribution);
                    field_ops::add_assign(&mut denom, &read_timestamp_contribution);
                    let accumulator = *(stage_2.get_unchecked(29usize));
                    let previous = *(stage_2.get_unchecked(28usize));
                    let mut individual_term = accumulator;
                    field_ops::mul_assign(&mut individual_term, &denom);
                    let mut t = previous;
                    field_ops::mul_assign(&mut t, &numerator);
                    field_ops::sub_assign(&mut individual_term, &t);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut numerator = state_permutation_argument_gamma;
                    field_ops::add_assign(&mut numerator, &*(memory.get_unchecked(22usize)));
                    let mut t = state_permutation_argument_linearization_challenges[0];
                    field_ops::mul_assign(&mut t, &*(memory.get_unchecked(23usize)));
                    field_ops::add_assign(&mut numerator, &t);
                    let mut t = state_permutation_argument_linearization_challenges[1];
                    field_ops::mul_assign(&mut t, &*(memory.get_unchecked(24usize)));
                    field_ops::add_assign(&mut numerator, &t);
                    let mut t = state_permutation_argument_linearization_challenges[2];
                    field_ops::mul_assign(&mut t, &*(memory.get_unchecked(25usize)));
                    field_ops::add_assign(&mut numerator, &t);
                    let mut denom = state_permutation_argument_gamma;
                    field_ops::add_assign(&mut denom, &*(memory.get_unchecked(18usize)));
                    let mut t = state_permutation_argument_linearization_challenges[0];
                    field_ops::mul_assign(&mut t, &*(memory.get_unchecked(19usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = state_permutation_argument_linearization_challenges[1];
                    field_ops::mul_assign(&mut t, &*(memory.get_unchecked(20usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = state_permutation_argument_linearization_challenges[2];
                    field_ops::mul_assign(&mut t, &*(memory.get_unchecked(21usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut individual_term = *(stage_2.get_unchecked(30usize));
                    field_ops::mul_assign(&mut individual_term, &denom);
                    let mut t = *(stage_2.get_unchecked(29usize));
                    field_ops::mul_assign(&mut t, &numerator);
                    field_ops::sub_assign(&mut individual_term, &t);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = *(stage_2.get_unchecked(31usize));
                    let predicate = *(memory.get_unchecked(17usize));
                    let mut t = *(stage_2.get_unchecked(30usize));
                    field_ops::mul_assign(&mut t, &predicate);
                    field_ops::sub_assign(&mut individual_term, &t);
                    field_ops::add_assign(&mut individual_term, &predicate);
                    field_ops::sub_assign_base(&mut individual_term, &Mersenne31Field::ONE);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = *(stage_2_next_row.get_unchecked(32usize));
                    let mut t = *(stage_2.get_unchecked(32usize));
                    field_ops::mul_assign(&mut t, &*(stage_2.get_unchecked(31usize)));
                    field_ops::sub_assign(&mut individual_term, &t);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        let divisor = divisors[0usize];
        field_ops::mul_assign(&mut accumulated_contribution, &divisor);
        accumulated_contribution
    };
    every_row_except_last_contribution
}
#[allow(unused_braces, unused_mut, unused_variables)]
unsafe fn evaluate_every_row_except_two(
    random_point: Mersenne31Quartic,
    witness: &[Mersenne31Quartic],
    memory: &[Mersenne31Quartic],
    setup: &[Mersenne31Quartic],
    stage_2: &[Mersenne31Quartic],
    witness_next_row: &[Mersenne31Quartic],
    memory_next_row: &[Mersenne31Quartic],
    stage_2_next_row: &[Mersenne31Quartic],
    quotient_alpha: Mersenne31Quartic,
    quotient_beta: Mersenne31Quartic,
    divisors: &[Mersenne31Quartic; 6usize],
    lookup_argument_linearization_challenges: &[Mersenne31Quartic;
         NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES],
    lookup_argument_gamma: Mersenne31Quartic,
    lookup_argument_two_gamma: Mersenne31Quartic,
    memory_argument_linearization_challenges: &[Mersenne31Quartic;
         NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES],
    memory_argument_gamma: Mersenne31Quartic,
    delegation_argument_linearization_challenges : & [Mersenne31Quartic ; NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES],
    delegation_argument_gamma: Mersenne31Quartic,
    decoder_lookup_argument_linearization_challenges : & [Mersenne31Quartic ; EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_LINEARIZATION_CHALLENGES],
    decoder_lookup_argument_gamma: Mersenne31Quartic,
    state_permutation_argument_linearization_challenges : & [Mersenne31Quartic ; NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES],
    state_permutation_argument_gamma: Mersenne31Quartic,
    public_inputs: &[Mersenne31Field; 0usize],
    aux_proof_values: &ProofAuxValues,
    aux_boundary_values: &[AuxArgumentsBoundaryValues; 0usize],
    memory_timestamp_high_from_sequence_idx: Mersenne31Field,
    delegation_type: Mersenne31Field,
    delegation_argument_interpolant_linear_coeff: Mersenne31Quartic,
) -> Mersenne31Quartic {
    let every_row_except_two_last_contribution = Mersenne31Quartic::ZERO;
    every_row_except_two_last_contribution
}
#[allow(unused_braces, unused_mut, unused_variables)]
unsafe fn evaluate_last_row_and_zero(
    random_point: Mersenne31Quartic,
    witness: &[Mersenne31Quartic],
    memory: &[Mersenne31Quartic],
    setup: &[Mersenne31Quartic],
    stage_2: &[Mersenne31Quartic],
    witness_next_row: &[Mersenne31Quartic],
    memory_next_row: &[Mersenne31Quartic],
    stage_2_next_row: &[Mersenne31Quartic],
    quotient_alpha: Mersenne31Quartic,
    quotient_beta: Mersenne31Quartic,
    divisors: &[Mersenne31Quartic; 6usize],
    lookup_argument_linearization_challenges: &[Mersenne31Quartic;
         NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES],
    lookup_argument_gamma: Mersenne31Quartic,
    lookup_argument_two_gamma: Mersenne31Quartic,
    memory_argument_linearization_challenges: &[Mersenne31Quartic;
         NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES],
    memory_argument_gamma: Mersenne31Quartic,
    delegation_argument_linearization_challenges : & [Mersenne31Quartic ; NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES],
    delegation_argument_gamma: Mersenne31Quartic,
    decoder_lookup_argument_linearization_challenges : & [Mersenne31Quartic ; EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_LINEARIZATION_CHALLENGES],
    decoder_lookup_argument_gamma: Mersenne31Quartic,
    state_permutation_argument_linearization_challenges : & [Mersenne31Quartic ; NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES],
    state_permutation_argument_gamma: Mersenne31Quartic,
    public_inputs: &[Mersenne31Field; 0usize],
    aux_proof_values: &ProofAuxValues,
    aux_boundary_values: &[AuxArgumentsBoundaryValues; 0usize],
    memory_timestamp_high_from_sequence_idx: Mersenne31Field,
    delegation_type: Mersenne31Field,
    delegation_argument_interpolant_linear_coeff: Mersenne31Quartic,
) -> Mersenne31Quartic {
    let last_row_and_zero_contribution = {
        let mut accumulated_contribution = {
            let individual_term = {
                let mut individual_term = *(stage_2.get_unchecked(23usize));
                let t = *(stage_2.get_unchecked(8usize));
                field_ops::sub_assign(&mut individual_term, &t);
                let t = *(stage_2.get_unchecked(9usize));
                field_ops::sub_assign(&mut individual_term, &t);
                let t = *(stage_2.get_unchecked(10usize));
                field_ops::sub_assign(&mut individual_term, &t);
                let t = *(stage_2.get_unchecked(11usize));
                field_ops::sub_assign(&mut individual_term, &t);
                individual_term
            };
            individual_term
        };
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = *(stage_2.get_unchecked(24usize));
                    let t = *(stage_2.get_unchecked(12usize));
                    field_ops::sub_assign(&mut individual_term, &t);
                    let t = *(stage_2.get_unchecked(13usize));
                    field_ops::sub_assign(&mut individual_term, &t);
                    let t = *(stage_2.get_unchecked(14usize));
                    field_ops::sub_assign(&mut individual_term, &t);
                    let t = *(stage_2.get_unchecked(15usize));
                    field_ops::sub_assign(&mut individual_term, &t);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = *(stage_2.get_unchecked(26usize));
                    field_ops::sub_assign(&mut individual_term, &*(stage_2.get_unchecked(22usize)));
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = *(stage_2.get_unchecked(25usize));
                    let t = *(stage_2.get_unchecked(16usize));
                    field_ops::sub_assign(&mut individual_term, &t);
                    let t = *(stage_2.get_unchecked(17usize));
                    field_ops::sub_assign(&mut individual_term, &t);
                    let t = *(stage_2.get_unchecked(18usize));
                    field_ops::sub_assign(&mut individual_term, &t);
                    let t = *(stage_2.get_unchecked(19usize));
                    field_ops::sub_assign(&mut individual_term, &t);
                    let t = *(stage_2.get_unchecked(20usize));
                    field_ops::sub_assign(&mut individual_term, &t);
                    let t = *(stage_2.get_unchecked(21usize));
                    field_ops::sub_assign(&mut individual_term, &t);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        let divisor = divisors[5usize];
        field_ops::mul_assign(&mut accumulated_contribution, &divisor);
        accumulated_contribution
    };
    last_row_and_zero_contribution
}
#[allow(unused_braces, unused_mut, unused_variables)]
pub unsafe fn evaluate_quotient(
    random_point: Mersenne31Quartic,
    witness: &[Mersenne31Quartic],
    memory: &[Mersenne31Quartic],
    setup: &[Mersenne31Quartic],
    stage_2: &[Mersenne31Quartic],
    witness_next_row: &[Mersenne31Quartic],
    memory_next_row: &[Mersenne31Quartic],
    stage_2_next_row: &[Mersenne31Quartic],
    quotient_alpha: Mersenne31Quartic,
    quotient_beta: Mersenne31Quartic,
    divisors: &[Mersenne31Quartic; 6usize],
    lookup_argument_linearization_challenges: &[Mersenne31Quartic;
         NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES],
    lookup_argument_gamma: Mersenne31Quartic,
    lookup_argument_two_gamma: Mersenne31Quartic,
    memory_argument_linearization_challenges: &[Mersenne31Quartic;
         NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES],
    memory_argument_gamma: Mersenne31Quartic,
    delegation_argument_linearization_challenges : & [Mersenne31Quartic ; NUM_DELEGATION_ARGUMENT_LINEARIZATION_CHALLENGES],
    delegation_argument_gamma: Mersenne31Quartic,
    decoder_lookup_argument_linearization_challenges : & [Mersenne31Quartic ; EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_LINEARIZATION_CHALLENGES],
    decoder_lookup_argument_gamma: Mersenne31Quartic,
    state_permutation_argument_linearization_challenges : & [Mersenne31Quartic ; NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES],
    state_permutation_argument_gamma: Mersenne31Quartic,
    public_inputs: &[Mersenne31Field; 0usize],
    aux_proof_values: &ProofAuxValues,
    aux_boundary_values: &[AuxArgumentsBoundaryValues; 0usize],
    memory_timestamp_high_from_sequence_idx: Mersenne31Field,
    delegation_type: Mersenne31Field,
    delegation_argument_interpolant_linear_coeff: Mersenne31Quartic,
) -> Mersenne31Quartic {
    let every_row_except_last_contribution = evaluate_every_row_except_last(
        random_point,
        witness,
        memory,
        setup,
        stage_2,
        witness_next_row,
        memory_next_row,
        stage_2_next_row,
        quotient_alpha,
        quotient_beta,
        divisors,
        lookup_argument_linearization_challenges,
        lookup_argument_gamma,
        lookup_argument_two_gamma,
        memory_argument_linearization_challenges,
        memory_argument_gamma,
        delegation_argument_linearization_challenges,
        delegation_argument_gamma,
        decoder_lookup_argument_linearization_challenges,
        decoder_lookup_argument_gamma,
        state_permutation_argument_linearization_challenges,
        state_permutation_argument_gamma,
        public_inputs,
        aux_proof_values,
        aux_boundary_values,
        memory_timestamp_high_from_sequence_idx,
        delegation_type,
        delegation_argument_interpolant_linear_coeff,
    );
    let every_row_except_two_last_contribution = evaluate_every_row_except_two(
        random_point,
        witness,
        memory,
        setup,
        stage_2,
        witness_next_row,
        memory_next_row,
        stage_2_next_row,
        quotient_alpha,
        quotient_beta,
        divisors,
        lookup_argument_linearization_challenges,
        lookup_argument_gamma,
        lookup_argument_two_gamma,
        memory_argument_linearization_challenges,
        memory_argument_gamma,
        delegation_argument_linearization_challenges,
        delegation_argument_gamma,
        decoder_lookup_argument_linearization_challenges,
        decoder_lookup_argument_gamma,
        state_permutation_argument_linearization_challenges,
        state_permutation_argument_gamma,
        public_inputs,
        aux_proof_values,
        aux_boundary_values,
        memory_timestamp_high_from_sequence_idx,
        delegation_type,
        delegation_argument_interpolant_linear_coeff,
    );
    let last_row_and_zero_contribution = evaluate_last_row_and_zero(
        random_point,
        witness,
        memory,
        setup,
        stage_2,
        witness_next_row,
        memory_next_row,
        stage_2_next_row,
        quotient_alpha,
        quotient_beta,
        divisors,
        lookup_argument_linearization_challenges,
        lookup_argument_gamma,
        lookup_argument_two_gamma,
        memory_argument_linearization_challenges,
        memory_argument_gamma,
        delegation_argument_linearization_challenges,
        delegation_argument_gamma,
        decoder_lookup_argument_linearization_challenges,
        decoder_lookup_argument_gamma,
        state_permutation_argument_linearization_challenges,
        state_permutation_argument_gamma,
        public_inputs,
        aux_proof_values,
        aux_boundary_values,
        memory_timestamp_high_from_sequence_idx,
        delegation_type,
        delegation_argument_interpolant_linear_coeff,
    );
    let first_row_contribution = {
        let mut accumulated_contribution = {
            let individual_term = {
                let mut individual_term = *(stage_2.get_unchecked(32usize));
                field_ops::sub_assign_base(&mut individual_term, &Mersenne31Field::ONE);
                individual_term
            };
            individual_term
        };
        let divisor = divisors[2usize];
        field_ops::mul_assign(&mut accumulated_contribution, &divisor);
        accumulated_contribution
    };
    let one_before_last_row_contribution = Mersenne31Quartic::ZERO;
    let last_row_contribution = {
        let mut accumulated_contribution = {
            let individual_term = {
                let mut individual_term = *(stage_2.get_unchecked(32usize));
                let t = aux_proof_values.grand_product_accumulator_final_value;
                field_ops::sub_assign(&mut individual_term, &t);
                individual_term
            };
            individual_term
        };
        let divisor = divisors[4usize];
        field_ops::mul_assign(&mut accumulated_contribution, &divisor);
        accumulated_contribution
    };
    let mut quotient = every_row_except_last_contribution;
    field_ops::mul_assign(&mut quotient, &quotient_beta);
    field_ops::add_assign(&mut quotient, &every_row_except_two_last_contribution);
    field_ops::mul_assign(&mut quotient, &quotient_beta);
    field_ops::add_assign(&mut quotient, &first_row_contribution);
    field_ops::mul_assign(&mut quotient, &quotient_beta);
    field_ops::add_assign(&mut quotient, &one_before_last_row_contribution);
    field_ops::mul_assign(&mut quotient, &quotient_beta);
    field_ops::add_assign(&mut quotient, &last_row_contribution);
    field_ops::mul_assign(&mut quotient, &quotient_beta);
    field_ops::add_assign(&mut quotient, &last_row_and_zero_contribution);
    quotient
}
