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
                let value = *(witness.get_unchecked(12usize));
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
                    let value = *(witness.get_unchecked(13usize));
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
                    let value = *(witness.get_unchecked(14usize));
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
                    let value = *(witness.get_unchecked(15usize));
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
                    let value = *(witness.get_unchecked(16usize));
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
                    let value = *(witness.get_unchecked(17usize));
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
                    let value = *(witness.get_unchecked(18usize));
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
                    let value = *(witness.get_unchecked(19usize));
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
                    let value = *(witness.get_unchecked(20usize));
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
                    let value = *(witness.get_unchecked(21usize));
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
                    let value = *(witness.get_unchecked(22usize));
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
                    let value = *(witness.get_unchecked(23usize));
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
                    let value = *(witness.get_unchecked(24usize));
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
                    let value = *(witness.get_unchecked(25usize));
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
                    let value = *(witness.get_unchecked(26usize));
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
                    let value = *(witness.get_unchecked(27usize));
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
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(17usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(17usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65536u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        let b = *(memory.get_unchecked(2usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        let b = *(memory.get_unchecked(3usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418111u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        let b = *(memory.get_unchecked(7usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        let b = *(memory.get_unchecked(8usize));
                        field_ops::mul_assign(&mut a, &b);
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
                        let mut a = *(witness.get_unchecked(17usize));
                        let b = *(witness.get_unchecked(20usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(17usize));
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
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(18usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(18usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65536u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        let b = *(memory.get_unchecked(2usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        let b = *(memory.get_unchecked(3usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418111u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        let b = *(memory.get_unchecked(7usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        let b = *(memory.get_unchecked(8usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65536u32));
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
                        let mut a = *(witness.get_unchecked(18usize));
                        let b = *(witness.get_unchecked(20usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(18usize));
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
                        let mut a = *(memory.get_unchecked(2usize));
                        let b = *(memory.get_unchecked(7usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(memory.get_unchecked(2usize));
                        let b = *(memory.get_unchecked(8usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65536u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(memory.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(7usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65536u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(memory.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(8usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(28usize));
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
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(19usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(19usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65536u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(19usize));
                        let b = *(witness.get_unchecked(28usize));
                        field_ops::mul_assign(&mut a, &b);
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
                        let mut a = *(witness.get_unchecked(19usize));
                        let b = *(witness.get_unchecked(20usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(19usize));
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
                        let mut a = *(witness.get_unchecked(0usize));
                        let b = *(witness.get_unchecked(8usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(8usize));
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
                        let b = *(witness.get_unchecked(9usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(9usize));
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
                        let mut a = *(witness.get_unchecked(21usize));
                        let b = *(memory.get_unchecked(18usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(21usize));
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
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(memory.get_unchecked(18usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(21usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
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
                        let mut a = *(witness.get_unchecked(21usize));
                        let b = *(memory.get_unchecked(18usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(21usize));
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
                        let mut a = *(witness.get_unchecked(21usize));
                        let b = *(witness.get_unchecked(22usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(memory.get_unchecked(19usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(22usize));
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
                        let mut a = *(witness.get_unchecked(21usize));
                        let b = *(witness.get_unchecked(30usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(30usize));
                        let b = *(memory.get_unchecked(19usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(22usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(30usize));
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
                        let mut a = *(witness.get_unchecked(21usize));
                        let b = *(witness.get_unchecked(22usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(memory.get_unchecked(19usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(21usize));
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
                        let mut a = *(witness.get_unchecked(1usize));
                        let b = *(witness.get_unchecked(13usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(1usize));
                        let b = *(witness.get_unchecked(15usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(1usize));
                        let b = *(witness.get_unchecked(16usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(12usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(13usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(14usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(15usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(16usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(17usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(18usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(19usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(10usize));
                        let b = *(witness.get_unchecked(17usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(10usize));
                        let b = *(witness.get_unchecked(18usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(10usize));
                        let b = *(witness.get_unchecked(19usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(memory.get_unchecked(2usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(memory.get_unchecked(7usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(13usize));
                        let b = *(memory.get_unchecked(2usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        let b = *(memory.get_unchecked(2usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        let b = *(memory.get_unchecked(7usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(16usize));
                        let b = *(memory.get_unchecked(18usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65535u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65535u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(19usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(65535u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(23usize));
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
                        let mut a = *(witness.get_unchecked(2usize));
                        let b = *(witness.get_unchecked(13usize));
                        field_ops::mul_assign(&mut a, &b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(2usize));
                        let b = *(witness.get_unchecked(15usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(2usize));
                        let b = *(witness.get_unchecked(16usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(12usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(13usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(14usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(15usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(16usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(17usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(18usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(19usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(17usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(18usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(19usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(memory.get_unchecked(3usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(memory.get_unchecked(8usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(13usize));
                        let b = *(memory.get_unchecked(3usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        let b = *(memory.get_unchecked(3usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        let b = *(memory.get_unchecked(8usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(16usize));
                        let b = *(memory.get_unchecked(19usize));
                        field_ops::mul_assign(&mut a, &b);
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(32767u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(32767u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(19usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(32767u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(20usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2147418111u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let a = *(witness.get_unchecked(23usize));
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
                        let mut a = *(witness.get_unchecked(4usize));
                        field_ops::negate(&mut a);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(12usize));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(13usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(2u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(4u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(15usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(8u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(16usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(16u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(32u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(64u32));
                        field_ops::add_assign(&mut individual_term, &a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(19usize));
                        field_ops::mul_assign_by_base(&mut a, &Mersenne31Field(128u32));
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
                        let mut a = *(witness.get_unchecked(27usize));
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
                        let mut a = *(witness.get_unchecked(27usize));
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
                let value = *(witness.get_unchecked(8usize));
                value
            };
            let b = {
                let value = *(witness.get_unchecked(9usize));
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
                        let acc_value = *(stage_2.get_unchecked(6usize));
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
                let value = *(witness.get_unchecked(10usize));
                value
            };
            let b = {
                let value = *(witness.get_unchecked(11usize));
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
                        let acc_value = *(stage_2.get_unchecked(7usize));
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
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(24usize));
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
                        let a = *(witness.get_unchecked(24usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    field_ops::add_assign_base(&mut individual_term, &Mersenne31Field(524288u32));
                    individual_term
                };
                individual_term
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
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(25usize));
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
                        let a = *(witness.get_unchecked(25usize));
                        field_ops::sub_assign(&mut individual_term, &a);
                    }
                    field_ops::add_assign_base(&mut individual_term, &Mersenne31Field(524288u32));
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
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(26usize));
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
                        let a = *(witness.get_unchecked(26usize));
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
                    field_ops::mul_assign(&mut individual_term, &*(stage_2.get_unchecked(12usize)));
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
                    let m = *(witness.get_unchecked(5usize));
                    let t = *(setup.get_unchecked(0usize));
                    let mut denom = lookup_argument_gamma;
                    field_ops::add_assign(&mut denom, &t);
                    let mut individual_term = denom;
                    field_ops::mul_assign(&mut individual_term, &*(stage_2.get_unchecked(13usize)));
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
                    field_ops::mul_assign(&mut individual_term, &*(stage_2.get_unchecked(14usize)));
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
                    field_ops::add_assign(&mut denom, &*(setup.get_unchecked(2usize)));
                    let mut t = decoder_lookup_argument_linearization_challenges[0usize];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(3usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[1usize];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(4usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[2usize];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(5usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[3usize];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(6usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[4usize];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(7usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[5usize];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(8usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[6usize];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(9usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[7usize];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(10usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut t = decoder_lookup_argument_linearization_challenges[8usize];
                    field_ops::mul_assign(&mut t, &*(setup.get_unchecked(11usize)));
                    field_ops::add_assign(&mut denom, &t);
                    let mut individual_term = denom;
                    field_ops::mul_assign(&mut individual_term, &*(stage_2.get_unchecked(15usize)));
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
                    let accumulator = *(stage_2.get_unchecked(16usize));
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
                    let accumulator = *(stage_2.get_unchecked(17usize));
                    let previous = *(stage_2.get_unchecked(16usize));
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
                    let accumulator = *(stage_2.get_unchecked(18usize));
                    let previous = *(stage_2.get_unchecked(17usize));
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
                    let mut individual_term = *(stage_2.get_unchecked(19usize));
                    field_ops::mul_assign(&mut individual_term, &denom);
                    let mut t = *(stage_2.get_unchecked(18usize));
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
                    let mut individual_term = *(stage_2.get_unchecked(20usize));
                    let predicate = *(memory.get_unchecked(17usize));
                    let mut t = *(stage_2.get_unchecked(19usize));
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
                    let mut individual_term = *(stage_2_next_row.get_unchecked(21usize));
                    let mut t = *(stage_2.get_unchecked(21usize));
                    field_ops::mul_assign(&mut t, &*(stage_2.get_unchecked(20usize)));
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
                let mut individual_term = *(stage_2.get_unchecked(13usize));
                let t = *(stage_2.get_unchecked(6usize));
                field_ops::sub_assign(&mut individual_term, &t);
                let t = *(stage_2.get_unchecked(7usize));
                field_ops::sub_assign(&mut individual_term, &t);
                individual_term
            };
            individual_term
        };
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = *(stage_2.get_unchecked(14usize));
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
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = *(stage_2.get_unchecked(15usize));
                    field_ops::sub_assign(&mut individual_term, &*(stage_2.get_unchecked(12usize)));
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
                let mut individual_term = *(stage_2.get_unchecked(21usize));
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
                let mut individual_term = *(stage_2.get_unchecked(21usize));
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
