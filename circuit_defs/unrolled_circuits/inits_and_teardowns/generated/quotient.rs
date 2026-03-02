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
    aux_boundary_values: &[AuxArgumentsBoundaryValues; 6usize],
    memory_timestamp_high_from_sequence_idx: Mersenne31Field,
    delegation_type: Mersenne31Field,
    delegation_argument_interpolant_linear_coeff: Mersenne31Quartic,
) -> Mersenne31Quartic {
    let every_row_except_last_contribution = {
        let mut accumulated_contribution = {
            let individual_term = {
                let value = *(witness.get_unchecked(13usize));
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
            let a = {
                let value = *(witness.get_unchecked(1usize));
                value
            };
            let b = {
                let value = *(witness.get_unchecked(2usize));
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
                let value = *(witness.get_unchecked(3usize));
                value
            };
            let b = {
                let value = *(witness.get_unchecked(4usize));
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
                let value = *(witness.get_unchecked(5usize));
                value
            };
            let b = {
                let value = *(witness.get_unchecked(6usize));
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
                let value = *(witness.get_unchecked(7usize));
                value
            };
            let b = {
                let value = *(witness.get_unchecked(8usize));
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
            let a = {
                let value = *(witness.get_unchecked(9usize));
                value
            };
            let b = {
                let value = *(witness.get_unchecked(10usize));
                value
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
                        let acc_value = *(stage_2.get_unchecked(16usize));
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
                let value = *(witness.get_unchecked(11usize));
                value
            };
            let b = {
                let value = *(witness.get_unchecked(12usize));
                value
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
                        let acc_value = *(stage_2.get_unchecked(17usize));
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
            let a = *(memory.get_unchecked(0usize));
            let b = *(memory.get_unchecked(1usize));
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
                        let acc_value = *(stage_2.get_unchecked(18usize));
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
            let a = *(memory.get_unchecked(6usize));
            let b = *(memory.get_unchecked(7usize));
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
                        let acc_value = *(stage_2.get_unchecked(19usize));
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
            let a = *(memory.get_unchecked(12usize));
            let b = *(memory.get_unchecked(13usize));
            let c = *(stage_2.get_unchecked(8usize));
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
                        let acc_value = *(stage_2.get_unchecked(20usize));
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
            let a = *(memory.get_unchecked(18usize));
            let b = *(memory.get_unchecked(19usize));
            let c = *(stage_2.get_unchecked(9usize));
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
                        let acc_value = *(stage_2.get_unchecked(21usize));
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
            let a = *(memory.get_unchecked(24usize));
            let b = *(memory.get_unchecked(25usize));
            let c = *(stage_2.get_unchecked(10usize));
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
                        let acc_value = *(stage_2.get_unchecked(22usize));
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
            let a = *(memory.get_unchecked(30usize));
            let b = *(memory.get_unchecked(31usize));
            let c = *(stage_2.get_unchecked(11usize));
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
                        let acc_value = *(stage_2.get_unchecked(23usize));
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
                    let m = *(witness.get_unchecked(0usize));
                    let t = *(setup.get_unchecked(0usize));
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
            let final_borrow_value = *(witness.get_unchecked(14usize));
            let mut final_borrow_minus_one = final_borrow_value;
            field_ops::sub_assign_base(&mut final_borrow_minus_one, &Mersenne31Field::ONE);
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let value_to_constraint = *(memory.get_unchecked(0usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(1usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(2usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(3usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(4usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(5usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        {
            let final_borrow_value = *(witness.get_unchecked(16usize));
            let mut final_borrow_minus_one = final_borrow_value;
            field_ops::sub_assign_base(&mut final_borrow_minus_one, &Mersenne31Field::ONE);
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let value_to_constraint = *(memory.get_unchecked(6usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(7usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(8usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(9usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(10usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(11usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        {
            let final_borrow_value = *(witness.get_unchecked(18usize));
            let mut final_borrow_minus_one = final_borrow_value;
            field_ops::sub_assign_base(&mut final_borrow_minus_one, &Mersenne31Field::ONE);
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let value_to_constraint = *(memory.get_unchecked(12usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(13usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(14usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(15usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(16usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(17usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        {
            let final_borrow_value = *(witness.get_unchecked(20usize));
            let mut final_borrow_minus_one = final_borrow_value;
            field_ops::sub_assign_base(&mut final_borrow_minus_one, &Mersenne31Field::ONE);
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let value_to_constraint = *(memory.get_unchecked(18usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(19usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(20usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(21usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(22usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(23usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        {
            let final_borrow_value = *(witness.get_unchecked(22usize));
            let mut final_borrow_minus_one = final_borrow_value;
            field_ops::sub_assign_base(&mut final_borrow_minus_one, &Mersenne31Field::ONE);
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let value_to_constraint = *(memory.get_unchecked(24usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(25usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(26usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(27usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(28usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(29usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        {
            let final_borrow_value = *(witness.get_unchecked(24usize));
            let mut final_borrow_minus_one = final_borrow_value;
            field_ops::sub_assign_base(&mut final_borrow_minus_one, &Mersenne31Field::ONE);
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let value_to_constraint = *(memory.get_unchecked(30usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(31usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(32usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(33usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(34usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                        let value_to_constraint = *(memory.get_unchecked(35usize));
                        let mut individual_term = final_borrow_minus_one;
                        field_ops::mul_assign(&mut individual_term, &value_to_constraint);
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
                    let address_low = *(memory.get_unchecked(0usize));
                    let mut t = memory_argument_linearization_challenges[0usize];
                    field_ops::mul_assign(&mut t, &address_low);
                    let mut numerator = t;
                    let address_high = *(memory.get_unchecked(1usize));
                    let mut t = memory_argument_linearization_challenges[1usize];
                    field_ops::mul_assign(&mut t, &address_high);
                    field_ops::add_assign(&mut numerator, &t);
                    field_ops::add_assign(&mut numerator, &memory_argument_gamma);
                    let mut denom = numerator;
                    let value_low = *(memory.get_unchecked(2usize));
                    let mut t = memory_argument_linearization_challenges[4usize];
                    field_ops::mul_assign(&mut t, &value_low);
                    field_ops::add_assign(&mut denom, &t);
                    let value_high = *(memory.get_unchecked(3usize));
                    let mut t = memory_argument_linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &value_high);
                    field_ops::add_assign(&mut denom, &t);
                    let timestamp_low = *(memory.get_unchecked(4usize));
                    let mut t = memory_argument_linearization_challenges[2usize];
                    field_ops::mul_assign(&mut t, &timestamp_low);
                    field_ops::add_assign(&mut denom, &t);
                    let timestamp_high = *(memory.get_unchecked(5usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    field_ops::mul_assign(&mut t, &timestamp_high);
                    field_ops::add_assign(&mut denom, &t);
                    let accumulator = *(stage_2.get_unchecked(25usize));
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
                    let address_low = *(memory.get_unchecked(6usize));
                    let mut t = memory_argument_linearization_challenges[0usize];
                    field_ops::mul_assign(&mut t, &address_low);
                    let mut numerator = t;
                    let address_high = *(memory.get_unchecked(7usize));
                    let mut t = memory_argument_linearization_challenges[1usize];
                    field_ops::mul_assign(&mut t, &address_high);
                    field_ops::add_assign(&mut numerator, &t);
                    field_ops::add_assign(&mut numerator, &memory_argument_gamma);
                    let mut denom = numerator;
                    let value_low = *(memory.get_unchecked(8usize));
                    let mut t = memory_argument_linearization_challenges[4usize];
                    field_ops::mul_assign(&mut t, &value_low);
                    field_ops::add_assign(&mut denom, &t);
                    let value_high = *(memory.get_unchecked(9usize));
                    let mut t = memory_argument_linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &value_high);
                    field_ops::add_assign(&mut denom, &t);
                    let timestamp_low = *(memory.get_unchecked(10usize));
                    let mut t = memory_argument_linearization_challenges[2usize];
                    field_ops::mul_assign(&mut t, &timestamp_low);
                    field_ops::add_assign(&mut denom, &t);
                    let timestamp_high = *(memory.get_unchecked(11usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    field_ops::mul_assign(&mut t, &timestamp_high);
                    field_ops::add_assign(&mut denom, &t);
                    let accumulator = *(stage_2.get_unchecked(26usize));
                    let previous = *(stage_2.get_unchecked(25usize));
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
                    let address_low = *(memory.get_unchecked(12usize));
                    let mut t = memory_argument_linearization_challenges[0usize];
                    field_ops::mul_assign(&mut t, &address_low);
                    let mut numerator = t;
                    let address_high = *(memory.get_unchecked(13usize));
                    let mut t = memory_argument_linearization_challenges[1usize];
                    field_ops::mul_assign(&mut t, &address_high);
                    field_ops::add_assign(&mut numerator, &t);
                    field_ops::add_assign(&mut numerator, &memory_argument_gamma);
                    let mut denom = numerator;
                    let value_low = *(memory.get_unchecked(14usize));
                    let mut t = memory_argument_linearization_challenges[4usize];
                    field_ops::mul_assign(&mut t, &value_low);
                    field_ops::add_assign(&mut denom, &t);
                    let value_high = *(memory.get_unchecked(15usize));
                    let mut t = memory_argument_linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &value_high);
                    field_ops::add_assign(&mut denom, &t);
                    let timestamp_low = *(memory.get_unchecked(16usize));
                    let mut t = memory_argument_linearization_challenges[2usize];
                    field_ops::mul_assign(&mut t, &timestamp_low);
                    field_ops::add_assign(&mut denom, &t);
                    let timestamp_high = *(memory.get_unchecked(17usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    field_ops::mul_assign(&mut t, &timestamp_high);
                    field_ops::add_assign(&mut denom, &t);
                    let accumulator = *(stage_2.get_unchecked(27usize));
                    let previous = *(stage_2.get_unchecked(26usize));
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
                    let address_low = *(memory.get_unchecked(18usize));
                    let mut t = memory_argument_linearization_challenges[0usize];
                    field_ops::mul_assign(&mut t, &address_low);
                    let mut numerator = t;
                    let address_high = *(memory.get_unchecked(19usize));
                    let mut t = memory_argument_linearization_challenges[1usize];
                    field_ops::mul_assign(&mut t, &address_high);
                    field_ops::add_assign(&mut numerator, &t);
                    field_ops::add_assign(&mut numerator, &memory_argument_gamma);
                    let mut denom = numerator;
                    let value_low = *(memory.get_unchecked(20usize));
                    let mut t = memory_argument_linearization_challenges[4usize];
                    field_ops::mul_assign(&mut t, &value_low);
                    field_ops::add_assign(&mut denom, &t);
                    let value_high = *(memory.get_unchecked(21usize));
                    let mut t = memory_argument_linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &value_high);
                    field_ops::add_assign(&mut denom, &t);
                    let timestamp_low = *(memory.get_unchecked(22usize));
                    let mut t = memory_argument_linearization_challenges[2usize];
                    field_ops::mul_assign(&mut t, &timestamp_low);
                    field_ops::add_assign(&mut denom, &t);
                    let timestamp_high = *(memory.get_unchecked(23usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    field_ops::mul_assign(&mut t, &timestamp_high);
                    field_ops::add_assign(&mut denom, &t);
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
                    let address_low = *(memory.get_unchecked(24usize));
                    let mut t = memory_argument_linearization_challenges[0usize];
                    field_ops::mul_assign(&mut t, &address_low);
                    let mut numerator = t;
                    let address_high = *(memory.get_unchecked(25usize));
                    let mut t = memory_argument_linearization_challenges[1usize];
                    field_ops::mul_assign(&mut t, &address_high);
                    field_ops::add_assign(&mut numerator, &t);
                    field_ops::add_assign(&mut numerator, &memory_argument_gamma);
                    let mut denom = numerator;
                    let value_low = *(memory.get_unchecked(26usize));
                    let mut t = memory_argument_linearization_challenges[4usize];
                    field_ops::mul_assign(&mut t, &value_low);
                    field_ops::add_assign(&mut denom, &t);
                    let value_high = *(memory.get_unchecked(27usize));
                    let mut t = memory_argument_linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &value_high);
                    field_ops::add_assign(&mut denom, &t);
                    let timestamp_low = *(memory.get_unchecked(28usize));
                    let mut t = memory_argument_linearization_challenges[2usize];
                    field_ops::mul_assign(&mut t, &timestamp_low);
                    field_ops::add_assign(&mut denom, &t);
                    let timestamp_high = *(memory.get_unchecked(29usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    field_ops::mul_assign(&mut t, &timestamp_high);
                    field_ops::add_assign(&mut denom, &t);
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
                    let address_low = *(memory.get_unchecked(30usize));
                    let mut t = memory_argument_linearization_challenges[0usize];
                    field_ops::mul_assign(&mut t, &address_low);
                    let mut numerator = t;
                    let address_high = *(memory.get_unchecked(31usize));
                    let mut t = memory_argument_linearization_challenges[1usize];
                    field_ops::mul_assign(&mut t, &address_high);
                    field_ops::add_assign(&mut numerator, &t);
                    field_ops::add_assign(&mut numerator, &memory_argument_gamma);
                    let mut denom = numerator;
                    let value_low = *(memory.get_unchecked(32usize));
                    let mut t = memory_argument_linearization_challenges[4usize];
                    field_ops::mul_assign(&mut t, &value_low);
                    field_ops::add_assign(&mut denom, &t);
                    let value_high = *(memory.get_unchecked(33usize));
                    let mut t = memory_argument_linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &value_high);
                    field_ops::add_assign(&mut denom, &t);
                    let timestamp_low = *(memory.get_unchecked(34usize));
                    let mut t = memory_argument_linearization_challenges[2usize];
                    field_ops::mul_assign(&mut t, &timestamp_low);
                    field_ops::add_assign(&mut denom, &t);
                    let timestamp_high = *(memory.get_unchecked(35usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    field_ops::mul_assign(&mut t, &timestamp_high);
                    field_ops::add_assign(&mut denom, &t);
                    let accumulator = *(stage_2.get_unchecked(30usize));
                    let previous = *(stage_2.get_unchecked(29usize));
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
                    let mut individual_term = *(stage_2_next_row.get_unchecked(31usize));
                    let mut t = *(stage_2.get_unchecked(31usize));
                    field_ops::mul_assign(&mut t, &*(stage_2.get_unchecked(30usize)));
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
    aux_boundary_values: &[AuxArgumentsBoundaryValues; 6usize],
    memory_timestamp_high_from_sequence_idx: Mersenne31Field,
    delegation_type: Mersenne31Field,
    delegation_argument_interpolant_linear_coeff: Mersenne31Quartic,
) -> Mersenne31Quartic {
    let every_row_except_two_last_contribution = {
        let mut accumulated_contribution = Mersenne31Quartic::ZERO;
        {
            let intermedaite_borrow_value = *(witness.get_unchecked(13usize));
            let final_borrow_value = *(witness.get_unchecked(14usize));
            let this_low = *(memory.get_unchecked(0usize));
            let this_high = *(memory.get_unchecked(1usize));
            let mut final_borrow_minus_one = final_borrow_value;
            field_ops::sub_assign_base(&mut final_borrow_minus_one, &Mersenne31Field::ONE);
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let next_low = *(memory_next_row.get_unchecked(0usize));
                        let aux_low = *(witness.get_unchecked(1usize));
                        let mut individual_term = intermedaite_borrow_value;
                        field_ops::mul_assign_by_base(
                            &mut individual_term,
                            &Mersenne31Field(1 << 16),
                        );
                        field_ops::add_assign(&mut individual_term, &this_low);
                        field_ops::sub_assign(&mut individual_term, &next_low);
                        field_ops::sub_assign(&mut individual_term, &aux_low);
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
                        let next_high = *(memory_next_row.get_unchecked(1usize));
                        let aux_high = *(witness.get_unchecked(2usize));
                        let mut individual_term = final_borrow_value;
                        field_ops::mul_assign_by_base(
                            &mut individual_term,
                            &Mersenne31Field(1 << 16),
                        );
                        field_ops::add_assign(&mut individual_term, &this_high);
                        field_ops::sub_assign(&mut individual_term, &intermedaite_borrow_value);
                        field_ops::sub_assign(&mut individual_term, &next_high);
                        field_ops::sub_assign(&mut individual_term, &aux_high);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        {
            let intermedaite_borrow_value = *(witness.get_unchecked(15usize));
            let final_borrow_value = *(witness.get_unchecked(16usize));
            let this_low = *(memory.get_unchecked(6usize));
            let this_high = *(memory.get_unchecked(7usize));
            let mut final_borrow_minus_one = final_borrow_value;
            field_ops::sub_assign_base(&mut final_borrow_minus_one, &Mersenne31Field::ONE);
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let next_low = *(memory_next_row.get_unchecked(6usize));
                        let aux_low = *(witness.get_unchecked(3usize));
                        let mut individual_term = intermedaite_borrow_value;
                        field_ops::mul_assign_by_base(
                            &mut individual_term,
                            &Mersenne31Field(1 << 16),
                        );
                        field_ops::add_assign(&mut individual_term, &this_low);
                        field_ops::sub_assign(&mut individual_term, &next_low);
                        field_ops::sub_assign(&mut individual_term, &aux_low);
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
                        let next_high = *(memory_next_row.get_unchecked(7usize));
                        let aux_high = *(witness.get_unchecked(4usize));
                        let mut individual_term = final_borrow_value;
                        field_ops::mul_assign_by_base(
                            &mut individual_term,
                            &Mersenne31Field(1 << 16),
                        );
                        field_ops::add_assign(&mut individual_term, &this_high);
                        field_ops::sub_assign(&mut individual_term, &intermedaite_borrow_value);
                        field_ops::sub_assign(&mut individual_term, &next_high);
                        field_ops::sub_assign(&mut individual_term, &aux_high);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        {
            let intermedaite_borrow_value = *(witness.get_unchecked(17usize));
            let final_borrow_value = *(witness.get_unchecked(18usize));
            let this_low = *(memory.get_unchecked(12usize));
            let this_high = *(memory.get_unchecked(13usize));
            let mut final_borrow_minus_one = final_borrow_value;
            field_ops::sub_assign_base(&mut final_borrow_minus_one, &Mersenne31Field::ONE);
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let next_low = *(memory_next_row.get_unchecked(12usize));
                        let aux_low = *(witness.get_unchecked(5usize));
                        let mut individual_term = intermedaite_borrow_value;
                        field_ops::mul_assign_by_base(
                            &mut individual_term,
                            &Mersenne31Field(1 << 16),
                        );
                        field_ops::add_assign(&mut individual_term, &this_low);
                        field_ops::sub_assign(&mut individual_term, &next_low);
                        field_ops::sub_assign(&mut individual_term, &aux_low);
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
                        let next_high = *(memory_next_row.get_unchecked(13usize));
                        let aux_high = *(witness.get_unchecked(6usize));
                        let mut individual_term = final_borrow_value;
                        field_ops::mul_assign_by_base(
                            &mut individual_term,
                            &Mersenne31Field(1 << 16),
                        );
                        field_ops::add_assign(&mut individual_term, &this_high);
                        field_ops::sub_assign(&mut individual_term, &intermedaite_borrow_value);
                        field_ops::sub_assign(&mut individual_term, &next_high);
                        field_ops::sub_assign(&mut individual_term, &aux_high);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        {
            let intermedaite_borrow_value = *(witness.get_unchecked(19usize));
            let final_borrow_value = *(witness.get_unchecked(20usize));
            let this_low = *(memory.get_unchecked(18usize));
            let this_high = *(memory.get_unchecked(19usize));
            let mut final_borrow_minus_one = final_borrow_value;
            field_ops::sub_assign_base(&mut final_borrow_minus_one, &Mersenne31Field::ONE);
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let next_low = *(memory_next_row.get_unchecked(18usize));
                        let aux_low = *(witness.get_unchecked(7usize));
                        let mut individual_term = intermedaite_borrow_value;
                        field_ops::mul_assign_by_base(
                            &mut individual_term,
                            &Mersenne31Field(1 << 16),
                        );
                        field_ops::add_assign(&mut individual_term, &this_low);
                        field_ops::sub_assign(&mut individual_term, &next_low);
                        field_ops::sub_assign(&mut individual_term, &aux_low);
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
                        let next_high = *(memory_next_row.get_unchecked(19usize));
                        let aux_high = *(witness.get_unchecked(8usize));
                        let mut individual_term = final_borrow_value;
                        field_ops::mul_assign_by_base(
                            &mut individual_term,
                            &Mersenne31Field(1 << 16),
                        );
                        field_ops::add_assign(&mut individual_term, &this_high);
                        field_ops::sub_assign(&mut individual_term, &intermedaite_borrow_value);
                        field_ops::sub_assign(&mut individual_term, &next_high);
                        field_ops::sub_assign(&mut individual_term, &aux_high);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        {
            let intermedaite_borrow_value = *(witness.get_unchecked(21usize));
            let final_borrow_value = *(witness.get_unchecked(22usize));
            let this_low = *(memory.get_unchecked(24usize));
            let this_high = *(memory.get_unchecked(25usize));
            let mut final_borrow_minus_one = final_borrow_value;
            field_ops::sub_assign_base(&mut final_borrow_minus_one, &Mersenne31Field::ONE);
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let next_low = *(memory_next_row.get_unchecked(24usize));
                        let aux_low = *(witness.get_unchecked(9usize));
                        let mut individual_term = intermedaite_borrow_value;
                        field_ops::mul_assign_by_base(
                            &mut individual_term,
                            &Mersenne31Field(1 << 16),
                        );
                        field_ops::add_assign(&mut individual_term, &this_low);
                        field_ops::sub_assign(&mut individual_term, &next_low);
                        field_ops::sub_assign(&mut individual_term, &aux_low);
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
                        let next_high = *(memory_next_row.get_unchecked(25usize));
                        let aux_high = *(witness.get_unchecked(10usize));
                        let mut individual_term = final_borrow_value;
                        field_ops::mul_assign_by_base(
                            &mut individual_term,
                            &Mersenne31Field(1 << 16),
                        );
                        field_ops::add_assign(&mut individual_term, &this_high);
                        field_ops::sub_assign(&mut individual_term, &intermedaite_borrow_value);
                        field_ops::sub_assign(&mut individual_term, &next_high);
                        field_ops::sub_assign(&mut individual_term, &aux_high);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        {
            let intermedaite_borrow_value = *(witness.get_unchecked(23usize));
            let final_borrow_value = *(witness.get_unchecked(24usize));
            let this_low = *(memory.get_unchecked(30usize));
            let this_high = *(memory.get_unchecked(31usize));
            let mut final_borrow_minus_one = final_borrow_value;
            field_ops::sub_assign_base(&mut final_borrow_minus_one, &Mersenne31Field::ONE);
            {
                field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let next_low = *(memory_next_row.get_unchecked(30usize));
                        let aux_low = *(witness.get_unchecked(11usize));
                        let mut individual_term = intermedaite_borrow_value;
                        field_ops::mul_assign_by_base(
                            &mut individual_term,
                            &Mersenne31Field(1 << 16),
                        );
                        field_ops::add_assign(&mut individual_term, &this_low);
                        field_ops::sub_assign(&mut individual_term, &next_low);
                        field_ops::sub_assign(&mut individual_term, &aux_low);
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
                        let next_high = *(memory_next_row.get_unchecked(31usize));
                        let aux_high = *(witness.get_unchecked(12usize));
                        let mut individual_term = final_borrow_value;
                        field_ops::mul_assign_by_base(
                            &mut individual_term,
                            &Mersenne31Field(1 << 16),
                        );
                        field_ops::add_assign(&mut individual_term, &this_high);
                        field_ops::sub_assign(&mut individual_term, &intermedaite_borrow_value);
                        field_ops::sub_assign(&mut individual_term, &next_high);
                        field_ops::sub_assign(&mut individual_term, &aux_high);
                        individual_term
                    };
                    individual_term
                };
                field_ops::add_assign(&mut accumulated_contribution, &contribution);
            }
        }
        let divisor = divisors[1usize];
        field_ops::mul_assign(&mut accumulated_contribution, &divisor);
        accumulated_contribution
    };
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
    aux_boundary_values: &[AuxArgumentsBoundaryValues; 6usize],
    memory_timestamp_high_from_sequence_idx: Mersenne31Field,
    delegation_type: Mersenne31Field,
    delegation_argument_interpolant_linear_coeff: Mersenne31Quartic,
) -> Mersenne31Quartic {
    let last_row_and_zero_contribution = {
        let mut accumulated_contribution = {
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
                let t = *(stage_2.get_unchecked(22usize));
                field_ops::sub_assign(&mut individual_term, &t);
                let t = *(stage_2.get_unchecked(23usize));
                field_ops::sub_assign(&mut individual_term, &t);
                individual_term
            };
            individual_term
        };
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
    aux_boundary_values: &[AuxArgumentsBoundaryValues; 6usize],
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
                let mut individual_term = *(memory.get_unchecked(0usize));
                let t = aux_boundary_values[0usize].lazy_init_first_row[0];
                field_ops::sub_assign_base(&mut individual_term, &t);
                individual_term
            };
            individual_term
        };
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = *(memory.get_unchecked(1usize));
                    let t = aux_boundary_values[0usize].lazy_init_first_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(2usize));
                    let t = aux_boundary_values[0usize].teardown_value_first_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(3usize));
                    let t = aux_boundary_values[0usize].teardown_value_first_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(4usize));
                    let t = aux_boundary_values[0usize].teardown_timestamp_first_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(5usize));
                    let t = aux_boundary_values[0usize].teardown_timestamp_first_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(6usize));
                    let t = aux_boundary_values[1usize].lazy_init_first_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(7usize));
                    let t = aux_boundary_values[1usize].lazy_init_first_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(8usize));
                    let t = aux_boundary_values[1usize].teardown_value_first_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(9usize));
                    let t = aux_boundary_values[1usize].teardown_value_first_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(10usize));
                    let t = aux_boundary_values[1usize].teardown_timestamp_first_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(11usize));
                    let t = aux_boundary_values[1usize].teardown_timestamp_first_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(12usize));
                    let t = aux_boundary_values[2usize].lazy_init_first_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(13usize));
                    let t = aux_boundary_values[2usize].lazy_init_first_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(14usize));
                    let t = aux_boundary_values[2usize].teardown_value_first_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(15usize));
                    let t = aux_boundary_values[2usize].teardown_value_first_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(16usize));
                    let t = aux_boundary_values[2usize].teardown_timestamp_first_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(17usize));
                    let t = aux_boundary_values[2usize].teardown_timestamp_first_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(18usize));
                    let t = aux_boundary_values[3usize].lazy_init_first_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(19usize));
                    let t = aux_boundary_values[3usize].lazy_init_first_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(20usize));
                    let t = aux_boundary_values[3usize].teardown_value_first_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(21usize));
                    let t = aux_boundary_values[3usize].teardown_value_first_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(22usize));
                    let t = aux_boundary_values[3usize].teardown_timestamp_first_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(23usize));
                    let t = aux_boundary_values[3usize].teardown_timestamp_first_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(24usize));
                    let t = aux_boundary_values[4usize].lazy_init_first_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(25usize));
                    let t = aux_boundary_values[4usize].lazy_init_first_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(26usize));
                    let t = aux_boundary_values[4usize].teardown_value_first_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(27usize));
                    let t = aux_boundary_values[4usize].teardown_value_first_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(28usize));
                    let t = aux_boundary_values[4usize].teardown_timestamp_first_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(29usize));
                    let t = aux_boundary_values[4usize].teardown_timestamp_first_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(30usize));
                    let t = aux_boundary_values[5usize].lazy_init_first_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(31usize));
                    let t = aux_boundary_values[5usize].lazy_init_first_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(32usize));
                    let t = aux_boundary_values[5usize].teardown_value_first_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(33usize));
                    let t = aux_boundary_values[5usize].teardown_value_first_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(34usize));
                    let t = aux_boundary_values[5usize].teardown_timestamp_first_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(35usize));
                    let t = aux_boundary_values[5usize].teardown_timestamp_first_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    field_ops::sub_assign_base(&mut individual_term, &Mersenne31Field::ONE);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        let divisor = divisors[2usize];
        field_ops::mul_assign(&mut accumulated_contribution, &divisor);
        accumulated_contribution
    };
    let one_before_last_row_contribution = {
        let mut accumulated_contribution = {
            let individual_term = {
                let mut individual_term = *(memory.get_unchecked(0usize));
                let t = aux_boundary_values[0usize].lazy_init_one_before_last_row[0];
                field_ops::sub_assign_base(&mut individual_term, &t);
                individual_term
            };
            individual_term
        };
        {
            field_ops::mul_assign(&mut accumulated_contribution, &quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = *(memory.get_unchecked(1usize));
                    let t = aux_boundary_values[0usize].lazy_init_one_before_last_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(2usize));
                    let t = aux_boundary_values[0usize].teardown_value_one_before_last_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(3usize));
                    let t = aux_boundary_values[0usize].teardown_value_one_before_last_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(4usize));
                    let t = aux_boundary_values[0usize].teardown_timestamp_one_before_last_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(5usize));
                    let t = aux_boundary_values[0usize].teardown_timestamp_one_before_last_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(6usize));
                    let t = aux_boundary_values[1usize].lazy_init_one_before_last_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(7usize));
                    let t = aux_boundary_values[1usize].lazy_init_one_before_last_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(8usize));
                    let t = aux_boundary_values[1usize].teardown_value_one_before_last_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(9usize));
                    let t = aux_boundary_values[1usize].teardown_value_one_before_last_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(10usize));
                    let t = aux_boundary_values[1usize].teardown_timestamp_one_before_last_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(11usize));
                    let t = aux_boundary_values[1usize].teardown_timestamp_one_before_last_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(12usize));
                    let t = aux_boundary_values[2usize].lazy_init_one_before_last_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(13usize));
                    let t = aux_boundary_values[2usize].lazy_init_one_before_last_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(14usize));
                    let t = aux_boundary_values[2usize].teardown_value_one_before_last_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(15usize));
                    let t = aux_boundary_values[2usize].teardown_value_one_before_last_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(16usize));
                    let t = aux_boundary_values[2usize].teardown_timestamp_one_before_last_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(17usize));
                    let t = aux_boundary_values[2usize].teardown_timestamp_one_before_last_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(18usize));
                    let t = aux_boundary_values[3usize].lazy_init_one_before_last_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(19usize));
                    let t = aux_boundary_values[3usize].lazy_init_one_before_last_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(20usize));
                    let t = aux_boundary_values[3usize].teardown_value_one_before_last_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(21usize));
                    let t = aux_boundary_values[3usize].teardown_value_one_before_last_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(22usize));
                    let t = aux_boundary_values[3usize].teardown_timestamp_one_before_last_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(23usize));
                    let t = aux_boundary_values[3usize].teardown_timestamp_one_before_last_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(24usize));
                    let t = aux_boundary_values[4usize].lazy_init_one_before_last_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(25usize));
                    let t = aux_boundary_values[4usize].lazy_init_one_before_last_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(26usize));
                    let t = aux_boundary_values[4usize].teardown_value_one_before_last_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(27usize));
                    let t = aux_boundary_values[4usize].teardown_value_one_before_last_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(28usize));
                    let t = aux_boundary_values[4usize].teardown_timestamp_one_before_last_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(29usize));
                    let t = aux_boundary_values[4usize].teardown_timestamp_one_before_last_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(30usize));
                    let t = aux_boundary_values[5usize].lazy_init_one_before_last_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(31usize));
                    let t = aux_boundary_values[5usize].lazy_init_one_before_last_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(32usize));
                    let t = aux_boundary_values[5usize].teardown_value_one_before_last_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(33usize));
                    let t = aux_boundary_values[5usize].teardown_value_one_before_last_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(34usize));
                    let t = aux_boundary_values[5usize].teardown_timestamp_one_before_last_row[0];
                    field_ops::sub_assign_base(&mut individual_term, &t);
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
                    let mut individual_term = *(memory.get_unchecked(35usize));
                    let t = aux_boundary_values[5usize].teardown_timestamp_one_before_last_row[1];
                    field_ops::sub_assign_base(&mut individual_term, &t);
                    individual_term
                };
                individual_term
            };
            field_ops::add_assign(&mut accumulated_contribution, &contribution);
        }
        let divisor = divisors[3usize];
        field_ops::mul_assign(&mut accumulated_contribution, &divisor);
        accumulated_contribution
    };
    let last_row_contribution = {
        let mut accumulated_contribution = {
            let individual_term = {
                let mut individual_term = *(stage_2.get_unchecked(31usize));
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
