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
                let value = *(witness.get_unchecked(17usize));
                let mut t = value;
                t.sub_assign_base(&Mersenne31Field::ONE);
                t.mul_assign(&value);
                t
            };
            individual_term
        };
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(18usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(19usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(20usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(21usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(22usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(23usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(24usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(25usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(26usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(27usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(28usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(29usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(30usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(31usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(32usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(33usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(34usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(35usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(36usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(37usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(38usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(39usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(40usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(41usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(42usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(43usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(44usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let value = *(witness.get_unchecked(45usize));
                    let mut t = value;
                    t.sub_assign_base(&Mersenne31Field::ONE);
                    t.mul_assign(&value);
                    t
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(witness.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        let b = *(memory.get_unchecked(7usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(3usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(67usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        let b = *(memory.get_unchecked(8usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(4usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(48usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(35usize));
                        let b = *(memory.get_unchecked(25usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(35usize));
                        a.mul_assign_by_base(&Mersenne31Field(2147418115u32));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(70usize));
                        let b = *(memory.get_unchecked(25usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(35usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(70usize));
                        a.mul_assign_by_base(&Mersenne31Field(2147418115u32));
                        individual_term.add_assign(&a);
                    }
                    individual_term.add_assign_base(&Mersenne31Field(2147483646u32));
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(35usize));
                        let b = *(memory.get_unchecked(25usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(35usize));
                        a.mul_assign_by_base(&Mersenne31Field(2147483643u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(68usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(25usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term.add_assign_base(&Mersenne31Field(4u32));
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(35usize));
                        let b = *(witness.get_unchecked(36usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(36usize));
                        let b = *(memory.get_unchecked(26usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(36usize));
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(35usize));
                        let b = *(witness.get_unchecked(71usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(71usize));
                        let b = *(memory.get_unchecked(26usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(36usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(71usize));
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    individual_term.add_assign_base(&Mersenne31Field(2147483646u32));
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(35usize));
                        let b = *(witness.get_unchecked(36usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(36usize));
                        let b = *(memory.get_unchecked(26usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(35usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(69usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(26usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(74usize));
                        let b = *(witness.get_unchecked(76usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(78usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(78usize));
                        a.mul_assign(&b);
                        a
                    };
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(13usize));
                        let b = *(witness.get_unchecked(76usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(68usize));
                        let b = *(witness.get_unchecked(76usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(68usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(79usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(14usize));
                        let b = *(witness.get_unchecked(76usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(69usize));
                        let b = *(witness.get_unchecked(76usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(69usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(80usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(33usize));
                        let b = *(witness.get_unchecked(81usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(75usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(82usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(33usize));
                        let b = *(witness.get_unchecked(76usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(76usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(77usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(83usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(32usize));
                        let b = *(memory.get_unchecked(2usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(32usize));
                        let b = *(memory.get_unchecked(25usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(86usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(2usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(32usize));
                        let b = *(memory.get_unchecked(3usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(32usize));
                        let b = *(memory.get_unchecked(26usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(87usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(3usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(25usize));
                        let b = *(witness.get_unchecked(74usize));
                        a.mul_assign(&b);
                        a
                    };
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(48usize));
                        let b = *(memory.get_unchecked(2usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(65536u32));
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(48usize));
                        let b = *(memory.get_unchecked(3usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(67usize));
                        let b = *(memory.get_unchecked(2usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(67usize));
                        let b = *(memory.get_unchecked(3usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(65536u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(88usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(32usize));
                        let b = *(witness.get_unchecked(48usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(65536u32));
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(32usize));
                        let b = *(witness.get_unchecked(67usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(32usize));
                        let b = *(memory.get_unchecked(2usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(32usize));
                        let b = *(memory.get_unchecked(3usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(65536u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(33usize));
                        let b = *(witness.get_unchecked(88usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(34usize));
                        let b = *(witness.get_unchecked(48usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(34usize));
                        let b = *(witness.get_unchecked(67usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(34usize));
                        let b = *(memory.get_unchecked(2usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(34usize));
                        let b = *(memory.get_unchecked(3usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(65536u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(89usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(90usize));
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(28usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(28usize));
                        let b = *(witness.get_unchecked(89usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(28usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(28usize));
                        let b = *(witness.get_unchecked(90usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(28usize));
                        let b = *(witness.get_unchecked(37usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(28usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(27usize));
                        let b = *(witness.get_unchecked(74usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(27usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(91usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(27usize));
                        let b = *(witness.get_unchecked(74usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(92usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(91usize));
                        let b = *(memory.get_unchecked(10usize));
                        a.mul_assign(&b);
                        a
                    };
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(91usize));
                        let b = *(memory.get_unchecked(11usize));
                        a.mul_assign(&b);
                        a
                    };
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(91usize));
                        let b = *(memory.get_unchecked(7usize));
                        a.mul_assign(&b);
                        a
                    };
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(91usize));
                        let b = *(memory.get_unchecked(8usize));
                        a.mul_assign(&b);
                        a
                    };
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(92usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(92usize));
                        let b = *(memory.get_unchecked(10usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(92usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(92usize));
                        let b = *(memory.get_unchecked(11usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(0usize));
                        let b = *(witness.get_unchecked(27usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(27usize));
                        let b = *(memory.get_unchecked(10usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(0usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(10usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(27usize));
                        let b = *(memory.get_unchecked(11usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(11usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(31usize));
                        let b = *(witness.get_unchecked(74usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        let b = *(witness.get_unchecked(75usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(31usize));
                        let b = *(witness.get_unchecked(76usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(31usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(31usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        let b = *(memory.get_unchecked(17usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(31usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(31usize));
                        let b = *(witness.get_unchecked(67usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        let b = *(memory.get_unchecked(19usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(31usize));
                        let b = *(witness.get_unchecked(48usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        let b = *(memory.get_unchecked(20usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(24usize));
                        let b = *(witness.get_unchecked(74usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(24usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(24usize));
                        let b = *(witness.get_unchecked(75usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(21usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(memory.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(21usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(23usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(21usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(22usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(15usize));
                        let b = *(witness.get_unchecked(75usize));
                        a.mul_assign(&b);
                        a
                    };
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(16usize));
                        let b = *(witness.get_unchecked(75usize));
                        a.mul_assign(&b);
                        a
                    };
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(witness.get_unchecked(21usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(witness.get_unchecked(25usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(witness.get_unchecked(27usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(witness.get_unchecked(31usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(20usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(21usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(23usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(25usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(27usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(28usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(30usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(31usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(13usize));
                        let b = *(witness.get_unchecked(28usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(20usize));
                        let b = *(witness.get_unchecked(67usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(20usize));
                        let b = *(memory.get_unchecked(2usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(21usize));
                        let b = *(memory.get_unchecked(25usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(67usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(memory.get_unchecked(2usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(25usize));
                        let b = *(witness.get_unchecked(86usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(27usize));
                        let b = *(memory.get_unchecked(2usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(30usize));
                        let b = *(witness.get_unchecked(67usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(30usize));
                        let b = *(memory.get_unchecked(2usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        let b = *(memory.get_unchecked(2usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(28usize));
                        a.mul_assign_by_base(&Mersenne31Field(65535u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(40usize));
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(21usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(25usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(27usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(31usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(20usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(21usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(23usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(25usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(27usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(28usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(30usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(31usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        let b = *(witness.get_unchecked(28usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(20usize));
                        let b = *(witness.get_unchecked(48usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(20usize));
                        let b = *(memory.get_unchecked(3usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(21usize));
                        let b = *(memory.get_unchecked(26usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(48usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(memory.get_unchecked(3usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(25usize));
                        let b = *(witness.get_unchecked(87usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(27usize));
                        let b = *(memory.get_unchecked(3usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(30usize));
                        let b = *(witness.get_unchecked(48usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(30usize));
                        let b = *(memory.get_unchecked(3usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        let b = *(memory.get_unchecked(3usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(28usize));
                        a.mul_assign_by_base(&Mersenne31Field(32767u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(37usize));
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(40usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(witness.get_unchecked(23usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(13usize));
                        let b = *(witness.get_unchecked(23usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(memory.get_unchecked(25usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(41usize));
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(23usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        let b = *(witness.get_unchecked(23usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(memory.get_unchecked(26usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(39usize));
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(41usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(23usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(93usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(23usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(94usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(93usize));
                        let b = *(witness.get_unchecked(95usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(94usize));
                        let b = *(witness.get_unchecked(95usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(38usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term.add_assign_base(&Mersenne31Field(2147483646u32));
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(38usize));
                        let b = *(witness.get_unchecked(93usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(38usize));
                        let b = *(witness.get_unchecked(94usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(witness.get_unchecked(24usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(25usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(31usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(27usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(13usize));
                        let b = *(witness.get_unchecked(23usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(72usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(73usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(51usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(73usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(74usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(24usize));
                        let b = *(witness.get_unchecked(74usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(25usize));
                        let b = *(witness.get_unchecked(74usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(27usize));
                        let b = *(witness.get_unchecked(74usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        let b = *(witness.get_unchecked(74usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        a.mul_assign_by_base(&Mersenne31Field(31u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(52usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(74usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(75usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(24usize));
                        let b = *(witness.get_unchecked(75usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(25usize));
                        let b = *(witness.get_unchecked(75usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(27usize));
                        let b = *(witness.get_unchecked(75usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(74usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        let b = *(witness.get_unchecked(75usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(53usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(22usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        a.mul_assign_by_base(&Mersenne31Field(17u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(24usize));
                        a.mul_assign_by_base(&Mersenne31Field(25u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(25usize));
                        a.mul_assign_by_base(&Mersenne31Field(17u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(27usize));
                        a.mul_assign_by_base(&Mersenne31Field(23u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        a.mul_assign_by_base(&Mersenne31Field(7u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        a.mul_assign_by_base(&Mersenne31Field(18u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(54usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(23usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(27usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(31usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(72usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2139095039u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(memory.get_unchecked(2usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(8388608u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(37usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(8u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(38usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(16u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(46usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(32u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(49usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(64u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(27usize));
                        let b = *(witness.get_unchecked(75usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(65536u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(33usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2097152u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(74usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(65536u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(memory.get_unchecked(2usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(55usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(67usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(8388608u32));
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(73usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2139095039u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(76usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(27usize));
                        let b = *(witness.get_unchecked(76usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(75usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        let b = *(witness.get_unchecked(76usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(56usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(75usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(77usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(27usize));
                        let b = *(witness.get_unchecked(77usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(76usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        let b = *(witness.get_unchecked(77usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(57usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(22usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        a.mul_assign_by_base(&Mersenne31Field(22u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(27usize));
                        a.mul_assign_by_base(&Mersenne31Field(24u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        a.mul_assign_by_base(&Mersenne31Field(37u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        a.mul_assign_by_base(&Mersenne31Field(23u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(58usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(47usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(memory.get_unchecked(3usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(33usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2097152u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(74usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(65536u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(memory.get_unchecked(3usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(59usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(48usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(50usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(77usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(60usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(76usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(81usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(61usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(22usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        a.mul_assign_by_base(&Mersenne31Field(37u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(62usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(47usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(32usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(46usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(74usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(63usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(50usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(84usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(64usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(77usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(85usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(65usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(22usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        a.mul_assign_by_base(&Mersenne31Field(20u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(66usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(witness.get_unchecked(26usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(20usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(21usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(28usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(30usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(15usize));
                        let b = *(witness.get_unchecked(24usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(74usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(75usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(77usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(25usize));
                        let b = *(witness.get_unchecked(68usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(82usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(84usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(76usize));
                        let b = *(witness.get_unchecked(91usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(92usize));
                        let b = *(memory.get_unchecked(7usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(96usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(26usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(20usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(21usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(28usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(30usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(16usize));
                        let b = *(witness.get_unchecked(24usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(76usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(77usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(25usize));
                        let b = *(witness.get_unchecked(69usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(83usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(85usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(77usize));
                        let b = *(witness.get_unchecked(91usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(92usize));
                        let b = *(memory.get_unchecked(8usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(97usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(2usize));
                        let b = *(witness.get_unchecked(96usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(96usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(98usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(2usize));
                        let b = *(witness.get_unchecked(97usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(97usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(99usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(1usize));
                        let b = *(witness.get_unchecked(17usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        let b = *(memory.get_unchecked(17usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(17usize));
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a
                    };
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(19usize));
                        let b = *(memory.get_unchecked(17usize));
                        a.mul_assign(&b);
                        a
                    };
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(19usize));
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a
                    };
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(17usize));
                        let b = *(witness.get_unchecked(98usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        let b = *(memory.get_unchecked(19usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(17usize));
                        let b = *(witness.get_unchecked(99usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        let b = *(memory.get_unchecked(20usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(19usize));
                        let b = *(memory.get_unchecked(19usize));
                        a.mul_assign(&b);
                        a
                    };
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(19usize));
                        let b = *(memory.get_unchecked(20usize));
                        a.mul_assign(&b);
                        a
                    };
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(20usize));
                        let b = *(witness.get_unchecked(68usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(21usize));
                        let b = *(witness.get_unchecked(68usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(68usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(79usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(24usize));
                        let b = *(witness.get_unchecked(68usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(25usize));
                        let b = *(witness.get_unchecked(75usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(26usize));
                        let b = *(witness.get_unchecked(68usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(27usize));
                        let b = *(witness.get_unchecked(68usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(28usize));
                        let b = *(witness.get_unchecked(68usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(68usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(30usize));
                        let b = *(witness.get_unchecked(68usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        let b = *(witness.get_unchecked(68usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(29usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(witness.get_unchecked(25usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(20usize));
                        let b = *(witness.get_unchecked(69usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(21usize));
                        let b = *(witness.get_unchecked(69usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(witness.get_unchecked(69usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        let b = *(witness.get_unchecked(80usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(24usize));
                        let b = *(witness.get_unchecked(69usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(26usize));
                        let b = *(witness.get_unchecked(69usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(27usize));
                        let b = *(witness.get_unchecked(69usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(28usize));
                        let b = *(witness.get_unchecked(69usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(witness.get_unchecked(69usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(30usize));
                        let b = *(witness.get_unchecked(69usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        let b = *(witness.get_unchecked(69usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(30usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(6usize));
                        a.negate();
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(17usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        a.mul_assign_by_base(&Mersenne31Field(2u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(19usize));
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(20usize));
                        a.mul_assign_by_base(&Mersenne31Field(8u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(21usize));
                        a.mul_assign_by_base(&Mersenne31Field(16u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(22usize));
                        a.mul_assign_by_base(&Mersenne31Field(32u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        a.mul_assign_by_base(&Mersenne31Field(64u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(24usize));
                        a.mul_assign_by_base(&Mersenne31Field(128u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(25usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(26usize));
                        a.mul_assign_by_base(&Mersenne31Field(512u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(27usize));
                        a.mul_assign_by_base(&Mersenne31Field(1024u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(28usize));
                        a.mul_assign_by_base(&Mersenne31Field(2048u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        a.mul_assign_by_base(&Mersenne31Field(4096u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(30usize));
                        a.mul_assign_by_base(&Mersenne31Field(8192u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        a.mul_assign_by_base(&Mersenne31Field(16384u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(32usize));
                        a.mul_assign_by_base(&Mersenne31Field(32768u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(33usize));
                        a.mul_assign_by_base(&Mersenne31Field(65536u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(34usize));
                        a.mul_assign_by_base(&Mersenne31Field(131072u32));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(27usize));
                        a.negate();
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(9usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term.add_assign_base(&Mersenne31Field(1u32));
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(31usize));
                        a.negate();
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(16usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term.add_assign_base(&Mersenne31Field(1u32));
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
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
            let c = *(stage_2.get_unchecked(0usize));
            {
                accumulated_contribution.mul_assign(&quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let mut individual_term = a;
                        individual_term.mul_assign(&b);
                        individual_term.sub_assign(&c);
                        individual_term
                    };
                    individual_term
                };
                accumulated_contribution.add_assign(&contribution);
            }
            {
                accumulated_contribution.mul_assign(&quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let acc_value = *(stage_2.get_unchecked(7usize));
                        let mut denom = lookup_argument_gamma;
                        denom.add_assign(&a);
                        denom.add_assign(&b);
                        denom.mul_assign(&lookup_argument_gamma);
                        denom.add_assign(&c);
                        denom.mul_assign(&acc_value);
                        let mut numerator = lookup_argument_two_gamma;
                        numerator.add_assign(&a);
                        numerator.add_assign(&b);
                        let mut individual_term = denom;
                        individual_term.sub_assign(&numerator);
                        individual_term
                    };
                    individual_term
                };
                accumulated_contribution.add_assign(&contribution);
            }
        }
        {
            let a = {
                let value = *(witness.get_unchecked(13usize));
                value
            };
            let b = {
                let value = *(witness.get_unchecked(14usize));
                value
            };
            let c = *(stage_2.get_unchecked(1usize));
            {
                accumulated_contribution.mul_assign(&quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let mut individual_term = a;
                        individual_term.mul_assign(&b);
                        individual_term.sub_assign(&c);
                        individual_term
                    };
                    individual_term
                };
                accumulated_contribution.add_assign(&contribution);
            }
            {
                accumulated_contribution.mul_assign(&quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let acc_value = *(stage_2.get_unchecked(8usize));
                        let mut denom = lookup_argument_gamma;
                        denom.add_assign(&a);
                        denom.add_assign(&b);
                        denom.mul_assign(&lookup_argument_gamma);
                        denom.add_assign(&c);
                        denom.mul_assign(&acc_value);
                        let mut numerator = lookup_argument_two_gamma;
                        numerator.add_assign(&a);
                        numerator.add_assign(&b);
                        let mut individual_term = denom;
                        individual_term.sub_assign(&numerator);
                        individual_term
                    };
                    individual_term
                };
                accumulated_contribution.add_assign(&contribution);
            }
        }
        {
            let a = {
                let value = *(witness.get_unchecked(15usize));
                value
            };
            let b = {
                let value = *(witness.get_unchecked(16usize));
                value
            };
            let c = *(stage_2.get_unchecked(2usize));
            {
                accumulated_contribution.mul_assign(&quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let mut individual_term = a;
                        individual_term.mul_assign(&b);
                        individual_term.sub_assign(&c);
                        individual_term
                    };
                    individual_term
                };
                accumulated_contribution.add_assign(&contribution);
            }
            {
                accumulated_contribution.mul_assign(&quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let acc_value = *(stage_2.get_unchecked(9usize));
                        let mut denom = lookup_argument_gamma;
                        denom.add_assign(&a);
                        denom.add_assign(&b);
                        denom.mul_assign(&lookup_argument_gamma);
                        denom.add_assign(&c);
                        denom.mul_assign(&acc_value);
                        let mut numerator = lookup_argument_two_gamma;
                        numerator.add_assign(&a);
                        numerator.add_assign(&b);
                        let mut individual_term = denom;
                        individual_term.sub_assign(&numerator);
                        individual_term
                    };
                    individual_term
                };
                accumulated_contribution.add_assign(&contribution);
            }
        }
        {
            let a = {
                let individual_term = {
                    let mut individual_term = {
                        let a = *(memory.get_unchecked(31usize));
                        a
                    };
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let a = *(memory.get_unchecked(32usize));
                        a
                    };
                    individual_term
                };
                individual_term
            };
            let c = *(stage_2.get_unchecked(3usize));
            {
                accumulated_contribution.mul_assign(&quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let mut individual_term = a;
                        individual_term.mul_assign(&b);
                        individual_term.sub_assign(&c);
                        individual_term
                    };
                    individual_term
                };
                accumulated_contribution.add_assign(&contribution);
            }
            {
                accumulated_contribution.mul_assign(&quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let acc_value = *(stage_2.get_unchecked(10usize));
                        let mut denom = lookup_argument_gamma;
                        denom.add_assign(&a);
                        denom.add_assign(&b);
                        denom.mul_assign(&lookup_argument_gamma);
                        denom.add_assign(&c);
                        denom.mul_assign(&acc_value);
                        let mut numerator = lookup_argument_two_gamma;
                        numerator.add_assign(&a);
                        numerator.add_assign(&b);
                        let mut individual_term = denom;
                        individual_term.sub_assign(&numerator);
                        individual_term
                    };
                    individual_term
                };
                accumulated_contribution.add_assign(&contribution);
            }
        }
        {
            let a = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(42usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(0usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(27usize));
                        individual_term.sub_assign(&a);
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
                        let a = *(memory.get_unchecked(28usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(42usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term.add_assign_base(&Mersenne31Field(524288u32));
                    individual_term
                };
                individual_term
            };
            let c = *(stage_2.get_unchecked(4usize));
            {
                accumulated_contribution.mul_assign(&quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let mut individual_term = a;
                        individual_term.mul_assign(&b);
                        individual_term.sub_assign(&c);
                        individual_term
                    };
                    individual_term
                };
                accumulated_contribution.add_assign(&contribution);
            }
            {
                accumulated_contribution.mul_assign(&quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let acc_value = *(stage_2.get_unchecked(11usize));
                        let mut denom = lookup_argument_gamma;
                        denom.add_assign(&a);
                        denom.add_assign(&b);
                        denom.mul_assign(&lookup_argument_gamma);
                        denom.add_assign(&c);
                        denom.mul_assign(&acc_value);
                        let mut numerator = lookup_argument_two_gamma;
                        numerator.add_assign(&a);
                        numerator.add_assign(&b);
                        let mut individual_term = denom;
                        individual_term.sub_assign(&numerator);
                        individual_term
                    };
                    individual_term
                };
                accumulated_contribution.add_assign(&contribution);
            }
        }
        {
            let a = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(43usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(5usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(27usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term.add_assign_base(&Mersenne31Field(2147483646u32));
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
                        let a = *(memory.get_unchecked(28usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(43usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term.add_assign_base(&Mersenne31Field(524288u32));
                    individual_term
                };
                individual_term
            };
            let c = *(stage_2.get_unchecked(5usize));
            {
                accumulated_contribution.mul_assign(&quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let mut individual_term = a;
                        individual_term.mul_assign(&b);
                        individual_term.sub_assign(&c);
                        individual_term
                    };
                    individual_term
                };
                accumulated_contribution.add_assign(&contribution);
            }
            {
                accumulated_contribution.mul_assign(&quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let acc_value = *(stage_2.get_unchecked(12usize));
                        let mut denom = lookup_argument_gamma;
                        denom.add_assign(&a);
                        denom.add_assign(&b);
                        denom.mul_assign(&lookup_argument_gamma);
                        denom.add_assign(&c);
                        denom.mul_assign(&acc_value);
                        let mut numerator = lookup_argument_two_gamma;
                        numerator.add_assign(&a);
                        numerator.add_assign(&b);
                        let mut individual_term = denom;
                        individual_term.sub_assign(&numerator);
                        individual_term
                    };
                    individual_term
                };
                accumulated_contribution.add_assign(&contribution);
            }
        }
        {
            let a = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(44usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(12usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(27usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term.add_assign_base(&Mersenne31Field(2147483645u32));
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let a = *(memory.get_unchecked(13usize));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(28usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(44usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term.add_assign_base(&Mersenne31Field(524288u32));
                    individual_term
                };
                individual_term
            };
            let c = *(stage_2.get_unchecked(6usize));
            {
                accumulated_contribution.mul_assign(&quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let mut individual_term = a;
                        individual_term.mul_assign(&b);
                        individual_term.sub_assign(&c);
                        individual_term
                    };
                    individual_term
                };
                accumulated_contribution.add_assign(&contribution);
            }
            {
                accumulated_contribution.mul_assign(&quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let acc_value = *(stage_2.get_unchecked(13usize));
                        let mut denom = lookup_argument_gamma;
                        denom.add_assign(&a);
                        denom.add_assign(&b);
                        denom.mul_assign(&lookup_argument_gamma);
                        denom.add_assign(&c);
                        denom.mul_assign(&acc_value);
                        let mut numerator = lookup_argument_two_gamma;
                        numerator.add_assign(&a);
                        numerator.add_assign(&b);
                        let mut individual_term = denom;
                        individual_term.sub_assign(&numerator);
                        individual_term
                    };
                    individual_term
                };
                accumulated_contribution.add_assign(&contribution);
            }
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let m = *(memory.get_unchecked(24usize));
                    let mut denom = decoder_lookup_argument_gamma;
                    denom.add_assign(&*(memory.get_unchecked(25usize)));
                    let mut t = decoder_lookup_argument_linearization_challenges[0usize];
                    t.mul_assign(&*(memory.get_unchecked(26usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[1usize];
                    t.mul_assign(&*(memory.get_unchecked(4usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[2usize];
                    t.mul_assign(&*(witness.get_unchecked(0usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[3usize];
                    t.mul_assign(&*(witness.get_unchecked(1usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[4usize];
                    t.mul_assign(&*(witness.get_unchecked(2usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[5usize];
                    t.mul_assign(&*(witness.get_unchecked(3usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[6usize];
                    t.mul_assign(&*(witness.get_unchecked(4usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[7usize];
                    t.mul_assign(&*(witness.get_unchecked(5usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[8usize];
                    t.mul_assign(&*(witness.get_unchecked(6usize)));
                    denom.add_assign(&t);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(20usize)));
                    individual_term.sub_assign(&m);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let src0 = {
                        let value = *(memory.get_unchecked(3usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(46usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(47usize));
                        value
                    };
                    let mut denom = lookup_argument_linearization_challenges[2];
                    let table_id = Mersenne31Field(16u32);
                    denom.mul_assign_by_base(&table_id);
                    let mut t = lookup_argument_linearization_challenges[1];
                    t.mul_assign_by_base(&src2);
                    denom.add_assign(&t);
                    let mut t = lookup_argument_linearization_challenges[0];
                    t.mul_assign_by_base(&src1);
                    denom.add_assign(&t);
                    denom.add_assign(&src0);
                    denom.add_assign(&lookup_argument_gamma);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(14usize)));
                    individual_term.sub_assign_base(&Mersenne31Field::ONE);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let src0 = {
                        let value = *(witness.get_unchecked(48usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(49usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(50usize));
                        value
                    };
                    let mut denom = lookup_argument_linearization_challenges[2];
                    let table_id = Mersenne31Field(16u32);
                    denom.mul_assign_by_base(&table_id);
                    let mut t = lookup_argument_linearization_challenges[1];
                    t.mul_assign_by_base(&src2);
                    denom.add_assign(&t);
                    let mut t = lookup_argument_linearization_challenges[0];
                    t.mul_assign_by_base(&src1);
                    denom.add_assign(&t);
                    denom.add_assign(&src0);
                    denom.add_assign(&lookup_argument_gamma);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(15usize)));
                    individual_term.sub_assign_base(&Mersenne31Field::ONE);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let src0 = {
                        let value = *(witness.get_unchecked(51usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(52usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(53usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(54usize));
                    let mut denom = lookup_argument_linearization_challenges[2];
                    denom.mul_assign(&table_id);
                    let mut t = lookup_argument_linearization_challenges[1];
                    t.mul_assign_by_base(&src2);
                    denom.add_assign(&t);
                    let mut t = lookup_argument_linearization_challenges[0];
                    t.mul_assign_by_base(&src1);
                    denom.add_assign(&t);
                    denom.add_assign(&src0);
                    denom.add_assign(&lookup_argument_gamma);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(16usize)));
                    individual_term.sub_assign_base(&Mersenne31Field::ONE);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let src0 = {
                        let value = *(witness.get_unchecked(55usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(56usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(57usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(58usize));
                    let mut denom = lookup_argument_linearization_challenges[2];
                    denom.mul_assign(&table_id);
                    let mut t = lookup_argument_linearization_challenges[1];
                    t.mul_assign_by_base(&src2);
                    denom.add_assign(&t);
                    let mut t = lookup_argument_linearization_challenges[0];
                    t.mul_assign_by_base(&src1);
                    denom.add_assign(&t);
                    denom.add_assign(&src0);
                    denom.add_assign(&lookup_argument_gamma);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(17usize)));
                    individual_term.sub_assign_base(&Mersenne31Field::ONE);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let src0 = {
                        let value = *(witness.get_unchecked(59usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(60usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(61usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(62usize));
                    let mut denom = lookup_argument_linearization_challenges[2];
                    denom.mul_assign(&table_id);
                    let mut t = lookup_argument_linearization_challenges[1];
                    t.mul_assign_by_base(&src2);
                    denom.add_assign(&t);
                    let mut t = lookup_argument_linearization_challenges[0];
                    t.mul_assign_by_base(&src1);
                    denom.add_assign(&t);
                    denom.add_assign(&src0);
                    denom.add_assign(&lookup_argument_gamma);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(18usize)));
                    individual_term.sub_assign_base(&Mersenne31Field::ONE);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let src0 = {
                        let value = *(witness.get_unchecked(63usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(64usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(65usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(66usize));
                    let mut denom = lookup_argument_linearization_challenges[2];
                    denom.mul_assign(&table_id);
                    let mut t = lookup_argument_linearization_challenges[1];
                    t.mul_assign_by_base(&src2);
                    denom.add_assign(&t);
                    let mut t = lookup_argument_linearization_challenges[0];
                    t.mul_assign_by_base(&src1);
                    denom.add_assign(&t);
                    denom.add_assign(&src0);
                    denom.add_assign(&lookup_argument_gamma);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(19usize)));
                    individual_term.sub_assign_base(&Mersenne31Field::ONE);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let m = *(witness.get_unchecked(7usize));
                    let t = *(setup.get_unchecked(0usize));
                    let mut denom = lookup_argument_gamma;
                    denom.add_assign(&t);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(21usize)));
                    individual_term.sub_assign(&m);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let m = *(witness.get_unchecked(8usize));
                    let t = *(setup.get_unchecked(1usize));
                    let mut denom = lookup_argument_gamma;
                    denom.add_assign(&t);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(22usize)));
                    individual_term.sub_assign(&m);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let m = *(witness.get_unchecked(9usize));
                    let mut denom = decoder_lookup_argument_gamma;
                    denom.add_assign(&*(setup.get_unchecked(6usize)));
                    let mut t = decoder_lookup_argument_linearization_challenges[0usize];
                    t.mul_assign(&*(setup.get_unchecked(7usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[1usize];
                    t.mul_assign(&*(setup.get_unchecked(8usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[2usize];
                    t.mul_assign(&*(setup.get_unchecked(9usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[3usize];
                    t.mul_assign(&*(setup.get_unchecked(10usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[4usize];
                    t.mul_assign(&*(setup.get_unchecked(11usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[5usize];
                    t.mul_assign(&*(setup.get_unchecked(12usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[6usize];
                    t.mul_assign(&*(setup.get_unchecked(13usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[7usize];
                    t.mul_assign(&*(setup.get_unchecked(14usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[8usize];
                    t.mul_assign(&*(setup.get_unchecked(15usize)));
                    denom.add_assign(&t);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(24usize)));
                    individual_term.sub_assign(&m);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let m = *(witness.get_unchecked(10usize));
                    let mut denom = lookup_argument_linearization_challenges[2];
                    let table_id = *(setup.get_unchecked(5usize));
                    denom.mul_assign(&table_id);
                    let mut t = lookup_argument_linearization_challenges[1];
                    t.mul_assign(&*(setup.get_unchecked(4usize)));
                    denom.add_assign(&t);
                    let mut t = lookup_argument_linearization_challenges[0];
                    t.mul_assign(&*(setup.get_unchecked(3usize)));
                    denom.add_assign(&t);
                    let t = *(setup.get_unchecked(2usize));
                    denom.add_assign(&t);
                    denom.add_assign(&lookup_argument_gamma);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(23usize)));
                    individual_term.sub_assign(&m);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let m = *(memory.get_unchecked(21usize));
                    let mut denom = delegation_argument_linearization_challenges[2];
                    let timestamp_high = *(memory.get_unchecked(28usize));
                    denom.mul_assign(&timestamp_high);
                    let mut timestamp_low = *(memory.get_unchecked(27usize));
                    timestamp_low.add_assign_base(&Mersenne31Field(3u32));
                    let mut t = delegation_argument_linearization_challenges[1];
                    t.mul_assign(&timestamp_low);
                    denom.add_assign(&t);
                    let mem_abi_offset = *(memory.get_unchecked(23usize));
                    let mut t = delegation_argument_linearization_challenges[0];
                    t.mul_assign(&mem_abi_offset);
                    denom.add_assign(&t);
                    let t = *(memory.get_unchecked(22usize));
                    denom.add_assign(&t);
                    denom.add_assign(&delegation_argument_gamma);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(25usize)));
                    individual_term.sub_assign(&m);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let address_contribution = {
                        let address_low = *(memory.get_unchecked(4usize));
                        let mut address_contribution =
                            memory_argument_linearization_challenges[0usize];
                        address_contribution.mul_assign(&address_low);
                        address_contribution.add_assign_base(&Mersenne31Field::ONE);
                        address_contribution
                    };
                    let value_low = *(memory.get_unchecked(2usize));
                    let mut value_contribution = memory_argument_linearization_challenges[4usize];
                    value_contribution.mul_assign(&value_low);
                    let value_high = *(memory.get_unchecked(3usize));
                    let mut t = memory_argument_linearization_challenges[5usize];
                    t.mul_assign(&value_high);
                    value_contribution.add_assign(&t);
                    let mut numerator = memory_argument_gamma;
                    numerator.add_assign(&address_contribution);
                    numerator.add_assign(&value_contribution);
                    let mut denom = numerator;
                    let read_timestamp_low = *(memory.get_unchecked(0usize));
                    let mut read_timestamp_contribution =
                        memory_argument_linearization_challenges[2usize];
                    read_timestamp_contribution.mul_assign(&read_timestamp_low);
                    let read_timestamp_high = *(memory.get_unchecked(1usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    t.mul_assign(&read_timestamp_high);
                    read_timestamp_contribution.add_assign(&t);
                    let mut write_timestamp_low = *(memory.get_unchecked(27usize));
                    write_timestamp_low.add_assign_base(&Mersenne31Field(0u32));
                    let mut write_timestamp_contribution =
                        memory_argument_linearization_challenges[2usize];
                    write_timestamp_contribution.mul_assign(&write_timestamp_low);
                    let mut write_timestamp_high = *(memory.get_unchecked(28usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    t.mul_assign(&write_timestamp_high);
                    write_timestamp_contribution.add_assign(&t);
                    numerator.add_assign(&write_timestamp_contribution);
                    denom.add_assign(&read_timestamp_contribution);
                    let accumulator = *(stage_2.get_unchecked(26usize));
                    let mut individual_term = accumulator;
                    individual_term.mul_assign(&denom);
                    individual_term.sub_assign(&numerator);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let address_contribution = {
                        let address_low = *(memory.get_unchecked(10usize));
                        let mut address_contribution =
                            memory_argument_linearization_challenges[0usize];
                        address_contribution.mul_assign(&address_low);
                        let address_high = *(memory.get_unchecked(11usize));
                        let mut t = memory_argument_linearization_challenges[1usize];
                        t.mul_assign(&address_high);
                        address_contribution.add_assign(&t);
                        let is_register = *(memory.get_unchecked(9usize));
                        address_contribution.add_assign(&is_register);
                        address_contribution
                    };
                    let value_low = *(memory.get_unchecked(7usize));
                    let mut value_contribution = memory_argument_linearization_challenges[4usize];
                    value_contribution.mul_assign(&value_low);
                    let value_high = *(memory.get_unchecked(8usize));
                    let mut t = memory_argument_linearization_challenges[5usize];
                    t.mul_assign(&value_high);
                    value_contribution.add_assign(&t);
                    let mut numerator = memory_argument_gamma;
                    numerator.add_assign(&address_contribution);
                    numerator.add_assign(&value_contribution);
                    let mut denom = numerator;
                    let read_timestamp_low = *(memory.get_unchecked(5usize));
                    let mut read_timestamp_contribution =
                        memory_argument_linearization_challenges[2usize];
                    read_timestamp_contribution.mul_assign(&read_timestamp_low);
                    let read_timestamp_high = *(memory.get_unchecked(6usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    t.mul_assign(&read_timestamp_high);
                    read_timestamp_contribution.add_assign(&t);
                    let mut write_timestamp_low = *(memory.get_unchecked(27usize));
                    write_timestamp_low.add_assign_base(&Mersenne31Field(1u32));
                    let mut write_timestamp_contribution =
                        memory_argument_linearization_challenges[2usize];
                    write_timestamp_contribution.mul_assign(&write_timestamp_low);
                    let mut write_timestamp_high = *(memory.get_unchecked(28usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    t.mul_assign(&write_timestamp_high);
                    write_timestamp_contribution.add_assign(&t);
                    numerator.add_assign(&write_timestamp_contribution);
                    denom.add_assign(&read_timestamp_contribution);
                    let accumulator = *(stage_2.get_unchecked(27usize));
                    let previous = *(stage_2.get_unchecked(26usize));
                    let mut individual_term = accumulator;
                    individual_term.mul_assign(&denom);
                    let mut t = previous;
                    t.mul_assign(&numerator);
                    individual_term.sub_assign(&t);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let address_contribution = {
                        let address_low = *(memory.get_unchecked(17usize));
                        let mut address_contribution =
                            memory_argument_linearization_challenges[0usize];
                        address_contribution.mul_assign(&address_low);
                        let address_high = *(memory.get_unchecked(18usize));
                        let mut t = memory_argument_linearization_challenges[1usize];
                        t.mul_assign(&address_high);
                        address_contribution.add_assign(&t);
                        let is_register = *(memory.get_unchecked(16usize));
                        address_contribution.add_assign(&is_register);
                        address_contribution
                    };
                    let mut numerator = memory_argument_gamma;
                    numerator.add_assign(&address_contribution);
                    let mut denom = numerator;
                    let read_value_low = *(memory.get_unchecked(14usize));
                    let mut read_value_contribution =
                        memory_argument_linearization_challenges[4usize];
                    read_value_contribution.mul_assign(&read_value_low);
                    let read_value_high = *(memory.get_unchecked(15usize));
                    let mut t = memory_argument_linearization_challenges[5usize];
                    t.mul_assign(&read_value_high);
                    read_value_contribution.add_assign(&t);
                    let write_value_low = *(memory.get_unchecked(19usize));
                    let mut write_value_contribution =
                        memory_argument_linearization_challenges[4usize];
                    write_value_contribution.mul_assign(&write_value_low);
                    let write_value_high = *(memory.get_unchecked(20usize));
                    let mut t = memory_argument_linearization_challenges[5usize];
                    t.mul_assign(&write_value_high);
                    write_value_contribution.add_assign(&t);
                    numerator.add_assign(&write_value_contribution);
                    denom.add_assign(&read_value_contribution);
                    let read_timestamp_low = *(memory.get_unchecked(12usize));
                    let mut read_timestamp_contribution =
                        memory_argument_linearization_challenges[2usize];
                    read_timestamp_contribution.mul_assign(&read_timestamp_low);
                    let read_timestamp_high = *(memory.get_unchecked(13usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    t.mul_assign(&read_timestamp_high);
                    read_timestamp_contribution.add_assign(&t);
                    let mut write_timestamp_low = *(memory.get_unchecked(27usize));
                    write_timestamp_low.add_assign_base(&Mersenne31Field(2u32));
                    let mut write_timestamp_contribution =
                        memory_argument_linearization_challenges[2usize];
                    write_timestamp_contribution.mul_assign(&write_timestamp_low);
                    let mut write_timestamp_high = *(memory.get_unchecked(28usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    t.mul_assign(&write_timestamp_high);
                    write_timestamp_contribution.add_assign(&t);
                    numerator.add_assign(&write_timestamp_contribution);
                    denom.add_assign(&read_timestamp_contribution);
                    let accumulator = *(stage_2.get_unchecked(28usize));
                    let previous = *(stage_2.get_unchecked(27usize));
                    let mut individual_term = accumulator;
                    individual_term.mul_assign(&denom);
                    let mut t = previous;
                    t.mul_assign(&numerator);
                    individual_term.sub_assign(&t);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut numerator = state_permutation_argument_gamma;
                    numerator.add_assign(&*(memory.get_unchecked(29usize)));
                    let mut t = state_permutation_argument_linearization_challenges[0];
                    t.mul_assign(&*(memory.get_unchecked(30usize)));
                    numerator.add_assign(&t);
                    let mut t = state_permutation_argument_linearization_challenges[1];
                    t.mul_assign(&*(memory.get_unchecked(31usize)));
                    numerator.add_assign(&t);
                    let mut t = state_permutation_argument_linearization_challenges[2];
                    t.mul_assign(&*(memory.get_unchecked(32usize)));
                    numerator.add_assign(&t);
                    let mut denom = state_permutation_argument_gamma;
                    denom.add_assign(&*(memory.get_unchecked(25usize)));
                    let mut t = state_permutation_argument_linearization_challenges[0];
                    t.mul_assign(&*(memory.get_unchecked(26usize)));
                    denom.add_assign(&t);
                    let mut t = state_permutation_argument_linearization_challenges[1];
                    t.mul_assign(&*(memory.get_unchecked(27usize)));
                    denom.add_assign(&t);
                    let mut t = state_permutation_argument_linearization_challenges[2];
                    t.mul_assign(&*(memory.get_unchecked(28usize)));
                    denom.add_assign(&t);
                    let mut individual_term = *(stage_2.get_unchecked(29usize));
                    individual_term.mul_assign(&denom);
                    let mut t = *(stage_2.get_unchecked(28usize));
                    t.mul_assign(&numerator);
                    individual_term.sub_assign(&t);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = *(stage_2.get_unchecked(30usize));
                    let predicate = *(memory.get_unchecked(24usize));
                    let mut t = *(stage_2.get_unchecked(29usize));
                    t.mul_assign(&predicate);
                    individual_term.sub_assign(&t);
                    individual_term.add_assign(&predicate);
                    individual_term.sub_assign_base(&Mersenne31Field::ONE);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = *(stage_2_next_row.get_unchecked(31usize));
                    let mut t = *(stage_2.get_unchecked(31usize));
                    t.mul_assign(&*(stage_2.get_unchecked(30usize)));
                    individual_term.sub_assign(&t);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        let divisor = divisors[0usize];
        accumulated_contribution.mul_assign(&divisor);
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
                let mut individual_term = *(stage_2.get_unchecked(21usize));
                let t = *(stage_2.get_unchecked(7usize));
                individual_term.sub_assign(&t);
                let t = *(stage_2.get_unchecked(8usize));
                individual_term.sub_assign(&t);
                let t = *(stage_2.get_unchecked(9usize));
                individual_term.sub_assign(&t);
                individual_term
            };
            individual_term
        };
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = *(stage_2.get_unchecked(22usize));
                    let t = *(stage_2.get_unchecked(10usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(11usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(12usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(13usize));
                    individual_term.sub_assign(&t);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = *(stage_2.get_unchecked(24usize));
                    individual_term.sub_assign(&*(stage_2.get_unchecked(20usize)));
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = *(stage_2.get_unchecked(23usize));
                    let t = *(stage_2.get_unchecked(14usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(15usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(16usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(17usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(18usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(19usize));
                    individual_term.sub_assign(&t);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = *(stage_2.get_unchecked(25usize));
                    let mut t = random_point;
                    t.mul_assign(&delegation_argument_interpolant_linear_coeff);
                    individual_term.sub_assign(&t);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        let divisor = divisors[5usize];
        accumulated_contribution.mul_assign(&divisor);
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
                let mut individual_term = *(stage_2.get_unchecked(31usize));
                individual_term.sub_assign_base(&Mersenne31Field::ONE);
                individual_term
            };
            individual_term
        };
        let divisor = divisors[2usize];
        accumulated_contribution.mul_assign(&divisor);
        accumulated_contribution
    };
    let one_before_last_row_contribution = Mersenne31Quartic::ZERO;
    let last_row_contribution = {
        let mut accumulated_contribution = {
            let individual_term = {
                let mut individual_term = *(stage_2.get_unchecked(31usize));
                let t = aux_proof_values.grand_product_accumulator_final_value;
                individual_term.sub_assign(&t);
                individual_term
            };
            individual_term
        };
        let divisor = divisors[4usize];
        accumulated_contribution.mul_assign(&divisor);
        accumulated_contribution
    };
    let mut quotient = every_row_except_last_contribution;
    quotient.mul_assign(&quotient_beta);
    quotient.add_assign(&every_row_except_two_last_contribution);
    quotient.mul_assign(&quotient_beta);
    quotient.add_assign(&first_row_contribution);
    quotient.mul_assign(&quotient_beta);
    quotient.add_assign(&one_before_last_row_contribution);
    quotient.mul_assign(&quotient_beta);
    quotient.add_assign(&last_row_contribution);
    quotient.mul_assign(&quotient_beta);
    quotient.add_assign(&last_row_and_zero_contribution);
    quotient
}
