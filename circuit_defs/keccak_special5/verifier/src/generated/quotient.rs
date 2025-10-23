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
                let value = *(witness.get_unchecked(3usize));
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
                    let value = *(witness.get_unchecked(4usize));
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
                    let value = *(witness.get_unchecked(5usize));
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
                    let value = *(witness.get_unchecked(6usize));
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
                    let value = *(witness.get_unchecked(7usize));
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
                    let value = *(witness.get_unchecked(8usize));
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
                    let value = *(witness.get_unchecked(9usize));
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
                    let value = *(witness.get_unchecked(10usize));
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
                    let value = *(witness.get_unchecked(11usize));
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
                    let value = *(witness.get_unchecked(12usize));
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
                    let value = *(witness.get_unchecked(13usize));
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
                    let value = *(witness.get_unchecked(14usize));
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
                    let value = *(witness.get_unchecked(15usize));
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
                    let value = *(witness.get_unchecked(16usize));
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
                    let value = *(witness.get_unchecked(17usize));
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
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(0usize));
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
                        let mut a = *(witness.get_unchecked(10usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(13usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(0usize));
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
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(3usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(4usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(5usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(6usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(7usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(8usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(9usize));
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
                        let mut a = *(witness.get_unchecked(10usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(13usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        let b = *(memory.get_unchecked(0usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(10usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(11usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(12usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(13usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(14usize));
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
                        let b = *(witness.get_unchecked(14usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483608u32));
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(witness.get_unchecked(14usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483608u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(witness.get_unchecked(14usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483608u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(14usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(19u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        a.mul_assign_by_base(&Mersenne31Field(8u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        a.mul_assign_by_base(&Mersenne31Field(2u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        a.mul_assign_by_base(&Mersenne31Field(3u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        a.mul_assign_by_base(&Mersenne31Field(11u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        a.mul_assign_by_base(&Mersenne31Field(12u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        a.mul_assign_by_base(&Mersenne31Field(6u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        a.mul_assign_by_base(&Mersenne31Field(13u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        a.mul_assign_by_base(&Mersenne31Field(8u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        a.mul_assign_by_base(&Mersenne31Field(16u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(13usize));
                        a.mul_assign_by_base(&Mersenne31Field(24u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        a.mul_assign_by_base(&Mersenne31Field(32u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(15usize));
                        a.mul_assign_by_base(&Mersenne31Field(64u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(16usize));
                        a.mul_assign_by_base(&Mersenne31Field(128u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        a.mul_assign_by_base(&Mersenne31Field(512u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(19usize));
                        a.mul_assign_by_base(&Mersenne31Field(1024u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(8usize));
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
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(witness.get_unchecked(10usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(159usize));
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
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(witness.get_unchecked(11usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(160usize));
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
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(witness.get_unchecked(12usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(161usize));
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
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(witness.get_unchecked(13usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(162usize));
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
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(witness.get_unchecked(14usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(163usize));
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
                        let mut a = *(witness.get_unchecked(10usize));
                        let b = *(witness.get_unchecked(15usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(10usize));
                        let b = *(witness.get_unchecked(16usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(10usize));
                        let b = *(witness.get_unchecked(17usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(10usize));
                        let b = *(witness.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(8u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(10usize));
                        let b = *(witness.get_unchecked(19usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(16u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(164usize));
                        a.mul_assign_by_base(&Mersenne31Field(2130771712u32));
                        individual_term.add_assign(&a);
                    }
                    individual_term.add_assign_base(&Mersenne31Field(1612701951u32));
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
                        let b = *(memory.get_unchecked(17usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(4usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(5usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(38usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(17usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(5usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(38usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(30usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(17usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(17usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(17usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(43usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(38usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(38usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(38usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(38usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(38usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145779711u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145845247u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145976319u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(34usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(38usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(164usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(35usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(39usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(35usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(39usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(82usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(30usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(17usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(35usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(35usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(35usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(35usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(35usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(39usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(39usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(39usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(39usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(39usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        a.mul_assign_by_base(&Mersenne31Field(49344u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(35usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(39usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(19usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(40usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(45usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(84usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(40usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(45usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(165usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(19usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(19usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(71usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(165usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(35usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(36usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(36usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(36usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(40usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(40usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(40usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483392u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(40usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(40usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(42usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(42usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(45usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(45usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(46usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(46usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(36usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(40usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(4usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(5usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(38usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(41usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(44usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(5usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(38usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(41usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(44usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(31usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(44usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(38usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(38usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(38usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(38usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(38usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(41usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(41usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(41usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(41usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(41usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(44usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(44usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(44usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(44usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(44usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145779711u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145845247u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145976319u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(41usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(44usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(164usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(42usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(45usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(42usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(45usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(83usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(31usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(42usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(42usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(42usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(42usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(42usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(45usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(45usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(45usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(45usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(45usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        a.mul_assign_by_base(&Mersenne31Field(32896u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(42usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(45usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(20usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(35usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(40usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(43usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(46usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(85usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(35usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(40usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(43usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(46usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(166usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(20usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(20usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(72usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(166usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(35usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(35usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(36usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(36usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(39usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(40usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(40usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(43usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(43usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(43usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(43usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(45usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(45usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(46usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(46usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(46usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(46usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(46usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(43usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(46usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(23usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(4usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(5usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(41usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(47usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(50usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(23usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(5usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(41usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(47usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(50usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(36usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(23usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(23usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(23usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(49usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(41usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(41usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(41usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(41usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(41usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(47usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(47usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(47usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(47usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(47usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(50usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(50usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(50usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(50usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(50usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145779711u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145845247u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145976319u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(47usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(50usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(164usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(48usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(51usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(48usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(51usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(88usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(36usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(23usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(48usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(48usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(48usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(48usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(48usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(51usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(51usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(51usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(51usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(51usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        a.mul_assign_by_base(&Mersenne31Field(16448u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(48usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(51usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(25usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(39usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(43usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(49usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(52usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(90usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(39usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(43usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(49usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(52usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(167usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(25usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(25usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(77usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(167usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(35usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(35usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(39usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(39usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(40usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(40usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(42usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(43usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(43usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(46usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(49usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(49usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(49usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(49usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(49usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(52usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(52usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(52usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(52usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(52usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(49usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(52usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(24usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(4usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(5usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(44usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(53usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(56usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(24usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(5usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(44usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(53usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(56usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(37usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(24usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(24usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(24usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(50usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(44usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(44usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(44usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(44usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(44usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(53usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(53usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(53usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(53usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(53usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(56usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(56usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(56usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(56usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(56usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145779711u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145845247u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145976319u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(53usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(56usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(164usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(54usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(57usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(54usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(57usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(89usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(37usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(24usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(54usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(54usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(54usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(54usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(54usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(57usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(57usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(57usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(57usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(57usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(54usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(57usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(26usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(42usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(46usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(55usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(58usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(91usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(42usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(46usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(55usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(58usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(168usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(26usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(26usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(78usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(168usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(36usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(39usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(39usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(42usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(42usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(43usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(43usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(45usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(46usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(46usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(55usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(55usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(55usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(55usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(55usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(58usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(58usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(58usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(58usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(58usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(55usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(58usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(19usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(4usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(63usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147155967u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147024895u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147155967u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(43usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(69usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(30usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(30usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(30usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(30usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(63usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(63usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(63usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(63usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(63usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147221503u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146303999u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146238463u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147090431u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147024895u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147221503u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(59usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(63usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(30usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(60usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(64usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(165usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(82usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(43usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(165usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(60usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(60usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(60usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(60usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(60usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(64usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(64usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(64usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(64usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(64usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(60usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(64usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(165usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(65usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(70usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(165usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(71usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(32usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(32usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(165usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(32usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(60usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(61usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(61usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(61usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(61usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(64usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(64usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(65usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(65usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(65usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(65usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483392u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(65usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(67usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(68usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(68usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(70usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(71usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(61usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(65usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(20usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(4usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(63usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(66usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(69usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147155967u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147024895u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147155967u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(44usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(70usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(31usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(31usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(31usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(31usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(63usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(63usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(63usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(63usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(63usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(66usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(66usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(66usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(66usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(66usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(69usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(69usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(69usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(69usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(69usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147221503u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146303999u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146238463u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147090431u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147024895u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147221503u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(66usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(69usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(31usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(67usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(70usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(166usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(83usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(44usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(166usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(67usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(67usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(67usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(67usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(67usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(70usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(70usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(70usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(70usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(70usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(67usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(70usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(166usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(60usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(65usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(68usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(71usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(166usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(72usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(33usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(33usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(166usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(33usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(60usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(61usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(64usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(65usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(67usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(67usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(68usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(68usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(68usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(68usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(70usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(71usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483392u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(71usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483392u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(71usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(71usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(71usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(68usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(71usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(25usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(4usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(66usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(72usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(75usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147155967u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147024895u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147155967u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(49usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(75usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(36usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(36usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(36usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(36usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(66usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(66usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(66usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(66usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(66usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(72usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(72usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(72usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(72usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(72usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(75usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(75usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(75usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(75usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(75usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147221503u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146303999u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146238463u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147090431u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147024895u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147221503u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(72usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(75usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(36usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(73usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(76usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(167usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(88usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(49usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(167usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(73usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(73usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(73usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(73usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(73usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(76usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(76usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(76usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(76usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(76usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(73usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(76usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(167usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(64usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(68usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(74usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(77usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(167usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(77usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(38usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(38usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(167usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(38usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(60usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(61usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(61usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(64usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(65usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(67usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(68usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(70usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(70usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(71usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(74usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(74usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(74usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(74usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(74usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(77usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(77usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(77usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(77usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(77usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(74usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(77usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(26usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(4usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(69usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(78usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(81usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147155967u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147024895u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147155967u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(50usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(76usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(37usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(37usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(37usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(37usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(69usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(69usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(69usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(69usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(69usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(78usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(78usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(78usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(78usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(78usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(81usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(81usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(81usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(81usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(81usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147221503u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146303999u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146238463u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147090431u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147024895u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147221503u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(78usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(81usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(37usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(79usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(82usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(168usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(89usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(50usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(168usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(79usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(79usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(79usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(79usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(79usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(82usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(82usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(82usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(82usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(82usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(79usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(82usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(168usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(67usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(71usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(80usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(83usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(168usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(78usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(39usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(39usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(168usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(39usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(60usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(60usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(61usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(64usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(65usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(65usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(67usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(68usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(70usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(71usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(80usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(80usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(80usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(80usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(80usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(83usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(83usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(83usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(83usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(83usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(80usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(83usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(165usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(17usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(5usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(88usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147221503u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(56usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(43usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(43usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(17usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(17usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(88usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(88usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(88usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(88usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(88usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147287039u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146107391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146238463u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146369535u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146172927u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146303999u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146893823u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147024895u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(84usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(88usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(43usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(165usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(85usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(89usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(82usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(165usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(69usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(85usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(85usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(85usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(85usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(85usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(89usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(89usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(89usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(89usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(89usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(85usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(89usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(169usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(19usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(90usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(95usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(169usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(45usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(45usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(19usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(169usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(86usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(86usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(86usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(89usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(89usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(90usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(90usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(90usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(90usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(90usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(92usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(93usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(93usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(95usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(95usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(96usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(86usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(90usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(166usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(5usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(88usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(91usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(94usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147221503u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(57usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(44usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(44usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(88usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(88usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(88usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(88usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(88usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(91usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(91usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(91usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(91usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(91usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(94usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(94usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(94usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(94usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(94usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147287039u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146107391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146238463u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146369535u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146172927u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146303999u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146893823u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147024895u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(91usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(94usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(44usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(166usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(92usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(95usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(83usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(166usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(70usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(92usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(92usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(92usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(92usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(92usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(95usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(95usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(95usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(95usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(95usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(92usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(95usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(170usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(20usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(85usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(90usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(93usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(96usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(170usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(46usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(46usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(20usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(170usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(85usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(85usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(86usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(90usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(90usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(92usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(92usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(93usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(93usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(93usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(93usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(93usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(95usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(96usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(96usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(96usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483392u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(96usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(96usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483392u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(93usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(96usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(167usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(23usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(5usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(91usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(97usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(100usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147221503u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(62usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(49usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(49usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(23usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(23usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(91usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(91usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(91usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(91usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(91usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(97usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(97usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(97usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(97usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(97usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(100usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(100usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(100usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(100usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(100usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147287039u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146107391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146238463u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146369535u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146172927u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146303999u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146893823u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147024895u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(97usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(100usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(49usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(167usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(98usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(101usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(88usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(167usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(75usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(98usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(98usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(98usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(98usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(98usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(101usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(101usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(101usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(101usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(101usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(98usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(101usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(171usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(25usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(89usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(93usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(99usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(102usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(171usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(51usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(51usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(25usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(171usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(85usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(86usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(86usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(89usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(89usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(90usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(93usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(93usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(95usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(95usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(99usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(99usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(99usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(99usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(99usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(102usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(102usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(102usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(102usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(102usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(99usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(102usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(168usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(24usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(5usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(94usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(103usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(106usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147221503u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(63usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(50usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(50usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(24usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(24usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(94usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(94usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(94usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(94usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(94usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(103usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(103usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(103usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(103usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(103usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(106usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(106usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(106usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(106usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(106usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147287039u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146697215u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146107391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146238463u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146369535u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146762751u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146172927u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146303999u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146893823u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147024895u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(103usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(106usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(50usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(168usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(104usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(107usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(89usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(168usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(76usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(104usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(104usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(104usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(104usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(104usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(107usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(107usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(107usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(107usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(107usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(104usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(107usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(172usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(26usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(92usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(96usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(105usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(108usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(172usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(52usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(52usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(26usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(172usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(85usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(85usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(89usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(90usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(90usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(92usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(92usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(93usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(96usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(96usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(105usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(105usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(105usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(105usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(105usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(108usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(108usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(108usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(108usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(108usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(105usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(108usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(169usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(4usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(113usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147090431u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146893823u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(69usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(30usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(56usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(56usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(43usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(43usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(113usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(113usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(113usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(113usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(113usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146893823u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146041855u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145910783u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146369535u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145648639u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146303999u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146107391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146172927u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145976319u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147155967u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(109usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(113usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(56usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(110usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(114usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(169usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(82usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(56usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(169usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(110usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(110usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(110usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(110usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(110usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(114usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(114usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(114usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(114usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(114usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(110usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(114usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(173usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(115usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(120usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(169usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(32usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(58usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(58usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(169usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(45usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(111usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(111usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(111usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(114usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(114usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(115usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(115usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(115usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(115usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(115usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(117usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(118usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(118usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(120usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(120usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(121usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(111usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(115usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(170usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(4usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(113usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(116usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(119usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147090431u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146893823u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(70usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(31usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(57usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(57usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(44usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(44usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(113usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(113usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(113usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(113usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(113usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(116usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(116usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(116usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(116usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(116usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(119usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(119usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(119usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(119usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(119usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146893823u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146041855u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145910783u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146369535u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145648639u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146303999u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146107391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146172927u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145976319u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147155967u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(116usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(119usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(57usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(117usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(120usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(170usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(83usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(57usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(170usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(117usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(117usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(117usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(117usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(117usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(120usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(120usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(120usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(120usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(120usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(117usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(120usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(174usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(110usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(115usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(118usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(121usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(170usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(33usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(59usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(59usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(170usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(46usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(110usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(110usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(111usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(115usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(115usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(117usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(117usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(118usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(118usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(118usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(118usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(118usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(120usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(121usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483392u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(121usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483392u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(121usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(121usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(121usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(118usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(121usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(171usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(4usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(116usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(122usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(125usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147090431u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146893823u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(75usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(36usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(62usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(62usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(49usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(49usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(116usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(116usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(116usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(116usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(116usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(122usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(122usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(122usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(122usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(122usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(125usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(125usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(125usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(125usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(125usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146893823u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146041855u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145910783u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146369535u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145648639u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146303999u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146107391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146172927u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145976319u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147155967u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(122usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(125usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(62usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(123usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(126usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(171usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(88usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(62usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(171usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(123usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(123usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(123usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(123usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(123usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(126usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(126usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(126usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(126usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(126usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(123usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(126usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(175usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(114usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(118usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(124usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(127usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(171usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(38usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(64usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(64usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(171usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(51usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(110usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(111usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(111usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(114usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(114usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(115usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(118usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(118usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(120usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(120usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(124usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(124usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(124usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(124usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(124usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(127usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(127usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(127usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(127usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(127usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(124usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(127usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(172usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(4usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(119usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(128usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(131usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147090431u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146893823u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(76usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(37usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(63usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(63usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(50usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(50usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(119usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(119usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(119usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(119usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(119usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(128usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(128usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(128usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(128usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(128usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(131usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(131usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(131usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(131usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(131usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146893823u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146041855u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145910783u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146369535u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145648639u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146303999u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146107391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146172927u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145976319u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147155967u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(128usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(131usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(63usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(129usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(132usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(witness.get_unchecked(172usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(89usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(63usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(172usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(129usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(129usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(129usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(129usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(129usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(132usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(132usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(132usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(132usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(132usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(129usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(132usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(176usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(117usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(121usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(130usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(133usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(172usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(39usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(65usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(65usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(172usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(52usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(110usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(110usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(114usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(115usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(115usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(117usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(117usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(118usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(121usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(121usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(130usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(130usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(130usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(130usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(130usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(133usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(133usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(133usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(133usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(133usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(130usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(133usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(173usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(43usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(56usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(69usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(69usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(30usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(17usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(138usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(138usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(138usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(138usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(138usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147221503u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146107391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145714175u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146041855u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(134usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(138usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(69usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(169usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(82usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(82usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(169usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(56usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(135usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(135usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(135usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(135usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(135usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(139usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(139usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(139usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(139usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(139usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(135usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(139usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(84usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(45usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(58usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(71usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(71usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(32usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(19usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(135usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(135usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(136usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(136usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(136usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(140usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(140usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(140usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483392u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(140usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483392u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(140usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(142usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(145usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(145usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(146usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(136usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(140usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(174usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(44usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(57usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(70usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(70usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(31usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(138usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(138usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(138usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(138usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(138usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(141usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(141usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(141usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(141usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(141usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(144usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(144usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(144usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(144usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(144usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147221503u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146107391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145714175u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146041855u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(141usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(144usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(70usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(170usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(83usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(83usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(170usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(57usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(142usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(142usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(142usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(142usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(142usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(145usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(145usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(145usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(145usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(145usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(142usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(145usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(85usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(46usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(59usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(72usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(72usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(33usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(20usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(135usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(135usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(136usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(139usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(139usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(140usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(140usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(143usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(143usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(143usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(145usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(146usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(146usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(146usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(146usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(146usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(143usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(146usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(175usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(49usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(62usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(75usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(75usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(36usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(23usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(141usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(141usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(141usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(141usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(141usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(147usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(147usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(147usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(147usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(147usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(150usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(150usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(150usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(150usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(150usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147221503u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146107391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145714175u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146041855u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(147usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(150usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(75usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(171usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(88usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(88usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(171usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(62usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(148usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(148usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(148usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(148usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(148usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(151usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(151usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(151usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(151usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(151usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(148usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(151usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(90usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(51usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(64usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(77usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(77usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(38usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(25usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(135usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(139usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(139usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(140usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(142usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(142usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(143usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(143usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(146usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(146usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(149usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(149usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(149usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(149usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(149usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(152usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(152usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(152usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(152usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(152usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(149usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(152usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(witness.get_unchecked(176usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(50usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(63usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(76usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(76usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(37usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(24usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(144usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(144usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(144usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(144usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(144usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(153usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(153usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(153usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(153usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(153usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(156usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(156usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(156usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(156usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(156usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147221503u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(159usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147352575u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146500607u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146828287u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(160usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146435071u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146631679u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146107391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(161usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2145714175u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146959359u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(162usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146041855u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(163usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2146566143u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(153usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(156usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(76usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(witness.get_unchecked(172usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(89usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(89usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(172usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(63usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(154usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(154usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(154usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(154usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(154usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(157usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(157usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(157usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(157usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(157usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(154usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(157usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(91usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(52usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(65usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(78usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(78usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(39usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(26usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(136usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(136usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(139usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(142usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(142usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(143usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(145usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(145usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(146usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(146usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(155usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(155usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(155usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(155usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(155usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(158usize));
                        let b = *(witness.get_unchecked(159usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(158usize));
                        let b = *(witness.get_unchecked(160usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(158usize));
                        let b = *(witness.get_unchecked(161usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(158usize));
                        let b = *(witness.get_unchecked(162usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(158usize));
                        let b = *(witness.get_unchecked(163usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483391u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(155usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(158usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
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
                        let b = *(memory.get_unchecked(30usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(32usize));
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
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(31usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(33usize));
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
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(36usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(38usize));
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
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(37usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(39usize));
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
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(43usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(45usize));
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
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(44usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(46usize));
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
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(49usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(51usize));
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
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(50usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(52usize));
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
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(56usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(58usize));
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
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(57usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(59usize));
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
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(62usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(64usize));
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
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(63usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(65usize));
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
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(69usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(71usize));
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
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(70usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(72usize));
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
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(75usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(77usize));
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
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(76usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(78usize));
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
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(30usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(32usize));
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
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(31usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(33usize));
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
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(36usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(38usize));
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
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(37usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(39usize));
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
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(56usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(58usize));
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
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(57usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(59usize));
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
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(62usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(64usize));
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
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(63usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(65usize));
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
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(69usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(71usize));
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
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(70usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(72usize));
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
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(75usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(77usize));
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
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(76usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        let b = *(memory.get_unchecked(78usize));
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
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(17usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(5usize));
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
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(5usize));
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
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(23usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(25usize));
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
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(24usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(26usize));
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
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(43usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(45usize));
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
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(44usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(46usize));
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
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(49usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(51usize));
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
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(50usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(52usize));
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
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(82usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(84usize));
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
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(83usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(85usize));
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
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(88usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(90usize));
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
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(89usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        let b = *(memory.get_unchecked(91usize));
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
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(82usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(84usize));
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
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(83usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(85usize));
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
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(88usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(90usize));
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
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(89usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        let b = *(memory.get_unchecked(91usize));
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
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(82usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(84usize));
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
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(83usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(85usize));
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
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(88usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(90usize));
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
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(89usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        let b = *(memory.get_unchecked(91usize));
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
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(17usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(84usize));
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
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(85usize));
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
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(23usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(90usize));
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
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(24usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(91usize));
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
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(43usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(45usize));
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
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(44usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(46usize));
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
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(49usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(51usize));
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
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(50usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(52usize));
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
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(56usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(58usize));
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
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(57usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(59usize));
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
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(62usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(64usize));
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
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(63usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(memory.get_unchecked(65usize));
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
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(56usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(58usize));
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
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(57usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(59usize));
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
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(62usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(64usize));
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
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(63usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(65usize));
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
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(69usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(71usize));
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
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(70usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(72usize));
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
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(75usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(77usize));
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
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(76usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(78usize));
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
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(82usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(84usize));
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
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(83usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(85usize));
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
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(88usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(90usize));
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
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(89usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(memory.get_unchecked(91usize));
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
                        let a = *(memory.get_unchecked(7usize));
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
                        let a = *(memory.get_unchecked(9usize));
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
                        let a = *(witness.get_unchecked(4usize));
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        a.mul_assign_by_base(&Mersenne31Field(2u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        a.mul_assign_by_base(&Mersenne31Field(3u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        a.mul_assign_by_base(&Mersenne31Field(5u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        a.mul_assign_by_base(&Mersenne31Field(6u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        a.mul_assign_by_base(&Mersenne31Field(8u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        a.mul_assign_by_base(&Mersenne31Field(16u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(13usize));
                        a.mul_assign_by_base(&Mersenne31Field(24u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        a.mul_assign_by_base(&Mersenne31Field(32u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(15usize));
                        a.mul_assign_by_base(&Mersenne31Field(64u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(16usize));
                        a.mul_assign_by_base(&Mersenne31Field(128u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        a.mul_assign_by_base(&Mersenne31Field(256u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        a.mul_assign_by_base(&Mersenne31Field(512u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(19usize));
                        a.mul_assign_by_base(&Mersenne31Field(1024u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(6usize));
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
                        let a = *(witness.get_unchecked(7usize));
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(159usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(160usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(161usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(162usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(163usize));
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
                        a.mul_assign_by_base(&Mersenne31Field(59u32));
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        a.mul_assign_by_base(&Mersenne31Field(61u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        a.mul_assign_by_base(&Mersenne31Field(61u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        a.mul_assign_by_base(&Mersenne31Field(61u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        a.mul_assign_by_base(&Mersenne31Field(60u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        a.mul_assign_by_base(&Mersenne31Field(60u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(37usize));
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
                        let a = *(witness.get_unchecked(7usize));
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(159usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(160usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(161usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(162usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(163usize));
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
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        a.mul_assign_by_base(&Mersenne31Field(61u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        a.mul_assign_by_base(&Mersenne31Field(61u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        a.mul_assign_by_base(&Mersenne31Field(60u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
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
                        let a = *(witness.get_unchecked(7usize));
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(159usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(160usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(161usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(162usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(163usize));
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
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        a.mul_assign_by_base(&Mersenne31Field(61u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        a.mul_assign_by_base(&Mersenne31Field(61u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        a.mul_assign_by_base(&Mersenne31Field(60u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(87usize));
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
                        let a = *(witness.get_unchecked(7usize));
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(159usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(160usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(161usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(162usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(163usize));
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
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        a.mul_assign_by_base(&Mersenne31Field(61u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        a.mul_assign_by_base(&Mersenne31Field(61u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        a.mul_assign_by_base(&Mersenne31Field(60u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(112usize));
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
                        let a = *(witness.get_unchecked(7usize));
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(159usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(160usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(161usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(162usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(163usize));
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
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(4usize));
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(5usize));
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(6usize));
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(7usize));
                        a.mul_assign_by_base(&Mersenne31Field(61u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(137usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            let predicate = *(memory.get_unchecked(0usize));
            let mut predicate_minus_one = predicate;
            predicate_minus_one.sub_assign_base(&Mersenne31Field::ONE);
            let mem_abi_offset = *(memory.get_unchecked(1usize));
            let write_timestamp_low = *(memory.get_unchecked(2usize));
            let write_timestamp_high = *(memory.get_unchecked(3usize));
            {
                accumulated_contribution.mul_assign(&quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let mut individual_term = predicate;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let mut individual_term = mem_abi_offset;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let mut individual_term = write_timestamp_low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let mut individual_term = *(memory.get_unchecked(3usize));
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(4usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(5usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(6usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(7usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(8usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(9usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(10usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(11usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(12usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(13usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(14usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(15usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(17usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(18usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(19usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(20usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(21usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(22usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(23usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(24usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(25usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(26usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(27usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(28usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(30usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(31usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(32usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(33usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(34usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(35usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(36usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(37usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(38usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(39usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(40usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(41usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(43usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(44usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(45usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(46usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(47usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(48usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(49usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(50usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(51usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(52usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(53usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(54usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(56usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(57usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(58usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(59usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(60usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(61usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(62usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(63usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(64usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(65usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(66usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(67usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(69usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(70usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(71usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(72usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(73usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(74usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(75usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(76usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(77usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(78usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(79usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(80usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(82usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(83usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(84usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(85usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(86usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(87usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(88usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(89usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let low = *(memory.get_unchecked(90usize));
                        let mut individual_term = low;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let high = *(memory.get_unchecked(91usize));
                        let mut individual_term = high;
                        individual_term.mul_assign(&predicate_minus_one);
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
                        let mut a = *(memory.get_unchecked(12usize));
                        a.mul_assign_by_base(&Mersenne31Field(8388608u32));
                        a
                    };
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(memory.get_unchecked(12usize));
                        a.mul_assign_by_base(&Mersenne31Field(8388608u32));
                        a
                    };
                    individual_term
                };
                individual_term
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
                        let acc_value = *(stage_2.get_unchecked(15usize));
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
                        let mut a = *(memory.get_unchecked(2usize));
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(20usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(4usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(memory.get_unchecked(0usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(3usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(20usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(5usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
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
                        let acc_value = *(stage_2.get_unchecked(16usize));
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
                        let mut a = *(memory.get_unchecked(2usize));
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(21usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(10usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(memory.get_unchecked(0usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(3usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(21usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(11usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
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
                        let acc_value = *(stage_2.get_unchecked(17usize));
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
                        let mut a = *(memory.get_unchecked(2usize));
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(22usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(14usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(memory.get_unchecked(0usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(3usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(22usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(15usize));
                        individual_term.add_assign(&a);
                    }
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
                        let acc_value = *(stage_2.get_unchecked(18usize));
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
                        let mut a = *(memory.get_unchecked(2usize));
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(23usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(21usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(memory.get_unchecked(0usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(3usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(23usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(22usize));
                        individual_term.add_assign(&a);
                    }
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
                        let acc_value = *(stage_2.get_unchecked(19usize));
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
                        let mut a = *(memory.get_unchecked(2usize));
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(24usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(27usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(memory.get_unchecked(0usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(3usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(24usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(28usize));
                        individual_term.add_assign(&a);
                    }
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
                        let acc_value = *(stage_2.get_unchecked(20usize));
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
                        let mut a = *(memory.get_unchecked(2usize));
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(25usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(34usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(memory.get_unchecked(0usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(3usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(25usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(35usize));
                        individual_term.add_assign(&a);
                    }
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
                        let acc_value = *(stage_2.get_unchecked(21usize));
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
                        let mut a = *(memory.get_unchecked(2usize));
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(26usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(40usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(memory.get_unchecked(0usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(3usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(26usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(41usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let c = *(stage_2.get_unchecked(7usize));
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
                        let acc_value = *(stage_2.get_unchecked(22usize));
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
                        let mut a = *(memory.get_unchecked(2usize));
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(27usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(47usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(memory.get_unchecked(0usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(3usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(27usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(48usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let c = *(stage_2.get_unchecked(8usize));
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
                        let acc_value = *(stage_2.get_unchecked(23usize));
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
                        let mut a = *(memory.get_unchecked(2usize));
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(28usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(53usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(memory.get_unchecked(0usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(3usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(28usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(54usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let c = *(stage_2.get_unchecked(9usize));
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
                        let acc_value = *(stage_2.get_unchecked(24usize));
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
                        let mut a = *(memory.get_unchecked(2usize));
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(29usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(60usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(memory.get_unchecked(0usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(3usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(29usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(61usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let c = *(stage_2.get_unchecked(10usize));
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
                        let acc_value = *(stage_2.get_unchecked(25usize));
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
                        let mut a = *(memory.get_unchecked(2usize));
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(30usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(66usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(memory.get_unchecked(0usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(3usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(30usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(67usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let c = *(stage_2.get_unchecked(11usize));
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
                        let acc_value = *(stage_2.get_unchecked(26usize));
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
                        let mut a = *(memory.get_unchecked(2usize));
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(31usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(73usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(memory.get_unchecked(0usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(3usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(31usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(74usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let c = *(stage_2.get_unchecked(12usize));
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
                        let acc_value = *(stage_2.get_unchecked(27usize));
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
                        let mut a = *(memory.get_unchecked(2usize));
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(32usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(79usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(memory.get_unchecked(0usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(3usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(32usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(80usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let c = *(stage_2.get_unchecked(13usize));
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
                        let acc_value = *(stage_2.get_unchecked(28usize));
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
                        let mut a = *(memory.get_unchecked(2usize));
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(33usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(86usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let b = {
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(memory.get_unchecked(0usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(3usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(33usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(87usize));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            let c = *(stage_2.get_unchecked(14usize));
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
                        let acc_value = *(stage_2.get_unchecked(29usize));
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
                    let src0 = {
                        let individual_term = {
                            let mut individual_term = {
                                let mut a = *(memory.get_unchecked(0usize));
                                a.mul_assign_by_base(&Mersenne31Field(2048u32));
                                a
                            };
                            {
                                let a = *(memory.get_unchecked(6usize));
                                individual_term.add_assign(&a);
                            }
                            individual_term
                        };
                        individual_term
                    };
                    let src1 = {
                        let individual_term = {
                            let mut individual_term = {
                                let a = *(memory.get_unchecked(16usize));
                                a
                            };
                            individual_term
                        };
                        individual_term
                    };
                    let src2 = {
                        let individual_term = {
                            let mut individual_term = {
                                let a = *(memory.get_unchecked(29usize));
                                a
                            };
                            individual_term
                        };
                        individual_term
                    };
                    let mut denom = lookup_argument_linearization_challenges[2];
                    let table_id = Mersenne31Field(56u32);
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(30usize)));
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
                        let individual_term = {
                            let mut individual_term = {
                                let mut a = *(memory.get_unchecked(0usize));
                                a.mul_assign_by_base(&Mersenne31Field(2048u32));
                                a
                            };
                            {
                                let a = *(memory.get_unchecked(6usize));
                                individual_term.add_assign(&a);
                            }
                            individual_term
                        };
                        individual_term
                    };
                    let src1 = {
                        let individual_term = {
                            let mut individual_term = {
                                let a = *(memory.get_unchecked(42usize));
                                a
                            };
                            individual_term
                        };
                        individual_term
                    };
                    let src2 = {
                        let individual_term = {
                            let mut individual_term = {
                                let a = *(memory.get_unchecked(55usize));
                                a
                            };
                            individual_term
                        };
                        individual_term
                    };
                    let mut denom = lookup_argument_linearization_challenges[2];
                    let table_id = Mersenne31Field(57u32);
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(31usize)));
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
                        let individual_term = {
                            let mut individual_term = {
                                let mut a = *(memory.get_unchecked(0usize));
                                a.mul_assign_by_base(&Mersenne31Field(2048u32));
                                a
                            };
                            {
                                let a = *(memory.get_unchecked(6usize));
                                individual_term.add_assign(&a);
                            }
                            individual_term
                        };
                        individual_term
                    };
                    let src1 = {
                        let individual_term = {
                            let mut individual_term = {
                                let a = *(memory.get_unchecked(68usize));
                                a
                            };
                            individual_term
                        };
                        individual_term
                    };
                    let src2 = {
                        let individual_term = {
                            let mut individual_term = {
                                let a = *(memory.get_unchecked(81usize));
                                a
                            };
                            individual_term
                        };
                        individual_term
                    };
                    let mut denom = lookup_argument_linearization_challenges[2];
                    let table_id = Mersenne31Field(58u32);
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(32usize)));
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
                        let value = *(witness.get_unchecked(34usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(35usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(36usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(37usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(33usize)));
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
                        let value = *(witness.get_unchecked(38usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(39usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(40usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(37usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(34usize)));
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
                        let value = *(witness.get_unchecked(41usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(42usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(43usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(37usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(35usize)));
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
                        let value = *(witness.get_unchecked(44usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(45usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(46usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(37usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(36usize)));
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
                        let value = *(witness.get_unchecked(47usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(48usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(49usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(37usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(37usize)));
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
                        let value = *(witness.get_unchecked(50usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(51usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(52usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(37usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(38usize)));
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
                        let value = *(witness.get_unchecked(53usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(54usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(55usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(37usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(39usize)));
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
                        let value = *(witness.get_unchecked(56usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(57usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(58usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(37usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(40usize)));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(41usize)));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(42usize)));
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
                        let value = *(witness.get_unchecked(66usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(67usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(68usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(43usize)));
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
                        let value = *(witness.get_unchecked(69usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(70usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(71usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(44usize)));
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
                        let value = *(witness.get_unchecked(72usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(73usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(74usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(45usize)));
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
                        let value = *(witness.get_unchecked(75usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(76usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(77usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(46usize)));
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
                        let value = *(witness.get_unchecked(78usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(79usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(80usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(47usize)));
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
                        let value = *(witness.get_unchecked(81usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(82usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(83usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(48usize)));
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
                        let value = *(witness.get_unchecked(84usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(85usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(86usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(87usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(49usize)));
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
                        let value = *(witness.get_unchecked(88usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(89usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(90usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(87usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(50usize)));
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
                        let value = *(witness.get_unchecked(91usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(92usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(93usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(87usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(51usize)));
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
                        let value = *(witness.get_unchecked(94usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(95usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(96usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(87usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(52usize)));
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
                        let value = *(witness.get_unchecked(97usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(98usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(99usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(87usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(53usize)));
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
                        let value = *(witness.get_unchecked(100usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(101usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(102usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(87usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(54usize)));
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
                        let value = *(witness.get_unchecked(103usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(104usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(105usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(87usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(55usize)));
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
                        let value = *(witness.get_unchecked(106usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(107usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(108usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(87usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(56usize)));
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
                        let value = *(witness.get_unchecked(109usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(110usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(111usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(112usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(57usize)));
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
                        let value = *(witness.get_unchecked(113usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(114usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(115usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(112usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(58usize)));
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
                        let value = *(witness.get_unchecked(116usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(117usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(118usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(112usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(59usize)));
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
                        let value = *(witness.get_unchecked(119usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(120usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(121usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(112usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(60usize)));
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
                        let value = *(witness.get_unchecked(122usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(123usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(124usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(112usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(61usize)));
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
                        let value = *(witness.get_unchecked(125usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(126usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(127usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(112usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(62usize)));
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
                        let value = *(witness.get_unchecked(128usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(129usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(130usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(112usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(63usize)));
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
                        let value = *(witness.get_unchecked(131usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(132usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(133usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(112usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(64usize)));
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
                        let value = *(witness.get_unchecked(134usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(135usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(136usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(137usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(65usize)));
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
                        let value = *(witness.get_unchecked(138usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(139usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(140usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(137usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(66usize)));
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
                        let value = *(witness.get_unchecked(141usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(142usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(143usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(137usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(67usize)));
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
                        let value = *(witness.get_unchecked(144usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(145usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(146usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(137usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(68usize)));
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
                        let value = *(witness.get_unchecked(147usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(148usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(149usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(137usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(69usize)));
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
                        let value = *(witness.get_unchecked(150usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(151usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(152usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(137usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(70usize)));
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
                        let value = *(witness.get_unchecked(153usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(154usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(155usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(137usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(71usize)));
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
                        let value = *(witness.get_unchecked(156usize));
                        value
                    };
                    let src1 = {
                        let value = *(witness.get_unchecked(157usize));
                        value
                    };
                    let src2 = {
                        let value = *(witness.get_unchecked(158usize));
                        value
                    };
                    let table_id = *(witness.get_unchecked(137usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(72usize)));
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
                    let m = *(witness.get_unchecked(0usize));
                    let t = *(setup.get_unchecked(0usize));
                    let mut denom = lookup_argument_gamma;
                    denom.add_assign(&t);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(73usize)));
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
                    let m = *(witness.get_unchecked(1usize));
                    let t = *(setup.get_unchecked(1usize));
                    let mut denom = lookup_argument_gamma;
                    denom.add_assign(&t);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(74usize)));
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
                    let m = *(witness.get_unchecked(2usize));
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
                    individual_term.mul_assign(&*(stage_2.get_unchecked(75usize)));
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
                    let m = *(memory.get_unchecked(0usize));
                    let mut denom = delegation_argument_linearization_challenges[2];
                    let timestamp_high = *(memory.get_unchecked(3usize));
                    denom.mul_assign(&timestamp_high);
                    let timestamp_low = *(memory.get_unchecked(2usize));
                    let mut t = delegation_argument_linearization_challenges[1];
                    t.mul_assign(&timestamp_low);
                    denom.add_assign(&t);
                    let mem_abi_offset = *(memory.get_unchecked(1usize));
                    let mut t = delegation_argument_linearization_challenges[0];
                    t.mul_assign(&mem_abi_offset);
                    denom.add_assign(&t);
                    let t = delegation_type;
                    denom.add_assign_base(&t);
                    denom.add_assign(&delegation_argument_gamma);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(76usize)));
                    individual_term.sub_assign(&m);
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
        }
        {
            let predicate = *(memory.get_unchecked(0usize));
            let address_high = *(memory.get_unchecked(1usize));
            let write_timestamp_low = *(memory.get_unchecked(2usize));
            let write_timestamp_high = *(memory.get_unchecked(3usize));
            let mut delegation_address_high_common_contribution =
                memory_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
            delegation_address_high_common_contribution.mul_assign(&address_high);
            let mut t = memory_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
            t.mul_assign(&write_timestamp_low);
            let mut write_timestamp_contribution = t;
            let mut t = memory_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
            t.mul_assign(&write_timestamp_high);
            write_timestamp_contribution.add_assign(&t);
            {
                accumulated_contribution.mul_assign(&quotient_alpha);
                let contribution = {
                    let individual_term = {
                        let mut address_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                        address_contribution.mul_assign_by_base(&Mersenne31Field(10u32));
                        address_contribution.add_assign_base(&Mersenne31Field::ONE);
                        let read_value_low = *(memory.get_unchecked(6usize));
                        let mut read_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        read_value_contribution.mul_assign(&read_value_low);
                        let read_value_high = *(memory.get_unchecked(7usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&read_value_high);
                        read_value_contribution.add_assign(&t);
                        let read_timestamp_low = *(memory.get_unchecked(4usize));
                        let mut read_timestamp_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                        read_timestamp_contribution.mul_assign(&read_timestamp_low);
                        let read_timestamp_high = *(memory.get_unchecked(5usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                        t.mul_assign(&read_timestamp_high);
                        read_timestamp_contribution.add_assign(&t);
                        let mut numerator = memory_argument_gamma;
                        numerator.add_assign(&address_contribution);
                        let previous = Mersenne31Quartic::ONE;
                        let write_value_low = *(memory.get_unchecked(8usize));
                        let mut write_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        write_value_contribution.mul_assign(&write_value_low);
                        let write_value_high = *(memory.get_unchecked(9usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&write_value_high);
                        write_value_contribution.add_assign(&t);
                        let mut denom = numerator;
                        numerator.add_assign(&write_value_contribution);
                        denom.add_assign(&read_value_contribution);
                        numerator.add_assign(&write_timestamp_contribution);
                        denom.add_assign(&read_timestamp_contribution);
                        let mut individual_term = *(stage_2.get_unchecked(77usize));
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
                        let mut address_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                        address_contribution.mul_assign_by_base(&Mersenne31Field(11u32));
                        address_contribution.add_assign_base(&Mersenne31Field::ONE);
                        let read_value_low = *(memory.get_unchecked(12usize));
                        let mut read_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        read_value_contribution.mul_assign(&read_value_low);
                        let read_value_high = *(memory.get_unchecked(13usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&read_value_high);
                        read_value_contribution.add_assign(&t);
                        let read_timestamp_low = *(memory.get_unchecked(10usize));
                        let mut read_timestamp_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                        read_timestamp_contribution.mul_assign(&read_timestamp_low);
                        let read_timestamp_high = *(memory.get_unchecked(11usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                        t.mul_assign(&read_timestamp_high);
                        read_timestamp_contribution.add_assign(&t);
                        let mut numerator = memory_argument_gamma;
                        numerator.add_assign(&address_contribution);
                        let previous = *(stage_2.get_unchecked(77usize));
                        numerator.add_assign(&read_value_contribution);
                        let mut denom = numerator;
                        numerator.add_assign(&write_timestamp_contribution);
                        denom.add_assign(&read_timestamp_contribution);
                        let mut individual_term = *(stage_2.get_unchecked(78usize));
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
                        let mut address_low = *(memory.get_unchecked(12usize));
                        address_low.add_assign_base(&Mersenne31Field(0u32));
                        let mut variable_offset = *(memory.get_unchecked(16usize));
                        variable_offset.mul_assign_by_base(&Mersenne31Field(8u32));
                        address_low.add_assign(&variable_offset);
                        let mut address_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                        address_contribution.mul_assign(&address_low);
                        let address_high = *(memory.get_unchecked(13usize));
                        let mut address_high_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                        address_high_contribution.mul_assign(&address_high);
                        address_contribution.add_assign(&address_high_contribution);
                        let read_value_low = *(memory.get_unchecked(17usize));
                        let mut read_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        read_value_contribution.mul_assign(&read_value_low);
                        let read_value_high = *(memory.get_unchecked(18usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&read_value_high);
                        read_value_contribution.add_assign(&t);
                        let read_timestamp_low = *(memory.get_unchecked(14usize));
                        let mut read_timestamp_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                        read_timestamp_contribution.mul_assign(&read_timestamp_low);
                        let read_timestamp_high = *(memory.get_unchecked(15usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                        t.mul_assign(&read_timestamp_high);
                        read_timestamp_contribution.add_assign(&t);
                        let mut numerator = memory_argument_gamma;
                        numerator.add_assign(&address_contribution);
                        let previous = *(stage_2.get_unchecked(78usize));
                        let write_value_low = *(memory.get_unchecked(19usize));
                        let mut write_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        write_value_contribution.mul_assign(&write_value_low);
                        let write_value_high = *(memory.get_unchecked(20usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&write_value_high);
                        write_value_contribution.add_assign(&t);
                        let mut denom = numerator;
                        numerator.add_assign(&write_value_contribution);
                        denom.add_assign(&read_value_contribution);
                        numerator.add_assign(&write_timestamp_contribution);
                        denom.add_assign(&read_timestamp_contribution);
                        let mut individual_term = *(stage_2.get_unchecked(79usize));
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
                        let mut address_low = *(memory.get_unchecked(12usize));
                        address_low.add_assign_base(&Mersenne31Field(4u32));
                        let mut variable_offset = *(memory.get_unchecked(16usize));
                        variable_offset.mul_assign_by_base(&Mersenne31Field(8u32));
                        address_low.add_assign(&variable_offset);
                        let mut address_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                        address_contribution.mul_assign(&address_low);
                        let address_high = *(memory.get_unchecked(13usize));
                        let mut address_high_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                        address_high_contribution.mul_assign(&address_high);
                        address_contribution.add_assign(&address_high_contribution);
                        let read_value_low = *(memory.get_unchecked(23usize));
                        let mut read_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        read_value_contribution.mul_assign(&read_value_low);
                        let read_value_high = *(memory.get_unchecked(24usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&read_value_high);
                        read_value_contribution.add_assign(&t);
                        let read_timestamp_low = *(memory.get_unchecked(21usize));
                        let mut read_timestamp_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                        read_timestamp_contribution.mul_assign(&read_timestamp_low);
                        let read_timestamp_high = *(memory.get_unchecked(22usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                        t.mul_assign(&read_timestamp_high);
                        read_timestamp_contribution.add_assign(&t);
                        let mut numerator = memory_argument_gamma;
                        numerator.add_assign(&address_contribution);
                        let previous = *(stage_2.get_unchecked(79usize));
                        let write_value_low = *(memory.get_unchecked(25usize));
                        let mut write_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        write_value_contribution.mul_assign(&write_value_low);
                        let write_value_high = *(memory.get_unchecked(26usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&write_value_high);
                        write_value_contribution.add_assign(&t);
                        let mut denom = numerator;
                        numerator.add_assign(&write_value_contribution);
                        denom.add_assign(&read_value_contribution);
                        numerator.add_assign(&write_timestamp_contribution);
                        denom.add_assign(&read_timestamp_contribution);
                        let mut individual_term = *(stage_2.get_unchecked(80usize));
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
                        let mut address_low = *(memory.get_unchecked(12usize));
                        address_low.add_assign_base(&Mersenne31Field(0u32));
                        let mut variable_offset = *(memory.get_unchecked(29usize));
                        variable_offset.mul_assign_by_base(&Mersenne31Field(8u32));
                        address_low.add_assign(&variable_offset);
                        let mut address_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                        address_contribution.mul_assign(&address_low);
                        let address_high = *(memory.get_unchecked(13usize));
                        let mut address_high_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                        address_high_contribution.mul_assign(&address_high);
                        address_contribution.add_assign(&address_high_contribution);
                        let read_value_low = *(memory.get_unchecked(30usize));
                        let mut read_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        read_value_contribution.mul_assign(&read_value_low);
                        let read_value_high = *(memory.get_unchecked(31usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&read_value_high);
                        read_value_contribution.add_assign(&t);
                        let read_timestamp_low = *(memory.get_unchecked(27usize));
                        let mut read_timestamp_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                        read_timestamp_contribution.mul_assign(&read_timestamp_low);
                        let read_timestamp_high = *(memory.get_unchecked(28usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                        t.mul_assign(&read_timestamp_high);
                        read_timestamp_contribution.add_assign(&t);
                        let mut numerator = memory_argument_gamma;
                        numerator.add_assign(&address_contribution);
                        let previous = *(stage_2.get_unchecked(80usize));
                        let write_value_low = *(memory.get_unchecked(32usize));
                        let mut write_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        write_value_contribution.mul_assign(&write_value_low);
                        let write_value_high = *(memory.get_unchecked(33usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&write_value_high);
                        write_value_contribution.add_assign(&t);
                        let mut denom = numerator;
                        numerator.add_assign(&write_value_contribution);
                        denom.add_assign(&read_value_contribution);
                        numerator.add_assign(&write_timestamp_contribution);
                        denom.add_assign(&read_timestamp_contribution);
                        let mut individual_term = *(stage_2.get_unchecked(81usize));
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
                        let mut address_low = *(memory.get_unchecked(12usize));
                        address_low.add_assign_base(&Mersenne31Field(4u32));
                        let mut variable_offset = *(memory.get_unchecked(29usize));
                        variable_offset.mul_assign_by_base(&Mersenne31Field(8u32));
                        address_low.add_assign(&variable_offset);
                        let mut address_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                        address_contribution.mul_assign(&address_low);
                        let address_high = *(memory.get_unchecked(13usize));
                        let mut address_high_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                        address_high_contribution.mul_assign(&address_high);
                        address_contribution.add_assign(&address_high_contribution);
                        let read_value_low = *(memory.get_unchecked(36usize));
                        let mut read_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        read_value_contribution.mul_assign(&read_value_low);
                        let read_value_high = *(memory.get_unchecked(37usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&read_value_high);
                        read_value_contribution.add_assign(&t);
                        let read_timestamp_low = *(memory.get_unchecked(34usize));
                        let mut read_timestamp_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                        read_timestamp_contribution.mul_assign(&read_timestamp_low);
                        let read_timestamp_high = *(memory.get_unchecked(35usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                        t.mul_assign(&read_timestamp_high);
                        read_timestamp_contribution.add_assign(&t);
                        let mut numerator = memory_argument_gamma;
                        numerator.add_assign(&address_contribution);
                        let previous = *(stage_2.get_unchecked(81usize));
                        let write_value_low = *(memory.get_unchecked(38usize));
                        let mut write_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        write_value_contribution.mul_assign(&write_value_low);
                        let write_value_high = *(memory.get_unchecked(39usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&write_value_high);
                        write_value_contribution.add_assign(&t);
                        let mut denom = numerator;
                        numerator.add_assign(&write_value_contribution);
                        denom.add_assign(&read_value_contribution);
                        numerator.add_assign(&write_timestamp_contribution);
                        denom.add_assign(&read_timestamp_contribution);
                        let mut individual_term = *(stage_2.get_unchecked(82usize));
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
                        let mut address_low = *(memory.get_unchecked(12usize));
                        address_low.add_assign_base(&Mersenne31Field(0u32));
                        let mut variable_offset = *(memory.get_unchecked(42usize));
                        variable_offset.mul_assign_by_base(&Mersenne31Field(8u32));
                        address_low.add_assign(&variable_offset);
                        let mut address_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                        address_contribution.mul_assign(&address_low);
                        let address_high = *(memory.get_unchecked(13usize));
                        let mut address_high_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                        address_high_contribution.mul_assign(&address_high);
                        address_contribution.add_assign(&address_high_contribution);
                        let read_value_low = *(memory.get_unchecked(43usize));
                        let mut read_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        read_value_contribution.mul_assign(&read_value_low);
                        let read_value_high = *(memory.get_unchecked(44usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&read_value_high);
                        read_value_contribution.add_assign(&t);
                        let read_timestamp_low = *(memory.get_unchecked(40usize));
                        let mut read_timestamp_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                        read_timestamp_contribution.mul_assign(&read_timestamp_low);
                        let read_timestamp_high = *(memory.get_unchecked(41usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                        t.mul_assign(&read_timestamp_high);
                        read_timestamp_contribution.add_assign(&t);
                        let mut numerator = memory_argument_gamma;
                        numerator.add_assign(&address_contribution);
                        let previous = *(stage_2.get_unchecked(82usize));
                        let write_value_low = *(memory.get_unchecked(45usize));
                        let mut write_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        write_value_contribution.mul_assign(&write_value_low);
                        let write_value_high = *(memory.get_unchecked(46usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&write_value_high);
                        write_value_contribution.add_assign(&t);
                        let mut denom = numerator;
                        numerator.add_assign(&write_value_contribution);
                        denom.add_assign(&read_value_contribution);
                        numerator.add_assign(&write_timestamp_contribution);
                        denom.add_assign(&read_timestamp_contribution);
                        let mut individual_term = *(stage_2.get_unchecked(83usize));
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
                        let mut address_low = *(memory.get_unchecked(12usize));
                        address_low.add_assign_base(&Mersenne31Field(4u32));
                        let mut variable_offset = *(memory.get_unchecked(42usize));
                        variable_offset.mul_assign_by_base(&Mersenne31Field(8u32));
                        address_low.add_assign(&variable_offset);
                        let mut address_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                        address_contribution.mul_assign(&address_low);
                        let address_high = *(memory.get_unchecked(13usize));
                        let mut address_high_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                        address_high_contribution.mul_assign(&address_high);
                        address_contribution.add_assign(&address_high_contribution);
                        let read_value_low = *(memory.get_unchecked(49usize));
                        let mut read_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        read_value_contribution.mul_assign(&read_value_low);
                        let read_value_high = *(memory.get_unchecked(50usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&read_value_high);
                        read_value_contribution.add_assign(&t);
                        let read_timestamp_low = *(memory.get_unchecked(47usize));
                        let mut read_timestamp_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                        read_timestamp_contribution.mul_assign(&read_timestamp_low);
                        let read_timestamp_high = *(memory.get_unchecked(48usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                        t.mul_assign(&read_timestamp_high);
                        read_timestamp_contribution.add_assign(&t);
                        let mut numerator = memory_argument_gamma;
                        numerator.add_assign(&address_contribution);
                        let previous = *(stage_2.get_unchecked(83usize));
                        let write_value_low = *(memory.get_unchecked(51usize));
                        let mut write_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        write_value_contribution.mul_assign(&write_value_low);
                        let write_value_high = *(memory.get_unchecked(52usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&write_value_high);
                        write_value_contribution.add_assign(&t);
                        let mut denom = numerator;
                        numerator.add_assign(&write_value_contribution);
                        denom.add_assign(&read_value_contribution);
                        numerator.add_assign(&write_timestamp_contribution);
                        denom.add_assign(&read_timestamp_contribution);
                        let mut individual_term = *(stage_2.get_unchecked(84usize));
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
                        let mut address_low = *(memory.get_unchecked(12usize));
                        address_low.add_assign_base(&Mersenne31Field(0u32));
                        let mut variable_offset = *(memory.get_unchecked(55usize));
                        variable_offset.mul_assign_by_base(&Mersenne31Field(8u32));
                        address_low.add_assign(&variable_offset);
                        let mut address_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                        address_contribution.mul_assign(&address_low);
                        let address_high = *(memory.get_unchecked(13usize));
                        let mut address_high_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                        address_high_contribution.mul_assign(&address_high);
                        address_contribution.add_assign(&address_high_contribution);
                        let read_value_low = *(memory.get_unchecked(56usize));
                        let mut read_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        read_value_contribution.mul_assign(&read_value_low);
                        let read_value_high = *(memory.get_unchecked(57usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&read_value_high);
                        read_value_contribution.add_assign(&t);
                        let read_timestamp_low = *(memory.get_unchecked(53usize));
                        let mut read_timestamp_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                        read_timestamp_contribution.mul_assign(&read_timestamp_low);
                        let read_timestamp_high = *(memory.get_unchecked(54usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                        t.mul_assign(&read_timestamp_high);
                        read_timestamp_contribution.add_assign(&t);
                        let mut numerator = memory_argument_gamma;
                        numerator.add_assign(&address_contribution);
                        let previous = *(stage_2.get_unchecked(84usize));
                        let write_value_low = *(memory.get_unchecked(58usize));
                        let mut write_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        write_value_contribution.mul_assign(&write_value_low);
                        let write_value_high = *(memory.get_unchecked(59usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&write_value_high);
                        write_value_contribution.add_assign(&t);
                        let mut denom = numerator;
                        numerator.add_assign(&write_value_contribution);
                        denom.add_assign(&read_value_contribution);
                        numerator.add_assign(&write_timestamp_contribution);
                        denom.add_assign(&read_timestamp_contribution);
                        let mut individual_term = *(stage_2.get_unchecked(85usize));
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
                        let mut address_low = *(memory.get_unchecked(12usize));
                        address_low.add_assign_base(&Mersenne31Field(4u32));
                        let mut variable_offset = *(memory.get_unchecked(55usize));
                        variable_offset.mul_assign_by_base(&Mersenne31Field(8u32));
                        address_low.add_assign(&variable_offset);
                        let mut address_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                        address_contribution.mul_assign(&address_low);
                        let address_high = *(memory.get_unchecked(13usize));
                        let mut address_high_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                        address_high_contribution.mul_assign(&address_high);
                        address_contribution.add_assign(&address_high_contribution);
                        let read_value_low = *(memory.get_unchecked(62usize));
                        let mut read_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        read_value_contribution.mul_assign(&read_value_low);
                        let read_value_high = *(memory.get_unchecked(63usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&read_value_high);
                        read_value_contribution.add_assign(&t);
                        let read_timestamp_low = *(memory.get_unchecked(60usize));
                        let mut read_timestamp_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                        read_timestamp_contribution.mul_assign(&read_timestamp_low);
                        let read_timestamp_high = *(memory.get_unchecked(61usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                        t.mul_assign(&read_timestamp_high);
                        read_timestamp_contribution.add_assign(&t);
                        let mut numerator = memory_argument_gamma;
                        numerator.add_assign(&address_contribution);
                        let previous = *(stage_2.get_unchecked(85usize));
                        let write_value_low = *(memory.get_unchecked(64usize));
                        let mut write_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        write_value_contribution.mul_assign(&write_value_low);
                        let write_value_high = *(memory.get_unchecked(65usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&write_value_high);
                        write_value_contribution.add_assign(&t);
                        let mut denom = numerator;
                        numerator.add_assign(&write_value_contribution);
                        denom.add_assign(&read_value_contribution);
                        numerator.add_assign(&write_timestamp_contribution);
                        denom.add_assign(&read_timestamp_contribution);
                        let mut individual_term = *(stage_2.get_unchecked(86usize));
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
                        let mut address_low = *(memory.get_unchecked(12usize));
                        address_low.add_assign_base(&Mersenne31Field(0u32));
                        let mut variable_offset = *(memory.get_unchecked(68usize));
                        variable_offset.mul_assign_by_base(&Mersenne31Field(8u32));
                        address_low.add_assign(&variable_offset);
                        let mut address_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                        address_contribution.mul_assign(&address_low);
                        let address_high = *(memory.get_unchecked(13usize));
                        let mut address_high_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                        address_high_contribution.mul_assign(&address_high);
                        address_contribution.add_assign(&address_high_contribution);
                        let read_value_low = *(memory.get_unchecked(69usize));
                        let mut read_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        read_value_contribution.mul_assign(&read_value_low);
                        let read_value_high = *(memory.get_unchecked(70usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&read_value_high);
                        read_value_contribution.add_assign(&t);
                        let read_timestamp_low = *(memory.get_unchecked(66usize));
                        let mut read_timestamp_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                        read_timestamp_contribution.mul_assign(&read_timestamp_low);
                        let read_timestamp_high = *(memory.get_unchecked(67usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                        t.mul_assign(&read_timestamp_high);
                        read_timestamp_contribution.add_assign(&t);
                        let mut numerator = memory_argument_gamma;
                        numerator.add_assign(&address_contribution);
                        let previous = *(stage_2.get_unchecked(86usize));
                        let write_value_low = *(memory.get_unchecked(71usize));
                        let mut write_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        write_value_contribution.mul_assign(&write_value_low);
                        let write_value_high = *(memory.get_unchecked(72usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&write_value_high);
                        write_value_contribution.add_assign(&t);
                        let mut denom = numerator;
                        numerator.add_assign(&write_value_contribution);
                        denom.add_assign(&read_value_contribution);
                        numerator.add_assign(&write_timestamp_contribution);
                        denom.add_assign(&read_timestamp_contribution);
                        let mut individual_term = *(stage_2.get_unchecked(87usize));
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
                        let mut address_low = *(memory.get_unchecked(12usize));
                        address_low.add_assign_base(&Mersenne31Field(4u32));
                        let mut variable_offset = *(memory.get_unchecked(68usize));
                        variable_offset.mul_assign_by_base(&Mersenne31Field(8u32));
                        address_low.add_assign(&variable_offset);
                        let mut address_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                        address_contribution.mul_assign(&address_low);
                        let address_high = *(memory.get_unchecked(13usize));
                        let mut address_high_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                        address_high_contribution.mul_assign(&address_high);
                        address_contribution.add_assign(&address_high_contribution);
                        let read_value_low = *(memory.get_unchecked(75usize));
                        let mut read_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        read_value_contribution.mul_assign(&read_value_low);
                        let read_value_high = *(memory.get_unchecked(76usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&read_value_high);
                        read_value_contribution.add_assign(&t);
                        let read_timestamp_low = *(memory.get_unchecked(73usize));
                        let mut read_timestamp_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                        read_timestamp_contribution.mul_assign(&read_timestamp_low);
                        let read_timestamp_high = *(memory.get_unchecked(74usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                        t.mul_assign(&read_timestamp_high);
                        read_timestamp_contribution.add_assign(&t);
                        let mut numerator = memory_argument_gamma;
                        numerator.add_assign(&address_contribution);
                        let previous = *(stage_2.get_unchecked(87usize));
                        let write_value_low = *(memory.get_unchecked(77usize));
                        let mut write_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        write_value_contribution.mul_assign(&write_value_low);
                        let write_value_high = *(memory.get_unchecked(78usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&write_value_high);
                        write_value_contribution.add_assign(&t);
                        let mut denom = numerator;
                        numerator.add_assign(&write_value_contribution);
                        denom.add_assign(&read_value_contribution);
                        numerator.add_assign(&write_timestamp_contribution);
                        denom.add_assign(&read_timestamp_contribution);
                        let mut individual_term = *(stage_2.get_unchecked(88usize));
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
                        let mut address_low = *(memory.get_unchecked(12usize));
                        address_low.add_assign_base(&Mersenne31Field(0u32));
                        let mut variable_offset = *(memory.get_unchecked(81usize));
                        variable_offset.mul_assign_by_base(&Mersenne31Field(8u32));
                        address_low.add_assign(&variable_offset);
                        let mut address_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                        address_contribution.mul_assign(&address_low);
                        let address_high = *(memory.get_unchecked(13usize));
                        let mut address_high_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                        address_high_contribution.mul_assign(&address_high);
                        address_contribution.add_assign(&address_high_contribution);
                        let read_value_low = *(memory.get_unchecked(82usize));
                        let mut read_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        read_value_contribution.mul_assign(&read_value_low);
                        let read_value_high = *(memory.get_unchecked(83usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&read_value_high);
                        read_value_contribution.add_assign(&t);
                        let read_timestamp_low = *(memory.get_unchecked(79usize));
                        let mut read_timestamp_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                        read_timestamp_contribution.mul_assign(&read_timestamp_low);
                        let read_timestamp_high = *(memory.get_unchecked(80usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                        t.mul_assign(&read_timestamp_high);
                        read_timestamp_contribution.add_assign(&t);
                        let mut numerator = memory_argument_gamma;
                        numerator.add_assign(&address_contribution);
                        let previous = *(stage_2.get_unchecked(88usize));
                        let write_value_low = *(memory.get_unchecked(84usize));
                        let mut write_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        write_value_contribution.mul_assign(&write_value_low);
                        let write_value_high = *(memory.get_unchecked(85usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&write_value_high);
                        write_value_contribution.add_assign(&t);
                        let mut denom = numerator;
                        numerator.add_assign(&write_value_contribution);
                        denom.add_assign(&read_value_contribution);
                        numerator.add_assign(&write_timestamp_contribution);
                        denom.add_assign(&read_timestamp_contribution);
                        let mut individual_term = *(stage_2.get_unchecked(89usize));
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
                        let mut address_low = *(memory.get_unchecked(12usize));
                        address_low.add_assign_base(&Mersenne31Field(4u32));
                        let mut variable_offset = *(memory.get_unchecked(81usize));
                        variable_offset.mul_assign_by_base(&Mersenne31Field(8u32));
                        address_low.add_assign(&variable_offset);
                        let mut address_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                        address_contribution.mul_assign(&address_low);
                        let address_high = *(memory.get_unchecked(13usize));
                        let mut address_high_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                        address_high_contribution.mul_assign(&address_high);
                        address_contribution.add_assign(&address_high_contribution);
                        let read_value_low = *(memory.get_unchecked(88usize));
                        let mut read_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        read_value_contribution.mul_assign(&read_value_low);
                        let read_value_high = *(memory.get_unchecked(89usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&read_value_high);
                        read_value_contribution.add_assign(&t);
                        let read_timestamp_low = *(memory.get_unchecked(86usize));
                        let mut read_timestamp_contribution =
                            memory_argument_linearization_challenges
                                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                        read_timestamp_contribution.mul_assign(&read_timestamp_low);
                        let read_timestamp_high = *(memory.get_unchecked(87usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                        t.mul_assign(&read_timestamp_high);
                        read_timestamp_contribution.add_assign(&t);
                        let mut numerator = memory_argument_gamma;
                        numerator.add_assign(&address_contribution);
                        let previous = *(stage_2.get_unchecked(89usize));
                        let write_value_low = *(memory.get_unchecked(90usize));
                        let mut write_value_contribution = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
                        write_value_contribution.mul_assign(&write_value_low);
                        let write_value_high = *(memory.get_unchecked(91usize));
                        let mut t = memory_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
                        t.mul_assign(&write_value_high);
                        write_value_contribution.add_assign(&t);
                        let mut denom = numerator;
                        numerator.add_assign(&write_value_contribution);
                        denom.add_assign(&read_value_contribution);
                        numerator.add_assign(&write_timestamp_contribution);
                        denom.add_assign(&read_timestamp_contribution);
                        let mut individual_term = *(stage_2.get_unchecked(90usize));
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
        }
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = *(stage_2_next_row.get_unchecked(91usize));
                    let mut t = *(stage_2.get_unchecked(91usize));
                    t.mul_assign(&*(stage_2.get_unchecked(90usize)));
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
                let mut individual_term = *(stage_2.get_unchecked(73usize));
                let t = *(stage_2.get_unchecked(15usize));
                individual_term.sub_assign(&t);
                individual_term
            };
            individual_term
        };
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = *(stage_2.get_unchecked(74usize));
                    let t = *(stage_2.get_unchecked(16usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(17usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(18usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(19usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(20usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(21usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(22usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(23usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(24usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(25usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(26usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(27usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(28usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(29usize));
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
                    let mut individual_term = *(stage_2.get_unchecked(75usize));
                    let t = *(stage_2.get_unchecked(30usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(31usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(32usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(33usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(34usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(35usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(36usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(37usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(38usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(39usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(40usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(41usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(42usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(43usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(44usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(45usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(46usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(47usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(48usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(49usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(50usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(51usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(52usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(53usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(54usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(55usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(56usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(57usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(58usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(59usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(60usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(61usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(62usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(63usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(64usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(65usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(66usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(67usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(68usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(69usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(70usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(71usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(72usize));
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
                    let mut individual_term = *(stage_2.get_unchecked(76usize));
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
                let mut individual_term = *(stage_2.get_unchecked(91usize));
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
                let mut individual_term = *(stage_2.get_unchecked(91usize));
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
