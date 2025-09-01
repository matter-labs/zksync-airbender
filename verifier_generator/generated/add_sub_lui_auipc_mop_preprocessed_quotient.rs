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
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(17usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(17usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(65536u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        let b = *(memory.get_unchecked(2usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        let b = *(memory.get_unchecked(3usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        let b = *(memory.get_unchecked(7usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        let b = *(memory.get_unchecked(8usize));
                        a.mul_assign(&b);
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
                        let mut a = *(witness.get_unchecked(17usize));
                        let b = *(witness.get_unchecked(20usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(17usize));
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
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(65536u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        let b = *(memory.get_unchecked(2usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        let b = *(memory.get_unchecked(3usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        let b = *(memory.get_unchecked(7usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        let b = *(memory.get_unchecked(8usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(65536u32));
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
                        let mut a = *(witness.get_unchecked(18usize));
                        let b = *(witness.get_unchecked(20usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(18usize));
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
                        let mut a = *(memory.get_unchecked(2usize));
                        let b = *(memory.get_unchecked(7usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(memory.get_unchecked(2usize));
                        let b = *(memory.get_unchecked(8usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(65536u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(memory.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(7usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(65536u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(memory.get_unchecked(3usize));
                        let b = *(memory.get_unchecked(8usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(28usize));
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
                        let b = *(witness.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(65536u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        let b = *(witness.get_unchecked(28usize));
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
                        let mut a = *(witness.get_unchecked(18usize));
                        let b = *(witness.get_unchecked(20usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(18usize));
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
                        let mut a = *(witness.get_unchecked(0usize));
                        let b = *(witness.get_unchecked(8usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(8usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(15usize));
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
                        let b = *(witness.get_unchecked(9usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(9usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(16usize));
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
                        let mut a = *(witness.get_unchecked(21usize));
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(21usize));
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
                        let mut a = *(witness.get_unchecked(29usize));
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(21usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(29usize));
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
                        let mut a = *(witness.get_unchecked(21usize));
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(21usize));
                        a.mul_assign_by_base(&Mersenne31Field(2147483643u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(18usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(22usize));
                        individual_term.sub_assign(&a);
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
                        let mut a = *(witness.get_unchecked(21usize));
                        let b = *(witness.get_unchecked(22usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(memory.get_unchecked(19usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(22usize));
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
                        let mut a = *(witness.get_unchecked(21usize));
                        let b = *(witness.get_unchecked(30usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(30usize));
                        let b = *(memory.get_unchecked(19usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(22usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(30usize));
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
                        let mut a = *(witness.get_unchecked(21usize));
                        let b = *(witness.get_unchecked(22usize));
                        a.mul_assign(&b);
                        a.negate();
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(22usize));
                        let b = *(memory.get_unchecked(19usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(21usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(19usize));
                        individual_term.add_assign(&a);
                    }
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
                        let mut a = *(witness.get_unchecked(1usize));
                        let b = *(witness.get_unchecked(13usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(1usize));
                        let b = *(witness.get_unchecked(15usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(1usize));
                        let b = *(witness.get_unchecked(16usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(12usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(13usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(14usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(15usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(16usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(17usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(8usize));
                        let b = *(witness.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483645u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(10usize));
                        let b = *(witness.get_unchecked(17usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(10usize));
                        let b = *(witness.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(memory.get_unchecked(2usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(memory.get_unchecked(7usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(13usize));
                        let b = *(memory.get_unchecked(2usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        let b = *(memory.get_unchecked(2usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        let b = *(memory.get_unchecked(7usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(16usize));
                        let b = *(memory.get_unchecked(18usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        a.mul_assign_by_base(&Mersenne31Field(65535u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        a.mul_assign_by_base(&Mersenne31Field(131070u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(23usize));
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
                        let mut a = *(witness.get_unchecked(2usize));
                        let b = *(witness.get_unchecked(13usize));
                        a.mul_assign(&b);
                        a
                    };
                    {
                        let mut a = *(witness.get_unchecked(2usize));
                        let b = *(witness.get_unchecked(15usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(2usize));
                        let b = *(witness.get_unchecked(16usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(12usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(13usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(14usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(15usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(16usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(17usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(9usize));
                        let b = *(witness.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2147483645u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(17usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(11usize));
                        let b = *(witness.get_unchecked(18usize));
                        a.mul_assign(&b);
                        a.mul_assign_by_base(&Mersenne31Field(2u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(memory.get_unchecked(3usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(12usize));
                        let b = *(memory.get_unchecked(8usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(13usize));
                        let b = *(memory.get_unchecked(3usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        let b = *(memory.get_unchecked(3usize));
                        a.mul_assign(&b);
                        individual_term.sub_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        let b = *(memory.get_unchecked(8usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(16usize));
                        let b = *(memory.get_unchecked(19usize));
                        a.mul_assign(&b);
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        a.mul_assign_by_base(&Mersenne31Field(32767u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        a.mul_assign_by_base(&Mersenne31Field(65534u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(20usize));
                        a.mul_assign_by_base(&Mersenne31Field(2147418111u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(23usize));
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
                        a.negate();
                        a
                    };
                    {
                        let a = *(witness.get_unchecked(12usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(13usize));
                        a.mul_assign_by_base(&Mersenne31Field(2u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(14usize));
                        a.mul_assign_by_base(&Mersenne31Field(4u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(15usize));
                        a.mul_assign_by_base(&Mersenne31Field(8u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(16usize));
                        a.mul_assign_by_base(&Mersenne31Field(16u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(17usize));
                        a.mul_assign_by_base(&Mersenne31Field(32u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(18usize));
                        a.mul_assign_by_base(&Mersenne31Field(64u32));
                        individual_term.add_assign(&a);
                    }
                    {
                        let mut a = *(witness.get_unchecked(19usize));
                        a.mul_assign_by_base(&Mersenne31Field(128u32));
                        individual_term.add_assign(&a);
                    }
                    individual_term
                };
                individual_term
            };
            accumulated_contribution.add_assign(&contribution);
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
                        let acc_value = *(stage_2.get_unchecked(6usize));
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
                let value = *(witness.get_unchecked(10usize));
                value
            };
            let b = {
                let value = *(witness.get_unchecked(11usize));
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
                let individual_term = {
                    let mut individual_term = {
                        let mut a = *(witness.get_unchecked(24usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(0usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(20usize));
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
                        let a = *(memory.get_unchecked(21usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(24usize));
                        individual_term.sub_assign(&a);
                    }
                    individual_term.add_assign_base(&Mersenne31Field(524288u32));
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
                        let mut a = *(witness.get_unchecked(25usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(5usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(20usize));
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
                        let a = *(memory.get_unchecked(21usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(25usize));
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
                        let mut a = *(witness.get_unchecked(26usize));
                        a.mul_assign_by_base(&Mersenne31Field(524288u32));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(10usize));
                        individual_term.add_assign(&a);
                    }
                    {
                        let a = *(memory.get_unchecked(20usize));
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
                        let a = *(memory.get_unchecked(11usize));
                        a
                    };
                    {
                        let a = *(memory.get_unchecked(21usize));
                        individual_term.sub_assign(&a);
                    }
                    {
                        let a = *(witness.get_unchecked(26usize));
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
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let m = *(memory.get_unchecked(17usize));
                    let mut denom = decoder_lookup_argument_gamma;
                    denom.add_assign(&*(memory.get_unchecked(18usize)));
                    let mut t = decoder_lookup_argument_linearization_challenges[0usize];
                    t.mul_assign(&*(memory.get_unchecked(19usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[1usize];
                    t.mul_assign(&*(memory.get_unchecked(4usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[2usize];
                    t.mul_assign(&*(memory.get_unchecked(9usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[3usize];
                    t.mul_assign(&*(memory.get_unchecked(14usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[4usize];
                    t.mul_assign(&*(witness.get_unchecked(0usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[5usize];
                    t.mul_assign(&*(witness.get_unchecked(1usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[6usize];
                    t.mul_assign(&*(witness.get_unchecked(2usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[7usize];
                    t.mul_assign(&*(witness.get_unchecked(3usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[8usize];
                    t.mul_assign(&*(witness.get_unchecked(4usize)));
                    denom.add_assign(&t);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(12usize)));
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
                    let m = *(witness.get_unchecked(5usize));
                    let t = *(setup.get_unchecked(0usize));
                    let mut denom = lookup_argument_gamma;
                    denom.add_assign(&t);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(13usize)));
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
                    let m = *(witness.get_unchecked(6usize));
                    let t = *(setup.get_unchecked(1usize));
                    let mut denom = lookup_argument_gamma;
                    denom.add_assign(&t);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(14usize)));
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
                    let m = *(witness.get_unchecked(7usize));
                    let mut denom = decoder_lookup_argument_gamma;
                    denom.add_assign(&*(setup.get_unchecked(2usize)));
                    let mut t = decoder_lookup_argument_linearization_challenges[0usize];
                    t.mul_assign(&*(setup.get_unchecked(3usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[1usize];
                    t.mul_assign(&*(setup.get_unchecked(4usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[2usize];
                    t.mul_assign(&*(setup.get_unchecked(5usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[3usize];
                    t.mul_assign(&*(setup.get_unchecked(6usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[4usize];
                    t.mul_assign(&*(setup.get_unchecked(7usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[5usize];
                    t.mul_assign(&*(setup.get_unchecked(8usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[6usize];
                    t.mul_assign(&*(setup.get_unchecked(9usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[7usize];
                    t.mul_assign(&*(setup.get_unchecked(10usize)));
                    denom.add_assign(&t);
                    let mut t = decoder_lookup_argument_linearization_challenges[8usize];
                    t.mul_assign(&*(setup.get_unchecked(11usize)));
                    denom.add_assign(&t);
                    let mut individual_term = denom;
                    individual_term.mul_assign(&*(stage_2.get_unchecked(15usize)));
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
                    let mut write_timestamp_low = *(memory.get_unchecked(20usize));
                    write_timestamp_low.add_assign_base(&Mersenne31Field(0u32));
                    let mut write_timestamp_contribution =
                        memory_argument_linearization_challenges[2usize];
                    write_timestamp_contribution.mul_assign(&write_timestamp_low);
                    let mut write_timestamp_high = *(memory.get_unchecked(21usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    t.mul_assign(&write_timestamp_high);
                    write_timestamp_contribution.add_assign(&t);
                    numerator.add_assign(&write_timestamp_contribution);
                    denom.add_assign(&read_timestamp_contribution);
                    let accumulator = *(stage_2.get_unchecked(16usize));
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
                        let address_low = *(memory.get_unchecked(9usize));
                        let mut address_contribution =
                            memory_argument_linearization_challenges[0usize];
                        address_contribution.mul_assign(&address_low);
                        address_contribution.add_assign_base(&Mersenne31Field::ONE);
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
                    let mut write_timestamp_low = *(memory.get_unchecked(20usize));
                    write_timestamp_low.add_assign_base(&Mersenne31Field(1u32));
                    let mut write_timestamp_contribution =
                        memory_argument_linearization_challenges[2usize];
                    write_timestamp_contribution.mul_assign(&write_timestamp_low);
                    let mut write_timestamp_high = *(memory.get_unchecked(21usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    t.mul_assign(&write_timestamp_high);
                    write_timestamp_contribution.add_assign(&t);
                    numerator.add_assign(&write_timestamp_contribution);
                    denom.add_assign(&read_timestamp_contribution);
                    let accumulator = *(stage_2.get_unchecked(17usize));
                    let previous = *(stage_2.get_unchecked(16usize));
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
                        let address_low = *(memory.get_unchecked(14usize));
                        let mut address_contribution =
                            memory_argument_linearization_challenges[0usize];
                        address_contribution.mul_assign(&address_low);
                        address_contribution.add_assign_base(&Mersenne31Field::ONE);
                        address_contribution
                    };
                    let mut numerator = memory_argument_gamma;
                    numerator.add_assign(&address_contribution);
                    let mut denom = numerator;
                    let read_value_low = *(memory.get_unchecked(12usize));
                    let mut read_value_contribution =
                        memory_argument_linearization_challenges[4usize];
                    read_value_contribution.mul_assign(&read_value_low);
                    let read_value_high = *(memory.get_unchecked(13usize));
                    let mut t = memory_argument_linearization_challenges[5usize];
                    t.mul_assign(&read_value_high);
                    read_value_contribution.add_assign(&t);
                    let write_value_low = *(memory.get_unchecked(15usize));
                    let mut write_value_contribution =
                        memory_argument_linearization_challenges[4usize];
                    write_value_contribution.mul_assign(&write_value_low);
                    let write_value_high = *(memory.get_unchecked(16usize));
                    let mut t = memory_argument_linearization_challenges[5usize];
                    t.mul_assign(&write_value_high);
                    write_value_contribution.add_assign(&t);
                    numerator.add_assign(&write_value_contribution);
                    denom.add_assign(&read_value_contribution);
                    let read_timestamp_low = *(memory.get_unchecked(10usize));
                    let mut read_timestamp_contribution =
                        memory_argument_linearization_challenges[2usize];
                    read_timestamp_contribution.mul_assign(&read_timestamp_low);
                    let read_timestamp_high = *(memory.get_unchecked(11usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    t.mul_assign(&read_timestamp_high);
                    read_timestamp_contribution.add_assign(&t);
                    let mut write_timestamp_low = *(memory.get_unchecked(20usize));
                    write_timestamp_low.add_assign_base(&Mersenne31Field(2u32));
                    let mut write_timestamp_contribution =
                        memory_argument_linearization_challenges[2usize];
                    write_timestamp_contribution.mul_assign(&write_timestamp_low);
                    let mut write_timestamp_high = *(memory.get_unchecked(21usize));
                    let mut t = memory_argument_linearization_challenges[3usize];
                    t.mul_assign(&write_timestamp_high);
                    write_timestamp_contribution.add_assign(&t);
                    numerator.add_assign(&write_timestamp_contribution);
                    denom.add_assign(&read_timestamp_contribution);
                    let accumulator = *(stage_2.get_unchecked(18usize));
                    let previous = *(stage_2.get_unchecked(17usize));
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
                    numerator.add_assign(&*(memory.get_unchecked(22usize)));
                    let mut t = state_permutation_argument_linearization_challenges[0];
                    t.mul_assign(&*(memory.get_unchecked(23usize)));
                    numerator.add_assign(&t);
                    let mut t = state_permutation_argument_linearization_challenges[1];
                    t.mul_assign(&*(memory.get_unchecked(24usize)));
                    numerator.add_assign(&t);
                    let mut t = state_permutation_argument_linearization_challenges[2];
                    t.mul_assign(&*(memory.get_unchecked(25usize)));
                    numerator.add_assign(&t);
                    let mut denom = state_permutation_argument_gamma;
                    denom.add_assign(&*(memory.get_unchecked(18usize)));
                    let mut t = state_permutation_argument_linearization_challenges[0];
                    t.mul_assign(&*(memory.get_unchecked(19usize)));
                    denom.add_assign(&t);
                    let mut t = state_permutation_argument_linearization_challenges[1];
                    t.mul_assign(&*(memory.get_unchecked(20usize)));
                    denom.add_assign(&t);
                    let mut t = state_permutation_argument_linearization_challenges[2];
                    t.mul_assign(&*(memory.get_unchecked(21usize)));
                    denom.add_assign(&t);
                    let mut individual_term = *(stage_2.get_unchecked(19usize));
                    individual_term.mul_assign(&denom);
                    let mut t = *(stage_2.get_unchecked(18usize));
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
                    let mut individual_term = *(stage_2.get_unchecked(20usize));
                    let predicate = *(memory.get_unchecked(17usize));
                    let mut t = *(stage_2.get_unchecked(19usize));
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
                    let mut individual_term = *(stage_2_next_row.get_unchecked(21usize));
                    let mut t = *(stage_2.get_unchecked(21usize));
                    t.mul_assign(&*(stage_2.get_unchecked(20usize)));
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
                let mut individual_term = *(stage_2.get_unchecked(13usize));
                let t = *(stage_2.get_unchecked(6usize));
                individual_term.sub_assign(&t);
                let t = *(stage_2.get_unchecked(7usize));
                individual_term.sub_assign(&t);
                individual_term
            };
            individual_term
        };
        {
            accumulated_contribution.mul_assign(&quotient_alpha);
            let contribution = {
                let individual_term = {
                    let mut individual_term = *(stage_2.get_unchecked(14usize));
                    let t = *(stage_2.get_unchecked(8usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(9usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(10usize));
                    individual_term.sub_assign(&t);
                    let t = *(stage_2.get_unchecked(11usize));
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
                    let mut individual_term = *(stage_2.get_unchecked(15usize));
                    individual_term.sub_assign(&*(stage_2.get_unchecked(12usize)));
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
                let mut individual_term = *(stage_2.get_unchecked(21usize));
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
                let mut individual_term = *(stage_2.get_unchecked(21usize));
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
