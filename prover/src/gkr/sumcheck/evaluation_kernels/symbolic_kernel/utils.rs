use super::*;
use cs::definitions::gkr::*;
use cs::definitions::*;
use cs::gkr_compiler::*;

pub(crate) fn vector_lookup_as_linear_symbolic_term<
    F: PrimeField,
    const WITH_ADDITIVE_PART: bool,
>(
    rel: &NoFieldVectorLookupRelation,
) -> (
    Vec<SymbolicGKRLinearTerm<F>>,
    Vec<SymbolicGKRCoefficient<F>>,
) {
    let mut linear_terms = vec![];
    let mut constant_terms = vec![];
    if WITH_ADDITIVE_PART {
        constant_terms.push(SymbolicGKRCoefficient {
            constant: F::ONE,
            challenge: Some(ChallengeType::LookupAdditivePart),
        });
    }

    let identity_coeff = SymbolicGKRCoefficient {
        constant: F::ONE,
        challenge: None,
    };

    for (idx, column) in rel.columns.iter().enumerate() {
        let challenge = if idx == 0 {
            None
        } else {
            Some(ChallengeType::LookupMultiplicativePart { power: idx })
        };
        for (coeff, a) in column.linear_terms.iter() {
            let prefactor = SymbolicGKRCoefficient {
                constant: F::from_u32_unchecked(*coeff),
                challenge,
            };
            linear_terms.push(SymbolicGKRLinearTerm {
                a: SymbolicGKRInput::BaseField(*a),
                coefficient_0: prefactor,
                coefficient_1: identity_coeff,
            });
        }
        let constant = F::from_u32_unchecked(column.constant);
        if constant.is_zero() == false {
            let prefactor = SymbolicGKRCoefficient {
                constant,
                challenge,
            };
            constant_terms.push(prefactor);
        }
    }

    (linear_terms, constant_terms)
}

pub(crate) fn memory_query_as_linear_symbolic_term<F: PrimeField>(
    rel: &NoFieldSpecialMemoryContributionRelation,
) -> (
    Vec<SymbolicGKRLinearTerm<F>>,
    Vec<SymbolicGKRCoefficient<F>>,
) {
    let mut linear_terms = vec![];
    let mut constant_terms = vec![];

    // additive part
    constant_terms.push(SymbolicGKRCoefficient {
        constant: F::ONE,
        challenge: Some(ChallengeType::PermutationAdditivePart),
    });

    // no challenge
    match rel.address_space {
        CompiledAddressSpaceRelationStrict::Constant(c) => {
            assert!(c < (1u32 << 16));
            constant_terms.push(SymbolicGKRCoefficient {
                constant: F::from_u32_unchecked(c),
                challenge: None,
            });
        }
        CompiledAddressSpaceRelationStrict::IsRam(offset) => {
            // if "1", then we should have address space == RAM (1)
            assert_eq!(AddressSpaceType::RAM as u8, 1);
            linear_terms.push(SymbolicGKRLinearTerm {
                a: SymbolicGKRInput::BaseField(GKRAddress::BaseLayerMemory(offset)),
                coefficient_0: SymbolicGKRCoefficient {
                    constant: F::ONE,
                    challenge: None,
                },
                coefficient_1: SymbolicGKRCoefficient::one(),
            });
        }
        CompiledAddressSpaceRelationStrict::IsRegister(offset) => {
            // if "1", then we should have address space == register (0)
            assert_eq!(AddressSpaceType::Register as u8, 0);
            constant_terms.push(SymbolicGKRCoefficient::one());
            linear_terms.push(SymbolicGKRLinearTerm {
                a: SymbolicGKRInput::BaseField(GKRAddress::BaseLayerMemory(offset)),
                coefficient_0: SymbolicGKRCoefficient {
                    constant: F::MINUS_ONE,
                    challenge: None,
                },
                coefficient_1: SymbolicGKRCoefficient::one(),
            });
        }
    }

    let challenge_address_low = Some(ChallengeType::PermutationDelinearization {
        index: MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    });
    let challenge_address_high = Some(ChallengeType::PermutationDelinearization {
        index: MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    });

    match &rel.address {
        &CompiledAddressStrict::ConstantU16(c) => {
            constant_terms.push(SymbolicGKRCoefficient {
                constant: F::from_u32_unchecked(c as u32),
                challenge: challenge_address_low,
            });
        }
        &CompiledAddressStrict::Constant(c) => {
            assert!(c < (1u32 << 16));
            constant_terms.push(SymbolicGKRCoefficient {
                constant: F::from_u32_unchecked(c as u32),
                challenge: challenge_address_low,
            });
        }
        &CompiledAddressStrict::U16Space(offset) => {
            linear_terms.push(SymbolicGKRLinearTerm {
                a: SymbolicGKRInput::BaseField(GKRAddress::BaseLayerMemory(offset)),
                coefficient_0: SymbolicGKRCoefficient {
                    constant: F::ONE,
                    challenge: challenge_address_low,
                },
                coefficient_1: SymbolicGKRCoefficient::one(),
            });
        }
        &CompiledAddressStrict::U32Space([low, high]) => {
            for (challenge, offset) in
                [(challenge_address_low, low), (challenge_address_high, high)]
            {
                linear_terms.push(SymbolicGKRLinearTerm {
                    a: SymbolicGKRInput::BaseField(GKRAddress::BaseLayerMemory(offset)),
                    coefficient_0: SymbolicGKRCoefficient {
                        constant: F::ONE,
                        challenge,
                    },
                    coefficient_1: SymbolicGKRCoefficient::one(),
                });
            }
        }
        CompiledAddressStrict::U32SpaceGeneric(..) => {
            todo!();
        }
        CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base,
            low_dynamic_offset,
            low_offset,
            high,
        } => {
            if let Some((c, offset)) = *low_dynamic_offset {
                linear_terms.push(SymbolicGKRLinearTerm {
                    a: SymbolicGKRInput::BaseField(GKRAddress::BaseLayerMemory(offset)),
                    coefficient_0: SymbolicGKRCoefficient {
                        constant: F::from_u32_unchecked(c as u32),
                        challenge: challenge_address_low,
                    },
                    coefficient_1: SymbolicGKRCoefficient::one(),
                });
            }
            {
                linear_terms.push(SymbolicGKRLinearTerm {
                    a: SymbolicGKRInput::BaseField(GKRAddress::BaseLayerMemory(*low_base)),
                    coefficient_0: SymbolicGKRCoefficient {
                        constant: F::ONE,
                        challenge: challenge_address_low,
                    },
                    coefficient_1: SymbolicGKRCoefficient::one(),
                });
                let low_offset = F::from_u32_unchecked(*low_offset);
                if low_offset.is_zero() == false {
                    constant_terms.push(SymbolicGKRCoefficient {
                        constant: low_offset,
                        challenge: challenge_address_low,
                    });
                }
            }
            {
                linear_terms.push(SymbolicGKRLinearTerm {
                    a: SymbolicGKRInput::BaseField(GKRAddress::BaseLayerMemory(*high)),
                    coefficient_0: SymbolicGKRCoefficient {
                        constant: F::ONE,
                        challenge: challenge_address_high,
                    },
                    coefficient_1: SymbolicGKRCoefficient::one(),
                });
            }
        }
    }

    // timestamp is a little special as we do add constant offset
    let challenge_timestamp_low = Some(ChallengeType::PermutationDelinearization {
        index: MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
    });
    let challenge_timestamp_high = Some(ChallengeType::PermutationDelinearization {
        index: MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    });

    match rel.timestamp {
        CompiledMemoryTimestamp::Zero => {}
        CompiledMemoryTimestamp::Normal(ts) => {
            {
                linear_terms.push(SymbolicGKRLinearTerm {
                    a: SymbolicGKRInput::BaseField(GKRAddress::BaseLayerMemory(ts[0])),
                    coefficient_0: SymbolicGKRCoefficient {
                        constant: F::ONE,
                        challenge: challenge_timestamp_low,
                    },
                    coefficient_1: SymbolicGKRCoefficient::one(),
                });
                let timestamp_offset = F::from_u32_unchecked(rel.timestamp_offset);
                if timestamp_offset.is_zero() == false {
                    constant_terms.push(SymbolicGKRCoefficient {
                        constant: timestamp_offset,
                        challenge: challenge_timestamp_low,
                    });
                }
            }
            {
                linear_terms.push(SymbolicGKRLinearTerm {
                    a: SymbolicGKRInput::BaseField(GKRAddress::BaseLayerMemory(ts[1])),
                    coefficient_0: SymbolicGKRCoefficient {
                        constant: F::ONE,
                        challenge: challenge_timestamp_high,
                    },
                    coefficient_1: SymbolicGKRCoefficient::one(),
                });
            }
        }
    }

    // and values are simplified for now
    let challenge_value_low = Some(ChallengeType::PermutationDelinearization {
        index: MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
    });
    let challenge_value_high = Some(ChallengeType::PermutationDelinearization {
        index: MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    });

    match rel.value {
        RamWordRepresentation::Zero => {
            // nothing
        }
        RamWordRepresentation::U16Limbs(read_value) => {
            for (challenge, offset) in [
                (challenge_value_low, read_value[0]),
                (challenge_value_high, read_value[1]),
            ] {
                linear_terms.push(SymbolicGKRLinearTerm {
                    a: SymbolicGKRInput::BaseField(GKRAddress::BaseLayerMemory(offset)),
                    coefficient_0: SymbolicGKRCoefficient {
                        constant: F::ONE,
                        challenge,
                    },
                    coefficient_1: SymbolicGKRCoefficient::one(),
                });
            }
        }
        RamWordRepresentation::U8Limbs(read_value_bytes) => {
            let byte_shift = F::from_u32_unchecked(1u32 << 8);
            for (challenge, offset_low, offset_high) in [
                (
                    challenge_value_low,
                    read_value_bytes[0],
                    read_value_bytes[1],
                ),
                (
                    challenge_value_high,
                    read_value_bytes[2],
                    read_value_bytes[3],
                ),
            ] {
                linear_terms.push(SymbolicGKRLinearTerm {
                    a: SymbolicGKRInput::BaseField(GKRAddress::BaseLayerMemory(offset_low)),
                    coefficient_0: SymbolicGKRCoefficient {
                        constant: F::ONE,
                        challenge,
                    },
                    coefficient_1: SymbolicGKRCoefficient::one(),
                });
                linear_terms.push(SymbolicGKRLinearTerm {
                    a: SymbolicGKRInput::BaseField(GKRAddress::BaseLayerMemory(offset_high)),
                    coefficient_0: SymbolicGKRCoefficient {
                        constant: byte_shift,
                        challenge,
                    },
                    coefficient_1: SymbolicGKRCoefficient::one(),
                });
            }
        }
    }

    (linear_terms, constant_terms)
}

pub(crate) fn single_column_lookup_as_linear_symbolic_term<
    F: PrimeField,
    const WITH_ADDITIVE_PART: bool,
>(
    rel: &NoFieldSingleColumnLookupRelation,
) -> (
    Vec<SymbolicGKRLinearTerm<F>>,
    Vec<SymbolicGKRCoefficient<F>>,
) {
    let mut linear_terms = vec![];
    let mut constant_terms = vec![];
    if WITH_ADDITIVE_PART {
        constant_terms.push(SymbolicGKRCoefficient {
            constant: F::ONE,
            challenge: Some(ChallengeType::LookupAdditivePart),
        });
    }
    let identity_coeff = SymbolicGKRCoefficient {
        constant: F::ONE,
        challenge: None,
    };

    for (coeff, a) in rel.input.linear_terms.iter() {
        let prefactor = SymbolicGKRCoefficient {
            constant: F::from_u32_unchecked(*coeff),
            challenge: None,
        };
        linear_terms.push(SymbolicGKRLinearTerm {
            a: SymbolicGKRInput::BaseField(*a),
            coefficient_0: prefactor,
            coefficient_1: identity_coeff,
        });
    }
    let constant = F::from_u32_unchecked(rel.input.constant);
    if constant.is_zero() == false {
        let prefactor = SymbolicGKRCoefficient {
            constant,
            challenge: None,
        };
        constant_terms.push(prefactor);
    }

    (linear_terms, constant_terms)
}

pub(crate) fn inits_or_teardowns_as_linear_symbolic_term<F: PrimeField>(
    timestamps_and_values: Option<([GKRAddress; 2], [GKRAddress; 2])>,
    setup: [GKRAddress; 2],
    address_high_bits: u32,
    address_high_bits_shift: u32,
) -> (
    Vec<SymbolicGKRLinearTerm<F>>,
    Vec<SymbolicGKRCoefficient<F>>,
) {
    use cs::definitions::gkr::AddressSpaceType;

    let mut linear_terms = vec![];
    let mut constant_terms = vec![];

    // additive part
    constant_terms.push(SymbolicGKRCoefficient {
        constant: F::ONE,
        challenge: Some(ChallengeType::PermutationAdditivePart),
    });

    // it's always RAM address space, no challenge
    constant_terms.push(SymbolicGKRCoefficient {
        constant: F::from_u32_unchecked(AddressSpaceType::RAM as u32),
        challenge: None,
    });

    {
        let challenge_address_low = Some(ChallengeType::PermutationDelinearization {
            index: MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
        });
        let challenge_address_high = Some(ChallengeType::PermutationDelinearization {
            index: MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
        });

        {
            linear_terms.push(SymbolicGKRLinearTerm {
                a: SymbolicGKRInput::BaseField(setup[0]),
                coefficient_0: SymbolicGKRCoefficient {
                    constant: F::ONE,
                    challenge: challenge_address_low,
                },
                coefficient_1: SymbolicGKRCoefficient::one(),
            });
        }
        {
            linear_terms.push(SymbolicGKRLinearTerm {
                a: SymbolicGKRInput::BaseField(setup[1]),
                coefficient_0: SymbolicGKRCoefficient {
                    constant: F::ONE,
                    challenge: challenge_address_high,
                },
                coefficient_1: SymbolicGKRCoefficient::one(),
            });

            constant_terms.push(SymbolicGKRCoefficient {
                constant: F::from_u32_unchecked(address_high_bits << address_high_bits_shift),
                challenge: challenge_address_high,
            });
        }
    }

    if let Some((timestamps, values)) = timestamps_and_values {
        let challenge_timestamp_low = Some(ChallengeType::PermutationDelinearization {
            index: MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
        });
        let challenge_timestamp_high = Some(ChallengeType::PermutationDelinearization {
            index: MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
        });

        for (challenge, offset) in [
            (challenge_timestamp_low, timestamps[0]),
            (challenge_timestamp_high, timestamps[1]),
        ] {
            linear_terms.push(SymbolicGKRLinearTerm {
                a: SymbolicGKRInput::BaseField(offset),
                coefficient_0: SymbolicGKRCoefficient {
                    constant: F::ONE,
                    challenge,
                },
                coefficient_1: SymbolicGKRCoefficient::one(),
            });
        }

        let challenge_value_low = Some(ChallengeType::PermutationDelinearization {
            index: MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
        });
        let challenge_value_high = Some(ChallengeType::PermutationDelinearization {
            index: MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
        });

        for (challenge, offset) in [
            (challenge_value_low, values[0]),
            (challenge_value_high, values[1]),
        ] {
            linear_terms.push(SymbolicGKRLinearTerm {
                a: SymbolicGKRInput::BaseField(offset),
                coefficient_0: SymbolicGKRCoefficient {
                    constant: F::ONE,
                    challenge,
                },
                coefficient_1: SymbolicGKRCoefficient::one(),
            });
        }
    }

    (linear_terms, constant_terms)
}
