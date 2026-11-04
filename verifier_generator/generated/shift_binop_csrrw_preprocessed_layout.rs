const COMPILED_WITNESS_LAYOUT: CompiledWitnessSubtree<Mersenne31Field> = CompiledWitnessSubtree {
    multiplicities_columns_for_range_check_16: ColumnSet::<1usize> {
        start: 5usize,
        num_elements: 1usize,
    },
    multiplicities_columns_for_timestamp_range_check: ColumnSet::<1usize> {
        start: 6usize,
        num_elements: 1usize,
    },
    multiplicities_columns_for_decoder_in_executor_families: ColumnSet::<1usize> {
        start: 7usize,
        num_elements: 1usize,
    },
    multiplicities_columns_for_generic_lookup: ColumnSet::<1usize> {
        start: 8usize,
        num_elements: 1usize,
    },
    range_check_16_columns: ColumnSet::<1usize> {
        start: 9usize,
        num_elements: 0usize,
    },
    width_3_lookups: &[
        VerifierCompiledLookupSetDescription {
            input_columns: [
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(21usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(22usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(23usize)),
            ],
            table_index: TableIndex::Variable(ColumnAddress::WitnessSubtree(24usize)),
        },
        VerifierCompiledLookupSetDescription {
            input_columns: [
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(25usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(26usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(27usize)),
            ],
            table_index: TableIndex::Variable(ColumnAddress::WitnessSubtree(28usize)),
        },
        VerifierCompiledLookupSetDescription {
            input_columns: [
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(29usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(30usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(31usize)),
            ],
            table_index: TableIndex::Variable(ColumnAddress::WitnessSubtree(32usize)),
        },
        VerifierCompiledLookupSetDescription {
            input_columns: [
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(33usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(34usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(35usize)),
            ],
            table_index: TableIndex::Variable(ColumnAddress::WitnessSubtree(36usize)),
        },
    ],
    range_check_16_lookup_expressions: &[],
    timestamp_range_check_lookup_expressions: &[
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[(Mersenne31Field(1u32), ColumnAddress::MemorySubtree(26usize))],
            constant_term: Mersenne31Field(0u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[(Mersenne31Field(1u32), ColumnAddress::MemorySubtree(27usize))],
            constant_term: Mersenne31Field(0u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (
                    Mersenne31Field(524288u32),
                    ColumnAddress::WitnessSubtree(17usize),
                ),
                (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(0usize)),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(22usize),
                ),
            ],
            constant_term: Mersenne31Field(0u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(1usize)),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(23usize),
                ),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(17usize),
                ),
            ],
            constant_term: Mersenne31Field(524288u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (
                    Mersenne31Field(524288u32),
                    ColumnAddress::WitnessSubtree(18usize),
                ),
                (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(5usize)),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(22usize),
                ),
            ],
            constant_term: Mersenne31Field(2147483646u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(6usize)),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(23usize),
                ),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(18usize),
                ),
            ],
            constant_term: Mersenne31Field(524288u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (
                    Mersenne31Field(524288u32),
                    ColumnAddress::WitnessSubtree(19usize),
                ),
                (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(10usize)),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(22usize),
                ),
            ],
            constant_term: Mersenne31Field(2147483645u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(11usize)),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(23usize),
                ),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(19usize),
                ),
            ],
            constant_term: Mersenne31Field(524288u32),
        }),
    ],
    offset_for_special_shuffle_ram_timestamps_range_check_expressions: 8usize,
    boolean_vars_columns_range: ColumnSet::<1usize> {
        start: 9usize,
        num_elements: 12usize,
    },
    scratch_space_columns_range: ColumnSet::<1usize> {
        start: 37usize,
        num_elements: 14usize,
    },
    total_width: 51usize,
};
const COMPILED_MEMORY_LAYOUT: CompiledMemorySubtree<'static> = CompiledMemorySubtree {
    shuffle_ram_inits_and_teardowns: &[],
    delegation_request_layout: Some(DelegationRequestLayout {
        multiplicity: ColumnSet::<1usize> {
            start: 17usize,
            num_elements: 1usize,
        },
        delegation_type: ColumnSet::<1usize> {
            start: 18usize,
            num_elements: 1usize,
        },
        abi_mem_offset_high: ColumnSet::<1usize> {
            start: 0usize,
            num_elements: 0usize,
        },
        in_cycle_write_index: 3u16,
    }),
    delegation_processor_layout: None,
    shuffle_ram_access_sets: &[
        ShuffleRamQueryColumns::Readonly(ShuffleRamQueryReadColumns {
            in_cycle_write_index: 0u32,
            address: ShuffleRamAddress::RegisterOnly(RegisterOnlyAccessAddress {
                register_index: ColumnSet::<1usize> {
                    start: 4usize,
                    num_elements: 1usize,
                },
            }),
            read_timestamp: ColumnSet::<2usize> {
                start: 0usize,
                num_elements: 1usize,
            },
            read_value: ColumnSet::<2usize> {
                start: 2usize,
                num_elements: 1usize,
            },
        }),
        ShuffleRamQueryColumns::Readonly(ShuffleRamQueryReadColumns {
            in_cycle_write_index: 1u32,
            address: ShuffleRamAddress::RegisterOnly(RegisterOnlyAccessAddress {
                register_index: ColumnSet::<1usize> {
                    start: 9usize,
                    num_elements: 1usize,
                },
            }),
            read_timestamp: ColumnSet::<2usize> {
                start: 5usize,
                num_elements: 1usize,
            },
            read_value: ColumnSet::<2usize> {
                start: 7usize,
                num_elements: 1usize,
            },
        }),
        ShuffleRamQueryColumns::Write(ShuffleRamQueryWriteColumns {
            in_cycle_write_index: 2u32,
            address: ShuffleRamAddress::RegisterOnly(RegisterOnlyAccessAddress {
                register_index: ColumnSet::<1usize> {
                    start: 14usize,
                    num_elements: 1usize,
                },
            }),
            read_timestamp: ColumnSet::<2usize> {
                start: 10usize,
                num_elements: 1usize,
            },
            read_value: ColumnSet::<2usize> {
                start: 12usize,
                num_elements: 1usize,
            },
            write_value: ColumnSet::<2usize> {
                start: 15usize,
                num_elements: 1usize,
            },
        }),
    ],
    machine_state_layout: Some(MachineStatePermutationVariables {
        pc: ColumnSet::<2usize> {
            start: 24usize,
            num_elements: 1usize,
        },
        timestamp: ColumnSet::<2usize> {
            start: 26usize,
            num_elements: 1usize,
        },
    }),
    intermediate_state_layout: Some(IntermediateStatePermutationVariables {
        pc: ColumnSet::<2usize> {
            start: 20usize,
            num_elements: 1usize,
        },
        timestamp: ColumnSet::<2usize> {
            start: 22usize,
            num_elements: 1usize,
        },
        execute: ColumnSet::<1usize> {
            start: 19usize,
            num_elements: 1usize,
        },
        rs1_index: ColumnSet::<1usize> {
            start: 4usize,
            num_elements: 1usize,
        },
        rs2_index: ColumnAddress::MemorySubtree(9usize),
        rd_index: ColumnAddress::MemorySubtree(14usize),
        decoder_witness_is_in_memory: false,
        rd_is_zero: ColumnSet::<1usize> {
            start: 0usize,
            num_elements: 1usize,
        },
        imm: ColumnSet::<2usize> {
            start: 1usize,
            num_elements: 1usize,
        },
        funct3: ColumnSet::<1usize> {
            start: 3usize,
            num_elements: 1usize,
        },
        funct7: ColumnSet::<1usize> {
            start: 0usize,
            num_elements: 0usize,
        },
        circuit_family: ColumnSet::<1usize> {
            start: 0usize,
            num_elements: 0usize,
        },
        circuit_family_extra_mask: ColumnAddress::WitnessSubtree(4usize),
    }),
    batched_ram_accesses: &[],
    register_and_indirect_accesses: &[],
    total_width: 28usize,
};
const COMPILED_SETUP_LAYOUT: SetupLayout = SetupLayout {
    timestamp_setup_columns: ColumnSet::<2usize> {
        start: 0usize,
        num_elements: 0usize,
    },
    timestamp_range_check_setup_column: ColumnSet::<1usize> {
        start: 1usize,
        num_elements: 1usize,
    },
    range_check_16_setup_column: ColumnSet::<1usize> {
        start: 0usize,
        num_elements: 1usize,
    },
    generic_lookup_setup_columns: ColumnSet::<4usize> {
        start: 2usize,
        num_elements: 1usize,
    },
    preprocessed_decoder_setup_columns: ColumnSet::<10usize> {
        start: 6usize,
        num_elements: 1usize,
    },
    total_width: 16usize,
};
const COMPILED_STAGE_2_LAYOUT: LookupAndMemoryArgumentLayout = LookupAndMemoryArgumentLayout {
    intermediate_polys_for_range_check_16: OptimizedOraclesForLookupWidth1 {
        num_pairs: 0usize,
        base_field_oracles: AlignedColumnSet::<1usize> {
            start: 0usize,
            num_elements: 0usize,
        },
        ext_4_field_oracles: AlignedColumnSet::<4usize> {
            start: 4usize,
            num_elements: 0usize,
        },
    },
    remainder_for_range_check_16: None,
    lazy_init_address_range_check_16: None,
    intermediate_polys_for_timestamp_range_checks: OptimizedOraclesForLookupWidth1 {
        num_pairs: 4usize,
        base_field_oracles: AlignedColumnSet::<1usize> {
            start: 0usize,
            num_elements: 4usize,
        },
        ext_4_field_oracles: AlignedColumnSet::<4usize> {
            start: 4usize,
            num_elements: 4usize,
        },
    },
    intermediate_polys_for_generic_lookup: AlignedColumnSet::<4usize> {
        start: 20usize,
        num_elements: 4usize,
    },
    intermediate_poly_for_decoder_accesses: AlignedColumnSet::<4usize> {
        start: 36usize,
        num_elements: 1usize,
    },
    intermediate_poly_for_range_check_16_multiplicity: AlignedColumnSet::<4usize> {
        start: 40usize,
        num_elements: 1usize,
    },
    intermediate_poly_for_timestamp_range_check_multiplicity: AlignedColumnSet::<4usize> {
        start: 44usize,
        num_elements: 1usize,
    },
    intermediate_polys_for_generic_multiplicities: AlignedColumnSet::<4usize> {
        start: 48usize,
        num_elements: 1usize,
    },
    intermediate_polys_for_decoder_multiplicities: AlignedColumnSet::<4usize> {
        start: 52usize,
        num_elements: 1usize,
    },
    delegation_processing_aux_poly: Some(AlignedColumnSet::<4usize> {
        start: 56usize,
        num_elements: 1usize,
    }),
    intermediate_polys_for_memory_init_teardown: AlignedColumnSet::<4usize> {
        start: 80usize,
        num_elements: 0usize,
    },
    intermediate_polys_for_memory_argument: AlignedColumnSet::<4usize> {
        start: 60usize,
        num_elements: 3usize,
    },
    intermediate_polys_for_state_permutation: AlignedColumnSet::<4usize> {
        start: 72usize,
        num_elements: 1usize,
    },
    intermediate_polys_for_permutation_masking: AlignedColumnSet::<4usize> {
        start: 76usize,
        num_elements: 1usize,
    },
    intermediate_poly_for_grand_product: AlignedColumnSet::<4usize> {
        start: 80usize,
        num_elements: 1usize,
    },
    ext4_polys_offset: 4usize,
    total_width: 84usize,
};
pub const VERIFIER_COMPILED_LAYOUT: VerifierCompiledCircuitArtifact<'static, Mersenne31Field> =
    VerifierCompiledCircuitArtifact {
        witness_layout: COMPILED_WITNESS_LAYOUT,
        memory_layout: COMPILED_MEMORY_LAYOUT,
        setup_layout: COMPILED_SETUP_LAYOUT,
        stage_2_layout: COMPILED_STAGE_2_LAYOUT,
        degree_2_constraints: &[
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(9usize),
                    ColumnAddress::WitnessSubtree(9usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(9usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(10usize),
                    ColumnAddress::WitnessSubtree(10usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(10usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(11usize),
                    ColumnAddress::WitnessSubtree(11usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(11usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(12usize),
                    ColumnAddress::WitnessSubtree(12usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(12usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(13usize),
                    ColumnAddress::WitnessSubtree(13usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(13usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(14usize),
                    ColumnAddress::WitnessSubtree(14usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(14usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(15usize),
                    ColumnAddress::WitnessSubtree(15usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(15usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(16usize),
                    ColumnAddress::WitnessSubtree(16usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(16usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(17usize),
                    ColumnAddress::WitnessSubtree(17usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(17usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(18usize),
                    ColumnAddress::WitnessSubtree(18usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(18usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(19usize),
                    ColumnAddress::WitnessSubtree(19usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(19usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(20usize),
                    ColumnAddress::WitnessSubtree(20usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(20usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(1usize),
                        ColumnAddress::WitnessSubtree(14usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(14usize),
                        ColumnAddress::MemorySubtree(7usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(37usize),
                    ),
                    (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(7usize)),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(2usize),
                        ColumnAddress::WitnessSubtree(14usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(14usize),
                        ColumnAddress::MemorySubtree(8usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(38usize),
                    ),
                    (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(8usize)),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(13usize),
                    ColumnAddress::WitnessSubtree(39usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(13usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(13usize),
                    ColumnAddress::WitnessSubtree(40usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(17usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(1usize),
                        ColumnAddress::MemorySubtree(17usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::MemorySubtree(17usize),
                        ColumnAddress::MemorySubtree(18usize),
                    ),
                ],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(41usize),
                    ColumnAddress::MemorySubtree(17usize),
                )],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(42usize),
                    ColumnAddress::MemorySubtree(17usize),
                )],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(17usize),
                    ColumnAddress::MemorySubtree(19usize),
                )],
                linear_terms: &[(Mersenne31Field(1u32), ColumnAddress::MemorySubtree(17usize))],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(1usize),
                        ColumnAddress::WitnessSubtree(13usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(37usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(37usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(37usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(39usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(21usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(39usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(39usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(39usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(41usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(13usize),
                        ColumnAddress::WitnessSubtree(39usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(22usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(40usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(40usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(40usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(43usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(13usize),
                        ColumnAddress::WitnessSubtree(40usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(23usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(3usize),
                    ColumnAddress::WitnessSubtree(12usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(47u32),
                        ColumnAddress::WitnessSubtree(9usize),
                    ),
                    (
                        Mersenne31Field(47u32),
                        ColumnAddress::WitnessSubtree(10usize),
                    ),
                    (
                        Mersenne31Field(47u32),
                        ColumnAddress::WitnessSubtree(11usize),
                    ),
                    (
                        Mersenne31Field(25u32),
                        ColumnAddress::WitnessSubtree(13usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(24usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(65536u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(39usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                    (
                        Mersenne31Field(65536u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(39usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                    (
                        Mersenne31Field(65536u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(39usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                    (
                        Mersenne31Field(2139095039u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(39usize),
                    ),
                    (
                        Mersenne31Field(8388608u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(13usize),
                        ColumnAddress::WitnessSubtree(41usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(25usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(41usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(41usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(41usize),
                    ),
                    (
                        Mersenne31Field(8388608u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(37usize),
                    ),
                    (
                        Mersenne31Field(2139095039u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(41usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(26usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(42usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(42usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(42usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(44usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(27usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(3usize),
                    ColumnAddress::WitnessSubtree(12usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(48u32),
                        ColumnAddress::WitnessSubtree(9usize),
                    ),
                    (
                        Mersenne31Field(50u32),
                        ColumnAddress::WitnessSubtree(10usize),
                    ),
                    (
                        Mersenne31Field(16u32),
                        ColumnAddress::WitnessSubtree(11usize),
                    ),
                    (
                        Mersenne31Field(53u32),
                        ColumnAddress::WitnessSubtree(13usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(28usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(65536u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(39usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                    (
                        Mersenne31Field(65536u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(39usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                    (
                        Mersenne31Field(65536u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(39usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(40usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(13usize),
                        ColumnAddress::WitnessSubtree(42usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(29usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(43usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(43usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(43usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(42usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(30usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(44usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(44usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(44usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(45usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(31usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(3usize),
                    ColumnAddress::WitnessSubtree(12usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(49u32),
                        ColumnAddress::WitnessSubtree(9usize),
                    ),
                    (
                        Mersenne31Field(51u32),
                        ColumnAddress::WitnessSubtree(10usize),
                    ),
                    (
                        Mersenne31Field(50u32),
                        ColumnAddress::WitnessSubtree(11usize),
                    ),
                    (
                        Mersenne31Field(53u32),
                        ColumnAddress::WitnessSubtree(13usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(32usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(65536u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(39usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                    (
                        Mersenne31Field(2139095039u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(40usize),
                    ),
                    (
                        Mersenne31Field(8388608u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(33usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(45usize),
                    ),
                    (
                        Mersenne31Field(8388608u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(38usize),
                    ),
                    (
                        Mersenne31Field(2139095039u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(42usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(34usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(46usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(46usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(35usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(3usize),
                    ColumnAddress::WitnessSubtree(12usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(51u32),
                        ColumnAddress::WitnessSubtree(11usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(36usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(41usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(43usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(41usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(43usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(41usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(43usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(45usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(43usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(44usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(13usize),
                        ColumnAddress::WitnessSubtree(41usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(47usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(42usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(44usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(42usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(44usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(42usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(44usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(46usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(45usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(46usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(13usize),
                        ColumnAddress::WitnessSubtree(42usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(48usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(0usize),
                    ColumnAddress::WitnessSubtree(47usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(47usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::MemorySubtree(15usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(0usize),
                    ColumnAddress::WitnessSubtree(48usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(48usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::MemorySubtree(16usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(15usize),
                    ColumnAddress::MemorySubtree(20usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147418115u32),
                    ColumnAddress::WitnessSubtree(15usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(49usize),
                    ColumnAddress::MemorySubtree(20usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(15usize),
                    ),
                    (
                        Mersenne31Field(2147418115u32),
                        ColumnAddress::WitnessSubtree(49usize),
                    ),
                ],
                constant_term: Mersenne31Field(2147483646u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(15usize),
                    ColumnAddress::MemorySubtree(20usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(2147483643u32),
                        ColumnAddress::WitnessSubtree(15usize),
                    ),
                    (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(20usize)),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::MemorySubtree(24usize),
                    ),
                ],
                constant_term: Mersenne31Field(4u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(15usize),
                        ColumnAddress::WitnessSubtree(16usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(16usize),
                        ColumnAddress::MemorySubtree(21usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147418111u32),
                    ColumnAddress::WitnessSubtree(16usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(15usize),
                        ColumnAddress::WitnessSubtree(50usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(50usize),
                        ColumnAddress::MemorySubtree(21usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(16usize),
                    ),
                    (
                        Mersenne31Field(2147418111u32),
                        ColumnAddress::WitnessSubtree(50usize),
                    ),
                ],
                constant_term: Mersenne31Field(2147483646u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(15usize),
                        ColumnAddress::WitnessSubtree(16usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(16usize),
                        ColumnAddress::MemorySubtree(21usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(15usize),
                    ),
                    (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(21usize)),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::MemorySubtree(25usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
        ],
        degree_1_constraints: &[StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(4usize),
                ),
                (Mersenne31Field(1u32), ColumnAddress::WitnessSubtree(9usize)),
                (
                    Mersenne31Field(2u32),
                    ColumnAddress::WitnessSubtree(10usize),
                ),
                (
                    Mersenne31Field(4u32),
                    ColumnAddress::WitnessSubtree(11usize),
                ),
                (
                    Mersenne31Field(8u32),
                    ColumnAddress::WitnessSubtree(12usize),
                ),
                (
                    Mersenne31Field(16u32),
                    ColumnAddress::WitnessSubtree(13usize),
                ),
                (
                    Mersenne31Field(32u32),
                    ColumnAddress::WitnessSubtree(14usize),
                ),
            ],
            constant_term: Mersenne31Field(0u32),
        }],
        state_linkage_constraints: &[],
        public_inputs: &[],
        lazy_init_address_aux_vars: &[],
        trace_len_log2: 24usize,
    };
