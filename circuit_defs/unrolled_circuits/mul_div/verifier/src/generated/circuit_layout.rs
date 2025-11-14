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
        start: 21usize,
        num_elements: 8usize,
    },
    width_3_lookups: &[
        VerifierCompiledLookupSetDescription {
            input_columns: [
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(9usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(10usize)),
                VerifierCompiledLookupExpression::Expression(
                    StaticVerifierCompiledDegree1Constraint {
                        linear_terms: &[],
                        constant_term: Mersenne31Field(0u32),
                    },
                ),
            ],
            table_index: TableIndex::Constant(TableType::RangeCheckSmall),
        },
        VerifierCompiledLookupSetDescription {
            input_columns: [
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(11usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(12usize)),
                VerifierCompiledLookupExpression::Expression(
                    StaticVerifierCompiledDegree1Constraint {
                        linear_terms: &[],
                        constant_term: Mersenne31Field(0u32),
                    },
                ),
            ],
            table_index: TableIndex::Constant(TableType::RangeCheckSmall),
        },
        VerifierCompiledLookupSetDescription {
            input_columns: [
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(13usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(14usize)),
                VerifierCompiledLookupExpression::Expression(
                    StaticVerifierCompiledDegree1Constraint {
                        linear_terms: &[],
                        constant_term: Mersenne31Field(0u32),
                    },
                ),
            ],
            table_index: TableIndex::Constant(TableType::RangeCheckSmall),
        },
        VerifierCompiledLookupSetDescription {
            input_columns: [
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(15usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(16usize)),
                VerifierCompiledLookupExpression::Expression(
                    StaticVerifierCompiledDegree1Constraint {
                        linear_terms: &[],
                        constant_term: Mersenne31Field(0u32),
                    },
                ),
            ],
            table_index: TableIndex::Constant(TableType::RangeCheckSmall),
        },
        VerifierCompiledLookupSetDescription {
            input_columns: [
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(17usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(18usize)),
                VerifierCompiledLookupExpression::Expression(
                    StaticVerifierCompiledDegree1Constraint {
                        linear_terms: &[],
                        constant_term: Mersenne31Field(0u32),
                    },
                ),
            ],
            table_index: TableIndex::Constant(TableType::RangeCheckSmall),
        },
        VerifierCompiledLookupSetDescription {
            input_columns: [
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(19usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(20usize)),
                VerifierCompiledLookupExpression::Expression(
                    StaticVerifierCompiledDegree1Constraint {
                        linear_terms: &[],
                        constant_term: Mersenne31Field(0u32),
                    },
                ),
            ],
            table_index: TableIndex::Constant(TableType::RangeCheckSmall),
        },
    ],
    range_check_16_lookup_expressions: &[
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(21usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(22usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(23usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(24usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(25usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(26usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(27usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(28usize)),
    ],
    timestamp_range_check_lookup_expressions: &[
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[(Mersenne31Field(1u32), ColumnAddress::MemorySubtree(24usize))],
            constant_term: Mersenne31Field(0u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[(Mersenne31Field(1u32), ColumnAddress::MemorySubtree(25usize))],
            constant_term: Mersenne31Field(0u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (
                    Mersenne31Field(524288u32),
                    ColumnAddress::WitnessSubtree(48usize),
                ),
                (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(0usize)),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(20usize),
                ),
            ],
            constant_term: Mersenne31Field(0u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(1usize)),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(21usize),
                ),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(48usize),
                ),
            ],
            constant_term: Mersenne31Field(524288u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (
                    Mersenne31Field(524288u32),
                    ColumnAddress::WitnessSubtree(49usize),
                ),
                (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(5usize)),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(20usize),
                ),
            ],
            constant_term: Mersenne31Field(2147483646u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(6usize)),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(21usize),
                ),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(49usize),
                ),
            ],
            constant_term: Mersenne31Field(524288u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (
                    Mersenne31Field(524288u32),
                    ColumnAddress::WitnessSubtree(50usize),
                ),
                (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(10usize)),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(20usize),
                ),
            ],
            constant_term: Mersenne31Field(2147483645u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(11usize)),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(21usize),
                ),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(50usize),
                ),
            ],
            constant_term: Mersenne31Field(524288u32),
        }),
    ],
    offset_for_special_shuffle_ram_timestamps_range_check_expressions: 8usize,
    boolean_vars_columns_range: ColumnSet::<1usize> {
        start: 29usize,
        num_elements: 23usize,
    },
    scratch_space_columns_range: ColumnSet::<1usize> {
        start: 52usize,
        num_elements: 28usize,
    },
    total_width: 80usize,
};
const COMPILED_MEMORY_LAYOUT: CompiledMemorySubtree<'static> = CompiledMemorySubtree {
    shuffle_ram_inits_and_teardowns: &[],
    delegation_request_layout: None,
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
            start: 22usize,
            num_elements: 1usize,
        },
        timestamp: ColumnSet::<2usize> {
            start: 24usize,
            num_elements: 1usize,
        },
    }),
    intermediate_state_layout: Some(IntermediateStatePermutationVariables {
        pc: ColumnSet::<2usize> {
            start: 18usize,
            num_elements: 1usize,
        },
        timestamp: ColumnSet::<2usize> {
            start: 20usize,
            num_elements: 1usize,
        },
        execute: ColumnSet::<1usize> {
            start: 17usize,
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
    total_width: 26usize,
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
        num_pairs: 4usize,
        base_field_oracles: AlignedColumnSet::<1usize> {
            start: 0usize,
            num_elements: 4usize,
        },
        ext_4_field_oracles: AlignedColumnSet::<4usize> {
            start: 8usize,
            num_elements: 4usize,
        },
    },
    remainder_for_range_check_16: None,
    lazy_init_address_range_check_16: None,
    intermediate_polys_for_timestamp_range_checks: OptimizedOraclesForLookupWidth1 {
        num_pairs: 4usize,
        base_field_oracles: AlignedColumnSet::<1usize> {
            start: 4usize,
            num_elements: 4usize,
        },
        ext_4_field_oracles: AlignedColumnSet::<4usize> {
            start: 24usize,
            num_elements: 4usize,
        },
    },
    intermediate_polys_for_generic_lookup: AlignedColumnSet::<4usize> {
        start: 40usize,
        num_elements: 6usize,
    },
    intermediate_poly_for_decoder_accesses: AlignedColumnSet::<4usize> {
        start: 64usize,
        num_elements: 1usize,
    },
    intermediate_poly_for_range_check_16_multiplicity: AlignedColumnSet::<4usize> {
        start: 68usize,
        num_elements: 1usize,
    },
    intermediate_poly_for_timestamp_range_check_multiplicity: AlignedColumnSet::<4usize> {
        start: 72usize,
        num_elements: 1usize,
    },
    intermediate_polys_for_generic_multiplicities: AlignedColumnSet::<4usize> {
        start: 76usize,
        num_elements: 1usize,
    },
    intermediate_polys_for_decoder_multiplicities: AlignedColumnSet::<4usize> {
        start: 80usize,
        num_elements: 1usize,
    },
    delegation_processing_aux_poly: None,
    intermediate_polys_for_memory_init_teardown: AlignedColumnSet::<4usize> {
        start: 104usize,
        num_elements: 0usize,
    },
    intermediate_polys_for_memory_argument: AlignedColumnSet::<4usize> {
        start: 84usize,
        num_elements: 3usize,
    },
    intermediate_polys_for_state_permutation: AlignedColumnSet::<4usize> {
        start: 96usize,
        num_elements: 1usize,
    },
    intermediate_polys_for_permutation_masking: AlignedColumnSet::<4usize> {
        start: 100usize,
        num_elements: 1usize,
    },
    intermediate_poly_for_grand_product: AlignedColumnSet::<4usize> {
        start: 104usize,
        num_elements: 1usize,
    },
    ext4_polys_offset: 8usize,
    total_width: 108usize,
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
                    ColumnAddress::WitnessSubtree(29usize),
                    ColumnAddress::WitnessSubtree(29usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(29usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(30usize),
                    ColumnAddress::WitnessSubtree(30usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(30usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(31usize),
                    ColumnAddress::WitnessSubtree(31usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(31usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(32usize),
                    ColumnAddress::WitnessSubtree(32usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(32usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(33usize),
                    ColumnAddress::WitnessSubtree(33usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(33usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(34usize),
                    ColumnAddress::WitnessSubtree(34usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(34usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(35usize),
                    ColumnAddress::WitnessSubtree(35usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(35usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(36usize),
                    ColumnAddress::WitnessSubtree(36usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(36usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(37usize),
                    ColumnAddress::WitnessSubtree(37usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(37usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(38usize),
                    ColumnAddress::WitnessSubtree(38usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(38usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(39usize),
                    ColumnAddress::WitnessSubtree(39usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(39usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(40usize),
                    ColumnAddress::WitnessSubtree(40usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(40usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(41usize),
                    ColumnAddress::WitnessSubtree(41usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(41usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(42usize),
                    ColumnAddress::WitnessSubtree(42usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(42usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(43usize),
                    ColumnAddress::WitnessSubtree(43usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(43usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(44usize),
                    ColumnAddress::WitnessSubtree(44usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(44usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(45usize),
                    ColumnAddress::WitnessSubtree(45usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(45usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(46usize),
                    ColumnAddress::WitnessSubtree(46usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(46usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(47usize),
                    ColumnAddress::WitnessSubtree(47usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(47usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(48usize),
                    ColumnAddress::WitnessSubtree(48usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(48usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(49usize),
                    ColumnAddress::WitnessSubtree(49usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(49usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(50usize),
                    ColumnAddress::WitnessSubtree(50usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(50usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(51usize),
                    ColumnAddress::WitnessSubtree(51usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(51usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483645u32),
                    ColumnAddress::WitnessSubtree(33usize),
                    ColumnAddress::WitnessSubtree(34usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(33usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(34usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(52usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::WitnessSubtree(54usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(24usize),
                        ColumnAddress::WitnessSubtree(54usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(53usize),
                )],
                constant_term: Mersenne31Field(2147483646u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::WitnessSubtree(53usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(24usize),
                        ColumnAddress::WitnessSubtree(53usize),
                    ),
                ],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(52usize),
                    ColumnAddress::WitnessSubtree(53usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(52usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(55usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(25usize),
                        ColumnAddress::WitnessSubtree(57usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(26usize),
                        ColumnAddress::WitnessSubtree(57usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(56usize),
                )],
                constant_term: Mersenne31Field(2147483646u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(25usize),
                        ColumnAddress::WitnessSubtree(56usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(26usize),
                        ColumnAddress::WitnessSubtree(56usize),
                    ),
                ],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(33usize),
                    ColumnAddress::WitnessSubtree(56usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(33usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(58usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::WitnessSubtree(29usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                ],
                linear_terms: &[
                    (Mersenne31Field(1u32), ColumnAddress::WitnessSubtree(9usize)),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(10usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(24usize),
                        ColumnAddress::WitnessSubtree(29usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(12usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(33usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(55usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(33usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(59usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(25usize),
                    ColumnAddress::WitnessSubtree(29usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(60usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(26usize),
                    ColumnAddress::WitnessSubtree(29usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(61usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(29usize),
                    ColumnAddress::WitnessSubtree(58usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(62usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::WitnessSubtree(29usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(23usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(63usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(24usize),
                        ColumnAddress::WitnessSubtree(29usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(24usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(64usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(25usize),
                        ColumnAddress::WitnessSubtree(29usize),
                    ),
                    (
                        Mersenne31Field(2147418112u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(33usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(25usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(65usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(26usize),
                        ColumnAddress::WitnessSubtree(29usize),
                    ),
                    (
                        Mersenne31Field(2147418112u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(33usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(26usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(66usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(13usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(14usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(13usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(2147418111u32),
                        ColumnAddress::WitnessSubtree(17usize),
                    ),
                    (
                        Mersenne31Field(2130706431u32),
                        ColumnAddress::WitnessSubtree(35usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(60usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(63usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(15usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(16usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(14usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(15usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(13usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(14usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(13usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(17usize),
                    ),
                    (
                        Mersenne31Field(2147418111u32),
                        ColumnAddress::WitnessSubtree(18usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(35usize),
                    ),
                    (
                        Mersenne31Field(2130706431u32),
                        ColumnAddress::WitnessSubtree(36usize),
                    ),
                    (
                        Mersenne31Field(2113929215u32),
                        ColumnAddress::WitnessSubtree(37usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(61usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(64usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(65535u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(34usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(16usize),
                    ),
                    (
                        Mersenne31Field(65280u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(34usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(15usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(16usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(14usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(15usize),
                    ),
                    (
                        Mersenne31Field(65535u32),
                        ColumnAddress::WitnessSubtree(13usize),
                        ColumnAddress::WitnessSubtree(59usize),
                    ),
                    (
                        Mersenne31Field(65280u32),
                        ColumnAddress::WitnessSubtree(14usize),
                        ColumnAddress::WitnessSubtree(59usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(18usize),
                    ),
                    (
                        Mersenne31Field(2147418111u32),
                        ColumnAddress::WitnessSubtree(19usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(36usize),
                    ),
                    (
                        Mersenne31Field(512u32),
                        ColumnAddress::WitnessSubtree(37usize),
                    ),
                    (
                        Mersenne31Field(2130706431u32),
                        ColumnAddress::WitnessSubtree(38usize),
                    ),
                    (
                        Mersenne31Field(2113929215u32),
                        ColumnAddress::WitnessSubtree(39usize),
                    ),
                    (
                        Mersenne31Field(2080374783u32),
                        ColumnAddress::WitnessSubtree(40usize),
                    ),
                    (
                        Mersenne31Field(65535u32),
                        ColumnAddress::WitnessSubtree(62usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(65usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(65535u32),
                        ColumnAddress::WitnessSubtree(9usize),
                        ColumnAddress::WitnessSubtree(34usize),
                    ),
                    (
                        Mersenne31Field(65535u32),
                        ColumnAddress::WitnessSubtree(10usize),
                        ColumnAddress::WitnessSubtree(34usize),
                    ),
                    (
                        Mersenne31Field(65535u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(34usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(16usize),
                    ),
                    (
                        Mersenne31Field(65280u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(34usize),
                    ),
                    (
                        Mersenne31Field(65535u32),
                        ColumnAddress::WitnessSubtree(13usize),
                        ColumnAddress::WitnessSubtree(59usize),
                    ),
                    (
                        Mersenne31Field(65535u32),
                        ColumnAddress::WitnessSubtree(14usize),
                        ColumnAddress::WitnessSubtree(59usize),
                    ),
                    (
                        Mersenne31Field(65535u32),
                        ColumnAddress::WitnessSubtree(15usize),
                        ColumnAddress::WitnessSubtree(59usize),
                    ),
                    (
                        Mersenne31Field(65280u32),
                        ColumnAddress::WitnessSubtree(16usize),
                        ColumnAddress::WitnessSubtree(59usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(19usize),
                    ),
                    (
                        Mersenne31Field(2147418111u32),
                        ColumnAddress::WitnessSubtree(20usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(38usize),
                    ),
                    (
                        Mersenne31Field(512u32),
                        ColumnAddress::WitnessSubtree(39usize),
                    ),
                    (
                        Mersenne31Field(1024u32),
                        ColumnAddress::WitnessSubtree(40usize),
                    ),
                    (
                        Mersenne31Field(2130706431u32),
                        ColumnAddress::WitnessSubtree(41usize),
                    ),
                    (
                        Mersenne31Field(2113929215u32),
                        ColumnAddress::WitnessSubtree(42usize),
                    ),
                    (
                        Mersenne31Field(2080374783u32),
                        ColumnAddress::WitnessSubtree(43usize),
                    ),
                    (
                        Mersenne31Field(65535u32),
                        ColumnAddress::WitnessSubtree(62usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(66usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::WitnessSubtree(30usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(25usize),
                        ColumnAddress::WitnessSubtree(30usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(25usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(67usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(24usize),
                        ColumnAddress::WitnessSubtree(30usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(26usize),
                        ColumnAddress::WitnessSubtree(30usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(26usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(68usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(70usize),
                        ColumnAddress::MemorySubtree(7usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(70usize),
                        ColumnAddress::MemorySubtree(8usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(69usize),
                )],
                constant_term: Mersenne31Field(2147483646u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(69usize),
                        ColumnAddress::MemorySubtree(7usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(69usize),
                        ColumnAddress::MemorySubtree(8usize),
                    ),
                ],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(29usize),
                    ColumnAddress::WitnessSubtree(69usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(71usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(23usize),
                    ColumnAddress::WitnessSubtree(71usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147418112u32),
                    ColumnAddress::WitnessSubtree(71usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(24usize),
                    ColumnAddress::WitnessSubtree(71usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147418112u32),
                    ColumnAddress::WitnessSubtree(71usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483645u32),
                    ColumnAddress::WitnessSubtree(34usize),
                    ColumnAddress::WitnessSubtree(58usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(34usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(58usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(72usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(2u32),
                        ColumnAddress::WitnessSubtree(25usize),
                        ColumnAddress::WitnessSubtree(72usize),
                    ),
                    (
                        Mersenne31Field(2147483645u32),
                        ColumnAddress::WitnessSubtree(27usize),
                        ColumnAddress::WitnessSubtree(72usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(25usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(27usize),
                    ),
                    (
                        Mersenne31Field(2147418111u32),
                        ColumnAddress::WitnessSubtree(44usize),
                    ),
                    (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(7usize)),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(2u32),
                        ColumnAddress::WitnessSubtree(26usize),
                        ColumnAddress::WitnessSubtree(72usize),
                    ),
                    (
                        Mersenne31Field(2147483645u32),
                        ColumnAddress::WitnessSubtree(28usize),
                        ColumnAddress::WitnessSubtree(72usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(26usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(28usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(44usize),
                    ),
                    (
                        Mersenne31Field(2147418111u32),
                        ColumnAddress::WitnessSubtree(45usize),
                    ),
                    (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(8usize)),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483645u32),
                    ColumnAddress::WitnessSubtree(45usize),
                    ColumnAddress::WitnessSubtree(72usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(45usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(72usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(73usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(27usize),
                        ColumnAddress::WitnessSubtree(75usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(28usize),
                        ColumnAddress::WitnessSubtree(75usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(74usize),
                )],
                constant_term: Mersenne31Field(2147483646u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(27usize),
                        ColumnAddress::WitnessSubtree(74usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(28usize),
                        ColumnAddress::WitnessSubtree(74usize),
                    ),
                ],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(73usize),
                    ColumnAddress::WitnessSubtree(74usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(73usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(74usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(76usize),
                    ),
                ],
                constant_term: Mersenne31Field(1u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(58usize),
                        ColumnAddress::WitnessSubtree(73usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(58usize),
                        ColumnAddress::WitnessSubtree(76usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(73usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(77usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(77usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(71usize),
                        ColumnAddress::WitnessSubtree(77usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(71usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(0usize),
                    ColumnAddress::WitnessSubtree(67usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(67usize),
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
                    ColumnAddress::WitnessSubtree(68usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(68usize),
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
                    ColumnAddress::WitnessSubtree(46usize),
                    ColumnAddress::MemorySubtree(18usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147418115u32),
                    ColumnAddress::WitnessSubtree(46usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(78usize),
                    ColumnAddress::MemorySubtree(18usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(46usize),
                    ),
                    (
                        Mersenne31Field(2147418115u32),
                        ColumnAddress::WitnessSubtree(78usize),
                    ),
                ],
                constant_term: Mersenne31Field(2147483646u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(46usize),
                    ColumnAddress::MemorySubtree(18usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(2147483643u32),
                        ColumnAddress::WitnessSubtree(46usize),
                    ),
                    (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(18usize)),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::MemorySubtree(22usize),
                    ),
                ],
                constant_term: Mersenne31Field(4u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(46usize),
                        ColumnAddress::WitnessSubtree(47usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(47usize),
                        ColumnAddress::MemorySubtree(19usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147418111u32),
                    ColumnAddress::WitnessSubtree(47usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(46usize),
                        ColumnAddress::WitnessSubtree(79usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(79usize),
                        ColumnAddress::MemorySubtree(19usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(47usize),
                    ),
                    (
                        Mersenne31Field(2147418111u32),
                        ColumnAddress::WitnessSubtree(79usize),
                    ),
                ],
                constant_term: Mersenne31Field(2147483646u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(46usize),
                        ColumnAddress::WitnessSubtree(47usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(47usize),
                        ColumnAddress::MemorySubtree(19usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(46usize),
                    ),
                    (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(19usize)),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::MemorySubtree(23usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
        ],
        degree_1_constraints: &[
            StaticVerifierCompiledDegree1Constraint {
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(4usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                    ),
                    (
                        Mersenne31Field(2u32),
                        ColumnAddress::WitnessSubtree(30usize),
                    ),
                    (
                        Mersenne31Field(4u32),
                        ColumnAddress::WitnessSubtree(31usize),
                    ),
                    (
                        Mersenne31Field(8u32),
                        ColumnAddress::WitnessSubtree(32usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree1Constraint {
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(21usize),
                    ),
                    (
                        Mersenne31Field(32768u32),
                        ColumnAddress::WitnessSubtree(31usize),
                    ),
                    (
                        Mersenne31Field(2147418111u32),
                        ColumnAddress::WitnessSubtree(33usize),
                    ),
                    (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(3usize)),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree1Constraint {
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(22usize),
                    ),
                    (
                        Mersenne31Field(32768u32),
                        ColumnAddress::WitnessSubtree(32usize),
                    ),
                    (
                        Mersenne31Field(2147418111u32),
                        ColumnAddress::WitnessSubtree(34usize),
                    ),
                    (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(8usize)),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree1Constraint {
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(13usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(14usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::MemorySubtree(7usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree1Constraint {
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(15usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(16usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::MemorySubtree(8usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
        ],
        state_linkage_constraints: &[],
        public_inputs: &[],
        lazy_init_address_aux_vars: &[],
        trace_len_log2: 21usize,
    };
