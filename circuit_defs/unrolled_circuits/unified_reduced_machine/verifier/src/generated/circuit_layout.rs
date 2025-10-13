const COMPILED_WITNESS_LAYOUT: CompiledWitnessSubtree<Mersenne31Field> = CompiledWitnessSubtree {
    multiplicities_columns_for_range_check_16: ColumnSet::<1usize> {
        start: 7usize,
        num_elements: 1usize,
    },
    multiplicities_columns_for_timestamp_range_check: ColumnSet::<1usize> {
        start: 8usize,
        num_elements: 1usize,
    },
    multiplicities_columns_for_decoder_in_executor_families: ColumnSet::<1usize> {
        start: 9usize,
        num_elements: 1usize,
    },
    multiplicities_columns_for_generic_lookup: ColumnSet::<1usize> {
        start: 10usize,
        num_elements: 1usize,
    },
    range_check_16_columns: ColumnSet::<1usize> {
        start: 11usize,
        num_elements: 6usize,
    },
    width_3_lookups: &[
        VerifierCompiledLookupSetDescription {
            input_columns: [
                VerifierCompiledLookupExpression::Variable(ColumnAddress::MemorySubtree(3usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(46usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(47usize)),
            ],
            table_index: TableIndex::Constant(TableType::U16GetSignAndHighByte),
        },
        VerifierCompiledLookupSetDescription {
            input_columns: [
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(48usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(49usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(50usize)),
            ],
            table_index: TableIndex::Constant(TableType::U16GetSignAndHighByte),
        },
        VerifierCompiledLookupSetDescription {
            input_columns: [
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(51usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(52usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(53usize)),
            ],
            table_index: TableIndex::Variable(ColumnAddress::WitnessSubtree(54usize)),
        },
        VerifierCompiledLookupSetDescription {
            input_columns: [
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(55usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(56usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(57usize)),
            ],
            table_index: TableIndex::Variable(ColumnAddress::WitnessSubtree(58usize)),
        },
        VerifierCompiledLookupSetDescription {
            input_columns: [
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(59usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(60usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(61usize)),
            ],
            table_index: TableIndex::Variable(ColumnAddress::WitnessSubtree(62usize)),
        },
        VerifierCompiledLookupSetDescription {
            input_columns: [
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(63usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(64usize)),
                VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(65usize)),
            ],
            table_index: TableIndex::Variable(ColumnAddress::WitnessSubtree(66usize)),
        },
    ],
    range_check_16_lookup_expressions: &[
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(11usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(12usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(13usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(14usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(15usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(16usize)),
    ],
    timestamp_range_check_lookup_expressions: &[
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[(Mersenne31Field(1u32), ColumnAddress::MemorySubtree(31usize))],
            constant_term: Mersenne31Field(0u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[(Mersenne31Field(1u32), ColumnAddress::MemorySubtree(32usize))],
            constant_term: Mersenne31Field(0u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (
                    Mersenne31Field(524288u32),
                    ColumnAddress::WitnessSubtree(42usize),
                ),
                (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(0usize)),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(27usize),
                ),
            ],
            constant_term: Mersenne31Field(0u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(1usize)),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(28usize),
                ),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(42usize),
                ),
            ],
            constant_term: Mersenne31Field(524288u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (
                    Mersenne31Field(524288u32),
                    ColumnAddress::WitnessSubtree(43usize),
                ),
                (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(5usize)),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(27usize),
                ),
            ],
            constant_term: Mersenne31Field(2147483646u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(6usize)),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(28usize),
                ),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(43usize),
                ),
            ],
            constant_term: Mersenne31Field(524288u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (
                    Mersenne31Field(524288u32),
                    ColumnAddress::WitnessSubtree(44usize),
                ),
                (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(12usize)),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(27usize),
                ),
            ],
            constant_term: Mersenne31Field(2147483645u32),
        }),
        VerifierCompiledLookupExpression::Expression(StaticVerifierCompiledDegree1Constraint {
            linear_terms: &[
                (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(13usize)),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(28usize),
                ),
                (
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(44usize),
                ),
            ],
            constant_term: Mersenne31Field(524288u32),
        }),
    ],
    offset_for_special_shuffle_ram_timestamps_range_check_expressions: 8usize,
    boolean_vars_columns_range: ColumnSet::<1usize> {
        start: 17usize,
        num_elements: 29usize,
    },
    scratch_space_columns_range: ColumnSet::<1usize> {
        start: 67usize,
        num_elements: 35usize,
    },
    total_width: 102usize,
};
const COMPILED_MEMORY_LAYOUT: CompiledMemorySubtree<'static> = CompiledMemorySubtree {
    shuffle_ram_inits_and_teardowns: &[],
    delegation_request_layout: Some(DelegationRequestLayout {
        multiplicity: ColumnSet::<1usize> {
            start: 21usize,
            num_elements: 1usize,
        },
        delegation_type: ColumnSet::<1usize> {
            start: 22usize,
            num_elements: 1usize,
        },
        abi_mem_offset_high: ColumnSet::<1usize> {
            start: 23usize,
            num_elements: 1usize,
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
            address: ShuffleRamAddress::RegisterOrRam(RegisterOrRamAccessAddress {
                is_register: ColumnSet::<1usize> {
                    start: 9usize,
                    num_elements: 1usize,
                },
                address: ColumnSet::<2usize> {
                    start: 10usize,
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
            address: ShuffleRamAddress::RegisterOrRam(RegisterOrRamAccessAddress {
                is_register: ColumnSet::<1usize> {
                    start: 16usize,
                    num_elements: 1usize,
                },
                address: ColumnSet::<2usize> {
                    start: 17usize,
                    num_elements: 1usize,
                },
            }),
            read_timestamp: ColumnSet::<2usize> {
                start: 12usize,
                num_elements: 1usize,
            },
            read_value: ColumnSet::<2usize> {
                start: 14usize,
                num_elements: 1usize,
            },
            write_value: ColumnSet::<2usize> {
                start: 19usize,
                num_elements: 1usize,
            },
        }),
    ],
    machine_state_layout: Some(MachineStatePermutationVariables {
        pc: ColumnSet::<2usize> {
            start: 29usize,
            num_elements: 1usize,
        },
        timestamp: ColumnSet::<2usize> {
            start: 31usize,
            num_elements: 1usize,
        },
    }),
    intermediate_state_layout: Some(IntermediateStatePermutationVariables {
        pc: ColumnSet::<2usize> {
            start: 25usize,
            num_elements: 1usize,
        },
        timestamp: ColumnSet::<2usize> {
            start: 27usize,
            num_elements: 1usize,
        },
        execute: ColumnSet::<1usize> {
            start: 24usize,
            num_elements: 1usize,
        },
        rs1_index: ColumnSet::<1usize> {
            start: 4usize,
            num_elements: 1usize,
        },
        rs2_index: ColumnAddress::WitnessSubtree(0usize),
        rd_index: ColumnAddress::WitnessSubtree(1usize),
        decoder_witness_is_in_memory: false,
        rd_is_zero: ColumnSet::<1usize> {
            start: 2usize,
            num_elements: 1usize,
        },
        imm: ColumnSet::<2usize> {
            start: 3usize,
            num_elements: 1usize,
        },
        funct3: ColumnSet::<1usize> {
            start: 5usize,
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
        circuit_family_extra_mask: ColumnAddress::WitnessSubtree(6usize),
    }),
    batched_ram_accesses: &[],
    register_and_indirect_accesses: &[],
    total_width: 33usize,
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
        num_pairs: 3usize,
        base_field_oracles: AlignedColumnSet::<1usize> {
            start: 0usize,
            num_elements: 3usize,
        },
        ext_4_field_oracles: AlignedColumnSet::<4usize> {
            start: 8usize,
            num_elements: 3usize,
        },
    },
    remainder_for_range_check_16: None,
    lazy_init_address_range_check_16: None,
    intermediate_polys_for_timestamp_range_checks: OptimizedOraclesForLookupWidth1 {
        num_pairs: 4usize,
        base_field_oracles: AlignedColumnSet::<1usize> {
            start: 3usize,
            num_elements: 4usize,
        },
        ext_4_field_oracles: AlignedColumnSet::<4usize> {
            start: 20usize,
            num_elements: 4usize,
        },
    },
    intermediate_polys_for_generic_lookup: AlignedColumnSet::<4usize> {
        start: 36usize,
        num_elements: 6usize,
    },
    intermediate_poly_for_decoder_accesses: AlignedColumnSet::<4usize> {
        start: 60usize,
        num_elements: 1usize,
    },
    intermediate_poly_for_range_check_16_multiplicity: AlignedColumnSet::<4usize> {
        start: 64usize,
        num_elements: 1usize,
    },
    intermediate_poly_for_timestamp_range_check_multiplicity: AlignedColumnSet::<4usize> {
        start: 68usize,
        num_elements: 1usize,
    },
    intermediate_polys_for_generic_multiplicities: AlignedColumnSet::<4usize> {
        start: 72usize,
        num_elements: 1usize,
    },
    intermediate_polys_for_decoder_multiplicities: AlignedColumnSet::<4usize> {
        start: 76usize,
        num_elements: 1usize,
    },
    delegation_processing_aux_poly: Some(AlignedColumnSet::<4usize> {
        start: 80usize,
        num_elements: 1usize,
    }),
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
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(21usize),
                    ColumnAddress::WitnessSubtree(21usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(21usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(22usize),
                    ColumnAddress::WitnessSubtree(22usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(22usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(23usize),
                    ColumnAddress::WitnessSubtree(23usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(23usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(24usize),
                    ColumnAddress::WitnessSubtree(24usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(24usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(25usize),
                    ColumnAddress::WitnessSubtree(25usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(25usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(26usize),
                    ColumnAddress::WitnessSubtree(26usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(26usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(27usize),
                    ColumnAddress::WitnessSubtree(27usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(27usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(28usize),
                    ColumnAddress::WitnessSubtree(28usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(28usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
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
                quadratic_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(3usize),
                        ColumnAddress::WitnessSubtree(18usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(18usize),
                        ColumnAddress::MemorySubtree(7usize),
                    ),
                ],
                linear_terms: &[
                    (Mersenne31Field(1u32), ColumnAddress::WitnessSubtree(3usize)),
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
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(4usize),
                        ColumnAddress::WitnessSubtree(18usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(18usize),
                        ColumnAddress::MemorySubtree(8usize),
                    ),
                ],
                linear_terms: &[
                    (Mersenne31Field(1u32), ColumnAddress::WitnessSubtree(4usize)),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(48usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(35usize),
                    ColumnAddress::MemorySubtree(25usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147418115u32),
                    ColumnAddress::WitnessSubtree(35usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(70usize),
                    ColumnAddress::MemorySubtree(25usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(35usize),
                    ),
                    (
                        Mersenne31Field(2147418115u32),
                        ColumnAddress::WitnessSubtree(70usize),
                    ),
                ],
                constant_term: Mersenne31Field(2147483646u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(35usize),
                    ColumnAddress::MemorySubtree(25usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(2147483643u32),
                        ColumnAddress::WitnessSubtree(35usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(68usize),
                    ),
                    (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(25usize)),
                ],
                constant_term: Mersenne31Field(4u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(35usize),
                        ColumnAddress::WitnessSubtree(36usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(36usize),
                        ColumnAddress::MemorySubtree(26usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147418111u32),
                    ColumnAddress::WitnessSubtree(36usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(35usize),
                        ColumnAddress::WitnessSubtree(71usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(71usize),
                        ColumnAddress::MemorySubtree(26usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(36usize),
                    ),
                    (
                        Mersenne31Field(2147418111u32),
                        ColumnAddress::WitnessSubtree(71usize),
                    ),
                ],
                constant_term: Mersenne31Field(2147483646u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(35usize),
                        ColumnAddress::WitnessSubtree(36usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(36usize),
                        ColumnAddress::MemorySubtree(26usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(35usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(69usize),
                    ),
                    (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(26usize)),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(74usize),
                    ColumnAddress::WitnessSubtree(76usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(78usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(23usize),
                    ColumnAddress::WitnessSubtree(78usize),
                )],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(13usize),
                        ColumnAddress::WitnessSubtree(76usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(68usize),
                        ColumnAddress::WitnessSubtree(76usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(68usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(79usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(14usize),
                        ColumnAddress::WitnessSubtree(76usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(69usize),
                        ColumnAddress::WitnessSubtree(76usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(69usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(80usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(33usize),
                    ColumnAddress::WitnessSubtree(81usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(75usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(82usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(33usize),
                    ColumnAddress::WitnessSubtree(76usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(76usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(77usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(83usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(32usize),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(32usize),
                        ColumnAddress::MemorySubtree(25usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(86usize),
                    ),
                    (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(2usize)),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(32usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(32usize),
                        ColumnAddress::MemorySubtree(26usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(87usize),
                    ),
                    (Mersenne31Field(1u32), ColumnAddress::MemorySubtree(3usize)),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(25usize),
                    ColumnAddress::WitnessSubtree(74usize),
                )],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(65536u32),
                        ColumnAddress::WitnessSubtree(48usize),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                    (
                        Mersenne31Field(2u32),
                        ColumnAddress::WitnessSubtree(48usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(67usize),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                    (
                        Mersenne31Field(65536u32),
                        ColumnAddress::WitnessSubtree(67usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(88usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(65536u32),
                        ColumnAddress::WitnessSubtree(32usize),
                        ColumnAddress::WitnessSubtree(48usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(32usize),
                        ColumnAddress::WitnessSubtree(67usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(32usize),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                    (
                        Mersenne31Field(65536u32),
                        ColumnAddress::WitnessSubtree(32usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(33usize),
                        ColumnAddress::WitnessSubtree(88usize),
                    ),
                    (
                        Mersenne31Field(2147418111u32),
                        ColumnAddress::WitnessSubtree(34usize),
                        ColumnAddress::WitnessSubtree(48usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(34usize),
                        ColumnAddress::WitnessSubtree(67usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(34usize),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                    (
                        Mersenne31Field(65536u32),
                        ColumnAddress::WitnessSubtree(34usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(89usize),
                    ),
                    (
                        Mersenne31Field(2147418111u32),
                        ColumnAddress::WitnessSubtree(90usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(28usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(28usize),
                        ColumnAddress::WitnessSubtree(89usize),
                    ),
                ],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(28usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(28usize),
                        ColumnAddress::WitnessSubtree(90usize),
                    ),
                ],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(28usize),
                    ColumnAddress::WitnessSubtree(37usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(28usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(27usize),
                    ColumnAddress::WitnessSubtree(74usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(27usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(91usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(27usize),
                    ColumnAddress::WitnessSubtree(74usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(92usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(91usize),
                    ColumnAddress::MemorySubtree(10usize),
                )],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(91usize),
                    ColumnAddress::MemorySubtree(11usize),
                )],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(91usize),
                    ColumnAddress::MemorySubtree(7usize),
                )],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(91usize),
                    ColumnAddress::MemorySubtree(8usize),
                )],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(92usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(92usize),
                        ColumnAddress::MemorySubtree(10usize),
                    ),
                ],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(92usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(92usize),
                        ColumnAddress::MemorySubtree(11usize),
                    ),
                ],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(0usize),
                        ColumnAddress::WitnessSubtree(27usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(27usize),
                        ColumnAddress::MemorySubtree(10usize),
                    ),
                ],
                linear_terms: &[
                    (Mersenne31Field(1u32), ColumnAddress::WitnessSubtree(0usize)),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::MemorySubtree(10usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(27usize),
                    ColumnAddress::MemorySubtree(11usize),
                )],
                linear_terms: &[(Mersenne31Field(1u32), ColumnAddress::MemorySubtree(11usize))],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(31usize),
                        ColumnAddress::WitnessSubtree(74usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(31usize),
                        ColumnAddress::WitnessSubtree(75usize),
                    ),
                ],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(31usize),
                    ColumnAddress::WitnessSubtree(76usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(31usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(31usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(31usize),
                        ColumnAddress::MemorySubtree(17usize),
                    ),
                ],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(31usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(31usize),
                        ColumnAddress::MemorySubtree(18usize),
                    ),
                ],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(31usize),
                        ColumnAddress::WitnessSubtree(67usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(31usize),
                        ColumnAddress::MemorySubtree(19usize),
                    ),
                ],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(31usize),
                        ColumnAddress::WitnessSubtree(48usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(31usize),
                        ColumnAddress::MemorySubtree(20usize),
                    ),
                ],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(24usize),
                    ColumnAddress::WitnessSubtree(74usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(24usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(24usize),
                    ColumnAddress::WitnessSubtree(75usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(21usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::MemorySubtree(3usize),
                    ColumnAddress::MemorySubtree(21usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(23usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(3usize),
                    ColumnAddress::MemorySubtree(21usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(22usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(15usize),
                    ColumnAddress::WitnessSubtree(75usize),
                )],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(16usize),
                    ColumnAddress::WitnessSubtree(75usize),
                )],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(3usize),
                        ColumnAddress::WitnessSubtree(21usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(3usize),
                        ColumnAddress::WitnessSubtree(25usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(3usize),
                        ColumnAddress::WitnessSubtree(27usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(3usize),
                        ColumnAddress::WitnessSubtree(31usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(20usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(21usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(23usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(25usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(27usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(28usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(30usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(31usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(13usize),
                        ColumnAddress::WitnessSubtree(28usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(20usize),
                        ColumnAddress::WitnessSubtree(67usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(20usize),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(21usize),
                        ColumnAddress::MemorySubtree(25usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::WitnessSubtree(67usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(25usize),
                        ColumnAddress::WitnessSubtree(86usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(27usize),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(30usize),
                        ColumnAddress::WitnessSubtree(67usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(30usize),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(31usize),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(65535u32),
                        ColumnAddress::WitnessSubtree(28usize),
                    ),
                    (
                        Mersenne31Field(2147418111u32),
                        ColumnAddress::WitnessSubtree(40usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(4usize),
                        ColumnAddress::WitnessSubtree(21usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(4usize),
                        ColumnAddress::WitnessSubtree(25usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(4usize),
                        ColumnAddress::WitnessSubtree(27usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(4usize),
                        ColumnAddress::WitnessSubtree(31usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(20usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(21usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(23usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(25usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(27usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(28usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(30usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(31usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(14usize),
                        ColumnAddress::WitnessSubtree(28usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(20usize),
                        ColumnAddress::WitnessSubtree(48usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(20usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(21usize),
                        ColumnAddress::MemorySubtree(26usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::WitnessSubtree(48usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(25usize),
                        ColumnAddress::WitnessSubtree(87usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(27usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(30usize),
                        ColumnAddress::WitnessSubtree(48usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(30usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(31usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(32767u32),
                        ColumnAddress::WitnessSubtree(28usize),
                    ),
                    (
                        Mersenne31Field(2147418111u32),
                        ColumnAddress::WitnessSubtree(37usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(40usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(3usize),
                        ColumnAddress::WitnessSubtree(23usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(13usize),
                        ColumnAddress::WitnessSubtree(23usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::MemorySubtree(25usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147418111u32),
                    ColumnAddress::WitnessSubtree(41usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(4usize),
                        ColumnAddress::WitnessSubtree(23usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(14usize),
                        ColumnAddress::WitnessSubtree(23usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::MemorySubtree(26usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(2147418111u32),
                        ColumnAddress::WitnessSubtree(39usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(41usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(11usize),
                    ColumnAddress::WitnessSubtree(23usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(93usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(12usize),
                    ColumnAddress::WitnessSubtree(23usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(94usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(93usize),
                        ColumnAddress::WitnessSubtree(95usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(94usize),
                        ColumnAddress::WitnessSubtree(95usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(38usize),
                )],
                constant_term: Mersenne31Field(2147483646u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(38usize),
                        ColumnAddress::WitnessSubtree(93usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(38usize),
                        ColumnAddress::WitnessSubtree(94usize),
                    ),
                ],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(3usize),
                        ColumnAddress::WitnessSubtree(24usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(25usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(31usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(27usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(13usize),
                        ColumnAddress::WitnessSubtree(23usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(72usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(73usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(51usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(73usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::WitnessSubtree(74usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(24usize),
                        ColumnAddress::WitnessSubtree(74usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(25usize),
                        ColumnAddress::WitnessSubtree(74usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(27usize),
                        ColumnAddress::WitnessSubtree(74usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(31usize),
                        ColumnAddress::WitnessSubtree(74usize),
                    ),
                ],
                linear_terms: &[
                    (
                        Mersenne31Field(31u32),
                        ColumnAddress::WitnessSubtree(29usize),
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
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(74usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::WitnessSubtree(75usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(24usize),
                        ColumnAddress::WitnessSubtree(75usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(25usize),
                        ColumnAddress::WitnessSubtree(75usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(27usize),
                        ColumnAddress::WitnessSubtree(75usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(74usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(31usize),
                        ColumnAddress::WitnessSubtree(75usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(53usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(5usize),
                    ColumnAddress::WitnessSubtree(22usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(17u32),
                        ColumnAddress::WitnessSubtree(23usize),
                    ),
                    (
                        Mersenne31Field(25u32),
                        ColumnAddress::WitnessSubtree(24usize),
                    ),
                    (
                        Mersenne31Field(17u32),
                        ColumnAddress::WitnessSubtree(25usize),
                    ),
                    (
                        Mersenne31Field(23u32),
                        ColumnAddress::WitnessSubtree(27usize),
                    ),
                    (
                        Mersenne31Field(7u32),
                        ColumnAddress::WitnessSubtree(29usize),
                    ),
                    (
                        Mersenne31Field(18u32),
                        ColumnAddress::WitnessSubtree(31usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(54usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(5usize),
                        ColumnAddress::WitnessSubtree(23usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(27usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(31usize),
                    ),
                    (
                        Mersenne31Field(2139095039u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(72usize),
                    ),
                    (
                        Mersenne31Field(8388608u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                    (
                        Mersenne31Field(8u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::WitnessSubtree(37usize),
                    ),
                    (
                        Mersenne31Field(16u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::WitnessSubtree(38usize),
                    ),
                    (
                        Mersenne31Field(32u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::WitnessSubtree(46usize),
                    ),
                    (
                        Mersenne31Field(64u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::WitnessSubtree(49usize),
                    ),
                    (
                        Mersenne31Field(65536u32),
                        ColumnAddress::WitnessSubtree(27usize),
                        ColumnAddress::WitnessSubtree(75usize),
                    ),
                    (
                        Mersenne31Field(2097152u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(33usize),
                    ),
                    (
                        Mersenne31Field(65536u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(74usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::MemorySubtree(2usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(55usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(8388608u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(67usize),
                    ),
                    (
                        Mersenne31Field(2139095039u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(73usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::WitnessSubtree(76usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(27usize),
                        ColumnAddress::WitnessSubtree(76usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(75usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(31usize),
                        ColumnAddress::WitnessSubtree(76usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(56usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(75usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::WitnessSubtree(77usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(27usize),
                        ColumnAddress::WitnessSubtree(77usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(76usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(31usize),
                        ColumnAddress::WitnessSubtree(77usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(57usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(5usize),
                    ColumnAddress::WitnessSubtree(22usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(22u32),
                        ColumnAddress::WitnessSubtree(23usize),
                    ),
                    (
                        Mersenne31Field(24u32),
                        ColumnAddress::WitnessSubtree(27usize),
                    ),
                    (
                        Mersenne31Field(37u32),
                        ColumnAddress::WitnessSubtree(29usize),
                    ),
                    (
                        Mersenne31Field(23u32),
                        ColumnAddress::WitnessSubtree(31usize),
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
                        Mersenne31Field(2147483391u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(47usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                    (
                        Mersenne31Field(2097152u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(33usize),
                    ),
                    (
                        Mersenne31Field(65536u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(74usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::MemorySubtree(3usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(59usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(48usize),
                    ),
                    (
                        Mersenne31Field(2147483391u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(50usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(77usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(60usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(76usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(81usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(61usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(5usize),
                    ColumnAddress::WitnessSubtree(22usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(37u32),
                        ColumnAddress::WitnessSubtree(29usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(62usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(47usize),
                    ),
                    (
                        Mersenne31Field(2u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(32usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(46usize),
                    ),
                    (
                        Mersenne31Field(4u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(74usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(63usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(50usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(84usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(64usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(77usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(85usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(65usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(5usize),
                    ColumnAddress::WitnessSubtree(22usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(20u32),
                        ColumnAddress::WitnessSubtree(29usize),
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
                        ColumnAddress::WitnessSubtree(3usize),
                        ColumnAddress::WitnessSubtree(26usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(20usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(21usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(28usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(11usize),
                        ColumnAddress::WitnessSubtree(30usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(15usize),
                        ColumnAddress::WitnessSubtree(24usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(74usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(75usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::WitnessSubtree(77usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(25usize),
                        ColumnAddress::WitnessSubtree(68usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(82usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(84usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(76usize),
                        ColumnAddress::WitnessSubtree(91usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(92usize),
                        ColumnAddress::MemorySubtree(7usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(96usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(4usize),
                        ColumnAddress::WitnessSubtree(26usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(20usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(21usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(28usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(30usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(16usize),
                        ColumnAddress::WitnessSubtree(24usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(76usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(77usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(25usize),
                        ColumnAddress::WitnessSubtree(69usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(83usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(85usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(77usize),
                        ColumnAddress::WitnessSubtree(91usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(92usize),
                        ColumnAddress::MemorySubtree(8usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(97usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(2usize),
                    ColumnAddress::WitnessSubtree(96usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(96usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(98usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(2usize),
                    ColumnAddress::WitnessSubtree(97usize),
                )],
                linear_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(97usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(99usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(1usize),
                        ColumnAddress::WitnessSubtree(17usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(17usize),
                        ColumnAddress::MemorySubtree(17usize),
                    ),
                ],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(17usize),
                    ColumnAddress::MemorySubtree(18usize),
                )],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(19usize),
                    ColumnAddress::MemorySubtree(17usize),
                )],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(19usize),
                    ColumnAddress::MemorySubtree(18usize),
                )],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(17usize),
                        ColumnAddress::WitnessSubtree(98usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(17usize),
                        ColumnAddress::MemorySubtree(19usize),
                    ),
                ],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(17usize),
                        ColumnAddress::WitnessSubtree(99usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(17usize),
                        ColumnAddress::MemorySubtree(20usize),
                    ),
                ],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(19usize),
                    ColumnAddress::MemorySubtree(19usize),
                )],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(19usize),
                    ColumnAddress::MemorySubtree(20usize),
                )],
                linear_terms: &[],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(20usize),
                        ColumnAddress::WitnessSubtree(68usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(21usize),
                        ColumnAddress::WitnessSubtree(68usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(68usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::WitnessSubtree(79usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(24usize),
                        ColumnAddress::WitnessSubtree(68usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(25usize),
                        ColumnAddress::WitnessSubtree(75usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(26usize),
                        ColumnAddress::WitnessSubtree(68usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(27usize),
                        ColumnAddress::WitnessSubtree(68usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(28usize),
                        ColumnAddress::WitnessSubtree(68usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(68usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(30usize),
                        ColumnAddress::WitnessSubtree(68usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(31usize),
                        ColumnAddress::WitnessSubtree(68usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(29usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(12usize),
                        ColumnAddress::WitnessSubtree(25usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(20usize),
                        ColumnAddress::WitnessSubtree(69usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(21usize),
                        ColumnAddress::WitnessSubtree(69usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(22usize),
                        ColumnAddress::WitnessSubtree(69usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(23usize),
                        ColumnAddress::WitnessSubtree(80usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(24usize),
                        ColumnAddress::WitnessSubtree(69usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(26usize),
                        ColumnAddress::WitnessSubtree(69usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(27usize),
                        ColumnAddress::WitnessSubtree(69usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(28usize),
                        ColumnAddress::WitnessSubtree(69usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(29usize),
                        ColumnAddress::WitnessSubtree(69usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(30usize),
                        ColumnAddress::WitnessSubtree(69usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(31usize),
                        ColumnAddress::WitnessSubtree(69usize),
                    ),
                ],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::MemorySubtree(30usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
        ],
        degree_1_constraints: &[
            StaticVerifierCompiledDegree1Constraint {
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(6usize),
                    ),
                    (
                        Mersenne31Field(1u32),
                        ColumnAddress::WitnessSubtree(17usize),
                    ),
                    (
                        Mersenne31Field(2u32),
                        ColumnAddress::WitnessSubtree(18usize),
                    ),
                    (
                        Mersenne31Field(4u32),
                        ColumnAddress::WitnessSubtree(19usize),
                    ),
                    (
                        Mersenne31Field(8u32),
                        ColumnAddress::WitnessSubtree(20usize),
                    ),
                    (
                        Mersenne31Field(16u32),
                        ColumnAddress::WitnessSubtree(21usize),
                    ),
                    (
                        Mersenne31Field(32u32),
                        ColumnAddress::WitnessSubtree(22usize),
                    ),
                    (
                        Mersenne31Field(64u32),
                        ColumnAddress::WitnessSubtree(23usize),
                    ),
                    (
                        Mersenne31Field(128u32),
                        ColumnAddress::WitnessSubtree(24usize),
                    ),
                    (
                        Mersenne31Field(256u32),
                        ColumnAddress::WitnessSubtree(25usize),
                    ),
                    (
                        Mersenne31Field(512u32),
                        ColumnAddress::WitnessSubtree(26usize),
                    ),
                    (
                        Mersenne31Field(1024u32),
                        ColumnAddress::WitnessSubtree(27usize),
                    ),
                    (
                        Mersenne31Field(2048u32),
                        ColumnAddress::WitnessSubtree(28usize),
                    ),
                    (
                        Mersenne31Field(4096u32),
                        ColumnAddress::WitnessSubtree(29usize),
                    ),
                    (
                        Mersenne31Field(8192u32),
                        ColumnAddress::WitnessSubtree(30usize),
                    ),
                    (
                        Mersenne31Field(16384u32),
                        ColumnAddress::WitnessSubtree(31usize),
                    ),
                    (
                        Mersenne31Field(32768u32),
                        ColumnAddress::WitnessSubtree(32usize),
                    ),
                    (
                        Mersenne31Field(65536u32),
                        ColumnAddress::WitnessSubtree(33usize),
                    ),
                    (
                        Mersenne31Field(131072u32),
                        ColumnAddress::WitnessSubtree(34usize),
                    ),
                ],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree1Constraint {
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(27usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::MemorySubtree(9usize),
                    ),
                ],
                constant_term: Mersenne31Field(1u32),
            },
            StaticVerifierCompiledDegree1Constraint {
                linear_terms: &[
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::WitnessSubtree(31usize),
                    ),
                    (
                        Mersenne31Field(2147483646u32),
                        ColumnAddress::MemorySubtree(16usize),
                    ),
                ],
                constant_term: Mersenne31Field(1u32),
            },
        ],
        state_linkage_constraints: &[],
        public_inputs: &[],
        lazy_init_address_aux_vars: &[],
        trace_len_log2: 23usize,
    };
