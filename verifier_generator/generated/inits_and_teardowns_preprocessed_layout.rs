const COMPILED_WITNESS_LAYOUT: CompiledWitnessSubtree<Mersenne31Field> = CompiledWitnessSubtree {
    multiplicities_columns_for_range_check_16: ColumnSet::<1usize> {
        start: 0usize,
        num_elements: 1usize,
    },
    multiplicities_columns_for_timestamp_range_check: ColumnSet::<1usize> {
        start: 0usize,
        num_elements: 0usize,
    },
    multiplicities_columns_for_decoder_in_executor_families: ColumnSet::<1usize> {
        start: 0usize,
        num_elements: 0usize,
    },
    multiplicities_columns_for_generic_lookup: ColumnSet::<1usize> {
        start: 0usize,
        num_elements: 0usize,
    },
    range_check_16_columns: ColumnSet::<1usize> {
        start: 1usize,
        num_elements: 32usize,
    },
    width_3_lookups: &[],
    range_check_16_lookup_expressions: &[
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(1usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(2usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(3usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(4usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(5usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(6usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(7usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(8usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(9usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(10usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(11usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(12usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(13usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(14usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(15usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(16usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(17usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(18usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(19usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(20usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(21usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(22usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(23usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(24usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(25usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(26usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(27usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(28usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(29usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(30usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(31usize)),
        VerifierCompiledLookupExpression::Variable(ColumnAddress::WitnessSubtree(32usize)),
    ],
    timestamp_range_check_lookup_expressions: &[],
    offset_for_special_shuffle_ram_timestamps_range_check_expressions: 0usize,
    boolean_vars_columns_range: ColumnSet::<1usize> {
        start: 33usize,
        num_elements: 32usize,
    },
    scratch_space_columns_range: ColumnSet::<1usize> {
        start: 65usize,
        num_elements: 0usize,
    },
    total_width: 65usize,
};
const COMPILED_MEMORY_LAYOUT: CompiledMemorySubtree<'static> = CompiledMemorySubtree {
    shuffle_ram_inits_and_teardowns: &[
        ShuffleRamInitAndTeardownLayout {
            lazy_init_addresses_columns: ColumnSet::<2usize> {
                start: 0usize,
                num_elements: 1usize,
            },
            lazy_teardown_values_columns: ColumnSet::<2usize> {
                start: 2usize,
                num_elements: 1usize,
            },
            lazy_teardown_timestamps_columns: ColumnSet::<2usize> {
                start: 4usize,
                num_elements: 1usize,
            },
        },
        ShuffleRamInitAndTeardownLayout {
            lazy_init_addresses_columns: ColumnSet::<2usize> {
                start: 6usize,
                num_elements: 1usize,
            },
            lazy_teardown_values_columns: ColumnSet::<2usize> {
                start: 8usize,
                num_elements: 1usize,
            },
            lazy_teardown_timestamps_columns: ColumnSet::<2usize> {
                start: 10usize,
                num_elements: 1usize,
            },
        },
        ShuffleRamInitAndTeardownLayout {
            lazy_init_addresses_columns: ColumnSet::<2usize> {
                start: 12usize,
                num_elements: 1usize,
            },
            lazy_teardown_values_columns: ColumnSet::<2usize> {
                start: 14usize,
                num_elements: 1usize,
            },
            lazy_teardown_timestamps_columns: ColumnSet::<2usize> {
                start: 16usize,
                num_elements: 1usize,
            },
        },
        ShuffleRamInitAndTeardownLayout {
            lazy_init_addresses_columns: ColumnSet::<2usize> {
                start: 18usize,
                num_elements: 1usize,
            },
            lazy_teardown_values_columns: ColumnSet::<2usize> {
                start: 20usize,
                num_elements: 1usize,
            },
            lazy_teardown_timestamps_columns: ColumnSet::<2usize> {
                start: 22usize,
                num_elements: 1usize,
            },
        },
        ShuffleRamInitAndTeardownLayout {
            lazy_init_addresses_columns: ColumnSet::<2usize> {
                start: 24usize,
                num_elements: 1usize,
            },
            lazy_teardown_values_columns: ColumnSet::<2usize> {
                start: 26usize,
                num_elements: 1usize,
            },
            lazy_teardown_timestamps_columns: ColumnSet::<2usize> {
                start: 28usize,
                num_elements: 1usize,
            },
        },
        ShuffleRamInitAndTeardownLayout {
            lazy_init_addresses_columns: ColumnSet::<2usize> {
                start: 30usize,
                num_elements: 1usize,
            },
            lazy_teardown_values_columns: ColumnSet::<2usize> {
                start: 32usize,
                num_elements: 1usize,
            },
            lazy_teardown_timestamps_columns: ColumnSet::<2usize> {
                start: 34usize,
                num_elements: 1usize,
            },
        },
        ShuffleRamInitAndTeardownLayout {
            lazy_init_addresses_columns: ColumnSet::<2usize> {
                start: 36usize,
                num_elements: 1usize,
            },
            lazy_teardown_values_columns: ColumnSet::<2usize> {
                start: 38usize,
                num_elements: 1usize,
            },
            lazy_teardown_timestamps_columns: ColumnSet::<2usize> {
                start: 40usize,
                num_elements: 1usize,
            },
        },
        ShuffleRamInitAndTeardownLayout {
            lazy_init_addresses_columns: ColumnSet::<2usize> {
                start: 42usize,
                num_elements: 1usize,
            },
            lazy_teardown_values_columns: ColumnSet::<2usize> {
                start: 44usize,
                num_elements: 1usize,
            },
            lazy_teardown_timestamps_columns: ColumnSet::<2usize> {
                start: 46usize,
                num_elements: 1usize,
            },
        },
        ShuffleRamInitAndTeardownLayout {
            lazy_init_addresses_columns: ColumnSet::<2usize> {
                start: 48usize,
                num_elements: 1usize,
            },
            lazy_teardown_values_columns: ColumnSet::<2usize> {
                start: 50usize,
                num_elements: 1usize,
            },
            lazy_teardown_timestamps_columns: ColumnSet::<2usize> {
                start: 52usize,
                num_elements: 1usize,
            },
        },
        ShuffleRamInitAndTeardownLayout {
            lazy_init_addresses_columns: ColumnSet::<2usize> {
                start: 54usize,
                num_elements: 1usize,
            },
            lazy_teardown_values_columns: ColumnSet::<2usize> {
                start: 56usize,
                num_elements: 1usize,
            },
            lazy_teardown_timestamps_columns: ColumnSet::<2usize> {
                start: 58usize,
                num_elements: 1usize,
            },
        },
        ShuffleRamInitAndTeardownLayout {
            lazy_init_addresses_columns: ColumnSet::<2usize> {
                start: 60usize,
                num_elements: 1usize,
            },
            lazy_teardown_values_columns: ColumnSet::<2usize> {
                start: 62usize,
                num_elements: 1usize,
            },
            lazy_teardown_timestamps_columns: ColumnSet::<2usize> {
                start: 64usize,
                num_elements: 1usize,
            },
        },
        ShuffleRamInitAndTeardownLayout {
            lazy_init_addresses_columns: ColumnSet::<2usize> {
                start: 66usize,
                num_elements: 1usize,
            },
            lazy_teardown_values_columns: ColumnSet::<2usize> {
                start: 68usize,
                num_elements: 1usize,
            },
            lazy_teardown_timestamps_columns: ColumnSet::<2usize> {
                start: 70usize,
                num_elements: 1usize,
            },
        },
        ShuffleRamInitAndTeardownLayout {
            lazy_init_addresses_columns: ColumnSet::<2usize> {
                start: 72usize,
                num_elements: 1usize,
            },
            lazy_teardown_values_columns: ColumnSet::<2usize> {
                start: 74usize,
                num_elements: 1usize,
            },
            lazy_teardown_timestamps_columns: ColumnSet::<2usize> {
                start: 76usize,
                num_elements: 1usize,
            },
        },
        ShuffleRamInitAndTeardownLayout {
            lazy_init_addresses_columns: ColumnSet::<2usize> {
                start: 78usize,
                num_elements: 1usize,
            },
            lazy_teardown_values_columns: ColumnSet::<2usize> {
                start: 80usize,
                num_elements: 1usize,
            },
            lazy_teardown_timestamps_columns: ColumnSet::<2usize> {
                start: 82usize,
                num_elements: 1usize,
            },
        },
        ShuffleRamInitAndTeardownLayout {
            lazy_init_addresses_columns: ColumnSet::<2usize> {
                start: 84usize,
                num_elements: 1usize,
            },
            lazy_teardown_values_columns: ColumnSet::<2usize> {
                start: 86usize,
                num_elements: 1usize,
            },
            lazy_teardown_timestamps_columns: ColumnSet::<2usize> {
                start: 88usize,
                num_elements: 1usize,
            },
        },
        ShuffleRamInitAndTeardownLayout {
            lazy_init_addresses_columns: ColumnSet::<2usize> {
                start: 90usize,
                num_elements: 1usize,
            },
            lazy_teardown_values_columns: ColumnSet::<2usize> {
                start: 92usize,
                num_elements: 1usize,
            },
            lazy_teardown_timestamps_columns: ColumnSet::<2usize> {
                start: 94usize,
                num_elements: 1usize,
            },
        },
    ],
    delegation_request_layout: None,
    delegation_processor_layout: None,
    shuffle_ram_access_sets: &[],
    machine_state_layout: None,
    intermediate_state_layout: None,
    batched_ram_accesses: &[],
    register_and_indirect_accesses: &[],
    total_width: 96usize,
};
const COMPILED_SETUP_LAYOUT: SetupLayout = SetupLayout {
    timestamp_setup_columns: ColumnSet::<2usize> {
        start: 0usize,
        num_elements: 0usize,
    },
    timestamp_range_check_setup_column: ColumnSet::<1usize> {
        start: 0usize,
        num_elements: 0usize,
    },
    range_check_16_setup_column: ColumnSet::<1usize> {
        start: 0usize,
        num_elements: 1usize,
    },
    generic_lookup_setup_columns: ColumnSet::<4usize> {
        start: 1usize,
        num_elements: 0usize,
    },
    preprocessed_decoder_setup_columns: ColumnSet::<10usize> {
        start: 0usize,
        num_elements: 0usize,
    },
    total_width: 1usize,
};
const COMPILED_STAGE_2_LAYOUT: LookupAndMemoryArgumentLayout = LookupAndMemoryArgumentLayout {
    intermediate_polys_for_range_check_16: OptimizedOraclesForLookupWidth1 {
        num_pairs: 16usize,
        base_field_oracles: AlignedColumnSet::<1usize> {
            start: 0usize,
            num_elements: 16usize,
        },
        ext_4_field_oracles: AlignedColumnSet::<4usize> {
            start: 32usize,
            num_elements: 16usize,
        },
    },
    remainder_for_range_check_16: None,
    lazy_init_address_range_check_16: Some(OptimizedOraclesForLookupWidth1 {
        num_pairs: 16usize,
        base_field_oracles: AlignedColumnSet::<1usize> {
            start: 16usize,
            num_elements: 16usize,
        },
        ext_4_field_oracles: AlignedColumnSet::<4usize> {
            start: 96usize,
            num_elements: 16usize,
        },
    }),
    intermediate_polys_for_timestamp_range_checks: OptimizedOraclesForLookupWidth1 {
        num_pairs: 0usize,
        base_field_oracles: AlignedColumnSet::<1usize> {
            start: 32usize,
            num_elements: 0usize,
        },
        ext_4_field_oracles: AlignedColumnSet::<4usize> {
            start: 160usize,
            num_elements: 0usize,
        },
    },
    intermediate_polys_for_generic_lookup: AlignedColumnSet::<4usize> {
        start: 160usize,
        num_elements: 0usize,
    },
    intermediate_poly_for_decoder_accesses: AlignedColumnSet::<4usize> {
        start: 0usize,
        num_elements: 0usize,
    },
    intermediate_poly_for_range_check_16_multiplicity: AlignedColumnSet::<4usize> {
        start: 160usize,
        num_elements: 1usize,
    },
    intermediate_poly_for_timestamp_range_check_multiplicity: AlignedColumnSet::<4usize> {
        start: 0usize,
        num_elements: 0usize,
    },
    intermediate_polys_for_generic_multiplicities: AlignedColumnSet::<4usize> {
        start: 0usize,
        num_elements: 0usize,
    },
    intermediate_polys_for_decoder_multiplicities: AlignedColumnSet::<4usize> {
        start: 0usize,
        num_elements: 0usize,
    },
    delegation_processing_aux_poly: None,
    intermediate_polys_for_memory_init_teardown: AlignedColumnSet::<4usize> {
        start: 164usize,
        num_elements: 16usize,
    },
    intermediate_polys_for_memory_argument: AlignedColumnSet::<4usize> {
        start: 0usize,
        num_elements: 0usize,
    },
    intermediate_polys_for_state_permutation: AlignedColumnSet::<4usize> {
        start: 0usize,
        num_elements: 0usize,
    },
    intermediate_polys_for_permutation_masking: AlignedColumnSet::<4usize> {
        start: 0usize,
        num_elements: 0usize,
    },
    intermediate_poly_for_grand_product: AlignedColumnSet::<4usize> {
        start: 228usize,
        num_elements: 1usize,
    },
    ext4_polys_offset: 32usize,
    total_width: 232usize,
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
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(52usize),
                    ColumnAddress::WitnessSubtree(52usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(52usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(53usize),
                    ColumnAddress::WitnessSubtree(53usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(53usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(54usize),
                    ColumnAddress::WitnessSubtree(54usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(54usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(55usize),
                    ColumnAddress::WitnessSubtree(55usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(55usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(56usize),
                    ColumnAddress::WitnessSubtree(56usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(56usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(57usize),
                    ColumnAddress::WitnessSubtree(57usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(57usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(58usize),
                    ColumnAddress::WitnessSubtree(58usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(58usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(59usize),
                    ColumnAddress::WitnessSubtree(59usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(59usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(60usize),
                    ColumnAddress::WitnessSubtree(60usize),
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
                    ColumnAddress::WitnessSubtree(61usize),
                    ColumnAddress::WitnessSubtree(61usize),
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
                    ColumnAddress::WitnessSubtree(62usize),
                    ColumnAddress::WitnessSubtree(62usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(62usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(63usize),
                    ColumnAddress::WitnessSubtree(63usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(63usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
            StaticVerifierCompiledDegree2Constraint {
                quadratic_terms: &[(
                    Mersenne31Field(1u32),
                    ColumnAddress::WitnessSubtree(64usize),
                    ColumnAddress::WitnessSubtree(64usize),
                )],
                linear_terms: &[(
                    Mersenne31Field(2147483646u32),
                    ColumnAddress::WitnessSubtree(64usize),
                )],
                constant_term: Mersenne31Field(0u32),
            },
        ],
        degree_1_constraints: &[],
        state_linkage_constraints: &[],
        public_inputs: &[],
        lazy_init_address_aux_vars: &[
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(1usize),
                    ColumnAddress::WitnessSubtree(2usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(33usize),
                final_borrow: ColumnAddress::WitnessSubtree(34usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(3usize),
                    ColumnAddress::WitnessSubtree(4usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(35usize),
                final_borrow: ColumnAddress::WitnessSubtree(36usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(5usize),
                    ColumnAddress::WitnessSubtree(6usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(37usize),
                final_borrow: ColumnAddress::WitnessSubtree(38usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(7usize),
                    ColumnAddress::WitnessSubtree(8usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(39usize),
                final_borrow: ColumnAddress::WitnessSubtree(40usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(9usize),
                    ColumnAddress::WitnessSubtree(10usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(41usize),
                final_borrow: ColumnAddress::WitnessSubtree(42usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(11usize),
                    ColumnAddress::WitnessSubtree(12usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(43usize),
                final_borrow: ColumnAddress::WitnessSubtree(44usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(13usize),
                    ColumnAddress::WitnessSubtree(14usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(45usize),
                final_borrow: ColumnAddress::WitnessSubtree(46usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(15usize),
                    ColumnAddress::WitnessSubtree(16usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(47usize),
                final_borrow: ColumnAddress::WitnessSubtree(48usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(17usize),
                    ColumnAddress::WitnessSubtree(18usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(49usize),
                final_borrow: ColumnAddress::WitnessSubtree(50usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(19usize),
                    ColumnAddress::WitnessSubtree(20usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(51usize),
                final_borrow: ColumnAddress::WitnessSubtree(52usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(21usize),
                    ColumnAddress::WitnessSubtree(22usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(53usize),
                final_borrow: ColumnAddress::WitnessSubtree(54usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(23usize),
                    ColumnAddress::WitnessSubtree(24usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(55usize),
                final_borrow: ColumnAddress::WitnessSubtree(56usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(25usize),
                    ColumnAddress::WitnessSubtree(26usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(57usize),
                final_borrow: ColumnAddress::WitnessSubtree(58usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(27usize),
                    ColumnAddress::WitnessSubtree(28usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(59usize),
                final_borrow: ColumnAddress::WitnessSubtree(60usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(29usize),
                    ColumnAddress::WitnessSubtree(30usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(61usize),
                final_borrow: ColumnAddress::WitnessSubtree(62usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(31usize),
                    ColumnAddress::WitnessSubtree(32usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(63usize),
                final_borrow: ColumnAddress::WitnessSubtree(64usize),
            },
        ],
        trace_len_log2: 24usize,
    };
