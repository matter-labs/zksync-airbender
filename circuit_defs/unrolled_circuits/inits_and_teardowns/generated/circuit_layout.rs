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
        num_elements: 12usize,
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
    ],
    timestamp_range_check_lookup_expressions: &[],
    offset_for_special_shuffle_ram_timestamps_range_check_expressions: 0usize,
    boolean_vars_columns_range: ColumnSet::<1usize> {
        start: 13usize,
        num_elements: 12usize,
    },
    scratch_space_columns_range: ColumnSet::<1usize> {
        start: 25usize,
        num_elements: 0usize,
    },
    total_width: 25usize,
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
    ],
    delegation_request_layout: None,
    delegation_processor_layout: None,
    shuffle_ram_access_sets: &[],
    machine_state_layout: None,
    intermediate_state_layout: None,
    batched_ram_accesses: &[],
    register_and_indirect_accesses: &[],
    total_width: 36usize,
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
        num_pairs: 6usize,
        base_field_oracles: AlignedColumnSet::<1usize> {
            start: 0usize,
            num_elements: 6usize,
        },
        ext_4_field_oracles: AlignedColumnSet::<4usize> {
            start: 12usize,
            num_elements: 6usize,
        },
    },
    remainder_for_range_check_16: None,
    lazy_init_address_range_check_16: Some(OptimizedOraclesForLookupWidth1 {
        num_pairs: 6usize,
        base_field_oracles: AlignedColumnSet::<1usize> {
            start: 6usize,
            num_elements: 6usize,
        },
        ext_4_field_oracles: AlignedColumnSet::<4usize> {
            start: 36usize,
            num_elements: 6usize,
        },
    }),
    intermediate_polys_for_timestamp_range_checks: OptimizedOraclesForLookupWidth1 {
        num_pairs: 0usize,
        base_field_oracles: AlignedColumnSet::<1usize> {
            start: 12usize,
            num_elements: 0usize,
        },
        ext_4_field_oracles: AlignedColumnSet::<4usize> {
            start: 60usize,
            num_elements: 0usize,
        },
    },
    intermediate_polys_for_generic_lookup: AlignedColumnSet::<4usize> {
        start: 60usize,
        num_elements: 0usize,
    },
    intermediate_poly_for_decoder_accesses: AlignedColumnSet::<4usize> {
        start: 0usize,
        num_elements: 0usize,
    },
    intermediate_poly_for_range_check_16_multiplicity: AlignedColumnSet::<4usize> {
        start: 60usize,
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
        start: 64usize,
        num_elements: 6usize,
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
        start: 88usize,
        num_elements: 1usize,
    },
    ext4_polys_offset: 12usize,
    total_width: 92usize,
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
                intermediate_borrow: ColumnAddress::WitnessSubtree(13usize),
                final_borrow: ColumnAddress::WitnessSubtree(14usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(3usize),
                    ColumnAddress::WitnessSubtree(4usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(15usize),
                final_borrow: ColumnAddress::WitnessSubtree(16usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(5usize),
                    ColumnAddress::WitnessSubtree(6usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(17usize),
                final_borrow: ColumnAddress::WitnessSubtree(18usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(7usize),
                    ColumnAddress::WitnessSubtree(8usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(19usize),
                final_borrow: ColumnAddress::WitnessSubtree(20usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(9usize),
                    ColumnAddress::WitnessSubtree(10usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(21usize),
                final_borrow: ColumnAddress::WitnessSubtree(22usize),
            },
            ShuffleRamAuxComparisonSet {
                aux_low_high: [
                    ColumnAddress::WitnessSubtree(11usize),
                    ColumnAddress::WitnessSubtree(12usize),
                ],
                intermediate_borrow: ColumnAddress::WitnessSubtree(23usize),
                final_borrow: ColumnAddress::WitnessSubtree(24usize),
            },
        ],
        trace_len_log2: 24usize,
    };
