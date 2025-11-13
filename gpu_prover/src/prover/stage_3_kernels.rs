use super::arg_utils::*;
use super::stage_3_utils::*;
use crate::device_structures::{
    DeviceMatrixChunk, DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride,
    PtrAndStride,
};
use crate::field::{BaseField, Ext2Field, Ext4Field};
use crate::utils::WARP_SIZE;
use cs::definitions::{
    DELEGATION_ARGUMENT_CHALLENGED_IDX_FOR_TIMESTAMP_HIGH,
    DELEGATION_ARGUMENT_CHALLENGED_IDX_FOR_TIMESTAMP_LOW,
    EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH, NUM_LOOKUP_ARGUMENT_KEY_PARTS,
    NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES,
};
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use field::{Field, FieldExtension, PrimeField};
use prover::definitions::AuxArgumentsBoundaryValues;
use prover::prover_stages::cached_data::ProverCachedData;
use prover::prover_stages::stage3::AlphaPowersLayout;
use std::alloc::Allocator;
use std::mem::MaybeUninit;

type BF = BaseField;
type E2 = Ext2Field;
type E4 = Ext4Field;

cuda_kernel!(
    GenericConstraints,
    generic_constraints,
    metadata: FlattenedGenericConstraintsMetadata,
    witness_cols: PtrAndStride<BF>,
    memory_cols: PtrAndStride<BF>,
    alpha_powers: *const E4,
    quotient: MutPtrAndStride<BF>,
    log_n: u32,
);

generic_constraints!(ab_generic_constraints_kernel);

cuda_kernel!(
    DelegatedWidth3Lookups,
    delegated_width_3_lookups,
    layout: DelegatedWidth3LookupsLayout,
    witness_cols: PtrAndStride<BF>,
    memory_cols: PtrAndStride<BF>,
    stage_2_e4_cols: PtrAndStride<BF>,
    e4_helpers: *const E4,
    quotient: MutPtrAndStride<BF>,
    decompression_factor_squared: E2,
    log_n: u32,
);

delegated_width_3_lookups!(ab_delegated_width_3_lookups_kernel);

// TODO:
// Maybe the generally optimal way to express and evaluate constraints is:
//  - Each term may be quadratic or linear.
//  - Each term component may be a col or an expression.
//    - each expression may or may not have a constant term
//  - Each term may or may not have an E4 coeff.
//  - Constant terms * challenges are folded into a global sum.
//  - Per-constraint challenges are folded into E4 coeffs and stashed in the
//  helper array.
// Even with this format, we'd need substantial hardcoded CPU logic to pack each
// constraint.
cuda_kernel!(
    HardcodedConstraints,
    hardcoded_constraints,
    setup_cols: PtrAndStride<BF>,
    witness_cols: PtrAndStride<BF>,
    memory_cols: PtrAndStride<BF>,
    stage_2_bf_cols: PtrAndStride<BF>,
    stage_2_e4_cols: PtrAndStride<BF>,
    process_delegations: bool,
    handle_delegation_requests: bool,
    delegation_aux_poly_col: u32,
    delegation_challenges: DelegationChallenges,
    delegation_processing_metadata: DelegationProcessingMetadata,
    delegation_request_metadata: DelegationRequestMetadata,
    lazy_init_teardown_args_start: u32,
    memory_args_start: u32,
    grand_product_src_col: u32,
    grand_product_dst_col: u32,
    lazy_init_teardown_layouts: LazyInitTeardownLayouts,
    shuffle_ram_accesses: ShuffleRamAccesses,
    machine_state_layout: MachineStateLayout,
    mask_arg_layout: MaskArgLayout,
    process_registers_and_indirect_access: bool,
    register_and_indirect_accesses: RegisterAndIndirectAccesses,
    range_check_16_layout: RangeCheck16ArgsLayout,
    range_check_16_expressions_layout: TEMPORARYFlattenedLookupExpressionsLayout,
    timestamp_range_check_expressions_layout: TEMPORARYFlattenedLookupExpressionsLayout,
    intermediate_state_lookup_layout: IntermediateStateLookupLayout,
    expressions_for_shuffle_ram_layout: FlattenedLookupExpressionsForShuffleRamLayout,
    width_3_lookups_layout: NonDelegatedWidth3LookupsLayout,
    range_check_16_multiplicities_layout: MultiplicitiesLayout,
    timestamp_range_check_multiplicities_layout: MultiplicitiesLayout,
    decoder_lookup_multiplicities_layout: MultiplicitiesLayout,
    generic_lookup_multiplicities_layout: MultiplicitiesLayout,
    state_linkage_constraints: StateLinkageConstraints,
    boundary_constraints: BoundaryConstraints,
    alpha_powers: *const E4,
    alpha_powers_every_row_except_last_two: *const E4,
    beta_powers: *const E4,
    e4_helpers: *const E4,
    constants_times_challenges_sum: *const ConstantsTimesChallenges,
    quotient: MutPtrAndStride<BF>,
    memory_timestamp_high_from_circuit_idx: BF,
    decompression_factor: E2,
    decompression_factor_squared: E2,
    every_row_zerofier : E2,
    omega_inv: E2,
    omega_inv_squared: E2,
    is_unrolled: bool,
    log_n: u32,
);

hardcoded_constraints!(ab_hardcoded_constraints_kernel);

#[derive(Clone)]
pub struct StaticMetadata {
    alpha_powers_layout: AlphaPowersLayout,
    flat_generic_constraints_metadata: FlattenedGenericConstraintsMetadata,
    delegated_width_3_lookups_layout: DelegatedWidth3LookupsLayout,
    non_delegated_width_3_lookups_layout: NonDelegatedWidth3LookupsLayout,
    range_check_16_layout: RangeCheck16ArgsLayout,
    range_check_16_expressions_layout: TEMPORARYFlattenedLookupExpressionsLayout,
    timestamp_range_check_expressions_layout: TEMPORARYFlattenedLookupExpressionsLayout,
    intermediate_state_lookup_layout: IntermediateStateLookupLayout,
    expressions_for_shuffle_ram_layout: FlattenedLookupExpressionsForShuffleRamLayout,
    decoder_lookup_multiplicities_layout: MultiplicitiesLayout,
    generic_lookup_multiplicities_layout: MultiplicitiesLayout,
    state_linkage_constraints: StateLinkageConstraints,
    boundary_constraints: BoundaryConstraints,
    lazy_init_teardown_args_start: usize,
    memory_args_start: usize,
    grand_product_src_col: usize,
    grand_product_dst_col: usize,
    lazy_init_teardown_layouts: LazyInitTeardownLayouts,
    shuffle_ram_accesses: ShuffleRamAccesses,
    machine_state_layout: MachineStateLayout,
    mask_arg_layout: MaskArgLayout,
    range_check_16_multiplicities_layout: MultiplicitiesLayout,
    timestamp_range_check_multiplicities_layout: MultiplicitiesLayout,
    delegation_aux_poly_col: usize,
    delegation_challenges: DelegationChallenges,
    delegation_processing_metadata: DelegationProcessingMetadata,
    delegation_request_metadata: DelegationRequestMetadata,
    register_and_indirect_accesses: RegisterAndIndirectAccesses,
    num_helpers_expected: usize,
    is_unrolled: bool,
}

impl StaticMetadata {
    pub(crate) fn new(
        tau: E2,
        omega_inv: E2,
        cached_data: &ProverCachedData,
        circuit: &CompiledCircuitArtifact<BF>,
        is_unrolled: bool,
        log_n: u32,
    ) -> Self {
        let n = 1 << log_n;
        let num_stage_2_bf_cols = circuit.stage_2_layout.num_base_field_polys();
        let num_stage_2_e4_cols = circuit.stage_2_layout.num_ext4_field_polys();
        let e4_cols_offset = circuit.stage_2_layout.ext4_polys_offset;
        assert_eq!(e4_cols_offset % 4, 0);
        assert!(num_stage_2_bf_cols <= e4_cols_offset);
        assert!(e4_cols_offset - num_stage_2_bf_cols < 4);

        let ProverCachedData {
            trace_len,
            memory_timestamp_high_from_circuit_idx,
            delegation_type,
            memory_argument_challenges,
            delegation_challenges,
            process_shuffle_ram_init,
            shuffle_ram_inits_and_teardowns,
            lazy_init_address_range_check_16,
            handle_delegation_requests,
            delegation_request_layout,
            process_batch_ram_access,
            process_registers_and_indirect_access,
            delegation_processor_layout,
            process_delegations,
            delegation_processing_aux_poly,
            num_set_polys_for_memory_shuffle,
            range_check_16_multiplicities_src,
            range_check_16_multiplicities_dst,
            range_check_16_setup_column,
            timestamp_range_check_multiplicities_src,
            timestamp_range_check_multiplicities_dst,
            timestamp_range_check_setup_column,
            generic_lookup_multiplicities_src_start,
            generic_lookup_multiplicities_dst_start,
            generic_lookup_setup_columns_start,
            range_check_16_width_1_lookups_access,
            range_check_16_width_1_lookups_access_via_expressions,
            timestamp_range_check_width_1_lookups_access_via_expressions,
            timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram,
            num_stage_3_quotient_terms,
            ..
        } = cached_data.clone();

        if process_batch_ram_access {
            panic!("deprecated");
        }

        assert_eq!(trace_len, n);

        // Technically won't be needed until prepare_async_challenge_data,
        // but imo better to construct on the main thread
        let alpha_powers_layout = AlphaPowersLayout::new(circuit, num_stage_3_quotient_terms);

        let flat_generic_constraints_metadata =
            FlattenedGenericConstraintsMetadata::new(circuit, tau, omega_inv, n);
        // Hardcoded constraints
        let translate_e4_offset = |raw_col: usize| -> usize {
            assert_eq!(raw_col % 4, 0);
            assert!(raw_col >= e4_cols_offset);
            (raw_col - e4_cols_offset) / 4
        };
        let num_range_check_16_multiplicities_cols = circuit
            .witness_layout
            .multiplicities_columns_for_range_check_16
            .num_elements();
        assert_eq!(num_range_check_16_multiplicities_cols, 1);
        assert_eq!(
            num_range_check_16_multiplicities_cols,
            circuit
                .stage_2_layout
                .intermediate_poly_for_range_check_16_multiplicity
                .num_elements(),
        );
        let num_timestamp_range_check_multiplicities_cols = circuit
            .witness_layout
            .multiplicities_columns_for_timestamp_range_check
            .num_elements();
        assert!(
            (num_timestamp_range_check_multiplicities_cols == 0)
                || (num_timestamp_range_check_multiplicities_cols == 1)
        );
        assert_eq!(
            num_timestamp_range_check_multiplicities_cols,
            circuit
                .stage_2_layout
                .intermediate_poly_for_timestamp_range_check_multiplicity
                .num_elements(),
        );
        let decoder_multiplicities_src = &circuit
            .witness_layout
            .multiplicities_columns_for_decoder_in_executor_families;
        let num_decoder_multiplicities_cols = decoder_multiplicities_src.num_elements();
        let num_generic_multiplicities_cols = circuit
            .setup_layout
            .generic_lookup_setup_columns
            .num_elements();
        assert_eq!(circuit.setup_layout.generic_lookup_setup_columns.width(), 4,);
        assert_eq!(
            num_generic_multiplicities_cols,
            circuit
                .witness_layout
                .multiplicities_columns_for_generic_lookup
                .num_elements(),
        );
        assert_eq!(
            generic_lookup_setup_columns_start,
            circuit.setup_layout.generic_lookup_setup_columns.start()
        );
        let num_generic_lookup_args = circuit
            .stage_2_layout
            .intermediate_polys_for_generic_lookup
            .num_elements();
        assert_eq!(
            num_generic_multiplicities_cols > 0,
            num_generic_lookup_args > 0
        );
        if !is_unrolled {
            assert!(num_generic_lookup_args > 0);
        }
        let (delegation_aux_poly_col, delegation_challenges) =
            if handle_delegation_requests || process_delegations {
                (
                    translate_e4_offset(delegation_processing_aux_poly.start()),
                    DelegationChallenges::new(&delegation_challenges),
                )
            } else {
                (0, DelegationChallenges::default())
            };
        let delegation_request_metadata = if handle_delegation_requests {
            let memory_timestamp_high_from_circuit_idx = if is_unrolled {
                None
            } else {
                Some(memory_timestamp_high_from_circuit_idx)
            };
            DelegationRequestMetadata::new(
                circuit,
                memory_timestamp_high_from_circuit_idx,
                &delegation_request_layout,
                is_unrolled,
            )
        } else {
            DelegationRequestMetadata::default()
        };
        let delegation_processing_metadata = if process_delegations {
            assert!(!is_unrolled);
            DelegationProcessingMetadata::new(&delegation_processor_layout, delegation_type)
        } else {
            DelegationProcessingMetadata::default()
        };
        let memory_challenges = MemoryChallenges::new(&memory_argument_challenges);
        let num_memory_args = circuit
            .stage_2_layout
            .intermediate_polys_for_memory_argument
            .num_elements();
        let register_and_indirect_accesses = if process_registers_and_indirect_access {
            assert!(!process_shuffle_ram_init);
            assert_eq!(circuit.memory_layout.shuffle_ram_access_sets.len(), 0);
            let register_and_indirect_accesses =
                &circuit.memory_layout.register_and_indirect_accesses;
            assert!(register_and_indirect_accesses.len() > 0);
            let write_timestamp_col = delegation_processor_layout.write_timestamp.start();
            let mut num_intermediate_polys_for_register_accesses = 0;
            for el in register_and_indirect_accesses.iter() {
                num_intermediate_polys_for_register_accesses += 1;
                num_intermediate_polys_for_register_accesses += el.indirect_accesses.len();
            }
            assert_eq!(
                num_memory_args,
                num_intermediate_polys_for_register_accesses,
            );
            assert_eq!(num_memory_args, num_set_polys_for_memory_shuffle);
            RegisterAndIndirectAccesses::new(
                &memory_challenges,
                register_and_indirect_accesses,
                write_timestamp_col,
            )
        } else {
            RegisterAndIndirectAccesses::default()
        };

        let range_check_16_layout = RangeCheck16ArgsLayout::new(
            circuit,
            &range_check_16_width_1_lookups_access,
            &range_check_16_width_1_lookups_access_via_expressions,
            &translate_e4_offset,
        );

        let range_check_16_expressions_layout =
            if range_check_16_width_1_lookups_access_via_expressions.len() > 0 {
                // Timestamp constant terms are probably always zero.
                TEMPORARYFlattenedLookupExpressionsLayout::new(
                    &range_check_16_width_1_lookups_access_via_expressions,
                    num_stage_2_bf_cols,
                    num_stage_2_e4_cols,
                    process_shuffle_ram_init, // expect_constant_terms_are_zero
                    &translate_e4_offset,
                )
            } else {
                TEMPORARYFlattenedLookupExpressionsLayout::default()
            };

        let timestamp_range_check_expressions_layout =
            if timestamp_range_check_width_1_lookups_access_via_expressions.len() > 0 {
                // Timestamp constant terms are probably always zero.
                TEMPORARYFlattenedLookupExpressionsLayout::new(
                    &timestamp_range_check_width_1_lookups_access_via_expressions,
                    num_stage_2_bf_cols,
                    num_stage_2_e4_cols,
                    !is_unrolled, // expect_constant_terms_are_zero
                    &translate_e4_offset,
                )
            } else {
                TEMPORARYFlattenedLookupExpressionsLayout::default()
            };

        let expressions_for_shuffle_ram_layout =
            if timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram.len()
                > 0
            {
                FlattenedLookupExpressionsForShuffleRamLayout::new(
                    &timestamp_range_check_width_1_lookups_access_via_expressions_for_shuffle_ram,
                    num_stage_2_bf_cols,
                    num_stage_2_e4_cols,
                    &translate_e4_offset,
                )
            } else {
                FlattenedLookupExpressionsForShuffleRamLayout::default()
            };

        // 32-bit lazy init addresses are treated as a pair of range check 16 cols
        let lazy_init_teardown_layouts = if process_shuffle_ram_init {
            assert!(circuit.lazy_init_address_aux_vars.len() > 0);
            LazyInitTeardownLayouts::new(
                circuit,
                &lazy_init_address_range_check_16,
                &shuffle_ram_inits_and_teardowns,
                &translate_e4_offset,
            )
        } else {
            assert_eq!(circuit.lazy_init_address_aux_vars.len(), 0);
            LazyInitTeardownLayouts::default()
        };

        // Parse metadata to figure out how many "helper" values we expect
        // the later (async) call to prepare_async_challenge_data must create.
        // prepare_async_challenge data will use this value as a double-check.
        let mut num_helpers_expected: usize = 0;
        // We must assign challenges for bare range check 16s,
        // range check 16 expressions, timestamp range check expressions,
        // and timestamp range check expressions for shuffle ram
        // in the same order challenges are assigned in the CPU code.
        let mut bound = range_check_16_width_1_lookups_access.len();
        if range_check_16_expressions_layout.constant_terms_are_zero {
            bound += range_check_16_width_1_lookups_access_via_expressions.len();
        }
        // bare (non-expression) range check 16s, plus range check 16 expressions if
        // all those expressions are known not to have constant terms
        for _ in 0..bound {
            num_helpers_expected += 2;
        }
        // range check 16 expressions, if constant terms are present
        if !range_check_16_expressions_layout.constant_terms_are_zero {
            for _ in 0..range_check_16_expressions_layout.num_expression_pairs {
                num_helpers_expected += 2;
            }
        }
        // lazy init addresses range checks
        for _ in 0..lazy_init_teardown_layouts.num_init_teardown_sets {
            num_helpers_expected += 2;
        }
        // timestamp range check expressions
        if timestamp_range_check_expressions_layout.constant_terms_are_zero {
            for _ in 0..timestamp_range_check_expressions_layout.num_expression_pairs {
                num_helpers_expected += 2;
            }
        } else {
            for _ in 0..timestamp_range_check_expressions_layout.num_expression_pairs {
                num_helpers_expected += 2;
            }
        }
        // decoder table lookups
        if !is_unrolled {
            assert_eq!(num_decoder_multiplicities_cols, 0);
            assert!(circuit.memory_layout.intermediate_state_layout.is_none());
        }
        let intermediate_state_lookup_layout =
            if circuit.memory_layout.intermediate_state_layout.is_some() {
                assert_eq!(num_decoder_multiplicities_cols, 1);
                num_helpers_expected += EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH;
                IntermediateStateLookupLayout::new(circuit, &translate_e4_offset)
            } else {
                IntermediateStateLookupLayout::default()
            };
        // timestamp range check expressions for shuffle ram
        if is_unrolled {
            assert_eq!(expressions_for_shuffle_ram_layout.num_expression_pairs, 0);
        }
        for _ in 0..expressions_for_shuffle_ram_layout.num_expression_pairs {
            num_helpers_expected += 2;
        }
        let (delegated_width_3_lookups_layout, non_delegated_width_3_lookups_layout) =
            if process_delegations {
                let delegated_layout = DelegatedWidth3LookupsLayout::new(
                    circuit,
                    num_helpers_expected,
                    is_unrolled,
                    &translate_e4_offset,
                );
                let non_delegated_placeholder = NonDelegatedWidth3LookupsLayout::new_placeholder(
                    delegated_layout.num_helpers_used,
                    delegated_layout.num_lookups,
                    delegated_layout.e4_arg_cols_start,
                );
                num_helpers_expected += delegated_layout.num_helpers_used as usize;
                (delegated_layout, non_delegated_placeholder)
            } else {
                let delegated_layout = DelegatedWidth3LookupsLayout::default();
                let non_delegated_layout = if num_generic_lookup_args > 0 {
                    NonDelegatedWidth3LookupsLayout::new(
                        circuit,
                        num_helpers_expected,
                        is_unrolled,
                        &translate_e4_offset,
                    )
                } else {
                    NonDelegatedWidth3LookupsLayout::default()
                };
                num_helpers_expected += non_delegated_layout.num_helpers_used as usize;
                (delegated_layout, non_delegated_layout)
            };

        let range_check_16_multiplicities_layout = if num_range_check_16_multiplicities_cols > 0 {
            MultiplicitiesLayout {
                src_cols_start: range_check_16_multiplicities_src as u32,
                dst_cols_start: translate_e4_offset(range_check_16_multiplicities_dst) as u32,
                setup_cols_start: range_check_16_setup_column as u32,
                num_dst_cols: num_range_check_16_multiplicities_cols as u32,
            }
        } else {
            MultiplicitiesLayout::default()
        };
        num_helpers_expected += num_range_check_16_multiplicities_cols;

        let timestamp_range_check_multiplicities_layout =
            if num_timestamp_range_check_multiplicities_cols > 0 {
                MultiplicitiesLayout {
                    src_cols_start: timestamp_range_check_multiplicities_src as u32,
                    dst_cols_start: translate_e4_offset(timestamp_range_check_multiplicities_dst)
                        as u32,
                    setup_cols_start: timestamp_range_check_setup_column as u32,
                    num_dst_cols: num_timestamp_range_check_multiplicities_cols as u32,
                }
            } else {
                MultiplicitiesLayout::default()
            };
        num_helpers_expected += num_timestamp_range_check_multiplicities_cols;

        let decoder_lookup_multiplicities_layout = if num_decoder_multiplicities_cols > 0 {
            let src_cols_start = decoder_multiplicities_src.start() as u32;
            let dst_cols = &circuit
                .stage_2_layout
                .intermediate_polys_for_decoder_multiplicities;
            assert_eq!(num_decoder_multiplicities_cols, dst_cols.num_elements());
            let dst_cols_start = translate_e4_offset(dst_cols.start()) as u32;
            let setup_cols_start = circuit
                .setup_layout
                .preprocessed_decoder_setup_columns
                .start() as u32;
            MultiplicitiesLayout {
                src_cols_start,
                dst_cols_start,
                setup_cols_start,
                num_dst_cols: num_decoder_multiplicities_cols as u32,
            }
        } else {
            MultiplicitiesLayout::default()
        };
        num_helpers_expected +=
            num_decoder_multiplicities_cols * EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH;

        let generic_lookup_multiplicities_layout = if num_generic_multiplicities_cols > 0 {
            MultiplicitiesLayout {
                src_cols_start: generic_lookup_multiplicities_src_start as u32,
                dst_cols_start: translate_e4_offset(generic_lookup_multiplicities_dst_start) as u32,
                setup_cols_start: generic_lookup_setup_columns_start as u32,
                num_dst_cols: num_generic_multiplicities_cols as u32,
            }
        } else {
            MultiplicitiesLayout::default()
        };
        num_helpers_expected += num_generic_multiplicities_cols * NUM_LOOKUP_ARGUMENT_KEY_PARTS;

        if handle_delegation_requests {
            num_helpers_expected += 1 + delegation_challenges.linearization_challenges.len();
        }
        if process_delegations {
            num_helpers_expected += 1 + delegation_challenges.linearization_challenges.len();
        }
        let memory_args_start = if num_memory_args > 0 {
            let raw_memory_args_start = circuit
                .stage_2_layout
                .intermediate_polys_for_memory_argument
                .start();
            translate_e4_offset(raw_memory_args_start)
        } else {
            0
        };
        // lazy init padding constraints go before shuffle ram accesses,
        // but don't use any helpers.
        // Grand product shuffle ram contributions
        let shuffle_ram_accesses = if is_unrolled {
            assert_eq!(
                num_memory_args > 0,
                circuit.memory_layout.intermediate_state_layout.is_some(),
            );
            assert_eq!(
                num_memory_args > 0,
                circuit.memory_layout.shuffle_ram_access_sets.len() > 0,
            );
            if num_memory_args > 0 {
                ShuffleRamAccesses::new(circuit, true)
            } else {
                ShuffleRamAccesses::default() // lazy inits and teardowns circuit
            }
        } else if process_shuffle_ram_init {
            ShuffleRamAccesses::new(circuit, false)
        } else {
            ShuffleRamAccesses::default()
        };
        let mut arg_prev_is_initialized: bool = false;
        for i in 0..shuffle_ram_accesses.num_accesses as usize {
            let access = &shuffle_ram_accesses.accesses[i];
            num_helpers_expected += 1;
            if !access.is_register_only {
                num_helpers_expected += 1;
            }
            num_helpers_expected += 5;
            if !arg_prev_is_initialized {
                arg_prev_is_initialized = true;
            } else {
                num_helpers_expected += 1;
            }
        }
        // Grand product machine state contributions
        let machine_state_layout = if circuit
            .stage_2_layout
            .intermediate_polys_for_state_permutation
            .num_elements()
            > 0
        {
            num_helpers_expected += NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES;
            if !arg_prev_is_initialized {
                arg_prev_is_initialized = true;
            }
            num_helpers_expected += 1;
            MachineStateLayout::new(circuit, &translate_e4_offset)
        } else {
            MachineStateLayout::default()
        };
        // Grand product masking contributions (no helper used)
        let mask_arg_layout = MaskArgLayout::new(circuit, &translate_e4_offset);
        if mask_arg_layout.process_mask {
            assert!(is_unrolled);
            assert!(arg_prev_is_initialized);
        }
        // Grand product lazy init and teardown contributions
        assert_eq!(
            circuit
                .stage_2_layout
                .intermediate_polys_for_memory_init_teardown
                .num_elements(),
            lazy_init_teardown_layouts.num_init_teardown_sets as usize,
        );
        if is_unrolled && lazy_init_teardown_layouts.num_init_teardown_sets > 0 {
            assert!(!arg_prev_is_initialized);
        }
        let raw_lazy_init_teardown_args_start = circuit
            .stage_2_layout
            .intermediate_polys_for_memory_init_teardown
            .start();
        let lazy_init_teardown_args_start = translate_e4_offset(raw_lazy_init_teardown_args_start);
        for _i in 0..lazy_init_teardown_layouts.num_init_teardown_sets as usize {
            num_helpers_expected += 7;
            arg_prev_is_initialized = true;
        }
        // At this point, process_delegations should be true and arg_prev_is_initialized
        // should be false, or vice versa.
        assert!(process_delegations != arg_prev_is_initialized);
        // Grand product register and indirect access contributions
        for i in 0..register_and_indirect_accesses.num_register_accesses as usize {
            num_helpers_expected += 5;
            for _j in 0..register_and_indirect_accesses.indirect_accesses_per_register_access[i] {
                num_helpers_expected += 7;
            }
        }
        let (grand_product_src_col, grand_product_dst_col) =
            get_grand_product_src_dst_cols(circuit, is_unrolled);
        // Prepare static layout data for constraints on all rows except the last two
        let state_linkage_constraints = if !is_unrolled {
            StateLinkageConstraints::new(circuit)
        } else {
            StateLinkageConstraints::default()
        };
        // Layout data for boundary constraints (first row and second-to-last row)
        let boundary_constraints = BoundaryConstraints::new(
            circuit,
            process_shuffle_ram_init,
            &lazy_init_teardown_layouts,
        );
        num_helpers_expected += 1; // grand product accumulator
        num_helpers_expected += 2 * boundary_constraints.num_init_teardown as usize;
        num_helpers_expected += boundary_constraints.num_public_first_row as usize;
        num_helpers_expected += boundary_constraints.num_public_one_before_last_row as usize;
        // Just one constraint at last row (grand product accumulator)
        num_helpers_expected += 2;
        // Constraints at last row and zero
        // range check 16 e4 arg sums
        // double-check we can reconstruct e4 arg locations from metadata
        let args_metadata = &circuit.stage_2_layout.intermediate_polys_for_range_check_16;
        let num_range_check_16_e4_args = args_metadata.ext_4_field_oracles.num_elements();
        assert_eq!(num_range_check_16_e4_args, args_metadata.num_pairs);
        assert_eq!(
            circuit
                .witness_layout
                .multiplicities_columns_for_range_check_16
                .num_elements(),
            1
        );
        assert_eq!(
            num_range_check_16_e4_args,
            (range_check_16_layout.num_dst_cols
                + range_check_16_expressions_layout.num_expression_pairs) as usize,
        );
        assert_eq!(
            translate_e4_offset(args_metadata.ext_4_field_oracles.start()),
            range_check_16_layout.e4_args_start as usize
        );
        num_helpers_expected += 1;
        // timestamp range check e4 arg sums
        if timestamp_range_check_multiplicities_layout.num_dst_cols > 0 {
            // double-check we can reconstruct e4 arg locations from metadata
            let args_metadata = &circuit
                .stage_2_layout
                .intermediate_polys_for_timestamp_range_checks;
            let num_timestamp_range_check_e4_args =
                args_metadata.ext_4_field_oracles.num_elements();
            let num_non_shuffle_ram_args =
                timestamp_range_check_expressions_layout.num_expression_pairs as usize;
            let num_shuffle_ram_args =
                expressions_for_shuffle_ram_layout.num_expression_pairs as usize;
            assert_eq!(num_timestamp_range_check_e4_args, args_metadata.num_pairs);
            assert_eq!(
                num_timestamp_range_check_e4_args,
                num_non_shuffle_ram_args + num_shuffle_ram_args,
            );
            for (i, dst) in args_metadata.ext_4_field_oracles.iter().enumerate() {
                if i < num_non_shuffle_ram_args {
                    assert_eq!(
                        timestamp_range_check_expressions_layout.e4_dst_cols[i] as usize,
                        translate_e4_offset(dst.start),
                    );
                } else {
                    assert_eq!(
                        expressions_for_shuffle_ram_layout.e4_dst_cols[i - num_non_shuffle_ram_args]
                            as usize,
                        translate_e4_offset(dst.start),
                    );
                }
            }
            num_helpers_expected += 1;
        }
        // decoder lookup e4 arg sums
        if num_decoder_multiplicities_cols > 0 {
            num_helpers_expected += 1;
        }
        // generic lookup e4 arg sums
        if num_generic_multiplicities_cols > 0 {
            num_helpers_expected += 1;
        }
        // delegation aux poly sums
        if handle_delegation_requests || process_delegations {
            num_helpers_expected += 2;
        }
        Self {
            alpha_powers_layout,
            flat_generic_constraints_metadata,
            delegated_width_3_lookups_layout,
            non_delegated_width_3_lookups_layout,
            range_check_16_layout,
            range_check_16_expressions_layout,
            timestamp_range_check_expressions_layout,
            intermediate_state_lookup_layout,
            expressions_for_shuffle_ram_layout,
            decoder_lookup_multiplicities_layout,
            generic_lookup_multiplicities_layout,
            state_linkage_constraints,
            boundary_constraints,
            lazy_init_teardown_args_start,
            memory_args_start,
            grand_product_src_col,
            grand_product_dst_col,
            lazy_init_teardown_layouts,
            shuffle_ram_accesses,
            machine_state_layout,
            mask_arg_layout,
            range_check_16_multiplicities_layout,
            timestamp_range_check_multiplicities_layout,
            delegation_aux_poly_col,
            delegation_challenges,
            delegation_processing_metadata,
            delegation_request_metadata,
            register_and_indirect_accesses,
            num_helpers_expected,
            is_unrolled,
        }
    }
}

pub(super) fn prepare_async_challenge_data(
    static_metadata: &StaticMetadata,
    h_alpha_powers: &[E4],
    h_beta_powers: &[E4],
    omega: E2,
    lookup_challenges: &LookupChallenges,
    decoder_table_challenges: &DecoderTableChallenges,
    cached_data: &ProverCachedData,
    circuit: &CompiledCircuitArtifact<BF>,
    aux_arguments_boundary_values: &[AuxArgumentsBoundaryValues],
    public_inputs: &[BF],
    grand_product_accumulator: E4,
    sum_over_delegation_poly: E4,
    helpers: &mut Vec<E4, impl Allocator>,
    constants_times_challenges: &mut ConstantsTimesChallenges,
) {
    let StaticMetadata {
        alpha_powers_layout,
        flat_generic_constraints_metadata,
        delegated_width_3_lookups_layout,
        non_delegated_width_3_lookups_layout,
        range_check_16_expressions_layout,
        timestamp_range_check_expressions_layout,
        intermediate_state_lookup_layout,
        expressions_for_shuffle_ram_layout,
        decoder_lookup_multiplicities_layout,
        generic_lookup_multiplicities_layout,
        state_linkage_constraints,
        boundary_constraints,
        lazy_init_teardown_layouts,
        shuffle_ram_accesses,
        mask_arg_layout,
        range_check_16_multiplicities_layout,
        timestamp_range_check_multiplicities_layout,
        delegation_challenges,
        delegation_processing_metadata,
        delegation_request_metadata,
        register_and_indirect_accesses,
        num_helpers_expected,
        is_unrolled,
        ..
    } = static_metadata;

    let ProverCachedData {
        memory_timestamp_high_from_circuit_idx,
        memory_argument_challenges,
        machine_state_argument_challenges,
        process_shuffle_ram_init,
        handle_delegation_requests,
        process_registers_and_indirect_access,
        process_delegations,
        range_check_16_width_1_lookups_access,
        range_check_16_width_1_lookups_access_via_expressions,
        ..
    } = cached_data.clone();

    // We keep references to host AND device copies of challenge powers,
    // because host copies come in handy to precompute challenges_times_powers_sum
    // and other helper values.
    let AlphaPowersLayout {
        num_quotient_terms_every_row_except_last,
        num_quotient_terms_every_row_except_last_two,
        num_quotient_terms_first_row,
        num_quotient_terms_one_before_last_row,
        num_quotient_terms_last_row,
        num_quotient_terms_last_row_and_at_zero,
        precomputation_size,
    } = alpha_powers_layout;
    assert_eq!(h_alpha_powers.len(), *precomputation_size);
    let h_alphas_for_every_row_except_last =
        &h_alpha_powers[(precomputation_size - num_quotient_terms_every_row_except_last)..];
    let h_alphas_for_every_row_except_last_two =
        &h_alpha_powers[(precomputation_size - num_quotient_terms_every_row_except_last_two)..];
    let h_alphas_for_first_row =
        &h_alpha_powers[(precomputation_size - num_quotient_terms_first_row)..];
    // let d_alphas_for_first_row =
    //     &d_alphas[(precomputation_size - num_quotient_terms_first_row)..];
    let h_alphas_for_one_before_last_row =
        &h_alpha_powers[(precomputation_size - num_quotient_terms_one_before_last_row)..];
    // let d_alphas_for_one_before_last_row =
    //     &d_alphas[(precomputation_size - num_quotient_terms_one_before_last_row)..];
    let h_alphas_for_last_row =
        &h_alpha_powers[(precomputation_size - num_quotient_terms_last_row)..];
    // let d_alphas_for_last_row =
    //     &d_alphas[(precomputation_size - num_quotient_terms_last_row)..];
    let h_alphas_for_last_row_and_at_zero =
        &h_alpha_powers[(precomputation_size - num_quotient_terms_last_row_and_at_zero)..];
    // let d_alphas_for_last_row_and_at_zero =
    //     &d_alphas[(precomputation_size - num_quotient_terms_last_row_and_at_zero)..];
    // Generic constraints
    let num_generic_constraints =
        circuit.degree_2_constraints.len() + circuit.degree_1_constraints.len();
    let (h_alphas_for_generic_constraints, h_alphas_for_hardcoded_every_row_except_last) =
        h_alphas_for_every_row_except_last.split_at(num_generic_constraints);
    constants_times_challenges.every_row_except_last = E4::ZERO;
    flat_generic_constraints_metadata.prepare_async_challenge_data(
        circuit,
        h_alphas_for_generic_constraints,
        constants_times_challenges,
    );
    let memory_challenges = MemoryChallenges::new(&memory_argument_challenges);
    // Host work to precompute constants_times_challenges sums and some helpers
    // that streamline device computation
    assert_eq!(helpers.len(), 0);
    assert_eq!(helpers.capacity(), MAX_HELPER_VALUES);
    let decompression_factor = flat_generic_constraints_metadata.decompression_factor;
    let decompression_factor_inv = decompression_factor.inverse().expect("must exist");
    let two = BF::from_u64_unchecked(2);
    let lookup_linearization_challenges = &lookup_challenges.linearization_challenges;
    let lookup_gamma = lookup_challenges.gamma;
    let lookup_gamma_squared = *lookup_gamma.clone().square();
    let lookup_two_gamma = *lookup_gamma.clone().mul_assign_by_base(&two);
    let mut alpha_offset = 0;
    if process_delegations {
        alpha_offset += 4;
    }
    if process_registers_and_indirect_access {
        let mut flat_indirect_idx = 0;
        for i in 0..register_and_indirect_accesses.num_register_accesses as usize {
            let register_access = &register_and_indirect_accesses.register_accesses[i];
            if register_access.is_write {
                alpha_offset += 6;
            } else {
                alpha_offset += 4;
            }
            for _j in 0..register_and_indirect_accesses.indirect_accesses_per_register_access[i] {
                let indirect_access =
                    &register_and_indirect_accesses.indirect_accesses[flat_indirect_idx];
                if indirect_access.has_write {
                    alpha_offset += 6;
                } else {
                    alpha_offset += 4;
                }
                if indirect_access.has_address_derivation_carry_bit {
                    alpha_offset += 1; // address_derivation_carry_bit constraint
                }
                flat_indirect_idx += 1;
            }
        }
    }
    // We must assign challenges for bare range check 16s,
    // range check 16 expressions, timestamp range check expressions,
    // and timestamp range check expressions for shuffle ram
    // in the same order challenges are assigned in the CPU code.
    let mut bound = range_check_16_width_1_lookups_access.len();
    if range_check_16_expressions_layout.constant_terms_are_zero {
        bound += range_check_16_width_1_lookups_access_via_expressions.len();
    }
    // bare (non-expression) range check 16s, plus range check 16 expressions if
    // all those expressions are known not to have constant terms
    for _ in 0..bound {
        alpha_offset += 1;
        let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
        helpers.push(*alpha.clone().mul_assign(&lookup_gamma));
        helpers.push(
            *alpha
                .clone()
                .mul_assign(&lookup_gamma_squared)
                .mul_assign_by_base(&decompression_factor_inv),
        );
        constants_times_challenges
            .every_row_except_last
            .sub_assign(alpha.clone().mul_assign(&lookup_two_gamma));
        alpha_offset += 1;
    }
    // Expressions may contain constant terms that need special handling.
    // Pain. need to pass alpha_offset rather than borrow it, because it's
    // also used by non-closure invocations during the lifetime of the
    // closure
    let stash_helpers_for_expressions_with_constant_terms =
        |num_expression_pairs: usize,
         constant_terms: &[BF],
         alpha_offset: &mut usize,
         helpers: &mut Vec<E4, _>,
         constants_times_challenges: &mut ConstantsTimesChallenges| {
            for i in 0..num_expression_pairs {
                let mut alpha = h_alphas_for_hardcoded_every_row_except_last[*alpha_offset];
                let a_constant_term = constant_terms[2 * i];
                let b_constant_term = constant_terms[2 * i + 1];
                let constants_prod = *a_constant_term.clone().mul_assign(&b_constant_term);
                constants_times_challenges
                    .every_row_except_last
                    .add_assign(alpha.mul_assign_by_base(&constants_prod));
                *alpha_offset += 1;
                let alpha = h_alphas_for_hardcoded_every_row_except_last[*alpha_offset];
                helpers.push(*alpha.clone().mul_assign(&lookup_gamma));
                let constants_sum = *a_constant_term.clone().add_assign(&b_constant_term);
                let mut gamma_corrections =
                    *lookup_gamma.clone().mul_assign_by_base(&constants_sum);
                gamma_corrections.add_assign(&lookup_gamma_squared);
                helpers.push(
                    *alpha
                        .clone()
                        .mul_assign(&gamma_corrections)
                        .mul_assign_by_base(&decompression_factor_inv),
                );
                constants_times_challenges
                    .every_row_except_last
                    .sub_assign(alpha.clone().mul_assign_by_base(&constants_sum));
                constants_times_challenges
                    .every_row_except_last
                    .sub_assign(alpha.clone().mul_assign(&lookup_two_gamma));
                *alpha_offset += 1;
            }
        };
    // range check 16 expressions, if constant terms are present
    if !range_check_16_expressions_layout.constant_terms_are_zero {
        let num_pairs = range_check_16_expressions_layout.num_expression_pairs as usize;
        stash_helpers_for_expressions_with_constant_terms(
            num_pairs as usize,
            &range_check_16_expressions_layout.constant_terms[0..2 * num_pairs],
            &mut alpha_offset,
            helpers,
            constants_times_challenges,
        );
    }
    // lazy init addresses range checks
    for _ in 0..lazy_init_teardown_layouts.num_init_teardown_sets {
        alpha_offset += 1;
        let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
        helpers.push(*alpha.clone().mul_assign(&lookup_gamma));
        helpers.push(
            *alpha
                .clone()
                .mul_assign(&lookup_gamma_squared)
                .mul_assign_by_base(&decompression_factor_inv),
        );
        constants_times_challenges
            .every_row_except_last
            .sub_assign(alpha.clone().mul_assign(&lookup_two_gamma));
        alpha_offset += 1;
    }
    // timestamp range check expressions
    if timestamp_range_check_expressions_layout.constant_terms_are_zero {
        for _ in 0..timestamp_range_check_expressions_layout.num_expression_pairs as usize {
            alpha_offset += 1;
            let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
            helpers.push(*alpha.clone().mul_assign(&lookup_gamma));
            helpers.push(
                *alpha
                    .clone()
                    .mul_assign(&lookup_gamma_squared)
                    .mul_assign_by_base(&decompression_factor_inv),
            );
            constants_times_challenges
                .every_row_except_last
                .sub_assign(alpha.clone().mul_assign(&lookup_two_gamma));
            alpha_offset += 1;
        }
    } else {
        let num_pairs = timestamp_range_check_expressions_layout.num_expression_pairs as usize;
        stash_helpers_for_expressions_with_constant_terms(
            num_pairs,
            &timestamp_range_check_expressions_layout.constant_terms[0..2 * num_pairs],
            &mut alpha_offset,
            helpers,
            constants_times_challenges,
        );
    }
    // decoder lookups
    if circuit.memory_layout.intermediate_state_layout.is_some() {
        intermediate_state_lookup_layout.prepare_async_challenge_data(
            decoder_table_challenges,
            &h_alphas_for_hardcoded_every_row_except_last,
            &mut alpha_offset,
            helpers,
            decompression_factor_inv,
        );
    } else {
        assert!(!intermediate_state_lookup_layout.has_decoder);
    }
    // timestamp range check expressions for shuffle ram
    let num_pairs = expressions_for_shuffle_ram_layout.num_expression_pairs as usize;
    let constant_terms_with_timestamp_high_circuit_idx_adjustment: Vec<BF> =
        expressions_for_shuffle_ram_layout
            .constant_terms
            .iter()
            .enumerate()
            .map(|(i, val)| {
                if i % 2 == 0 {
                    *val
                } else {
                    *val.clone()
                        .sub_assign(&memory_timestamp_high_from_circuit_idx)
                }
            })
            .collect();
    stash_helpers_for_expressions_with_constant_terms(
        num_pairs,
        &constant_terms_with_timestamp_high_circuit_idx_adjustment[0..2 * num_pairs],
        &mut alpha_offset,
        helpers,
        constants_times_challenges,
    );
    if process_delegations {
        delegated_width_3_lookups_layout.prepare_async_challenge_data(
            circuit,
            lookup_linearization_challenges,
            lookup_gamma,
            &h_alphas_for_hardcoded_every_row_except_last,
            &mut alpha_offset,
            helpers,
            decompression_factor_inv,
            constants_times_challenges,
        );
    } else {
        if circuit.witness_layout.width_3_lookups.len() > 0 {
            non_delegated_width_3_lookups_layout.prepare_async_challenge_data(
                circuit,
                lookup_linearization_challenges,
                lookup_gamma,
                &h_alphas_for_hardcoded_every_row_except_last,
                &mut alpha_offset,
                helpers,
                decompression_factor_inv,
                constants_times_challenges,
            );
        } else {
            assert_eq!(non_delegated_width_3_lookups_layout.num_lookups, 0);
        }
    };
    range_check_16_multiplicities_layout.prepare_async_challenge_data(
        1,
        lookup_challenges.gamma,
        &[],
        &h_alphas_for_hardcoded_every_row_except_last,
        &mut alpha_offset,
        helpers,
        decompression_factor_inv,
    );
    timestamp_range_check_multiplicities_layout.prepare_async_challenge_data(
        1,
        lookup_challenges.gamma,
        &[],
        &h_alphas_for_hardcoded_every_row_except_last,
        &mut alpha_offset,
        helpers,
        decompression_factor_inv,
    );
    decoder_lookup_multiplicities_layout.prepare_async_challenge_data(
        EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH,
        decoder_table_challenges.gamma,
        &decoder_table_challenges.linearization_challenges,
        &h_alphas_for_hardcoded_every_row_except_last,
        &mut alpha_offset,
        helpers,
        decompression_factor_inv,
    );
    generic_lookup_multiplicities_layout.prepare_async_challenge_data(
        NUM_LOOKUP_ARGUMENT_KEY_PARTS,
        lookup_challenges.gamma,
        &lookup_challenges.linearization_challenges,
        &h_alphas_for_hardcoded_every_row_except_last,
        &mut alpha_offset,
        helpers,
        decompression_factor_inv,
    );
    if handle_delegation_requests {
        let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
        alpha_offset += 1;
        let mut timestamp_low_constant = delegation_challenges.linearization_challenges
            [DELEGATION_ARGUMENT_CHALLENGED_IDX_FOR_TIMESTAMP_LOW];
        timestamp_low_constant.mul_assign_by_base(&delegation_request_metadata.in_cycle_write_idx);
        let mut timestamp_high_constant = delegation_challenges.linearization_challenges
            [DELEGATION_ARGUMENT_CHALLENGED_IDX_FOR_TIMESTAMP_HIGH];
        timestamp_high_constant.mul_assign_by_base(
            &delegation_request_metadata.memory_timestamp_high_from_circuit_idx,
        );
        helpers.push(
            *delegation_challenges
                .gamma
                .clone()
                .add_assign(&timestamp_low_constant)
                .add_assign(&timestamp_high_constant)
                .mul_assign(&alpha)
                .mul_assign_by_base(&decompression_factor_inv),
        );
        for challenge in delegation_challenges.linearization_challenges.iter() {
            helpers.push(*alpha.clone().mul_assign(&challenge));
        }
    }
    if process_delegations {
        let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
        alpha_offset += 1;
        helpers.push(
            *delegation_challenges
                .gamma
                .clone()
                .add_assign_base(&delegation_processing_metadata.delegation_type)
                .mul_assign(&alpha)
                .mul_assign_by_base(&decompression_factor_inv),
        );
        for challenge in delegation_challenges.linearization_challenges.iter() {
            helpers.push(*alpha.clone().mul_assign(&challenge));
        }
    }
    // for lazy init padding constraints (limbs are zero if "final borrow" is zero)
    for _ in 0..lazy_init_teardown_layouts.num_init_teardown_sets {
        alpha_offset += 6;
    }
    // Helpers for shuffle ram grand product contributions
    let mut arg_prev_is_initialized: bool = false;
    for i in 0..shuffle_ram_accesses.num_accesses as usize {
        let access = &shuffle_ram_accesses.accesses[i];
        let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
        alpha_offset += 1;
        let mc = &memory_challenges;
        let mut numerator_constant = mc.gamma;
        if access.is_register_only {
            numerator_constant.add_assign_base(&BF::ONE);
        }
        let mut denom_constant = numerator_constant;
        let write_timestamp_low_constant = *mc
            .timestamp_low_challenge
            .clone()
            .mul_assign_by_base(&BF::from_u64_unchecked(i as u64));
        numerator_constant.add_assign(&write_timestamp_low_constant);
        if !is_unrolled {
            let write_timestamp_high_constant = *mc
                .timestamp_high_challenge
                .clone()
                .mul_assign_by_base(&memory_timestamp_high_from_circuit_idx);
            numerator_constant.add_assign(&write_timestamp_high_constant);
        }
        numerator_constant.mul_assign(&alpha);
        helpers.push(*alpha.clone().mul_assign(&mc.address_low_challenge));
        if !access.is_register_only {
            helpers.push(*alpha.clone().mul_assign(&mc.address_high_challenge));
        }
        helpers.push(*alpha.clone().mul_assign(&mc.value_low_challenge));
        helpers.push(*alpha.clone().mul_assign(&mc.value_high_challenge));
        helpers.push(*alpha.clone().mul_assign(&mc.timestamp_low_challenge));
        helpers.push(*alpha.clone().mul_assign(&mc.timestamp_high_challenge));
        helpers.push(
            *denom_constant
                .mul_assign(&alpha)
                .mul_assign_by_base(&decompression_factor_inv),
        );
        if !arg_prev_is_initialized {
            constants_times_challenges
                .every_row_except_last
                .sub_assign(&numerator_constant);
            arg_prev_is_initialized = true;
        } else {
            helpers.push(*numerator_constant.mul_assign_by_base(&decompression_factor_inv));
        }
    }
    // Helpers for machine state grand product contributions
    if circuit
        .stage_2_layout
        .intermediate_polys_for_state_permutation
        .num_elements()
        > 0
    {
        let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
        alpha_offset += 1;
        let constant = *alpha
            .clone()
            .mul_assign(&machine_state_argument_challenges.additive_term);
        for challenge in machine_state_argument_challenges
            .linearization_challenges
            .iter()
        {
            helpers.push(*alpha.clone().mul_assign(challenge));
        }
        if !arg_prev_is_initialized {
            constants_times_challenges
                .every_row_except_last
                .sub_assign(&constant);
            arg_prev_is_initialized = true;
        }
        helpers.push(
            *constant
                .clone()
                .mul_assign_by_base(&decompression_factor_inv),
        );
    }
    // Account for grand product masking argument, if present
    if mask_arg_layout.process_mask {
        let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
        alpha_offset += 1;
        constants_times_challenges
            .every_row_except_last
            .sub_assign(&alpha);
    }
    // Helpers for lazy init and teardown grand product contributions
    for _i in 0..lazy_init_teardown_layouts.num_init_teardown_sets as usize {
        let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
        alpha_offset += 1;
        let alpha_times_gamma = *alpha.clone().mul_assign(&memory_challenges.gamma);
        let mc = &memory_challenges;
        helpers.push(*alpha.clone().mul_assign(&mc.address_low_challenge));
        helpers.push(*alpha.clone().mul_assign(&mc.address_high_challenge));
        helpers.push(*alpha.clone().mul_assign(&mc.value_low_challenge));
        helpers.push(*alpha.clone().mul_assign(&mc.value_high_challenge));
        helpers.push(*alpha.clone().mul_assign(&mc.timestamp_low_challenge));
        helpers.push(*alpha.clone().mul_assign(&mc.timestamp_high_challenge));
        if !arg_prev_is_initialized {
            constants_times_challenges
                .every_row_except_last
                .sub_assign(&alpha_times_gamma);
            arg_prev_is_initialized = true;
        }
        helpers.push(
            *alpha_times_gamma
                .clone()
                .mul_assign_by_base(&decompression_factor_inv),
        );
    }
    // Helpers for register and indirect access grand product contributions
    let mut flat_indirect_idx = 0;
    for i in 0..register_and_indirect_accesses.num_register_accesses as usize {
        let register_access = &register_and_indirect_accesses.register_accesses[i];
        let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
        alpha_offset += 1;
        let mc = &memory_challenges;
        let mut constant = register_access.gamma_plus_one_plus_address_low_contribution;
        constant.mul_assign(&alpha);
        if i == 0 {
            constants_times_challenges
                .every_row_except_last
                .sub_assign(&constant);
        }
        helpers.push(*alpha.clone().mul_assign(&mc.value_low_challenge));
        helpers.push(*alpha.clone().mul_assign(&mc.value_high_challenge));
        helpers.push(*alpha.clone().mul_assign(&mc.timestamp_low_challenge));
        helpers.push(*alpha.clone().mul_assign(&mc.timestamp_high_challenge));
        helpers.push(*constant.mul_assign_by_base(&decompression_factor_inv));
        for j in 0..register_and_indirect_accesses.indirect_accesses_per_register_access[i] {
            let indirect_access =
                &register_and_indirect_accesses.indirect_accesses[flat_indirect_idx];
            flat_indirect_idx += 1;
            let alpha = h_alphas_for_hardcoded_every_row_except_last[alpha_offset];
            alpha_offset += 1;
            // sanity checks based on our known circuit geometries
            if indirect_access.has_write {
                if j == 0 {
                    assert_eq!(j == 0, indirect_access.offset_constant == 0);
                }
            } else {
                assert_eq!(j == 0, indirect_access.offset_constant == 0);
            }
            let offset = BF::from_u64_unchecked(indirect_access.offset_constant as u64);
            let mut constant = *mc
                .address_low_challenge
                .clone()
                .mul_assign_by_base(&offset)
                .add_assign(&mc.gamma)
                .mul_assign(&alpha);
            helpers.push(*alpha.clone().mul_assign(&mc.address_low_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.address_high_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.value_low_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.value_high_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.timestamp_low_challenge));
            helpers.push(*alpha.clone().mul_assign(&mc.timestamp_high_challenge));
            helpers.push(*constant.mul_assign_by_base(&decompression_factor_inv));
        }
    }
    alpha_offset += 1; // grand product row linkage
    assert_eq!(
        alpha_offset,
        h_alphas_for_hardcoded_every_row_except_last.len()
    );
    // Prepare args and helpers for constraints on all rows except the last two
    alpha_offset = 0;
    alpha_offset += state_linkage_constraints.num_constraints as usize;
    for _ in 0..lazy_init_teardown_layouts.num_init_teardown_sets {
        // alphas for "next lazy init timestamp > current lazy init timestamp"
        alpha_offset += 2;
    }
    assert_eq!(alpha_offset, h_alphas_for_every_row_except_last_two.len());
    // Args and helpers for boundary constraints (first row and second-to-last row)
    // "+ 1" accounts for the additional grand product == 1 at row 0 constraint
    assert_eq!(
        (boundary_constraints.num_init_teardown + boundary_constraints.num_public_first_row)
            as usize
            + 1,
        h_alphas_for_first_row.len()
    );
    assert_eq!(
        (boundary_constraints.num_init_teardown
            + boundary_constraints.num_public_one_before_last_row) as usize,
        h_alphas_for_one_before_last_row.len()
    );
    boundary_constraints.prepare_async_challenge_data(
        circuit,
        aux_arguments_boundary_values,
        public_inputs,
        process_shuffle_ram_init,
        h_alphas_for_first_row,
        h_alphas_for_one_before_last_row,
        helpers,
        h_beta_powers,
        decompression_factor,
        constants_times_challenges,
    );
    // Just one constraint at last row (grand product accumulator)
    let mut alpha = h_alphas_for_last_row[0];
    alpha.mul_assign(&h_beta_powers[1]);
    helpers.push(*alpha.clone().mul_assign_by_base(&decompression_factor));
    helpers.push(*alpha.negate().mul_assign(&grand_product_accumulator));
    assert_eq!(1, h_alphas_for_last_row.len());
    // Constraints at last row and zero
    // range check 16 e4 arg sums
    let mut alpha_offset = 0;
    let mut alpha = h_alphas_for_last_row_and_at_zero[alpha_offset];
    alpha_offset += 1;
    helpers.push(*alpha.negate().mul_assign_by_base(&decompression_factor));
    // timestamp range check e4 arg sums
    if timestamp_range_check_multiplicities_layout.num_dst_cols > 0 {
        let mut alpha = h_alphas_for_last_row_and_at_zero[alpha_offset];
        alpha_offset += 1;
        helpers.push(*alpha.negate().mul_assign_by_base(&decompression_factor));
    }
    // decoder lookup e4 arg sums
    if decoder_lookup_multiplicities_layout.num_dst_cols > 0 {
        let mut alpha = h_alphas_for_last_row_and_at_zero[alpha_offset];
        alpha_offset += 1;
        helpers.push(*alpha.negate().mul_assign_by_base(&decompression_factor));
    }
    // generic lookup e4 arg sums
    if generic_lookup_multiplicities_layout.num_dst_cols > 0 {
        let mut alpha = h_alphas_for_last_row_and_at_zero[alpha_offset];
        alpha_offset += 1;
        helpers.push(*alpha.negate().mul_assign_by_base(&decompression_factor));
    }
    // delegation aux poly sums
    if handle_delegation_requests || process_delegations {
        let mut alpha = h_alphas_for_last_row_and_at_zero[alpha_offset];
        alpha_offset += 1;
        let mut delegation_accumulator_interpolant_prefactor = sum_over_delegation_poly;
        delegation_accumulator_interpolant_prefactor
            .negate()
            .mul_assign_by_base(&omega)
            .mul_assign_by_base(&decompression_factor_inv);
        helpers.push(delegation_accumulator_interpolant_prefactor);
        helpers.push(*alpha.mul_assign_by_base(&decompression_factor));
    }
    assert_eq!(alpha_offset, h_alphas_for_last_row_and_at_zero.len());
    assert_eq!(helpers.len(), *num_helpers_expected);
    assert!(helpers.len() <= MAX_HELPER_VALUES);
    helpers
        .spare_capacity_mut()
        .fill(MaybeUninit::new(E4::ZERO));
    unsafe {
        helpers.set_len(MAX_HELPER_VALUES);
    }
}

pub fn compute_stage_3_composition_quotient_on_coset(
    cached_data: &ProverCachedData,
    circuit: &CompiledCircuitArtifact<BF>,
    static_metadata: StaticMetadata,
    setup_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    witness_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    memory_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    stage_2_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    d_alpha_powers: &DeviceSlice<E4>,
    d_beta_powers: &DeviceSlice<E4>,
    d_helpers: &DeviceSlice<E4>,
    d_constants_times_challenges: &DeviceVariable<ConstantsTimesChallenges>,
    quotient: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_n: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let n = 1 << log_n;
    let num_setup_cols = circuit.setup_layout.total_width;
    let num_witness_cols = circuit.witness_layout.total_width;
    let num_memory_cols = circuit.memory_layout.total_width;
    let num_stage_2_bf_cols = circuit.stage_2_layout.num_base_field_polys();
    let num_stage_2_e4_cols = circuit.stage_2_layout.num_ext4_field_polys();
    let e4_cols_offset = circuit.stage_2_layout.ext4_polys_offset;
    assert_eq!(e4_cols_offset % 4, 0);
    assert!(num_stage_2_bf_cols <= e4_cols_offset);
    assert!(e4_cols_offset - num_stage_2_bf_cols < 4);
    assert_eq!(setup_cols.rows(), n);
    assert_eq!(setup_cols.cols(), num_setup_cols);
    assert_eq!(witness_cols.rows(), n);
    assert_eq!(witness_cols.cols(), num_witness_cols,);
    assert_eq!(memory_cols.rows(), n);
    assert_eq!(memory_cols.cols(), num_memory_cols,);
    assert_eq!(quotient.rows(), n);
    assert_eq!(quotient.cols(), 4);
    let ProverCachedData {
        trace_len,
        memory_timestamp_high_from_circuit_idx,
        handle_delegation_requests,
        process_registers_and_indirect_access,
        process_delegations,
        ..
    } = cached_data.clone();
    assert_eq!(trace_len, n);
    let StaticMetadata {
        alpha_powers_layout,
        flat_generic_constraints_metadata,
        delegated_width_3_lookups_layout,
        non_delegated_width_3_lookups_layout,
        range_check_16_layout,
        range_check_16_expressions_layout,
        timestamp_range_check_expressions_layout,
        intermediate_state_lookup_layout,
        expressions_for_shuffle_ram_layout,
        decoder_lookup_multiplicities_layout,
        generic_lookup_multiplicities_layout,
        state_linkage_constraints,
        boundary_constraints,
        lazy_init_teardown_args_start,
        memory_args_start,
        grand_product_src_col,
        grand_product_dst_col,
        lazy_init_teardown_layouts,
        shuffle_ram_accesses,
        machine_state_layout,
        mask_arg_layout,
        range_check_16_multiplicities_layout,
        timestamp_range_check_multiplicities_layout,
        delegation_aux_poly_col,
        delegation_challenges,
        delegation_processing_metadata,
        delegation_request_metadata,
        register_and_indirect_accesses,
        num_helpers_expected: _,
        is_unrolled,
    } = static_metadata;
    let AlphaPowersLayout {
        num_quotient_terms_every_row_except_last,
        num_quotient_terms_every_row_except_last_two,
        precomputation_size,
        ..
    } = alpha_powers_layout;
    let d_e4_helpers = d_helpers.as_ptr();
    let d_constants_times_challenges = d_constants_times_challenges.as_ptr();
    assert_eq!(d_alpha_powers.len(), precomputation_size);
    let d_alphas_for_every_row_except_last =
        &d_alpha_powers[(precomputation_size - num_quotient_terms_every_row_except_last)..];
    let d_alphas_for_every_row_except_last_two =
        &d_alpha_powers[(precomputation_size - num_quotient_terms_every_row_except_last_two)..];
    let num_generic_constraints =
        circuit.degree_2_constraints.len() + circuit.degree_1_constraints.len();
    let (d_alphas_for_generic_constraints, d_alphas_for_hardcoded_every_row_except_last) =
        d_alphas_for_every_row_except_last.split_at(num_generic_constraints);
    // it's handy to keep a copy
    let generic_constraints_metadata = flat_generic_constraints_metadata.clone();
    let witness_cols = witness_cols.as_ptr_and_stride();
    let memory_cols = memory_cols.as_ptr_and_stride();
    let d_alphas_for_generic_constraints = d_alphas_for_generic_constraints.as_ptr();
    let quotient = quotient.as_mut_ptr_and_stride();
    let block_dim = 4 * WARP_SIZE;
    let grid_dim = (n as u32 + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenericConstraintsArguments::new(
        generic_constraints_metadata,
        witness_cols,
        memory_cols,
        d_alphas_for_generic_constraints,
        quotient,
        log_n,
    );
    GenericConstraintsFunction(ab_generic_constraints_kernel).launch(&config, &args)?;
    // for convenience, demarcate bf and vectorized e4 sections of stage_2_cols
    assert_eq!(stage_2_cols.rows(), n);
    assert_eq!(
        stage_2_cols.cols(),
        e4_cols_offset + 4 * num_stage_2_e4_cols
    );
    let (stage_2_bf_cols, stage_2_e4_cols) = {
        let stride = stage_2_cols.stride();
        let offset = stage_2_cols.offset();
        let slice = stage_2_cols.slice();
        let (bf_slice, e4_slice) = slice.split_at(e4_cols_offset * stride);
        (
            DeviceMatrixChunk::new(
                &bf_slice[0..num_stage_2_bf_cols * stride],
                stride,
                offset,
                n,
            ),
            DeviceMatrixChunk::new(e4_slice, stride, offset, n),
        )
    };
    let setup_cols = setup_cols.as_ptr_and_stride();
    let stage_2_bf_cols = stage_2_bf_cols.as_ptr_and_stride();
    let stage_2_e4_cols = stage_2_e4_cols.as_ptr_and_stride();
    let d_alphas_for_hardcoded_every_row_except_last =
        d_alphas_for_hardcoded_every_row_except_last.as_ptr();
    let d_alphas_for_every_row_except_last_two = d_alphas_for_every_row_except_last_two.as_ptr();
    let d_beta_powers = d_beta_powers.as_ptr();
    let block_dim = 4 * WARP_SIZE;
    let grid_dim = (n as u32 + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    if process_delegations {
        let args = DelegatedWidth3LookupsArguments::new(
            delegated_width_3_lookups_layout,
            witness_cols,
            memory_cols,
            stage_2_e4_cols,
            d_e4_helpers,
            quotient,
            flat_generic_constraints_metadata.decompression_factor_squared,
            log_n,
        );
        DelegatedWidth3LookupsFunction(ab_delegated_width_3_lookups_kernel)
            .launch(&config, &args)?;
    }
    let omega_inv = flat_generic_constraints_metadata.omega_inv;
    let omega_inv_squared = *omega_inv.clone().square();
    let args = HardcodedConstraintsArguments::new(
        setup_cols,
        witness_cols,
        memory_cols,
        stage_2_bf_cols,
        stage_2_e4_cols,
        process_delegations,
        handle_delegation_requests,
        delegation_aux_poly_col as u32,
        delegation_challenges,
        delegation_processing_metadata,
        delegation_request_metadata,
        lazy_init_teardown_args_start as u32,
        memory_args_start as u32,
        grand_product_src_col as u32,
        grand_product_dst_col as u32,
        lazy_init_teardown_layouts,
        shuffle_ram_accesses,
        machine_state_layout,
        mask_arg_layout,
        process_registers_and_indirect_access,
        register_and_indirect_accesses,
        range_check_16_layout,
        range_check_16_expressions_layout,
        timestamp_range_check_expressions_layout,
        intermediate_state_lookup_layout,
        expressions_for_shuffle_ram_layout,
        non_delegated_width_3_lookups_layout,
        range_check_16_multiplicities_layout,
        timestamp_range_check_multiplicities_layout,
        decoder_lookup_multiplicities_layout,
        generic_lookup_multiplicities_layout,
        state_linkage_constraints,
        boundary_constraints,
        d_alphas_for_hardcoded_every_row_except_last,
        d_alphas_for_every_row_except_last_two,
        d_beta_powers,
        d_e4_helpers,
        d_constants_times_challenges,
        quotient,
        memory_timestamp_high_from_circuit_idx,
        flat_generic_constraints_metadata.decompression_factor,
        flat_generic_constraints_metadata.decompression_factor_squared,
        flat_generic_constraints_metadata.every_row_zerofier,
        omega_inv,
        omega_inv_squared,
        is_unrolled,
        log_n,
    );
    HardcodedConstraintsFunction(ab_hardcoded_constraints_kernel).launch(&config, &args)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::device_context::DeviceContext;
    use crate::device_structures::DeviceMatrixMut;
    use crate::ops_complex::transpose;
    use std::alloc::Global;

    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use fft::materialize_powers_serial_starting_with_one;
    use field::Field;
    use prover::tests::{
        run_basic_delegation_test_impl,
        run_basic_unrolled_test_in_transpiler_with_word_specialization_impl, run_keccak_test_impl,
        GpuComparisonArgs,
    };
    use serial_test::serial;

    type BF = BaseField;
    type E4 = Ext4Field;

    fn comparison_hook(gpu_comparison_args: &GpuComparisonArgs) {
        let GpuComparisonArgs {
            circuit,
            setup,
            external_challenges,
            aux_boundary_values,
            public_inputs,
            twiddles,
            lde_precomputations,
            lookup_mapping: _,
            log_n,
            circuit_sequence,
            delegation_processing_type,
            is_unrolled,
            prover_data,
        } = gpu_comparison_args;
        let log_n = *log_n;
        let circuit_sequence = circuit_sequence.unwrap_or(0);
        let delegation_processing_type = delegation_processing_type.unwrap_or(0);
        let domain_size = 1 << log_n;
        let stage_1_output = &prover_data.stage_1_result;
        let stage_2_output = &prover_data.stage_2_result;
        let stage_3_output = &prover_data.quotient_commitment_result;
        let domain_index = 1;
        let tau = lde_precomputations.domain_bound_precomputations[domain_index]
            .as_ref()
            .unwrap()
            .coset_offset;

        let cached_data = ProverCachedData::new(
            &circuit,
            &external_challenges,
            domain_size,
            circuit_sequence,
            delegation_processing_type,
        );

        print_size::<FlattenedGenericConstraintsMetadata>("FlattenedGenericConstraintsMetadata");
        print_size::<DelegatedWidth3LookupsLayout>("DelegatedWidth3LookupsLayout");
        print_size::<NonDelegatedWidth3LookupsLayout>("NonDelegatedWidth3LookupsLayout");
        print_size::<StateLinkageConstraints>("StageLinkageConstraints");
        print_size::<BoundaryConstraints>("BoundaryConstraints");
        print_sizes();

        let num_setup_cols = circuit.setup_layout.total_width;
        let num_witness_cols = circuit.witness_layout.total_width;
        let num_memory_cols = circuit.memory_layout.total_width;
        let num_trace_cols = num_witness_cols + num_memory_cols;
        let num_stage_2_cols = circuit.stage_2_layout.total_width;

        // Internally, AlphaPowersLayout::new calls circuit.as_verifier_compiled_artifact.
        // We expect this to be negligible, but it doesn't hurt to sanity check.
        let now = std::time::Instant::now();
        let alpha_powers_layout =
            AlphaPowersLayout::new(&circuit, cached_data.num_stage_3_quotient_terms);
        let duration = now.elapsed();
        println!("Time to construct AlphaPowersLayout {:?}", duration);
        assert!(duration < std::time::Duration::from_micros(50));

        let mut h_quotient: Vec<BF> = vec![BF::ZERO; 4 * domain_size];
        let mut h_alpha_powers: Vec<E4> = materialize_powers_serial_starting_with_one::<_, Global>(
            stage_3_output.quotient_alpha,
            alpha_powers_layout.precomputation_size,
        );
        h_alpha_powers.reverse();
        let h_beta_powers = materialize_powers_serial_starting_with_one::<_, Global>(
            stage_3_output.quotient_beta,
            BETA_POWERS_COUNT,
        );

        let h_setup = &setup.ldes[domain_index].trace;
        let h_trace = &stage_1_output.ldes[domain_index].trace;
        let h_stage_2 = &stage_2_output.ldes[domain_index].trace;
        let h_setup_slice = h_setup.as_slice();
        let h_trace_slice = h_trace.as_slice();
        let h_stage_2_slice = h_stage_2.as_slice();
        assert_eq!(h_setup_slice.len(), domain_size * h_setup.padded_width);
        assert_eq!(h_trace_slice.len(), domain_size * h_trace.padded_width);
        assert_eq!(h_stage_2_slice.len(), domain_size * h_stage_2.padded_width);
        let mut h_helpers = Vec::with_capacity(MAX_HELPER_VALUES);
        let mut h_constants_times_challenges = ConstantsTimesChallenges::default();
        let lookup_challenges = LookupChallenges::new(
            &prover_data
                .stage_2_result
                .lookup_argument_linearization_challenges,
            prover_data.stage_2_result.lookup_argument_gamma,
        );
        let decoder_table_challenges = if *is_unrolled {
            DecoderTableChallenges::new(
                &prover_data
                    .stage_2_result
                    .decoder_table_linearization_challenges,
                prover_data.stage_2_result.decoder_table_gamma,
            )
        } else {
            DecoderTableChallenges::default()
        };
        let static_metadata = StaticMetadata::new(
            tau,
            twiddles.omega_inv,
            &cached_data,
            &circuit,
            *is_unrolled,
            log_n as u32,
        );
        // Allocate GPU memory
        let stream = CudaStream::default();

        println!("h_setup_slice.len() {}", h_setup_slice.len());
        let mut d_setup_row_major = DeviceAllocation::<BF>::alloc(h_setup_slice.len()).unwrap();
        let mut d_setup_column_major =
            DeviceAllocation::<BF>::alloc(domain_size * num_setup_cols).unwrap();
        memory_copy_async(&mut d_setup_row_major, &h_setup_slice, &stream).unwrap();
        let d_setup_row_major_matrix =
            DeviceMatrixChunk::new(&d_setup_row_major, h_setup.padded_width, 0, num_setup_cols);
        let mut d_setup_cols = DeviceMatrixMut::new(&mut d_setup_column_major, domain_size);
        transpose(&d_setup_row_major_matrix, &mut d_setup_cols, &stream).unwrap();
        drop(d_setup_row_major_matrix);
        d_setup_row_major.free().unwrap();

        println!("h_trace_slice.len() {}", h_trace_slice.len());
        let mut d_trace_row_major = DeviceAllocation::<BF>::alloc(h_trace_slice.len()).unwrap();
        let mut d_trace_column_major =
            DeviceAllocation::<BF>::alloc(domain_size * num_trace_cols).unwrap();
        memory_copy_async(&mut d_trace_row_major, &h_trace_slice, &stream).unwrap();
        let d_trace_row_major_matrix =
            DeviceMatrixChunk::new(&d_trace_row_major, h_trace.padded_width, 0, num_trace_cols);
        let mut d_trace_cols = DeviceMatrixMut::new(&mut d_trace_column_major, domain_size);
        transpose(&d_trace_row_major_matrix, &mut d_trace_cols, &stream).unwrap();
        drop(d_trace_row_major_matrix);
        d_trace_row_major.free().unwrap();

        println!("h_stage_2_slice.len() {}", h_stage_2_slice.len());
        let mut d_stage_2_row_major = DeviceAllocation::<BF>::alloc(h_stage_2_slice.len()).unwrap();
        let mut d_stage_2_column_major =
            DeviceAllocation::<BF>::alloc(domain_size * num_stage_2_cols).unwrap();
        memory_copy_async(&mut d_stage_2_row_major, &h_stage_2_slice, &stream).unwrap();
        let d_stage_2_row_major_matrix = DeviceMatrixChunk::new(
            &d_stage_2_row_major,
            h_stage_2.padded_width,
            0,
            num_stage_2_cols,
        );
        let mut d_stage_2_cols = DeviceMatrixMut::new(&mut d_stage_2_column_major, domain_size);
        transpose(&d_stage_2_row_major_matrix, &mut d_stage_2_cols, &stream).unwrap();
        drop(d_stage_2_row_major_matrix);
        d_stage_2_row_major.free().unwrap();

        let mut d_alpha_powers =
            DeviceAllocation::<E4>::alloc(alpha_powers_layout.precomputation_size).unwrap();
        let mut d_beta_powers = DeviceAllocation::alloc(BETA_POWERS_COUNT).unwrap();
        let mut d_helpers = DeviceAllocation::<E4>::alloc(MAX_HELPER_VALUES).unwrap();
        let mut d_constants_times_challenges = DeviceAllocation::alloc(1).unwrap();
        let mut d_alloc_quotient = DeviceAllocation::<BF>::alloc(4 * domain_size).unwrap();
        prepare_async_challenge_data(
            &static_metadata,
            &h_alpha_powers,
            &h_beta_powers,
            twiddles.omega,
            &lookup_challenges,
            &decoder_table_challenges,
            &cached_data,
            &circuit,
            aux_boundary_values,
            &public_inputs,
            stage_2_output.grand_product_accumulator,
            stage_2_output.sum_over_delegation_poly,
            &mut h_helpers,
            &mut h_constants_times_challenges,
        );
        memory_copy_async(&mut d_alpha_powers, &h_alpha_powers, &stream).unwrap();
        memory_copy_async(&mut d_beta_powers, &h_beta_powers, &stream).unwrap();
        memory_copy_async(&mut d_helpers, &h_helpers, &stream).unwrap();
        memory_copy_async(
            &mut d_constants_times_challenges,
            &[h_constants_times_challenges],
            &stream,
        )
        .unwrap();
        let slice = d_trace_cols.slice();
        let stride = d_trace_cols.stride();
        let offset = d_trace_cols.offset();
        let d_witness_cols = DeviceMatrixChunk::new(
            &slice[0..num_witness_cols * stride],
            stride,
            offset,
            domain_size,
        );
        let d_memory_cols = DeviceMatrixChunk::new(
            &slice[num_witness_cols * stride..],
            stride,
            offset,
            domain_size,
        );
        let mut d_quotient = DeviceMatrixMut::new(&mut d_alloc_quotient, domain_size);
        compute_stage_3_composition_quotient_on_coset(
            &cached_data,
            &circuit,
            static_metadata,
            &d_setup_cols,
            &d_witness_cols,
            &d_memory_cols,
            &d_stage_2_cols,
            &d_alpha_powers,
            &d_beta_powers,
            &d_helpers,
            &d_constants_times_challenges[0],
            &mut d_quotient,
            log_n as u32,
            &stream,
        )
        .unwrap();
        memory_copy_async(&mut h_quotient, &d_alloc_quotient, &stream).unwrap();
        stream.synchronize().unwrap();

        let mut cpu_result_view = stage_3_output.ldes[domain_index]
            .trace
            .row_view(0..domain_size);
        unsafe {
            for i in 0..domain_size {
                let cpu_result_view_row = cpu_result_view.current_row_ref();
                let cpu_src = cpu_result_view_row.as_ptr().cast::<E4>();
                assert!(cpu_src.is_aligned());
                let gpu_result: [BF; 4] = std::array::from_fn(|j| h_quotient[i + j * domain_size]);
                assert_eq!(
                    E4::from_array_of_base(gpu_result),
                    cpu_src.read(),
                    "failed at row {}",
                    i,
                );
                cpu_result_view.advance_row();
            }
        }
    }

    #[test]
    #[serial]
    fn test_standalone_stage_3_non_unrolled_for_main_and_blake() {
        let ctx = DeviceContext::create(12).unwrap();
        run_basic_delegation_test_impl(
            Some(Box::new(comparison_hook)),
            Some(Box::new(comparison_hook)),
        );
        ctx.destroy().unwrap();
    }

    #[test]
    #[serial]
    #[ignore]
    fn test_standalone_stage_3_non_unrolled_for_main_and_keccak() {
        let ctx = DeviceContext::create(12).unwrap();
        run_keccak_test_impl(
            Some(Box::new(comparison_hook)),
            Some(Box::new(comparison_hook)),
        );
        ctx.destroy().unwrap();
    }

    #[test]
    #[serial]
    #[ignore]
    fn test_standalone_stage_3_unrolled_with_transpiler_for_main_and_keccak() {
        let ctx = DeviceContext::create(12).unwrap();
        run_basic_unrolled_test_in_transpiler_with_word_specialization_impl(
            Some(Box::new(comparison_hook)),
            Some(Box::new(comparison_hook)),
        );
        ctx.destroy().unwrap();
    }
}
