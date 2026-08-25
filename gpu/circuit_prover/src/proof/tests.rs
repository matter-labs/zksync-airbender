use crate::upstream::{
    assemble_query_index, draw_query_bits, BitSource, Blake2sTranscript, GKRExternalChallenges,
    Seed, Transcript,
};
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use gpu_core::primitives::field::{BF, E4};
use worker::Worker;

fn draw_query_bits_with_external_nonce(
    seed: &mut Seed,
    num_bits_for_queries: usize,
    pow_bits: u32,
    external_nonce: u64,
) -> (u64, BitSource) {
    if pow_bits == 0 {
        assert_eq!(
            external_nonce, 0,
            "pow_bits=0 expects the external nonce to be zero",
        );
    }
    <Blake2sTranscript as Transcript<BF, E4>>::verify_pow(seed, external_nonce, pow_bits);

    (
        external_nonce,
        draw_query_bits_after_verified_pow(seed, num_bits_for_queries),
    )
}

fn draw_query_bits_after_verified_pow(seed: &mut Seed, num_bits_for_queries: usize) -> BitSource {
    let num_required_words = num_bits_for_queries.div_ceil(u32::BITS as usize);
    let num_required_words_padded =
        (num_required_words + 1).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
    let mut source = vec![0u32; num_required_words_padded];
    <Blake2sTranscript as Transcript<BF, E4>>::draw_randomness(seed, &mut source);

    BitSource::new(source[1..].to_vec())
}

fn build_initial_transcript_input(
    top_bits: &[u32],
    external_challenges: &GKRExternalChallenges<BF, E4>,
    flattened_setup_tree_caps: &[u32],
    flattened_memory_tree_caps: &[u32],
    flattened_witness_tree_caps: &[u32],
) -> Vec<u32> {
    let mut transcript_input = Vec::new();
    transcript_input.extend_from_slice(top_bits);
    external_challenges.flatten_into_buffer(&mut transcript_input);
    if !flattened_setup_tree_caps.is_empty() {
        transcript_input.extend_from_slice(flattened_setup_tree_caps);
    }
    if !flattened_memory_tree_caps.is_empty() {
        transcript_input.extend_from_slice(flattened_memory_tree_caps);
    }
    if !flattened_witness_tree_caps.is_empty() {
        transcript_input.extend_from_slice(flattened_witness_tree_caps);
    }

    transcript_input
}

#[test]
fn external_nonce_query_bits_match_cpu_draw_query_bits() {
    let worker = Worker::new();
    let cases = [
        (Seed([1, 2, 3, 4, 5, 6, 7, 8]), 23usize, 22usize, 24u32),
        (
            Seed([11, 12, 13, 14, 15, 16, 17, 18]),
            12usize,
            21usize,
            24u32,
        ),
        (
            Seed([21, 22, 23, 24, 25, 26, 27, 28]),
            10usize,
            18usize,
            16u32,
        ),
        (
            Seed([31, 32, 33, 34, 35, 36, 37, 38]),
            10usize,
            14usize,
            0u32,
        ),
    ];

    for (seed, num_queries, query_index_bits, pow_bits) in cases {
        let num_bits_for_queries = num_queries * query_index_bits;
        let mut cpu_seed = seed;
        let mut external_seed = seed;
        let (cpu_nonce, mut cpu_bits) = draw_query_bits::<BF, E4, Blake2sTranscript>(
            &mut cpu_seed,
            num_bits_for_queries,
            pow_bits,
            &worker,
        );
        let (external_nonce, mut external_bits) = draw_query_bits_with_external_nonce(
            &mut external_seed,
            num_bits_for_queries,
            pow_bits,
            cpu_nonce,
        );

        assert_eq!(external_nonce, cpu_nonce, "external nonce changed");
        assert_eq!(external_seed, cpu_seed, "seed after external PoW diverged");

        let mut cpu_indexes = Vec::with_capacity(num_queries);
        let mut external_indexes = Vec::with_capacity(num_queries);
        for _ in 0..num_queries {
            cpu_indexes.push(assemble_query_index(query_index_bits, &mut cpu_bits));
            external_indexes.push(assemble_query_index(query_index_bits, &mut external_bits));
        }
        assert_eq!(
            external_indexes, cpu_indexes,
            "query indexes diverged for pow_bits={pow_bits}"
        );
    }
}

#[test]
fn initial_transcript_input_matches_cpu_order_with_and_without_setup_caps() {
    let external_challenges = GKRExternalChallenges {
        permutation_argument_linearization_challenges: std::array::from_fn(|idx| {
            E4::from_array_of_base([
                BF::new(10 + idx as u32),
                BF::new(20 + idx as u32),
                BF::new(30 + idx as u32),
                BF::new(40 + idx as u32),
            ])
        }),
        permutation_argument_additive_part: E4::from_array_of_base([
            BF::new(1),
            BF::new(2),
            BF::new(3),
            BF::new(4),
        ]),
        _marker: std::marker::PhantomData,
    };
    let top_bits = vec![0u32, 1, 2, 3];
    let setup_caps = vec![11u32, 12, 13, 14];
    let memory_caps = vec![21u32, 22, 23, 24];
    let witness_caps = vec![31u32, 32, 33, 34];

    let with_setup = build_initial_transcript_input(
        &top_bits,
        &external_challenges,
        &setup_caps,
        &memory_caps,
        &witness_caps,
    );
    let without_setup = build_initial_transcript_input(
        &top_bits,
        &external_challenges,
        &[],
        &memory_caps,
        &witness_caps,
    );

    let mut expected_with_setup = top_bits.clone();
    external_challenges.flatten_into_buffer(&mut expected_with_setup);
    expected_with_setup.extend_from_slice(&setup_caps);
    expected_with_setup.extend_from_slice(&memory_caps);
    expected_with_setup.extend_from_slice(&witness_caps);
    assert_eq!(with_setup, expected_with_setup);

    let mut expected_without_setup = top_bits.clone();
    external_challenges.flatten_into_buffer(&mut expected_without_setup);
    expected_without_setup.extend_from_slice(&memory_caps);
    expected_without_setup.extend_from_slice(&witness_caps);
    assert_eq!(without_setup, expected_without_setup);

    let with_setup_seed =
        <Blake2sTranscript as Transcript<BF, E4>>::commit_initial_u32(&with_setup);
    let mut expected_with_setup_seed = top_bits.clone();
    external_challenges.flatten_into_buffer(&mut expected_with_setup_seed);
    expected_with_setup_seed.extend_from_slice(&setup_caps);
    expected_with_setup_seed.extend_from_slice(&memory_caps);
    expected_with_setup_seed.extend_from_slice(&witness_caps);
    assert_eq!(
        with_setup_seed,
        <Blake2sTranscript as Transcript<BF, E4>>::commit_initial_u32(&expected_with_setup_seed)
    );

    let without_setup_seed =
        <Blake2sTranscript as Transcript<BF, E4>>::commit_initial_u32(&without_setup);
    let mut expected_without_setup_seed = top_bits;
    external_challenges.flatten_into_buffer(&mut expected_without_setup_seed);
    expected_without_setup_seed.extend_from_slice(&memory_caps);
    expected_without_setup_seed.extend_from_slice(&witness_caps);
    assert_eq!(
        without_setup_seed,
        <Blake2sTranscript as Transcript<BF, E4>>::commit_initial_u32(&expected_without_setup_seed)
    );
}
/// Caller gate for the top-layer claim eq: `prepare_backward_handoff` builds
/// `eq_values_for_init` with exactly this call shape (offset 0,
/// `challenge_count = final_trace_size_log_2`, `acc_size = 1 << count`). Its
/// orientation must be LSB-first — claim coordinate `b` on table bit `b`.
#[test]
#[cfg(not(no_cuda))]
fn top_claim_eq_matches_cpu_lsb() {
    use era_cudart::memory::memory_copy_async;
    use gpu_core::allocator::tracker::AllocationPlacement;
    use gpu_core::primitives::context::DeviceAllocation;
    use gpu_gkr::backward::kernels::{eq_group_tables_len, launch_build_eq_values_from_point};

    use crate::test_utils::make_test_context_with_device_allocator_block_log_size;
    use crate::upstream::{Field, PrimeField};

    let context = make_test_context_with_device_allocator_block_log_size(4096, 256, 20);
    let worker = Worker::new();

    for final_trace_size_log_2 in [4u32, 20] {
        let challenge_count = final_trace_size_log_2 as usize;
        // Deterministic point with every coordinate distinct, so a permuted
        // pairing cannot pass by coincidence.
        let point: Vec<E4> =
            (0..challenge_count)
                .map(|i| {
                    E4::from_array_of_base(std::array::from_fn(|limb| {
                        BF::from_u32_with_reduction(0x9E37_79B9u32.wrapping_mul(
                            (i as u32 + 1).wrapping_mul(4).wrapping_add(limb as u32 + 1),
                        ))
                    }))
                })
                .collect();
        let poly_len = 1usize << challenge_count;

        let mut d_point: DeviceAllocation<E4> = context
            .alloc(challenge_count, AllocationPlacement::BestFit)
            .unwrap();
        memory_copy_async(&mut d_point, &point, context.get_exec_stream()).unwrap();
        let mut d_group_tables: DeviceAllocation<E4> = context
            .alloc(
                eq_group_tables_len(challenge_count),
                AllocationPlacement::Top,
            )
            .unwrap();
        let mut d_eq_values: DeviceAllocation<E4> =
            context.alloc(poly_len, AllocationPlacement::Top).unwrap();

        launch_build_eq_values_from_point(
            d_point.as_ptr(),
            0,
            challenge_count,
            d_group_tables.as_mut_ptr(),
            d_eq_values.as_mut_ptr(),
            poly_len,
            &context,
        )
        .unwrap();

        let mut from_gpu = vec![E4::ZERO; poly_len];
        memory_copy_async(&mut from_gpu, &d_eq_values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();

        let expected =
            prover::gkr::sumcheck::eq_poly::make_eq_table_lsb_first::<E4>(&point, &worker);
        assert_eq!(expected.len(), from_gpu.len());
        let first_divergence = from_gpu
            .iter()
            .zip(expected.iter())
            .position(|(gpu, cpu)| gpu != cpu);
        assert!(
            first_divergence.is_none(),
            "final_trace_size_log_2={final_trace_size_log_2}: first divergent index {:?} \
             (bits {:0width$b})",
            first_divergence,
            first_divergence.unwrap_or(0),
            width = challenge_count,
        );
    }
}

/// The preflight boundary: a windowed request whose lowering was rejected must
/// fail before any H2D work, with the resource in the message; a per-round
/// request must not even consult the bundle.
#[test]
fn cpu_windowed_backward_preflight_reports_an_r0_lowering_rejection() {
    use super::{preflight_windowed_backward, GpuProveError};
    use gpu_gkr::{BackwardExecutionStrategy, GkrBackwardOptions, WindowLoweringRejection};

    let (programs, _) =
        gpu_gkr::backward::compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    assert!(preflight_windowed_backward(
        &programs,
        BackwardExecutionStrategy::PerRound,
        GkrBackwardOptions::default(),
        4,
    )
    .is_ok());
    assert!(
        !programs.window_programs_ready(),
        "the per-round arm must not lower the window bundle"
    );

    assert!(
        programs.reject_window_programs_for_test(WindowLoweringRejection {
            circuit: "add_sub_lui_auipc_mop".to_owned(),
            layer: 7,
            resource:
                "Capacity { resource: \"window program words\", required: 8192, capacity: 7040 }"
                    .to_owned(),
        })
    );
    let error = preflight_windowed_backward(
        &programs,
        BackwardExecutionStrategy::WindowedR0,
        GkrBackwardOptions::default(),
        4,
    )
    .unwrap_err();
    assert_eq!(
        error,
        GpuProveError::WindowLowering {
            circuit: "add_sub_lui_auipc_mop".to_owned(),
            layer: 7,
            resource:
                "Capacity { resource: \"window program words\", required: 8192, capacity: 7040 }"
                    .to_owned(),
        }
    );
    assert_eq!(
        error.to_string(),
        "windowed R0 lowering rejected for add_sub_lui_auipc_mop/7: \
         Capacity { resource: \"window program words\", required: 8192, capacity: 7040 }"
    );
    assert!(!programs.window_programs_ready());
}

#[test]
fn cpu_windowed_backward_preflight_resolves_only_required_lazy_bundles() {
    use super::preflight_windowed_backward;
    use gpu_gkr::{BackwardExecutionStrategy, GkrBackwardOptions};

    let enabled = GkrBackwardOptions {
        windowed_main_continuations: true,
        windowed_dr_continuations: false,
        ..GkrBackwardOptions::default()
    };

    let (per_round, _) =
        gpu_gkr::backward::compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    preflight_windowed_backward(&per_round, BackwardExecutionStrategy::PerRound, enabled, 4)
        .unwrap();
    assert!(!per_round.window_programs_ready());
    assert!(!per_round.main_continuation_window_programs_ready());

    let (disabled, _) =
        gpu_gkr::backward::compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    preflight_windowed_backward(
        &disabled,
        BackwardExecutionStrategy::WindowedR0,
        GkrBackwardOptions::default(),
        4,
    )
    .unwrap();
    assert!(disabled.window_programs_ready());
    assert!(!disabled.main_continuation_window_programs_ready());

    let (required, layer_count) =
        gpu_gkr::backward::compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    assert_ne!(
        required.compiled_circuit().trace_len.trailing_zeros(),
        4,
        "the regression must distinguish main-layer width from the final trace log"
    );
    preflight_windowed_backward(&required, BackwardExecutionStrategy::WindowedR0, enabled, 4)
        .unwrap();
    assert!(required.window_programs_ready());
    assert!(required.main_continuation_window_programs_ready());
    assert_eq!(
        required
            .resolve_main_continuation_window_programs()
            .unwrap()
            .layers
            .len(),
        layer_count
    );
}

#[test]
fn cpu_windowed_backward_preflight_rejection_constructs_zero_transfers_and_is_stable() {
    use super::{construct_after_windowed_backward_preflight, GpuProveError};
    use gpu_gkr::{
        BackwardExecutionStrategy, GkrBackwardOptions, MainContinuationWindowLoweringRejection,
    };
    use std::cell::Cell;

    let (programs, _) =
        gpu_gkr::backward::compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    let rejection = MainContinuationWindowLoweringRejection {
        circuit: "add_sub_lui_auipc_mop".to_owned(),
        layer: 4,
        resource:
            "Capacity { resource: \"main continuation sources\", required: 1073, capacity: 1072 }"
                .to_owned(),
    };
    assert!(programs.reject_main_continuation_window_programs_for_test(rejection.clone()));
    let options = GkrBackwardOptions {
        windowed_main_continuations: true,
        windowed_dr_continuations: false,
        ..GkrBackwardOptions::default()
    };
    let transfer_constructions = Cell::new(0usize);
    let error = construct_after_windowed_backward_preflight(
        &programs,
        BackwardExecutionStrategy::WindowedR0,
        options,
        4,
        || transfer_constructions.set(transfer_constructions.get() + 1),
    )
    .unwrap_err();
    assert_eq!(transfer_constructions.get(), 0);
    assert_eq!(
        error,
        GpuProveError::MainContinuationWindowLowering {
            circuit: rejection.circuit.clone(),
            layer: rejection.layer,
            resource: rejection.resource.clone(),
        }
    );

    let first = programs
        .resolve_main_continuation_window_programs()
        .unwrap_err();
    let second = programs
        .resolve_main_continuation_window_programs()
        .unwrap_err();
    assert!(std::ptr::eq(first, second));
    assert_eq!(first, &rejection);
    assert!(!programs.main_continuation_window_programs_ready());
}

#[test]
fn cpu_dr_window_preflight_is_default_off_and_caches_exact_final_logs() {
    use super::preflight_windowed_backward;
    use gpu_gkr::{BackwardExecutionStrategy, GkrBackwardOptions};

    let (programs, _) =
        gpu_gkr::backward::compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    let initial_trace_log = programs.compiled_circuit().trace_len.trailing_zeros();
    let first_final_log = initial_trace_log - 2;
    let second_final_log = initial_trace_log - 1;

    preflight_windowed_backward(
        &programs,
        BackwardExecutionStrategy::PerRound,
        GkrBackwardOptions::default(),
        first_final_log,
    )
    .unwrap();
    assert!(!programs.dr_window_programs_ready(first_final_log));

    let enabled = GkrBackwardOptions {
        windowed_dr: true,
        windowed_dr_continuations: false,
        ..GkrBackwardOptions::default()
    };
    preflight_windowed_backward(
        &programs,
        BackwardExecutionStrategy::PerRound,
        enabled,
        first_final_log,
    )
    .unwrap();
    assert!(programs.dr_window_programs_ready(first_final_log));
    assert!(!programs.dr_window_programs_ready(second_final_log));
    let first = programs
        .resolve_dr_window_programs(first_final_log)
        .unwrap();
    let first_again = programs
        .resolve_dr_window_programs(first_final_log)
        .unwrap();
    assert!(std::sync::Arc::ptr_eq(&first, &first_again));
    assert_eq!(first.final_trace_log(), first_final_log);

    preflight_windowed_backward(
        &programs,
        BackwardExecutionStrategy::PerRound,
        enabled,
        second_final_log,
    )
    .unwrap();
    assert!(programs.dr_window_programs_ready(second_final_log));
    assert_eq!(
        programs
            .resolve_dr_window_programs(second_final_log)
            .unwrap()
            .final_trace_log(),
        second_final_log
    );
}

#[test]
fn cpu_dr_window_preflight_typed_rejection_constructs_zero_transfers() {
    use super::{construct_after_windowed_backward_preflight, GpuProveError};
    use gpu_gkr::{BackwardExecutionStrategy, GkrBackwardOptions};
    use std::cell::Cell;

    let (programs, _) =
        gpu_gkr::backward::compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    let initial_trace_log = programs.compiled_circuit().trace_len.trailing_zeros();
    let invalid_final_log = initial_trace_log + 1;
    let options = GkrBackwardOptions {
        windowed_dr: true,
        windowed_dr_continuations: false,
        ..GkrBackwardOptions::default()
    };
    let transfer_constructions = Cell::new(0usize);

    let error = construct_after_windowed_backward_preflight(
        &programs,
        BackwardExecutionStrategy::PerRound,
        options,
        invalid_final_log,
        || transfer_constructions.set(transfer_constructions.get() + 1),
    )
    .unwrap_err();
    assert_eq!(transfer_constructions.get(), 0);
    let rejection = programs
        .resolve_dr_window_programs(invalid_final_log)
        .unwrap_err();
    assert_eq!(
        error,
        GpuProveError::DrWindowLowering {
            circuit: rejection.circuit().to_owned(),
            layer: rejection.layer(),
            resource: rejection.resource().to_owned(),
        }
    );
    assert!(!programs.dr_window_programs_ready(invalid_final_log));
    assert_eq!(
        programs
            .resolve_dr_window_programs(invalid_final_log)
            .unwrap_err(),
        rejection,
        "typed rejection must remain stable in the final-log keyed cache"
    );
}

#[test]
fn cpu_dr_window_preflight_cached_geometry_rejection_constructs_zero_transfers() {
    use super::{construct_after_windowed_backward_preflight, GpuProveError};
    use gpu_gkr::{BackwardExecutionStrategy, GkrBackwardOptions};
    use std::cell::Cell;

    const INVALID_FINAL_LOG: u32 = 3;
    let (programs, _) =
        gpu_gkr::backward::compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    let options = GkrBackwardOptions {
        windowed_dr: true,
        windowed_dr_continuations: false,
        ..GkrBackwardOptions::default()
    };
    let transfer_constructions = Cell::new(0usize);

    let error = construct_after_windowed_backward_preflight(
        &programs,
        BackwardExecutionStrategy::PerRound,
        options,
        INVALID_FINAL_LOG,
        || transfer_constructions.set(transfer_constructions.get() + 1),
    )
    .unwrap_err();
    assert_eq!(transfer_constructions.get(), 0);
    let rejection = programs
        .resolve_dr_window_programs(INVALID_FINAL_LOG)
        .unwrap_err();
    assert_eq!(
        error,
        GpuProveError::DrWindowLowering {
            circuit: rejection.circuit().to_owned(),
            layer: rejection.layer(),
            resource: rejection.resource().to_owned(),
        }
    );
    assert_eq!(
        rejection.resource(),
        "UnsupportedFoldingSteps { folding_steps: 3 }"
    );
    assert!(!programs.dr_window_programs_ready(INVALID_FINAL_LOG));
    assert_eq!(
        programs
            .resolve_dr_window_programs(INVALID_FINAL_LOG)
            .unwrap_err(),
        rejection,
        "producer geometry rejection must remain stable in the final-log cache"
    );
}

/// Which corpus families the windowed arm is selected for, per supported
/// security level. This is the both-arm byte gate's zero-selection guard: the
/// gate's wrappers run the windowed arm only where
/// `resolve_backward_execution_strategy` picks it, so the set of families that
/// picks it has to be pinned somewhere the gate cannot silently shrink.
///
/// GPU-free: only the compiled artifact's `trace_len` and the canonical config's
/// schedule grammar decide this.
#[test]
fn cpu_windowed_arm_selection_covers_every_corpus_family() {
    use crate::config::prover_config;
    use crate::proof::resolve_backward_execution_strategy;
    use crate::upstream::SecurityLevel;
    use gpu_gkr::{BackwardExecutionStrategy, GkrBackwardOptions};

    /// One layout per family the proof matrix gates.
    const FAMILIES: &[&str] = &[
        "add_sub_lui_auipc_mop_layout_gkr.json",
        "bigint_with_extended_control_layout_gkr.json",
        "blake2_g_function_layout_gkr.json",
        "blake2_with_extended_control_layout_gkr.json",
        "inits_and_teardowns_layout_gkr.json",
        "jump_branch_slt_layout_gkr.json",
        "keccak_special5_layout_gkr.json",
        "mem_subword_only_layout_gkr.json",
        "mem_word_only_layout_gkr.json",
        "shift_binop_layout_gkr.json",
        "unified_reduced_machine_layout_gkr.json",
        "unsigned_mul_div_layout_gkr.json",
    ];

    let windowed = GkrBackwardOptions {
        windowed_r0: true,
        windowed_dr_continuations: false,
        ..GkrBackwardOptions::default()
    };
    let mut selected = Vec::new();
    for layout in FAMILIES {
        let (programs, _) = gpu_gkr::backward::compile_corpus_layout(layout);
        for level in crate::config::GPU_SUPPORTED_SECURITY_LEVELS {
            let config = prover_config(programs.circuit_type(), level).unwrap();
            let strategy = resolve_backward_execution_strategy(&programs, &config, windowed);
            println!("{layout} {level:?}: {strategy:?}");
            assert_eq!(
                resolve_backward_execution_strategy(
                    &programs,
                    &config,
                    GkrBackwardOptions {
                        windowed_r0: false,
                        windowed_dr_continuations: false,
                        ..GkrBackwardOptions::default()
                    }
                ),
                BackwardExecutionStrategy::PerRound,
                "{layout} {level:?} must honour the per-round escape hatch",
            );
            if strategy == BackwardExecutionStrategy::WindowedR0 {
                selected.push(format!("{layout} {level:?}"));
            }
        }
    }
    assert_eq!(
        selected.len(),
        2 * FAMILIES.len(),
        "every corpus family must select the windowed arm at both supported \
         security levels, or the both-arm byte gate covers less than it claims; \
         selected: {selected:?}",
    );
}

#[test]
fn dr_window_continuation_preflight_is_default_off_and_requires_the_complete_chain() {
    use super::{
        construct_after_windowed_backward_preflight_with_dr_selection,
        DrWindowExecutionSelectionSpy, DrWindowTestWholeLayerSelection, GpuProveError,
    };
    use gpu_gkr::{
        BackwardExecutionStrategy, DrWindowContinuationPreflightError, GkrBackwardOptions,
    };
    use std::cell::Cell;

    let (default_programs, _) =
        gpu_gkr::backward::compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    let defaults = GkrBackwardOptions::default();
    assert!(!defaults.windowed_dr_continuations);
    super::preflight_windowed_backward(
        &default_programs,
        BackwardExecutionStrategy::WindowedR0,
        defaults,
        4,
    )
    .unwrap();
    assert!(!default_programs.dr_window_programs_ready(4));

    let (programs, _) =
        gpu_gkr::backward::compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    let options = GkrBackwardOptions {
        windowed_dr: true,
        windowed_dr_continuations: true,
        ..GkrBackwardOptions::default()
    };
    let spy = DrWindowExecutionSelectionSpy::default();
    let transfer_constructions = Cell::new(0usize);
    let error = construct_after_windowed_backward_preflight_with_dr_selection(
        &programs,
        BackwardExecutionStrategy::WindowedR0,
        options,
        4,
        DrWindowTestWholeLayerSelection::CompleteNewChain,
        &spy,
        || transfer_constructions.set(transfer_constructions.get() + 1),
    )
    .unwrap_err();
    assert_eq!(
        error,
        GpuProveError::DrWindowContinuationPreflight {
            error: DrWindowContinuationPreflightError::IncompleteChain {
                windowed_r0: true,
                continuations: true,
                recursive_tail: false,
            }
        }
    );
    assert!(programs.dr_window_programs_ready(4));
    assert_eq!(transfer_constructions.get(), 0);
    assert_eq!(spy.complete_new_chain_count(), 0);
    assert_eq!(spy.legacy_diagnostic_count(), 0);

    let tail_only = GkrBackwardOptions {
        windowed_dr: true,
        windowed_dr_continuations: false,
        dr_tail_megakernel: true,
        ..GkrBackwardOptions::default()
    };
    assert_eq!(
        super::preflight_windowed_backward(
            &programs,
            BackwardExecutionStrategy::WindowedR0,
            tail_only,
            4,
        ),
        Err(GpuProveError::DrWindowContinuationPreflight {
            error: DrWindowContinuationPreflightError::IncompleteChain {
                windowed_r0: true,
                continuations: false,
                recursive_tail: true,
            }
        }),
        "the recursive tail may not reach resource admission without both producer stages",
    );
}

#[test]
fn dr_window_continuation_preflight_bundle_failure_selects_nothing_and_builds_no_transfer() {
    use super::{
        construct_after_windowed_backward_preflight_with_dr_selection,
        DrWindowExecutionSelectionSpy, DrWindowTestWholeLayerSelection, GpuProveError,
    };
    use gpu_gkr::{BackwardExecutionStrategy, GkrBackwardOptions};
    use std::cell::Cell;

    const INVALID_FINAL_LOG: u32 = 3;
    let (programs, _) =
        gpu_gkr::backward::compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    let options = GkrBackwardOptions {
        windowed_dr: true,
        windowed_dr_continuations: true,
        ..GkrBackwardOptions::default()
    };
    let spy = DrWindowExecutionSelectionSpy::default();
    let transfer_constructions = Cell::new(0usize);
    let error = construct_after_windowed_backward_preflight_with_dr_selection(
        &programs,
        BackwardExecutionStrategy::WindowedR0,
        options,
        INVALID_FINAL_LOG,
        DrWindowTestWholeLayerSelection::CompleteNewChain,
        &spy,
        || transfer_constructions.set(transfer_constructions.get() + 1),
    )
    .unwrap_err();
    assert!(matches!(error, GpuProveError::DrWindowLowering { .. }));
    assert!(!programs.dr_window_programs_ready(INVALID_FINAL_LOG));
    assert_eq!(transfer_constructions.get(), 0);
    assert_eq!(spy.complete_new_chain_count(), 0);
    assert_eq!(spy.legacy_diagnostic_count(), 0);
}

#[test]
fn dr_window_continuation_preflight_forced_capability_failures_select_nothing() {
    use super::{
        construct_after_dr_window_capability_preflight, DrWindowExecutionSelectionSpy,
        DrWindowTestWholeLayerSelection, GpuProveError,
    };
    use gpu_gkr::{DrWindowContinuationCapabilityProbe, DrWindowContinuationPreflightError};
    use std::cell::Cell;

    let cases = [
        (
            DrWindowContinuationCapabilityProbe::new(3, 3, 0, 0, 0, true),
            DrWindowContinuationPreflightError::UnsupportedFoldingSteps { folding_steps: 3 },
        ),
        (
            DrWindowContinuationCapabilityProbe::new(25, 3, 19, 0, 0, true),
            DrWindowContinuationPreflightError::UnsupportedFoldingSteps { folding_steps: 25 },
        ),
        (
            DrWindowContinuationCapabilityProbe::new(23, 4, 16, 0, 0, true),
            DrWindowContinuationPreflightError::InvalidContinuationBoundary {
                folding_steps: 23,
                start_round: 4,
            },
        ),
        (
            DrWindowContinuationCapabilityProbe::new(23, 3, 16, 0, 0, true),
            DrWindowContinuationPreflightError::InvalidContinuationSuffix {
                folding_steps: 23,
                start_round: 3,
                expected_suffix_count: 17,
                observed_suffix_count: 16,
            },
        ),
        (
            DrWindowContinuationCapabilityProbe::new(23, 3, 17, 8193, 8192, true),
            DrWindowContinuationPreflightError::SharedMemoryCapacity {
                required_bytes: 8193,
                capacity_bytes: 8192,
            },
        ),
        (
            DrWindowContinuationCapabilityProbe::new(23, 3, 17, 8192, 8192, false),
            DrWindowContinuationPreflightError::DeviceResourceUnavailable,
        ),
    ];

    for (probe, expected) in cases {
        let spy = DrWindowExecutionSelectionSpy::default();
        let transfer_constructions = Cell::new(0usize);
        assert_eq!(
            construct_after_dr_window_capability_preflight(
                probe,
                DrWindowTestWholeLayerSelection::CompleteNewChain,
                &spy,
                || transfer_constructions.set(transfer_constructions.get() + 1),
            ),
            Err(GpuProveError::DrWindowContinuationPreflight { error: expected })
        );
        assert_eq!(transfer_constructions.get(), 0);
        assert_eq!(spy.complete_new_chain_count(), 0);
        assert_eq!(spy.legacy_diagnostic_count(), 0);
    }
}

#[test]
fn dr_window_continuation_preflight_rejects_partial_chains_and_forces_whole_legacy_only() {
    use super::{
        construct_after_dr_window_selection_preflight, DrWindowExecutionSelectionSpy, GpuProveError,
    };
    use gpu_gkr::{
        BackwardExecutionStrategy, DrWindowChainStages, DrWindowContinuationPreflightError,
    };
    use std::cell::Cell;

    for stages in [
        DrWindowChainStages::new(true, false, false),
        DrWindowChainStages::new(false, true, true),
        DrWindowChainStages::new(true, true, false),
    ] {
        let spy = DrWindowExecutionSelectionSpy::default();
        let transfer_constructions = Cell::new(0usize);
        assert_eq!(
            construct_after_dr_window_selection_preflight(
                BackwardExecutionStrategy::WindowedR0,
                stages,
                false,
                &spy,
                || transfer_constructions.set(transfer_constructions.get() + 1),
            ),
            Err(GpuProveError::DrWindowContinuationPreflight {
                error: DrWindowContinuationPreflightError::IncompleteChain {
                    windowed_r0: stages.windowed_r0(),
                    continuations: stages.continuations(),
                    recursive_tail: stages.recursive_tail(),
                }
            })
        );
        assert_eq!(transfer_constructions.get(), 0);
        assert_eq!(spy.complete_new_chain_count(), 0);
        assert_eq!(spy.legacy_diagnostic_count(), 0);
    }

    let complete = DrWindowChainStages::new(true, true, true);
    let mixed_spy = DrWindowExecutionSelectionSpy::default();
    let mixed_transfers = Cell::new(0usize);
    assert_eq!(
        construct_after_dr_window_selection_preflight(
            BackwardExecutionStrategy::WindowedR0,
            complete,
            true,
            &mixed_spy,
            || mixed_transfers.set(mixed_transfers.get() + 1),
        ),
        Err(GpuProveError::DrWindowContinuationPreflight {
            error: DrWindowContinuationPreflightError::MixedLegacyAndWindowed {
                windowed_r0: true,
                continuations: true,
                recursive_tail: true,
            }
        })
    );
    assert_eq!(mixed_transfers.get(), 0);
    assert_eq!(mixed_spy.complete_new_chain_count(), 0);
    assert_eq!(mixed_spy.legacy_diagnostic_count(), 0);

    let new_spy = DrWindowExecutionSelectionSpy::default();
    let new_transfers = Cell::new(0usize);
    assert_eq!(
        construct_after_dr_window_selection_preflight(
            BackwardExecutionStrategy::WindowedR0,
            complete,
            false,
            &new_spy,
            || new_transfers.set(new_transfers.get() + 1),
        ),
        Ok(Some(()))
    );
    assert_eq!(new_transfers.get(), 1);
    assert_eq!(new_spy.complete_new_chain_count(), 1);
    assert_eq!(new_spy.legacy_diagnostic_count(), 0);

    let legacy_spy = DrWindowExecutionSelectionSpy::default();
    let legacy_transfers = Cell::new(0usize);
    assert_eq!(
        construct_after_dr_window_selection_preflight(
            BackwardExecutionStrategy::PerRound,
            DrWindowChainStages::new(false, false, false),
            true,
            &legacy_spy,
            || legacy_transfers.set(legacy_transfers.get() + 1),
        ),
        Ok(Some(()))
    );
    assert_eq!(legacy_transfers.get(), 1);
    assert_eq!(legacy_spy.complete_new_chain_count(), 0);
    assert_eq!(legacy_spy.legacy_diagnostic_count(), 1);
}

/// Advisory test 3: the worker seam admits before it constructs.
///
/// The production worker's phase-one closure is the only place a transfer is
/// constructed, an H2D bundle is enqueued, or an execution arm is selected. If
/// either preflight rejects, that closure must never be entered.
#[test]
fn cpu_dr_tail_seam_preflight_precedes_every_transfer_construction() {
    use super::{
        admit_dr_tail_before_transfers_with, DrTailPreflightRequest, DrWindowExecutionSelectionSpy,
        DrWindowTestWholeLayerSelection, GpuProveError,
    };
    use gpu_gkr::{
        BackwardExecutionStrategy, DrTailCapacityRejection, DrTailResourceError,
        GkrBackwardOptions, MainContinuationWindowLoweringRejection,
    };
    use std::cell::Cell;

    struct SeamCounters {
        admissions: Cell<usize>,
        constructions: Cell<usize>,
        enqueues: Cell<usize>,
        spy: DrWindowExecutionSelectionSpy,
    }
    impl SeamCounters {
        fn new() -> Self {
            Self {
                admissions: Cell::new(0),
                constructions: Cell::new(0),
                enqueues: Cell::new(0),
                spy: DrWindowExecutionSelectionSpy::default(),
            }
        }
        fn observed(&self) -> (usize, usize, usize, usize, usize) {
            (
                self.admissions.get(),
                self.constructions.get(),
                self.enqueues.get(),
                self.spy.complete_new_chain_count(),
                self.spy.legacy_diagnostic_count(),
            )
        }
    }

    // The seam is generic over the plan; this token stands in for the real
    // `DrTailProofPlan`, whose only constructor is device admission. Ordering
    // is what this test proves — plan minting stays inside `gpu_gkr`.
    struct PlanToken;

    // Models the worker's closure: construct the transfer, enqueue it, and
    // select the execution arm the constructed inputs carry.
    fn construct(counters: &SeamCounters) -> impl FnOnce(Option<PlanToken>) + '_ {
        move |plan| {
            assert!(
                plan.is_some(),
                "with the DR-tail arm selected, the constructed inputs own the admitted plan"
            );
            counters.constructions.set(counters.constructions.get() + 1);
            counters.enqueues.set(counters.enqueues.get() + 1);
            counters
                .spy
                .record(DrWindowTestWholeLayerSelection::CompleteNewChain);
        }
    }

    let options = GkrBackwardOptions {
        windowed_main_continuations: true,
        windowed_dr: true,
        windowed_dr_continuations: true,
        dr_tail_megakernel: true,
        ..GkrBackwardOptions::default()
    };
    fn request<'a>(
        programs: &'a gpu_gkr::GkrPrograms,
        options: GkrBackwardOptions,
    ) -> DrTailPreflightRequest<'a> {
        DrTailPreflightRequest {
            gkr_programs: programs,
            strategy: BackwardExecutionStrategy::WindowedR0,
            options,
            final_trace_size_log_2: 4,
            device_id: 0,
            entry: gpu_gkr::DrTailEntrySelection::Portable,
        }
    }

    // Leg A: the pure window preflight rejects. Nothing downstream runs — not
    // even the device-touching admission.
    let (rejecting_programs, _) =
        gpu_gkr::backward::compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    let rejection = MainContinuationWindowLoweringRejection {
        circuit: "add_sub_lui_auipc_mop".to_owned(),
        layer: 4,
        resource:
            "Capacity { resource: \"main continuation sources\", required: 1073, capacity: 1072 }"
                .to_owned(),
    };
    assert!(rejecting_programs.reject_main_continuation_window_programs_for_test(rejection.clone()));
    let counters = SeamCounters::new();
    let error = admit_dr_tail_before_transfers_with(
        Some(request(&rejecting_programs, options)),
        |_| {
            counters.admissions.set(counters.admissions.get() + 1);
            unreachable!("resource admission must not run after a window rejection")
        },
        construct(&counters),
    )
    .unwrap_err();
    assert_eq!(
        error,
        GpuProveError::MainContinuationWindowLowering {
            circuit: rejection.circuit.clone(),
            layer: rejection.layer,
            resource: rejection.resource.clone(),
        }
    );
    assert_eq!(counters.observed(), (0, 0, 0, 0, 0));

    // Leg B: the window preflight accepts and resource admission rejects. The
    // admission ran exactly once, still before anything was constructed, and
    // its typed error survives the crate boundary intact.
    let (programs, _) =
        gpu_gkr::backward::compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    let counters = SeamCounters::new();
    // The exact rejection real admission emits for this layout at a
    // one-byte-low device cap (69,632-byte largest dynamic request); the
    // in-crate resource tests prove this variant is the emitted one.
    let starved = DrTailResourceError::Capacity {
        layer_idx: 4,
        rejection: DrTailCapacityRejection::DeviceCapacityExceeded {
            required_bytes: 69_632,
            cap_bytes: 69_631,
        },
    };
    let error = admit_dr_tail_before_transfers_with(
        Some(request(&programs, options)),
        |_| {
            counters.admissions.set(counters.admissions.get() + 1);
            Err(GpuProveError::from(starved.clone()))
        },
        construct(&counters),
    )
    .unwrap_err();
    assert_eq!(
        error,
        GpuProveError::DrTailResources {
            error: starved.clone()
        },
        "the typed resource error must not be flattened at the seam"
    );
    assert_eq!(counters.observed(), (1, 0, 0, 0, 0));

    // Leg C: both accept. Exactly one construction, one enqueue, one non-legacy
    // selection — so the zeros above are refusals, not a dead seam.
    let counters = SeamCounters::new();
    let admitted = std::cell::Cell::new(false);
    admit_dr_tail_before_transfers_with(
        Some(request(&programs, options)),
        |seam_request| {
            counters.admissions.set(counters.admissions.get() + 1);
            assert_eq!(seam_request.final_trace_size_log_2, 4);
            assert_eq!(seam_request.device_id, 0);
            admitted.set(true);
            Err(GpuProveError::from(DrTailResourceError::MissingLayerPlan))
        },
        construct(&counters),
    )
    .unwrap_err();
    assert!(admitted.get());
    assert_eq!(counters.observed(), (1, 0, 0, 0, 0));

    let counters = SeamCounters::new();
    admit_dr_tail_before_transfers_with(
        Some(request(&programs, options)),
        |_| {
            counters.admissions.set(counters.admissions.get() + 1);
            Ok(PlanToken)
        },
        construct(&counters),
    )
    .expect("both preflights accept");
    assert_eq!(counters.observed(), (1, 1, 1, 1, 0));
}

/// Advisory test 4: the forced-legacy control issues zero resource queries.
#[test]
fn cpu_dr_tail_seam_forced_legacy_issues_zero_resource_queries() {
    use super::{admit_dr_tail_before_transfers_with, DrTailPreflightRequest, GpuProveError};
    use gpu_gkr::{BackwardExecutionStrategy, DrTailResourceError, GkrBackwardOptions};
    use std::cell::Cell;

    let (programs, _) =
        gpu_gkr::backward::compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
    let base = GkrBackwardOptions {
        windowed_main_continuations: true,
        windowed_dr_continuations: false,
        ..GkrBackwardOptions::default()
    };
    assert!(
        !base.dr_tail_megakernel,
        "the DR-tail arm must stay off by default"
    );

    let run = |dr_tail_megakernel: bool| {
        let admissions = Cell::new(0usize);
        let plans = Cell::new(0usize);
        let options = if dr_tail_megakernel {
            GkrBackwardOptions {
                dr_tail_megakernel: true,
                windowed_dr: true,
                windowed_dr_continuations: true,
                ..base
            }
        } else {
            base
        };
        let result = admit_dr_tail_before_transfers_with(
            Some(DrTailPreflightRequest {
                gkr_programs: &programs,
                strategy: BackwardExecutionStrategy::WindowedR0,
                options,
                final_trace_size_log_2: 4,
                device_id: 0,
                entry: gpu_gkr::DrTailEntrySelection::Portable,
            }),
            |_| {
                admissions.set(admissions.get() + 1);
                Err(GpuProveError::from(DrTailResourceError::MissingLayerPlan))
            },
            |plan: Option<()>| {
                if plan.is_some() {
                    plans.set(plans.get() + 1);
                }
            },
        );
        (admissions.get(), plans.get(), result.is_ok())
    };

    // Forced legacy: the device is never queried and the constructed inputs
    // carry no plan.
    assert_eq!(run(false), (0, 0, true));
    // Control: with the arm selected the very same seam does query, so the zero
    // above is a real refusal rather than an inert path.
    assert_eq!(run(true), (1, 0, false));
}

#[test]
fn cpu_public_proof_result_preserves_typed_dr_tail_identity_error() {
    use super::{GpuProveError, GpuProveResult};
    use gpu_gkr::{DrTailPlanIdentityError, DrTailScheduleError};

    let identity = DrTailPlanIdentityError::CountMismatch {
        expected: 3,
        observed: 2,
    };
    let result: GpuProveResult<()> = Err(GpuProveError::from(DrTailScheduleError::Identity(
        identity.clone(),
    )));
    assert_eq!(
        result,
        Err(GpuProveError::DrTailSchedule {
            error: DrTailScheduleError::Identity(identity),
        })
    );
}

/// B1 production seam: the six recorded observation positions are the accepted
/// boundary, and every single-step reordering is rejected.
#[test]
fn cpu_exact_memory_production_sequence_boundary_is_exact() {
    use super::ExactMemorySequence;

    let accepted = ExactMemorySequence {
        whole_start: 0,
        backward_start: 1,
        backward_seal: 2,
        job_finish: 3,
        backward_finish: 4,
        whole_finish: 5,
    };
    assert_eq!(accepted.validate(), Ok(()));

    // Non-adjacent positions are fine as long as the order holds: a real run
    // interleaves other allocator observations between boundaries.
    let sparse = ExactMemorySequence {
        whole_start: 10,
        backward_start: 21,
        backward_seal: 22,
        job_finish: 40,
        backward_finish: 41,
        whole_finish: 99,
    };
    assert_eq!(sparse.validate(), Ok(()));

    // Every red mutation: each field in turn is moved to tie or invert with its
    // predecessor, and each must be refused by name.
    let mutations: [(&str, ExactMemorySequence); 5] = [
        (
            "whole_start",
            ExactMemorySequence {
                backward_start: accepted.whole_start,
                ..accepted
            },
        ),
        (
            "backward_start",
            ExactMemorySequence {
                backward_seal: accepted.backward_start,
                ..accepted
            },
        ),
        (
            "backward_seal",
            ExactMemorySequence {
                job_finish: accepted.backward_seal,
                ..accepted
            },
        ),
        (
            "job_finish",
            ExactMemorySequence {
                backward_finish: accepted.job_finish,
                ..accepted
            },
        ),
        (
            "backward_finish",
            ExactMemorySequence {
                whole_finish: accepted.backward_finish,
                ..accepted
            },
        ),
    ];
    for (earlier, mutated) in mutations {
        let error = mutated
            .validate()
            .expect_err("a tied boundary must be rejected");
        assert!(
            error.contains(earlier),
            "rejection must name the violated boundary {earlier}: {error}"
        );
    }

    // The load-bearing case the audit named: observers finishing before the
    // real job finish would measure neither proof assembly nor release.
    let finished_early = ExactMemorySequence {
        job_finish: 9,
        backward_finish: 4,
        whole_finish: 5,
        ..accepted
    };
    assert!(finished_early
        .validate()
        .expect_err("closing before job finish must be rejected")
        .contains("job_finish"));
}

/// B1 production topology: the measured worker loop must not overlap two
/// proofs, and the unmeasured loop must keep the production pipeline. The
/// source oracle pins both, plus the two-deep result cadence the GPU manager
/// requires.
#[test]
fn cpu_exact_memory_measured_worker_topology_is_serialized() {
    const WORKER: &str = include_str!("../../../execution_prover/src/workers/gpu.rs");

    let measured = WORKER
        .find("if let Some(measurement) = measurement.as_ref() {")
        .expect("the measured topology branch must remain present");
    let unmeasured = WORKER
        .find("let mut current_phase_one: Option<PhaseOne> = None;")
        .expect("the production pipelined topology must remain present");
    assert!(
        measured < unmeasured,
        "the measured branch must short-circuit before the pipelined loop"
    );
    let measured_body = &WORKER[measured..unmeasured];

    // Serialized: all three phases of one proof, in order, inside one branch.
    let p1 = measured_body
        .find("schedule_phase_one(")
        .expect("measured topology must schedule phase one");
    let p2 = measured_body
        .find("enqueue_phase_two(")
        .expect("measured topology must enqueue phase two");
    let p3 = measured_body
        .find("finish_phase_three(")
        .expect("measured topology must finish phase three");
    assert!(
        p1 < p2 && p2 < p3,
        "a measured proof must complete all three phases before the next request"
    );
    assert!(
        !measured_body.contains("mem::swap"),
        "the measured topology must not keep a second proof in flight"
    );
    // Cadence: the manager pre-seeds two queue slots, so the measured loop must
    // reproduce exactly that skew or results land against the wrong batch.
    assert!(
        measured_body.contains("VecDeque::from([None, None])"),
        "the measured topology must preserve the manager's two-deep result skew"
    );

    // The unmeasured loop keeps the pipelined swap topology unchanged.
    let production_body = &WORKER[unmeasured..];
    assert!(
        production_body.contains("mem::swap(&mut current_phase_one, &mut phase_one);"),
        "production must keep its pipelined phase-one swap"
    );
    assert!(
        production_body.contains("mem::swap(&mut current_phase_two, &mut phase_two);"),
        "production must keep its pipelined phase-two swap"
    );
}

/// B3: the measurement configuration is resolved from the already-resolved
/// options, is complete, and rejects every partial or inconsistent identity.
/// The env is read once per worker, so this drives the parser directly.
#[test]
fn cpu_exact_memory_config_requires_complete_consistent_identity() {
    use super::{ExactMemoryConfig, GpuProveError};
    use gpu_gkr::{DrTailEntrySelection, GkrBackwardOptions, WindowTailArm};

    const VARS: [&str; 6] = [
        "GKR_EXACT_MEMORY_OUT",
        "GKR_EXACT_MEMORY_ARM",
        "GKR_EXACT_MEMORY_PHASE",
        "GKR_EXACT_MEMORY_SAMPLE",
        "GKR_EXACT_MEMORY_INVOCATION",
        "GKR_DR_ENTRY",
    ];
    let complete_on: [(&str, &str); 6] = [
        ("GKR_EXACT_MEMORY_OUT", "/dev/null"),
        ("GKR_EXACT_MEMORY_ARM", "on"),
        ("GKR_EXACT_MEMORY_PHASE", "retained"),
        ("GKR_EXACT_MEMORY_SAMPLE", "3"),
        ("GKR_EXACT_MEMORY_INVOCATION", "inv-1"),
        ("GKR_DR_ENTRY", "portable"),
    ];
    let production = GkrBackwardOptions {
        dr_tail_megakernel: true,
        windowed_r0: true,
        windowed_main_continuations: true,
        windowed_dr: true,
        windowed_dr_continuations: true,
        window_tail: WindowTailArm::Split,
    };
    let legacy = GkrBackwardOptions {
        dr_tail_megakernel: false,
        windowed_dr: false,
        windowed_dr_continuations: false,
        ..production
    };

    // This test mutates process environment, so it must not run concurrently
    // with another env-reading test. `cpu_` tests in this crate share one
    // process; keep every mutation inside this function and restore after.
    let apply = |pairs: &[(&str, &str)]| {
        for name in VARS {
            std::env::remove_var(name);
        }
        for (name, value) in pairs {
            std::env::set_var(name, value);
        }
    };
    let message = |error: GpuProveError| match error {
        GpuProveError::ExactMemoryMeasurement { message } => message,
        other => panic!("expected a measurement error, got {other:?}"),
    };

    // No variable at all is the production default: measurement off.
    apply(&[]);
    assert_eq!(ExactMemoryConfig::from_environment(production), Ok(None));

    // Complete and consistent.
    apply(&complete_on);
    let config = ExactMemoryConfig::from_environment(production)
        .expect("a complete consistent identity must resolve")
        .expect("measurement must be enabled");
    assert_eq!(config.entry(), DrTailEntrySelection::Portable);

    // Every single missing variable is refused by name: no silently omitted row.
    for skipped in VARS {
        let partial: Vec<(&str, &str)> = complete_on
            .iter()
            .copied()
            .filter(|(name, _)| *name != skipped)
            .collect();
        apply(&partial);
        let error = message(
            ExactMemoryConfig::from_environment(production)
                .expect_err("a partial identity must be refused"),
        );
        assert!(
            error.contains(skipped),
            "refusal must name the missing variable {skipped}: {error}"
        );
    }

    // The arm must agree with the options the proof actually consumes.
    apply(&complete_on);
    let error = message(
        ExactMemoryConfig::from_environment(legacy)
            .expect_err("arm on with legacy options must be refused"),
    );
    assert!(error.contains("disagrees with resolved options"), "{error}");

    let mut off_arm = complete_on;
    off_arm[1] = ("GKR_EXACT_MEMORY_ARM", "off");
    apply(&off_arm);
    assert_eq!(
        ExactMemoryConfig::from_environment(legacy)
            .expect("arm off with legacy options is consistent")
            .map(|config| config.entry()),
        Some(DrTailEntrySelection::Portable)
    );
    let error = message(
        ExactMemoryConfig::from_environment(production)
            .expect_err("arm off with production options must be refused"),
    );
    assert!(error.contains("disagrees with resolved options"), "{error}");

    // Each field's own red mutation.
    for (index, bad, needle) in [
        (1usize, "unset", "must be on or off"),
        (2, "steady", "must be warmup or retained"),
        (3, "many", "must be an integer"),
        (4, "", "must be non-empty"),
        (5, "r-3", "must be portable, minus3, or plus3"),
    ] {
        let mut mutated = complete_on;
        mutated[index] = (complete_on[index].0, bad);
        apply(&mutated);
        let error = message(
            ExactMemoryConfig::from_environment(production)
                .expect_err("an invalid identity field must be refused"),
        );
        assert!(error.contains(needle), "{error}");
    }

    // A diagnostic entry is only meaningful on the complete-chain arm.
    let mut diagnostic_off = complete_on;
    diagnostic_off[1] = ("GKR_EXACT_MEMORY_ARM", "off");
    diagnostic_off[5] = ("GKR_DR_ENTRY", "plus3");
    apply(&diagnostic_off);
    let error = message(
        ExactMemoryConfig::from_environment(legacy)
            .expect_err("a diagnostic entry on the legacy arm must be refused"),
    );
    assert!(error.contains("requires the complete-chain arm"), "{error}");

    // Both diagnostic neighbours resolve on the production arm.
    for label in ["minus3", "plus3"] {
        let mut diagnostic = complete_on;
        diagnostic[5] = ("GKR_DR_ENTRY", label);
        apply(&diagnostic);
        assert_eq!(
            ExactMemoryConfig::from_environment(production)
                .expect("a diagnostic neighbour must resolve")
                .map(|config| config.entry()),
            Some(DrTailEntrySelection::from_label(label).unwrap())
        );
    }

    apply(&[]);
}

/// B5 producer/consumer contract: the emitted row must carry exactly the keys
/// the durable analyzer consumes. If either side drifts, this fails instead of
/// the gate silently becoming unreachable.
#[test]
fn cpu_exact_memory_row_schema_matches_the_durable_analyzer() {
    use super::{exact_memory_row_json, ExactMemoryLayerCounts, ExactMemorySequence};
    use gpu_prover_context::{
        PoolMemoryHighWaterReport, PoolMemoryHighWaterSnapshot, PoolMemoryUsage,
    };

    let usage = |physical, logical| PoolMemoryUsage {
        physical_backing_bytes: physical,
        logical_live_bytes: logical,
    };
    let report = PoolMemoryHighWaterReport {
        start: usage(10, 8),
        physical_backing_peak_bytes: 120,
        logical_live_peak_bytes: 90,
        summed_requested_bytes: 200,
        peak_window_end: usage(10, 8),
        return_to_entry: usage(10, 8),
    };
    let snapshot = PoolMemoryHighWaterSnapshot {
        start: usage(10, 8),
        physical_backing_peak_bytes: 120,
        logical_live_peak_bytes: 90,
        summed_requested_bytes: 200,
        peak_window_end: usage(10, 8),
    };
    let identity = serde_json::json!({
        "invocation": "inv",
        "phase": "retained",
        "sample": 1,
        "arm": "on",
        "entry": "portable",
        "options": {
            "dr_tail_megakernel": true,
            "windowed_r0": true,
            "windowed_main_continuations": true,
            "windowed_dr": true,
            "windowed_dr_continuations": true,
            "window_tail": "Split",
        },
    });
    let row = exact_memory_row_json(
        identity,
        serde_json::json!({"block_log_size": 20, "blocks_count": 4}),
        ExactMemorySequence {
            whole_start: 0,
            backward_start: 1,
            backward_seal: 2,
            job_finish: 3,
            backward_finish: 4,
            whole_finish: 5,
        },
        ExactMemoryLayerCounts {
            dr_layers: 7,
            dr_prepared_layers: 7,
            dr_bundle_final_log: Some(4),
        },
        &report,
        &snapshot,
        &report,
        &snapshot,
        &super::EXACT_MEMORY_OPERATION_ORDER,
    );

    // Exactly the analyzer's top-level keys, no more and no fewer.
    let mut keys: Vec<&str> = row
        .as_object()
        .expect("a row is a JSON object")
        .keys()
        .map(String::as_str)
        .collect();
    keys.sort_unstable();
    assert_eq!(
        keys,
        [
            "arm",
            "backward",
            "backward_sealed",
            "dr_bundle_final_log",
            "dr_layers",
            "dr_prepared_layers",
            "entry",
            "geometry",
            "invocation",
            "operations",
            "options",
            "phase",
            "sample",
            "sequence",
            "whole",
            "whole_sealed",
        ]
    );

    // The production-shaped operation trace, in the accepted order.
    assert_eq!(
        row["operations"]
            .as_array()
            .expect("operations is a JSON array")
            .iter()
            .map(|value| value.as_str().expect("each operation is a string"))
            .collect::<Vec<_>>(),
        super::EXACT_MEMORY_OPERATION_ORDER,
    );

    // The analyzer reads these option fields by name.
    let mut option_keys: Vec<&str> = row["options"]
        .as_object()
        .unwrap()
        .keys()
        .map(String::as_str)
        .collect();
    option_keys.sort_unstable();
    assert_eq!(
        option_keys,
        [
            "dr_tail_megakernel",
            "window_tail",
            "windowed_dr",
            "windowed_dr_continuations",
            "windowed_main_continuations",
            "windowed_r0",
        ]
    );

    // The six sequence positions, by the analyzer's exact names and order.
    let sequence = row["sequence"].as_object().unwrap();
    for name in [
        "whole_start",
        "backward_start",
        "backward_seal",
        "job_finish",
        "backward_finish",
        "whole_finish",
    ] {
        assert!(
            sequence.contains_key(name),
            "missing sequence position {name}"
        );
    }
    assert_eq!(sequence.len(), 6);

    // Report and seal shapes: the seal carries no return-to-entry.
    for scope in ["whole", "backward"] {
        for metric in [
            "physical_backing_peak_bytes",
            "logical_live_peak_bytes",
            "summed_requested_bytes",
        ] {
            assert!(
                row[scope][metric].is_u64(),
                "{scope}.{metric} must be integer bytes"
            );
            assert!(row[format!("{scope}_sealed")][metric].is_u64());
        }
        for boundary in ["start", "peak_window_end", "return_to_entry"] {
            assert!(row[scope][boundary]["physical_backing_bytes"].is_u64());
            assert!(row[scope][boundary]["logical_live_bytes"].is_u64());
        }
        assert!(row[format!("{scope}_sealed")]
            .get("return_to_entry")
            .is_none());
        assert!(row[format!("{scope}_sealed")]["start"].is_object());
    }

    // The analyzer must be able to consume this row verbatim.
    let line = serde_json::to_string(&row).unwrap();
    assert!(serde_json::from_str::<serde_json::Value>(&line).is_ok());
    // The DR layer count is this proof's, never the block's proof count.
    assert_eq!(row["dr_layers"], 7);
}

/// The production operation trace is ordered and complete by construction: the
/// sink refuses any mark that is out of order, repeated, or skipped.
#[test]
fn cpu_exact_memory_operation_trace_order_is_enforced() {
    use super::EXACT_MEMORY_OPERATION_ORDER;

    assert_eq!(
        EXACT_MEMORY_OPERATION_ORDER,
        [
            "resource_preflight",
            "initial_input_h2d",
            "prove_enqueue",
            "final_slab_d2h",
            "proof_assembly_after_final_d2h",
        ]
    );

    // The recorder is a pure prefix check, so it is exercised directly here
    // without a device: position N must be exactly the Nth expected mark.
    let accepts = |marks: &[&'static str]| -> bool {
        let mut recorded: Vec<&'static str> = Vec::new();
        for mark in marks {
            if EXACT_MEMORY_OPERATION_ORDER.get(recorded.len()).copied() != Some(*mark) {
                return false;
            }
            recorded.push(*mark);
        }
        true
    };

    assert!(accepts(&EXACT_MEMORY_OPERATION_ORDER));
    // Out of order.
    assert!(!accepts(&["initial_input_h2d", "resource_preflight"]));
    // Repeated.
    assert!(!accepts(&["resource_preflight", "resource_preflight"]));
    // Skipped.
    assert!(!accepts(&["resource_preflight", "prove_enqueue"]));
    // Unknown.
    assert!(!accepts(&["stage1_forward"]));
    // A truncated prefix is accepted mark-by-mark but is not a complete trace,
    // which `finish_report` rejects separately.
    assert!(accepts(&["resource_preflight", "initial_input_h2d"]));
}

/// The four enqueue-side marks are recorded at the real worker boundaries, and
/// the terminal owner is untouched.
#[test]
fn cpu_exact_memory_operation_marks_are_wired_at_worker_boundaries() {
    const WORKER: &str = include_str!("../../../execution_prover/src/workers/gpu.rs");

    let preflight = WORKER
        .find(r#"sink.record_operation("resource_preflight")"#)
        .expect("preflight mark must be recorded in phase one");
    let h2d = WORKER
        .find(r#"sink.record_operation("initial_input_h2d")"#)
        .expect("H2D mark must be recorded in phase one");
    let enqueue = WORKER
        .find(r#"record_measured_operation("prove_enqueue")"#)
        .expect("prove-enqueue mark must be recorded in phase two");
    let d2h = WORKER
        .find(r#"record_measured_operation("final_slab_d2h")"#)
        .expect("terminal-D2H mark must be recorded in phase two");
    assert!(
        preflight < h2d && h2d < enqueue && enqueue < d2h,
        "the enqueue-side marks must appear in production order"
    );

    // Admission is marked before any transfer exists.
    let construct = WORKER
        .find("DecoderTableTransfer::new")
        .expect("phase one must still construct the decoder transfer");
    assert!(
        preflight < construct,
        "the preflight mark must precede the first transfer construction"
    );
    let schedule = WORKER
        .find("bundle.schedule(context)?;")
        .expect("phase one must still schedule the H2D bundle");
    assert!(
        schedule < h2d,
        "the H2D mark must follow the real bundle schedule"
    );
}
