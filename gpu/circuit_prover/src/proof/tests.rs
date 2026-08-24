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
