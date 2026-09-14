use super::*;

// ---------------------------------------------------------------------------
// Generic test bodies
// ---------------------------------------------------------------------------

/// Full GPU proof == CPU reference (single proof).
pub(super) fn run_proof_parity(fixture: &BasicUnrolledProofFixture) {
    #[cfg(feature = "r0_diagnostics")]
    if let Ok(table) = std::env::var("AB_R0_BANK_TABLE") {
        gpu_gkr::backward::window::diagnostics::set_dispatch_override(Some(&table));
    }
    #[cfg(feature = "r0_diagnostics")]
    gpu_gkr::backward::window::diagnostics::begin_from_env(&fixture.base.context).unwrap();
    #[cfg(feature = "continuation_diagnostics")]
    gpu_gkr::backward::main_continuation::fusion_diagnostics::begin_from_env(&fixture.base.context)
        .unwrap();
    #[cfg(feature = "continuation_diagnostics")]
    gpu_gkr::backward::main_continuation::partition_diagnostics::begin_from_env(
        &fixture.base.context,
    )
    .unwrap();
    #[cfg(feature = "continuation_diagnostics")]
    if std::env::var_os("AB_CONT_FUSION_POLICY").is_some() {
        gpu_gkr::backward::main_continuation::fusion_diagnostics::start_policy(true);
    }
    #[cfg(feature = "continuation_diagnostics")]
    if std::env::var_os("AB_CONT_PARTITION_PRODUCTION").is_some() {
        gpu_gkr::backward::main_continuation::partition_diagnostics::set_production_override(true);
    }
    let proof_job = fixture.schedule_prove().unwrap();
    let (gpu_proof, _ms) = proof_job.finish().unwrap();
    #[cfg(feature = "r0_diagnostics")]
    gpu_gkr::backward::window::diagnostics::finish(&fixture.base.context).unwrap();
    #[cfg(feature = "r0_diagnostics")]
    gpu_gkr::backward::window::diagnostics::finish_dispatch_override();
    #[cfg(feature = "continuation_diagnostics")]
    gpu_gkr::backward::main_continuation::fusion_diagnostics::finish(&fixture.base.context)
        .unwrap();
    #[cfg(feature = "continuation_diagnostics")]
    if std::env::var_os("AB_CONT_FUSION_POLICY").is_some() {
        let coverage = gpu_gkr::backward::main_continuation::fusion_diagnostics::finish_policy();
        eprintln!("CONT_POLICY_CPU coverage={coverage:?}");
    }
    #[cfg(feature = "continuation_diagnostics")]
    gpu_gkr::backward::main_continuation::partition_diagnostics::finish(&fixture.base.context)
        .unwrap();
    #[cfg(feature = "continuation_diagnostics")]
    if std::env::var_os("AB_CONT_PARTITION_PRODUCTION").is_some() {
        gpu_gkr::backward::main_continuation::partition_diagnostics::finish_production_override();
    }
    assert_gkr_proof_eq_for_test(&gpu_proof, &fixture.expected_cpu_proof);
}

/// Two concurrently-scheduled proofs on a recycled-block arena (the
/// uninitialized-witness regression guard). schedule -> schedule -> finish -> finish.
pub(super) fn run_multi_schedule(fixture: &BasicUnrolledProofFixture) {
    let baseline = fixture.base.context.get_used_mem_current();
    let job0 = fixture.schedule_prove().unwrap();
    let job1 = fixture.schedule_prove().unwrap();
    let (p0, ms0) = job0.finish().unwrap();
    eprintln!("proof_job_0 proof time: {ms0} ms");
    assert_gkr_proof_eq_for_test(&p0, &fixture.expected_cpu_proof);
    drop(p0);
    let (p1, ms1) = job1.finish().unwrap();
    eprintln!("proof_job_1 proof time: {ms1} ms");
    assert_gkr_proof_eq_for_test(&p1, &fixture.expected_cpu_proof);
    drop(p1);
    assert_eq!(
        fixture.base.context.get_used_mem_current(),
        baseline,
        "device memory must return to baseline after both proofs complete"
    );
}

/// Warmup + profiled prove; structure check only (no CPU reference needed).
pub(super) fn run_profile(fixture: &BasicUnrolledFixture) {
    #[cfg(feature = "continuation_diagnostics")]
    if std::env::var_os("AB_CONT_PARTITION_PROOF_OUTPUT").is_some() {
        run_partition_policy_profile(fixture);
        return;
    }
    #[cfg(feature = "continuation_diagnostics")]
    if std::env::var_os("AB_CONT_FUSION_POLICY").is_some() {
        run_continuation_policy_profile(fixture);
        return;
    }
    #[cfg(feature = "r0_diagnostics")]
    if let Ok(table) = std::env::var("AB_R0_BANK_TABLE") {
        run_bank_profile(fixture, &table);
        return;
    }
    let baseline = fixture.context.get_used_mem_current();
    let warm = fixture.schedule_transfers().unwrap();
    fixture.context.get_h2d_stream().synchronize().unwrap();
    let warm_job = fixture.prove(warm).unwrap();
    let (warm_proof, warm_ms) = warm_job.finish().unwrap();
    eprintln!("warmup proof time: {warm_ms} ms");
    assert_gkr_proof_structure_for_test(&warm_proof, &fixture.prover_config.whir_schedule);
    #[cfg(not(any(feature = "r0_diagnostics", feature = "continuation_diagnostics")))]
    drop(warm_proof);
    #[cfg(feature = "r0_diagnostics")]
    gpu_gkr::backward::window::diagnostics::begin_from_env(&fixture.context).unwrap();
    #[cfg(feature = "continuation_diagnostics")]
    gpu_gkr::backward::main_continuation::fusion_diagnostics::begin_from_env(&fixture.context)
        .unwrap();
    #[cfg(feature = "continuation_diagnostics")]
    gpu_gkr::backward::main_continuation::partition_diagnostics::begin_from_env(&fixture.context)
        .unwrap();
    let prof = fixture.schedule_transfers().unwrap();
    fixture.context.get_h2d_stream().synchronize().unwrap();
    fixture.context.reset_used_mem_peak();
    let (prof_proof, prof_ms) = {
        let _range = scoped_range(
            Some("gpu_circuit_prover.tests"),
            "test.gpu.prove.profiled_call",
        );
        fixture.prove(prof).unwrap().finish().unwrap()
    };
    eprintln!("profiled proof time: {prof_ms} ms");
    #[cfg(feature = "r0_diagnostics")]
    {
        gpu_gkr::backward::window::diagnostics::finish(&fixture.context).unwrap();
        assert_gkr_proof_eq_for_test(&prof_proof, &warm_proof);
    }
    #[cfg(feature = "continuation_diagnostics")]
    {
        gpu_gkr::backward::main_continuation::fusion_diagnostics::finish(&fixture.context).unwrap();
        gpu_gkr::backward::main_continuation::partition_diagnostics::finish(&fixture.context)
            .unwrap();
        assert_gkr_proof_eq_for_test(&prof_proof, &warm_proof);
    }
    assert_gkr_proof_structure_for_test(&prof_proof, &fixture.prover_config.whir_schedule);
    drop(prof_proof);
    let peak = fixture.context.get_used_mem_peak();
    eprintln!(
        "peak device memory: {:.3} GiB",
        peak as f64 / (1u64 << 30) as f64
    );
    assert!(peak > baseline);
    assert_eq!(fixture.context.get_used_mem_current(), baseline);
}

/// Paired full proofs with actual candidate dispatch and no resident-input
/// probes. The table is selected outside the timed proof scheduling region.
#[cfg(feature = "r0_diagnostics")]
fn run_bank_profile(fixture: &BasicUnrolledFixture, table: &str) {
    use gpu_gkr::backward::window::diagnostics::{finish_dispatch_override, set_dispatch_override};
    use std::io::Write;
    let baseline = fixture.context.get_used_mem_current();
    let run = |candidate: bool| {
        set_dispatch_override(candidate.then_some(table));
        let transfers = fixture.schedule_transfers().unwrap();
        fixture.context.get_h2d_stream().synchronize().unwrap();
        let before_prove = fixture.context.get_used_mem_current();
        let (proof, ms) = {
            let _range = scoped_range(
                Some("gpu_circuit_prover.tests"),
                if candidate {
                    "test.gpu.r0_bank.candidate"
                } else {
                    "test.gpu.r0_bank.baseline"
                },
            );
            let job = fixture.prove(transfers).unwrap();
            assert_eq!(fixture.context.get_used_mem_current(), before_prove);
            // Keep the NVTX range open through completion so a range-triggered
            // nsys capture includes the queued kernels, not only their enqueue.
            job.finish().unwrap()
        };
        let launches = finish_dispatch_override();
        if candidate {
            assert!(launches > 0);
        }
        assert_gkr_proof_structure_for_test(&proof, &fixture.prover_config.whir_schedule);
        assert_eq!(fixture.context.get_used_mem_current(), baseline);
        (proof, ms, launches)
    };
    let (reference, _, _) = run(false);
    for _ in 0..2 {
        for candidate in [true, false] {
            let (proof, _, _) = run(candidate);
            assert_gkr_proof_eq_for_test(&proof, &reference);
        }
    }
    let pairs: usize = std::env::var("AB_R0_BANK_PAIRS")
        .unwrap_or_else(|_| "20".into())
        .parse()
        .unwrap();
    assert!((1..=100).contains(&pairs));
    let session: usize = std::env::var("AB_R0_BANK_SESSION")
        .unwrap_or_else(|_| "0".into())
        .parse()
        .unwrap();
    let output = std::env::var("AB_R0_BANK_OUTPUT").expect("absolute AB_R0_BANK_OUTPUT");
    let mut file = std::fs::File::create(output).unwrap();
    writeln!(file, "session,iteration,position,arm,ms,candidate_launches").unwrap();
    for iteration in 0..pairs {
        let order = if (iteration + session) % 2 == 0 {
            [false, true]
        } else {
            [true, false]
        };
        for (position, candidate) in order.into_iter().enumerate() {
            let (proof, ms, launches) = run(candidate);
            assert_gkr_proof_eq_for_test(&proof, &reference);
            writeln!(
                file,
                "{session},{iteration},{position},{},{ms:.9},{launches}",
                if candidate { "candidate" } else { "baseline" }
            )
            .unwrap();
        }
    }
    eprintln!("R0_BANK_PROOF pairs={pairs} all_proofs_equal=true");
}

#[cfg(feature = "continuation_diagnostics")]
fn run_continuation_policy_profile(fixture: &BasicUnrolledFixture) {
    use gpu_gkr::backward::main_continuation::fusion_diagnostics::{finish_policy, start_policy};
    use std::io::Write;
    let baseline = fixture.context.get_used_mem_current();
    let packed_comparison = std::env::var_os("AB_CONT_PACKED_POLICY").is_some();
    let split_comparison = std::env::var_os("AB_CONT_SPLIT_PACKED").is_some();
    let gated_comparison = std::env::var_os("AB_CONT_PACING_GATED").is_some();
    let canonical_comparison = std::env::var_os("AB_CONT_CANONICAL_FUSION").is_some();
    let fold_comparison = std::env::var_os("AB_CONT_FOLD_LANE8_POLICY").is_some();
    let wide_mode = std::env::var("AB_CONT_FOLD_WIDE_POLICY").ok();
    if let Some(mode) = &wide_mode {
        assert!(matches!(
            mode.as_str(),
            "fused" | "split" | "both" | "fused_original"
        ));
    }
    let wide_comparison = wide_mode.is_some();
    let evaluator_mode = std::env::var("AB_CONT_EVALUATOR_POLICY").ok();
    if let Some(mode) = &evaluator_mode {
        assert!(matches!(
            mode.as_str(),
            "compact" | "split_compact" | "x1" | "current"
        ));
    }
    let evaluator_comparison = evaluator_mode.is_some();
    assert!(
        [
            packed_comparison,
            split_comparison,
            gated_comparison,
            canonical_comparison,
            fold_comparison,
            wide_comparison,
            evaluator_comparison,
        ]
        .into_iter()
        .filter(|v| *v)
        .count()
            <= 1
    );
    let identical = std::env::var_os("AB_CONT_POLICY_IDENTICAL").is_some();
    let run = |candidate: bool| {
        let selected = candidate && !identical;
        start_policy(selected);
        let transfers = fixture.schedule_transfers().unwrap();
        fixture.context.get_h2d_stream().synchronize().unwrap();
        let before_prove = fixture.context.get_used_mem_current();
        let (proof, ms) = {
            let _range = scoped_range(
                Some("gpu_circuit_prover.tests"),
                if candidate {
                    "test.gpu.main_cont_policy.candidate"
                } else {
                    "test.gpu.main_cont_policy.baseline"
                },
            );
            let job = fixture.prove(transfers).unwrap();
            assert_eq!(fixture.context.get_used_mem_current(), before_prove);
            // Keep the NVTX range open through completion so a range-triggered
            // nsys capture includes the queued kernels, not only their enqueue.
            job.finish().unwrap()
        };
        let coverage = finish_policy();
        let launches = coverage.iter().filter(|pass| pass.fused).count();
        let packed_launches = coverage.iter().filter(|pass| pass.packed).count();
        let split_packed_launches = coverage.iter().filter(|pass| pass.split_packed).count();
        let gated_launches = coverage.iter().filter(|pass| pass.gated).count();
        let paced_launches = coverage.iter().filter(|pass| pass.paced).count();
        for pass in &coverage {
            if canonical_comparison {
                let sm_count = fixture.context.get_device_properties().sm_count;
                assert_eq!(
                    pass.min_tiles,
                    if selected && pass.canonical_input {
                        sm_count
                    } else {
                        4 * sm_count
                    }
                );
            }
            assert_eq!(
                pass.fused,
                (selected
                    || packed_comparison
                    || split_comparison
                    || gated_comparison
                    || canonical_comparison
                    || fold_comparison
                    || wide_comparison
                    || evaluator_comparison)
                    && pass.tiles >= pass.min_tiles
            );
            assert_eq!(
                pass.packed,
                (selected
                    || split_comparison
                    || gated_comparison
                    || canonical_comparison
                    || fold_comparison
                    || wide_comparison
                    || evaluator_comparison)
                    && pass.tiles >= pass.min_tiles
            );
            assert_eq!(
                pass.split_packed,
                !pass.fused
                    && (selected
                        || packed_comparison
                        || gated_comparison
                        || canonical_comparison
                        || fold_comparison
                        || wide_comparison
                        || evaluator_comparison)
            );
            let current_candidate = evaluator_mode.as_deref() == Some("current") && selected;
            let word_cutoff = if current_candidate {
                std::env::var("AB_CONT_CURRENT_WORDS")
                    .map(|v| v.parse::<usize>().unwrap())
                    .unwrap_or(1024)
            } else {
                1024
            };
            let fused_upper = if current_candidate {
                std::env::var("AB_CONT_CURRENT_FUSED_UPPER")
                    .map(|v| v.parse::<usize>().unwrap())
                    .unwrap_or(5500)
            } else {
                5500
            };
            assert_eq!(
                pass.static_x0,
                pass.words >= word_cutoff && (!pass.fused || pass.words < fused_upper)
            );
            assert_eq!(
                pass.gated,
                (wide_comparison
                    || evaluator_comparison
                    || fold_comparison
                    || canonical_comparison
                    || (gated_comparison && selected))
                    && pass.fused
                    && !pass.static_x0
            );
            assert_eq!(pass.paced, pass.gated && pass.words >= 1024);
            assert_eq!(
                pass.fold_candidate,
                fold_comparison && selected && !pass.fused
            );
            if evaluator_mode.is_some() {
                assert_eq!(
                    pass.min_tiles,
                    if current_candidate
                        && std::env::var_os("AB_CONT_LARGE_CANONICAL_FUSION").is_some()
                        && pass.round > 3
                        && pass.words >= 5500
                    {
                        fixture.context.get_device_properties().sm_count
                    } else {
                        2 * fixture.context.get_device_properties().sm_count
                            * if current_candidate {
                                std::env::var("AB_CONT_CURRENT_WAVES")
                                    .map(|v| v.parse::<usize>().unwrap())
                                    .unwrap_or(2)
                            } else {
                                2
                            }
                    }
                );
                let expected_arm = if evaluator_mode.as_deref() == Some("current") {
                    match (pass.fused, pass.static_x0) {
                        (true, false) => 19,
                        (true, true) => 20,
                        (false, false) => 21,
                        (false, true) => 22,
                    }
                } else if evaluator_mode.as_deref() == Some("x1") {
                    if pass.fused {
                        if selected {
                            17
                        } else {
                            12
                        }
                    } else if pass.static_x0 {
                        if selected {
                            18
                        } else {
                            16
                        }
                    } else {
                        5
                    }
                } else if evaluator_mode.as_deref() == Some("split_compact") {
                    if pass.fused {
                        12
                    } else if pass.static_x0 && selected {
                        16
                    } else {
                        5
                    }
                } else if pass.fused {
                    if pass.static_x0 && !selected {
                        15
                    } else {
                        12
                    }
                } else if pass.static_x0 {
                    16
                } else {
                    5
                };
                assert_eq!(pass.fold_arm, expected_arm);
            }
            if let Some(mode) = &wide_mode {
                let wide = selected
                    && (mode == "both"
                        || (pass.fused && (mode == "fused" || mode == "fused_original"))
                        || (!pass.fused && mode == "split"));
                assert_eq!(
                    pass.fold_arm,
                    match (pass.fused, wide) {
                        (true, true) => 12,
                        (true, false) => 9,
                        (false, true) => 13,
                        (false, false) =>
                            if mode == "fused_original" {
                                5
                            } else {
                                11
                            },
                    }
                );
            }
        }
        eprintln!("CONT_POLICY_COVERAGE selected={selected} {coverage:?}");
        assert_gkr_proof_structure_for_test(&proof, &fixture.prover_config.whir_schedule);
        assert_eq!(fixture.context.get_used_mem_current(), baseline);
        (
            proof,
            ms,
            launches,
            packed_launches,
            split_packed_launches,
            gated_launches,
            paced_launches,
        )
    };
    let (reference, _, _, _, _, _, _) = run(false);
    for _ in 0..2 {
        for candidate in [true, false] {
            let (proof, _, _, _, _, _, _) = run(candidate);
            assert_gkr_proof_eq_for_test(&proof, &reference);
        }
    }
    let pairs: usize = std::env::var("AB_CONT_POLICY_PAIRS")
        .unwrap_or_else(|_| "10".into())
        .parse()
        .unwrap();
    assert!((1..=100).contains(&pairs));
    let session: usize = std::env::var("AB_CONT_POLICY_SESSION")
        .unwrap_or_else(|_| "0".into())
        .parse()
        .unwrap();
    let output = std::env::var("AB_CONT_POLICY_OUTPUT").expect("absolute AB_CONT_POLICY_OUTPUT");
    let mut file = std::fs::File::create(output).unwrap();
    writeln!(
        file,
        "session,iteration,position,arm,ms,candidate_launches,packed_launches,split_packed_launches,gated_launches,paced_launches"
    )
    .unwrap();
    for iteration in 0..pairs {
        let order = if (iteration + session) % 2 == 0 {
            [false, true]
        } else {
            [true, false]
        };
        for (position, candidate) in order.into_iter().enumerate() {
            let (
                proof,
                ms,
                launches,
                packed_launches,
                split_packed_launches,
                gated_launches,
                paced_launches,
            ) = run(candidate);
            assert_gkr_proof_eq_for_test(&proof, &reference);
            writeln!(
                file,
                "{session},{iteration},{position},{},{ms:.9},{launches},{packed_launches},{split_packed_launches},{gated_launches},{paced_launches}",
                if candidate { "candidate" } else { "baseline" }
            )
            .unwrap();
        }
    }
    eprintln!("CONT_POLICY_PROOF pairs={pairs} packed_comparison={packed_comparison} split_comparison={split_comparison} gated_comparison={gated_comparison} canonical_comparison={canonical_comparison} fold_comparison={fold_comparison} wide_mode={wide_mode:?} evaluator_mode={evaluator_mode:?} all_proofs_equal=true");
}

fn assert_device_slices_equal_chunked<T>(
    label: &str,
    lhs: &era_cudart::slice::DeviceSlice<T>,
    rhs: &era_cudart::slice::DeviceSlice<T>,
    context: &ProverContext,
) where
    T: Copy + Default + PartialEq + std::fmt::Debug,
{
    assert_eq!(lhs.len(), rhs.len(), "{label} length mismatch");
    const CHUNK_BYTES: usize = 64 << 20;
    let chunk_len = (CHUNK_BYTES / std::mem::size_of::<T>()).max(1);
    let mut lhs_host = vec![T::default(); chunk_len.min(lhs.len())];
    let mut rhs_host = vec![T::default(); chunk_len.min(rhs.len())];
    for offset in (0..lhs.len()).step_by(chunk_len) {
        let len = chunk_len.min(lhs.len() - offset);
        memory_copy_async(
            &mut lhs_host[..len],
            &lhs[offset..offset + len],
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut rhs_host[..len],
            &rhs[offset..offset + len],
            context.get_exec_stream(),
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        if lhs_host[..len] != rhs_host[..len] {
            let local = lhs_host[..len]
                .iter()
                .zip(&rhs_host[..len])
                .position(|(lhs, rhs)| lhs != rhs)
                .unwrap();
            assert_eq!(
                lhs_host[local],
                rhs_host[local],
                "{label} mismatch at element {}",
                offset + local
            );
        }
    }
}

fn run_stage1_buffer_parity(fixture: &BasicUnrolledFixture) {
    use gpu_gkr::proof_layout::GpuGKRTraceGeometry;
    use gpu_gkr::stage1::{
        generate_with_witness_strategy, GpuGKRStage1Output, WitnessGenerationStrategy,
    };

    let transfers = fixture.schedule_transfers().unwrap();
    transfers
        .transfer
        .ensure_transferred(&fixture.context)
        .unwrap();
    let setup = transfers
        .setup
        .as_ref()
        .expect("stage-1 parity fixture requires a setup transfer");
    let geometry = GpuGKRTraceGeometry {
        log_domain_size: setup.trace_holder.log_domain_size,
        log_lde_factor: setup.trace_holder.log_lde_factor,
        log_rows_per_leaf: setup.trace_holder.log_rows_per_leaf,
        log_tree_cap_size: setup.trace_holder.log_tree_cap_size,
    };
    let generate = |strategy| -> GpuGKRStage1Output {
        generate_with_witness_strategy(
            fixture.circuit_type,
            &fixture.compiled_circuit,
            geometry,
            Some(setup.trace_holder.get_hypercube_evals()),
            transfers
                .decoder
                .as_ref()
                .map(|decoder| &decoder.data_device[..]),
            transfers
                .inits_and_teardowns
                .as_ref()
                .map(|transfer| &transfer.data_device),
            transfers
                .tracing_data
                .as_ref()
                .map(|transfer| &transfer.data_device),
            None,
            &fixture.context,
            strategy,
        )
        .unwrap()
    };

    let split = generate(WitnessGenerationStrategy::Split);
    fixture.context.get_exec_stream().synchronize().unwrap();
    let fused = generate(WitnessGenerationStrategy::Fused);
    fixture.context.get_exec_stream().synchronize().unwrap();
    assert_device_slices_equal_chunked(
        "memory hypercube",
        split.memory_trace_holder.get_hypercube_evals(),
        fused.memory_trace_holder.get_hypercube_evals(),
        &fixture.context,
    );
    assert_device_slices_equal_chunked(
        "witness hypercube",
        split.witness_trace_holder.get_hypercube_evals(),
        fused.witness_trace_holder.get_hypercube_evals(),
        &fixture.context,
    );
    match (
        split.scratch_space_for_test(),
        fused.scratch_space_for_test(),
    ) {
        (Some(split), Some(fused)) => {
            assert_device_slices_equal_chunked("scratch", split, fused, &fixture.context)
        }
        (None, None) => {}
        _ => panic!("scratch allocation presence differs"),
    }
    assert_device_slices_equal_chunked(
        "generic/decoder mappings",
        split.lookup_mappings.generic_family(),
        fused.lookup_mappings.generic_family(),
        &fixture.context,
    );
    assert_device_slices_equal_chunked(
        "range-16 mappings",
        split.lookup_mappings.range_check_16(),
        fused.lookup_mappings.range_check_16(),
        &fixture.context,
    );
    assert_device_slices_equal_chunked(
        "timestamp mappings",
        split.lookup_mappings.timestamp(),
        fused.lookup_mappings.timestamp(),
        &fixture.context,
    );
}

#[test]
#[ignore]
fn run_add_sub_stage1_buffer_parity_test() {
    run_stage1_buffer_parity(&prepare_basic_unrolled_profiling_fixture());
}

#[test]
#[ignore]
fn run_load_store_subword_stage1_buffer_parity_test() {
    run_stage1_buffer_parity(&prepare_load_store_subword_only_profiling_fixture());
}

#[test]
#[ignore]
fn run_unified_stage1_buffer_parity_test() {
    run_stage1_buffer_parity(&prepare_unified_profiling_fixture());
}

#[test]
#[ignore]
fn run_blake2_compression_delegation_stage1_buffer_parity_test() {
    run_stage1_buffer_parity(&prepare_blake2_with_compression_profiling_fixture());
}

/// Full-proof parity at Sec100, where the lookup-challenge and WHIR-batching
/// PoWs are non-zero — exercises the on-device grinding + nonce path.
#[test]
#[ignore]
fn run_add_sub_proof_parity_test_sec100() {
    run_proof_parity(&prepare_basic_unrolled_proof_fixture_sec100());
}

#[test]
#[ignore]
fn run_add_sub_multi_schedule_test() {
    run_multi_schedule(&prepare_basic_unrolled_proof_fixture());
}

#[test]
#[ignore]
fn run_add_sub_profile_test() {
    run_profile(&prepare_basic_unrolled_profiling_fixture());
}

// ---------------------------------------------------------------------------
// jump_branch_slt fixture wrappers + test functions
// ---------------------------------------------------------------------------

fn prepare_jump_branch_slt_proof_fixture() -> BasicUnrolledProofFixture {
    let (base, p) = prepare_unrolled_non_memory_proof_fixture::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        common_constants::PC_STEP as u32, // default_pc_value_in_padding
        UnrolledNonMemoryCircuitType::JumpBranchSlt,
        JUMP_BRANCH_SLT_LAYOUT_PATH,
        jump_branch_slt_mod::witness_eval_fn,
        cs::gkr_circuits::jump_branch_slt_family::jump_branch_slt_table_driver_fn::<BF>,
        true,
    );
    BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: p.unwrap(),
    }
}

fn prepare_jump_branch_slt_profiling_fixture() -> BasicUnrolledFixture {
    prepare_unrolled_non_memory_proof_fixture::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        common_constants::PC_STEP as u32, // default_pc_value_in_padding
        UnrolledNonMemoryCircuitType::JumpBranchSlt,
        JUMP_BRANCH_SLT_LAYOUT_PATH,
        jump_branch_slt_mod::witness_eval_fn,
        cs::gkr_circuits::jump_branch_slt_family::jump_branch_slt_table_driver_fn::<BF>,
        false,
    )
    .0
}

#[test]
#[ignore]
fn run_jump_branch_slt_proof_parity_test() {
    run_proof_parity(&prepare_jump_branch_slt_proof_fixture());
}

#[test]
#[ignore]
fn run_jump_branch_slt_multi_schedule_test() {
    run_multi_schedule(&prepare_jump_branch_slt_proof_fixture());
}

#[test]
#[ignore]
fn run_jump_branch_slt_profile_test() {
    run_profile(&prepare_jump_branch_slt_profiling_fixture());
}

// ---------------------------------------------------------------------------
// shift_binop fixture wrappers + test functions
// ---------------------------------------------------------------------------

fn prepare_shift_binop_proof_fixture() -> BasicUnrolledProofFixture {
    let (base, p) = prepare_unrolled_non_memory_proof_fixture::<SHIFT_BINARY_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        common_constants::PC_STEP as u32, // default_pc_value_in_padding
        UnrolledNonMemoryCircuitType::ShiftBinary,
        SHIFT_BINOP_LAYOUT_PATH,
        shift_binop_mod::witness_eval_fn,
        cs::gkr_circuits::binary_shifts_family::shift_binop_table_driver_fn::<BF>,
        true,
    );
    BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: p.unwrap(),
    }
}

fn prepare_shift_binop_profiling_fixture() -> BasicUnrolledFixture {
    prepare_unrolled_non_memory_proof_fixture::<SHIFT_BINARY_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        common_constants::PC_STEP as u32, // default_pc_value_in_padding
        UnrolledNonMemoryCircuitType::ShiftBinary,
        SHIFT_BINOP_LAYOUT_PATH,
        shift_binop_mod::witness_eval_fn,
        cs::gkr_circuits::binary_shifts_family::shift_binop_table_driver_fn::<BF>,
        false,
    )
    .0
}

#[test]
#[ignore]
fn run_shift_binop_proof_parity_test() {
    run_proof_parity(&prepare_shift_binop_proof_fixture());
}

#[test]
#[ignore]
fn run_shift_binop_multi_schedule_test() {
    run_multi_schedule(&prepare_shift_binop_proof_fixture());
}

#[test]
#[ignore]
fn run_shift_binop_profile_test() {
    run_profile(&prepare_shift_binop_profiling_fixture());
}

// ---------------------------------------------------------------------------
// mul_div fixture wrappers + test functions
// ---------------------------------------------------------------------------

fn prepare_mul_div_proof_fixture() -> BasicUnrolledProofFixture {
    let (base, p) = prepare_unrolled_non_memory_proof_fixture::<MUL_DIV_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        common_constants::PC_STEP as u32, // default_pc_value_in_padding
        UnrolledNonMemoryCircuitType::MulDivUnsigned,
        UNSIGNED_MUL_DIV_LAYOUT_PATH,
        unsigned_mul_div_mod::witness_eval_fn,
        cs::gkr_circuits::mul_div::mul_div_table_driver_fn::<BF, false>,
        true,
    );
    BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: p.unwrap(),
    }
}

fn prepare_mul_div_profiling_fixture() -> BasicUnrolledFixture {
    prepare_unrolled_non_memory_proof_fixture::<MUL_DIV_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        common_constants::PC_STEP as u32, // default_pc_value_in_padding
        UnrolledNonMemoryCircuitType::MulDivUnsigned,
        UNSIGNED_MUL_DIV_LAYOUT_PATH,
        unsigned_mul_div_mod::witness_eval_fn,
        cs::gkr_circuits::mul_div::mul_div_table_driver_fn::<BF, false>,
        false,
    )
    .0
}

#[test]
#[ignore]
fn run_mul_div_proof_parity_test() {
    run_proof_parity(&prepare_mul_div_proof_fixture());
}

#[test]
#[ignore]
fn run_mul_div_multi_schedule_test() {
    run_multi_schedule(&prepare_mul_div_proof_fixture());
}

#[test]
#[ignore]
fn run_mul_div_profile_test() {
    run_profile(&prepare_mul_div_profiling_fixture());
}

// ---------------------------------------------------------------------------
// load_store_word_only fixture wrappers + test functions
// ---------------------------------------------------------------------------

fn prepare_load_store_word_only_proof_fixture() -> BasicUnrolledProofFixture {
    let (base, p) = prepare_unrolled_memory_proof_fixture::<LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        UnrolledMemoryCircuitType::LoadStoreWordOnly,
        MEM_WORD_ONLY_LAYOUT_PATH,
        mem_word_only_mod::witness_eval_fn,
        |td, binary| {
            cs::gkr_circuits::mem_word_only::mem_word_only_table_driver_fn(td);
            for (t, tbl) in cs::gkr_circuits::mem_word_only::create_mem_word_only_special_tables::<
                _,
                { common_constants::ROM_SECOND_WORD_BITS },
            >(binary)
            {
                td.add_table_with_content(t, tbl);
            }
        },
        true,
    );
    BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: p.unwrap(),
    }
}

fn prepare_load_store_word_only_profiling_fixture() -> BasicUnrolledFixture {
    prepare_unrolled_memory_proof_fixture::<LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        UnrolledMemoryCircuitType::LoadStoreWordOnly,
        MEM_WORD_ONLY_LAYOUT_PATH,
        mem_word_only_mod::witness_eval_fn,
        |td, binary| {
            cs::gkr_circuits::mem_word_only::mem_word_only_table_driver_fn(td);
            for (t, tbl) in cs::gkr_circuits::mem_word_only::create_mem_word_only_special_tables::<
                _,
                { common_constants::ROM_SECOND_WORD_BITS },
            >(binary)
            {
                td.add_table_with_content(t, tbl);
            }
        },
        false,
    )
    .0
}

#[test]
#[ignore]
fn run_load_store_word_only_proof_parity_test() {
    run_proof_parity(&prepare_load_store_word_only_proof_fixture());
}

#[test]
#[ignore]
fn run_load_store_word_only_multi_schedule_test() {
    run_multi_schedule(&prepare_load_store_word_only_proof_fixture());
}

#[test]
#[ignore]
fn run_load_store_word_only_profile_test() {
    run_profile(&prepare_load_store_word_only_profiling_fixture());
}

// ---------------------------------------------------------------------------
// load_store_subword_only fixture wrappers + test functions
// ---------------------------------------------------------------------------

fn prepare_load_store_subword_only_proof_fixture() -> BasicUnrolledProofFixture {
    let (base, p) =
        prepare_unrolled_memory_proof_fixture::<LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX>(
            &[15, 1],
            UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
            MEM_SUBWORD_ONLY_LAYOUT_PATH,
            mem_subword_only_mod::witness_eval_fn,
            |td, binary| {
                cs::gkr_circuits::mem_subword_only::mem_subword_only_table_driver_fn(td);
                for (t, tbl) in
                    cs::gkr_circuits::mem_subword_only::create_mem_subword_only_special_tables::<
                        _,
                        { common_constants::ROM_SECOND_WORD_BITS },
                    >(binary)
                {
                    td.add_table_with_content(t, tbl);
                }
            },
            true,
        );
    BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: p.unwrap(),
    }
}

fn prepare_load_store_subword_only_profiling_fixture() -> BasicUnrolledFixture {
    prepare_unrolled_memory_proof_fixture::<LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
        MEM_SUBWORD_ONLY_LAYOUT_PATH,
        mem_subword_only_mod::witness_eval_fn,
        |td, binary| {
            cs::gkr_circuits::mem_subword_only::mem_subword_only_table_driver_fn(td);
            for (t, tbl) in
                cs::gkr_circuits::mem_subword_only::create_mem_subword_only_special_tables::<
                    _,
                    { common_constants::ROM_SECOND_WORD_BITS },
                >(binary)
            {
                td.add_table_with_content(t, tbl);
            }
        },
        false,
    )
    .0
}

#[test]
#[ignore]
fn run_load_store_subword_only_proof_parity_test() {
    run_proof_parity(&prepare_load_store_subword_only_proof_fixture());
}

#[test]
#[ignore]
fn run_load_store_subword_only_multi_schedule_test() {
    run_multi_schedule(&prepare_load_store_subword_only_proof_fixture());
}

#[test]
#[ignore]
fn run_load_store_subword_only_profile_test() {
    run_profile(&prepare_load_store_subword_only_profiling_fixture());
}

// ===========================================================================
// DELEGATION PROOF FIXTURES
//
// These drive a delegation circuit through the GPU `prove()` path. Each replays
// from its OWN correct workload: bigint from `examples/bigint_with_control`
// (issues one bigint call), keccak from keccak_f1600, and the two blake2 variants
// from the `examples/multi_family_smoke` apps (nd `[50, 0xDEAD_BEEF]`, matching the
// CPU unified orchestration test). All four build their fixture + CPU reference +
// tracing host, then prove on the GPU.
//
// All four tests are kept `#[ignore]`d (heavy GPU) — run with `--ignored`.
// ===========================================================================

const BIGINT_DELEGATION_LAYOUT_PATH: &str =
    "cs/compiled_circuits/bigint_with_extended_control_layout_gkr.json";
const BIGINT_WITH_CONTROL_BINARY_PATH: &str = "examples/bigint_with_control/app.bin";
const BIGINT_WITH_CONTROL_TEXT_PATH: &str = "examples/bigint_with_control/app.text";

const BLAKE2_WITH_COMPRESSION_LAYOUT_PATH: &str =
    "cs/compiled_circuits/blake2_with_extended_control_layout_gkr.json";
const BLAKE2_WITH_COMPRESSION_BINARY_PATH: &str =
    "examples/multi_family_smoke/app_blake2_with_compression.bin";
const BLAKE2_WITH_COMPRESSION_TEXT_PATH: &str =
    "examples/multi_family_smoke/app_blake2_with_compression.text";
const BLAKE2_WITH_COMPRESSION_ND: [u32; 2] = [50, 0xDEAD_BEEF];
const BLAKE2_NUM_DELEGATION_CYCLES: usize = 1 << 20;

const BLAKE2_G_FUNCTION_LAYOUT_PATH: &str =
    "cs/compiled_circuits/blake2_g_function_layout_gkr.json";
const BLAKE2_G_FUNCTION_BINARY_PATH: &str = "examples/multi_family_smoke/app_blake2_g_function.bin";
const BLAKE2_G_FUNCTION_TEXT_PATH: &str = "examples/multi_family_smoke/app_blake2_g_function.text";
const BLAKE2_G_FUNCTION_ND: [u32; 2] = [50, 0xDEAD_BEEF];
const BLAKE2_G_FUNCTION_NUM_DELEGATION_CYCLES: usize = 1 << 22;

/// Replays `examples/bigint_with_control` (a program that issues exactly one
/// bigint delegation call via the bigint CSR ABI; it takes no non-determinism
/// input, so the nd array below is unused padding), so `bigint_calls > 0` and
/// the fixture drives a REAL bigint delegation proof.
fn replay_bigint_delegation_buffer() -> (Vec<BigintDelegationWitness>, TableDriver<BF>) {
    let buffer = replay_delegation_trace_buffer_for_workload::<_, FullUnsignedMachineDecoderConfig>(
        BIGINT_WITH_CONTROL_BINARY_PATH,
        BIGINT_WITH_CONTROL_TEXT_PATH,
        &[15, 1],
        false,
        |counters| counters.bigint_calls,
        BigintDelegationWitness::empty(),
        |tape, cycles_bound, replay_state, replay_ram, buffer| {
            let mut buffers = [buffer];
            let mut tracer = BigintDelegationDestinationHolder {
                buffers: &mut buffers[..],
            };
            ReplayerVM::<DelegationsAndFamiliesCounters>::replay_basic_unrolled::<_, _, BF>(
                replay_state,
                replay_ram,
                tape,
                &mut (),
                cycles_bound,
                &mut tracer,
            );
        },
    );
    assert!(
        !buffer.is_empty(),
        "examples/bigint_with_control must exercise the bigint delegation \
         (bigint_calls == 0) — the workload assumption is wrong",
    );
    eprintln!("bigint delegation: bigint_calls = {}", buffer.len());

    let mut table_driver = TableDriver::<BF>::new();
    cs::gkr_circuits::delegation::bigint_with_control::bigint_with_extended_control_delegation_circuit_table_driver_fn(
        &mut table_driver,
    );
    (buffer, table_driver)
}

fn prepare_bigint_proof_fixture() -> BasicUnrolledProofFixture {
    let (buffer, table_driver) = replay_bigint_delegation_buffer();
    let oracle = BigintDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    // The oracle borrows `buffer`; `prepare_delegation_proof_fixture` consumes
    // the buffer only after building the CPU reference (which is what uses the
    // oracle), so clone the buffer for the tracing host.
    let buffer_for_host = buffer.clone();
    let fixture = prepare_delegation_proof_fixture(
        DelegationCircuitType::BigIntWithControl,
        BIGINT_DELEGATION_LAYOUT_PATH,
        &table_driver,
        buffer_for_host,
        &oracle,
        bigint_with_extended_control_mod::witness_eval_fn,
        CircuitType::Delegation(DelegationCircuitType::BigIntWithControl).get_domain_size(),
    );
    drop(buffer);
    fixture
}

fn prepare_bigint_profiling_fixture() -> BasicUnrolledFixture {
    let (buffer, table_driver) = replay_bigint_delegation_buffer();
    prepare_delegation_profiling_fixture(
        DelegationCircuitType::BigIntWithControl,
        BIGINT_DELEGATION_LAYOUT_PATH,
        &table_driver,
        buffer,
        CircuitType::Delegation(DelegationCircuitType::BigIntWithControl).get_domain_size(),
    )
}

/// bigint delegation proof_parity: GPU proof == CPU reference, byte-identical.
/// `#[ignore]`d as a heavy GPU test — run with `--ignored`.
#[test]
#[ignore]
fn run_bigint_proof_parity_test() {
    run_proof_parity(&prepare_bigint_proof_fixture());
}

#[test]
#[ignore]
fn run_bigint_multi_schedule_test() {
    run_multi_schedule(&prepare_bigint_proof_fixture());
}

#[test]
#[ignore]
fn run_bigint_profile_test() {
    run_profile(&prepare_bigint_profiling_fixture());
}

// ---------------------------------------------------------------------------
// keccak_special5 delegation fixture wrappers + test functions
//
// keccak_f1600 exercises the keccak delegation (`keccak_calls > 0`); the GPU
// delegation proof is verified byte-equal to the CPU reference — see the section
// banner above.
// ---------------------------------------------------------------------------

const KECCAK_SPECIAL5_DELEGATION_LAYOUT_PATH: &str =
    "cs/compiled_circuits/keccak_special5_layout_gkr.json";

/// Replay the keccak_special5 delegation witness buffer from the keccak_f1600
/// workload. Asserts `keccak_calls > 0` (an empty delegation produces no proof)
/// BEFORE the caller reaches the expensive GPU build.
fn replay_keccak_special5_delegation_buffer(
) -> (Vec<KeccakSpecial5DelegationWitness>, TableDriver<BF>) {
    let buffer = replay_delegation_trace_buffer(
        false,
        |counters| counters.keccak_calls,
        KeccakSpecial5DelegationWitness::empty(),
        |tape, cycles_bound, replay_state, replay_ram, buffer| {
            let mut buffers = [buffer];
            let mut tracer = KeccakDelegationDestinationHolder {
                buffers: &mut buffers[..],
            };
            ReplayerVM::<DelegationsAndFamiliesCounters>::replay_basic_unrolled::<_, _, BF>(
                replay_state,
                replay_ram,
                tape,
                &mut (),
                cycles_bound,
                &mut tracer,
            );
        },
    );
    assert!(
        !buffer.is_empty(),
        "keccak_f1600 workload must exercise the keccak delegation (keccak_calls > 0); \
         got an empty buffer — the workload assumption is wrong",
    );
    eprintln!("keccak delegation: keccak_calls = {}", buffer.len());

    let mut table_driver = TableDriver::<BF>::new();
    cs::gkr_circuits::delegation::keccak_special5::keccak_special5_delegation_circuit_table_driver_fn(
        &mut table_driver,
    );
    (buffer, table_driver)
}

fn prepare_keccak_special5_proof_fixture() -> BasicUnrolledProofFixture {
    let (buffer, table_driver) = replay_keccak_special5_delegation_buffer();
    let oracle = KeccakDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    let buffer_for_host = buffer.clone();
    let fixture = prepare_delegation_proof_fixture(
        DelegationCircuitType::KeccakSpecial5,
        KECCAK_SPECIAL5_DELEGATION_LAYOUT_PATH,
        &table_driver,
        buffer_for_host,
        &oracle,
        fixtures::keccak_special5_mod::witness_eval_fn,
        1 << 22,
    );
    drop(buffer);
    fixture
}

fn prepare_keccak_special5_profiling_fixture() -> BasicUnrolledFixture {
    let (buffer, table_driver) = replay_keccak_special5_delegation_buffer();
    prepare_delegation_profiling_fixture(
        DelegationCircuitType::KeccakSpecial5,
        KECCAK_SPECIAL5_DELEGATION_LAYOUT_PATH,
        &table_driver,
        buffer,
        1 << 22,
    )
}

/// keccak_special5 delegation proof_parity: GPU proof == CPU reference,
/// byte-identical. `#[ignore]`d as a heavy GPU test — run with `--ignored`.
#[test]
#[ignore]
fn run_keccak_special5_proof_parity_test() {
    run_proof_parity(&prepare_keccak_special5_proof_fixture());
}

#[test]
#[ignore]
fn run_keccak_special5_multi_schedule_test() {
    run_multi_schedule(&prepare_keccak_special5_proof_fixture());
}

#[test]
#[ignore]
fn run_keccak_special5_profile_test() {
    run_profile(&prepare_keccak_special5_profiling_fixture());
}

// ---------------------------------------------------------------------------
// blake2_with_compression delegation fixture wrappers + test functions
//
// Replays from `examples/multi_family_smoke/app_blake2_with_compression` with
// nd `[50, 0xDEAD_BEEF]` (the same program + inputs the CPU unified
// orchestration test's `multi_family_smoke_blake_compression` config uses),
// which exercises the blake2 round-function (compression) delegation
// (`blake_calls > 0`). GPU↔CPU proof parity is verified byte-identical — see the
// section banner above.
// ---------------------------------------------------------------------------

/// The oracle/witness types this delegation needs, imported directly (test-only
/// exemption from the upstream-only-import rule): `Blake2sGFunctionDelegationOracle`
/// is not re-exported by `crate::upstream` (only the round-function/bigint/keccak
/// oracles are), and `Blake2sGFunctionDelegationWitness` lives one level deeper
/// than the `mod.rs`-level `witness::` imports reach.
use prover::tracers::oracles::transpiler_oracles::delegation::Blake2sGFunctionDelegationOracle;
use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
use riscv_transpiler::witness::BlakeGFunctionDelegationDestinationHolder;

/// Replay the blake2_with_extended_control (compression) delegation witness
/// buffer from the `app_blake2_with_compression` workload. Asserts
/// `blake_calls > 0` BEFORE the caller reaches the expensive GPU build.
fn replay_blake2_with_compression_delegation_buffer(
) -> (Vec<Blake2sRoundFunctionDelegationWitness>, TableDriver<BF>) {
    // multi_family_smoke is a reduced-machine program; it uses the
    // special-opcode extension only the reduced decoder knows.
    let buffer = replay_delegation_trace_buffer_for_workload::<_, ReducedMachineDecoderConfig>(
        BLAKE2_WITH_COMPRESSION_BINARY_PATH,
        BLAKE2_WITH_COMPRESSION_TEXT_PATH,
        &BLAKE2_WITH_COMPRESSION_ND,
        false,
        |counters| counters.blake_calls,
        Blake2sRoundFunctionDelegationWitness::empty(),
        |tape, cycles_bound, replay_state, replay_ram, buffer| {
            let mut buffers = [buffer];
            let mut tracer = BlakeDelegationDestinationHolder {
                buffers: &mut buffers[..],
            };
            ReplayerVM::<DelegationsAndFamiliesCounters>::replay_basic_unrolled::<_, _, BF>(
                replay_state,
                replay_ram,
                tape,
                &mut (),
                cycles_bound,
                &mut tracer,
            );
        },
    );
    assert!(
        !buffer.is_empty(),
        "app_blake2_with_compression workload must exercise the blake2 round-function \
         (compression) delegation (blake_calls == 0); got an empty buffer — the workload \
         assumption is wrong",
    );
    eprintln!(
        "blake2_with_compression delegation: blake_calls = {}",
        buffer.len()
    );

    let mut table_driver = TableDriver::<BF>::new();
    cs::gkr_circuits::delegation::blake2_round_with_extended_control::blake2_with_extended_control_table_driver_fn(
        &mut table_driver,
    );
    (buffer, table_driver)
}

fn prepare_blake2_with_compression_proof_fixture() -> BasicUnrolledProofFixture {
    let (buffer, table_driver) = replay_blake2_with_compression_delegation_buffer();
    let oracle = Blake2sDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    let buffer_for_host = buffer.clone();
    let fixture = prepare_delegation_proof_fixture(
        DelegationCircuitType::Blake2WithCompression,
        BLAKE2_WITH_COMPRESSION_LAYOUT_PATH,
        &table_driver,
        buffer_for_host,
        &oracle,
        fixtures::blake2_with_extended_control_mod::witness_eval_fn,
        BLAKE2_NUM_DELEGATION_CYCLES,
    );
    drop(buffer);
    fixture
}

fn prepare_blake2_with_compression_profiling_fixture() -> BasicUnrolledFixture {
    let (buffer, table_driver) = replay_blake2_with_compression_delegation_buffer();
    prepare_delegation_profiling_fixture(
        DelegationCircuitType::Blake2WithCompression,
        BLAKE2_WITH_COMPRESSION_LAYOUT_PATH,
        &table_driver,
        buffer,
        BLAKE2_NUM_DELEGATION_CYCLES,
    )
}

/// blake2_with_compression (blake2_with_extended_control) delegation proof_parity:
/// GPU proof == CPU reference, byte-identical. `#[ignore]`d as a heavy GPU test —
/// run with `--ignored`.
#[test]
#[ignore]
fn run_blake2_with_compression_proof_parity_test() {
    run_proof_parity(&prepare_blake2_with_compression_proof_fixture());
}

#[test]
#[ignore]
fn run_blake2_with_compression_multi_schedule_test() {
    run_multi_schedule(&prepare_blake2_with_compression_proof_fixture());
}

#[test]
#[ignore]
fn run_blake2_with_compression_profile_test() {
    run_profile(&prepare_blake2_with_compression_profiling_fixture());
}

// ---------------------------------------------------------------------------
// blake2_g_function delegation fixture wrappers + test functions
//
// Replays from `examples/multi_family_smoke/app_blake2_g_function` with nd
// `[50, 0xDEAD_BEEF]` (the same program + inputs the CPU unified
// orchestration test's `multi_family_smoke_blake_g_function` config uses,
// and the default workload `prepare_unified_proof_fixture` already drives),
// which exercises the blake2 G-function delegation
// (`blake_g_function_calls > 0`). GPU proof == CPU reference, byte-identical
// (see the section banner). `#[ignore]`d as a heavy GPU test — run with `--ignored`.
// ---------------------------------------------------------------------------

/// Replay the blake2_g_function delegation witness buffer from the
/// `app_blake2_g_function` workload. Asserts `blake_g_function_calls > 0`
/// BEFORE the caller reaches the expensive GPU build.
fn replay_blake2_g_function_delegation_buffer(
) -> (Vec<Blake2sGFunctionDelegationWitness>, TableDriver<BF>) {
    let buffer = replay_delegation_trace_buffer_for_workload::<_, ReducedMachineDecoderConfig>(
        BLAKE2_G_FUNCTION_BINARY_PATH,
        BLAKE2_G_FUNCTION_TEXT_PATH,
        &BLAKE2_G_FUNCTION_ND,
        false,
        |counters| counters.blake_g_function_calls,
        Blake2sGFunctionDelegationWitness::empty(),
        |tape, cycles_bound, replay_state, replay_ram, buffer| {
            let mut buffers = [buffer];
            let mut tracer = BlakeGFunctionDelegationDestinationHolder {
                buffers: &mut buffers[..],
            };
            ReplayerVM::<DelegationsAndFamiliesCounters>::replay_basic_unrolled::<_, _, BF>(
                replay_state,
                replay_ram,
                tape,
                &mut (),
                cycles_bound,
                &mut tracer,
            );
        },
    );
    assert!(
        !buffer.is_empty(),
        "app_blake2_g_function workload must exercise the blake2 G-function delegation \
         (blake_g_function_calls == 0); got an empty buffer — the workload assumption is wrong",
    );
    eprintln!(
        "blake2_g_function delegation: blake_g_function_calls = {}",
        buffer.len()
    );

    let mut table_driver = TableDriver::<BF>::new();
    cs::gkr_circuits::delegation::blake2_g_function::blake2_g_function_table_driver_fn(
        &mut table_driver,
    );
    (buffer, table_driver)
}

fn prepare_blake2_g_function_proof_fixture() -> BasicUnrolledProofFixture {
    let (buffer, table_driver) = replay_blake2_g_function_delegation_buffer();
    let oracle = Blake2sGFunctionDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    let buffer_for_host = buffer.clone();
    let fixture = prepare_delegation_proof_fixture(
        DelegationCircuitType::Blake2GFunction,
        BLAKE2_G_FUNCTION_LAYOUT_PATH,
        &table_driver,
        buffer_for_host,
        &oracle,
        fixtures::blake2_g_function_mod::witness_eval_fn,
        BLAKE2_G_FUNCTION_NUM_DELEGATION_CYCLES,
    );
    drop(buffer);
    fixture
}

fn prepare_blake2_g_function_profiling_fixture() -> BasicUnrolledFixture {
    let (buffer, table_driver) = replay_blake2_g_function_delegation_buffer();
    prepare_delegation_profiling_fixture(
        DelegationCircuitType::Blake2GFunction,
        BLAKE2_G_FUNCTION_LAYOUT_PATH,
        &table_driver,
        buffer,
        BLAKE2_G_FUNCTION_NUM_DELEGATION_CYCLES,
    )
}

/// blake2_g_function delegation proof_parity. The GPU proof is
/// byte-identical to the CPU reference (blake_g_function_calls = 80). `#[ignore]`d
/// only because it is a heavy GPU test.
#[test]
#[ignore]
fn run_blake2_g_function_proof_parity_test() {
    run_proof_parity(&prepare_blake2_g_function_proof_fixture());
}

#[test]
#[ignore]
fn run_blake2_g_function_multi_schedule_test() {
    run_multi_schedule(&prepare_blake2_g_function_proof_fixture());
}

#[test]
#[ignore]
fn run_blake2_g_function_profile_test() {
    run_profile(&prepare_blake2_g_function_profiling_fixture());
}

// ---------------------------------------------------------------------------
// unified multi_schedule (with closure-to-ONE grand-product assertions)
// ---------------------------------------------------------------------------

#[test]
#[ignore]
fn run_unified_proof_parity_test() {
    run_proof_parity(&prepare_unified_proof_fixture());
}

/// Full e2e unified proof parity + closure-to-ONE.
///
/// Proves the unified_reduced_machine circuit on the GPU and asserts the proof is
/// field-wise bit-exact vs the CPU `prove_configured_with_gkr` reference
/// (`assert_gkr_proof_eq_for_test` covers `grand_product_accumulator_computed` AND
/// `whir_proof` incl. PoW/queries). Then drives the no-filter grand-product
/// accumulator closure using the GPU proof's accumulator and asserts it closes to
/// `E4::ONE` — mirroring the CPU orchestration (orchestration/unified.rs:259-278).
/// This exercises the full backward and WHIR path, including base-layer cached
/// relation extras in the transcript.
///
/// Concurrent shape (schedule -> schedule -> finish -> finish), NOT serial: both
/// unified (2^24) jobs are scheduled before either finishes, so the second proof's
/// device allocations land on blocks the first proof wrote and freed. The first
/// job retains host data and callback owners until `finish()`, while its device
/// reservations have already been released. This is the exact
/// condition that exposed a witness-trace uninitialized-read: the witness
/// generators write the per-opcode lookup columns only under `IF` guards, so rows
/// whose opcode doesn't match were left unwritten and read as fresh-page zeros on a
/// first proof but as stale data on the recycled second proof — diverging the
/// `Lookup16Bits`/`LookupTimestamps`/`GenericLookup` base-layer claims. The fix is
/// the codegen zero-default for conditionally-written witness columns
/// (`gpu_witness_eval_generator`); this test guards against its regression.
#[test]
#[ignore]
fn run_unified_multi_schedule_test() {
    let fixture = prepare_unified_proof_fixture();
    let baseline_device_usage = fixture.base.context.get_used_mem_current();

    // Schedule both jobs before finishing either: the second proof reuses the
    // first's freed (written) device blocks, exercising the cross-proof recycling
    // path that surfaced the uninitialized-witness read.
    let proof_job_0 = fixture.schedule_prove().unwrap();
    let proof_job_1 = fixture.schedule_prove().unwrap();

    let (gpu_proof_0, proof_time_ms_0) = proof_job_0.finish().unwrap();
    eprintln!("unified proof_job_0 proof time: {proof_time_ms_0} ms");
    assert_gkr_proof_eq_for_test(&gpu_proof_0, &fixture.expected_cpu_proof);

    // No-filter grand-product accumulator closure, driven by the GPU proof's
    // `grand_product_accumulator_computed` (proven == CPU above). Closing to ONE
    // confirms the GPU path produces a sound full-machine permutation argument.
    let mut acc = produce_initial_permutation_product_contribution::<BF, E4>(
        &fixture.base.unified_register_final_state,
        INITIAL_PC,
        split_timestamp(INITIAL_TIMESTAMP),
        fixture.base.unified_final_pc,
        split_timestamp(fixture.base.unified_final_timestamp),
        &fixture.base.external_challenges,
    );
    acc.mul_assign(&gpu_proof_0.grand_product_accumulator_computed);
    for factor in fixture.base.delegation_grand_product_factors.iter() {
        acc.mul_assign(factor);
    }
    assert_eq!(
        acc,
        E4::ONE,
        "unified grand-product accumulator must close to ONE"
    );
    drop(gpu_proof_0);

    // The concurrently-scheduled second proof must be bit-exact too (this is the
    // one that ran on recycled blocks) and device memory must return to baseline.
    let (gpu_proof_1, proof_time_ms_1) = proof_job_1.finish().unwrap();
    eprintln!("unified proof_job_1 proof time: {proof_time_ms_1} ms");
    assert_gkr_proof_eq_for_test(&gpu_proof_1, &fixture.expected_cpu_proof);
    drop(gpu_proof_1);

    assert_eq!(
        fixture.base.context.get_used_mem_current(),
        baseline_device_usage,
        "device memory must return to baseline after both proofs complete"
    );
}

/// Unified circuit profile run (warmup + profiled prove, structure check only).
/// Uses a no-CPU-reference fixture so it skips the expensive CPU unified prove.
#[test]
#[ignore]
fn run_unified_profile_test() {
    run_profile(&prepare_unified_profiling_fixture());
}

// ---------------------------------------------------------------------------
// inits_and_teardowns fixture wrappers + test functions
//
// The standalone i/t circuit is memory-only (zero-width setup, no per-cycle
// witness); its `BasicUnrolledFixture` is built in the `inits_and_teardowns`
// module (setup = None, empty tracing host, i/t trace host = Some). It is
// still driven through the same three matrix bodies as every other circuit.
// ---------------------------------------------------------------------------

fn prepare_inits_and_teardowns_matrix_proof_fixture() -> BasicUnrolledProofFixture {
    let (base, p) = super::inits_and_teardowns::prepare_inits_and_teardowns_proof_fixture(true);
    BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: p.unwrap(),
    }
}

fn prepare_inits_and_teardowns_matrix_profiling_fixture() -> BasicUnrolledFixture {
    super::inits_and_teardowns::prepare_inits_and_teardowns_proof_fixture(false).0
}

// Regression guards for zero-width base-layer handling (width-0 witness):
// initial transcript cap gating and WHIR base-cap gating.
#[test]
#[ignore]
fn run_inits_and_teardowns_proof_parity_test() {
    run_proof_parity(&prepare_inits_and_teardowns_matrix_proof_fixture());
}

#[test]
#[ignore]
fn run_inits_and_teardowns_multi_schedule_test() {
    run_multi_schedule(&prepare_inits_and_teardowns_matrix_proof_fixture());
}

// run_profile checks proof structure + peak memory only (no CPU comparison),
// unlike the other two.
#[test]
#[ignore]
fn run_inits_and_teardowns_profile_test() {
    run_profile(&prepare_inits_and_teardowns_matrix_profiling_fixture());
}

/// Feature-only paired proof events. Partition planning happens before prove;
/// there are no publication snapshots, poison checks, or resident timing loops.
#[cfg(feature = "continuation_diagnostics")]
fn run_partition_policy_profile(fixture: &BasicUnrolledFixture) {
    use gpu_gkr::backward::main_continuation::partition_diagnostics::{
        begin_from_env, finish, finish_production_override, set_production_override,
    };
    use std::io::Write;
    assert!(std::env::var_os("AB_CONT_PARTITION_PROOF_ONLY").is_some());
    assert!(std::env::var_os("AB_CONT_PARTITION_OUTPUT").is_none());
    let session: usize = std::env::var("AB_CONT_PARTITION_SESSION")
        .unwrap_or("0".into())
        .parse()
        .unwrap();
    let identical = std::env::var_os("AB_CONT_PARTITION_IDENTICAL").is_some();
    let production = std::env::var_os("AB_CONT_PARTITION_PRODUCTION").is_some();
    if production {
        assert!(std::env::var_os("AB_CONT_PARTITION_MANIFEST").is_none());
    }
    let execute = |candidate: bool| {
        set_production_override(production && candidate && !identical);
        if !production && candidate && !identical {
            begin_from_env(&fixture.context).unwrap();
        }
        let transfer = fixture.schedule_transfers().unwrap();
        fixture.context.get_h2d_stream().synchronize().unwrap();
        let result = fixture.prove(transfer).unwrap().finish().unwrap();
        if !production && candidate && !identical {
            finish(&fixture.context).unwrap();
        }
        // In legacy diagnostic mode its explicit kernels bypass production
        // dispatch. Its baseline still uses an explicit disabled production arm.
        finish_production_override();
        result
    };
    let (reference, _) = execute(false);
    for _ in 0..3 {
        for arm in [false, true] {
            let (proof, _) = execute(arm);
            assert_gkr_proof_eq_for_test(&proof, &reference);
        }
    }
    let mut file =
        std::fs::File::create(std::env::var("AB_CONT_PARTITION_PROOF_OUTPUT").unwrap()).unwrap();
    writeln!(file, "session,iteration,position,arm,ms").unwrap();
    for iteration in 0..10 {
        let order = if (session + iteration) % 2 == 0 {
            [false, true]
        } else {
            [true, false]
        };
        for (position, candidate) in order.into_iter().enumerate() {
            let (proof, ms) = execute(candidate);
            assert_gkr_proof_eq_for_test(&proof, &reference);
            writeln!(
                file,
                "{session},{iteration},{position},{},{ms:.9}",
                if candidate { "candidate" } else { "baseline" }
            )
            .unwrap();
        }
    }
    eprintln!("PARTITION_PROOF_GATE pairs=10 identical={identical} all_proofs_equal=true");
}
