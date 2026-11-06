use super::*;

// ---------------------------------------------------------------------------
// Generic test bodies
// ---------------------------------------------------------------------------

/// Full GPU proof == committed proof (single proof).
pub(super) fn run_proof_parity(fixture: &BasicUnrolledProofFixture) {
    let proof_job = fixture.schedule_prove().unwrap();
    let (gpu_proof, _ms) = proof_job.finish().unwrap();
    fixture.assert_proof(&gpu_proof);
}

/// Two concurrently-scheduled proofs on a recycled-block arena (the
/// uninitialized-witness regression guard). schedule -> schedule -> finish -> finish.
pub(super) fn run_multi_schedule(fixture: &BasicUnrolledProofFixture) {
    let baseline = fixture.base.context.get_used_mem_current();

    fixture.base.context.reset_used_mem_peak();
    let job0 = fixture.schedule_prove().unwrap();
    let job1 = fixture.schedule_prove().unwrap();
    let (p0, _ms0) = job0.finish().unwrap();

    fixture.assert_proof(&p0);
    drop(p0);
    let (p1, _ms1) = job1.finish().unwrap();

    fixture.assert_proof(&p1);
    drop(p1);
    assert_eq!(
        fixture.base.context.get_used_mem_current(),
        baseline,
        "device memory must return to baseline after both proofs complete"
    );
}

#[test]
#[ignore]
fn run_mixed_circuit_multi_schedule_test() {
    let add_sub = prepare_basic_unrolled_proof_fixture();
    // Both contexts use the default twiddle geometry. Keep Keccak's context
    // alive through finish: its construction replaces the shared twiddle pointers.
    let keccak = prepare_keccak_special5_proof_fixture();
    let context = &add_sub.base.context;
    let baseline = context.get_used_mem_current();
    let fixtures = [&add_sub, &keccak, &add_sub];
    let mut jobs = Vec::with_capacity(fixtures.len());
    for fixture in fixtures {
        let base = &fixture.base;
        let mut transfers = base.create_transfers_for_context(context).unwrap();
        transfers.schedule(context).unwrap();
        jobs.push(
            prove::<Global>(
                &base.gkr_programs,
                &base.prover_config,
                base.final_trace_size_log_2,
                transfers,
                ProofMemoryPolicy::default(),
                context,
            )
            .unwrap(),
        );
        assert_eq!(context.get_used_mem_current(), baseline);
    }
    for (job, fixture) in jobs.into_iter().zip(fixtures) {
        let (proof, _) = job.finish().unwrap();
        fixture.assert_proof(&proof);
    }
    assert_eq!(context.get_used_mem_current(), baseline);
}

/// Warmup + profiled prove; structure check only (no committed proof needed).
pub(super) fn run_profile(fixture: &BasicUnrolledFixture) {
    let baseline = fixture.context.get_used_mem_current();
    let warm = fixture.schedule_transfers().unwrap();
    fixture.context.get_h2d_stream().synchronize().unwrap();
    let warm_job = fixture.prove(warm).unwrap();
    let (warm_proof, _warm_ms) = warm_job.finish().unwrap();

    assert_gkr_proof_structure_for_test(&warm_proof, &fixture.prover_config.whir_schedule);
    drop(warm_proof);
    let prof = fixture.schedule_transfers().unwrap();
    fixture.context.get_h2d_stream().synchronize().unwrap();
    fixture.context.reset_used_mem_peak();
    let (prof_proof, _prof_ms) = {
        let _range = scoped_range(
            Some("gpu_circuit_prover.tests"),
            "test.gpu.prove.profiled_call",
        );
        fixture.prove(prof).unwrap().finish().unwrap()
    };

    assert_gkr_proof_structure_for_test(&prof_proof, &fixture.prover_config.whir_schedule);
    drop(prof_proof);
    let peak = fixture.context.get_used_mem_peak();

    assert!(peak > baseline);
    assert_eq!(fixture.context.get_used_mem_current(), baseline);
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
            BaseCommitmentGeometry::from_config(
                &fixture.prover_config,
                BaseColumns::of(&fixture.compiled_circuit),
            ),
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
    run_proof_parity(&prepare_basic_unrolled_proof_fixture());
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

pub(super) fn prepare_jump_branch_slt_proof_fixture() -> BasicUnrolledProofFixture {
    prepare_canonical_proof_fixture(
        CanonicalCircuit::JumpBranchSlt,
        circuit_common::SoundnessMode::DEFAULT,
    )
}

fn prepare_jump_branch_slt_profiling_fixture() -> BasicUnrolledFixture {
    prepare_jump_branch_slt_proof_fixture().base
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

pub(super) fn prepare_shift_binop_proof_fixture() -> BasicUnrolledProofFixture {
    prepare_canonical_proof_fixture(
        CanonicalCircuit::ShiftBinop,
        circuit_common::SoundnessMode::DEFAULT,
    )
}

fn prepare_shift_binop_profiling_fixture() -> BasicUnrolledFixture {
    prepare_shift_binop_proof_fixture().base
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

pub(super) fn prepare_mul_div_proof_fixture() -> BasicUnrolledProofFixture {
    prepare_canonical_proof_fixture(
        CanonicalCircuit::UnsignedMulDiv,
        circuit_common::SoundnessMode::DEFAULT,
    )
}

fn prepare_mul_div_profiling_fixture() -> BasicUnrolledFixture {
    prepare_mul_div_proof_fixture().base
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

pub(super) fn prepare_load_store_word_only_proof_fixture() -> BasicUnrolledProofFixture {
    prepare_canonical_proof_fixture(
        CanonicalCircuit::MemWordOnly,
        circuit_common::SoundnessMode::DEFAULT,
    )
}

fn prepare_load_store_word_only_profiling_fixture() -> BasicUnrolledFixture {
    prepare_load_store_word_only_proof_fixture().base
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

pub(super) fn prepare_load_store_subword_only_proof_fixture() -> BasicUnrolledProofFixture {
    prepare_canonical_proof_fixture(
        CanonicalCircuit::MemSubwordOnly,
        circuit_common::SoundnessMode::DEFAULT,
    )
}

fn prepare_load_store_subword_only_profiling_fixture() -> BasicUnrolledFixture {
    prepare_load_store_subword_only_proof_fixture().base
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
// These fixtures use the shared canonical recipe and committed proof bytes.
// Tests remain ignored because they execute complete GPU proofs.

pub(super) fn prepare_bigint_proof_fixture() -> BasicUnrolledProofFixture {
    prepare_canonical_proof_fixture(
        CanonicalCircuit::BigintWithExtendedControl,
        circuit_common::SoundnessMode::DEFAULT,
    )
}

pub(super) fn prepare_bigint_proof_fixture_for_config(
    config: ProverConfig,
) -> BasicUnrolledProofFixture {
    prepare_canonical_proof_fixture_for_config(CanonicalCircuit::BigintWithExtendedControl, config)
}

fn prepare_bigint_profiling_fixture() -> BasicUnrolledFixture {
    prepare_bigint_proof_fixture().base
}

/// bigint delegation proof_parity: GPU proof == committed proof, byte-identical.
/// `#[ignore]`d as a heavy GPU test — run with `--ignored`.
#[test]
#[ignore]
fn run_bigint_proof_parity_test() {
    run_proof_parity(&prepare_bigint_proof_fixture());
}

#[test]
#[ignore]
fn run_bigint_multi_schedule_test() {
    super::geometry_proof::geometry_proof(prepare_bigint_proof_fixture());
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
// delegation proof is verified byte-equal to the committed proof — see the section
// banner above.
// ---------------------------------------------------------------------------

pub(super) fn prepare_keccak_special5_proof_fixture() -> BasicUnrolledProofFixture {
    prepare_canonical_proof_fixture(
        CanonicalCircuit::KeccakSpecial5,
        circuit_common::SoundnessMode::DEFAULT,
    )
}

fn prepare_keccak_special5_profiling_fixture() -> BasicUnrolledFixture {
    prepare_keccak_special5_proof_fixture().base
}

/// keccak_special5 delegation proof_parity: GPU proof == committed proof,
/// byte-identical. `#[ignore]`d as a heavy GPU test — run with `--ignored`.
#[test]
#[ignore]
fn run_keccak_special5_proof_parity_test() {
    run_proof_parity(&prepare_keccak_special5_proof_fixture());
}

#[test]
#[ignore]
fn run_keccak_special5_multi_schedule_test() {
    super::geometry_proof::geometry_proof(prepare_keccak_special5_proof_fixture());
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

pub(super) fn prepare_blake2_with_compression_proof_fixture() -> BasicUnrolledProofFixture {
    prepare_canonical_proof_fixture(
        CanonicalCircuit::Blake2WithExtendedControl,
        circuit_common::SoundnessMode::DEFAULT,
    )
}

pub(super) fn prepare_blake2_with_compression_proof_fixture_for_config(
    config: ProverConfig,
) -> BasicUnrolledProofFixture {
    prepare_canonical_proof_fixture_for_config(CanonicalCircuit::Blake2WithExtendedControl, config)
}

fn prepare_blake2_with_compression_profiling_fixture() -> BasicUnrolledFixture {
    prepare_blake2_with_compression_proof_fixture().base
}

/// blake2_with_compression (blake2_with_extended_control) delegation proof_parity:
/// GPU proof == committed proof, byte-identical. `#[ignore]`d as a heavy GPU test —
/// run with `--ignored`.
#[test]
#[ignore]
fn run_blake2_with_compression_proof_parity_test() {
    run_proof_parity(&prepare_blake2_with_compression_proof_fixture());
}

#[test]
#[ignore]
fn run_blake2_with_compression_multi_schedule_test() {
    super::geometry_proof::geometry_proof(prepare_blake2_with_compression_proof_fixture());
}

#[test]
#[ignore]
fn run_blake2_with_compression_profile_test() {
    run_profile(&prepare_blake2_with_compression_profiling_fixture());
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
/// field-wise bit-exact vs the committed canonical proof
/// (`assert_gkr_proof_eq_for_test` covers `grand_product_accumulator_computed` AND
/// `whir_proof` incl. PoW/queries). Then drives the no-filter grand-product
/// accumulator closure using the GPU proof's accumulator and asserts it closes to
/// `E4::ONE` using the replayed boundary and committed compression factor.
/// This exercises the full backward and WHIR path, including base-layer cached
/// relation extras in the transcript.
///
/// Concurrent shape (schedule -> schedule -> finish -> finish), NOT serial: both
/// unified (2^23) jobs are scheduled before either finishes, so the second proof's
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

    let (gpu_proof_0, _proof_time_ms_0) = proof_job_0.finish().unwrap();

    fixture.assert_proof(&gpu_proof_0);

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
    let (gpu_proof_1, _proof_time_ms_1) = proof_job_1.finish().unwrap();

    fixture.assert_proof(&gpu_proof_1);
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

pub(super) fn prepare_inits_and_teardowns_matrix_proof_fixture() -> BasicUnrolledProofFixture {
    prepare_canonical_proof_fixture(
        CanonicalCircuit::InitsAndTeardowns,
        circuit_common::SoundnessMode::DEFAULT,
    )
}

fn prepare_inits_and_teardowns_matrix_profiling_fixture() -> BasicUnrolledFixture {
    prepare_inits_and_teardowns_matrix_proof_fixture().base
}

// Regression guards for zero-width base-layer handling (width-0 witness):
// initial transcript cap gating and WHIR base-cap gating.
#[test]
#[ignore]
fn run_inits_and_teardowns_proof_parity_test() {
    let fixture = prepare_inits_and_teardowns_matrix_proof_fixture();
    assert_eq!(fixture.base.compiled_circuit.witness_layout.total_width, 0);
    assert_eq!(fixture.base.compiled_circuit.generic_lookup_tables_width, 0);
    assert!(fixture.base.gpu_setup_host.is_none());
    run_proof_parity(&fixture);
}

#[test]
#[ignore]
fn run_inits_and_teardowns_ethproofs_proof_parity_test() {
    run_whir_pow_proof_parity(&prepare_canonical_proof_fixture(
        CanonicalCircuit::InitsAndTeardowns,
        circuit_common::SoundnessMode::EthproofsSoundnessCalc,
    ));
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

pub(super) mod keccak_f1600 {
    use super::*;
    pub(in crate::tests) fn keccak_chi5() -> BasicUnrolledProofFixture {
        prepare_canonical_proof_fixture(
            CanonicalCircuit::KeccakChi5,
            circuit_common::SoundnessMode::DEFAULT,
        )
    }
    #[test]
    #[ignore]
    fn run_keccak_chi5_multi_schedule_test() {
        super::super::geometry_proof::geometry_proof(keccak_chi5());
    }
    #[test]
    #[ignore]
    fn run_keccak_chi5_stage1_buffer_parity_test() {
        run_stage1_buffer_parity(&keccak_chi5().base);
    }
    pub(in crate::tests) fn keccak_column_parity() -> BasicUnrolledProofFixture {
        prepare_canonical_proof_fixture(
            CanonicalCircuit::KeccakColumnParity,
            circuit_common::SoundnessMode::DEFAULT,
        )
    }
    #[test]
    #[ignore]
    fn run_keccak_column_parity_multi_schedule_test() {
        super::super::geometry_proof::geometry_proof(keccak_column_parity());
    }
    #[test]
    #[ignore]
    fn run_keccak_column_parity_stage1_buffer_parity_test() {
        run_stage1_buffer_parity(&keccak_column_parity().base);
    }
    pub(in crate::tests) fn keccak_theta_rho() -> BasicUnrolledProofFixture {
        prepare_canonical_proof_fixture(
            CanonicalCircuit::KeccakThetaRho,
            circuit_common::SoundnessMode::DEFAULT,
        )
    }
    #[test]
    #[ignore]
    fn run_keccak_theta_rho_multi_schedule_test() {
        super::super::geometry_proof::geometry_proof(keccak_theta_rho());
    }
    #[test]
    #[ignore]
    fn run_keccak_theta_rho_stage1_buffer_parity_test() {
        run_stage1_buffer_parity(&keccak_theta_rho().base);
    }
}

// ---------------------------------------------------------------------------
// EthproofsSoundnessCalc mode: internal-round folding-challenge and OOD-draw
// PoW. The committed proof and the GPU proof share the mode's config.
// ---------------------------------------------------------------------------

/// GPU proof == committed proof under a config that gates WHIR folding
/// challenges and OOD draws, and the reference really carries those nonces.
fn run_whir_pow_proof_parity(fixture: &BasicUnrolledProofFixture) {
    let schedule = &fixture.base.prover_config.whir_schedule;
    let whir = &fixture.committed_proof.whir_proof;
    assert_eq!(schedule.base_round.folding_pow_bits, 0);
    assert!(schedule.internal_rounds.iter().any(|r| r.ood_pow_bits > 0));
    for (oracle, round) in whir
        .intermediate_whir_oracles
        .iter()
        .zip(&schedule.internal_rounds)
    {
        assert!(round.folding_pow_bits > 0);
        assert_eq!(oracle.folding_pow_nonces.len(), round.folding_log2);
        assert_eq!(oracle.ood_pow_nonce.is_some(), round.ood_pow_bits > 0);
    }
    let (gpu_proof, _ms) = fixture.schedule_prove().unwrap().finish().unwrap();
    fixture.assert_proof(&gpu_proof);
}

#[test]
#[ignore]
fn run_bigint_ethproofs_proof_parity_test() {
    let config = CanonicalCircuit::BigintWithExtendedControl.prover_config(
        &test_artifact_path(""),
        circuit_common::SoundnessMode::EthproofsSoundnessCalc,
    );
    run_whir_pow_proof_parity(&prepare_bigint_proof_fixture_for_config(config));
}

#[test]
#[ignore]
fn run_blake2_with_compression_ethproofs_proof_parity_test() {
    let config = CanonicalCircuit::Blake2WithExtendedControl.prover_config(
        &test_artifact_path(""),
        circuit_common::SoundnessMode::EthproofsSoundnessCalc,
    );
    run_whir_pow_proof_parity(&prepare_blake2_with_compression_proof_fixture_for_config(
        config,
    ));
}

#[test]
#[ignore]
fn run_add_sub_ethproofs_proof_parity_test() {
    run_whir_pow_proof_parity(&prepare_basic_unrolled_proof_fixture_in_mode(
        circuit_common::SoundnessMode::EthproofsSoundnessCalc,
    ));
}

#[test]
#[ignore]
fn run_unified_ethproofs_proof_parity_test() {
    run_whir_pow_proof_parity(&prepare_unified_proof_fixture_in_mode(
        circuit_common::SoundnessMode::EthproofsSoundnessCalc,
    ));
}
