use super::*;

// ---------------------------------------------------------------------------
// Generic test bodies
// ---------------------------------------------------------------------------

/// Full GPU proof == CPU reference (single proof).
pub(super) fn run_proof_parity(fixture: BasicUnrolledProofFixture) {
    let proof_job = fixture.schedule_prove().unwrap();
    let (gpu_proof, _ms) = proof_job.finish().unwrap();
    assert_gkr_proof_eq_for_test(&gpu_proof, &fixture.expected_cpu_proof);
}

/// Two concurrently-scheduled proofs on a recycled-block arena (the
/// uninitialized-witness regression guard). schedule -> schedule -> finish -> finish.
pub(super) fn run_multi_schedule(fixture: BasicUnrolledProofFixture) {
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
pub(super) fn run_profile(fixture: BasicUnrolledFixture) {
    let baseline = fixture.context.get_used_mem_current();
    let warm = fixture.schedule_transfers().unwrap();
    fixture.context.get_h2d_stream().synchronize().unwrap();
    let warm_job = fixture.prove(warm).unwrap();
    let (warm_proof, warm_ms) = warm_job.finish().unwrap();
    eprintln!("warmup proof time: {warm_ms} ms");
    assert_gkr_proof_structure_for_test(&warm_proof, &fixture.prover_config.whir_schedule);
    drop(warm_proof);
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

// ---------------------------------------------------------------------------
// add_sub hand-written per-circuit test functions
// ---------------------------------------------------------------------------

#[test]
#[serial]
#[ignore]
fn run_add_sub_proof_parity_test() {
    run_proof_parity(prepare_basic_unrolled_proof_fixture());
}

/// Full-proof parity at Sec100, where the lookup-challenge and WHIR-batching
/// PoWs are non-zero — exercises the on-device grinding + nonce path.
#[test]
#[serial]
#[ignore]
fn run_add_sub_proof_parity_test_sec100() {
    run_proof_parity(prepare_basic_unrolled_proof_fixture_sec100());
}

#[test]
#[serial]
#[ignore]
fn run_add_sub_multi_schedule_test() {
    run_multi_schedule(prepare_basic_unrolled_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_add_sub_profile_test() {
    run_profile(prepare_basic_unrolled_profiling_fixture());
}

// ---------------------------------------------------------------------------
// jump_branch_slt fixture wrappers + test functions
// ---------------------------------------------------------------------------

fn prepare_jump_branch_slt_proof_fixture() -> BasicUnrolledProofFixture {
    let (base, p) = prepare_unrolled_non_memory_proof_fixture::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        4, // jump_branch_slt default_pc_value_in_padding (== GPU PC_STEP)
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
        4, // jump_branch_slt default_pc_value_in_padding (== GPU PC_STEP)
        UnrolledNonMemoryCircuitType::JumpBranchSlt,
        JUMP_BRANCH_SLT_LAYOUT_PATH,
        jump_branch_slt_mod::witness_eval_fn,
        cs::gkr_circuits::jump_branch_slt_family::jump_branch_slt_table_driver_fn::<BF>,
        false,
    )
    .0
}

#[test]
#[serial]
#[ignore]
fn run_jump_branch_slt_proof_parity_test() {
    run_proof_parity(prepare_jump_branch_slt_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_jump_branch_slt_multi_schedule_test() {
    run_multi_schedule(prepare_jump_branch_slt_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_jump_branch_slt_profile_test() {
    run_profile(prepare_jump_branch_slt_profiling_fixture());
}

// ---------------------------------------------------------------------------
// shift_binop fixture wrappers + test functions
// ---------------------------------------------------------------------------

fn prepare_shift_binop_proof_fixture() -> BasicUnrolledProofFixture {
    let (base, p) = prepare_unrolled_non_memory_proof_fixture::<SHIFT_BINARY_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        4,
        UnrolledNonMemoryCircuitType::ShiftBinaryCsr,
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
        4,
        UnrolledNonMemoryCircuitType::ShiftBinaryCsr,
        SHIFT_BINOP_LAYOUT_PATH,
        shift_binop_mod::witness_eval_fn,
        cs::gkr_circuits::binary_shifts_family::shift_binop_table_driver_fn::<BF>,
        false,
    )
    .0
}

#[test]
#[serial]
#[ignore]
fn run_shift_binop_proof_parity_test() {
    run_proof_parity(prepare_shift_binop_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_shift_binop_multi_schedule_test() {
    run_multi_schedule(prepare_shift_binop_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_shift_binop_profile_test() {
    run_profile(prepare_shift_binop_profiling_fixture());
}

// ---------------------------------------------------------------------------
// mul_div fixture wrappers + test functions
// ---------------------------------------------------------------------------

fn prepare_mul_div_proof_fixture() -> BasicUnrolledProofFixture {
    let (base, p) = prepare_unrolled_non_memory_proof_fixture::<MUL_DIV_CIRCUIT_FAMILY_IDX>(
        &[15, 1],
        4,
        UnrolledNonMemoryCircuitType::MulDivUnsigned,
        UNSIGNED_MUL_DIV_LAYOUT_PATH,
        unsigned_mul_div_mod::witness_eval_fn,
        |td| cs::gkr_circuits::mul_div::mul_div_table_driver_fn::<BF, false>(td),
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
        4,
        UnrolledNonMemoryCircuitType::MulDivUnsigned,
        UNSIGNED_MUL_DIV_LAYOUT_PATH,
        unsigned_mul_div_mod::witness_eval_fn,
        |td| cs::gkr_circuits::mul_div::mul_div_table_driver_fn::<BF, false>(td),
        false,
    )
    .0
}

#[test]
#[serial]
#[ignore]
fn run_mul_div_proof_parity_test() {
    run_proof_parity(prepare_mul_div_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_mul_div_multi_schedule_test() {
    run_multi_schedule(prepare_mul_div_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_mul_div_profile_test() {
    run_profile(prepare_mul_div_profiling_fixture());
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
#[serial]
#[ignore]
fn run_load_store_word_only_proof_parity_test() {
    run_proof_parity(prepare_load_store_word_only_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_load_store_word_only_multi_schedule_test() {
    run_multi_schedule(prepare_load_store_word_only_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_load_store_word_only_profile_test() {
    run_profile(prepare_load_store_word_only_profiling_fixture());
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
#[serial]
#[ignore]
fn run_load_store_subword_only_proof_parity_test() {
    run_proof_parity(prepare_load_store_subword_only_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_load_store_subword_only_multi_schedule_test() {
    run_multi_schedule(prepare_load_store_subword_only_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_load_store_subword_only_profile_test() {
    run_profile(prepare_load_store_subword_only_profiling_fixture());
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
// keccak / bigint / blake2_with_compression originally overflowed the fused flat
// backward path's inline `__constant__`/`__grid_constant__` capacity caps. They
// are unblocked by the dual-path device-memory fallback + capacity
// raises (coeff / terms / recipe device buffers, per-layer cap raises), plus the
// GKR materialize-gate sumcheck-emit fix and the WHIR query-index transcript fix.
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
/// the fixture drives a REAL bigint delegation proof instead of the previous
/// empty-buffer short-circuit.
fn replay_bigint_delegation_buffer() -> (Vec<BigintDelegationWitness>, TableDriver<BF>) {
    let buffer = replay_delegation_trace_buffer_for_workload::<_, FullUnsignedMachineDecoderConfig>(
        BIGINT_WITH_CONTROL_BINARY_PATH,
        BIGINT_WITH_CONTROL_TEXT_PATH,
        &[15, 1],
        false,
        |counters| counters.bigint_calls,
        BigintDelegationWitness::empty(),
        |tape, cycles_bound, replay_state, replay_ram, buffer| {
            let mut buffers = vec![buffer];
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
        table_driver,
        buffer_for_host,
        oracle,
        bigint_with_extended_control_mod::witness_eval_fn,
        1 << 22,
    );
    drop(buffer);
    fixture
}

fn prepare_bigint_profiling_fixture() -> BasicUnrolledFixture {
    let (buffer, table_driver) = replay_bigint_delegation_buffer();
    let oracle = BigintDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    let buffer_for_host = buffer.clone();
    let fixture = prepare_delegation_profiling_fixture(
        DelegationCircuitType::BigIntWithControl,
        BIGINT_DELEGATION_LAYOUT_PATH,
        table_driver,
        buffer_for_host,
        oracle,
        bigint_with_extended_control_mod::witness_eval_fn,
        1 << 22,
    );
    drop(buffer);
    fixture
}

/// bigint delegation proof_parity: GPU proof == CPU reference, byte-identical.
/// `#[ignore]`d as a heavy GPU test — run with `--ignored`.
#[test]
#[serial]
#[ignore]
fn run_bigint_proof_parity_test() {
    run_proof_parity(prepare_bigint_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_bigint_multi_schedule_test() {
    run_multi_schedule(prepare_bigint_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_bigint_profile_test() {
    run_profile(prepare_bigint_profiling_fixture());
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
            let mut buffers = vec![buffer];
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
        table_driver,
        buffer_for_host,
        oracle,
        fixtures::keccak_special5_mod::witness_eval_fn,
        1 << 22,
    );
    drop(buffer);
    fixture
}

fn prepare_keccak_special5_profiling_fixture() -> BasicUnrolledFixture {
    let (buffer, table_driver) = replay_keccak_special5_delegation_buffer();
    let oracle = KeccakDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    let buffer_for_host = buffer.clone();
    let fixture = prepare_delegation_profiling_fixture(
        DelegationCircuitType::KeccakSpecial5,
        KECCAK_SPECIAL5_DELEGATION_LAYOUT_PATH,
        table_driver,
        buffer_for_host,
        oracle,
        fixtures::keccak_special5_mod::witness_eval_fn,
        1 << 22,
    );
    drop(buffer);
    fixture
}

/// keccak_special5 delegation proof_parity: GPU proof == CPU reference,
/// byte-identical. `#[ignore]`d as a heavy GPU test — run with `--ignored`.
#[test]
#[serial]
#[ignore]
fn run_keccak_special5_proof_parity_test() {
    run_proof_parity(prepare_keccak_special5_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_keccak_special5_multi_schedule_test() {
    run_multi_schedule(prepare_keccak_special5_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_keccak_special5_profile_test() {
    run_profile(prepare_keccak_special5_profiling_fixture());
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
            let mut buffers = vec![buffer];
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
        table_driver,
        buffer_for_host,
        oracle,
        fixtures::blake2_with_extended_control_mod::witness_eval_fn,
        BLAKE2_NUM_DELEGATION_CYCLES,
    );
    drop(buffer);
    fixture
}

fn prepare_blake2_with_compression_profiling_fixture() -> BasicUnrolledFixture {
    let (buffer, table_driver) = replay_blake2_with_compression_delegation_buffer();
    let oracle = Blake2sDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    let buffer_for_host = buffer.clone();
    let fixture = prepare_delegation_profiling_fixture(
        DelegationCircuitType::Blake2WithCompression,
        BLAKE2_WITH_COMPRESSION_LAYOUT_PATH,
        table_driver,
        buffer_for_host,
        oracle,
        fixtures::blake2_with_extended_control_mod::witness_eval_fn,
        BLAKE2_NUM_DELEGATION_CYCLES,
    );
    drop(buffer);
    fixture
}

/// blake2_with_compression (blake2_with_extended_control) delegation proof_parity:
/// GPU proof == CPU reference, byte-identical. `#[ignore]`d as a heavy GPU test —
/// run with `--ignored`.
#[test]
#[serial]
#[ignore]
fn run_blake2_with_compression_proof_parity_test() {
    run_proof_parity(prepare_blake2_with_compression_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_blake2_with_compression_multi_schedule_test() {
    run_multi_schedule(prepare_blake2_with_compression_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_blake2_with_compression_profile_test() {
    run_profile(prepare_blake2_with_compression_profiling_fixture());
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
            let mut buffers = vec![buffer];
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
        table_driver,
        buffer_for_host,
        oracle,
        fixtures::blake2_g_function_mod::witness_eval_fn,
        BLAKE2_G_FUNCTION_NUM_DELEGATION_CYCLES,
    );
    drop(buffer);
    fixture
}

fn prepare_blake2_g_function_profiling_fixture() -> BasicUnrolledFixture {
    let (buffer, table_driver) = replay_blake2_g_function_delegation_buffer();
    let oracle = Blake2sGFunctionDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    let buffer_for_host = buffer.clone();
    let fixture = prepare_delegation_profiling_fixture(
        DelegationCircuitType::Blake2GFunction,
        BLAKE2_G_FUNCTION_LAYOUT_PATH,
        table_driver,
        buffer_for_host,
        oracle,
        fixtures::blake2_g_function_mod::witness_eval_fn,
        BLAKE2_G_FUNCTION_NUM_DELEGATION_CYCLES,
    );
    drop(buffer);
    fixture
}

/// blake2_g_function delegation proof_parity. The GPU proof is
/// byte-identical to the CPU reference (blake_g_function_calls = 80). This is the
/// one delegation that proves end-to-end via the GPU `prove()` path, confirming the
/// generic delegation fixture builder is sound. `#[ignore]`d only because it is a
/// heavy GPU test.
#[test]
#[serial]
#[ignore]
fn run_blake2_g_function_proof_parity_test() {
    run_proof_parity(prepare_blake2_g_function_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_blake2_g_function_multi_schedule_test() {
    run_multi_schedule(prepare_blake2_g_function_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_blake2_g_function_profile_test() {
    run_profile(prepare_blake2_g_function_profiling_fixture());
}

// ---------------------------------------------------------------------------
// unified multi_schedule (with closure-to-ONE grand-product assertions)
// ---------------------------------------------------------------------------

/// Full e2e unified proof parity + closure-to-ONE.
///
/// Proves the unified_reduced_machine circuit on the GPU and asserts the proof is
/// field-wise bit-exact vs the CPU `prove_configured_with_gkr` reference
/// (`assert_gkr_proof_eq_for_test` covers `grand_product_accumulator_computed` AND
/// `whir_proof` incl. PoW/queries). Then drives the no-filter grand-product
/// accumulator closure using the GPU proof's accumulator and asserts it closes to
/// `E4::ONE` — mirroring the CPU orchestration (orchestration/unified.rs:259-278).
/// Unlike GATE 2 (stagewise), this exercises the full backward+WHIR path, so it is
/// the first test that commits the base-layer (layer 0) cached-relation extras into
/// the WHIR transcript.
///
/// Concurrent shape (schedule -> schedule -> finish -> finish), NOT serial: both
/// unified (2^24) jobs are scheduled before either finishes, so the second proof's
/// device allocations land on blocks the first proof wrote and freed (the first
/// job keeps only its input transfers alive until `finish()`, which shifts the
/// second proof's placement onto recycled, non-zero memory). This is the exact
/// condition that exposed a witness-trace uninitialized-read: the witness
/// generators write the per-opcode lookup columns only under `IF` guards, so rows
/// whose opcode doesn't match were left unwritten and read as fresh-page zeros on a
/// first proof but as stale data on the recycled second proof — diverging the
/// `Lookup16Bits`/`LookupTimestamps`/`GenericLookup` base-layer claims. The fix is
/// the codegen zero-default for conditionally-written witness columns
/// (`gpu_witness_eval_generator`); this test guards against its regression.
/// `prove()` is balanced — every device allocation it makes is released
/// stream-ordered before it returns (asserted per-prove in `schedule_prove`) — so a
/// single ~54 GiB peak fits the 64 GiB fixture arena even with both jobs live.
#[test]
#[serial]
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

/// Unified circuit single-proof parity, matching the `proof_parity` body every
/// other circuit uses: prove once and assert field-wise bit-exactness vs the CPU
/// `prove_configured_with_gkr` reference (`assert_gkr_proof_eq_for_test`, which
/// covers `grand_product_accumulator_computed` and the full `whir_proof`). The
/// grand-product closure-to-ONE check specific to the full machine lives in
/// `run_unified_multi_schedule_test`; this test exists so unified has the same
/// proof_parity / multi_schedule / profile trio as the other circuits.
#[test]
#[serial]
#[ignore]
fn run_unified_proof_parity_test() {
    run_proof_parity(prepare_unified_proof_fixture());
}

/// Unified circuit profile run (warmup + profiled prove, structure check only).
/// Uses a no-CPU-reference fixture so it skips the expensive CPU unified prove.
#[test]
#[serial]
#[ignore]
fn run_unified_profile_test() {
    run_profile(prepare_unified_profiling_fixture());
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

// Full-proof parity for the reduced-output inits-and-teardowns circuit
// (PermutationProduct only, width-0 witness layer). These were the regression
// guards for two zero-width-base-layer GPU bugs, now FIXED (CPU = source of
// truth):
//   1. The initial transcript committed the width-0 witness Merkle cap that the
//      CPU omits (`witness_layout.total_width == 0`), diverging the seed and
//      every downstream challenge — the evaluation point, backward sumcheck, and
//      WHIR. Fixed in `stage1_forward.rs` by gating the memory/witness cap
//      commits on their layout widths, matching the CPU.
//   2. The parsed WHIR proof emitted a degenerate 16-digest cap for the width-0
//      witness oracle, where the CPU's dummy tree yields an empty cap. Fixed in
//      `proof_layout/accessors.rs::parse_whir_proof` by gating the base cap on
//      `num_columns == 0`.
#[test]
#[serial]
#[ignore]
fn run_inits_and_teardowns_proof_parity_test() {
    run_proof_parity(prepare_inits_and_teardowns_matrix_proof_fixture());
}

#[test]
#[serial]
#[ignore]
fn run_inits_and_teardowns_multi_schedule_test() {
    run_multi_schedule(prepare_inits_and_teardowns_matrix_proof_fixture());
}

// This one PASSES: `run_profile` checks proof structure + peak memory only (no
// CPU comparison), so it is unaffected by the backward-sumcheck divergence.
#[test]
#[serial]
#[ignore]
fn run_inits_and_teardowns_profile_test() {
    run_profile(prepare_inits_and_teardowns_matrix_profiling_fixture());
}

// ---------------------------------------------------------------------------
// Forward VM layer-0 gate
// ---------------------------------------------------------------------------

/// Sets an env var for the duration of a test and restores the previous value.
struct EnvGuard {
    key: &'static str,
    previous: Option<String>,
}

impl EnvGuard {
    fn set(key: &'static str, value: &str) -> Self {
        let previous = std::env::var(key).ok();
        std::env::set_var(key, value);
        Self { key, previous }
    }
}

impl Drop for EnvGuard {
    fn drop(&mut self) {
        match &self.previous {
            Some(value) => std::env::set_var(self.key, value),
            None => std::env::remove_var(self.key),
        }
    }
}

/// The forward VM computing EVERY non-dimension-reducing layer of add_sub inside
/// the real prover must produce the same proof as the CPU reference, and must
/// actually have run — once per selected layer.
///
/// Both halves are load-bearing:
///
/// - Parity alone can pass vacuously. These tests are `#[serial]` in one
///   process, so by the time this runs the pool has already held — and freed —
///   blocks containing correct layer-0 outputs from earlier proofs. A VM that
///   launches but writes nothing could reproduce the right proof from recycled
///   values. `prepare_layer0_destinations` poisons every materialized
///   destination in test builds precisely so that cannot happen.
/// - The launch count alone proves nothing about values. It is asserted
///   EXACTLY, not `> 0`: one launch would not prove that every selected layer
///   ran, and the count must move with the selection rather than merely be
///   nonzero.
#[test]
#[serial]
#[ignore]
fn run_add_sub_vm_all_layers_proof_parity_test() {
    use crate::prover::gkr::forward::path::AB_GKR_FWD_VM_LAYERS_ENV;
    use crate::prover::gkr::forward::vm::count_fwd_vm_s4_launches;
    use crate::prover::gkr::forward::vm::production_bind::AB_GKR_FWD_VM_POISON_DESTINATIONS_ENV;

    let fixture = prepare_basic_unrolled_proof_fixture();
    // Opt into the destination poison: this gate, not the timing harness, is
    // where it belongs.
    let _poison = EnvGuard::set(AB_GKR_FWD_VM_POISON_DESTINATIONS_ENV, "1");
    let counter = count_fwd_vm_s4_launches();
    assert_eq!(
        counter.launches(),
        0,
        "counter must start at zero for the count below to mean anything"
    );

    // Every non-dimension-reducing layer of add_sub. Dimension reduction runs
    // after the layer loop and is not a VM layer.
    const SELECTED: &str = "0,1,2,3";
    let selected_layers = SELECTED.split(',').count();
    let (gpu_proof, launches) = {
        let _env = EnvGuard::set(AB_GKR_FWD_VM_LAYERS_ENV, SELECTED);
        let job = fixture.schedule_prove().unwrap();
        let (proof, _ms) = job.finish().unwrap();
        (proof, counter.launches())
    };

    assert_gkr_proof_eq_for_test(&gpu_proof, &fixture.expected_cpu_proof);
    assert_eq!(
        launches, selected_layers,
        "the VM must have launched exactly once per selected layer"
    );
    eprintln!("[fwd-vm-parity] {selected_layers} layers on the VM, proof bit-equal to the CPU reference");
}

/// With the switches unset neither VM must run at all — the guard that the
/// env vars, and nothing else, are what select the paths.
#[test]
#[serial]
#[ignore]
fn run_add_sub_without_the_vm_switch_launches_no_vm_kernel() {
    use crate::prover::gkr::backward::vm::production_bind::count_bwd_vm_r0_launches;
    use crate::prover::gkr::forward::vm::count_fwd_vm_s4_launches;

    let fixture = prepare_basic_unrolled_proof_fixture();
    let fwd_counter = count_fwd_vm_s4_launches();
    let bwd_counter = count_bwd_vm_r0_launches();
    let job = fixture.schedule_prove().unwrap();
    let (gpu_proof, _ms) = job.finish().unwrap();
    assert_gkr_proof_eq_for_test(&gpu_proof, &fixture.expected_cpu_proof);
    assert_eq!(fwd_counter.launches(), 0);
    assert_eq!(bwd_counter.launches(), 0);
}

/// The backward VM computing add_sub L0's round 0 inside the real prover must
/// produce the same proof as the CPU reference, and must actually have run —
/// exactly once.
///
/// Both halves are load-bearing, for the same reasons as the forward gate
/// above: parity alone can pass vacuously (the accumulator poison closes the
/// recycled-pool hole), and a count alone proves nothing about values.
#[test]
#[serial]
#[ignore]
fn run_add_sub_bwd_vm_l0_r0_proof_parity_test() {
    use crate::prover::gkr::backward::vm::coords::AB_GKR_BWD_VM_COORDS_ENV;
    use crate::prover::gkr::backward::vm::production_bind::{
        count_bwd_vm_r0_launches, AB_GKR_BWD_VM_POISON_ACCUMULATOR_ENV,
    };

    let fixture = prepare_basic_unrolled_proof_fixture();
    // Opt into the accumulator poison: this gate, not the timing harness, is
    // where it belongs.
    let _poison = EnvGuard::set(AB_GKR_BWD_VM_POISON_ACCUMULATOR_ENV, "1");
    let counter = count_bwd_vm_r0_launches();
    assert_eq!(
        counter.launches(),
        0,
        "counter must start at zero for the count below to mean anything"
    );

    let (gpu_proof, launches) = {
        let _env = EnvGuard::set(AB_GKR_BWD_VM_COORDS_ENV, "0:R0");
        let job = fixture.schedule_prove().unwrap();
        let (proof, _ms) = job.finish().unwrap();
        (proof, counter.launches())
    };

    assert_gkr_proof_eq_for_test(&gpu_proof, &fixture.expected_cpu_proof);
    assert_eq!(
        launches, 1,
        "exactly one VM-owned R0 launch: L0's round 0 and nothing else"
    );
    eprintln!("[bwd-vm-parity] L0 R0 on the VM, proof bit-equal to the CPU reference");
}

/// The add_sub fixture's main-layer folding steps (trace_len = 2^24), pinned:
/// the Ext gates assert their launch counts EXACTLY, and the expected count is
/// `folding_steps - 1` continuation rounds. A fixture trace-size change fails
/// these gates loudly and updates this constant deliberately.
/// add_sub's main-layer count — the layers its backward VM coordinates cover.
/// Pinned here rather than read from the artifact so a layer-count change shows up
/// as a test failure with a name on it.
const ADD_SUB_MAIN_LAYERS: usize = 4;

const ADD_SUB_FIXTURE_FOLDING_STEPS: usize = 24;

/// The backward VM owning ALL of add_sub L0's continuation rounds (1..=23,
/// the final round included) inside the real prover must produce the same
/// proof as the CPU reference — with the final gather untouched, reading the
/// cascade slots the VM published — and must have launched exactly once per
/// continuation round.
///
/// Round 0 stays flat here (`0:Ext` alone), so the R0 counter must stay zero:
/// the two coordinates select independently.
#[test]
#[serial]
#[ignore]
fn run_add_sub_bwd_vm_l0_ext_proof_parity_test() {
    use crate::prover::gkr::backward::vm::coords::AB_GKR_BWD_VM_COORDS_ENV;
    use crate::prover::gkr::backward::vm::production_bind::{
        count_bwd_vm_r0_launches, AB_GKR_BWD_VM_POISON_ACCUMULATOR_ENV,
        AB_GKR_BWD_VM_POISON_CASCADE_ENV,
    };

    let fixture = prepare_basic_unrolled_proof_fixture();
    // Opt into the per-round accumulator poison: 23 VM rounds each rewrite the
    // halves they own, so a round that silently launched nothing fails parity.
    // The cascade poison closes the other vacuity hole: every fold slot the
    // gather or a chain read consumes must first be VM-written, and the slots
    // the Inline policy never writes must never be read.
    let _poison = EnvGuard::set(AB_GKR_BWD_VM_POISON_ACCUMULATOR_ENV, "1");
    let _cascade_poison = EnvGuard::set(AB_GKR_BWD_VM_POISON_CASCADE_ENV, "1");
    let counter = count_bwd_vm_r0_launches();
    assert_eq!(
        (counter.launches(), counter.ext_launches()),
        (0, 0),
        "counters must start at zero for the counts below to mean anything"
    );

    let (gpu_proof, r0_launches, ext_launches) = {
        let _env = EnvGuard::set(AB_GKR_BWD_VM_COORDS_ENV, "0:Ext");
        let job = fixture.schedule_prove().unwrap();
        let (proof, _ms) = job.finish().unwrap();
        (proof, counter.launches(), counter.ext_launches())
    };

    assert_gkr_proof_eq_for_test(&gpu_proof, &fixture.expected_cpu_proof);
    assert_eq!(r0_launches, 0, "0:Ext must not select round 0");
    assert_eq!(
        ext_launches,
        ADD_SUB_FIXTURE_FOLDING_STEPS - 1,
        "exactly one VM launch per continuation round of L0, the final round included"
    );
    eprintln!(
        "[bwd-vm-parity] L0 rounds 1..={ext_launches} on the VM, proof bit-equal to the CPU \
         reference"
    );
}

/// Both coordinates together: the VM owns L0's round 0 AND every continuation
/// round — the whole layer — and the proof stays bit-equal.
#[test]
#[serial]
#[ignore]
fn run_add_sub_bwd_vm_l0_full_proof_parity_test() {
    use crate::prover::gkr::backward::vm::coords::AB_GKR_BWD_VM_COORDS_ENV;
    use crate::prover::gkr::backward::vm::production_bind::{
        count_bwd_vm_r0_launches, AB_GKR_BWD_VM_POISON_ACCUMULATOR_ENV,
        AB_GKR_BWD_VM_POISON_CASCADE_ENV,
    };

    let fixture = prepare_basic_unrolled_proof_fixture();
    let _poison = EnvGuard::set(AB_GKR_BWD_VM_POISON_ACCUMULATOR_ENV, "1");
    let _cascade_poison = EnvGuard::set(AB_GKR_BWD_VM_POISON_CASCADE_ENV, "1");
    let counter = count_bwd_vm_r0_launches();
    assert_eq!(
        (counter.launches(), counter.ext_launches()),
        (0, 0),
        "counters must start at zero for the counts below to mean anything"
    );

    let (gpu_proof, r0_launches, ext_launches) = {
        let _env = EnvGuard::set(AB_GKR_BWD_VM_COORDS_ENV, "0:R0,0:Ext");
        let job = fixture.schedule_prove().unwrap();
        let (proof, _ms) = job.finish().unwrap();
        (proof, counter.launches(), counter.ext_launches())
    };

    assert_gkr_proof_eq_for_test(&gpu_proof, &fixture.expected_cpu_proof);
    assert_eq!(r0_launches, 1, "exactly one VM-owned R0 launch");
    assert_eq!(
        ext_launches,
        ADD_SUB_FIXTURE_FOLDING_STEPS - 1,
        "exactly one VM launch per continuation round of L0"
    );
    eprintln!(
        "[bwd-vm-parity] L0 whole layer on the VM ({} launches), proof bit-equal to the CPU \
         reference",
        r0_launches + ext_launches
    );
}

/// Every main layer, both regimes: the VM owns the ENTIRE main-layer backward
/// sumcheck of add_sub, and the proof stays bit-equal.
///
/// Only the dimension-reducing sumcheck is left on the incumbent, which is a
/// permanent decision, not a gap. Each main layer folds over the same trace, so
/// every layer runs the same `folding_steps` — the expected counts are one R0
/// launch per layer and `folding_steps - 1` continuation launches per layer.
#[test]
#[serial]
#[ignore]
fn run_add_sub_bwd_vm_all_main_layers_proof_parity_test() {
    use crate::prover::gkr::backward::vm::coords::AB_GKR_BWD_VM_COORDS_ENV;
    use crate::prover::gkr::backward::vm::production_bind::{
        count_bwd_vm_r0_launches, AB_GKR_BWD_VM_POISON_ACCUMULATOR_ENV,
        AB_GKR_BWD_VM_POISON_CASCADE_ENV,
    };

    let fixture = prepare_basic_unrolled_proof_fixture();
    let _poison = EnvGuard::set(AB_GKR_BWD_VM_POISON_ACCUMULATOR_ENV, "1");
    let _cascade_poison = EnvGuard::set(AB_GKR_BWD_VM_POISON_CASCADE_ENV, "1");
    let counter = count_bwd_vm_r0_launches();
    assert_eq!(
        (counter.launches(), counter.ext_launches()),
        (0, 0),
        "counters must start at zero for the counts below to mean anything"
    );

    let coords = (0..ADD_SUB_MAIN_LAYERS)
        .map(|layer| format!("{layer}:R0,{layer}:Ext"))
        .collect::<Vec<_>>()
        .join(",");

    let (gpu_proof, r0_launches, ext_launches) = {
        let _env = EnvGuard::set(AB_GKR_BWD_VM_COORDS_ENV, &coords);
        let job = fixture.schedule_prove().unwrap();
        let (proof, _ms) = job.finish().unwrap();
        (proof, counter.launches(), counter.ext_launches())
    };

    assert_gkr_proof_eq_for_test(&gpu_proof, &fixture.expected_cpu_proof);
    assert_eq!(
        r0_launches, ADD_SUB_MAIN_LAYERS,
        "exactly one VM-owned R0 launch per main layer"
    );
    assert_eq!(
        ext_launches,
        ADD_SUB_MAIN_LAYERS * (ADD_SUB_FIXTURE_FOLDING_STEPS - 1),
        "exactly one VM launch per continuation round of every main layer"
    );
    eprintln!(
        "[bwd-vm-parity] all {ADD_SUB_MAIN_LAYERS} main layers on the VM ({} launches), proof bit-equal \
         to the CPU reference",
        r0_launches + ext_launches
    );
}

/// blake2_with_extended_control's main-layer count. The second (and only other)
/// entry in `gkr::vm_circuit_name`'s allowlist, and the widest circuit the VM has
/// a path for: 8 main layers against add_sub's 4.
const BLAKE2_MAIN_LAYERS: usize = 8;

/// The backward VM owning every main layer of blake2_with_extended_control, both
/// regimes, inside the real prover — the second circuit of the coverage gate.
///
/// This is the coordinate set the pre-address-table descriptor could not express.
/// `MAX_SOURCE_WINDOWS_USED = 17` bounded windows BEFORE splitting while blake2
/// L0 R0 needed 18 after, so the circuit was blocked on a cap that counted the
/// wrong thing. The combined source/destination address table removed splitting
/// altogether — slots are keyed by BACKING, and blake2 L0 Ext peaks at 24 of 64 —
/// so the bound this test exists to check is no longer the one that failed.
///
/// Launch counts are REPORTED, not pinned. add_sub's gates pin theirs against
/// `ADD_SUB_FIXTURE_FOLDING_STEPS`; blake2's fold depth has no constant in this
/// file yet, and inventing one from a first green run would pin whatever this run
/// happened to do rather than a fact about the circuit. Bit-equality against the
/// CPU reference is the claim; the counts are there to prove the VM ran at all,
/// which a silently-empty selection would otherwise fake.
#[test]
#[serial]
#[ignore]
fn run_blake2_bwd_vm_all_main_layers_proof_parity_test() {
    use crate::prover::gkr::backward::vm::coords::AB_GKR_BWD_VM_COORDS_ENV;
    use crate::prover::gkr::backward::vm::production_bind::{
        count_bwd_vm_r0_launches, AB_GKR_BWD_VM_POISON_ACCUMULATOR_ENV,
        AB_GKR_BWD_VM_POISON_CASCADE_ENV,
    };

    let fixture = prepare_blake2_with_compression_proof_fixture();
    let _poison = EnvGuard::set(AB_GKR_BWD_VM_POISON_ACCUMULATOR_ENV, "1");
    let _cascade_poison = EnvGuard::set(AB_GKR_BWD_VM_POISON_CASCADE_ENV, "1");
    let counter = count_bwd_vm_r0_launches();
    assert_eq!(
        (counter.launches(), counter.ext_launches()),
        (0, 0),
        "counters must start at zero for the counts below to mean anything"
    );

    let coords = (0..BLAKE2_MAIN_LAYERS)
        .map(|layer| format!("{layer}:R0,{layer}:Ext"))
        .collect::<Vec<_>>()
        .join(",");

    let (gpu_proof, r0_launches, ext_launches) = {
        let _env = EnvGuard::set(AB_GKR_BWD_VM_COORDS_ENV, &coords);
        let job = fixture.schedule_prove().unwrap();
        let (proof, _ms) = job.finish().unwrap();
        (proof, counter.launches(), counter.ext_launches())
    };

    assert_gkr_proof_eq_for_test(&gpu_proof, &fixture.expected_cpu_proof);
    assert_eq!(
        r0_launches, BLAKE2_MAIN_LAYERS,
        "exactly one VM-owned R0 launch per main layer"
    );
    assert!(
        ext_launches >= BLAKE2_MAIN_LAYERS,
        "every main layer must have run at least one continuation round; got {ext_launches}"
    );
    eprintln!(
        "[bwd-vm-parity] blake2: all {BLAKE2_MAIN_LAYERS} main layers on the VM \
         ({r0_launches} R0 + {ext_launches} Ext launches), proof bit-equal to the CPU reference"
    );
}

/// blake2 with BOTH VMs owning everything they have a path for — every forward
/// layer and every main layer's whole backward sumcheck, in one proof, against the
/// CPU reference.
///
/// This is the coverage claim for the second allowlisted circuit, and it is not
/// implied by the two single-arm gates: the arms share storage, and a forward layer
/// that publishes where a backward binder expects raw data would pass both alone
/// and fail here. Both poisons are on, so an arm that reads a destination it did
/// not write reads deliberate garbage rather than a plausible stale value.
#[test]
#[serial]
#[ignore]
fn run_blake2_both_vms_proof_parity_test() {
    use crate::prover::gkr::backward::vm::coords::AB_GKR_BWD_VM_COORDS_ENV;
    use crate::prover::gkr::backward::vm::production_bind::{
        count_bwd_vm_r0_launches, AB_GKR_BWD_VM_POISON_ACCUMULATOR_ENV,
        AB_GKR_BWD_VM_POISON_CASCADE_ENV,
    };
    use crate::prover::gkr::forward::path::AB_GKR_FWD_VM_LAYERS_ENV;
    use crate::prover::gkr::forward::vm::count_fwd_vm_s4_launches;
    use crate::prover::gkr::forward::vm::production_bind::AB_GKR_FWD_VM_POISON_DESTINATIONS_ENV;

    let fixture = prepare_blake2_with_compression_proof_fixture();
    let _fwd_poison = EnvGuard::set(AB_GKR_FWD_VM_POISON_DESTINATIONS_ENV, "1");
    let _poison = EnvGuard::set(AB_GKR_BWD_VM_POISON_ACCUMULATOR_ENV, "1");
    let _cascade_poison = EnvGuard::set(AB_GKR_BWD_VM_POISON_CASCADE_ENV, "1");

    let fwd_counter = count_fwd_vm_s4_launches();
    let bwd_counter = count_bwd_vm_r0_launches();

    let layers = (0..BLAKE2_MAIN_LAYERS)
        .map(|layer| layer.to_string())
        .collect::<Vec<_>>()
        .join(",");
    let coords = (0..BLAKE2_MAIN_LAYERS)
        .map(|layer| format!("{layer}:R0,{layer}:Ext"))
        .collect::<Vec<_>>()
        .join(",");

    let gpu_proof = {
        let _fwd = EnvGuard::set(AB_GKR_FWD_VM_LAYERS_ENV, &layers);
        let _bwd = EnvGuard::set(AB_GKR_BWD_VM_COORDS_ENV, &coords);
        let job = fixture.schedule_prove().unwrap();
        let (proof, _ms) = job.finish().unwrap();
        proof
    };

    assert_gkr_proof_eq_for_test(&gpu_proof, &fixture.expected_cpu_proof);
    let (fwd, r0, ext) = (
        fwd_counter.launches(),
        bwd_counter.launches(),
        bwd_counter.ext_launches(),
    );
    assert!(
        fwd > 0 && r0 > 0 && ext > 0,
        "both arms must have run; got fwd={fwd} r0={r0} ext={ext}"
    );
    eprintln!(
        "[both-vms-parity] blake2: {BLAKE2_MAIN_LAYERS} forward layers + \
         {BLAKE2_MAIN_LAYERS} backward main layers ({fwd} fwd + {r0} R0 + {ext} Ext launches), \
         proof bit-equal to the CPU reference"
    );
}

/// A/B the forward VM on every non-dimension-reducing add_sub layer: N interleaved pairs of whole proofs
/// in one process, VM-on against VM-off, reporting per-pair deltas plus the
/// median, min, max and both peak-memory figures.
///
/// Interleaved and order-alternated because the two arms share a device, an
/// allocator and a thermal envelope; running all of one arm then all of the
/// other would let drift masquerade as effect.
///
/// A timing number from an arm that produced a different proof is not a
/// number, so every pair asserts the two proofs are byte-equal. This uses the
/// profiling fixture (no CPU reference), which is exactly right here: the
/// question is whether the VM changes the proof, and the two GPU arms answer
/// that against each other. Parity against the CPU is
/// `run_add_sub_vm_layer0_proof_parity_test`.
#[test]
#[serial]
#[ignore]
fn run_add_sub_fwd_vm_all_layers_ab_test() {
    use crate::prover::gkr::forward::path::AB_GKR_FWD_VM_LAYERS_ENV;

    const PAIRS: usize = 20;
    /// Every non-dimension-reducing layer of add_sub.
    const FWD_VM_AB_LAYERS: &str = "0,1,2,3";

    let fixture = prepare_basic_unrolled_profiling_fixture();
    assert!(
        !crate::prover::gkr::forward::vm::production_bind::poison_destinations_enabled(),
        "the destination poison is ~36 full-length column writes charged to the VM arm alone; \
         leaving it on inverts this measurement"
    );

    // Warm up both arms before measuring: first-touch allocation, the
    // OnceLock'd VM program compile, and module load all land here.
    for layers in ["", FWD_VM_AB_LAYERS] {
        let _env = EnvGuard::set(AB_GKR_FWD_VM_LAYERS_ENV, layers);
        let t = fixture.schedule_transfers().unwrap();
        fixture.context.get_h2d_stream().synchronize().unwrap();
        let (proof, ms) = fixture.prove(t).unwrap().finish().unwrap();
        eprintln!("[fwd-vm-ab] warmup vm={layers:?}: {ms} ms");
        drop(proof);
    }

    let mut run = |layers: &str| {
        let _env = EnvGuard::set(AB_GKR_FWD_VM_LAYERS_ENV, layers);
        let t = fixture.schedule_transfers().unwrap();
        fixture.context.get_h2d_stream().synchronize().unwrap();
        fixture.context.reset_used_mem_peak();
        let (proof, ms) = fixture.prove(t).unwrap().finish().unwrap();
        (proof, ms, fixture.context.get_used_mem_peak())
    };

    let mut deltas = Vec::with_capacity(PAIRS);
    let mut on_peak = 0usize;
    let mut off_peak = 0usize;
    eprintln!("[fwd-vm-ab] pair  vm_on_ms  vm_off_ms  delta_ms");
    for pair in 0..PAIRS {
        // Alternate which arm goes first so a systematic first-slot cost
        // (allocator state, clocks) cannot be attributed to one arm.
        let (on, off) = if pair % 2 == 0 {
            let on = run(FWD_VM_AB_LAYERS);
            let off = run("");
            (on, off)
        } else {
            let off = run("");
            let on = run(FWD_VM_AB_LAYERS);
            (on, off)
        };
        // Field-by-field: GKRProof has no PartialEq. A timing number from an
        // arm that produced a different proof is not a number.
        assert_gkr_proof_eq_for_test(&on.0, &off.0);
        let delta = on.1 - off.1;
        eprintln!(
            "[fwd-vm-ab] {pair:>4}  {:>8.3}  {:>9.3}  {:>8.3}",
            on.1, off.1, delta
        );
        deltas.push(delta);
        on_peak = on_peak.max(on.2);
        off_peak = off_peak.max(off.2);
    }

    deltas.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = deltas[deltas.len() / 2];
    eprintln!(
        "[fwd-vm-ab] delta_ms (vm_on - vm_off) over {PAIRS} pairs: median {median:.3}, \
         min {:.3}, max {:.3}",
        deltas[0],
        deltas[deltas.len() - 1],
    );
    eprintln!(
        "[fwd-vm-ab] peak device memory: vm_on {:.4} GiB, vm_off {:.4} GiB, delta {} B",
        on_peak as f64 / (1u64 << 30) as f64,
        off_peak as f64 / (1u64 << 30) as f64,
        on_peak as i64 - off_peak as i64,
    );
}

/// A/B everything the DAG-derived path owns: the forward VM on all four
/// non-dimension-reducing layers plus the backward VM on every main layer's
/// round 0 and continuation rounds.
///
/// This is the e2e number for add_sub. It also settled additivity — forward
/// −2.418 alone plus backward L0 −3.710 alone came to −6.067 measured against
/// −6.128 predicted, so the two passes compose.
///
/// The backward arm covers all four main layers because they all pay now. They
/// did not before `BWD_SEG_OUTPUT_PARTIALS`: the VM used to hand the tail
/// full-length per-row contributions, and the ~0.5 ms of extra DRAM traffic and
/// launches that cost is INDEPENDENT of layer size (every main layer folds the
/// same 24 rounds over the same rows), so it swamped the smaller layers. Per
/// `run_add_sub_bwd_vm_per_main_layer_ab_test`, moving the row-axis reduction
/// into the kernel moved every layer by about that much: L0 −3.741 to −4.212,
/// L1 +0.060 to −0.600, L2 +0.536 to −0.024, L3 +0.520 to +0.016.
///
/// The only GKR work left on the incumbent is the backward dimension-reducing
/// sumcheck (22.3 ms GPU-projected, ~11% of the proof), permanently.
#[test]
#[serial]
#[ignore]
fn run_add_sub_both_vms_ab_test() {
    use crate::prover::gkr::backward::vm::coords::AB_GKR_BWD_VM_COORDS_ENV;
    use crate::prover::gkr::forward::path::AB_GKR_FWD_VM_LAYERS_ENV;

    const PAIRS: usize = 20;
    /// Every non-dimension-reducing forward layer.
    const FWD_VM_AB_LAYERS: &str = "0,1,2,3";
    /// Every main layer's whole sumcheck, both regimes.
    const BWD_VM_AB_COORDS: &str = "0:R0,0:Ext,1:R0,1:Ext,2:R0,2:Ext,3:R0,3:Ext";

    let fixture = prepare_basic_unrolled_profiling_fixture();
    assert!(
        !crate::prover::gkr::forward::vm::production_bind::poison_destinations_enabled(),
        "the destination poison is charged to the VM arm alone; leaving it on inverts this \
         measurement"
    );
    assert!(
        !crate::prover::gkr::backward::vm::production_bind::poison_accumulator_enabled(),
        "the accumulator poison is charged to the VM arm alone; leaving it on inverts this \
         measurement"
    );
    assert!(
        !crate::prover::gkr::backward::vm::production_bind::cascade_poison_enabled(),
        "the cascade poison fills every fold backing on both arms; leaving it on adds noise \
         this measurement cannot absorb"
    );

    // Warm up both arms: first-touch allocation, both OnceLock'd compiles
    // (forward program and backward coordinates), and module load.
    for (layers, coords) in [("", ""), (FWD_VM_AB_LAYERS, BWD_VM_AB_COORDS)] {
        let _fwd = EnvGuard::set(AB_GKR_FWD_VM_LAYERS_ENV, layers);
        let _bwd = EnvGuard::set(AB_GKR_BWD_VM_COORDS_ENV, coords);
        let t = fixture.schedule_transfers().unwrap();
        fixture.context.get_h2d_stream().synchronize().unwrap();
        let (proof, ms) = fixture.prove(t).unwrap().finish().unwrap();
        eprintln!("[both-vms-ab] warmup fwd={layers:?} bwd={coords:?}: {ms} ms");
        drop(proof);
    }

    let mut run = |layers: &str, coords: &str| {
        let _fwd = EnvGuard::set(AB_GKR_FWD_VM_LAYERS_ENV, layers);
        let _bwd = EnvGuard::set(AB_GKR_BWD_VM_COORDS_ENV, coords);
        let t = fixture.schedule_transfers().unwrap();
        fixture.context.get_h2d_stream().synchronize().unwrap();
        fixture.context.reset_used_mem_peak();
        let (proof, ms) = fixture.prove(t).unwrap().finish().unwrap();
        (proof, ms, fixture.context.get_used_mem_peak())
    };

    let mut deltas = Vec::with_capacity(PAIRS);
    let mut on_peak = 0usize;
    let mut off_peak = 0usize;
    eprintln!("[both-vms-ab] pair  vm_on_ms  vm_off_ms  delta_ms");
    for pair in 0..PAIRS {
        let (on, off) = if pair % 2 == 0 {
            let on = run(FWD_VM_AB_LAYERS, BWD_VM_AB_COORDS);
            let off = run("", "");
            (on, off)
        } else {
            let off = run("", "");
            let on = run(FWD_VM_AB_LAYERS, BWD_VM_AB_COORDS);
            (on, off)
        };
        assert_gkr_proof_eq_for_test(&on.0, &off.0);
        let delta = on.1 - off.1;
        eprintln!(
            "[both-vms-ab] {pair:>4}  {:>8.3}  {:>9.3}  {:>8.3}",
            on.1, off.1, delta
        );
        deltas.push(delta);
        on_peak = on_peak.max(on.2);
        off_peak = off_peak.max(off.2);
    }

    deltas.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = deltas[deltas.len() / 2];
    eprintln!(
        "[both-vms-ab] delta_ms (both on - both off) over {PAIRS} pairs: median {median:.3}, \
         min {:.3}, max {:.3}",
        deltas[0],
        deltas[deltas.len() - 1],
    );
    eprintln!(
        "[both-vms-ab] reference points: forward alone -2.418, backward main layers -4.820 \
         (per-layer sum), so the additive prediction is about -7.24"
    );
    eprintln!(
        "[both-vms-ab] peak device memory: on {:.4} GiB, off {:.4} GiB, delta {} B",
        on_peak as f64 / (1u64 << 30) as f64,
        off_peak as f64 / (1u64 << 30) as f64,
        on_peak as i64 - off_peak as i64,
    );
}

/// A/B the backward VM ONE MAIN LAYER AT A TIME, so each layer's contribution is
/// its own number instead of a share of a lump.
///
/// Needed because the lumped measurement inverted: the whole main-layer sumcheck
/// on the VM is −4.871 ms, but forward + backward L0 alone was −6.067, so layers
/// 1..=3 together cost about +1.2 ms rather than the −3.9 their GPU-projected
/// 35.0 ms would suggest at L0's rate. The mechanism is visible in the R0 slice's
/// own result (+0.196 ms): the incumbent runs the FUSED warp-partial path, the VM
/// pays an unfused reduction + round-update tail, and that fixed cost is
/// amortized by L0's big rounds but not by the smaller layers'.
///
/// A cutover decision is per layer, so the evidence has to be per layer. The
/// forward arm stays OFF throughout — this isolates the backward layers.
#[test]
#[serial]
#[ignore]
fn run_add_sub_bwd_vm_per_main_layer_ab_test() {
    use crate::prover::gkr::backward::vm::coords::AB_GKR_BWD_VM_COORDS_ENV;

    const PAIRS: usize = 20;

    let fixture = prepare_basic_unrolled_profiling_fixture();
    assert!(
        !crate::prover::gkr::backward::vm::production_bind::poison_accumulator_enabled(),
        "the accumulator poison is charged to the VM arm alone; leaving it on inverts this"
    );
    assert!(
        !crate::prover::gkr::backward::vm::production_bind::cascade_poison_enabled(),
        "the cascade poison adds noise this measurement cannot absorb"
    );

    let mut run = |coords: &str| {
        let _env = EnvGuard::set(AB_GKR_BWD_VM_COORDS_ENV, coords);
        let t = fixture.schedule_transfers().unwrap();
        fixture.context.get_h2d_stream().synchronize().unwrap();
        let (proof, ms) = fixture.prove(t).unwrap().finish().unwrap();
        (proof, ms)
    };

    // One warmup per arm: the per-layer coordinate compiles are OnceLock'd, and
    // a first-call compile inside a measured arm would be charged to the VM.
    let all_coords = (0..ADD_SUB_MAIN_LAYERS)
        .map(|layer| format!("{layer}:R0,{layer}:Ext"))
        .collect::<Vec<_>>()
        .join(",");
    for coords in ["", all_coords.as_str()] {
        let (proof, ms) = run(coords);
        eprintln!("[bwd-vm-layer-ab] warmup bwd={coords:?}: {ms} ms");
        drop(proof);
    }

    eprintln!("[bwd-vm-layer-ab] layer  median_ms  min_ms  max_ms  pairs_winning");
    let mut medians = Vec::with_capacity(ADD_SUB_MAIN_LAYERS);
    for layer in 0..ADD_SUB_MAIN_LAYERS {
        let coords = format!("{layer}:R0,{layer}:Ext");
        let mut deltas = Vec::with_capacity(PAIRS);
        for pair in 0..PAIRS {
            let (on, off) = if pair % 2 == 0 {
                let on = run(&coords);
                let off = run("");
                (on, off)
            } else {
                let off = run("");
                let on = run(&coords);
                (on, off)
            };
            assert_gkr_proof_eq_for_test(&on.0, &off.0);
            deltas.push(on.1 - off.1);
        }
        deltas.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let median = deltas[deltas.len() / 2];
        let winning = deltas.iter().filter(|d| **d < 0.0).count();
        eprintln!(
            "[bwd-vm-layer-ab] {layer:>5}  {median:>9.3}  {:>6.3}  {:>6.3}  {winning:>13}",
            deltas[0],
            deltas[deltas.len() - 1],
        );
        medians.push(median);
    }

    let sum: f32 = medians.iter().sum();
    eprintln!(
        "[bwd-vm-layer-ab] per-layer medians sum to {sum:.3} ms; the whole-sumcheck lump measured \
         -4.871 with the forward arm also on (-2.418 alone)"
    );
}

/// A/B the backward VM on add_sub L0 R0: N interleaved order-alternated pairs
/// of whole proofs in one process, VM-on against VM-off, per-pair byte-equal.
///
/// Sizing caveat, stated up front so a null result reads correctly: L0's
/// round 0 is ~5.8 ms of a ~204 ms proof (nsys, 2026-07-30) — under 3% — and
/// the arms differ by more than the eval kernel (the incumbent runs the FUSED
/// warp-partial round 0; the VM runs the segmented kernel plus the unfused
/// reduction + round-update tail). A sub-millisecond median here is expected;
/// the cutover-relevant claim this test can settle is "no regression at the
/// whole-proof scale", not a precise per-kernel ratio (that number is the
/// bench's calibrated 0.9588 against `main_round0_constant`).
#[test]
#[serial]
#[ignore]
fn run_add_sub_bwd_vm_l0_r0_ab_test() {
    use crate::prover::gkr::backward::vm::coords::AB_GKR_BWD_VM_COORDS_ENV;

    const PAIRS: usize = 20;
    const BWD_VM_AB_COORDS: &str = "0:R0";

    let fixture = prepare_basic_unrolled_profiling_fixture();
    assert!(
        !crate::prover::gkr::backward::vm::production_bind::poison_accumulator_enabled(),
        "the accumulator poison is a full-length device write charged to the VM arm alone; \
         leaving it on inverts this measurement"
    );

    // Warm up both arms before measuring: first-touch allocation, the
    // OnceLock'd coordinate compile, and module load all land here.
    for coords in ["", BWD_VM_AB_COORDS] {
        let _env = EnvGuard::set(AB_GKR_BWD_VM_COORDS_ENV, coords);
        let t = fixture.schedule_transfers().unwrap();
        fixture.context.get_h2d_stream().synchronize().unwrap();
        let (proof, ms) = fixture.prove(t).unwrap().finish().unwrap();
        eprintln!("[bwd-vm-ab] warmup vm={coords:?}: {ms} ms");
        drop(proof);
    }

    let mut run = |coords: &str| {
        let _env = EnvGuard::set(AB_GKR_BWD_VM_COORDS_ENV, coords);
        let t = fixture.schedule_transfers().unwrap();
        fixture.context.get_h2d_stream().synchronize().unwrap();
        fixture.context.reset_used_mem_peak();
        let (proof, ms) = fixture.prove(t).unwrap().finish().unwrap();
        (proof, ms, fixture.context.get_used_mem_peak())
    };

    let mut deltas = Vec::with_capacity(PAIRS);
    let mut on_peak = 0usize;
    let mut off_peak = 0usize;
    eprintln!("[bwd-vm-ab] pair  vm_on_ms  vm_off_ms  delta_ms");
    for pair in 0..PAIRS {
        // Alternate which arm goes first so a systematic first-slot cost
        // (allocator state, clocks) cannot be attributed to one arm.
        let (on, off) = if pair % 2 == 0 {
            let on = run(BWD_VM_AB_COORDS);
            let off = run("");
            (on, off)
        } else {
            let off = run("");
            let on = run(BWD_VM_AB_COORDS);
            (on, off)
        };
        // A timing number from an arm that produced a different proof is not
        // a number.
        assert_gkr_proof_eq_for_test(&on.0, &off.0);
        let delta = on.1 - off.1;
        eprintln!(
            "[bwd-vm-ab] {pair:>4}  {:>8.3}  {:>9.3}  {:>8.3}",
            on.1, off.1, delta
        );
        deltas.push(delta);
        on_peak = on_peak.max(on.2);
        off_peak = off_peak.max(off.2);
    }

    deltas.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = deltas[deltas.len() / 2];
    eprintln!(
        "[bwd-vm-ab] delta_ms (vm_on - vm_off) over {PAIRS} pairs: median {median:.3}, \
         min {:.3}, max {:.3}",
        deltas[0],
        deltas[deltas.len() - 1],
    );
    eprintln!(
        "[bwd-vm-ab] peak device memory: vm_on {:.4} GiB, vm_off {:.4} GiB, delta {} B",
        on_peak as f64 / (1u64 << 30) as f64,
        off_peak as f64 / (1u64 << 30) as f64,
        on_peak as i64 - off_peak as i64,
    );
}

/// A/B the backward VM on the WHOLE of add_sub L0 — round 0 plus all 23
/// continuation rounds: N interleaved order-alternated pairs of whole proofs in
/// one process, VM-on against VM-off, per-pair byte-equal.
///
/// Unlike the R0-only A/B, this arm is not a rounding error: L0's backward
/// sumcheck is the bulk of a backward pass that is itself ~44% of the ~204 ms
/// proof, so the whole-proof instrument resolves the question it is asked. The
/// arms still differ by more than the eval kernels — the incumbent runs the
/// FUSED warp-partial path on every continuation round, the VM runs the
/// segmented kernel plus the unfused reduction + round-update tail — so the
/// delta is the cutover's true cost, not a per-kernel ratio.
#[test]
#[serial]
#[ignore]
fn run_add_sub_bwd_vm_l0_full_ab_test() {
    use crate::prover::gkr::backward::vm::coords::AB_GKR_BWD_VM_COORDS_ENV;

    const PAIRS: usize = 20;
    /// The whole layer: round 0 and every continuation round.
    const BWD_VM_AB_COORDS: &str = "0:R0,0:Ext";

    let fixture = prepare_basic_unrolled_profiling_fixture();
    assert!(
        !crate::prover::gkr::backward::vm::production_bind::poison_accumulator_enabled(),
        "the accumulator poison is a full-length device write per VM round charged to the VM arm \
         alone; leaving it on inverts this measurement"
    );
    assert!(
        !crate::prover::gkr::backward::vm::production_bind::cascade_poison_enabled(),
        "the cascade poison fills every fold backing on both arms' layer prepares; leaving it on \
         adds noise this measurement cannot absorb"
    );

    // Warm up both arms before measuring: first-touch allocation, the
    // OnceLock'd coordinate compile, and module load all land here.
    for coords in ["", BWD_VM_AB_COORDS] {
        let _env = EnvGuard::set(AB_GKR_BWD_VM_COORDS_ENV, coords);
        let t = fixture.schedule_transfers().unwrap();
        fixture.context.get_h2d_stream().synchronize().unwrap();
        let (proof, ms) = fixture.prove(t).unwrap().finish().unwrap();
        eprintln!("[bwd-vm-full-ab] warmup vm={coords:?}: {ms} ms");
        drop(proof);
    }

    let mut run = |coords: &str| {
        let _env = EnvGuard::set(AB_GKR_BWD_VM_COORDS_ENV, coords);
        let t = fixture.schedule_transfers().unwrap();
        fixture.context.get_h2d_stream().synchronize().unwrap();
        fixture.context.reset_used_mem_peak();
        let (proof, ms) = fixture.prove(t).unwrap().finish().unwrap();
        (proof, ms, fixture.context.get_used_mem_peak())
    };

    let mut deltas = Vec::with_capacity(PAIRS);
    let mut on_peak = 0usize;
    let mut off_peak = 0usize;
    eprintln!("[bwd-vm-full-ab] pair  vm_on_ms  vm_off_ms  delta_ms");
    for pair in 0..PAIRS {
        // Alternate which arm goes first so a systematic first-slot cost
        // (allocator state, clocks) cannot be attributed to one arm.
        let (on, off) = if pair % 2 == 0 {
            let on = run(BWD_VM_AB_COORDS);
            let off = run("");
            (on, off)
        } else {
            let off = run("");
            let on = run(BWD_VM_AB_COORDS);
            (on, off)
        };
        // A timing number from an arm that produced a different proof is not
        // a number.
        assert_gkr_proof_eq_for_test(&on.0, &off.0);
        let delta = on.1 - off.1;
        eprintln!(
            "[bwd-vm-full-ab] {pair:>4}  {:>8.3}  {:>9.3}  {:>8.3}",
            on.1, off.1, delta
        );
        deltas.push(delta);
        on_peak = on_peak.max(on.2);
        off_peak = off_peak.max(off.2);
    }

    deltas.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = deltas[deltas.len() / 2];
    eprintln!(
        "[bwd-vm-full-ab] delta_ms (vm_on - vm_off) over {PAIRS} pairs: median {median:.3}, \
         min {:.3}, max {:.3}",
        deltas[0],
        deltas[deltas.len() - 1],
    );
    eprintln!(
        "[bwd-vm-full-ab] peak device memory: vm_on {:.4} GiB, vm_off {:.4} GiB, delta {} B",
        on_peak as f64 / (1u64 << 30) as f64,
        off_peak as f64 / (1u64 << 30) as f64,
        on_peak as i64 - off_peak as i64,
    );
}
