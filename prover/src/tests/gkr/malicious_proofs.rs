use super::orchestration::common::{
    hardcoded_external_challenges, run_vm_and_capture, ProgramConfig,
};
use super::orchestration::per_family::{
    build_mem_family_full_trace, build_nonmem_family_full_trace, prove_built_family_trace,
};
use super::*;
use crate::definitions::SecurityLevel;
use crate::gkr::prover::GKRProof;
use crate::merkle_trees::DefaultTreeConstructor;
use ::field::baby_bear::base::BabyBearField;
use ::field::baby_bear::ext4::BabyBearExt4;
use cs::gkr_circuits::opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization;
use cs::gkr_circuits::process_binary_into_separate_tables_ext;
use cs::tables::TableDriver;
use field::Field;
use field::PrimeField;
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
use riscv_transpiler::vm::{Counters, DelegationsAndFamiliesCounters};
use std::alloc::Global;
use worker::Worker;

const TRACE_LEN_LOG2: usize = 24;
const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;

const MULTIPLICITY_COL_RANGE_CHECK_16: usize = 26;
const MULTIPLICITY_COL_TIMESTAMP: usize = 27;
const MULTIPLICITY_COL_GENERIC: usize = 28;

/// Generate a jump_branch_slt proof with a witness mutation applied before proving.
fn generate_proof(
    mutate: impl FnOnce(&mut GKRFullWitnessTrace<BabyBearField, Global, Global>),
) -> GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
    type CountersT = DelegationsAndFamiliesCounters;
    const CIRCUIT_TYPE: u8 = JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX;

    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let worker = Worker::new_with_num_threads(8);

    let config = ProgramConfig::keccak_f1600();
    let vm = run_vm_and_capture::<CountersT, FullUnsignedMachineDecoderConfig>(&config, &worker);

    let preprocessing_data = process_binary_into_separate_tables_ext::<
        BabyBearField,
        FullUnsignedMachineDecoderConfig,
        true,
        Global,
    >(
        &vm.text_section,
        &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
        1 << 20,
        &[
            NON_DETERMINISM_CSR as u16,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            KECCAK_SPECIAL5_CSR_REGISTER as u16,
        ],
    );
    let decoder_table_data = &preprocessing_data[&CIRCUIT_TYPE];

    let circuit: GKRCircuitArtifact<BabyBearField> = deserialize_from_file(
        &super::orchestration::per_family::circuit_path("jump_branch_slt"),
    );

    let mut table_driver = TableDriver::<BabyBearField>::new();
    cs::gkr_circuits::jump_branch_slt_family::jump_branch_slt_table_driver_fn(&mut table_driver);

    let num_calls = vm.counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>();
    assert!(
        num_calls > 0,
        "no jump_branch_slt instructions found in trace"
    );

    let mut full_trace = build_nonmem_family_full_trace::<CIRCUIT_TYPE, _>(
        &vm.snapshotter,
        &vm.tape,
        &vm.expected_final_state(),
        vm.cycles_bound,
        num_calls,
        &circuit,
        &table_driver,
        decoder_table_data,
        jump_branch_slt::witness_eval_fn,
        NUM_CYCLES_PER_CHUNK,
        false,
        &worker,
    )
    .full_trace;

    println!("Applying witness mutation");
    mutate(&mut full_trace);

    println!("Proving with corrupted witness");
    prove_built_family_trace(
        &circuit,
        &table_driver,
        decoder_table_data,
        full_trace,
        trace_len,
        &hardcoded_external_challenges(),
        SecurityLevel::Sec80,
        &worker,
    )
}

#[test]
#[ignore]
fn generate_malicious_proofs() {
    let proof = generate_proof(|trace| {
        let col = MULTIPLICITY_COL_RANGE_CHECK_16;
        let before = trace.column_major_witness_trace[col][0];
        trace.column_major_witness_trace[col][0].add_assign(&BabyBearField::ONE);
        let after = trace.column_major_witness_trace[col][0];
        println!(
            "range_check_16 multiplicity col={} row=0: {:?} -> {:?}",
            col, before, after
        );
    });
    serialize_to_file(&proof, "test_proofs/malicious_lookup_16bits_gkr_proof.json");

    let proof = generate_proof(|trace| {
        let col = MULTIPLICITY_COL_TIMESTAMP;
        let before = trace.column_major_witness_trace[col][0];
        trace.column_major_witness_trace[col][0].add_assign(&BabyBearField::ONE);
        let after = trace.column_major_witness_trace[col][0];
        println!(
            "timestamp multiplicity col={} row=0: {:?} -> {:?}",
            col, before, after
        );
    });
    serialize_to_file(
        &proof,
        "test_proofs/malicious_lookup_timestamps_gkr_proof.json",
    );

    // Generic lookup via multiplicity corruption
    let proof = generate_proof(|trace| {
        let col = MULTIPLICITY_COL_GENERIC;
        let before = trace.column_major_witness_trace[col][0];
        trace.column_major_witness_trace[col][0].add_assign(&BabyBearField::ONE);
        let after = trace.column_major_witness_trace[col][0];
        println!(
            "generic multiplicity col={} row=0: {:?} -> {:?}",
            col, before, after
        );
    });
    serialize_to_file(
        &proof,
        "test_proofs/malicious_lookup_generic_gkr_proof.json",
    );

    // --- Constraint / permutation violations ---

    let proof = generate_proof(|trace| {
        trace.column_major_witness_trace[0][0].add_assign(&BabyBearField::ONE);
    });
    serialize_to_file(&proof, "test_proofs/malicious_witness_value_gkr_proof.json");

    let proof = generate_proof(|trace| {
        trace.column_major_memory_trace[0][0].add_assign(&BabyBearField::ONE);
    });
    serialize_to_file(&proof, "test_proofs/malicious_memory_value_gkr_proof.json");
}

/// Requires the `gkr_test_forge` feature: the mid-prove cache perturbation runs through the
/// `test_forge` hook, whose call sites are compiled out without the feature (so a
/// feature-off run would silently emit honest proofs). Gated so it cannot run misconfigured.
///
/// Generates all three jump_branch_slt fixtures in one invocation (no pre-prove witness
/// mutation — the divergence is injected at the cache-materialization point):
///
/// * control             -> honest, ACCEPTED by the verifier.
/// * memtuple cacheforge  -> MemoryTuple cache poly perturbed on active row 0; base columns
///   honest (identical commitments). REJECTED with GkrPermutationCacheRelationFailed.
/// * lookup cacheforge (negative control) -> BOUND SingleColumnLookup cache perturbed;
///   REJECTED with GkrSingleLookupCacheRelationFailed
///
/// Row 0 of the jump_branch_slt test trace is active (execute=1). Run WITHOUT gkr_self_checks
/// (release): the debug cache-relation self-check would catch the divergence at prove time.
#[cfg(feature = "gkr_test_forge")]
#[test]
#[ignore]
fn generate_memtuple_regression_proofs() {
    use crate::gkr::prover::test_forge::{self, Forge, ForgeSite};
    const FORGE_ROW: usize = 0;

    test_forge::clear();
    let control = generate_proof(|_trace| {});
    serialize_to_file(
        &control,
        "test_proofs/malicious_memtuple_control_gkr_proof.json",
    );

    test_forge::clear();
    test_forge::register(Forge {
        site: ForgeSite::MemTupleCache,
        row: FORGE_ROW,
    });
    let cacheforge = generate_proof(|_trace| {});
    serialize_to_file(
        &cacheforge,
        "test_proofs/malicious_memtuple_cacheforge_gkr_proof.json",
    );

    test_forge::clear();
    test_forge::register(Forge {
        site: ForgeSite::SingleColumnLookupCache,
        row: FORGE_ROW,
    });
    let lookupforge = generate_proof(|_trace| {});
    serialize_to_file(
        &lookupforge,
        "test_proofs/malicious_lookup_cacheforge_gkr_proof.json",
    );

    test_forge::clear();
}

/// Generate a mem_subword_only proof with a witness mutation applied before proving.
fn generate_subword_proof(
    mutate: impl FnOnce(&mut GKRFullWitnessTrace<BabyBearField, Global, Global>),
) -> GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
    type CountersT = DelegationsAndFamiliesCounters;
    const CIRCUIT_TYPE: u8 = LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX;

    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let worker = Worker::new_with_num_threads(8);

    let config = ProgramConfig::keccak_f1600();
    let vm = run_vm_and_capture::<CountersT, FullUnsignedMachineDecoderConfig>(&config, &worker);

    let preprocessing_data = process_binary_into_separate_tables_ext::<
        BabyBearField,
        FullUnsignedMachineDecoderConfig,
        true,
        Global,
    >(
        &vm.text_section,
        &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
        1 << 20,
        &[
            NON_DETERMINISM_CSR as u16,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            KECCAK_SPECIAL5_CSR_REGISTER as u16,
        ],
    );
    let decoder_table_data = &preprocessing_data[&CIRCUIT_TYPE];

    let circuit: GKRCircuitArtifact<BabyBearField> = deserialize_from_file(
        &super::orchestration::per_family::circuit_path("mem_subword_only"),
    );

    let mut table_driver = TableDriver::<BabyBearField>::new();
    cs::gkr_circuits::mem_subword_only::mem_subword_only_table_driver_fn(&mut table_driver);
    let extra_tables = cs::gkr_circuits::mem_subword_only::create_mem_subword_only_special_tables::<
        _,
        { common_constants::ROM_SECOND_WORD_BITS },
    >(&vm.binary);
    for (table_type, table) in extra_tables {
        table_driver.add_table_with_content(table_type, table);
    }

    let num_calls = vm.counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>();
    assert!(
        num_calls > 0,
        "no mem_subword_only instructions found in trace"
    );

    let mut full_trace = build_mem_family_full_trace::<CIRCUIT_TYPE, _>(
        &vm.snapshotter,
        &vm.tape,
        &vm.expected_final_state(),
        vm.cycles_bound,
        num_calls,
        &circuit,
        &table_driver,
        decoder_table_data,
        mem_subword_only::witness_eval_fn,
        NUM_CYCLES_PER_CHUNK,
        false,
        &worker,
    )
    .full_trace;

    println!("Applying witness mutation");
    mutate(&mut full_trace);

    println!("Proving with corrupted witness");
    prove_built_family_trace(
        &circuit,
        &table_driver,
        decoder_table_data,
        full_trace,
        trace_len,
        &hardcoded_external_challenges(),
        SecurityLevel::Sec80,
        &worker,
    )
}

/// subword-alias regression fixture.
///
/// Locates an ACTIVE byte-load row (execute=1, is_store=0, is_byte=1, byte offset >= 1)
/// and trades the byte offset against the word-cell address:
///   cleanaddr_lo' = cleanaddr_lo + d ;  (b0' + 2*b1') = (b0 + 2*b1) - d
/// keeping the address equation rs1_lo+imm_lo == cleanaddr_lo + b0 + 2*b1 + of_lo*2^16
/// satisfied (so every PRE-FIX constraint still passes) while aiming the load at a
/// different physical word cell. Post-fix, the new alignment constraint
/// cleanaddr_lo == 4*(cleanaddr_lo>>2) rejects it (cleanaddr_lo' is not word-aligned).
///
/// Column map (mem_subword_only layout, LOAD row so cleanaddr uses memwrite_addr):
///   execute      = memory col 20
///   is_store     = memory col 9   (WRITE_BIT of circuit_family_mask_bits)
///   is_byte      = witness col 4  (BYTE_BIT)
///   cleanaddr_lo = memory col 16  (memwrite_addr[0])
///   is_bit0      = witness col 6
///   is_bit1      = witness col 7
///
/// Run WITHOUT gkr_self_checks (release): the debug constraint self-check would catch
/// the divergence at prove time. This is a pre-prove witness-trace mutation, so no
/// in-prover hook (and hence no `gkr_test_forge` feature) is required.
#[test]
#[ignore]
fn generate_subword_regression_proof() {
    const EXECUTE: usize = 20;
    const IS_STORE: usize = 9;
    const IS_BYTE_W: usize = 4;
    const CLEANADDR_LO_M: usize = 16;
    const B0_W: usize = 6;
    const B1_W: usize = 7;

    let proof = generate_subword_proof(|trace| {
        let n = trace.column_major_memory_trace[EXECUTE].len();
        let mut target = None;
        for row in 0..n {
            let execute = trace.column_major_memory_trace[EXECUTE][row].as_u32_reduced();
            let is_store = trace.column_major_memory_trace[IS_STORE][row].as_u32_reduced();
            let is_byte = trace.column_major_witness_trace[IS_BYTE_W][row].as_u32_reduced();
            let b0 = trace.column_major_witness_trace[B0_W][row].as_u32_reduced();
            let b1 = trace.column_major_witness_trace[B1_W][row].as_u32_reduced();
            let offset = b0 + 2 * b1;
            if execute == 1 && is_store == 0 && is_byte == 1 && offset >= 1 {
                target = Some((row, b0, b1, offset));
                break;
            }
        }
        let (row, b0, b1, offset) = target.expect(
            "F1 forge: no active byte-load row (execute=1, is_store=0, is_byte=1, offset>=1) in trace",
        );
        // Shift by d=1: move one unit of offset into the cell address.
        let d: u32 = 1;
        let new_offset = offset - d;
        let new_b0 = new_offset & 1;
        let new_b1 = (new_offset >> 1) & 1;
        let old_addr = trace.column_major_memory_trace[CLEANADDR_LO_M][row].as_u32_reduced();
        trace.column_major_memory_trace[CLEANADDR_LO_M][row]
            .add_assign(&BabyBearField::from_u32_with_reduction(d));
        trace.column_major_witness_trace[B0_W][row] =
            BabyBearField::from_u32_with_reduction(new_b0);
        trace.column_major_witness_trace[B1_W][row] =
            BabyBearField::from_u32_with_reduction(new_b1);
        println!(
            "forge row {}: cleanaddr_lo {} -> {} (not word-aligned), (b0,b1) ({},{}) -> ({},{}); address equation preserved",
            row, old_addr, old_addr + d, b0, b1, new_b0, new_b1
        );
    });
    serialize_to_file(&proof, "test_proofs/malicious_subword_alias_gkr_proof.json");
}
