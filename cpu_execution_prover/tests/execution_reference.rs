#![feature(allocator_api)]
//! The CPU backend against the legacy CPU prover, and against its own cache.
//!
//! First, a full execution driven through the shared orchestrator must agree
//! with the unchanged legacy entry point, which is called only from this file
//! and is never adjusted to agree with us; both legs run the same ISA, RAM and
//! cycle bound, because a comparison across differing configurations can
//! distinguish nothing. Second, a combined commit-and-prove must reuse the
//! traces its commit pass produced rather than simulating twice, asserted on
//! exact counts because a cache test that cannot tell a hit from a
//! re-simulation proves nothing.
//!
//! Production circuit dimensions make these expensive, so they are ignored by
//! default and selected explicitly.

use cpu_execution_prover::{CpuExecutionProver, CpuExecutionProverConfiguration};
use execution_prover::{ExecutionKind, MachineType};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use std::collections::{BTreeMap, BTreeSet};

/// Mirrors the legacy reference's own parameters, so both legs bound the run
/// identically rather than each taking its own default.
const CYCLES_BOUND: usize = 1 << 31;
/// `JitRunnerRam::Medium`, which is what the CPU defaults select.
const RAM_BOUND: usize = 1 << 30;

/// A binary that actually calls a delegation, so the comparison covers a
/// delegation proof rather than only the RISC-V families.
fn delegating_fixture() -> (Vec<u32>, Vec<u32>) {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    let (_, binary) = setups::read_and_pad_binary(
        &root.join("examples/hashed_fibonacci/app_blake2_with_compression.bin"),
    );
    let (_, text) = setups::read_and_pad_binary(
        &root.join("examples/hashed_fibonacci/app_blake2_with_compression.text"),
    );
    (binary, text)
}

type Proof = prover::gkr::prover::GKRProof<
    field::baby_bear::base::BabyBearField,
    field::baby_bear::ext4::BabyBearExt4,
    prover::merkle_trees::DefaultTreeConstructor,
>;

/// The external challenges carried by whichever proof the program has; both
/// legs derive them from the same transcript, so they must agree.
fn first_challenges(
    proof: &full_statement_verifier::program_proof::ProgramProof,
) -> prover::definitions::GKRExternalChallenges<
    field::baby_bear::base::BabyBearField,
    field::baby_bear::ext4::BabyBearExt4,
> {
    proof
        .riscv_proofs
        .values()
        .chain(proof.delegation_proofs.values())
        .flatten()
        .next()
        .expect("a program proof carries at least one circuit proof")
        .external_challenges
}

fn assert_memory_cap_and_bytes(
    mine: &Proof,
    legacy: &Proof,
    circuit: &cs::gkr_compiler::GKRCircuitArtifact<field::baby_bear::base::BabyBearField>,
    label: &str,
) {
    assert_eq!(
        mine.whir_proof.memory_commitment.commitment.cap.cap,
        legacy.whir_proof.memory_commitment.commitment.cap.cap,
        "memory cap of {label}"
    );
    assert_eq!(
        verifier_common::gkr::flatten::flatten_gkr_proof_for_nds(mine, circuit),
        verifier_common::gkr::flatten::flatten_gkr_proof_for_nds(legacy, circuit),
        "flattened proof of {label}"
    );
}

fn non_determinism() -> QuasiUARTSource {
    QuasiUARTSource::new_with_reads(vec![100, 5])
}

fn prover(configuration: CpuExecutionProverConfiguration) -> CpuExecutionProver {
    CpuExecutionProver::with_configuration(configuration)
        .expect("configuration must be valid for the CPU backend")
}

fn registered(prover: &mut CpuExecutionProver) -> execution_prover::BinaryHandle {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    let (_, binary) = setups::read_and_pad_binary(&root.join("examples/hashed_fibonacci/app.bin"));
    let (_, text) = setups::read_and_pad_binary(&root.join("examples/hashed_fibonacci/app.text"));
    prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        binary,
        text,
        None,
    )
}

/// The all-cached case: at the shipping default the quota holds this fixture
/// whole (~35 blocks), so the prove pass is served entirely from cache.
#[test]
#[ignore = "production circuit dimensions: minutes and many GiB"]
fn a_combined_call_simulates_once_and_reuses_its_traces() {
    let mut prover = prover(CpuExecutionProverConfiguration::default());
    assert!(
        prover.cache_quota_blocks() > 0,
        "the default pool must leave a cache quota, or this test cannot distinguish reuse from re-simulation"
    );
    let handle = registered(&mut prover);

    let before = prover.simulations_started();
    let _result = prover.commit_memory_and_prove(1, &handle, non_determinism());
    assert_eq!(
        prover.simulations_started() - before,
        1,
        "a combined call must simulate exactly once across both passes"
    );
    assert!(
        prover.cache_hits() > 0,
        "the prove pass must have been served from the commit pass's traces"
    );
    assert!(prover.peak_cached_blocks() > 0);
    assert!(prover.peak_cached_blocks() <= prover.cache_quota_blocks());
}

/// The mixed case: a quota deliberately too small for the fixture, so some
/// traces are retained and the rest are evicted and rebuilt. Since the minimum
/// pool is `R_effective + 1`, the quota is exactly `SPILLING_QUOTA_BLOCKS`.
#[test]
#[ignore = "a real execution: minutes and tens of GiB"]
fn a_spilling_execution_reuses_what_it_kept_and_rebuilds_the_rest() {
    const SPILLING_QUOTA_BLOCKS: usize = 4;

    let mut configuration = CpuExecutionProverConfiguration::default();
    configuration.host_allocators_per_job_count = configuration
        .minimum_host_allocators_per_job()
        .expect("the minimum must be derivable")
        + SPILLING_QUOTA_BLOCKS;
    let mut prover = prover(configuration);
    assert_eq!(
        prover.cache_quota_blocks(),
        SPILLING_QUOTA_BLOCKS,
        "the quota is the pool above the reserve"
    );
    let total_blocks = prover.available_trace_blocks();
    let handle = registered(&mut prover);

    let before = prover.simulations_started();
    let _result = prover.commit_memory_and_prove(1, &handle, non_determinism());

    // Both halves, asserted separately: what was kept, and what was lost.
    assert_eq!(
        prover.simulations_started() - before,
        2,
        "the prove pass must re-simulate what the quota could not hold"
    );
    assert!(
        prover.cache_hits() > 0,
        "some requests must still have been served from cache, or this is the \
         all-evicted case rather than the mixed one"
    );
    assert!(
        prover.peak_cached_blocks() > 0,
        "a positive quota must retain something"
    );
    assert!(
        prover.peak_cached_blocks() <= SPILLING_QUOTA_BLOCKS,
        "retention is bounded by the quota"
    );
    assert_eq!(
        prover.available_trace_blocks(),
        total_blocks,
        "every block must be back in the pool once the call returns"
    );
}

/// At the minimum pool the quota is zero: nothing is retained, and the prove
/// pass necessarily simulates again.
#[test]
#[ignore = "a real execution: minutes"]
fn a_minimum_pool_retains_nothing() {
    let mut configuration = CpuExecutionProverConfiguration::default();
    configuration.host_allocators_per_job_count = configuration
        .minimum_host_allocators_per_job()
        .expect("the minimum must be derivable");
    let mut prover = prover(configuration);
    assert_eq!(
        prover.cache_quota_blocks(),
        0,
        "at the minimum pool there is no room to cache"
    );
    let handle = registered(&mut prover);

    let before = prover.simulations_started();
    let _result = prover.commit_memory_and_prove(1, &handle, non_determinism());
    assert_eq!(
        prover.peak_cached_blocks(),
        0,
        "a zero quota must retain nothing"
    );
    assert!(
        prover.simulations_started() - before >= 2,
        "with nothing cached the prove pass must simulate again"
    );
}

/// Separate commit and prove calls each take their own execution, so the prove
/// pass re-simulates: the standalone commitment ticket carries no trace credits.
#[test]
#[ignore = "production circuit dimensions: minutes and many GiB"]
fn separate_commit_and_prove_calls_each_simulate() {
    let mut prover = prover(CpuExecutionProverConfiguration::default());
    let handle = registered(&mut prover);

    let before = prover.simulations_started();
    let ticket = prover.commit_memory(1, &handle, non_determinism());
    assert_eq!(prover.simulations_started() - before, 1);
    let _result = prover.prove(1, ticket, non_determinism());
    assert_eq!(
        prover.simulations_started() - before,
        2,
        "a standalone prove pass has no cached traces to reuse"
    );
}

/// Repeated calls against one registered binary reuse setups and twiddles and
/// stay independent: each call simulates exactly once.
#[test]
#[ignore = "production circuit dimensions: minutes and many GiB"]
fn repeated_calls_reuse_setup_state() {
    let mut prover = prover(CpuExecutionProverConfiguration::default());
    let handle = registered(&mut prover);

    for batch_id in 0..2u64 {
        let before = prover.simulations_started();
        let _result = prover.commit_memory_and_prove(batch_id, &handle, non_determinism());
        assert_eq!(prover.simulations_started() - before, 1);
    }
    assert!(
        !prover.is_terminal(),
        "repeated calls must not end the prover"
    );
}

/// One proving thread still completes: the pipeline must not depend on a spare
/// thread being idle.
#[test]
#[ignore = "production circuit dimensions: minutes and many GiB"]
fn a_one_thread_configuration_completes() {
    let mut configuration = CpuExecutionProverConfiguration::default();
    configuration.backend.proving_threads = Some(1);
    let mut prover = prover(configuration);
    let handle = registered(&mut prover);
    let _result = prover.commit_memory_and_prove(1, &handle, non_determinism());
}

/// The shared orchestrator's output against the unchanged legacy CPU prover.
///
/// Both legs run the same program on the same ISA, RAM, cycle bound,
/// non-determinism, security level, proof-of-work bits and backends: with any
/// of those differing, neither a match nor a mismatch could be read as a
/// verdict on the new path. Byte-identical proofs are required because
/// `deterministic_pow` makes the proof-of-work search reproducible.
#[test]
#[ignore = "two full executions of a real binary: the most expensive gate in this crate"]
fn the_shared_path_agrees_with_the_legacy_cpu_prover() {
    let (binary, text) = delegating_fixture();

    // Scoped: the prover owns the whole block pool, the trace cache and the
    // guest-RAM holders, and holding it alive through the legacy leg below
    // would stack two executions' footprints in one process.
    let (mine, my_setups) = {
        let mut prover = prover(CpuExecutionProverConfiguration::default());
        let handle = prover.add_binary(
            ExecutionKind::Unrolled,
            MachineType::FullUnsigned,
            binary.clone(),
            text.clone(),
            Some(CYCLES_BOUND as u32),
        );
        let result = prover.commit_memory_and_prove(1, &handle, non_determinism());
        let artifacts = prover.program_artifacts(&handle);
        program_prover::assemble_program_proof(&artifacts, result)
    };

    // Legacy oracle, same configuration on every axis.
    let worker = worker::Worker::new();
    let (legacy, legacy_setups) = program_prover::unrolled::prove_unrolled_execution_with_replayer::<
        riscv_transpiler::cycle::IMStandardIsaConfigUnsignedMulDivOnly,
        std::alloc::Global,
        _,
        _,
    >(
        CYCLES_BOUND,
        &binary,
        &text,
        true,
        non_determinism(),
        RAM_BOUND,
        &worker,
        prover::definitions::SecurityLevel::Sec100,
        verifier_common::MEMORY_DELEGATION_POW_BITS as u32,
        &prover::gkr::prover::DefaultBabyBearBackend::default(),
        &prover::gkr::prover::DefaultBabyBearGKRBackend::default(),
    );

    // Final state.
    assert_eq!(mine.final_pc, legacy.final_pc, "final pc");
    assert_eq!(
        mine.final_timestamp, legacy.final_timestamp,
        "final timestamp"
    );
    assert_eq!(
        mine.register_final_values, legacy.register_final_values,
        "final register values"
    );
    // The legacy leg leaves `end_params` as a placeholder (its driver computes
    // them externally), so comparing the fields would compare a real value
    // against a stand-in. Recompute over each leg's own setups instead, and
    // check our assembled field really is that recomputation rather than a
    // placeholder of our own.
    let my_end_params =
        full_statement_verifier::host_utils::compute_end_params(&my_setups, mine.final_pc);
    assert_eq!(
        mine.end_params, my_end_params,
        "our assembled end params must be the recomputation, not a placeholder"
    );
    assert_eq!(
        my_end_params,
        full_statement_verifier::host_utils::compute_end_params(&legacy_setups, legacy.final_pc),
        "end params recomputed over each leg's setups"
    );
    assert_eq!(mine.pow_challenge, legacy.pow_challenge, "pow challenge");

    // Setup caps, family by family.
    assert_eq!(
        my_setups.keys().collect::<Vec<_>>(),
        legacy_setups.keys().collect::<Vec<_>>(),
        "setup family keys"
    );
    for (family, mine_params) in my_setups.iter() {
        assert_eq!(mine_params, &legacy_setups[family], "setup params {family}");
    }

    // Family and sequence counts, over the UNION of both key sets with a
    // missing family read as zero proofs.
    //
    // An absent family and a present-but-empty one are the same statement: the
    // flattener emits a zero count for either, so the two representations are
    // equivalent in the proof. They differ only in how each leg gets there —
    // the shared assembly keeps an empty list for every family that has a
    // setup, while the legacy prover's "for consistency" empties go into its
    // internal `main_proofs` and never reach the returned `riscv_proofs`. For
    // this fixture that is family 17 (LOAD_STORE_SUBWORD_ONLY), which the run
    // never exercises. Comparing key sets literally would therefore fail on a
    // representation difference that no verifier can observe. This mirrors the
    // migrated GPU proof-diff, which already compares the same way.
    let riscv_count = |proofs: &BTreeMap<u32, Vec<_>>, family: &u32| {
        proofs.get(family).map(Vec::len).unwrap_or(0)
    };
    let all_families: BTreeSet<u32> = mine
        .riscv_proofs
        .keys()
        .chain(legacy.riscv_proofs.keys())
        .copied()
        .collect();
    for family in &all_families {
        assert_eq!(
            riscv_count(&mine.riscv_proofs, family),
            riscv_count(&legacy.riscv_proofs, family),
            "sequence count for family {family}"
        );
    }
    // A representation-tolerant count comparison must not become a vacuous
    // one: this fixture has to actually prove RISC-V families.
    assert!(
        all_families
            .iter()
            .any(|family| riscv_count(&mine.riscv_proofs, family) > 0),
        "no family carries any proof, so the comparison above proves nothing"
    );
    assert_eq!(
        mine.delegation_proofs.keys().collect::<Vec<_>>(),
        legacy.delegation_proofs.keys().collect::<Vec<_>>(),
        "delegation keys"
    );
    assert!(
        !mine.delegation_proofs.is_empty(),
        "this fixture must actually delegate, or it is not a delegation test"
    );
    for (delegation, mine_proofs) in mine.delegation_proofs.iter() {
        assert_eq!(
            mine_proofs.len(),
            legacy.delegation_proofs[delegation].len(),
            "sequence count for delegation {delegation}"
        );
    }
    assert_eq!(
        mine.inits_and_teardown_proofs.len(),
        legacy.inits_and_teardown_proofs.len(),
        "inits-and-teardowns instance count"
    );

    // Inits-and-teardowns windows, and the shared challenges every proof carries.
    for (index, (mine_proof, legacy_proof)) in mine
        .inits_and_teardown_proofs
        .iter()
        .zip(legacy.inits_and_teardown_proofs.iter())
        .enumerate()
    {
        assert_eq!(
            mine_proof.inits_and_teardowns_top_bits, legacy_proof.inits_and_teardowns_top_bits,
            "inits-and-teardowns windows of instance {index}"
        );
    }
    let my_challenges = first_challenges(&mine);
    assert_eq!(
        my_challenges,
        first_challenges(&legacy),
        "shared external challenges"
    );

    // Memory caps and the proofs themselves, byte for byte.
    for (family, circuit) in mine.compiled_riscv_circuits.iter() {
        // Absent reads as empty on both sides, per the union comparison above;
        // indexing would panic on a family that only one leg materialises.
        let empty: Vec<_> = Vec::new();
        let mine_family = mine.riscv_proofs.get(family).unwrap_or(&empty);
        let legacy_family = legacy.riscv_proofs.get(family).unwrap_or(&empty);
        for (index, (mine_proof, legacy_proof)) in
            mine_family.iter().zip(legacy_family.iter()).enumerate()
        {
            assert_memory_cap_and_bytes(
                mine_proof,
                legacy_proof,
                circuit,
                &format!("family {family} sequence {index}"),
            );
        }
    }
    if let Some(circuit) = mine.inits_and_teardowns_circuit.as_ref() {
        for (index, (mine_proof, legacy_proof)) in mine
            .inits_and_teardown_proofs
            .iter()
            .zip(legacy.inits_and_teardown_proofs.iter())
            .enumerate()
        {
            assert_memory_cap_and_bytes(
                mine_proof,
                legacy_proof,
                circuit,
                &format!("inits-and-teardowns {index}"),
            );
        }
    }
    // Drive this from the PROOFS, not from the compiled circuits: assembly
    // embeds an artifact for every delegation circuit whether or not it fired,
    // so iterating the circuits and indexing the proof map panics on the first
    // delegation this fixture never calls. The strict key and count assertions
    // above already constrain the proof map itself; absent still reads as empty
    // so this cannot panic on either side.
    let no_proofs: Vec<_> = Vec::new();
    for (delegation, mine_delegation_proofs) in mine.delegation_proofs.iter() {
        let circuit = mine
            .compiled_delegation_circuits
            .get(delegation)
            .unwrap_or_else(|| panic!("delegation {delegation} has proofs but no circuit"));
        let legacy_delegation_proofs = legacy
            .delegation_proofs
            .get(delegation)
            .unwrap_or(&no_proofs);
        for (index, (mine_proof, legacy_proof)) in mine_delegation_proofs
            .iter()
            .zip(legacy_delegation_proofs.iter())
            .enumerate()
        {
            assert_memory_cap_and_bytes(
                mine_proof,
                legacy_proof,
                circuit,
                &format!("delegation {delegation} sequence {index}"),
            );
        }
    }
}
