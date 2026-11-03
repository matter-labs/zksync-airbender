#![feature(allocator_api)]
//! The CPU backend against the legacy CPU prover, which is called only from
//! here and never adjusted to agree with us. Ignored by default: two full
//! executions of a real binary.

use cpu_execution_prover::{CpuExecutionProver, CpuExecutionProverConfiguration};
use execution_prover::{ExecutionKind, MachineType};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use std::collections::{BTreeMap, BTreeSet};

/// Shared by both legs; the JIT's timestamp bound must fit `u32`, which
/// `1 << 31` cycles would not.
const CYCLES_BOUND: usize = 1 << 29;
/// `JitRunnerRam::Medium`, which the CPU defaults select.
const RAM_BOUND: usize = 1 << 30;

/// Calls a delegation, so the comparison covers a delegation proof.
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

/// Byte-identical proofs are required: `deterministic_pow` makes the
/// proof-of-work search reproducible, and every other input is shared.
#[test]
#[ignore = "two full executions of a real binary: the most expensive gate in this crate"]
fn the_shared_path_agrees_with_the_legacy_cpu_prover() {
    let (binary, text) = delegating_fixture();

    // Scoped so the block pool and caches are released before the legacy leg.
    let (mine, my_setups) = {
        let mut prover =
            CpuExecutionProver::with_configuration(CpuExecutionProverConfiguration::default());
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

    assert_eq!(mine.final_pc, legacy.final_pc, "final pc");
    assert_eq!(
        mine.final_timestamp, legacy.final_timestamp,
        "final timestamp"
    );
    assert_eq!(
        mine.register_final_values, legacy.register_final_values,
        "final register values"
    );
    assert_eq!(mine.pow_challenge, legacy.pow_challenge, "pow challenge");

    assert_eq!(
        my_setups.keys().collect::<Vec<_>>(),
        legacy_setups.keys().collect::<Vec<_>>(),
        "setup family keys"
    );
    for (family, mine_params) in my_setups.iter() {
        assert_eq!(mine_params, &legacy_setups[family], "setup params {family}");
    }

    // The verifier encodes absent and empty families alike, so compare counts
    // over the union of keys.
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

    for (family, circuit) in mine.compiled_riscv_circuits.iter() {
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
    for (delegation, mine_delegation_proofs) in mine.delegation_proofs.iter() {
        for (index, (mine_proof, legacy_proof)) in mine_delegation_proofs
            .iter()
            .zip(legacy.delegation_proofs[delegation].iter())
            .enumerate()
        {
            assert_memory_cap_and_bytes(
                mine_proof,
                legacy_proof,
                &mine.compiled_delegation_circuits[delegation],
                &format!("delegation {delegation} sequence {index}"),
            );
        }
    }
}
