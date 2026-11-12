//! The sole writer of ordinary committed Sec100 circuit proofs.

use super::orchestration::canonical_fixtures::{
    canonical_circuits, capture_canonical_inputs, CanonicalCircuit, CanonicalInputs,
    CanonicalTrace, SparseInitsAndTeardowns,
};
use super::orchestration::common::hardcoded_external_challenges;
use crate::definitions::{GKRExternalChallenges, SoundnessMode};
use crate::gkr::prover::setup::GKRSetup;
use crate::gkr::prover::{
    prove_configured_with_gkr_with_storage_and_backend, DefaultBabyBearGKRBackend, GKRProof,
    OperationMode, WhirOracleStorage, WorkStealingBackend,
};
use crate::gkr::prover_config::ProverConfig;
use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use crate::gkr::witness_gen::delegation_circuits::evaluate_gkr_witness_for_delegation_circuit;
use crate::gkr::witness_gen::family_circuits::{
    evaluate_gkr_witness_for_executor_family, evaluate_init_and_teardown_memory_witness,
    GKRFullWitnessTrace,
};
use crate::gkr::witness_gen::oracles::{
    MemoryCircuitOracle, NonMemoryCircuitOracle, UnifiedRiscvCircuitOracle,
};
use crate::merkle_trees::DefaultTreeConstructor;
use crate::tracers::oracles::transpiler_oracles::delegation::{
    BigintDelegationOracle, Blake2sDelegationOracle, KeccakChi5DelegationOracle,
    KeccakColumnParityDelegationOracle, KeccakDelegationOracle, KeccakThetaRhoDelegationOracle,
};
use cs::gkr_compiler::GKRCircuitArtifact;
use cs::utils::split_timestamp;
use fft::Twiddles;
use field::baby_bear::{base::BabyBearField as BF, ext4::BabyBearExt4 as E4};
use field::{Field, PrimeField};
use std::alloc::Global;
use std::collections::BTreeSet;
use std::path::PathBuf;
use std::time::Instant;
use transcript::Blake2sTranscript;
use worker::Worker;

type Proof = GKRProof<BF, E4, DefaultTreeConstructor>;
type Trace = GKRFullWitnessTrace<BF, Global, Global>;

struct Prepared {
    circuit: CanonicalCircuit,
    mode: SoundnessMode,
    started: Instant,
    compiled: GKRCircuitArtifact<BF>,
    config: ProverConfig,
    witness: Trace,
    setup: GKRSetup<BF>,
    top_bits: Vec<u32>,
}

fn root() -> PathBuf {
    proof_fixtures::root()
}

fn dense_ram(sparse: &SparseInitsAndTeardowns, rows: usize) -> Vec<([Vec<BF>; 2], [Vec<BF>; 2])> {
    let mut sets: Vec<_> = sparse
        .top_bits
        .iter()
        .map(|_| {
            (
                [vec![BF::ZERO; rows], vec![BF::ZERO; rows]],
                [vec![BF::ZERO; rows], vec![BF::ZERO; rows]],
            )
        })
        .collect();
    for &(address, (timestamp, value)) in &sparse.touched {
        let word = address as usize >> 2;
        let top_bits = (word / rows) as u32;
        let set = sparse.top_bits.binary_search(&top_bits).unwrap();
        let row = word % rows;
        let (low, high) = split_timestamp(timestamp);
        sets[set].0[0][row] = BF::from_u32_unchecked(low);
        sets[set].0[1][row] = BF::from_u32_unchecked(high);
        sets[set].1[0][row] = BF::from_u32_unchecked(value & 0xffff);
        sets[set].1[1][row] = BF::from_u32_unchecked(value >> 16);
    }
    sets
}

fn prepare(circuit: CanonicalCircuit, mode: SoundnessMode, worker: &Worker) -> Prepared {
    let started = Instant::now();
    println!("canonical-entry-begin {} {:?}", circuit.stem(), mode);
    let root = root();
    let CanonicalInputs {
        compiled_circuit: compiled,
        table_driver,
        decoder_table,
        trace,
        inits_and_teardowns,
        ..
    } = capture_canonical_inputs(&root, circuit, worker);
    let config = circuit.prover_config(&root, mode);
    assert_eq!(1 << config.trace_len_log2, compiled.trace_len);
    let rows = compiled.trace_len;
    let top_bits = inits_and_teardowns
        .as_ref()
        .map(|ram| ram.top_bits.clone())
        .unwrap_or_default();
    macro_rules! delegation {
        ($rows:expr, $oracle:ident, $module:ident) => {{
            let oracle = $oracle {
                cycle_data: &$rows,
                marker: core::marker::PhantomData,
            };
            evaluate_gkr_witness_for_delegation_circuit(
                &compiled,
                super::$module::witness_eval_fn,
                rows,
                &oracle,
                &table_driver,
                worker,
                Global,
                Global,
            )
        }};
    }
    let witness = match trace {
        CanonicalTrace::NonMemory(buffer) => {
            let oracle = NonMemoryCircuitOracle {
                inner: &buffer,
                decoder_table: &decoder_table,
                default_pc_value_in_padding: 4,
            };
            let evaluator: fn(&mut ColumnMajorWitnessProxy<'_, NonMemoryCircuitOracle<'_>, BF>) =
                match circuit {
                    CanonicalCircuit::AddSubLuiAuipcMop => {
                        super::add_sub_lui_auipc_mop::witness_eval_fn
                    }
                    CanonicalCircuit::JumpBranchSlt => super::jump_branch_slt::witness_eval_fn,
                    CanonicalCircuit::ShiftBinop => super::shift_binary_ops::witness_eval_fn,
                    CanonicalCircuit::UnsignedMulDiv => super::unsigned_mul_div::witness_eval_fn,
                    _ => unreachable!(),
                };
            evaluate_gkr_witness_for_executor_family(
                &compiled,
                evaluator,
                rows,
                &oracle,
                &table_driver,
                worker,
                None,
                Global,
                Global,
            )
        }
        CanonicalTrace::Memory(buffer) => {
            let oracle = MemoryCircuitOracle {
                inner: &buffer,
                decoder_table: &decoder_table,
            };
            let evaluator: fn(&mut ColumnMajorWitnessProxy<'_, MemoryCircuitOracle<'_>, BF>) =
                match circuit {
                    CanonicalCircuit::MemWordOnly => super::mem_word_only::witness_eval_fn,
                    CanonicalCircuit::MemSubwordOnly => super::mem_subword_only::witness_eval_fn,
                    _ => unreachable!(),
                };
            evaluate_gkr_witness_for_executor_family(
                &compiled,
                evaluator,
                rows,
                &oracle,
                &table_driver,
                worker,
                None,
                Global,
                Global,
            )
        }
        CanonicalTrace::Unified(buffer) => {
            let oracle = UnifiedRiscvCircuitOracle {
                inner: &buffer,
                decoder_table: &decoder_table,
            };
            evaluate_gkr_witness_for_executor_family(
                &compiled,
                super::unified_reduced_machine::witness_eval_fn,
                rows,
                &oracle,
                &table_driver,
                worker,
                Some(dense_ram(inits_and_teardowns.as_ref().unwrap(), rows)),
                Global,
                Global,
            )
        }
        CanonicalTrace::Bigint(buffer) => {
            delegation!(buffer, BigintDelegationOracle, bigint_with_extended_control)
        }
        CanonicalTrace::Blake2WithCompression(buffer) => delegation!(
            buffer,
            Blake2sDelegationOracle,
            blake2_with_extended_control
        ),
        CanonicalTrace::KeccakSpecial5(buffer) => {
            delegation!(buffer, KeccakDelegationOracle, keccak_special5)
        }
        CanonicalTrace::KeccakColumnParity(buffer) => delegation!(
            buffer,
            KeccakColumnParityDelegationOracle,
            keccak_column_parity
        ),
        CanonicalTrace::KeccakThetaRho(buffer) => {
            delegation!(buffer, KeccakThetaRhoDelegationOracle, keccak_theta_rho)
        }
        CanonicalTrace::KeccakChi5(buffer) => {
            delegation!(buffer, KeccakChi5DelegationOracle, keccak_chi5)
        }
        CanonicalTrace::InitsAndTeardowns => Trace {
            column_major_memory_trace: evaluate_init_and_teardown_memory_witness(
                dense_ram(inits_and_teardowns.as_ref().unwrap(), rows),
                &compiled,
                Global,
                Global,
            ),
            column_major_witness_trace: Vec::new(),
            column_major_scratch_space_trace: Vec::new(),
            generic_lookup_mapping: Vec::new(),
            range_check_16_lookup_mapping: Vec::new(),
            timestamp_range_check_lookup_mapping: Vec::new(),
        },
    };
    if matches!(
        circuit,
        CanonicalCircuit::AddSubLuiAuipcMop | CanonicalCircuit::ShiftBinop
    ) || cfg!(feature = "gkr_check_satisfied")
    {
        assert!(super::check_satisfied(&compiled, &witness));
    }
    let setup = GKRSetup::construct(&table_driver, &decoder_table, rows, &compiled, worker);
    // The witness and setup own their data. Do not retain lookup maps during
    // commitments and GKR/WHIR proving, especially the subword ROM tables.
    drop(table_driver);
    drop(decoder_table);
    println!(
        "canonical {} {:?}: input/witness/setup {:.3?}",
        circuit.stem(),
        mode,
        started.elapsed()
    );
    Prepared {
        circuit,
        mode,
        started,
        compiled,
        config,
        witness,
        setup,
        top_bits,
    }
}

fn prove(prepared: Prepared, challenges: &GKRExternalChallenges<BF, E4>, worker: &Worker) -> Proof {
    let started = Instant::now();
    let twiddles =
        Twiddles::<BF, Global>::new(1 << prepared.config.whir_message_size_log2(), worker);
    let backend = WorkStealingBackend;
    let setup_commitment = prepared.setup.commit_for_config::<DefaultTreeConstructor>(
        &twiddles,
        &prepared.config,
        worker,
    );
    let proof = prove_configured_with_gkr_with_storage_and_backend::<
        BF,
        E4,
        DefaultTreeConstructor,
        Blake2sTranscript,
        _,
        _,
    >(
        &prepared.compiled,
        challenges,
        prepared.witness,
        &prepared.setup,
        &setup_commitment,
        &twiddles,
        &prepared.config,
        OperationMode::MultipleChunks,
        WhirOracleStorage::fully_in_memory_continuous(),
        prepared.top_bits,
        prepared.compiled.trace_len,
        &backend,
        &DefaultBabyBearGKRBackend::default(),
        worker,
    );
    assert_eq!(
        proof.whir_proof.whir_schedule,
        prepared.config.whir_schedule
    );
    println!(
        "canonical {}: proving {:.3?}",
        prepared.circuit.stem(),
        started.elapsed()
    );
    println!(
        "canonical-entry-end {} {:?} {:.6}",
        prepared.circuit.stem(),
        prepared.mode,
        prepared.started.elapsed().as_secs_f64()
    );
    proof
}

fn write(circuit: CanonicalCircuit, mode: SoundnessMode, proof: &Proof) {
    let path = circuit.proof_path(&proof_fixtures::output_root(), mode);
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    proof_fixtures::write_file(&path, proof);
}

#[test]
fn regenerate_canonical_circuit_proofs_pessimistic_conjecture() {
    regenerate_canonical_circuit_proofs(SoundnessMode::PessimisticConjecture);
}

#[test]
fn regenerate_canonical_circuit_proofs_ethproofs_soundcalc() {
    regenerate_canonical_circuit_proofs(SoundnessMode::EthproofsSoundnessCalc);
}

fn regenerate_canonical_circuit_proofs(mode: SoundnessMode) {
    let worker = Worker::new();
    for circuit in canonical_circuits(mode) {
        let prepared = prepare(circuit, mode, &worker);
        let proof = prove(prepared, &hardcoded_external_challenges(), &worker);
        write(circuit, mode, &proof);
    }
    let output_root = proof_fixtures::output_root();
    let expected: BTreeSet<_> = canonical_circuits(mode)
        .map(|circuit| circuit.proof_path(&output_root, mode))
        .collect();
    let produced: BTreeSet<_> = std::fs::read_dir(
        output_root
            .join("fixtures/circuits")
            .join(mode.file_suffix()),
    )
    .unwrap()
    .map(|entry| entry.unwrap().path())
    .collect();
    assert_eq!(expected, produced);
}

fn pilot(circuit: CanonicalCircuit) {
    let worker = Worker::new();
    let prepared = prepare(circuit, SoundnessMode::DEFAULT, &worker);
    let proof = prove(prepared, &hardcoded_external_challenges(), &worker);
    println!(
        "pilot {}: {} proof bytes; no fixture write",
        circuit.stem(),
        serde_json::to_vec_pretty(&proof).unwrap().len()
    );
}

#[test]
#[ignore = "CPU proof cost pilot; no committed fixture writes"]
fn canonical_proof_pilot_add_sub() {
    pilot(CanonicalCircuit::AddSubLuiAuipcMop);
}

#[test]
#[ignore = "CPU proof cost pilot; no committed fixture writes"]
fn canonical_proof_pilot_bigint() {
    pilot(CanonicalCircuit::BigintWithExtendedControl);
}
