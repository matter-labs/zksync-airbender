//! Delegation prove orchestration — shared between per-family and unified
//! modes. Each function proves one delegation circuit (blake2 / bigint /
//! keccak / blake2-g-function) against the captured VM snapshotter.
//!
//! Each call replays the snapshotter into the delegation-specific tracer,
//! builds the oracle, computes memory + full witnesses, optionally proves
//! the circuit, and returns the memory trace + an `Option<GKRProof>`. The
//! caller uses the memory trace to populate the cross-circuit
//! `memory_read_set` / `memory_write_set` / `delegation_read_set` via
//! `parse_delegation_ram_accesses_from_full_trace`.
//!
//! Witness-eval functions are taken as `fn` parameters because their
//! current home is in the test module (`prover/src/tests/gkr/mod.rs`); the
//! orchestration stays decoupled from that.

use super::common::*;
use crate::cs::gkr_compiler::GKRCircuitArtifact;
use crate::cs::tables::TableDriver;
use crate::definitions::SecurityLevel;
use crate::gkr::prover::prove_configured_with_gkr;
use crate::gkr::prover::setup::GKRSetup;
use crate::gkr::prover::{GKRExternalChallenges, GKRProof};
use crate::gkr::prover_config::example_configs;
use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use crate::gkr::witness_gen::delegation_circuits::{
    evaluate_gkr_memory_witness_for_delegation_circuit,
    evaluate_gkr_witness_for_delegation_circuit,
};
use crate::gkr::witness_gen::family_circuits::GKRMemoryOnlyWitnessTrace;
use crate::merkle_trees::DefaultTreeConstructor;
use crate::tracers::oracles::transpiler_oracles::delegation::{
    BigintDelegationOracle, Blake2sDelegationOracle, Blake2sGFunctionDelegationOracle,
    KeccakDelegationOracle,
};
use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use common_constants::{
    BIGINT_OPS_WITH_CONTROL_CSR_REGISTER, BLAKE2S_DELEGATION_CSR_REGISTER,
    BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER, KECCAK_SPECIAL5_CSR_REGISTER,
};
use cs::oracle::Oracle;
use fft::Twiddles;
use field::Field;
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{Counters, ReplayBuffer, SimpleSnapshotter, SimpleTape, State};
use riscv_transpiler::witness::{
    BigintDelegationDestinationHolder, BlakeDelegationDestinationHolder,
    BlakeGFunctionDelegationDestinationHolder, DelegationWitness,
    KeccakDelegationDestinationHolder,
};
use std::alloc::Global;
use worker::Worker;

const USE_GKR_WITH_CACHES: bool = cfg!(not(feature = "no_caches"));

/// Output of [`prove_delegation_blake`] / [`prove_delegation_bigint`] /
/// [`prove_delegation_keccak`] / [`prove_delegation_blake_g_function`].
///
/// `memory_trace` is always populated (the caller needs it to update the
/// cross-circuit memory permutation sets). `proof` is `None` when:
///   - the delegation is empty AND `prove_empty == false`,
///   - the circuits filter excluded this delegation, or
///   - `compute_only == true` (memory-permutation-only mode).
pub struct DelegationProveOutput {
    pub memory_trace: GKRMemoryOnlyWitnessTrace<BabyBearField, Global, Global>,
    pub compiled_circuit: GKRCircuitArtifact<BabyBearField>,
    pub proof: Option<GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>>,
    pub delegation_type: u16,
}

impl DelegationProveOutput {
    /// The grand-product contribution for the memory-permutation accumulator.
    /// `BabyBearExt4::ONE` when the proof was skipped (or the circuit had no
    /// calls, in which case the prover-side check already asserted ONE).
    pub fn grand_product_factor(&self) -> BabyBearExt4 {
        self.proof
            .as_ref()
            .map(|p| p.grand_product_accumulator_computed)
            .unwrap_or(BabyBearExt4::ONE)
    }
}

/// Common prove-side logic shared by all four delegations.
fn prove_delegation_inner<O: Oracle<BabyBearField> + DelegationOracleExt>(
    circuit: &GKRCircuitArtifact<BabyBearField>,
    table_driver: &TableDriver<BabyBearField>,
    oracle: &O,
    eval_fn: fn(&mut ColumnMajorWitnessProxy<'_, O, BabyBearField>),
    num_delegation_cycles: usize,
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    level: SecurityLevel,
    should_prove: bool,
    proof_path: &str,
    worker: &Worker,
) -> (
    GKRMemoryOnlyWitnessTrace<BabyBearField, Global, Global>,
    Option<GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>>,
) {
    let memory_trace = evaluate_gkr_memory_witness_for_delegation_circuit(
        circuit,
        num_delegation_cycles,
        oracle,
        worker,
        Global,
        Global,
    );

    let full_trace = evaluate_gkr_witness_for_delegation_circuit(
        circuit,
        eval_fn,
        num_delegation_cycles,
        oracle,
        table_driver,
        worker,
        Global,
        Global,
    );

    super::common::ensure_memory_trace_consistency(&memory_trace, &full_trace);

    if !should_prove {
        return (memory_trace, None);
    }

    #[cfg(all(feature = "gkr_check_satisfied", any(test, feature = "test")))]
    {
        println!("Checking constraint satisfiability");
        assert!(
            crate::tests::gkr::check_satisfied(circuit, &full_trace),
            "delegation circuit constraint not satisfied"
        );
    }

    let prover_config = example_configs::config_for_security_level_under_pessimistic_conjecture(
        num_delegation_cycles.trailing_zeros() as usize,
        level,
    );
    let twiddles: Twiddles<_, Global> = Twiddles::new(num_delegation_cycles, worker);
    let setup = GKRSetup::construct(table_driver, &[], num_delegation_cycles, circuit);
    let setup_commitment = setup.commit(
        &twiddles,
        prover_config.lde_factor,
        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
        prover_config.cap_size,
        num_delegation_cycles.trailing_zeros() as usize,
        worker,
    );

    println!("Trying to prove");
    let now = std::time::Instant::now();
    let proof = prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
        circuit,
        external_challenges,
        full_trace,
        &setup,
        &setup_commitment,
        &twiddles,
        &prover_config,
        Vec::new(),
        num_delegation_cycles,
        worker,
    );
    println!("Proving time is {:?}", now.elapsed());

    if oracle.is_empty() {
        assert_eq!(proof.grand_product_accumulator_computed, BabyBearExt4::ONE);
    }

    serialize_to_file(&proof, proof_path);

    (memory_trace, Some(proof))
}

/// Trait for the four delegation oracles, only used so the inner helper can
/// query `is_empty()` consistently.
trait DelegationOracleExt {
    fn is_empty(&self) -> bool;
}
impl<'a> DelegationOracleExt for Blake2sDelegationOracle<'a> {
    fn is_empty(&self) -> bool {
        self.cycle_data.is_empty()
    }
}
impl<'a> DelegationOracleExt for BigintDelegationOracle<'a> {
    fn is_empty(&self) -> bool {
        self.cycle_data.is_empty()
    }
}
impl<'a> DelegationOracleExt for KeccakDelegationOracle<'a> {
    fn is_empty(&self) -> bool {
        self.cycle_data.is_empty()
    }
}
impl<'a> DelegationOracleExt for Blake2sGFunctionDelegationOracle<'a> {
    fn is_empty(&self) -> bool {
        self.cycle_data.is_empty()
    }
}

/// Path helper: per-variant compiled-circuit JSON.
fn circuit_path(stem: &str) -> String {
    if USE_GKR_WITH_CACHES {
        format!("../cs/compiled_circuits/{stem}_layout_gkr.json")
    } else {
        format!("../cs/compiled_circuits/{stem}_layout_no_caches_gkr.json")
    }
}

pub fn prove_delegation_blake<C>(
    snapshotter: &SimpleSnapshotter<C, { common_constants::ROM_SECOND_WORD_BITS }>,
    tape: &SimpleTape,
    expected_final_state: &State<C>,
    cycles_bound: usize,
    num_calls: usize,
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    level: SecurityLevel,
    prove_empty: bool,
    compute_only: bool,
    circuits_filter: &Option<std::collections::HashSet<String>>,
    proof_suffix: &str,
    worker: &Worker,
    eval_fn: fn(&mut ColumnMajorWitnessProxy<'_, Blake2sDelegationOracle<'_>, BabyBearField>),
) -> DelegationProveOutput
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    println!("Will try to prove Blake delegation");

    let circuit: GKRCircuitArtifact<BabyBearField> =
        deserialize_from_file(&circuit_path("blake2_with_extended_control"));
    let mut table_driver = TableDriver::<BabyBearField>::new();
    cs::gkr_circuits::delegation::blake2_round_with_extended_control::blake2_with_extended_control_table_driver_fn(&mut table_driver);

    let mut state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };

    let mut buffer = vec![DelegationWitness::empty(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = BlakeDelegationDestinationHolder {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<C>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut ram,
        tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(*expected_final_state, state);

    let delegation_type = BLAKE2S_DELEGATION_CSR_REGISTER as u16;
    let oracle = Blake2sDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    let should_prove = !compute_only
        && circuit_in_filter(circuits_filter, "blake2_with_extended_control")
        && (prove_empty || !oracle.is_empty());

    let (memory_trace, proof) = prove_delegation_inner(
        &circuit,
        &table_driver,
        &oracle,
        eval_fn,
        BLAKE_NUM_DELEGATION_CYCLES,
        external_challenges,
        level,
        should_prove,
        &format!(
            "test_proofs/blake2_with_extended_control_{}_gkr_proof.json",
            proof_suffix
        ),
        worker,
    );

    DelegationProveOutput {
        memory_trace,
        compiled_circuit: circuit,
        proof,
        delegation_type,
    }
}

pub fn prove_delegation_bigint<C>(
    snapshotter: &SimpleSnapshotter<C, { common_constants::ROM_SECOND_WORD_BITS }>,
    tape: &SimpleTape,
    expected_final_state: &State<C>,
    cycles_bound: usize,
    num_calls: usize,
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    level: SecurityLevel,
    prove_empty: bool,
    compute_only: bool,
    circuits_filter: &Option<std::collections::HashSet<String>>,
    proof_suffix: &str,
    worker: &Worker,
    eval_fn: fn(&mut ColumnMajorWitnessProxy<'_, BigintDelegationOracle<'_>, BabyBearField>),
) -> DelegationProveOutput
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    println!("Will try to prove Bigint delegation");

    let circuit: GKRCircuitArtifact<BabyBearField> =
        deserialize_from_file(&circuit_path("bigint_with_extended_control"));
    let mut table_driver = TableDriver::<BabyBearField>::new();
    cs::gkr_circuits::delegation::bigint_with_control::bigint_with_extended_control_delegation_circuit_table_driver_fn(&mut table_driver);

    let mut state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };

    let mut buffer = vec![DelegationWitness::empty(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = BigintDelegationDestinationHolder {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<C>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut ram,
        tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(*expected_final_state, state);

    let delegation_type = BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16;
    let oracle = BigintDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    let should_prove = !compute_only
        && circuit_in_filter(circuits_filter, "bigint_with_extended_control")
        && (prove_empty || !oracle.is_empty());

    let (memory_trace, proof) = prove_delegation_inner(
        &circuit,
        &table_driver,
        &oracle,
        eval_fn,
        BIGINT_NUM_DELEGATION_CYCLES,
        external_challenges,
        level,
        should_prove,
        &format!(
            "test_proofs/bigint_with_extended_control_{}_gkr_proof.json",
            proof_suffix
        ),
        worker,
    );

    DelegationProveOutput {
        memory_trace,
        compiled_circuit: circuit,
        proof,
        delegation_type,
    }
}

pub fn prove_delegation_keccak<C>(
    snapshotter: &SimpleSnapshotter<C, { common_constants::ROM_SECOND_WORD_BITS }>,
    tape: &SimpleTape,
    expected_final_state: &State<C>,
    cycles_bound: usize,
    num_calls: usize,
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    level: SecurityLevel,
    prove_empty: bool,
    compute_only: bool,
    circuits_filter: &Option<std::collections::HashSet<String>>,
    proof_suffix: &str,
    worker: &Worker,
    eval_fn: fn(&mut ColumnMajorWitnessProxy<'_, KeccakDelegationOracle<'_>, BabyBearField>),
) -> DelegationProveOutput
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    println!("Will try to prove Keccak delegation");

    let circuit: GKRCircuitArtifact<BabyBearField> =
        deserialize_from_file(&circuit_path("keccak_special5"));
    let mut table_driver = TableDriver::<BabyBearField>::new();
    cs::gkr_circuits::delegation::keccak_special5::keccak_special5_delegation_circuit_table_driver_fn(&mut table_driver);

    let mut state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };

    let mut buffer = vec![DelegationWitness::empty(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = KeccakDelegationDestinationHolder {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<C>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut ram,
        tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(*expected_final_state, state);

    let delegation_type = KECCAK_SPECIAL5_CSR_REGISTER as u16;
    let oracle = KeccakDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    let should_prove = !compute_only
        && circuit_in_filter(circuits_filter, "keccak_special5")
        && (prove_empty || !oracle.is_empty());

    let (memory_trace, proof) = prove_delegation_inner(
        &circuit,
        &table_driver,
        &oracle,
        eval_fn,
        KECCAK_NUM_DELEGATION_CYCLES,
        external_challenges,
        level,
        should_prove,
        &format!(
            "test_proofs/keccak_special5_{}_gkr_proof.json",
            proof_suffix
        ),
        worker,
    );

    DelegationProveOutput {
        memory_trace,
        compiled_circuit: circuit,
        proof,
        delegation_type,
    }
}

pub fn prove_delegation_blake_g_function<C>(
    snapshotter: &SimpleSnapshotter<C, { common_constants::ROM_SECOND_WORD_BITS }>,
    tape: &SimpleTape,
    expected_final_state: &State<C>,
    cycles_bound: usize,
    num_calls: usize,
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    level: SecurityLevel,
    prove_empty: bool,
    compute_only: bool,
    circuits_filter: &Option<std::collections::HashSet<String>>,
    proof_suffix: &str,
    worker: &Worker,
    eval_fn: fn(
        &mut ColumnMajorWitnessProxy<'_, Blake2sGFunctionDelegationOracle<'_>, BabyBearField>,
    ),
) -> DelegationProveOutput
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    println!("Will try to prove Blake G-function delegation");

    let circuit: GKRCircuitArtifact<BabyBearField> =
        deserialize_from_file(&circuit_path("blake2_g_function"));
    let mut table_driver = TableDriver::<BabyBearField>::new();
    cs::gkr_circuits::delegation::blake2_g_function::blake2_g_function_table_driver_fn(&mut table_driver);

    let mut state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };

    let mut buffer = vec![DelegationWitness::empty(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = BlakeGFunctionDelegationDestinationHolder {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<C>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut ram,
        tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(*expected_final_state, state);

    let delegation_type = BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16;
    let oracle = Blake2sGFunctionDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    let should_prove = !compute_only
        && circuit_in_filter(circuits_filter, "blake2_g_function")
        && (prove_empty || !oracle.is_empty());

    let (memory_trace, proof) = prove_delegation_inner(
        &circuit,
        &table_driver,
        &oracle,
        eval_fn,
        BLAKE_G_FUNCTION_NUM_DELEGATION_CYCLES,
        external_challenges,
        level,
        should_prove,
        &format!(
            "test_proofs/blake2_g_function_{}_gkr_proof.json",
            proof_suffix
        ),
        worker,
    );

    DelegationProveOutput {
        memory_trace,
        compiled_circuit: circuit,
        proof,
        delegation_type,
    }
}

// Local helpers re-exported by the orchestration. We can't import from
// `crate::tests::*` (private to test build), so the orchestration carries
// its own copies of these tiny utilities.
pub(super) fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).unwrap();
    serde_json::from_reader(src).unwrap()
}

pub(super) fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}
