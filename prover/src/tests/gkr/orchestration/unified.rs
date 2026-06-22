use super::common::*;
use super::delegations::{
    deserialize_from_file as delegations_deserialize, prove_delegation_bigint,
    prove_delegation_blake, prove_delegation_blake_g_function, prove_delegation_keccak,
    serialize_to_file as delegations_serialize, DelegationProveOutput,
};
use crate::cs::definitions::TimestampScalar;
use crate::cs::gkr_compiler::GKRCircuitArtifact;
use crate::definitions::{
    produce_initial_permutation_product_contribution, FinalRegisterValue, MerkleTreeCap,
    SecurityLevel, DEFAULT_CAP_SIZE,
};
use crate::gkr::prover::prove_configured_with_gkr;
use crate::gkr::prover::setup::GKRSetup;
use crate::gkr::prover::stages::stage1::commit_trace_part;
use crate::gkr::prover::{GKRExternalChallenges, GKRProof};
use crate::gkr::prover_config::example_configs;
use crate::gkr::witness_gen::family_circuits::{
    build_unified_table_driver, evaluate_gkr_memory_witness_for_executor_family,
    evaluate_gkr_witness_for_executor_family, GKRMemoryOnlyWitnessTrace,
};
use crate::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;
use crate::gkr::witness_gen::trace_structs::RamShuffleMemStateRecord;
use crate::merkle_trees::DefaultTreeConstructor;
use crate::merkle_trees::{ColumnMajorMerkleTreeConstructor, MerkleTreeCapVarLength};
use crate::tests::gkr::GKRFullWitnessTrace;
use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
use common_constants::INITIAL_PC;
use common_constants::{
    BIGINT_OPS_WITH_CONTROL_CSR_REGISTER, BLAKE2S_DELEGATION_CSR_REGISTER,
    BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER, KECCAK_SPECIAL5_CSR_REGISTER,
};
use cs::definitions::INITIAL_TIMESTAMP;
use cs::gkr_circuits::ExecutorFamilyDecoderData;
use cs::tables::TableDriver;
use cs::utils::split_timestamp;
use fft::Twiddles;
use field::Field;
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{Counters, ReplayBuffer};
use riscv_transpiler::witness::data_structs::UnifiedOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::UnifiedDestinationHolder;
use std::alloc::Global;
use transcript::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS;
use transcript::{Blake2sBufferingTranscript, Seed};
use worker::Worker;

/// Unified-mode prove output. `unified_proof` is `None` only when the
/// circuits filter explicitly excludes `unified_reduced_machine`.
pub struct UnifiedProverOutput {
    pub unified_proof: Option<GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>>,
    pub compiled_unified_circuit: GKRCircuitArtifact<BabyBearField>,
    pub delegation_outputs: Vec<DelegationProveOutput>,
    pub register_final_state: [RamShuffleMemStateRecord; 32],
    pub final_pc: u32,
    pub final_timestamp: TimestampScalar,
    pub external_challenges: GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    /// The unified circuit's setup-tree cap (the FSV's prepended verification key).
    /// `Some` whenever the unified circuit was proved; `None` only under a circuits
    /// filter that excludes `unified_reduced_machine`.
    pub unified_setup_cap: Option<MerkleTreeCap<DEFAULT_CAP_SIZE>>,
    /// Closes to ONE when the full applicable set was proved (no filter,
    /// machine state + unified proof + all relevant delegations).
    pub permutation_argument_accumulator: BabyBearExt4,
}

const USE_GKR_WITH_CACHES: bool = cfg!(not(feature = "no_caches"));

/// Per-delegation cycle counts. Provided by the caller because the
/// `Counters` trait doesn't expose them via a generic accessor (per-family
/// and unified counter types each have these as plain fields). The test
/// reads the right field for its counter type and passes the count.
#[derive(Clone, Copy, Debug, Default)]
pub struct DelegationCallCounts {
    pub blake: usize,
    pub bigint: usize,
    pub keccak: usize,
    pub blake_g_function: usize,
}

/// Per-delegation witness-eval fn pointers, supplied by the caller (they
/// live in the test module today). Each is `Some` for delegations the
/// active blake-variant build wires up; the orchestration uses `None` to
/// short-circuit that delegation.
pub struct DelegationEvalFns {
    pub blake: Option<
        fn(
            &mut crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<
                '_,
                crate::tracers::oracles::transpiler_oracles::delegation::Blake2sDelegationOracle<'_>,
                BabyBearField,
            >,
        ),
    >,
    pub bigint: Option<
        fn(
            &mut crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<
                '_,
                crate::tracers::oracles::transpiler_oracles::delegation::BigintDelegationOracle<'_>,
                BabyBearField,
            >,
        ),
    >,
    pub keccak: Option<
        fn(
            &mut crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<
                '_,
                crate::tracers::oracles::transpiler_oracles::delegation::KeccakDelegationOracle<'_>,
                BabyBearField,
            >,
        ),
    >,
    pub blake_g_function: Option<
        fn(
            &mut crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<
                '_,
                crate::tracers::oracles::transpiler_oracles::delegation::Blake2sGFunctionDelegationOracle<'_>,
                BabyBearField,
            >,
        ),
    >,
}

/// Unified-mode entry point. Takes a pre-captured `VmRunOutput<C>` from
/// [`run_vm_and_capture`] (so the caller stays in charge of when the VM
/// runs — symmetric with how `family_circuits.rs` drives the per-family
/// helpers), proves the unified circuit plus each active delegation,
/// asserts the grand-product accumulator closes to ONE (unless a circuits
/// filter is active, in which case the assert is skipped because partial
/// proving can't close).
///
/// `unified_eval_fn` is the unified-circuit witness eval fn, supplied by
/// the caller from the test module. Same for the delegation eval fns.
pub fn prove_unified<C>(
    vm: VmRunOutput<C>,
    level: SecurityLevel,
    proof_suffix: &str,
    worker: &Worker,
    unified_eval_fn: fn(
        &mut crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<
            '_,
            UnifiedRiscvCircuitOracle<'_>,
            BabyBearField,
        >,
    ),
    delegation_eval_fns: &DelegationEvalFns,
    delegation_call_counts: &DelegationCallCounts,
) -> UnifiedProverOutput
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    let prove_empty = parse_prove_empty();
    let circuits_filter = parse_circuits_filter();

    // We derive Fiat-Shamir-consistent external challenges (matching what the full statement
    // verifier re-derives from the memory transcript) ONLY when proving the full applicable
    // set (no circuits filter) — a partial/filtered debug run can't close the permutation
    // argument anyway, so it keeps the historical hardcoded challenges. See `derive_unified_fiat_shamir_challenges`.
    let use_fiat_shamir = circuits_filter.is_none();

    // Load the unified circuit and sanity-check its i/t coverage.
    let unified_circuit: GKRCircuitArtifact<BabyBearField> = if USE_GKR_WITH_CACHES {
        delegations_deserialize("../cs/compiled_circuits/unified_reduced_machine_layout_gkr.json")
    } else {
        delegations_deserialize(
            "../cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json",
        )
    };
    let num_unified_teardown_sets = unified_circuit.memory_layout.teardown_sets.len();
    let unified_ram_coverage_bytes: usize =
        (num_unified_teardown_sets << TRACE_LEN_LOG2) << (WORD_BITS as usize);
    assert!(
        unified_ram_coverage_bytes >= vm.cycles_bound * 4 * 4
            || unified_ram_coverage_bytes >= vm.ram_bound_bytes,
        "unified circuit i/t coverage ({unified_ram_coverage_bytes} bytes) is smaller than the \
         run's max RAM footprint; recompile unified with a larger num_inits_and_teardowns_pairs"
    );

    let _ = REDUCED_MACHINE_CIRCUIT_FAMILY_IDX; // touch import

    let prove_unified = circuit_in_filter(&circuits_filter, "unified_reduced_machine");
    let num_unified_calls = sum_executor_family_calls(&vm.counters);
    assert!(num_unified_calls < NUM_CYCLES_PER_CHUNK);

    // --- Build the unified witness trace once (reused for both the Fiat-Shamir memory-cap
    // commitment and the actual proof). `None` only under a filter excluding unified. ---
    let unified_built = if prove_unified {
        Some(build_unified_full_trace(
            &vm,
            &unified_circuit,
            num_unified_teardown_sets,
            num_unified_calls,
            unified_eval_fn,
            true,
            worker,
        ))
    } else {
        None
    };

    // --- External challenges. ---
    // Full proving (no filter) ⇒ derive Fiat-Shamir-consistent challenges so the proof
    // verifies in the full statement verifier, which re-derives them from the memory
    // transcript. Filtered debug runs keep the historical hardcoded challenges (they cannot
    // close the permutation argument anyway, so the FS seed would be ill-defined).
    let external_challenges = if use_fiat_shamir {
        let (unified_trace, _, _) = unified_built
            .as_ref()
            .expect("no circuits filter ⇒ unified circuit is always proved");
        let unified_memory_columns: Vec<&[BabyBearField]> = unified_trace
            .column_major_memory_trace
            .iter()
            .map(|c| &c[..])
            .collect();
        let unified_memory_cap = commit_memory_cap(&unified_memory_columns, level, worker);
        derive_unified_fiat_shamir_challenges::<C>(
            &vm,
            &unified_memory_cap,
            level,
            proof_suffix,
            worker,
            delegation_eval_fns,
            delegation_call_counts,
            prove_empty,
            &circuits_filter,
        )
    } else {
        hardcoded_external_challenges()
    };

    // --- Prove delegations with the now-fixed external challenges. ---
    let mut delegation_outputs: Vec<DelegationProveOutput> = Vec::new();
    if let Some(eval_fn) = delegation_eval_fns.blake {
        delegation_outputs.push(prove_delegation_blake::<C>(
            &vm.snapshotter,
            &vm.tape,
            &vm.expected_final_state(),
            vm.cycles_bound,
            delegation_call_counts.blake,
            &external_challenges,
            level,
            prove_empty,
            false,
            &circuits_filter,
            proof_suffix,
            worker,
            eval_fn,
        ));
    }
    if let Some(eval_fn) = delegation_eval_fns.bigint {
        delegation_outputs.push(prove_delegation_bigint::<C>(
            &vm.snapshotter,
            &vm.tape,
            &vm.expected_final_state(),
            vm.cycles_bound,
            delegation_call_counts.bigint,
            &external_challenges,
            level,
            prove_empty,
            false,
            &circuits_filter,
            proof_suffix,
            worker,
            eval_fn,
        ));
    }
    if let Some(eval_fn) = delegation_eval_fns.keccak {
        delegation_outputs.push(prove_delegation_keccak::<C>(
            &vm.snapshotter,
            &vm.tape,
            &vm.expected_final_state(),
            vm.cycles_bound,
            delegation_call_counts.keccak,
            &external_challenges,
            level,
            prove_empty,
            false,
            &circuits_filter,
            proof_suffix,
            worker,
            eval_fn,
        ));
    }
    if let Some(eval_fn) = delegation_eval_fns.blake_g_function {
        delegation_outputs.push(prove_delegation_blake_g_function::<C>(
            &vm.snapshotter,
            &vm.tape,
            &vm.expected_final_state(),
            vm.cycles_bound,
            delegation_call_counts.blake_g_function,
            &external_challenges,
            level,
            prove_empty,
            false,
            &circuits_filter,
            proof_suffix,
            worker,
            eval_fn,
        ));
    }

    // --- Prove the unified circuit, reusing the pre-built trace. ---
    let (unified_proof, unified_setup_cap) =
        if let Some((unified_full_trace, unified_table_driver, decoder_table)) = unified_built {
            #[cfg(all(feature = "gkr_check_satisfied", any(test, feature = "test")))]
            {
                println!("Checking constraint satisfiability (unified)");
                assert!(
                    crate::tests::gkr::check_satisfied(&unified_circuit, &unified_full_trace),
                    "unified circuit constraint not satisfied"
                );
            }

            let (proof, setup_cap) = prove_built_unified_trace(
                &unified_circuit,
                unified_full_trace,
                &unified_table_driver,
                &decoder_table,
                num_unified_teardown_sets,
                &external_challenges,
                level,
                worker,
            );

            delegations_serialize(
                &proof,
                &format!(
                    "test_proofs/unified_reduced_machine_{}_gkr_proof.json",
                    proof_suffix
                ),
            );

            (Some(proof), Some(setup_cap))
        } else {
            (None, None)
        };

    // --- Accumulator close-check. ---

    let register_final_state_raw = vm
        .register_final_state()
        .map(|el| (el.current_value, split_timestamp(el.last_access_timestamp)));
    let mut permutation_argument_accumulator =
        produce_initial_permutation_product_contribution::<BabyBearField, BabyBearExt4>(
            &register_final_state_raw,
            INITIAL_PC,
            split_timestamp(INITIAL_TIMESTAMP),
            vm.final_pc(),
            split_timestamp(vm.final_timestamp()),
            &external_challenges,
        );
    if let Some(ref p) = unified_proof {
        permutation_argument_accumulator.mul_assign(&p.grand_product_accumulator_computed);
    }
    for d in &delegation_outputs {
        permutation_argument_accumulator.mul_assign(&d.grand_product_factor());
    }

    UnifiedProverOutput {
        unified_proof,
        compiled_unified_circuit: unified_circuit,
        delegation_outputs,
        register_final_state: vm.register_final_state(),
        final_pc: vm.final_pc(),
        final_timestamp: vm.final_timestamp(),
        external_challenges,
        unified_setup_cap,
        permutation_argument_accumulator,
    }
}

/// Memory-only commitment for a set of column-major memory-trace columns, returning the
/// memory tree cap. Uses the same params (`config_for_security_level_under_pessimistic_conjecture`
/// for `trace_len`) that `prove_configured_with_gkr` uses for its in-prove `stage1` memory
/// commitment, so the cap returned here is bit-identical to the one embedded in the proof.
fn commit_memory_cap(
    columns: &[&[BabyBearField]],
    level: SecurityLevel,
    worker: &Worker,
) -> MerkleTreeCapVarLength {
    let trace_len = columns[0].len();
    assert!(trace_len.is_power_of_two());
    let trace_len_log2 = trace_len.trailing_zeros() as usize;
    let prover_config = example_configs::config_for_security_level_under_pessimistic_conjecture(
        trace_len_log2,
        level,
    );
    let twiddles: Twiddles<BabyBearField, Global> = Twiddles::new(trace_len, worker);
    let mem = commit_trace_part::<BabyBearField, DefaultTreeConstructor>(
        columns,
        &twiddles,
        prover_config.lde_factor,
        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
        prover_config.cap_size,
        trace_len_log2,
        worker,
    );
    <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BabyBearField>>::get_cap(&mem.tree)
}

fn unified_register_final_values<C>(vm: &VmRunOutput<C>) -> Vec<FinalRegisterValue>
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    vm.register_final_state()
        .iter()
        .map(|el| FinalRegisterValue {
            value: el.current_value,
            last_access_timestamp: el.last_access_timestamp,
        })
        .collect()
}

fn flatten_merkle_cap(cap: &MerkleTreeCapVarLength) -> Vec<u32> {
    let mut result = Vec::new();
    for cap_element in cap.cap.iter() {
        result.extend_from_slice(cap_element);
    }
    result
}

/// Re-derives the Fiat-Shamir memory seed for the unified circuit exactly as
/// `full_statement_verifier::unified_circuit_statement::verify_full_statement_for_unified_circuit`
/// does, then draws the external challenges from it. Mirrors
/// `trace_and_split::fs_transform_for_permutation_argument` specialised to the unified shape:
/// a single reduced-machine family (one instance), NO separate inits/teardowns section (folded
/// into the unified circuit), and delegations absorbed in the FSV's
/// `DELEGATION_CIRCUITS_SETUP_PARAMS` order (blake, bigint, keccak, blake_g_function) — NOT
/// type-sorted. `trace_and_split`'s version asserts type-sorted order; we mirror the FSV's actual
/// order instead so the seed is guaranteed to match.
#[allow(clippy::too_many_arguments)]
fn derive_unified_fiat_shamir_challenges<C>(
    vm: &VmRunOutput<C>,
    unified_memory_cap: &MerkleTreeCapVarLength,
    level: SecurityLevel,
    proof_suffix: &str,
    worker: &Worker,
    delegation_eval_fns: &DelegationEvalFns,
    delegation_call_counts: &DelegationCallCounts,
    prove_empty: bool,
    circuits_filter: &Option<std::collections::HashSet<String>>,
) -> GKRExternalChallenges<BabyBearField, BabyBearExt4>
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    // Placeholder: `prove_delegation_*` with `compute_only = true` never proves, so this
    // value is unused — those calls only build & return the (challenge-independent) memory
    // trace, which we commit to obtain the FS memory cap.
    let placeholder = hardcoded_external_challenges();

    // Collect the memory caps of exactly the delegations that the prove pass will prove, in the
    // SAME order the unified FSV absorbs them. The FSV absorbs a delegation's type+caps iff
    // `num_circuits > 0` (i.e. it was proved), so we include a cap iff it will be proved
    // (`in_filter && (prove_empty || calls > 0)`) — the same predicate `prove_delegation_*` uses.
    let mut delegation_caps: Vec<(u32, MerkleTreeCapVarLength)> = Vec::new();
    let mut collect =
        |csr: u32, memory_trace: &GKRMemoryOnlyWitnessTrace<BabyBearField, Global, Global>| {
            let columns: Vec<&[BabyBearField]> = memory_trace
                .column_major_trace
                .iter()
                .map(|c| &c[..])
                .collect();
            delegation_caps.push((csr, commit_memory_cap(&columns, level, worker)));
        };

    if let Some(eval_fn) = delegation_eval_fns.blake {
        if circuit_in_filter(circuits_filter, "blake2_with_extended_control")
            && (prove_empty || delegation_call_counts.blake > 0)
        {
            let out = prove_delegation_blake::<C>(
                &vm.snapshotter,
                &vm.tape,
                &vm.expected_final_state(),
                vm.cycles_bound,
                delegation_call_counts.blake,
                &placeholder,
                level,
                prove_empty,
                true,
                circuits_filter,
                proof_suffix,
                worker,
                eval_fn,
            );
            collect(BLAKE2S_DELEGATION_CSR_REGISTER, &out.memory_trace);
        }
    }
    if let Some(eval_fn) = delegation_eval_fns.bigint {
        if circuit_in_filter(circuits_filter, "bigint_with_extended_control")
            && (prove_empty || delegation_call_counts.bigint > 0)
        {
            let out = prove_delegation_bigint::<C>(
                &vm.snapshotter,
                &vm.tape,
                &vm.expected_final_state(),
                vm.cycles_bound,
                delegation_call_counts.bigint,
                &placeholder,
                level,
                prove_empty,
                true,
                circuits_filter,
                proof_suffix,
                worker,
                eval_fn,
            );
            collect(BIGINT_OPS_WITH_CONTROL_CSR_REGISTER, &out.memory_trace);
        }
    }
    if let Some(eval_fn) = delegation_eval_fns.keccak {
        if circuit_in_filter(circuits_filter, "keccak_special5")
            && (prove_empty || delegation_call_counts.keccak > 0)
        {
            let out = prove_delegation_keccak::<C>(
                &vm.snapshotter,
                &vm.tape,
                &vm.expected_final_state(),
                vm.cycles_bound,
                delegation_call_counts.keccak,
                &placeholder,
                level,
                prove_empty,
                true,
                circuits_filter,
                proof_suffix,
                worker,
                eval_fn,
            );
            collect(KECCAK_SPECIAL5_CSR_REGISTER, &out.memory_trace);
        }
    }
    if let Some(eval_fn) = delegation_eval_fns.blake_g_function {
        if circuit_in_filter(circuits_filter, "blake2_g_function")
            && (prove_empty || delegation_call_counts.blake_g_function > 0)
        {
            let out = prove_delegation_blake_g_function::<C>(
                &vm.snapshotter,
                &vm.tape,
                &vm.expected_final_state(),
                vm.cycles_bound,
                delegation_call_counts.blake_g_function,
                &placeholder,
                level,
                prove_empty,
                true,
                circuits_filter,
                proof_suffix,
                worker,
                eval_fn,
            );
            collect(
                BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER,
                &out.memory_trace,
            );
        }
    }

    let register_final_values = unified_register_final_values(vm);
    let seed = fs_transform_for_unified_circuit(
        &register_final_values,
        vm.final_pc(),
        vm.final_timestamp(),
        unified_memory_cap,
        &delegation_caps,
    );

    // MEMORY_DELEGATION_POW_BITS = 0 in the FSV ⇒ no proof-of-work, `pow_challenge` is unused
    // in the derivation. If the FSV's pow-bits ever becomes non-zero, this (and the fixture's
    // `pow_challenge`) must be updated in lockstep.
    GKRExternalChallenges::draw_from_transcript_seed(seed, 0, 0)
}

/// Memory-transcript seed for the unified circuit. Must match
/// `verify_full_statement_for_unified_circuit`'s absorb order exactly (and the
/// `Blake2sBufferingTranscript::<true>` reduced-rounds setting it uses).
fn fs_transform_for_unified_circuit(
    register_final_values: &[FinalRegisterValue],
    final_pc: u32,
    final_timestamp: TimestampScalar,
    unified_memory_cap: &MerkleTreeCapVarLength,
    delegation_memory_caps: &[(u32, MerkleTreeCapVarLength)],
) -> Seed {
    let mut transcript = Blake2sBufferingTranscript::<true>::new();

    // registers
    let mut registers = Vec::with_capacity(32 + 32 * 2);
    for register in register_final_values.iter() {
        registers.push(register.value);
        let (low, high) = split_timestamp(register.last_access_timestamp);
        registers.push(low);
        registers.push(high);
    }
    transcript.absorb(&registers);

    // final pc + timestamp
    let (ts_low, ts_high) = split_timestamp(final_timestamp);
    let mut final_pc_buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
    final_pc_buffer[0] = final_pc;
    final_pc_buffer[1] = ts_low;
    final_pc_buffer[2] = ts_high;
    transcript.absorb(&final_pc_buffer);

    // single reduced-machine family with one instance (no separate inits/teardowns section —
    // it is folded into the unified circuit). The FSV absorbs the family idx unconditionally
    // (num_circuits > 0 is asserted), so we always absorb it here.
    let mut family_buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
    family_buffer[0] = REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32;
    transcript.absorb(&family_buffer);
    transcript.absorb(&flatten_merkle_cap(unified_memory_cap));

    assert_eq!(
        transcript.get_current_buffer_offset(),
        BLAKE2S_BLOCK_SIZE_U32_WORDS
    );

    // delegations, in the FSV's DELEGATION_CIRCUITS_SETUP_PARAMS order (the caller already
    // collected them in that order).
    for (delegation_type, cap) in delegation_memory_caps.iter() {
        let mut buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
        buffer[0] = *delegation_type;
        transcript.absorb(&buffer);
        transcript.absorb(&flatten_merkle_cap(cap));
        assert_eq!(
            transcript.get_current_buffer_offset(),
            BLAKE2S_BLOCK_SIZE_U32_WORDS
        );
    }

    transcript.finalize()
}

pub fn build_unified_full_trace<C>(
    vm: &VmRunOutput<C>,
    unified_circuit: &GKRCircuitArtifact<BabyBearField>,
    num_unified_teardown_sets: usize,
    num_calls: usize,
    eval_fn: fn(
        &mut crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy<
            '_,
            UnifiedRiscvCircuitOracle<'_>,
            BabyBearField,
        >,
    ),
    run_memory_consistency_check: bool,
    worker: &Worker,
) -> (
    GKRFullWitnessTrace<BabyBearField, Global, Global>,
    TableDriver<BabyBearField>,
    Vec<Option<ExecutorFamilyDecoderData>>,
)
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    // Replay the captured trace into the unified destination holder.
    let mut state = vm.snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = vm
        .snapshotter
        .reads_buffer
        .make_range(0..vm.snapshotter.reads_buffer.len());
    let mut replay_ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![UnifiedOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = UnifiedDestinationHolder {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<C>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut replay_ram,
        &vm.tape,
        &mut (),
        vm.cycles_bound,
        &mut tracer,
    );
    assert_eq!(vm.expected_final_state(), state);

    use common_constants::*;
    use cs::gkr_circuits::*;

    let decoders: Vec<Box<dyn OpcodeFamilyDecoder>> = vec![Box::new(UnifiedReducedMachineDecoder)];
    const SUPPORTED_CSRS: &[u16] = &[
        NON_DETERMINISM_CSR as u16,
        BLAKE2S_DELEGATION_CSR_REGISTER as u16,
        BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
        KECCAK_SPECIAL5_CSR_REGISTER as u16,
        BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
    ];
    let mut preprocessing_data = process_binary_into_separate_tables_ext::<
        BabyBearField,
        ReducedMachineDecoderConfig,
        true,
        Global,
    >(
        &vm.text_section,
        &decoders,
        common_constants::ROM_WORD_SIZE,
        SUPPORTED_CSRS,
    );
    let decoder_table = preprocessing_data
        .remove(&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX)
        .expect("UnifiedReducedMachineDecoder must produce a family-128 entry");

    let oracle = UnifiedRiscvCircuitOracle {
        inner: &buffer,
        decoder_table: &decoder_table,
    };
    let unified_table_driver = build_unified_table_driver::<BabyBearField>(&vm.binary);

    // Collect i/t columns sized to the unified circuit's set count.
    let mut unified_inits_and_teardowns = Vec::with_capacity(num_unified_teardown_sets);
    for _ in 0..num_unified_teardown_sets {
        let a = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let b = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let c = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let d = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        unified_inits_and_teardowns.push(([a, b], [c, d]));
    }
    vm.ram
        .collect_inits_and_teardowns_into_columns::<BabyBearField, _>(
            worker,
            TRACE_LEN_LOG2,
            0,
            &mut unified_inits_and_teardowns,
        );

    let memory_trace = if run_memory_consistency_check {
        println!("Computing memory trace (unified)");
        Some(evaluate_gkr_memory_witness_for_executor_family::<
            BabyBearField,
            _,
            _,
            _,
        >(
            unified_circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            worker,
            Some(unified_inits_and_teardowns.clone()),
            Global,
            Global,
        ))
    } else {
        None
    };

    println!("Computing full trace (unified)");
    let unified_full_trace = evaluate_gkr_witness_for_executor_family::<BabyBearField, _, _, _>(
        unified_circuit,
        eval_fn,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &unified_table_driver,
        worker,
        Some(unified_inits_and_teardowns),
        Global,
        Global,
    );

    if let Some(memory_trace) = &memory_trace {
        super::common::ensure_memory_trace_consistency(memory_trace, &unified_full_trace);
    }

    (unified_full_trace, unified_table_driver, decoder_table)
}

/// Prove a *pre-built* unified witness trace: prover config + twiddles, construct &
/// commit the setup, run the GKR prover with the inits/teardowns top-bits. Returns the
/// proof together with the setup-tree cap (the full statement verifier's prepended
/// verification key). Used by both [`prove_unified`] and the unified malicious-proof
/// generator (caller owns serialization).
#[allow(clippy::too_many_arguments)]
pub fn prove_built_unified_trace(
    unified_circuit: &GKRCircuitArtifact<BabyBearField>,
    unified_full_trace: GKRFullWitnessTrace<BabyBearField, Global, Global>,
    unified_table_driver: &TableDriver<BabyBearField>,
    decoder_table: &[Option<ExecutorFamilyDecoderData>],
    num_unified_teardown_sets: usize,
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    level: SecurityLevel,
    worker: &Worker,
) -> (
    GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>,
    MerkleTreeCap<DEFAULT_CAP_SIZE>,
) {
    let trace_len: usize = 1 << TRACE_LEN_LOG2;

    let prover_config = example_configs::config_for_security_level_under_pessimistic_conjecture(
        trace_len.trailing_zeros() as usize,
        level,
    );
    let unified_twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, worker);
    let unified_setup = GKRSetup::construct(
        unified_table_driver,
        decoder_table,
        trace_len,
        unified_circuit,
    );
    let unified_setup_commitment = unified_setup.commit(
        &unified_twiddles,
        prover_config.lde_factor,
        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
        prover_config.cap_size,
        trace_len.trailing_zeros() as usize,
        worker,
    );

    let unified_top_bits: Vec<u32> = (0..num_unified_teardown_sets).map(|i| i as u32).collect();

    println!("Trying to prove (unified)");
    let now = std::time::Instant::now();
    let proof = prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
        unified_circuit,
        external_challenges,
        unified_full_trace,
        &unified_setup,
        &unified_setup_commitment,
        &unified_twiddles,
        &prover_config,
        unified_top_bits,
        trace_len,
        worker,
    );
    println!("Unified proving time is {:?}", now.elapsed());

    // The setup-tree cap is the FSV's prepended verification key (matched against every
    // proof's embedded setup cap). cap_size == DEFAULT_CAP_SIZE, so `into_fixed_holder` fits.
    let setup_cap =
        <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BabyBearField>>::get_cap(
            &unified_setup_commitment.tree,
        )
        .into_fixed_holder::<DEFAULT_CAP_SIZE>();

    (proof, setup_cap)
}

/// Total executor cycle count. The unified counter (`DelegationsAndUnifiedCounters`)
/// exposes this directly under `REDUCED_MACHINE_CIRCUIT_FAMILY_IDX` (sum of all
/// per-family cycles); the per-family counter would need a 6-way sum, but the
/// unified mode is always driven by the unified counter type, so we just go
/// through the one canonical accessor.
fn sum_executor_family_calls<C: Counters + Copy + std::fmt::Debug>(counters: &C) -> usize {
    counters.get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>()
}
