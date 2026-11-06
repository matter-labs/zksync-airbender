use super::common::*;
use crate::cs::definitions::TimestampScalar;
use crate::cs::gkr_compiler::GKRCircuitArtifact;
use crate::definitions::{FinalRegisterValue, MerkleTreeCap, SecurityLevel, DEFAULT_CAP_SIZE};
use crate::gkr::prover::prove_configured_with_gkr_with_backends;
use crate::gkr::prover::setup::GKRSetup;
use crate::gkr::prover::OperationMode;
use crate::gkr::prover::{GKRExternalChallenges, GKRProof};
use crate::gkr::witness_gen::family_circuits::{
    build_unified_table_driver, evaluate_gkr_memory_witness_for_executor_family,
    evaluate_gkr_witness_for_executor_family,
};
use crate::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;
use crate::merkle_trees::DefaultTreeConstructor;
use crate::merkle_trees::MerkleTreeCapVarLength;
use crate::tests::gkr::GKRFullWitnessTrace;
use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
use cs::gkr_circuits::ExecutorFamilyDecoderData;
use cs::tables::TableDriver;
use cs::utils::split_timestamp;
use fft::Twiddles;
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{Counters, ReplayBuffer};
use riscv_transpiler::witness::data_structs::UnifiedOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::UnifiedDestinationHolder;
use std::alloc::Global;
use transcript::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS;
use transcript::{Blake2sBufferingTranscript, Blake2sTranscript, Seed};
use worker::Worker;

/// Memory/delegation PoW bits the FSV expects: `verifier_common::memory_delegation_pow_bits`
/// = `security_bits - (BABYBEAR_EXT4_SIZE_LOG2 - MAX_PERMUTATION_ELEMENTS_LOG2 - 2)`
/// = `security_bits - (123 - 40 - 2)`. `prover` cannot depend on `verifier_common` (it is the
/// other way round), so this mirrors the derivation; the FSV test asserts the fixture's bits
/// equal `MEMORY_DELEGATION_POW_BITS`, so drift fails loudly there.
pub(super) const fn memory_delegation_pow_bits(level: SecurityLevel) -> u32 {
    level.security_bits().saturating_sub(123 - 40 - 2) as u32
}

fn flatten_merkle_cap(cap: &MerkleTreeCapVarLength) -> Vec<u32> {
    let mut result = Vec::new();
    for cap_element in cap.cap.iter() {
        result.extend_from_slice(cap_element);
    }
    result
}

/// Memory-transcript seed for the unified circuit. Must match
/// `verify_full_statement_for_unified_circuit`'s absorb order exactly (and the
/// `Blake2sBufferingTranscript::<true>` reduced-rounds setting it uses).
pub(super) fn fs_transform_for_unified_circuit(
    register_final_values: &[FinalRegisterValue],
    final_pc: u32,
    final_timestamp: TimestampScalar,
    unified_memory_cap: &MerkleTreeCapVarLength,
    inits_and_teardowns_top_bits: &[u32],
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
    // it is folded into the unified circuit). Per instance the FSV absorbs a block holding the
    // family idx + this instance's inits/teardowns `top_bits`, then the memory caps — mirroring
    // `trace_and_split::fs_transform_unified_for_permutation_argument`. Binding `top_bits` into
    // the seed (not just the memory columns) is the soundness fix for multi-instance.
    let mut family_buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
    family_buffer[0] = REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32;
    assert!(inits_and_teardowns_top_bits.len() < BLAKE2S_BLOCK_SIZE_U32_WORDS);
    family_buffer[1..][..inits_and_teardowns_top_bits.len()]
        .copy_from_slice(inits_and_teardowns_top_bits);
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

/// Inits/teardowns columns of the unified circuit, one `(top_bits, columns)` group.
pub type UnifiedInitsAndTeardowns = (
    Vec<u32>,
    Vec<([Vec<BabyBearField>; 2], [Vec<BabyBearField>; 2])>,
);

/// Collect the unified circuit's inits/teardowns the way production does
/// (`program_prover::unified`): only the touched `trace_len`-word RAM chunks, each tagged with
/// its chunk index as `top_bits`, grouped (and padded) into sets of the circuit's teardown-set
/// count. The harness proves a single unified instance, so every touched chunk must fit in
/// one group — asserted rather than silently dropping teardowns (which breaks the permutation
/// argument: e.g. multi_family_smoke's stack/data sit at 64–68 MiB, outside a 0-based pair of
/// 2^23-word chunks).
fn collect_unified_inits_and_teardowns<C>(
    vm: &VmRunOutput<C>,
    unified_circuit: &GKRCircuitArtifact<BabyBearField>,
    worker: &Worker,
) -> UnifiedInitsAndTeardowns
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    let num_teardown_sets = unified_circuit.memory_layout.teardown_sets.len();
    let mut groups = vm
        .ram
        .collect_inits_and_teardowns_sets::<BabyBearField, Global>(
            worker,
            unified_circuit.trace_len.trailing_zeros() as usize,
            num_teardown_sets,
            None,
        );
    assert_eq!(
        groups.len(),
        1,
        "the harness proves one unified instance, but the run touched RAM needing {} groups of \
         {num_teardown_sets} chunks",
        groups.len()
    );
    groups.pop().unwrap()
}

/// Replay the captured VM run into the per-cycle unified oracle data.
pub fn replay_unified_cycles<C>(
    vm: &VmRunOutput<C>,
    num_calls: usize,
) -> Vec<UnifiedOpcodeTracingDataWithTimestamp>
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    let mut state = vm.snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = vm
        .snapshotter
        .reads_buffer
        .make_range(0..vm.snapshotter.reads_buffer.len());
    let mut replay_ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![UnifiedOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = [&mut buffer[..]];
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
    buffer
}

pub fn build_unified_full_trace<C>(
    vm: &VmRunOutput<C>,
    unified_circuit: &GKRCircuitArtifact<BabyBearField>,
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
    Vec<u32>,
)
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    let buffer = replay_unified_cycles(vm, num_calls);

    use common_constants::*;
    use cs::gkr_circuits::*;

    let decoders: Vec<Box<dyn OpcodeFamilyDecoder>> = vec![Box::new(UnifiedReducedMachineDecoder)];
    const SUPPORTED_CSRS: &[u16] = &[
        NON_DETERMINISM_CSR as u16,
        BLAKE2S_DELEGATION_CSR_REGISTER as u16,
        BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
        BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
        KECCAK_SPECIAL5_CSR_REGISTER as u16,
        KECCAK_THETA_RHO_CSR_REGISTER as u16,
        KECCAK_COLUMN_PARITY_CSR_REGISTER as u16,
        KECCAK_CHI5_CSR_REGISTER as u16,
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

    let (inits_and_teardowns_top_bits, unified_inits_and_teardowns) =
        collect_unified_inits_and_teardowns(vm, unified_circuit, worker);

    let memory_trace = if run_memory_consistency_check {
        println!("Computing memory trace (unified)");
        Some(evaluate_gkr_memory_witness_for_executor_family::<
            BabyBearField,
            _,
            _,
            _,
        >(
            unified_circuit,
            unified_circuit.trace_len,
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
        unified_circuit.trace_len,
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

    (
        unified_full_trace,
        unified_table_driver,
        decoder_table,
        inits_and_teardowns_top_bits,
    )
}

/// Prove a *pre-built* unified witness trace: prover config + twiddles, construct &
/// commit the setup, run the GKR prover with the inits/teardowns top-bits. Returns the
/// proof together with the setup-tree cap (the full statement verifier's prepended
/// verification key). Used by the unified malicious-proof
/// generator (caller owns serialization).
pub fn prove_built_unified_trace(
    unified_circuit: &GKRCircuitArtifact<BabyBearField>,
    unified_full_trace: GKRFullWitnessTrace<BabyBearField, Global, Global>,
    unified_table_driver: &TableDriver<BabyBearField>,
    decoder_table: &[Option<ExecutorFamilyDecoderData>],
    inits_and_teardowns_top_bits: Vec<u32>,
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    level: SecurityLevel,
    worker: &Worker,
) -> (
    GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>,
    MerkleTreeCap<DEFAULT_CAP_SIZE>,
) {
    let trace_len: usize = unified_circuit.trace_len;

    // the circuit definition's config of the current soundness mode
    let prover_config = super::common::fixture_prover_config("unified_reduced_machine", level);
    assert_eq!(1usize << prover_config.trace_len_log2, trace_len);
    let unified_twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, worker);
    let unified_setup = GKRSetup::construct(
        unified_table_driver,
        decoder_table,
        trace_len,
        unified_circuit,
    );
    let unified_setup_commitment =
        unified_setup.commit_for_config(&unified_twiddles, &prover_config, worker);

    println!("Trying to prove (unified)");
    let now = std::time::Instant::now();
    let proof = prove_configured_with_gkr_with_backends::<
        BabyBearField,
        BabyBearExt4,
        DefaultTreeConstructor,
        Blake2sTranscript,
        _,
        _,
    >(
        unified_circuit,
        external_challenges,
        unified_full_trace,
        &unified_setup,
        &unified_setup_commitment,
        &unified_twiddles,
        &prover_config,
        OperationMode::MultipleChunks,
        inits_and_teardowns_top_bits,
        trace_len,
        &crate::gkr::prover::WorkStealingBackend,
        &crate::gkr::prover::DefaultBabyBearGKRBackend::default(),
        worker,
    );
    println!("Unified proving time is {:?}", now.elapsed());

    // The setup-tree cap is the FSV's prepended verification key (matched against every
    // proof's embedded setup cap). cap_size == DEFAULT_CAP_SIZE, so `into_fixed_holder` fits.
    let setup_cap = unified_setup_commitment
        .get_cap()
        .into_fixed_holder::<DEFAULT_CAP_SIZE>();

    (proof, setup_cap)
}
