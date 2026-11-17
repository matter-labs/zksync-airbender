use super::*;
use prover::tests::gkr::orchestration::canonical_fixtures::{
    capture_canonical_inputs, CanonicalCircuit, CanonicalInputs, CanonicalTrace,
};
use prover::tests::gkr::orchestration::common::hardcoded_external_challenges;

pub(super) fn default_fixture_device_allocator_block_log_size() -> u32 {
    gpu_prover_context::ProverContextConfig::default().allocator_block_log_size
}

pub(super) fn canonical_circuit_type(circuit: CanonicalCircuit) -> CircuitType {
    use CanonicalCircuit::*;
    match circuit {
        AddSubLuiAuipcMop => CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
        )),
        JumpBranchSlt => CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::JumpBranchSlt,
        )),
        ShiftBinop => CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::ShiftBinary,
        )),
        UnsignedMulDiv => CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::MulDivUnsigned,
        )),
        MemWordOnly => CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreWordOnly,
        )),
        MemSubwordOnly => CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
        )),
        InitsAndTeardowns => CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
        UnifiedReducedMachine | Compression => CircuitType::Unrolled(UnrolledCircuitType::Unified),
        CompressionFinal => CircuitType::Unrolled(UnrolledCircuitType::Unified22),
        BigintWithExtendedControl => {
            CircuitType::Delegation(DelegationCircuitType::BigIntWithControl)
        }
        Blake2WithExtendedControl => {
            CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression)
        }
        KeccakSpecial5 => CircuitType::Delegation(DelegationCircuitType::KeccakSpecial5),
        KeccakColumnParity => CircuitType::Delegation(DelegationCircuitType::KeccakColumnParity),
        KeccakThetaRho => CircuitType::Delegation(DelegationCircuitType::KeccakThetaRho),
        KeccakChi5 => CircuitType::Delegation(DelegationCircuitType::KeccakChi5),
    }
}

fn assert_external_challenges_eq(
    a: &GKRExternalChallenges<BF, E4>,
    b: &GKRExternalChallenges<BF, E4>,
) {
    assert_eq!(
        a.permutation_argument_linearization_challenges,
        b.permutation_argument_linearization_challenges
    );
    assert_eq!(
        a.permutation_argument_additive_part,
        b.permutation_argument_additive_part
    );
}

fn build_input_fixture(
    circuit: CanonicalCircuit,
    prover_config: ProverConfig,
    committed: &GKRProof<BF, E4, DefaultTreeConstructor>,
) -> BasicUnrolledFixture {
    let worker = Worker::new_with_num_threads(8);
    let root = test_artifact_path("");
    let CanonicalInputs {
        compiled_circuit,
        table_driver,
        decoder_table,
        trace,
        inits_and_teardowns,
        ..
    } = capture_canonical_inputs(&root, circuit, &worker);
    let circuit_type = canonical_circuit_type(circuit);
    assert_eq!(compiled_circuit.trace_len, circuit_type.get_domain_size());
    assert_eq!(
        1 << prover_config.trace_len_log2,
        compiled_circuit.trace_len
    );
    let top_bits = inits_and_teardowns
        .as_ref()
        .map(|ram| ram.top_bits.clone())
        .unwrap_or_default();
    assert_eq!(top_bits, committed.inits_and_teardowns_top_bits);
    let external_challenges = hardcoded_external_challenges();
    assert_external_challenges_eq(&external_challenges, &committed.external_challenges);

    // Construct raw setup columns only. Their LDE and commitment run on the GPU.
    let setup = (circuit != CanonicalCircuit::InitsAndTeardowns).then(|| {
        CpuGKRSetup::construct(
            &table_driver,
            &decoder_table,
            compiled_circuit.trace_len,
            &compiled_circuit,
            &worker,
        )
    });
    drop(table_driver);
    let context = make_test_context_with_device_allocator_block_log_size(
        None,
        1024,
        default_fixture_device_allocator_block_log_size(),
    );
    let geometry =
        BaseCommitmentGeometry::from_config(&prover_config, BaseColumns::of(&compiled_circuit));
    let gpu_setup_host = setup.as_ref().map(|setup| {
        Arc::new(GpuGKRSetupHost::precompute_for_geometry(setup, geometry, &context).unwrap())
    });
    drop(setup);
    let witness_gen_data = decoder_table
        .iter()
        .map(|entry| entry.unwrap_or_default())
        .collect_vec();
    let decoder_table_host = make_decoder_table_host_for_test(&witness_gen_data);
    drop(decoder_table);
    let tracing_data_host = if matches!(&trace, CanonicalTrace::InitsAndTeardowns) {
        None
    } else {
        Some(match trace {
            CanonicalTrace::NonMemory(rows) => make_non_memory_tracing_host_for_test(rows),
            CanonicalTrace::Memory(rows) => make_memory_tracing_host_for_test(rows),
            CanonicalTrace::Unified(rows) => make_unified_tracing_host_for_test(rows),
            CanonicalTrace::Bigint(rows) => make_delegation_tracing_host_for_test(
                DelegationCircuitType::BigIntWithControl,
                rows,
            ),
            CanonicalTrace::Blake2WithCompression(rows) => make_delegation_tracing_host_for_test(
                DelegationCircuitType::Blake2WithCompression,
                rows,
            ),
            CanonicalTrace::KeccakSpecial5(rows) => {
                make_delegation_tracing_host_for_test(DelegationCircuitType::KeccakSpecial5, rows)
            }
            CanonicalTrace::KeccakColumnParity(rows) => make_delegation_tracing_host_for_test(
                DelegationCircuitType::KeccakColumnParity,
                rows,
            ),
            CanonicalTrace::KeccakThetaRho(rows) => {
                make_delegation_tracing_host_for_test(DelegationCircuitType::KeccakThetaRho, rows)
            }
            CanonicalTrace::KeccakChi5(rows) => {
                make_delegation_tracing_host_for_test(DelegationCircuitType::KeccakChi5, rows)
            }
            CanonicalTrace::InitsAndTeardowns => unreachable!(),
        })
    };
    let inits_and_teardowns_host = inits_and_teardowns.map(|ram| {
        let (pages, values, timestamps) =
            inits_and_teardowns::build_inits_and_teardowns_pages_for_selected_sets_for_test(
                &[ram.touched],
                compiled_circuit.trace_len.trailing_zeros(),
                &ram.top_bits,
            );
        inits_and_teardowns::build_inits_and_teardowns_trace_host_for_test(
            &pages,
            &values,
            &timestamps,
            &ram.top_bits,
        )
    });
    BasicUnrolledFixture {
        context,
        circuit_type,
        gkr_programs: Arc::new(
            GkrPrograms::compile(circuit_type, Arc::new(compiled_circuit.clone())).unwrap(),
        ),
        compiled_circuit,
        external_challenges,
        final_trace_size_log_2: prover_config.sumcheck_explicit_output_size_log_2 as u32,
        prover_config,
        gpu_setup_host,
        decoder_table_host,
        tracing_data_host,
        memory_tree_caps: Vec::new(),
        inits_and_teardowns_host,
        inits_and_teardowns_top_bits: Some(top_bits),
    }
}

pub(super) fn assert_memory_caps_match_committed(
    caps: &[MerkleTreeCapVarLength],
    proof: &GKRProof<BF, E4, DefaultTreeConstructor>,
) {
    let actual: Vec<_> = caps
        .iter()
        .flat_map(|cap| cap.cap.iter().copied())
        .collect();
    assert_eq!(
        actual, proof.whir_proof.memory_commitment.commitment.cap.cap,
        "GPU memory cap differs from committed proof"
    );
}

pub(super) fn prepare_canonical_proof_fixture(
    circuit: CanonicalCircuit,
    mode: circuit_common::SoundnessMode,
) -> BasicUnrolledProofFixture {
    let committed = load_committed_proof(circuit, mode);
    let config = circuit.prover_config(&test_artifact_path(""), mode);
    let mut base = build_input_fixture(circuit, config, &committed.proof);
    let geometry = BaseCommitmentGeometry::from_config(
        &base.prover_config,
        BaseColumns::of(&base.compiled_circuit),
    );
    let caps = geometry_proof::gpu_memory_caps(&base, geometry);
    assert_memory_caps_match_committed(&caps, &committed.proof);
    base.memory_tree_caps = caps;
    BasicUnrolledProofFixture {
        base,
        committed_proof: committed.proof,
        committed_proof_bytes: committed.bytes,
    }
}

pub(super) fn make_delegation_tracing_host_for_test<W>(
    circuit_type: DelegationCircuitType,
    buffer: Vec<W>,
) -> TracingDataHost<Global>
where
    W: gpu_trace::trace::tracing_data::DelegationTracingDataHostSource,
{
    let trace = gpu_trace::witness::trace_delegation::DelegationTraceHost::<W, Global> {
        chunks: vec![Arc::new(buffer)],
    };
    TracingDataHost::Delegation(W::get(circuit_type, trace))
}
