//! Setup and memory-commitment handlers against the CPU primitives they
//! dispatch to.

mod commitments {
    use crate::host_storage::CpuTraceAllocator;
    use crate::jobs::*;
    use crate::upstream::{
        Blake2sGFunctionAbiDescription, DefaultTreeConstructor, MerkleTreeCapVarLength,
        TwiddleSetOps, UnrolledCircuitWitnessEvalFn,
    };
    use execution_prover::backend::CircuitPrecomputation;
    use execution_prover::messages::{
        MemoryCommitmentRequest, SetupInitializationRequest, WorkRequest, WorkResult,
    };
    use execution_prover::prover_config;
    use execution_prover::setup::{build_delegation_setup, build_unrolled_setup};
    use execution_prover::MachineType;
    use execution_prover_model::caps::{join_memory_caps, split_memory_cap};
    use execution_prover_model::circuit_type::{
        CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledNonMemoryCircuitType,
    };
    use execution_prover_model::trace::{
        ChunkedTraceHolder, DelegationTracingDataHost, TracingDataHost, UnrolledTracingDataHost,
    };
    use prover::definitions::SecurityLevel;
    use riscv_transpiler::witness::data_structs::NonMemoryOpcodeTracingDataWithTimestamp;
    use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
    use std::alloc::Global;
    use std::sync::OnceLock;

    const SECURITY_LEVEL: SecurityLevel = SecurityLevel::Sec100;
    /// The smallest delegation circuit, so the real commitments below cost as
    /// little as a production-dimension commitment can.
    const CIRCUIT: CircuitType = CircuitType::Delegation(DelegationCircuitType::Blake2GFunction);

    fn worker() -> &'static Worker {
        static WORKER: OnceLock<Worker> = OnceLock::new();
        WORKER.get_or_init(Worker::new)
    }

    /// Built once per test binary: compiling a circuit is the expensive part.
    fn precomputations() -> &'static CpuCircuitPrecomputations {
        static PRECOMPUTATIONS: OnceLock<CpuCircuitPrecomputations> = OnceLock::new();
        PRECOMPUTATIONS.get_or_init(|| {
            let setup = build_delegation_setup(DelegationCircuitType::Blake2GFunction, worker());
            CpuCircuitPrecomputations::from_canonical(CIRCUIT, setup)
        })
    }

    /// A real family setup, so the decoder rows and the padding PC under test
    /// are the ones a registered binary actually produces.
    fn family_precomputations() -> &'static CpuCircuitPrecomputations {
        static PRECOMPUTATIONS: OnceLock<CpuCircuitPrecomputations> = OnceLock::new();
        PRECOMPUTATIONS.get_or_init(|| {
            // Padded exactly as the pipeline pads before registering a binary:
            // the memory families assert on the padded ROM width.
            let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
            let (_, binary) =
                setups::read_and_pad_binary(&root.join("examples/hashed_fibonacci/app.bin"));
            let (_, text) =
                setups::read_and_pad_binary(&root.join("examples/hashed_fibonacci/app.text"));
            let circuit_type =
                UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop);
            let setup = build_unrolled_setup(
                MachineType::FullUnsigned,
                circuit_type,
                &binary,
                &text,
                worker(),
            );
            CpuCircuitPrecomputations::from_canonical(CircuitType::Unrolled(circuit_type), setup)
        })
    }

    fn empty_delegation_trace() -> TracingDataHost<CpuTraceAllocator> {
        TracingDataHost::Delegation(DelegationTracingDataHost::Blake2GFunction(
            ChunkedTraceHolder { chunks: Vec::new() },
        ))
    }

    #[test]
    fn a_setup_cap_is_published_only_after_initialization() {
        let jobs = CpuJobs::default();
        let precomputations = precomputations().clone();
        // The circuit has setup columns, so an absent cap here can only mean the
        // setup job has not run — which is what the shared barrier waits for.
        assert!(precomputations.has_setup_columns());

        let request = SetupInitializationRequest {
            batch_id: 1,
            circuit_type: CIRCUIT,
            sequence_id: 0,
            precomputations: precomputations.clone(),
            security_level: SECURITY_LEVEL,
        };
        let result = setup::run(&jobs, request, worker());
        assert_eq!(result.batch_id, 1);
        assert_eq!(result.circuit_type, CIRCUIT);
        assert_eq!(result.sequence_id, 0);
        assert!(precomputations.setup_cap().is_some());
    }

    #[test]
    fn the_setup_cap_matches_a_direct_commitment() {
        let jobs = CpuJobs::default();
        let precomputations = precomputations().clone();
        let config = prover_config(CIRCUIT, SECURITY_LEVEL);
        let request = SetupInitializationRequest {
            batch_id: 2,
            circuit_type: CIRCUIT,
            sequence_id: 0,
            precomputations: precomputations.clone(),
            security_level: SECURITY_LEVEL,
        };
        setup::run(&jobs, request, worker());

        let twiddles = jobs.twiddles(precomputations.trace_len(), worker());
        let expected = precomputations
            .setup_columns()
            .commit::<DefaultTreeConstructor>(
                twiddles.plain(),
                config.lde_factor,
                config.whir_schedule.whir_steps_schedule[0],
                config.cap_size,
                precomputations.trace_len_log2(),
                worker(),
            )
            .get_cap();
        let cap = precomputations.setup_cap().unwrap();
        assert_eq!(cap.cap.len(), config.cap_size);
        assert!(cap.cap.iter().any(|digest| digest != &[0u32; 8]));
        assert_eq!(cap.cap, expected.cap);
    }

    #[test]
    fn memory_caps_match_the_direct_primitive_and_split_per_coset() {
        let jobs = CpuJobs::default();
        let precomputations = precomputations().clone();
        let config = prover_config(CIRCUIT, SECURITY_LEVEL);

        let request = WorkRequest::MemoryCommitment(MemoryCommitmentRequest {
            batch_id: 3,
            circuit_type: CIRCUIT,
            sequence_id: 7,
            precomputations: precomputations.clone(),
            inits_and_teardowns: None,
            tracing_data: Some(empty_delegation_trace()),
            security_level: SECURITY_LEVEL,
        });
        let WorkResult::MemoryCommitment(result) = jobs.execute(request, worker()).unwrap() else {
            panic!("a memory commitment request must produce a memory commitment result");
        };
        assert_eq!(result.batch_id, 3);
        assert_eq!(result.sequence_id, 7);
        assert_eq!(result.circuit_type, CIRCUIT);
        assert!(
            result.tracing_data.is_some(),
            "trace ownership must come back in the completion"
        );

        let twiddles = jobs.twiddles(precomputations.trace_len(), worker());
        // The delegation oracle pads a short chunk to the domain, so an empty
        // instance is a legal commitment input.
        let no_rows: &[Blake2sGFunctionDelegationWitness] = &[];
        let expected = crate::upstream::commit_memory_tree_for_delegation_circuit::<
            crate::upstream::BF,
            crate::upstream::E4,
            DefaultTreeConstructor,
            Global,
            Global,
            Blake2sGFunctionAbiDescription,
            _,
            _,
            _,
            _,
            _,
        >(
            jobs.backend(),
            precomputations.compiled_circuit(),
            no_rows,
            &*twiddles,
            &config,
            worker(),
        );

        assert_eq!(result.merkle_tree_caps.len(), config.lde_factor);
        assert_eq!(expected.cap.len(), config.cap_size);
        assert!(expected.cap.iter().any(|digest| digest != &[0u32; 8]));
        let rejoined =
            join_memory_caps(&result.merkle_tree_caps, config.lde_factor, config.cap_size).unwrap();
        assert_eq!(
            rejoined.cap, expected.cap,
            "per-coset caps must rebuild the canonical flat cap the primitive produced"
        );
        assert_eq!(
            result.merkle_tree_caps,
            split_memory_cap(&expected, config.lde_factor, config.cap_size).unwrap()
        );
    }

    /// The completion has to hand every block back: the adapter may borrow or
    /// flatten while it commits, but nothing may outlive the request.
    #[test]
    fn a_committed_trace_returns_every_block() {
        let jobs = CpuJobs::default();
        let rows_per_chunk = 3;
        let chunks: Vec<_> = (0..2)
            .map(|_| {
                let allocator = CpuTraceAllocator::new(1 << 16);
                let mut chunk = Vec::with_capacity_in(rows_per_chunk, allocator);
                for _ in 0..rows_per_chunk {
                    // Plain `repr(C)` data with no drop glue; the rows only
                    // have to be identical on both sides, not meaningful.
                    chunk.push(unsafe { std::mem::zeroed::<Blake2sGFunctionDelegationWitness>() });
                }
                std::sync::Arc::new(chunk)
            })
            .collect();
        let trace = TracingDataHost::Delegation(DelegationTracingDataHost::Blake2GFunction(
            ChunkedTraceHolder { chunks },
        ));
        let request = WorkRequest::MemoryCommitment(MemoryCommitmentRequest {
            batch_id: 6,
            circuit_type: CIRCUIT,
            sequence_id: 0,
            precomputations: precomputations().clone(),
            inits_and_teardowns: None,
            tracing_data: Some(trace),
            security_level: SECURITY_LEVEL,
        });
        let WorkResult::MemoryCommitment(result) = jobs.execute(request, worker()).unwrap() else {
            panic!("a memory commitment request must produce a memory commitment result");
        };
        let returned = result.tracing_data.expect("trace ownership comes back");
        assert_eq!(returned.into_allocators().len(), 2);
    }

    /// A family keeps the decoder rows with their holes and its padding PC:
    /// the canonical dense view defaults an absent row, and a defaulted row is
    /// not the same row.
    #[test]
    fn a_family_keeps_its_decoder_holes_and_padding_pc() {
        let precomputations = family_precomputations();
        let decoder_table = precomputations.decoder_table();
        assert!(!decoder_table.is_empty());
        assert!(
            decoder_table.iter().any(|entry| entry.is_none()),
            "a family's decoder table should not be dense for a real binary"
        );
        let Some(UnrolledCircuitWitnessEvalFn::NonMemory {
            default_pc_value_in_padding,
            ..
        }) = precomputations.witness_eval_fn()
        else {
            panic!("a non-memory family carries a non-memory evaluator");
        };
        assert_eq!(
            precomputations.default_pc_value_in_padding(),
            *default_pc_value_in_padding
        );
    }

    /// The non-memory family arm, against the same primitive with the same
    /// decoder rows and padding PC.
    #[test]
    fn family_memory_caps_match_the_direct_primitive() {
        let jobs = CpuJobs::default();
        let precomputations = family_precomputations().clone();
        let circuit_type = precomputations.circuit_type();
        let config = prover_config(circuit_type, SECURITY_LEVEL);
        let trace: TracingDataHost<CpuTraceAllocator> =
            TracingDataHost::Unrolled(UnrolledTracingDataHost::NonMemory(ChunkedTraceHolder {
                chunks: Vec::new(),
            }));
        let request = WorkRequest::MemoryCommitment(MemoryCommitmentRequest {
            batch_id: 7,
            circuit_type,
            sequence_id: 0,
            precomputations: precomputations.clone(),
            inits_and_teardowns: None,
            tracing_data: Some(trace),
            security_level: SECURITY_LEVEL,
        });
        let WorkResult::MemoryCommitment(result) = jobs.execute(request, worker()).unwrap() else {
            panic!("a memory commitment request must produce a memory commitment result");
        };

        let twiddles = jobs.twiddles(precomputations.trace_len(), worker());
        let no_rows: &[NonMemoryOpcodeTracingDataWithTimestamp] = &[];
        let expected = crate::upstream::commit_memory_tree_for_unrolled_nonmem_circuits::<
            crate::upstream::BF,
            crate::upstream::E4,
            DefaultTreeConstructor,
            Global,
            Global,
            _,
        >(
            jobs.backend(),
            precomputations.compiled_circuit(),
            no_rows,
            &*twiddles,
            &config,
            precomputations.default_pc_value_in_padding(),
            precomputations.decoder_table(),
            worker(),
        );
        assert_eq!(expected.cap.len(), config.cap_size);
        assert!(expected.cap.iter().any(|digest| digest != &[0u32; 8]));
        assert_eq!(
            result.merkle_tree_caps,
            split_memory_cap(&expected, config.lde_factor, config.cap_size).unwrap()
        );
    }

    #[test]
    #[should_panic(expected = "received a trace of a different shape")]
    fn a_mismatched_trace_shape_is_refused() {
        let jobs = CpuJobs::default();
        let request = WorkRequest::MemoryCommitment(MemoryCommitmentRequest {
            batch_id: 4,
            circuit_type: CircuitType::Delegation(DelegationCircuitType::KeccakSpecial5),
            sequence_id: 0,
            precomputations: precomputations().clone(),
            inits_and_teardowns: None,
            tracing_data: Some(empty_delegation_trace()),
            security_level: SECURITY_LEVEL,
        });
        let _ = jobs.execute(request, worker());
    }

    #[test]
    fn the_executor_seam_serves_setup_requests() {
        let jobs = CpuJobs::default();
        let request = WorkRequest::SetupInitialization(SetupInitializationRequest {
            batch_id: 5,
            circuit_type: CIRCUIT,
            sequence_id: 0,
            precomputations: precomputations().clone(),
            security_level: SECURITY_LEVEL,
        });
        assert!(RequestExecutor::<CpuTraceAllocator, _>::execute(&jobs, request, worker()).is_ok());
    }

    /// The permutation is only the identity for the production LDE factor of two;
    /// this pins it at four distinct cosets so the conversion cannot silently
    /// degrade into "copy the segments in order".
    #[test]
    fn four_distinct_cosets_are_not_permuted_by_identity() {
        let digest = |value: u32| [value; 8];
        let flat = MerkleTreeCapVarLength {
            cap: vec![
                digest(0),
                digest(1),
                digest(2),
                digest(3),
                digest(4),
                digest(5),
                digest(6),
                digest(7),
            ],
        };
        let per_coset = split_memory_cap(&flat, 4, 8).unwrap();
        // canonical segment p holds natural coset bitreverse(p, 2): 0,2,1,3.
        assert_eq!(per_coset[0].cap, vec![digest(0), digest(1)]);
        assert_eq!(per_coset[2].cap, vec![digest(2), digest(3)]);
        assert_eq!(per_coset[1].cap, vec![digest(4), digest(5)]);
        assert_eq!(per_coset[3].cap, vec![digest(6), digest(7)]);
        assert_eq!(join_memory_caps(&per_coset, 4, 8).unwrap().cap, flat.cap);
    }
}

/// Per-circuit proofs, against the same primitives composed the way the legacy
/// CPU prover composes them, and compared through the verifier's own
/// flattening.
mod proofs {
    use crate::adapters::inits_and_teardowns::TeardownColumns;
    use crate::host_storage::CpuTraceAllocator;
    use crate::jobs::*;
    use crate::precomputations::CpuCircuitPrecomputations;
    use crate::upstream::{
        bigint_witness_eval_fn, blake2_g_function_witness_eval_fn,
        blake2_with_compression_witness_eval_fn, evaluate_gkr_witness_for_delegation_circuit,
        evaluate_gkr_witness_for_executor_family, evaluate_init_and_teardown_memory_witness,
        keccak_special5_witness_eval_fn, prove_configured_with_gkr_with_backends,
        BigintAbiDescription, Blake2sGFunctionAbiDescription, Blake2sRoundFunctionAbiDescription,
        Blake2sTranscript, CommitmentMode, DefaultTreeConstructor, DelegationOracle,
        GKRExternalChallenges, GKRFullWitnessTrace, KeccakSpecial5AbiDescription,
        MemoryCircuitOracle, NonMemoryCircuitOracle, UnifiedRiscvCircuitOracle,
        UnrolledCircuitWitnessEvalFn, BF, E4,
    };
    use execution_prover::backend::CircuitPrecomputation;
    use execution_prover::messages::{
        MemoryCommitmentRequest, ProofRequest, ScheduledProof, SetupInitializationRequest,
        WorkRequest, WorkResult,
    };
    use execution_prover::prover_config;
    use execution_prover::setup::{
        build_delegation_setup, build_inits_and_teardowns_setup, build_unified_setup,
        build_unrolled_setup,
    };
    use execution_prover::MachineType;
    use execution_prover_model::circuit_type::{
        CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
        UnrolledNonMemoryCircuitType,
    };
    use execution_prover_model::trace::{
        ChunkedTraceHolder, DelegationTracingDataHost, InitsAndTeardownsTraceHost, TracingDataHost,
        UnrolledTracingDataHost,
    };
    use field::Field;
    use prover::definitions::SecurityLevel;
    use riscv_transpiler::witness::data_structs::{
        MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
        UnifiedOpcodeTracingDataWithTimestamp,
    };
    use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
    use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
    use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
    use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
    use std::alloc::Global;
    use std::sync::OnceLock;

    const SECURITY_LEVEL: SecurityLevel = SecurityLevel::Sec100;

    fn worker() -> &'static Worker {
        static WORKER: OnceLock<Worker> = OnceLock::new();
        WORKER.get_or_init(Worker::new)
    }

    /// Fixed, non-zero challenges: zero challenges would let a handler that
    /// dropped them agree with the oracle by accident.
    fn challenges() -> GKRExternalChallenges<BF, E4> {
        let total = GKRExternalChallenges::<BF, E4>::TOTAL_CHALLENGES;
        let values: Vec<E4> = (0..total as u32)
            .map(|index| {
                E4::from_array_of_base([
                    BF::new(2 + index),
                    BF::new(5 + index * 7),
                    BF::new(42 + index * 11),
                    BF::new(123 + index * 13),
                ])
            })
            .collect();
        GKRExternalChallenges::from_slice(&values)
    }

    fn fixture() -> (Vec<u32>, Vec<u32>) {
        let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let (_, binary) =
            setups::read_and_pad_binary(&root.join("examples/hashed_fibonacci/app.bin"));
        let (_, text) =
            setups::read_and_pad_binary(&root.join("examples/hashed_fibonacci/app.text"));
        (binary, text)
    }

    fn family(circuit_type: UnrolledCircuitType) -> CpuCircuitPrecomputations {
        let (binary, text) = fixture();
        let setup = build_unrolled_setup(
            MachineType::FullUnsigned,
            circuit_type,
            &binary,
            &text,
            worker(),
        );
        CpuCircuitPrecomputations::from_canonical(CircuitType::Unrolled(circuit_type), setup)
    }

    fn delegation(delegation_type: DelegationCircuitType) -> CpuCircuitPrecomputations {
        let setup = build_delegation_setup(delegation_type, worker());
        CpuCircuitPrecomputations::from_canonical(CircuitType::Delegation(delegation_type), setup)
    }

    /// Run the three jobs the way the orchestrator will: initialize the setup,
    /// commit memory, then prove against the caps that commitment produced.
    fn run_jobs(
        jobs: &CpuJobs,
        precomputations: &CpuCircuitPrecomputations,
        tracing_data: Option<TracingDataHost<CpuTraceAllocator>>,
    ) -> ScheduledProof {
        let circuit_type = precomputations.circuit_type();
        setup::run(
            jobs,
            SetupInitializationRequest {
                batch_id: 1,
                circuit_type,
                sequence_id: 0,
                precomputations: precomputations.clone(),
                security_level: SECURITY_LEVEL,
            },
            worker(),
        );

        let WorkResult::MemoryCommitment(committed) = jobs
            .execute(
                WorkRequest::MemoryCommitment(MemoryCommitmentRequest {
                    batch_id: 1,
                    circuit_type,
                    sequence_id: 0,
                    precomputations: precomputations.clone(),
                    inits_and_teardowns: None,
                    tracing_data: tracing_data.clone(),
                    security_level: SECURITY_LEVEL,
                }),
                worker(),
            )
            .unwrap()
        else {
            panic!("memory commitment request produced the wrong result kind");
        };

        let WorkResult::Proof(proved) = RequestExecutor::<CpuTraceAllocator, _>::execute(
            jobs,
            WorkRequest::Proof(ProofRequest {
                batch_id: 1,
                circuit_type,
                sequence_id: 0,
                precomputations: precomputations.clone(),
                inits_and_teardowns: None,
                tracing_data,
                external_challenges: challenges(),
                memory_caps: committed.merkle_tree_caps,
                security_level: SECURITY_LEVEL,
            }),
            worker(),
        )
        .unwrap() else {
            panic!("proof request produced the wrong result kind");
        };
        proved.proof
    }

    /// A second implementation of the adapter's all-zero teardown columns: the
    /// oracle must not be built by the code under test.
    fn zero_columns(num_sets: usize, trace_len: usize) -> Vec<TeardownColumns> {
        (0..num_sets)
            .map(|_| {
                (
                    [vec![BF::ZERO; trace_len], vec![BF::ZERO; trace_len]],
                    [vec![BF::ZERO; trace_len], vec![BF::ZERO; trace_len]],
                )
            })
            .collect()
    }

    fn flatten(precomputations: &CpuCircuitPrecomputations, proof: &ScheduledProof) -> Vec<u32> {
        verifier_common::gkr::flatten::flatten_gkr_proof_for_nds(
            proof,
            precomputations.compiled_circuit(),
        )
    }

    /// The oracle leg: the same primitives the handler dispatches to, composed
    /// here by hand so the comparison is against `program_prover`'s wiring and
    /// not against the code under test.
    fn prove_directly(
        jobs: &CpuJobs,
        precomputations: &CpuCircuitPrecomputations,
        witness: GKRFullWitnessTrace<BF, Global, Global>,
        inits_and_teardowns_top_bits: Vec<u32>,
    ) -> ScheduledProof {
        let config = prover_config(precomputations.circuit_type(), SECURITY_LEVEL);
        let twiddles = jobs.twiddles(precomputations.trace_len(), worker());
        prove_configured_with_gkr_with_backends::<
            BF,
            E4,
            DefaultTreeConstructor,
            Blake2sTranscript,
            _,
            _,
        >(
            precomputations.compiled_circuit(),
            &challenges(),
            witness,
            precomputations.setup_columns(),
            precomputations.setup_commitment().unwrap(),
            &*twiddles,
            &config,
            CommitmentMode::SeparateMemoryAndWitness,
            inits_and_teardowns_top_bits,
            precomputations.trace_len(),
            jobs.backend(),
            jobs.gkr_backend(),
            worker(),
        )
    }

    #[test]
    fn a_non_memory_family_proof_matches_the_legacy_primitives() {
        let jobs = CpuJobs::default();
        let precomputations = family(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
        ));
        let trace =
            TracingDataHost::Unrolled(UnrolledTracingDataHost::NonMemory(ChunkedTraceHolder {
                chunks: Vec::new(),
            }));
        let mine = run_jobs(&jobs, &precomputations, Some(trace));

        let Some(UnrolledCircuitWitnessEvalFn::NonMemory {
            witness_fn,
            decoder_table,
            default_pc_value_in_padding,
        }) = precomputations.witness_eval_fn()
        else {
            panic!("a non-memory family carries a non-memory evaluator");
        };
        let no_rows: &[NonMemoryOpcodeTracingDataWithTimestamp] = &[];
        let oracle = NonMemoryCircuitOracle {
            inner: no_rows,
            decoder_table,
            default_pc_value_in_padding: *default_pc_value_in_padding,
        };
        let witness = evaluate_gkr_witness_for_executor_family::<BF, _, _, _>(
            precomputations.compiled_circuit(),
            *witness_fn,
            precomputations.trace_len(),
            &oracle,
            precomputations.table_driver(),
            worker(),
            None,
            Global,
            Global,
        );
        let expected = prove_directly(&jobs, &precomputations, witness, Vec::new());
        assert_eq!(
            flatten(&precomputations, &mine),
            flatten(&precomputations, &expected)
        );
    }

    #[test]
    fn a_memory_family_proof_matches_the_legacy_primitives() {
        let jobs = CpuJobs::default();
        let precomputations = family(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreWordOnly,
        ));
        let trace =
            TracingDataHost::Unrolled(UnrolledTracingDataHost::Memory(ChunkedTraceHolder {
                chunks: Vec::new(),
            }));
        let mine = run_jobs(&jobs, &precomputations, Some(trace));

        let Some(UnrolledCircuitWitnessEvalFn::Memory {
            witness_fn,
            decoder_table,
        }) = precomputations.witness_eval_fn()
        else {
            panic!("a memory family carries a memory evaluator");
        };
        let no_rows: &[MemoryOpcodeTracingDataWithTimestamp] = &[];
        let oracle = MemoryCircuitOracle {
            inner: no_rows,
            decoder_table,
        };
        let witness = evaluate_gkr_witness_for_executor_family::<BF, _, _, _>(
            precomputations.compiled_circuit(),
            *witness_fn,
            precomputations.trace_len(),
            &oracle,
            precomputations.table_driver(),
            worker(),
            None,
            Global,
            Global,
        );
        let expected = prove_directly(&jobs, &precomputations, witness, Vec::new());
        assert_eq!(
            flatten(&precomputations, &mine),
            flatten(&precomputations, &expected)
        );
    }

    #[test]
    fn a_delegation_proof_matches_the_legacy_primitives() {
        let no_rows: &[Blake2sGFunctionDelegationWitness] = &[];
        delegation_proof_matches::<Blake2sGFunctionAbiDescription, _, _, _, _>(
            DelegationCircuitType::Blake2GFunction,
            TracingDataHost::Delegation(DelegationTracingDataHost::Blake2GFunction(
                ChunkedTraceHolder { chunks: Vec::new() },
            )),
            no_rows,
            blake2_g_function_witness_eval_fn,
        );
    }

    /// Standalone inits-and-teardowns: no table driver, no decoder, and zero
    /// setup columns, so its setup commitment is empty. An empty commitment is
    /// still a commitment — this is the arm that breaks if "no setup columns" is
    /// confused with "setup never ran".
    #[test]
    fn a_standalone_inits_and_teardowns_proof_matches_the_legacy_primitives() {
        let jobs = CpuJobs::default();
        let setup = build_inits_and_teardowns_setup(worker());
        let circuit_type = CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns);
        let precomputations = CpuCircuitPrecomputations::from_canonical(circuit_type, setup);
        assert!(
            !precomputations.has_setup_columns(),
            "this arm is only meaningful while the circuit has no setup columns"
        );
        let num_sets = precomputations
            .compiled_circuit()
            .memory_layout
            .teardown_sets
            .len();
        let trace_len = precomputations.trace_len();
        let top_bits: Vec<u32> = (0..num_sets as u32).collect();
        // An instance that touched no page: every column is zero, which is the
        // cheapest input that still exercises the whole path.
        let trace: InitsAndTeardownsTraceHost<CpuTraceAllocator> = InitsAndTeardownsTraceHost {
            page_indices: ChunkedTraceHolder { chunks: Vec::new() },
            values_packed: ChunkedTraceHolder { chunks: Vec::new() },
            timestamps_packed: ChunkedTraceHolder { chunks: Vec::new() },
            top_bits: top_bits.clone(),
        };

        setup::run(
            &jobs,
            SetupInitializationRequest {
                batch_id: 3,
                circuit_type,
                sequence_id: 0,
                precomputations: precomputations.clone(),
                security_level: SECURITY_LEVEL,
            },
            worker(),
        );
        assert!(
            precomputations.setup_commitment().is_some(),
            "an empty setup still commits"
        );
        assert!(precomputations.setup_cap().is_none());

        let WorkResult::MemoryCommitment(committed) = jobs
            .execute(
                WorkRequest::MemoryCommitment(MemoryCommitmentRequest {
                    batch_id: 3,
                    circuit_type,
                    sequence_id: 0,
                    precomputations: precomputations.clone(),
                    inits_and_teardowns: Some(trace.clone()),
                    tracing_data: None,
                    security_level: SECURITY_LEVEL,
                }),
                worker(),
            )
            .unwrap()
        else {
            panic!("memory commitment request produced the wrong result kind");
        };
        let WorkResult::Proof(proved) = jobs
            .execute(
                WorkRequest::Proof(ProofRequest {
                    batch_id: 3,
                    circuit_type,
                    sequence_id: 0,
                    precomputations: precomputations.clone(),
                    inits_and_teardowns: Some(trace),
                    tracing_data: None,
                    external_challenges: challenges(),
                    memory_caps: committed.merkle_tree_caps,
                    security_level: SECURITY_LEVEL,
                }),
                worker(),
            )
            .unwrap()
        else {
            panic!("proof request produced the wrong result kind");
        };

        let sets = zero_columns(num_sets, trace_len);
        let witness = GKRFullWitnessTrace {
            column_major_memory_trace: evaluate_init_and_teardown_memory_witness(
                sets,
                precomputations.compiled_circuit(),
                Global,
                Global,
            ),
            column_major_witness_trace: Vec::new(),
            column_major_scratch_space_trace: Vec::new(),
            generic_lookup_mapping: Vec::new(),
            range_check_16_lookup_mapping: Vec::new(),
            timestamp_range_check_lookup_mapping: Vec::new(),
        };
        let expected = prove_directly(&jobs, &precomputations, witness, top_bits);
        assert_eq!(
            flatten(&precomputations, &proved.proof),
            flatten(&precomputations, &expected)
        );
    }

    /// One delegation arm: prove through the jobs, then again straight from the
    /// primitives, and require the same proof.
    fn delegation_proof_matches<
        D: crate::upstream::DelegationAbiDescription,
        const REG_ACCESSES: usize,
        const INDIRECT_READS: usize,
        const INDIRECT_WRITES: usize,
        const VARIABLE_OFFSETS: usize,
    >(
        delegation_type: DelegationCircuitType,
        trace: TracingDataHost<CpuTraceAllocator>,
        no_rows: &[crate::upstream::DelegationWitness<
            REG_ACCESSES,
            INDIRECT_READS,
            INDIRECT_WRITES,
            VARIABLE_OFFSETS,
        >],
        witness_eval_fn: fn(
            &mut crate::upstream::ColumnMajorWitnessProxy<
                '_,
                DelegationOracle<
                    '_,
                    D,
                    REG_ACCESSES,
                    INDIRECT_READS,
                    INDIRECT_WRITES,
                    VARIABLE_OFFSETS,
                >,
                BF,
            >,
        ),
    ) {
        let jobs = CpuJobs::default();
        let precomputations = delegation(delegation_type);
        let mine = run_jobs(&jobs, &precomputations, Some(trace));

        let oracle = DelegationOracle::<D, _, _, _, _> {
            cycle_data: no_rows,
            marker: core::marker::PhantomData,
        };
        let witness = evaluate_gkr_witness_for_delegation_circuit::<BF, _, _, _>(
            precomputations.compiled_circuit(),
            witness_eval_fn,
            precomputations.trace_len(),
            &oracle,
            precomputations.table_driver(),
            worker(),
            Global,
            Global,
        );
        let expected = prove_directly(&jobs, &precomputations, witness, Vec::new());
        assert_eq!(
            flatten(&precomputations, &mine),
            flatten(&precomputations, &expected)
        );
    }

    #[test]
    fn a_bigint_delegation_proof_matches_the_legacy_primitives() {
        let no_rows: &[BigintDelegationWitness] = &[];
        delegation_proof_matches::<BigintAbiDescription, _, _, _, _>(
            DelegationCircuitType::BigIntWithControl,
            TracingDataHost::Delegation(DelegationTracingDataHost::BigIntWithControl(
                ChunkedTraceHolder { chunks: Vec::new() },
            )),
            no_rows,
            bigint_witness_eval_fn,
        );
    }

    #[test]
    fn a_blake2_with_compression_delegation_proof_matches_the_legacy_primitives() {
        let no_rows: &[Blake2sRoundFunctionDelegationWitness] = &[];
        delegation_proof_matches::<Blake2sRoundFunctionAbiDescription, _, _, _, _>(
            DelegationCircuitType::Blake2WithCompression,
            TracingDataHost::Delegation(DelegationTracingDataHost::Blake2WithCompression(
                ChunkedTraceHolder { chunks: Vec::new() },
            )),
            no_rows,
            blake2_with_compression_witness_eval_fn,
        );
    }

    #[test]
    fn a_keccak_delegation_proof_matches_the_legacy_primitives() {
        let no_rows: &[KeccakSpecial5DelegationWitness] = &[];
        delegation_proof_matches::<KeccakSpecial5AbiDescription, _, _, _, _>(
            DelegationCircuitType::KeccakSpecial5,
            TracingDataHost::Delegation(DelegationTracingDataHost::KeccakSpecial5(
                ChunkedTraceHolder { chunks: Vec::new() },
            )),
            no_rows,
            keccak_special5_witness_eval_fn,
        );
    }

    /// Unified: inline inits-and-teardowns and a top-bits vector sized to the
    /// circuit's teardown sets, which a family proof must not carry.
    #[test]
    fn a_unified_proof_matches_the_legacy_primitives() {
        let jobs = CpuJobs::default();
        let (binary, text) = fixture();
        let setup = build_unified_setup(&binary, &text, worker());
        let circuit_type = CircuitType::Unrolled(UnrolledCircuitType::Unified);
        let precomputations = CpuCircuitPrecomputations::from_canonical(circuit_type, setup);
        let trace =
            TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(ChunkedTraceHolder {
                chunks: Vec::new(),
            }));
        let mine = run_jobs(&jobs, &precomputations, Some(trace));

        let num_sets = precomputations
            .compiled_circuit()
            .memory_layout
            .teardown_sets
            .len();
        let trace_len = precomputations.trace_len();
        let sets = zero_columns(num_sets, trace_len);
        let Some(UnrolledCircuitWitnessEvalFn::Unified {
            witness_fn,
            decoder_table,
        }) = precomputations.witness_eval_fn()
        else {
            panic!("a unified circuit carries a unified evaluator");
        };
        let no_rows: &[UnifiedOpcodeTracingDataWithTimestamp] = &[];
        let oracle = UnifiedRiscvCircuitOracle {
            inner: no_rows,
            decoder_table,
        };
        let witness = evaluate_gkr_witness_for_executor_family::<BF, _, _, _>(
            precomputations.compiled_circuit(),
            *witness_fn,
            trace_len,
            &oracle,
            precomputations.table_driver(),
            worker(),
            Some(sets),
            Global,
            Global,
        );
        let expected = prove_directly(&jobs, &precomputations, witness, vec![0u32; num_sets]);
        assert_eq!(
            flatten(&precomputations, &mine),
            flatten(&precomputations, &expected)
        );
    }

    /// Byte parity says the handler agrees with the legacy primitives; it
    /// cannot say either of them produces something a verifier accepts. The
    /// generated per-circuit verifier is the independent judge.
    #[cfg(feature = "verifiers")]
    #[test]
    fn a_delegation_proof_verifies_natively() {
        use full_statement_verifier::imports::blake2_g_function_sec_100;
        use verifier_common::errors::DebugErrorCreator;

        let jobs = CpuJobs::default();
        let precomputations = delegation(DelegationCircuitType::Blake2GFunction);
        let trace = TracingDataHost::Delegation(DelegationTracingDataHost::Blake2GFunction(
            ChunkedTraceHolder { chunks: Vec::new() },
        ));
        let proof = run_jobs(&jobs, &precomputations, Some(trace));
        let stream = flatten(&precomputations, &proof);
        let challenges = challenges();

        // The verifier recurses deeply, so it gets its own thread and stack.
        let verified = std::thread::Builder::new()
            .name("verify-blake2-g-function".to_owned())
            .stack_size(1 << 27)
            .spawn(move || {
                let mut source = stream.into_iter();
                blake2_g_function_sec_100::verify::<_, DebugErrorCreator>(&challenges, &mut source)
                    .map(|_| ())
            })
            .expect("verifier thread spawned")
            .join();
        match verified {
            Ok(Ok(())) => {}
            Ok(Err(error)) => {
                panic!("the verifier rejected a proof this handler produced: {error:?}")
            }
            Err(_) => panic!("the verifier panicked on a proof this handler produced"),
        }
    }

    /// The proof re-commits memory; a prior cap that does not match it means the
    /// two passes described different traces.
    #[test]
    #[should_panic(expected = "disagrees with the cap committed")]
    fn an_altered_prior_memory_cap_is_rejected() {
        let jobs = CpuJobs::default();
        let precomputations = delegation(DelegationCircuitType::Blake2GFunction);
        let circuit_type = precomputations.circuit_type();
        let trace: TracingDataHost<CpuTraceAllocator> = TracingDataHost::Delegation(
            DelegationTracingDataHost::Blake2GFunction(ChunkedTraceHolder { chunks: Vec::new() }),
        );
        setup::run(
            &jobs,
            SetupInitializationRequest {
                batch_id: 2,
                circuit_type,
                sequence_id: 0,
                precomputations: precomputations.clone(),
                security_level: SECURITY_LEVEL,
            },
            worker(),
        );
        let WorkResult::MemoryCommitment(committed) = jobs
            .execute(
                WorkRequest::MemoryCommitment(MemoryCommitmentRequest {
                    batch_id: 2,
                    circuit_type,
                    sequence_id: 0,
                    precomputations: precomputations.clone(),
                    inits_and_teardowns: None,
                    tracing_data: Some(trace.clone()),
                    security_level: SECURITY_LEVEL,
                }),
                worker(),
            )
            .unwrap()
        else {
            panic!("memory commitment request produced the wrong result kind");
        };

        let mut altered = committed.merkle_tree_caps;
        altered[0].cap[0][0] ^= 1;
        let _ = jobs.execute(
            WorkRequest::Proof(ProofRequest {
                batch_id: 2,
                circuit_type,
                sequence_id: 0,
                precomputations: precomputations.clone(),
                inits_and_teardowns: None,
                tracing_data: Some(trace),
                external_challenges: challenges(),
                memory_caps: altered,
                security_level: SECURITY_LEVEL,
            }),
            worker(),
        );
    }
}
