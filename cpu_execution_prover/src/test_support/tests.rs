use super::*;
use common_constants::TimestampScalar;
use execution_prover::messages::{MemoryCommitmentRequest, MemoryCommitmentResult};
use execution_prover::BinaryHandle;
use execution_prover_model::circuit_type::UnrolledCircuitType;
use execution_prover_model::trace::{TracingDataHost, UnrolledTracingDataHost};
use riscv_transpiler::witness::UnifiedOpcodeTracingDataWithTimestamp;

const PROGRAM: [u32; 2] = [0x0001_2083, 0xffdf_f06f];
const CYCLES: u32 = 32;

fn capture(callback: impl for<'a> FnOnce(L1WrapFixture<'a>) -> u64 + Send + 'static) -> u64 {
    with_l1_wrap_fixture(
        CpuExecutionProverConfiguration::default(),
        PROGRAM.to_vec(),
        PROGRAM.to_vec(),
        Vec::new(),
        Some(CYCLES),
        callback,
    )
}

#[test]
fn capture_setup_ack() {
    let prover = ExecutionProver::<CaptureBackend>::with_configuration(
        CpuExecutionProverConfiguration::default(),
    );
    drop(prover);
}

#[test]
fn capture_one_callback_and_returned_owners() {
    let final_timestamp = capture(|fixture| {
        let OperationMode::SingleChunk {
            final_timestamp, ..
        } = fixture.operation_mode
        else {
            panic!("wrong mode")
        };
        assert_eq!(
            fixture.setup.trace_len,
            CircuitType::L1Wrap21.get_domain_size()
        );
        assert_eq!(fixture.tracing_data.len(), CYCLES as usize);
        final_timestamp
    });
    assert_eq!(
        final_timestamp,
        common_constants::INITIAL_TIMESTAMP + CYCLES as u64 * common_constants::TIMESTAMP_STEP
    );
}

#[test]
fn capture_callback_panic() {
    let outcome = catch_unwind(|| capture(|_| panic!("capture callback panic probe")));
    let payload = outcome.expect_err("the callback panic must reach the caller");
    assert_eq!(
        payload.downcast_ref::<&str>(),
        Some(&"capture callback panic probe")
    );
}

type WitnessInputs = (
    Vec<u32>,
    Vec<u32>,
    Vec<TimestampScalar>,
    Vec<u32>,
    Vec<UnifiedOpcodeTracingDataWithTimestamp>,
);

fn wrap_inputs(fixture: L1WrapFixture<'_>) -> WitnessInputs {
    witness_inputs(fixture.inits_and_teardowns, fixture.tracing_data)
}

fn witness_inputs(
    it: &InitsAndTeardownsTraceHost<CpuTraceAllocator>,
    trace: &UnrolledUnifiedTraceHost<CpuTraceAllocator>,
) -> WitnessInputs {
    (
        it.page_indices
            .chunks
            .iter()
            .flat_map(|c| c.iter().copied())
            .collect(),
        it.values_packed
            .chunks
            .iter()
            .flat_map(|c| c.iter().copied())
            .collect(),
        it.timestamps_packed
            .chunks
            .iter()
            .flat_map(|c| c.iter().copied())
            .collect(),
        it.top_bits.clone(),
        trace
            .chunks
            .iter()
            .flat_map(|chunk| chunk.iter().copied())
            .collect(),
    )
}

/// The memory holders serve two 2^21 wrap binaries, one of them storing into
/// RAM at 1 MiB (inside the regular ROM range, outside the 512 KiB wrap ROM),
/// in an order that hands each holder to both binaries. Every run of a binary
/// sees exactly the inputs of its first, fresh-holder run, and the store
/// binary keeps the stored word's teardown value. The store program exits at
/// its self-jump after four cycles.
#[test]
fn two_wrap_binaries_reuse_memory_holders() {
    const STORED: u32 = 0xdead_c000;
    const STORE_PROGRAM: [u32; 4] = [
        0x0010_00b7, // lui x1, 0x100
        0xdead_c137, // lui x2, 0xdeadc
        0x0020_a023, // sw x2, 0(x1)
        0x0000_006f, // jal x0, 0
    ];
    let mut prover =
        ExecutionProver::<CaptureBackend>::with_configuration(CpuExecutionProverConfiguration {
            expected_concurrent_jobs: 1,
            ..Default::default()
        });
    let looping = prover.add_binary(
        ExecutionKind::L1Wrap21,
        MachineType::Reduced,
        PROGRAM.to_vec(),
        PROGRAM.to_vec(),
        Some(CYCLES),
        &[ProofProfile::L1Wrap],
    );
    let storing = prover.add_binary(
        ExecutionKind::L1Wrap21,
        MachineType::Reduced,
        STORE_PROGRAM.to_vec(),
        STORE_PROGRAM.to_vec(),
        Some(CYCLES),
        &[ProofProfile::L1Wrap],
    );
    let mut runs = Vec::new();
    for (is_store, handle) in [
        (false, &looping),
        (true, &storing),
        (false, &looping),
        (false, &looping),
        (true, &storing),
        (true, &storing),
    ] {
        let (sender, receiver) = unbounded();
        prover.backend().install(
            Box::new(|fixture: L1WrapFixture<'_>| {
                Box::new(wrap_inputs(fixture)) as Box<dyn Any + Send>
            }),
            sender,
        );
        prover.prove_l1_wrap(
            FIXTURE_BATCH_ID,
            handle,
            FlatResponsesSource::new_with_reads(Vec::new()),
        );
        let inputs = match receiver.recv().unwrap() {
            Ok(value) => *value.downcast::<WitnessInputs>().unwrap(),
            Err(payload) => resume_unwind(payload),
        };
        runs.push((is_store, inputs));
    }
    for is_store in [false, true] {
        let mut same_binary = runs.iter().filter(|(storing, _)| *storing == is_store);
        let (_, fresh) = same_binary.next().unwrap();
        for (_, reused) in same_binary {
            assert_eq!(reused, fresh, "storing wrap = {is_store}");
        }
        assert_eq!(fresh.1.contains(&STORED), is_store);
        assert_eq!(fresh.4.len(), if is_store { 4 } else { CYCLES as usize });
    }
}

impl CaptureBackend {
    fn install_regular(&self, result: Sender<CaptureOutcome>) {
        let mut state = self.state.lock().unwrap();
        assert!(state.callback.is_none() && state.result.is_none() && !state.regular);
        state.regular = true;
        state.result = Some(result);
    }
}

// Capture actual simulator/replayer inputs; these synthetic caps are not a
// commitment or proof oracle. Return the original owners through the manager.
pub(super) fn capture_regular(
    request: MemoryCommitmentRequest<CpuTraceAllocator, CpuCircuitPrecomputations>,
    worker: &Worker,
    state: &Mutex<CaptureState>,
) -> MemoryCommitmentResult<CpuTraceAllocator> {
    let CaptureState {
        regular, result, ..
    } = std::mem::take(&mut *state.lock().unwrap());
    assert!(
        regular,
        "regular capture must be installed before the request"
    );
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        worker.pool.install(|| {
            assert_eq!(request.profile, ProofProfile::Standard);
            assert_eq!(
                request.circuit_type,
                CircuitType::Unrolled(UnrolledCircuitType::Unified)
            );
            let Some(TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(trace))) =
                request.tracing_data.as_ref()
            else {
                panic!("regular capture requires the unified trace");
            };
            let it = request
                .inits_and_teardowns
                .as_ref()
                .expect("regular init/teardown inputs");
            Box::new(witness_inputs(it, trace)) as Box<dyn Any + Send>
        })
    }));
    result
        .expect("regular capture receiver")
        .send(outcome)
        .unwrap();
    let config = execution_prover::prover_config(
        request.circuit_type,
        request.profile,
        request.security_level,
    );
    assert!(config.cap_size.is_multiple_of(config.lde_factor));
    MemoryCommitmentResult {
        batch_id: request.batch_id,
        circuit_type: request.circuit_type,
        sequence_id: request.sequence_id,
        inits_and_teardowns: request.inits_and_teardowns,
        tracing_data: request.tracing_data,
        memory_partial_trees: None,
        merkle_tree_caps: vec![
            crate::upstream::MerkleTreeCapVarLength {
                cap: vec![[0; 8]; config.cap_size / config.lde_factor],
            };
            config.lde_factor
        ],
    }
}

fn add_geometry(prover: &mut ExecutionProver<CaptureBackend>, is_wrap: bool) -> BinaryHandle {
    let (kind, profile, binary, text) = if is_wrap {
        let program = vec![0x0010_00b7, 0xdead_c137, 0x0020_a023, 0x0000_006f];
        (
            ExecutionKind::L1Wrap21,
            ProofProfile::L1Wrap,
            program.clone(),
            program,
        )
    } else {
        let text = vec![0x0010_00b7, 0x0000_a103, 0x0000_006f];
        let mut binary = vec![0; (1 << 20) / 4 + 1];
        binary[..text.len()].copy_from_slice(&text);
        binary[(1 << 20) / 4] = 0x1234_5000;
        (ExecutionKind::Unified, ProofProfile::Standard, binary, text)
    };
    prover.add_binary(
        kind,
        MachineType::Reduced,
        binary,
        text,
        Some(CYCLES),
        &[profile],
    )
}

fn capture_geometry(
    prover: &ExecutionProver<CaptureBackend>,
    handle: &BinaryHandle,
    is_wrap: bool,
) -> WitnessInputs {
    let (sender, receiver) = unbounded();
    if is_wrap {
        prover
            .backend()
            .install(Box::new(|fixture| Box::new(wrap_inputs(fixture))), sender);
        prover.prove_l1_wrap(
            FIXTURE_BATCH_ID,
            handle,
            FlatResponsesSource::new_with_reads(Vec::new()),
        );
    } else {
        prover.backend().install_regular(sender);
        prover.commit_memory(
            FIXTURE_BATCH_ID,
            handle,
            FlatResponsesSource::new_with_reads(Vec::new()),
            ProofProfile::Standard,
        );
    }
    match receiver.recv().unwrap() {
        Ok(value) => *value.downcast::<WitnessInputs>().unwrap(),
        Err(payload) => resume_unwind(payload),
    }
}

/// R,W,W,R,R,W crosses both ROM geometries regardless of the holder pool's
/// order: FIFO gives each of the two holders both R->W and W->R; LIFO reuses
/// one holder, which also crosses in both directions. Each result is compared
/// with the matching binary's independently fresh-holder baseline. The word
/// at 1 MiB is ROM for Standard and RAM for Wrap21. Compare full opcode traces
/// and init/teardown inputs; the capture does not verify commitments or proofs.
#[test]
fn standard_and_wrap_witness_inputs_reuse_memory_holders() {
    let expected = [false, true].map(|is_wrap| {
        let mut fresh = ExecutionProver::<CaptureBackend>::with_configuration(
            CpuExecutionProverConfiguration {
                expected_concurrent_jobs: 1,
                ..Default::default()
            },
        );
        let handle = add_geometry(&mut fresh, is_wrap);
        capture_geometry(&fresh, &handle, is_wrap)
    });
    assert!(!expected[0].1.contains(&0xdead_c000));
    assert!(expected[1].1.contains(&0xdead_c000));
    assert_eq!(expected[0].4.len(), 3);
    assert_eq!(expected[1].4.len(), 4);
    let mut prover =
        ExecutionProver::<CaptureBackend>::with_configuration(CpuExecutionProverConfiguration {
            expected_concurrent_jobs: 1,
            ..Default::default()
        });
    let regular = add_geometry(&mut prover, false);
    let wrap = add_geometry(&mut prover, true);
    for is_wrap in [false, true, true, false, false, true] {
        let handle = if is_wrap { &wrap } else { &regular };
        let actual = capture_geometry(&prover, handle, is_wrap);
        assert_eq!(actual, expected[usize::from(is_wrap)], "wrap21={is_wrap}");
    }
}
