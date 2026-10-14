use super::*;
use common_constants::TimestampScalar;

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
        let CommitmentMode::MergedAndPackedMemoryAndWitness {
            final_timestamp, ..
        } = fixture.commitment_mode
        else {
            panic!("wrong mode")
        };
        assert_eq!(
            fixture.setup.trace_len,
            CircuitType::L1Wrap.get_domain_size()
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

type WrapInputs = (Vec<u32>, Vec<u32>, Vec<TimestampScalar>, Vec<u32>, usize);

fn wrap_inputs(fixture: L1WrapFixture<'_>) -> WrapInputs {
    let it = fixture.inits_and_teardowns;
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
        fixture.tracing_data.len(),
    )
}

/// The memory holders serve the 2^22 wrap (regular 4 MiB ROM) and the 2^21
/// wrap (512 KiB ROM) of a program storing into RAM at 1 MiB, inside the
/// regular ROM range, in an order that hands each holder to both geometries.
/// Every run of a binary sees exactly the inputs of its first, fresh-holder
/// run, and the 2^21 wrap keeps the stored word's teardown value. The store
/// program exits at its self-jump after four cycles.
#[test]
fn mixed_regular_and_wrap_witness_reuse_one_holder() {
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
    let regular = prover.add_binary(
        ExecutionKind::L1Wrap,
        MachineType::Reduced,
        PROGRAM.to_vec(),
        PROGRAM.to_vec(),
        Some(CYCLES),
        &[ProofProfile::L1Wrap],
    );
    let wrap = prover.add_binary(
        ExecutionKind::L1Wrap21,
        MachineType::Reduced,
        STORE_PROGRAM.to_vec(),
        STORE_PROGRAM.to_vec(),
        Some(CYCLES),
        &[ProofProfile::L1Wrap],
    );
    let mut runs = Vec::new();
    for (is_wrap, handle) in [
        (false, &regular),
        (true, &wrap),
        (false, &regular),
        (false, &regular),
        (true, &wrap),
        (true, &wrap),
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
            Ok(value) => *value.downcast::<WrapInputs>().unwrap(),
            Err(payload) => resume_unwind(payload),
        };
        runs.push((is_wrap, inputs));
    }
    for is_wrap in [false, true] {
        let mut same_binary = runs.iter().filter(|(wrap, _)| *wrap == is_wrap);
        let (_, fresh) = same_binary.next().unwrap();
        for (_, reused) in same_binary {
            assert_eq!(reused, fresh, "wrap21 = {is_wrap}");
        }
        assert_eq!(fresh.1.contains(&STORED), is_wrap);
        assert_eq!(fresh.4, if is_wrap { 4 } else { CYCLES as usize });
    }
}
