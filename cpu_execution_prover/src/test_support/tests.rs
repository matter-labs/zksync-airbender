use super::*;

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
