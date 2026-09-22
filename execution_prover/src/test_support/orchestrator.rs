use super::*;
use crate::{ExecutionKind, ExecutionProver, MachineType};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;

/// Three batches on a prover sized for one: the extra callers wait for a
/// cached memory holder and trace chunk set, and every block comes back.
#[test]
fn concurrent_batches_wait_for_cached_resources_and_return_every_block() {
    REQUESTS.store(0, Ordering::SeqCst);
    // One memory access every two cycles fills two JIT trace chunks.
    let program = vec![0x0001_2083, 0xffdf_f06f]; // lw x1, 0(x2); jal x0, -4
    let cycles = 4 * riscv_transpiler::jit::TRACE_CHUNK_LEN as u32;
    let mut prover = ExecutionProver::<TestBackend>::new();
    let handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        program.clone(),
        program,
        Some(cycles),
    );
    let expected_final_timestamp =
        common_constants::INITIAL_TIMESTAMP + u64::from(cycles) * common_constants::TIMESTAMP_STEP;
    std::thread::scope(|scope| {
        for batch_id in 1..=3 {
            let prover = &prover;
            let handle = &handle;
            scope.spawn(move || {
                let commitment =
                    prover.commit_memory(batch_id, handle, QuasiUARTSource::new_with_reads(vec![]));
                assert_eq!(commitment.final_timestamp, expected_final_timestamp);
            });
        }
    });
    assert!(REQUESTS.load(Ordering::SeqCst) > 0);
    drop(prover);
    assert_eq!(LIVE_BLOCKS.load(Ordering::SeqCst), 0);
}
