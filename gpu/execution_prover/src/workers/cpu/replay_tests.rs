use super::*;
use crate::tracing::{
    PtrRange, SplitDataTraceRanges, SplitTracingType, UnifiedDataTraceRanges, UnifiedTracingType,
};
use crossbeam_channel::{bounded, unbounded, Select};
use era_cudart::memory::{CudaHostAllocFlags, HostAllocation};
use riscv_transpiler::jit::MachineState;
use riscv_transpiler::vm::SimpleTape;

// MachineState carries the packed register timestamp table; constructing and
// replaying a snapshot needs more than libtest's default 2 MiB thread stack.
const REPLAY_STACK_SIZE: usize = 16 << 20;

fn with_replay_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(REPLAY_STACK_SIZE)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

/// Stop the real replayer at its completion send. A cache-hit consumer may
/// recycle the trace as soon as it sees this notification, so no tracer-owned
/// Arc may survive it. Zero cycles isolate ownership from instruction replay.
fn assert_replayer_releases_traces<T: TracingType, Row>(
    make_ranges: impl FnOnce(PtrRange<Row>) -> T::Ranges,
) where
    T::Ranges: 'static,
{
    let allocation = HostAllocation::alloc(1 << 20, CudaHostAllocFlags::DEFAULT).unwrap();
    let chunk = Arc::new(Vec::<Row, A>::new_in(A::new([allocation], 20)));
    let ranges = make_ranges(PtrRange {
        _chunk: Some(Arc::clone(&chunk)),
        ..Default::default()
    });
    let mut trace = LockedBoxedTraceChunk::new();
    trace.len = 0;
    let (snapshots_tx, snapshots_rx) = unbounded();
    snapshots_tx
        .send(Snapshot {
            index: 7,
            cycles_count: 0,
            initial_state: MachineState::initial(),
            final_state: MachineState::initial(),
            trace,
            trace_ranges: ranges,
        })
        .unwrap();
    drop(snapshots_tx);
    let (free_tx, free_rx) = unbounded();
    let (results_tx, results_rx) = bounded(0);
    let replayer = std::thread::Builder::new()
        .stack_size(REPLAY_STACK_SIZE)
        .spawn(move || {
            run_replayer::<T>(
                0,
                0,
                Arc::new(SimpleTape::new(&[])),
                snapshots_rx,
                free_tx,
                results_tx,
                Arc::new(AtomicBool::new(false)),
            );
        })
        .unwrap();
    let mut select = Select::new();
    select.recv(&results_rx);
    let ready = select.ready_timeout(Duration::from_secs(10));
    // ready_timeout does not receive the message: the worker remains blocked
    // in send, exposing every reference it still owns at publication.
    let owners_at_completion = Arc::strong_count(&chunk);
    let result = results_rx.recv_timeout(Duration::from_secs(10));
    drop(results_rx);
    replayer.join().unwrap();
    ready.expect("replayer did not publish completion");
    assert!(matches!(result.unwrap(), WorkerResult::SnapshotReplayed(7)));
    assert_eq!(free_rx.iter().count(), 1);
    assert_eq!(owners_at_completion, 1, "replayer still owns a trace chunk");
    assert_eq!(
        ChunkedTraceHolder {
            chunks: vec![chunk]
        }
        .into_allocators()
        .len(),
        1
    );
}

#[test]
fn replayer_releases_traces_before_completion_unified() {
    with_replay_stack(|| {
        assert_replayer_releases_traces::<UnifiedTracingType, _>(|range| UnifiedDataTraceRanges {
            cycles: [range].into(),
            ..Default::default()
        })
    });
}

#[test]
fn replayer_releases_traces_before_completion_split() {
    with_replay_stack(|| {
        assert_replayer_releases_traces::<SplitTracingType, _>(|range| SplitDataTraceRanges {
            add_sub_family: [range].into(),
            ..Default::default()
        })
    });
}
