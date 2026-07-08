//! Shared timing primitives for the fwd-VM bench (`fwd_vm/`): CUDA-event-timed
//! median/min over N launches, the flat-replay baseline, and the timing knobs.

use super::fixture::CircuitFixture;

/// N for the full A/B timing (median + min over this many iters).
pub(super) const TIMING_ITERS: usize = 50;

/// Cross-circuit timing cap: time at `min(trace_len, 1<<20)` so runtime is
/// bounded and the flat-vs-interp comparison is apples-to-apples at the same
/// element count.
pub(super) const TIMING_COUNT_CAP: usize = 1 << 20;

/// Time the FLAT side of one layer: the full replay launch sequence at `count`,
/// over `iters` iterations. Returns `(median_ms, min_ms, launch_count)` — the
/// interpreter's replayed-flat baseline in the A/B.
pub(super) fn time_flat(
    fixture: &CircuitFixture,
    layer_idx: usize,
    count: usize,
    iters: usize,
) -> (f32, f32, usize) {
    let context = fixture.context();
    let stream = context.get_exec_stream();
    let (median, min) = time_iters(stream, iters, || {
        fixture.replay_layer_count(layer_idx, count).unwrap();
    });
    let launches = fixture.layers[layer_idx].replayable_launch_count();
    (median, min, launches)
}

/// Median + min wall-clock (ms) over `iters` CUDA-event-timed runs of `f`. `f`
/// enqueues the work on `stream`; one start/end event pair brackets each iter,
/// `stream.synchronize()` then reads the elapsed time. Test/bench code only.
pub(super) fn time_iters<F: FnMut()>(
    stream: &era_cudart::stream::CudaStream,
    iters: usize,
    mut f: F,
) -> (f32, f32) {
    use era_cudart::event::{elapsed_time, CudaEvent};
    let start = CudaEvent::create().unwrap();
    let end = CudaEvent::create().unwrap();
    let mut samples = Vec::with_capacity(iters);
    for _ in 0..iters {
        start.record(stream).unwrap();
        f();
        end.record(stream).unwrap();
        stream.synchronize().unwrap();
        samples.push(elapsed_time(&start, &end).unwrap());
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let min = samples[0];
    let median = samples[samples.len() / 2];
    (median, min)
}
