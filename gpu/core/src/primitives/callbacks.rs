//! Owning list of stream-scheduled host callbacks.
//!
//! Each `Callbacks` instance owns the `HostFn` objects backing one stream's
//! `launch_host_fn` calls. The CUDA driver dereferences the `HostFn` when the
//! callback fires on the stream, so the `Callbacks` must outlive every queued
//! op until those ops have been **scheduled** (not completed). After the last
//! call to `schedule`, the `Callbacks` can be parked alongside the rest of
//! the per-stream keepalive bundle and dropped together once the proof or
//! workflow that produced it finishes.
//!
//! See `docs/gpu_scheduling_contract.md` §Lifetime rules for the broader
//! "scheduled vs. completed" distinction.

use era_cudart::execution::{launch_host_fn, HostFn};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;

pub struct Callbacks<'a>(Vec<HostFn<'a>>);

impl<'a> Callbacks<'a> {
    pub fn new() -> Self {
        Self(vec![])
    }
    pub fn schedule(
        &mut self,
        func: impl Fn() + Send + Sync + 'a,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        let func = HostFn::new(func);
        launch_host_fn(stream, &func)?;
        self.0.push(func);
        Ok(())
    }

    pub fn extend(&mut self, other: Self) {
        self.0.extend(other.0);
    }
}
