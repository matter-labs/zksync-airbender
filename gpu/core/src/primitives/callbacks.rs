//! Owning list of stream-scheduled host callbacks.
//!
//! Each `Callbacks` instance owns the `HostFn` objects backing its
//! `launch_host_fn` calls. CUDA holds only a weak reference to each callback;
//! dropping the owner before execution can silently skip the callback and
//! release its captured resources too early. Keep the owner alive until a
//! stream or event synchronization confirms that all its callbacks completed.
//!
//! Unlike stream-ordered pool reservations, callback owners cannot be released
//! merely because their users have been scheduled.

use era_cudart::execution::{launch_host_fn, HostFn};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;

pub struct Callbacks<'a>(Vec<HostFn<'a>>);

impl Default for Callbacks<'_> {
    fn default() -> Self {
        Self::new()
    }
}

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
