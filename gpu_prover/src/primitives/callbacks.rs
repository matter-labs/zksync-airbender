use era_cudart::execution::{launch_host_fn, HostFn};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;

pub(crate) struct Callbacks<'a>(Vec<HostFn<'a>>);

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
