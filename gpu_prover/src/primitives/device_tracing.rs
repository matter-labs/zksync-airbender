use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::execution::{launch_host_fn, HostFn};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use std::sync::{Arc, OnceLock};

pub(crate) struct Range {
    start_event: CudaEvent,
    start_fn: HostFn<'static>,
    end_event: CudaEvent,
    end_fn: HostFn<'static>,
}

impl Range {
    pub fn new(name: impl Into<Arc<str>>) -> CudaResult<Self> {
        let name = name.into();
        let id = Arc::new(OnceLock::new());
        let start_event = CudaEvent::create()?;
        let start_fn = {
            let id = id.clone();
            let name = Arc::clone(&name);
            HostFn::new(move || {
                id.set(nvtx::range_start!("{}", name.as_ref())).unwrap();
            })
        };
        let end_event = CudaEvent::create()?;
        let end_fn = {
            let id = id.clone();
            HostFn::new(move || {
                let id = *id.get().unwrap();
                nvtx::range_end!(id);
            })
        };
        let range = Self {
            start_event,
            start_fn,
            end_event,
            end_fn,
        };
        Ok(range)
    }

    pub fn start(&self, stream: &CudaStream) -> CudaResult<()> {
        self.start_event.record(stream)?;
        launch_host_fn(stream, &self.start_fn)
    }

    pub fn end(&self, stream: &CudaStream) -> CudaResult<()> {
        launch_host_fn(stream, &self.end_fn)?;
        self.end_event.record(stream)
    }

    pub fn elapsed(&self) -> CudaResult<f32> {
        elapsed_time(&self.start_event, &self.end_event)
    }
}
