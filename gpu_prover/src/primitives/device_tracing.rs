use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::execution::{launch_host_fn, HostFn};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;

use crate::primitives::context::UnsafeMutAccessor;

pub(crate) struct Range {
    start_event: CudaEvent,
    start_fn: HostFn<'static>,
    end_event: CudaEvent,
    end_fn: HostFn<'static>,
    #[allow(dead_code)] // Keeps the shared range id alive for both queued callbacks.
    id: Box<Option<i32>>,
}

impl Range {
    pub fn new(name: impl Into<Box<str>>) -> CudaResult<Self> {
        let name = name.into();
        let mut id = Box::new(None::<i32>);
        let id_handle = UnsafeMutAccessor::new(id.as_mut());
        let start_event = CudaEvent::create()?;
        let start_fn = {
            let id = id_handle;
            HostFn::new(move || unsafe {
                *id.get_mut() = Some(nvtx::range_start!("{}", name.as_ref()));
            })
        };
        let end_event = CudaEvent::create()?;
        let end_fn = {
            let id = id_handle;
            HostFn::new(move || unsafe {
                let id = id
                    .get_mut()
                    .take()
                    .expect("NVTX range end callback ran before the start callback");
                nvtx::range_end!(id);
            })
        };
        let range = Self {
            start_event,
            start_fn,
            end_event,
            end_fn,
            id,
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
