use std::cell::Cell;

use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;

use crate::primitives::nvtx::{end_range, start_range, RangeId};

const DOMAIN_NAME: &str = "ab";

pub(crate) struct Range {
    name: String,
    start_event: CudaEvent,
    end_event: CudaEvent,
    id: Cell<Option<RangeId>>,
}

impl Range {
    pub fn new(name: impl AsRef<str>) -> CudaResult<Self> {
        let start_event = CudaEvent::create()?;
        let end_event = CudaEvent::create()?;
        Ok(Self {
            name: name.as_ref().to_owned(),
            start_event,
            end_event,
            id: Cell::new(None),
        })
    }

    pub fn start(&self, stream: &CudaStream) -> CudaResult<()> {
        self.start_event.record(stream)?;
        let id = start_range(Some(DOMAIN_NAME), &self.name);
        assert!(
            self.id.replace(Some(id)).is_none(),
            "NVTX range started twice without ending",
        );
        Ok(())
    }

    pub fn end(&self, stream: &CudaStream) -> CudaResult<()> {
        let id = self.id.take().expect("NVTX range end called before start");
        end_range(id);
        self.end_event.record(stream)
    }

    pub fn elapsed(&self) -> CudaResult<f32> {
        elapsed_time(&self.start_event, &self.end_event)
    }
}
