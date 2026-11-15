use era_cudart::event::CudaEvent;
use era_cudart::result::CudaResult;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::nvtx::scoped_range;
use gpu_gkr::backward::GKRBackwardStageSnapshotSink;

use crate::upstream::Field;

#[doc(hidden)]
pub trait ProofResult: super::sealed::ResultSealed {
    type Field: Field;
    type Finished;
    type Stagewise;
    const MEASURE_TIME: bool;
    const FINISH_RANGE: Option<&'static str>;
    fn finish(self, time_ms: f32) -> Self::Finished;
    fn finish_stagewise(
        self,
        snapshots: Option<Box<GKRBackwardStageSnapshotSink<Self::Field>>>,
        time_ms: f32,
    ) -> Self::Stagewise;
}

pub struct ProofJob<'a, T: ProofResult, K> {
    pub(crate) is_finished_event: CudaEvent,
    pub(crate) callbacks: Callbacks<'a>,
    pub(crate) result: Box<Option<T>>,
    pub(crate) ranges: Vec<Range>,
    pub(crate) stage_snapshots: Option<Box<GKRBackwardStageSnapshotSink<T::Field>>>,
    pub(crate) keepalive: K,
}

impl<T: ProofResult, K> ProofJob<'_, T, K> {
    fn finish_inner(
        self,
    ) -> CudaResult<(T, Option<Box<GKRBackwardStageSnapshotSink<T::Field>>>, f32)> {
        let Self {
            is_finished_event,
            callbacks,
            mut result,
            ranges,
            stage_snapshots,
            keepalive,
        } = self;
        let _range = T::FINISH_RANGE.map(|name| scoped_range(Some("ab"), name));
        is_finished_event.synchronize()?;
        drop(callbacks);
        drop(keepalive);
        let result = result
            .take()
            .expect("proof assembly callback must run before finish");
        let time_ms = if T::MEASURE_TIME {
            ranges
                .last()
                .expect("proof job must keep the top-level range")
                .elapsed()?
        } else {
            0.0
        };
        Ok((result, stage_snapshots, time_ms))
    }

    pub fn finish(self) -> CudaResult<T::Finished> {
        let (result, _, time_ms) = self.finish_inner()?;
        Ok(result.finish(time_ms))
    }

    #[doc(hidden)]
    pub fn finish_stagewise(self) -> CudaResult<T::Stagewise> {
        let (result, snapshots, time_ms) = self.finish_inner()?;
        Ok(result.finish_stagewise(snapshots, time_ms))
    }
}
