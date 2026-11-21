use crate::proof::ProofResult;
use crate::upstream::L1WrapResult;
use gpu_core::primitives::field::PR;
use gpu_gkr::backward::{GKRBackwardStageSnapshot, GKRBackwardStageSnapshotSink};

impl crate::proof::sealed::ResultSealed for L1WrapResult {}
impl ProofResult for L1WrapResult {
    type Field = PR;
    type Finished = Self;
    type Stagewise = (Self, Vec<GKRBackwardStageSnapshot<PR>>);
    const MEASURE_TIME: bool = false;
    const FINISH_RANGE: Option<&'static str> = Some("l1_wrap.finish");
    fn finish(self, _time_ms: f32) -> Self::Finished {
        self
    }
    fn finish_stagewise(
        self,
        snapshots: Option<Box<GKRBackwardStageSnapshotSink<PR>>>,
        _time_ms: f32,
    ) -> Self::Stagewise {
        (
            self,
            snapshots
                .expect("stagewise proof job must collect snapshots")
                .into_snapshots(),
        )
    }
}
