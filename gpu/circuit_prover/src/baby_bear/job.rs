use crate::proof::ProofResult;
use crate::upstream::{DefaultTreeConstructor, GKRProof};
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr::backward::{GKRBackwardStageSnapshot, GKRBackwardStageSnapshotSink};

type BabyBearProof = GKRProof<BF, E4, DefaultTreeConstructor>;

impl crate::proof::sealed::ResultSealed for BabyBearProof {}
impl ProofResult for BabyBearProof {
    type Field = E4;
    type Finished = (Self, f32);
    type Stagewise = (Self, Vec<GKRBackwardStageSnapshot<E4>>, f32);
    const MEASURE_TIME: bool = true;
    const FINISH_RANGE: Option<&'static str> = None;
    fn finish(self, time_ms: f32) -> Self::Finished {
        (self, time_ms)
    }
    fn finish_stagewise(
        self,
        snapshots: Option<Box<GKRBackwardStageSnapshotSink<E4>>>,
        time_ms: f32,
    ) -> Self::Stagewise {
        (
            self,
            snapshots
                .expect("stagewise proof job must collect snapshots")
                .into_snapshots(),
            time_ms,
        )
    }
}
