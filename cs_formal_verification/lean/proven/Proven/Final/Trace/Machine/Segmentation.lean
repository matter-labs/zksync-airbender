module
public import Proven.Trace.Machine.Segmentation

@[expose] public section
namespace Airbender.Trace.Machine
open Airbender.Trace.Machine.Proofs
set_option warningAsError true

/-- Native unrolled matching partitions all submitted hash worker occurrences. -/
theorem unrolled_hash_segmentation : UnrolledHashSegmentationClaim := by
  intro trace workers program windows accepted initial aligned profile
  exact hash_segmentation_of_matching (unrolled_requests_complete accepted initial aligned) profile
    (worker_fulfillments_live accepted.toWorkersAccepted)

/-- Native unified matching partitions all submitted hash worker occurrences. -/
theorem unified_hash_segmentation : UnifiedHashSegmentationClaim := by
  intro trace workers program windows accepted initial aligned profile
  exact hash_segmentation_of_matching (unified_requests_complete accepted initial aligned) profile
    (worker_fulfillments_live accepted.toWorkersAccepted)

end Airbender.Trace.Machine
