module
public import Proven.Trace.Machine.CodeWindows

@[expose] public section
namespace Airbender.Trace.Machine
set_option warningAsError true

/-- Public unrolled code and native duration derive the complete hash-worker partition. -/
theorem unrolled_code_hash_segmentation : UnrolledCodeHashSegmentationClaim :=
  Airbender.Trace.Machine.Proofs.unrolled_code_hash_segmentation

/-- Public unified code and native duration derive the complete hash-worker partition. -/
theorem unified_code_hash_segmentation : UnifiedCodeHashSegmentationClaim :=
  Airbender.Trace.Machine.Proofs.unified_code_hash_segmentation

end Airbender.Trace.Machine
