module
public import Human.Circuits.InitsTeardowns.UnifiedArtifact
public import Proven.KernelRfl
import all Init.Data.Range.Basic -- Init.Data.Range.Basic is not exposed

@[expose] public section

namespace Airbender.InitsTeardowns

/-- The kernel evaluates the meaning on the transcribed artifact and compares it with the emitted terms. -/
theorem unified_import : UnifiedImportClaim :=
  by delta UnifiedImportClaim; kernel_rfl

end Airbender.InitsTeardowns
