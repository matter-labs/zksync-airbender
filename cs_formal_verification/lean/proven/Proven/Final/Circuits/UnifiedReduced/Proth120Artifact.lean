module
public import Human.Circuits.UnifiedReduced.Proth120Artifact
public import Proven.KernelRfl
import all Init.Data.Range.Basic

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120

set_option maxRecDepth 32768 in
theorem artifact_import : ArtifactImportClaim := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> kernel_rfl

end Airbender.UnifiedReduced.Proth120
