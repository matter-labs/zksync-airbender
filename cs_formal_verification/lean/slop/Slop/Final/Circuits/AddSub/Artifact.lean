module
public import Human.Circuits.AddSub.Artifact
public import Slop.KernelRfl
import all Init.Data.Range.Basic -- Init.Data.Range.Basic is not exposed

@[expose] public section

namespace Airbender.AddSub

/-- The kernel evaluates the meaning on the transcribed artifact and compares it with the emitted terms. -/
theorem artifact_import : ArtifactImportClaim :=
  by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> kernel_rfl

end Airbender.AddSub
