module
public import Human.Circuits.Blake2Round.Artifact
public import Slop.KernelRfl
import all Init.Data.Array.Basic
import all Init.Data.Range.Basic

@[expose] public section

namespace Airbender.Blake2Round

/-- The kernel evaluates the meaning on the transcribed artifact and compares it with the emitted terms. -/
theorem artifact_import : ArtifactImportClaim :=
  by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> kernel_rfl

end Airbender.Blake2Round
