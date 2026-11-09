module
public import Human.Circuits.KeccakSplit.Chi5.Artifact
public import Slop.KernelRfl
import all Init.Data.Array.Basic -- Init.Data.Array.Basic is only partly exposed (still true in 4.35)
import all Init.Data.Range.Basic -- Init.Data.Range.Basic is not exposed

@[expose] public section

namespace Airbender.Keccak.Split.Chi5

/-- The kernel evaluates the meaning on the transcribed artifact and compares it with the emitted terms. -/
theorem artifact_import : ArtifactImportClaim :=
  by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> kernel_rfl

end Airbender.Keccak.Split.Chi5
