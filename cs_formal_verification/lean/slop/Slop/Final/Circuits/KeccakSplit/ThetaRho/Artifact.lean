module
public import Human.Circuits.KeccakSplit.ThetaRho.Artifact
public import Slop.KernelRfl
import all Init.Data.Array.Basic -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)
import all Init.Data.Range.Basic -- Init.Data.Range.Basic is not exposed

@[expose] public section

namespace Airbender.Keccak.Split.ThetaRho

/-- The kernel evaluates the meaning on the transcribed artifact and compares it with the emitted terms. -/
theorem artifact_import : ArtifactImportClaim :=
  by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> kernel_rfl

end Airbender.Keccak.Split.ThetaRho
