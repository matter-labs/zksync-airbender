module
public import Human.Circuits.InitsTeardowns.SharedArtifact
public import Proven.KernelRfl
import all Init.Data.Range.Basic -- Init.Data.Range.Basic is not exposed
import all Init.Data.Repr -- Init.Data.Repr is not exposed (still true in 4.35)
import all Init.Data.String.Defs -- Init.Data.Repr is not exposed (still true in 4.35)
import all Init.Data.Int.Repr -- Int.repr is not exposed

@[expose] public section

namespace Airbender.InitsTeardowns

/-- The kernel parses and decodes the file's bytes and compares the result with the shared transcription. -/
theorem shared_bytes : SharedBytesClaim :=
  by delta SharedBytesClaim; kernel_rfl

/-- The shared transcription is the decoded circuit, and the kernel counts its placement entries. -/
theorem shared_bytes_satisfiable : SharedBytesSatisfiableClaim :=
  ⟨sharedLayoutCircuit, shared_bytes, by kernel_rfl⟩

end Airbender.InitsTeardowns
