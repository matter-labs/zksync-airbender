module
public import Human.Circuits.InitsTeardowns.Artifact
public import Slop.KernelRfl
import all Init.Data.Range.Basic -- Init.Data.Range.Basic is not exposed
import all Init.Data.Repr -- Init.Data.Repr is not exposed (still true in 4.35)
import all Init.Data.String.Defs -- Init.Data.Repr is not exposed (still true in 4.35)
import all Init.Data.Int.Repr -- Int.repr is not exposed

@[expose] public section

namespace Airbender.InitsTeardowns

/-- The kernel evaluates the meaning on the transcribed artifact and compares it with the emitted terms. -/
theorem standalone_import : StandaloneImportClaim :=
  by delta StandaloneImportClaim; kernel_rfl

/-- The kernel parses and decodes the file's bytes and compares the result with the transcribed artifact. -/
theorem standalone_bytes : StandaloneBytesClaim :=
  by delta StandaloneBytesClaim; kernel_rfl

end Airbender.InitsTeardowns
