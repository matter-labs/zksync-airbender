module
public import Human.Circuits.InitsTeardowns.Artifact
public import Slop.KernelRfl
import all Init.Data.Array.Basic
import all Init.Data.Range.Basic

@[expose] public section

namespace Airbender.InitsTeardowns

/-- The kernel evaluates the meaning on the transcribed artifact and compares it with the emitted terms. -/
theorem standalone_import : StandaloneImportClaim :=
  by delta StandaloneImportClaim; kernel_rfl

end Airbender.InitsTeardowns
