module
public import Human.Compiler.Captures.ShiftBinop
public import Proven.KernelRfl

@[expose] public section

namespace Airbender.Compiler.Bindings.ShiftBinop

/-- The cached capture keeps every field of the existing description except its compiled layers. -/
theorem cached_description : Airbender.Compiler.ShiftBinopCachedDescriptionClaim := by
  unfold Airbender.Compiler.ShiftBinopCachedDescriptionClaim
  kernel_rfl

end Airbender.Compiler.Bindings.ShiftBinop
