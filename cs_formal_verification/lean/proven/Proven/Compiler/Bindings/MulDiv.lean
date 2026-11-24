module
public import Human.Compiler.Captures.MulDiv
public import Proven.KernelRfl

@[expose] public section

namespace Airbender.Compiler.Bindings.MulDiv

/-- The cached capture keeps every field of the existing description except its compiled layers. -/
theorem cached_description : Airbender.Compiler.MulDivCachedDescriptionClaim := by
  unfold Airbender.Compiler.MulDivCachedDescriptionClaim
  kernel_rfl

end Airbender.Compiler.Bindings.MulDiv
