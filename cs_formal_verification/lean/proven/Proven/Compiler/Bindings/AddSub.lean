module
public import Human.Compiler.Captures.AddSub
public import Proven.KernelRfl

@[expose] public section

namespace Airbender.Compiler.Bindings.AddSub

/-- The cached capture keeps every field of the existing description except its compiled layers. -/
theorem cached_description : Airbender.Compiler.AddSubCachedDescriptionClaim := by
  unfold Airbender.Compiler.AddSubCachedDescriptionClaim
  kernel_rfl

end Airbender.Compiler.Bindings.AddSub
