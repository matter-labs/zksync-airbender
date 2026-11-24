module
public import Human.Compiler.Captures.Unified
public import Proven.KernelRfl

@[expose] public section

namespace Airbender.Compiler.Bindings.Unified

/-- The cached capture keeps every field of the existing description except its compiled layers. -/
theorem cached_description : Airbender.Compiler.UnifiedCachedDescriptionClaim := by
  unfold Airbender.Compiler.UnifiedCachedDescriptionClaim
  kernel_rfl

end Airbender.Compiler.Bindings.Unified
