module
public import Human.Compiler.Captures.WordMemory
public import Proven.KernelRfl

@[expose] public section

namespace Airbender.Compiler.Bindings.WordMemory

/-- The cached capture keeps every field of the existing description except its compiled layers. -/
theorem cached_description : Airbender.Compiler.WordMemoryCachedDescriptionClaim := by
  unfold Airbender.Compiler.WordMemoryCachedDescriptionClaim
  kernel_rfl

end Airbender.Compiler.Bindings.WordMemory
