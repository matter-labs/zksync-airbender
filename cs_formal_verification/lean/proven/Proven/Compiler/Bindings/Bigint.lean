module
public import Human.Compiler.Captures.Bigint
public import Proven.KernelRfl

@[expose] public section

namespace Airbender.Compiler.Bindings.Bigint

/-- The cached capture keeps every field of the existing description except its compiled layers. -/
theorem cached_description : Airbender.Compiler.BigintCachedDescriptionClaim := by
  unfold Airbender.Compiler.BigintCachedDescriptionClaim
  kernel_rfl

end Airbender.Compiler.Bindings.Bigint
