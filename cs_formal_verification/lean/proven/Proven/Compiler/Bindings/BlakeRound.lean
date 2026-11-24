module
public import Human.Compiler.Captures.BlakeRound
public import Proven.KernelRfl

@[expose] public section

namespace Airbender.Compiler.Bindings.BlakeRound

/-- The cached capture keeps every field of the existing description except its compiled layers. -/
theorem cached_description : Airbender.Compiler.BlakeRoundCachedDescriptionClaim := by
  unfold Airbender.Compiler.BlakeRoundCachedDescriptionClaim
  kernel_rfl

end Airbender.Compiler.Bindings.BlakeRound
