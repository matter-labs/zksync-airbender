module
public import Human.Compiler.Captures.Keccak
public import Proven.KernelRfl

@[expose] public section

namespace Airbender.Compiler.Bindings.Keccak

/-- The cached capture keeps every field of the existing description except its compiled layers. -/
theorem cached_description : Airbender.Compiler.KeccakCachedDescriptionClaim := by
  unfold Airbender.Compiler.KeccakCachedDescriptionClaim
  kernel_rfl

end Airbender.Compiler.Bindings.Keccak
