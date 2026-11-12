module
public import Human.Compiler.Captures.JumpBranch
public import Proven.KernelRfl

@[expose] public section

namespace Airbender.Compiler.Bindings.JumpBranch

/-- The cached capture keeps every field of the existing description except its compiled layers. -/
theorem cached_description : Airbender.Compiler.JumpBranchCachedDescriptionClaim := by
  unfold Airbender.Compiler.JumpBranchCachedDescriptionClaim
  kernel_rfl

end Airbender.Compiler.Bindings.JumpBranch
