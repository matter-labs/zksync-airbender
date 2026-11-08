module
public import Human.Circuits.InitsTeardowns.Theorems
public import Slop.InitsTeardowns.Claims

@[expose] public section

/-! The inits/teardowns claims of `Human.Circuits.InitsTeardowns.Theorems`. -/

namespace Airbender.InitsTeardowns
open Proofs

/-- The standalone circuit: init tuples are the zero boot image of the windows named by the checked
    top bits, teardown tuples carry the final columns at the same addresses, and the windows of
    `0, …, 63` cover every aligned RAM word. -/
theorem standalone_claim : StandaloneClaim := by
  have shape : Shape importedLayout := ⟨rfl, Or.inr rfl⟩
  refine ⟨claims shape, fun address aligned => covered shape address aligned ?_⟩
  have := address.isLt
  show address.toNat < 64 * 2 ^ (24 + 2)
  omega

/-- The same for the unified reduced machine's inline sets; coverage below `2 ^ 31`. -/
theorem unified_claim : UnifiedClaim := by
  have shape : Shape unifiedLayout := ⟨rfl, Or.inl rfl⟩
  refine ⟨claims shape, fun address aligned below => covered shape address aligned ?_⟩
  show address.toNat < 64 * 2 ^ (23 + 2)
  omega

end Airbender.InitsTeardowns
