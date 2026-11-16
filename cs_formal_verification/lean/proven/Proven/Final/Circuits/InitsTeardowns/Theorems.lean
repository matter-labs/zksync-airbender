module
public import Proven.InitsTeardowns.Claims

@[expose] public section

/-! The inits/teardowns claims of `Human.Circuits.InitsTeardowns.Theorems`. -/

namespace Airbender.InitsTeardowns
open Proofs Trace

/-- The standalone circuit: init tuples are the zero boot image of the windows named by the checked
    top bits, teardown tuples carry the final columns at the same addresses, and the windows of
    `0, …, 63` cover every aligned RAM word. -/
theorem standalone_claim :
  Claims importedLayout ∧
    ∀ address : BitVec 32, (Cell.ram address).Aligned →
      Cell.ram address ∈ windowCells importedLayout (List.range maxTopBit) := by
  have shape : Shape importedLayout := ⟨rfl, Or.inr rfl⟩
  refine ⟨claims shape, fun address aligned => covered shape address aligned ?_⟩
  have := address.isLt
  show address.toNat < 64 * 2 ^ (24 + 2)
  omega

/-- The same for the unified reduced machine's inline sets; coverage below `2 ^ 31`. -/
theorem unified_claim :
  Claims unifiedLayout ∧
    ∀ address : BitVec 32, (Cell.ram address).Aligned → address.toNat < 2 ^ 31 →
      Cell.ram address ∈ windowCells unifiedLayout (List.range maxTopBit) := by
  have shape : Shape unifiedLayout := ⟨rfl, Or.inl rfl⟩
  refine ⟨claims shape, fun address aligned below => covered shape address aligned ?_⟩
  show address.toNat < 64 * 2 ^ (23 + 2)
  omega

/-- The reviewed token properties follow from the native layout theorem. -/
theorem standalone_properties : StandaloneClaim := standalone_claim

/-- The window top-bits check has a public witness. -/
theorem standalone_satisfiable : StandaloneSatisfiableClaim :=
  ⟨[⟨#v[0, 1, 2, 3, 4, 5, 6, 7], fun _ _ => 0⟩], by decide +kernel, by
    change TopBitsChecked [0, 1, 2, 3, 4, 5, 6, 7]
    simp [TopBitsChecked, maxTopBit]⟩

/-- The reviewed token properties follow from the native layout theorem. -/
theorem unified_properties : UnifiedClaim := unified_claim

/-- The window top-bits check has a public witness. -/
theorem unified_satisfiable : UnifiedSatisfiableClaim :=
  ⟨[⟨#v[0, 1], fun _ _ => 0⟩], by decide +kernel, by
    change TopBitsChecked [0, 1]
    simp [TopBitsChecked, maxTopBit]⟩

end Airbender.InitsTeardowns
