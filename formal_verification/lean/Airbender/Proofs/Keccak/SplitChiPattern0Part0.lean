import Airbender.Data.Setup.Keccak.Chi5Generic

namespace Airbender.Keccak.Split.Native.Fixed.Proofs.ChiPattern0Part0
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000

/-- Check one bounded group of retained native chi output values. -/
theorem spec : ∀ index : Fin 1024,
    let position : Fin 4096 := ⟨0 + index.val, by omega⟩
    let a := position.val % 16
    let b := position.val / 16 % 16
    let c := position.val / 256 % 16
    chi5GenericBlock98Pattern[position] = a ^^^ ((15 ^^^ b) &&& c) := by
  simp only [chi5GenericBlock98Pattern, Fin.getElem_fin, Vector.getElem_ofFn]
  decide +kernel

end Airbender.Keccak.Split.Native.Fixed.Proofs.ChiPattern0Part0
