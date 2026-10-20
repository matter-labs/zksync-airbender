import Airbender.Proofs.SubwordMemory.LoadGeometry

namespace Airbender.SubwordMemory.LoadProofs
set_option autoImplicit false

/-- Sixteen actual stored template entries, in a separate bounded worker. -/
theorem rotatedCarryValues_sample_06 : ∀ k : Fin 16,
    (rotatedCarryValues[(96 + k.val)]?.getD 0) = (((96 + k.val) + 1) / 256) := by decide +kernel

end Airbender.SubwordMemory.LoadProofs
