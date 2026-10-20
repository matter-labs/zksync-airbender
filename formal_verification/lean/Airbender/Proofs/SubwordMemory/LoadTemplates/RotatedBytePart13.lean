import Airbender.Proofs.SubwordMemory.LoadGeometry

namespace Airbender.SubwordMemory.LoadProofs
set_option autoImplicit false

/-- Sixteen actual stored template entries, in a separate bounded worker. -/
theorem rotatedByteValues_sample_13 : ∀ k : Fin 16,
    (rotatedByteValues[(208 + k.val)]?.getD 0) = (((208 + k.val) + 1) % 256) := by decide +kernel

end Airbender.SubwordMemory.LoadProofs
