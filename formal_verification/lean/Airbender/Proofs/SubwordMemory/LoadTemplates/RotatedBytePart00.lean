import Airbender.Proofs.SubwordMemory.LoadGeometry

namespace Airbender.SubwordMemory.LoadProofs
set_option autoImplicit false

/-- Sixteen actual stored template entries, in a separate bounded worker. -/
theorem rotatedByteValues_sample_00 : ∀ k : Fin 16,
    (rotatedByteValues[(0 + k.val)]?.getD 0) = (((0 + k.val) + 1) % 256) := by decide +kernel

end Airbender.SubwordMemory.LoadProofs
