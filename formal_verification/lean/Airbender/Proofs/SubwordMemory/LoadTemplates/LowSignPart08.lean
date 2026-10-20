import Airbender.Proofs.SubwordMemory.LoadGeometry

namespace Airbender.SubwordMemory.LoadProofs
set_option autoImplicit false

/-- Sixteen actual stored template entries, in a separate bounded worker. -/
theorem lowSignValues_sample_08 : ∀ k : Fin 16,
    (lowSignValues[(128 + k.val)]?.getD 0) = (if (128 + k.val) < 128 then (128 + k.val) else (128 + k.val) + 65280) := by decide +kernel

end Airbender.SubwordMemory.LoadProofs
