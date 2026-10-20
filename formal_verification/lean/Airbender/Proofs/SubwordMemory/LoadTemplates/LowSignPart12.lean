import Airbender.Proofs.SubwordMemory.LoadGeometry

namespace Airbender.SubwordMemory.LoadProofs
set_option autoImplicit false

/-- Sixteen actual stored template entries, in a separate bounded worker. -/
theorem lowSignValues_sample_12 : ∀ k : Fin 16,
    (lowSignValues[(192 + k.val)]?.getD 0) = (if (192 + k.val) < 128 then (192 + k.val) else (192 + k.val) + 65280) := by decide +kernel

end Airbender.SubwordMemory.LoadProofs
