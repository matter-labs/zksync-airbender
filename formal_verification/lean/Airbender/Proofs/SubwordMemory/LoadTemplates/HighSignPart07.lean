import Airbender.Proofs.SubwordMemory.LoadGeometry

namespace Airbender.SubwordMemory.LoadProofs
set_option autoImplicit false

/-- Sixteen actual stored template entries, in a separate bounded worker. -/
theorem highSignValues_sample_07 : ∀ k : Fin 16,
    (highSignValues[(112 + k.val)]?.getD 0) = (if (112 + k.val) < 128 then 0 else 65535) := by decide +kernel

end Airbender.SubwordMemory.LoadProofs
