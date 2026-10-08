import Airbender.Proofs.Bigint.Lookups
import Airbender.Proofs.Bigint.Additive
import Airbender.Proofs.Bigint.Equality

namespace Airbender.Bigint.Proofs

theorem mapped_source_ranges {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {left right : Vector Nat 16} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable))
    (leftMap : ∀ i : Fin 16, left[i] = (w Variables.leftLimbs[i]).val)
    (rightMap : ∀ i : Fin 16, right[i] = (w Variables.rightLimbs[i]).val) :
    (∀ i : Fin 16, left[i] < Arithmetic.limbBase) ∧
      (∀ i : Fin 16, right[i] < Arithmetic.limbBase) := by
  constructor
  · intro i; rw [leftMap i]; exact (source_ranges hp h i).1
  · intro i; rw [rightMap i]; exact (source_ranges hp h i).2

end Airbender.Bigint.Proofs

namespace Airbender.Bigint.Additive.Proofs

theorem modeled_soundness {p : Nat} [Fact p.Prime] (hp : 131072 ≤ p) :
    Properties.Soundness (circuitModel (setupTable (p := p))).relation spec := by
  intro input output w ⟨h, mapping⟩
  exact soundness hp setupTable input output w
    ⟨Bigint.Proofs.mapped_source_ranges (by omega) h mapping.left mapping.right, h, mapping⟩

end Airbender.Bigint.Additive.Proofs

namespace Airbender.Bigint.Equality.Proofs

theorem modeled_soundness {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p) :
    Properties.Soundness (circuitModel (setupTable (p := p))).relation spec := by
  intro input output w ⟨h, mapping⟩
  exact soundness hp setupTable input output w
    ⟨Bigint.Proofs.mapped_source_ranges (by omega) h mapping.left mapping.right, h, mapping⟩

end Airbender.Bigint.Equality.Proofs
